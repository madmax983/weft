//! Places: names, fields, indexes, the implicit dereferences of the THIR,
//! and borrows (`docs/ir.md` 5.8, 5.9, 5.32).
//!
//! The THIR keys each implicit dereference by the expression whose value it
//! follows (`Tables::adjust`). The builder writes each one as a `Deref`
//! projection after the place of that expression. So `r.f` with `r: &S` is
//! `(*r).f`, `b.f` with `b: Box<S>` is `(*b).f` with `Deref(Box)`, and `h.f`
//! with `h: Rc<S>` is `(*h).f` with `Deref(Rc)`.
//!
//! No expression writes a split step (`Proj::Split`): a split place comes only
//! from a signature (`docs/ir.md` 5.8).

use weft_ir::{FieldIdx, LocalId, Operand, Place, Proj, Rvalue, StmtKind, TempKind, Ty, TyId};
use weft_syntax::ast::{Expr, ExprKind};

use super::{unsupported, Builder, Construct, R};
use crate::thir::{self, Res};

/// Returns the projection of an implicit dereference of the THIR.
const fn deref_proj(k: thir::DerefKind) -> Proj {
    Proj::Deref(match k {
        thir::DerefKind::Ref => weft_ir::DerefKind::Ref,
        thir::DerefKind::Box => weft_ir::DerefKind::Box,
        thir::DerefKind::Rc => weft_ir::DerefKind::Rc,
    })
}

impl Builder<'_> {
    /// Returns the implicit dereferences of the value of `e`.
    fn adjust(&self, e: &Expr) -> &[thir::DerefKind] {
        self.t.adjust.get(&e.id).map_or(&[], Vec::as_slice)
    }

    /// Returns the type of the value of `e` after its implicit dereferences:
    /// the type of the place that [`Builder::as_place`] gives, or of the
    /// operand that [`Builder::into`] writes. A step that does not fit the
    /// type gives `Unsupported` (the THIR is wrong).
    pub(super) fn value_ty(&self, e: &Expr) -> R<TyId> {
        let mut t = self.ty(e)?;
        for &k in self.adjust(e) {
            let next = match (k, self.tys.try_get(t)) {
                (thir::DerefKind::Ref, Some(Ty::Ref(x))) => Some(*x),
                (thir::DerefKind::Box | thir::DerefKind::Rc, Some(Ty::Adt(_, args))) => {
                    args.first().copied()
                }
                _ => None,
            };
            match next {
                Some(x) => t = x,
                None => return unsupported(Construct::NoThir, e.span),
            }
        }
        Ok(t)
    }

    /// Returns true if `e` is a path of a local and fields: a place whose
    /// read runs no code (`docs/ir.md` 5.1.1). Its dereferences run no code
    /// either.
    pub(super) fn plain_path(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Name(_) => matches!(self.t.res.get(&e.id), Some(Res::Local(_))),
            ExprKind::Field { base, .. } => {
                matches!(self.t.field.get(&e.id), Some(thir::FieldIdx::Field(_)))
                    && !self.t.res.contains_key(&e.id)
                    && self.plain_path(base)
            }
            _ => false,
        }
    }

    /// Evaluates the place expression `e` and gives its place (`docs/ir.md`
    /// 5.1.1, 5.8), after the implicit dereferences of the THIR. The index
    /// expressions run now, in order, into temporaries, each one followed by
    /// its `Bounds` check. A value with an implicit dereference goes into a
    /// temporary of the current statement first. Another value gives `None`
    /// and no statement.
    pub(super) fn as_place(&mut self, e: &Expr) -> R<Option<Place>> {
        let mut place = match &e.kind {
            ExprKind::Name(_) => self.local_place(e)?,
            ExprKind::Field { base, .. } => {
                if matches!(base.kind, ExprKind::Lit(_)) {
                    // A duration literal `2.s`: a constant.
                    return Ok(None);
                }
                if self.t.res.contains_key(&e.id) {
                    // A member of a path: a variant or an item.
                    return unsupported(Construct::ItemName, e.span);
                }
                match self.t.field.get(&e.id) {
                    Some(thir::FieldIdx::Field(i)) => {
                        let mut p = self.place_or_temp(base)?;
                        p.proj.push(Proj::Field(FieldIdx(*i)));
                        p
                    }
                    Some(thir::FieldIdx::Variant(v)) => self.variant_field(base, *v, e)?,
                    None => return unsupported(Construct::NoThir, e.span),
                }
            }
            ExprKind::Index { base, index } => {
                let mut p = self.place_or_temp(base)?;
                if let Some(i) = index {
                    let ti = self.index_temp(i)?;
                    let origin = self.origin(e.span, Some(e.id));
                    let len = Operand::Copy(Place::local(ti));
                    self.push(StmtKind::Bounds(p.clone(), len), origin);
                    p.proj.push(Proj::Index(ti));
                } else {
                    // The verifier finds the type `[T]` of the place in the
                    // table.
                    let ty = self.ty(e)?;
                    if !matches!(self.tys.try_get(ty), Some(Ty::Slice(_))) {
                        return unsupported(Construct::NoThir, e.span);
                    }
                    p.proj.push(Proj::Elems);
                }
                p
            }
            _ if !self.adjust(e).is_empty() => {
                let ty = self.ty(e)?;
                let origin = self.origin(e.span, Some(e.id));
                let t = self.temp(ty, TempKind::Operand, origin);
                self.value_into(e, Place::local(t))?;
                Place::local(t)
            }
            _ => return Ok(None),
        };
        // Check the steps against the types before the projections go in.
        self.value_ty(e)?;
        place
            .proj
            .extend(self.adjust(e).iter().map(|&k| deref_proj(k)));
        Ok(Some(place))
    }

    /// Returns the place of the payload of variant `v` of `base`, the place
    /// expression `e` (`docs/ir.md` 5.8): `(p as V).0` after a test of the
    /// variant.
    ///
    /// ```text
    /// td := Discriminant(p); Switch(move td) [v: next, otherwise: fail]
    /// fail: Unreachable
    /// ```
    ///
    /// The value at run time can be another variant: the interpreter stops
    /// with a fault there. The checker follows only the path of the variant.
    fn variant_field(&mut self, base: &Expr, v: u32, e: &Expr) -> R<Place> {
        let mut p = self.place_or_temp(base)?;
        let ty = self.value_ty(base)?;
        let one = match self.tys.try_get(ty) {
            Some(Ty::Adt(a, _)) => match self.tys.adts().get(a.index()).map(|d| &d.kind) {
                Some(weft_ir::ty::AdtKind::Enum(vs)) => {
                    vs.get(v as usize).is_some_and(|x| x.fields.len() == 1)
                }
                _ => false,
            },
            _ => false,
        };
        if !one {
            return unsupported(Construct::VariantField, e.span);
        }
        let origin = self.origin(e.span, Some(e.id));
        let uty = self.tys.intern(Ty::Int(weft_ir::IntTy::Usize));
        let td = self.temp(uty, TempKind::Scrutinee, origin);
        self.assign(Place::local(td), Rvalue::Discriminant(p.clone()), origin);
        let (ok, fail) = (self.new_block(), self.new_block());
        self.terminate(
            weft_ir::TermKind::Switch {
                on: Operand::Move(Place::local(td)),
                arms: vec![(u128::from(v), weft_ir::BlockId(super::id_of(ok)))],
                otherwise: weft_ir::BlockId(super::id_of(fail)),
            },
            origin,
        );
        self.enter(fail);
        self.terminate(weft_ir::TermKind::Unreachable, origin);
        self.enter(ok);
        p.proj.push(Proj::Variant(weft_ir::VariantIdx(v)));
        p.proj.push(Proj::Field(FieldIdx(0)));
        Ok(p)
    }

    /// Returns the place of the local that name `e` names.
    fn local_place(&self, e: &Expr) -> R<Place> {
        match self.t.res.get(&e.id) {
            Some(Res::Local(b)) => match self.vars.get(b) {
                Some(&l) => Ok(Place::local(l)),
                None => unsupported(Construct::NoThir, e.span),
            },
            Some(_) => unsupported(Construct::ItemName, e.span),
            None => unsupported(Construct::NoThir, e.span),
        }
    }

    /// Returns the place of `e`. A value with no place goes into a temporary
    /// of the current statement (`docs/ir.md` 5.1.1).
    fn place_or_temp(&mut self, e: &Expr) -> R<Place> {
        if let Some(p) = self.as_place(e)? {
            return Ok(p);
        }
        let ty = self.ty(e)?;
        let origin = self.origin(e.span, Some(e.id));
        let t = self.temp(ty, TempKind::Operand, origin);
        self.value_into(e, Place::local(t))?;
        Ok(Place::local(t))
    }

    /// Evaluates index expression `i` into a new temporary of type `usize`.
    fn index_temp(&mut self, i: &Expr) -> R<LocalId> {
        let ty = self.value_ty(i)?;
        if !matches!(self.tys.try_get(ty), Some(Ty::Int(weft_ir::IntTy::Usize))) {
            return unsupported(Construct::NoThir, i.span);
        }
        let origin = self.origin(i.span, Some(i.id));
        let t = self.temp(ty, TempKind::Operand, origin);
        self.into(i, Place::local(t))?;
        Ok(t)
    }

    /// Returns the operand that reads place `p` of type `ty` (the type of
    /// `e`): a copy of plain data, else a move. A move through a reference is
    /// W0303 (`docs/ir.md` 5.36): the builder does not lower it yet.
    pub(super) fn read_place(&self, p: Place, ty: TyId, e: &Expr) -> R<Operand> {
        if !self.tys.not_copy(ty) {
            return Ok(Operand::Copy(p));
        }
        if p.proj.contains(&Proj::Deref(weft_ir::DerefKind::Ref)) {
            return unsupported(Construct::MoveThroughRef, e.span);
        }
        Ok(Operand::Move(p))
    }

    /// Returns the right side of borrow `&inner` (`docs/ir.md` 5.9):
    ///
    /// ```text
    /// &p        =>  &<place p>
    /// &p[]      =>  &<place p>[]
    /// &value    =>  tv := <value>; &tv          (tv in the current Stmt scope)
    /// ```
    ///
    /// A borrow does not read the value.
    pub(super) fn borrow(&mut self, inner: &Expr) -> R<Rvalue> {
        if let Some(p) = self.as_place(inner)? {
            return Ok(Rvalue::Ref(p));
        }
        let ty = self.ty(inner)?;
        let origin = self.origin(inner.span, Some(inner.id));
        let tv = self.temp(ty, TempKind::Borrowed, origin);
        self.value_into(inner, Place::local(tv))?;
        Ok(Rvalue::Ref(Place::local(tv)))
    }

    /// Returns true if the old value at a place of type `t` can be linear: a
    /// part is linear, or a part is a type parameter (`docs/ir.md` 5.1.3, V17).
    pub(super) fn maybe_linear(&self, t: TyId) -> bool {
        crate::props::ir_maybe_linear(self.tys, t)
    }
}
