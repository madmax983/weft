//! Patterns: the tests and the bindings of a `match` arm and of a `let`
//! (`docs/ir.md` 5.3, 5.13).
//!
//! The builder walks a pattern once and makes a plan ([`Plan`]): the tests,
//! in pre-order and left to right, and the actions (the bindings, the moves of
//! the parts under `_`, the ends of linear values), in the order of the
//! source. Then it writes all the tests, and after the last test the actions.
//! So no binding and no move comes before the last test of its arm. A test
//! only reads: `Discriminant`, a copy of a scalar, or a comparison of a
//! string.
//!
//! The place of each part of the pattern is a place below the scrutinee: a
//! tuple part is `q.k`, a payload is `(q as V).k`, and each implicit
//! dereference of the THIR (`Tables::pat_adjust`) is `(*q)`. A `Variant`
//! projection is only in a block after the test of its variant (V8).

use weft_ir::ty::AdtKind;
use weft_ir::{
    BinOp, Const, FieldIdx, IntTy, LocalId, Operand, Place, Proj, Rvalue, StmtKind, TempKind, Ty,
    TyId, VariantIdx,
};
use weft_syntax::ast::{Lit, Pattern, PatternKind, Span, StrPart};

use super::{no_ir, unsupported, Builder, Construct, NoIr, R};
use crate::thir::{self, BindingId};

/// One test of a pattern.
#[derive(Clone, Debug)]
enum Test {
    /// The value at the place is variant `v` of an enum.
    Variant(Place, u32),
    /// The scalar at the place has this value.
    Scalar(Place, u128),
    /// The string at the place (of this type) is this text.
    Str(Place, TyId, String),
}

/// How a binding takes its value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum How {
    /// A copy of plain data.
    Copy,
    /// A move.
    Move,
    /// A reference to the place: a binding through a reference.
    Ref,
}

/// One action of a pattern after its tests.
#[derive(Clone, Debug)]
enum Act {
    /// A binding gets the value at the place.
    Bind(BindingId, Span, Place, How),
    /// `_` over the part at the place, of this type.
    Wild(Span, Place, TyId),
    /// The value at the place is finished if it can be linear: a variant
    /// with no payload, or a struct that the pattern takes apart.
    Finish(Span, Place, TyId),
}

/// The plan of one pattern.
#[derive(Clone, Debug, Default)]
pub(super) struct Plan {
    /// The tests, in pre-order.
    tests: Vec<(Span, Test)>,
    /// The actions, in the order of the source.
    acts: Vec<Act>,
    /// A binding moves a part of the value.
    pub(super) moves: bool,
}

impl Plan {
    /// Returns true if the pattern has a test: it can fail.
    pub(super) fn has_tests(&self) -> bool {
        !self.tests.is_empty()
    }
}

/// Returns the projection of an implicit dereference of the THIR.
const fn deref_proj(k: thir::DerefKind) -> Proj {
    Proj::Deref(match k {
        thir::DerefKind::Ref => weft_ir::DerefKind::Ref,
        thir::DerefKind::Box => weft_ir::DerefKind::Box,
        thir::DerefKind::Rc => weft_ir::DerefKind::Rc,
    })
}

/// Returns place `q` with projection `p` after it.
fn with(q: &Place, p: Proj) -> Place {
    let mut q = q.clone();
    q.proj.push(p);
    q
}

/// Returns true if place `q` goes through a reference: a move cannot take
/// its value.
fn through_ref(q: &Place) -> bool {
    q.proj.contains(&Proj::Deref(weft_ir::DerefKind::Ref))
}

impl Builder<'_> {
    /// Returns the place and the type after the dereference `k` of place `q`
    /// of type `t`.
    fn deref_step(&self, q: &Place, t: TyId, k: thir::DerefKind, span: Span) -> R<(Place, TyId)> {
        let next = match (k, self.tys.try_get(t)) {
            (thir::DerefKind::Ref, Some(Ty::Ref(x))) => Some(*x),
            (thir::DerefKind::Box | thir::DerefKind::Rc, Some(Ty::Adt(_, args))) => {
                args.first().copied()
            }
            _ => None,
        };
        match next {
            Some(x) => Ok((with(q, deref_proj(k)), x)),
            None => unsupported(Construct::NoThir, span),
        }
    }

    /// Returns the place and the type of the value that pattern `pat` tests:
    /// place `q` of type `t` after the dereferences of `pat`.
    fn pat_place(&self, pat: &Pattern, q: Place, t: TyId) -> R<(Place, TyId)> {
        let steps = self
            .t
            .pat_adjust
            .get(&pat.id)
            .map_or(&[][..], Vec::as_slice);
        let (mut q, mut t) = (q, t);
        for &k in steps {
            (q, t) = self.deref_step(&q, t, k, pat.span())?;
        }
        Ok((q, t))
    }

    /// Makes the plan of pattern `pat` over place `q` of type `t`.
    pub(super) fn plan(&mut self, pat: &Pattern, q: Place, t: TyId) -> R<Plan> {
        let mut plan = Plan::default();
        self.plan_into(pat, q, t, &mut plan)?;
        Ok(plan)
    }

    /// Adds the tests and the actions of pattern `pat` over place `q` of type
    /// `t` to `plan`. The recursion follows the nesting of the pattern, which
    /// the parser bounds.
    fn plan_into(&mut self, pat: &Pattern, q: Place, t: TyId, plan: &mut Plan) -> R<()> {
        let span = pat.span();
        match &pat.kind {
            PatternKind::Wild(_) => plan.acts.push(Act::Wild(span, q, t)),
            PatternKind::Bind(id) => {
                let (b, how, q) = self.bind_how(pat, q, t, id.span)?;
                plan.moves |= how == How::Move;
                plan.acts.push(Act::Bind(b, id.span, q, how));
            }
            PatternKind::Tuple(ps, _) => {
                let (q, t) = self.pat_place(pat, q, t)?;
                let ts = match self.tys.try_get(t) {
                    Some(Ty::Tuple(ts)) if ts.len() == ps.len() => ts.clone(),
                    _ => return unsupported(Construct::NoThir, span),
                };
                for (i, (p, &pt)) in ps.iter().zip(&ts).enumerate() {
                    let qi = with(&q, Proj::Field(FieldIdx(super::id_of(i))));
                    self.plan_into(p, qi, pt, plan)?;
                }
            }
            PatternKind::Variant { path, fields, .. } => {
                let (q, t) = self.pat_place(pat, q, t)?;
                let Some(Ty::Adt(a, args)) = self.tys.try_get(t).cloned() else {
                    return unsupported(Construct::NoThir, span);
                };
                let name = path.last().map_or("", |p| p.name.as_str());
                // Only the shape that the pattern needs: a copy of all the
                // variants for each arm makes a wide `match` quadratic.
                let shape = match self.tys.adts().get(a.index()).map(|d| &d.kind) {
                    Some(AdtKind::Enum(vs)) => vs
                        .iter()
                        .enumerate()
                        .find(|(_, v)| v.name == name)
                        .map(|(v, vd)| (Some(super::id_of(v)), vd.fields.clone())),
                    Some(AdtKind::Struct(fs)) => {
                        Some((None, fs.iter().map(|f| f.ty).collect::<Vec<TyId>>()))
                    }
                    _ => None,
                };
                let Some((variant, fts)) = shape else {
                    return unsupported(Construct::NoThir, span);
                };
                if fts.len() != fields.len() {
                    return unsupported(Construct::NoThir, span);
                }
                if let Some(v) = variant {
                    plan.tests.push((span, Test::Variant(q.clone(), v)));
                }
                for (k, (p, &ft)) in fields.iter().zip(&fts).enumerate() {
                    let ft = super::unset::subst(self.tys, ft, &args);
                    let mut qk = q.clone();
                    if let Some(v) = variant {
                        qk.proj.push(Proj::Variant(VariantIdx(v)));
                    }
                    qk.proj.push(Proj::Field(FieldIdx(super::id_of(k))));
                    self.plan_into(p, qk, ft, plan)?;
                }
                if variant.is_none() || fields.is_empty() {
                    plan.acts.push(Act::Finish(span, q, t));
                }
            }
            PatternKind::Lit(lit, _) => {
                let (q, t) = self.pat_place(pat, q, t)?;
                let test = match (lit, self.tys.try_get(t)) {
                    (Lit::Int(n), Some(Ty::Int(_))) => Test::Scalar(q, u128::from(*n)),
                    (Lit::Bool(b), Some(Ty::Bool)) => Test::Scalar(q, u128::from(*b)),
                    // `()` has one value: no test.
                    (Lit::Unit, Some(Ty::Unit)) => return Ok(()),
                    (Lit::Str(parts), _) => {
                        let mut s = String::new();
                        for p in parts {
                            match p {
                                StrPart::Text(x) => s.push_str(x),
                                StrPart::Interp(_) => return unsupported(Construct::NoThir, span),
                            }
                        }
                        Test::Str(q, t, s)
                    }
                    _ => return unsupported(Construct::NoThir, span),
                };
                plan.tests.push((span, test));
            }
        }
        Ok(())
    }

    /// Returns the binding of name pattern `pat` over place `q` of type `t`,
    /// how it takes its value, and the place it takes it from.
    ///
    /// The type of the local decides: the type of the place is a binding by
    /// value (a copy or a move), a reference to it is a binding by reference.
    /// Each implicit dereference of the pattern is tried in turn: a binding of
    /// a reference payload by value copies the reference.
    fn bind_how(&self, pat: &Pattern, q: Place, t: TyId, span: Span) -> R<(BindingId, How, Place)> {
        let Some(&b) = self.t.binding.get(&pat.id) else {
            return unsupported(Construct::NoThir, span);
        };
        let Some(bty) = self.t.binding_of(b).map(|x| x.ty) else {
            return unsupported(Construct::NoThir, span);
        };
        let steps = self
            .t
            .pat_adjust
            .get(&pat.id)
            .map_or(&[][..], Vec::as_slice);
        let (mut q, mut t) = (q, t);
        for i in 0..=steps.len() {
            if bty == t {
                if self.copies(&q, t) {
                    return Ok((b, How::Copy, q));
                }
                if through_ref(&q) {
                    return no_ir(NoIr::MoveThroughRef);
                }
                return Ok((b, How::Move, q));
            }
            if self.tys.find(&Ty::Ref(t)) == Some(bty) {
                return Ok((b, How::Ref, q));
            }
            if let Some(&k) = steps.get(i) {
                (q, t) = self.deref_step(&q, t, k, span)?;
            }
        }
        unsupported(Construct::NoThir, span)
    }

    /// Writes the tests of `plan` (`docs/ir.md` 5.13). Each failed test ends
    /// the temporaries of the tests before it, then goes to the tests of the
    /// next arm: the block that the result gives. `None`: no test can fail.
    /// After the last test, the temporaries of the tests end.
    pub(super) fn tests(&mut self, plan: &Plan) -> Option<usize> {
        let mut next: Option<usize> = None;
        let mut temps: Vec<LocalId> = Vec::new();
        for (span, test) in &plan.tests {
            let origin = self.origin(*span, None);
            let (on, val) = match test {
                Test::Variant(q, v) => {
                    let ty = self.tys.intern(Ty::Int(IntTy::Usize));
                    let td = self.loose_temp(ty, TempKind::Scrutinee, origin);
                    self.assign(Place::local(td), Rvalue::Discriminant(q.clone()), origin);
                    temps.push(td);
                    (Operand::Move(Place::local(td)), u128::from(*v))
                }
                Test::Scalar(q, v) => (Operand::Copy(q.clone()), *v),
                Test::Str(q, ty, s) => {
                    let read = if self.tys.not_copy(*ty) {
                        let rty = self.tys.intern(Ty::Ref(*ty));
                        let tq = self.loose_temp(rty, TempKind::Operand, origin);
                        self.assign(Place::local(tq), Rvalue::Ref(q.clone()), origin);
                        temps.push(tq);
                        Operand::Move(Place::local(tq))
                    } else {
                        Operand::Copy(q.clone())
                    };
                    let bty = self.tys.intern(Ty::Bool);
                    let tb = self.loose_temp(bty, TempKind::Operand, origin);
                    let rv = Rvalue::Binary(
                        BinOp::Eq,
                        None,
                        read,
                        Operand::Const(Const::Str(s.clone())),
                    );
                    self.assign(Place::local(tb), rv, origin);
                    temps.push(tb);
                    (Operand::Move(Place::local(tb)), 1)
                }
            };
            let n = if let Some(n) = next {
                n
            } else {
                let n = self.new_block();
                next = Some(n);
                n
            };
            let ok = self.new_block();
            let no = if temps.is_empty() {
                n
            } else {
                self.new_block()
            };
            self.terminate(
                weft_ir::TermKind::Switch {
                    on,
                    arms: vec![(val, super::BlockId(super::id_of(ok)))],
                    otherwise: super::BlockId(super::id_of(no)),
                },
                origin,
            );
            if no != n {
                self.enter(no);
                for &t in temps.iter().rev() {
                    self.push(StmtKind::Dead(t), origin);
                }
                self.goto(n, origin);
            }
            self.enter(ok);
        }
        if let Some((span, _)) = plan.tests.last() {
            let origin = self.origin(*span, None);
            for &t in temps.iter().rev() {
                self.push(StmtKind::Dead(t), origin);
            }
        }
        next
    }

    /// Writes the actions of `plan`: the bindings, in the innermost block
    /// scope, the moves of linear parts under `_` (if the arm or the `let`
    /// `takes` the value), and the ends of linear values.
    pub(super) fn binds(&mut self, plan: &Plan, takes: bool) -> R<()> {
        for act in &plan.acts {
            match act {
                Act::Bind(b, span, q, how) => {
                    let l = self.user_local(*b, *span)?;
                    let rv = match how {
                        How::Copy => Rvalue::Use(Operand::Copy(q.clone())),
                        How::Move => Rvalue::Use(Operand::Move(q.clone())),
                        How::Ref => Rvalue::Ref(q.clone()),
                    };
                    let origin = self.origin(*span, None);
                    self.assign(Place::local(l), rv, origin);
                }
                Act::Wild(span, q, t) => {
                    // `t := move q; Dead(t)`: the facts see a part move and
                    // the end of the part (W0601 for a linear part).
                    if takes && !through_ref(q) && self.tys.not_copy(*t) && self.maybe_linear(*t) {
                        let origin = self.origin(*span, None);
                        let tw = self.loose_temp(*t, TempKind::Discarded, origin);
                        self.assign(
                            Place::local(tw),
                            Rvalue::Use(Operand::Move(q.clone())),
                            origin,
                        );
                        self.push(StmtKind::Dead(tw), origin);
                    }
                }
                Act::Finish(span, q, t) => {
                    if !through_ref(q) && self.maybe_linear(*t) {
                        let origin = self.origin(*span, None);
                        self.push(StmtKind::Consume(q.clone()), origin);
                    }
                }
            }
        }
        Ok(())
    }

    /// Lowers `let p: T` with no value (`docs/ir.md` 5.3): `Live(x);
    /// Uninit(x)` for each binding of the pattern.
    pub(super) fn let_uninit(&mut self, pat: &Pattern) -> R<()> {
        match &pat.kind {
            PatternKind::Bind(id) => {
                let Some(&b) = self.t.binding.get(&pat.id) else {
                    return unsupported(Construct::NoThir, id.span);
                };
                let l = self.user_local(b, id.span)?;
                let origin = self.origin(id.span, None);
                self.push(StmtKind::Uninit(Place::local(l)), origin);
                Ok(())
            }
            PatternKind::Wild(_) => Ok(()),
            PatternKind::Tuple(ps, _) => {
                for p in ps {
                    self.let_uninit(p)?;
                }
                Ok(())
            }
            PatternKind::Variant { .. } | PatternKind::Lit(..) => {
                unsupported(Construct::NoThir, pat.span())
            }
        }
    }
}
