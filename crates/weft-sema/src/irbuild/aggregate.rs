//! Aggregates: tuples, arrays, `Vec` literals, struct literals, positional
//! structs and variants (`docs/ir.md` 5.17).
//!
//! The parts run in order, each one into an operand where it is written. A
//! part that moves is a temporary that lives until the aggregate. The
//! aggregate writes into its destination itself. A `!Move` part that the
//! aggregate builds is built in place: its temporary is `in_place` (5.36).

use std::collections::HashMap;

use weft_ir::ty::{AdtKind, Lang};
use weft_ir::{AggKind, Const, Operand, Place, Rvalue, Ty, TyId, VariantIdx};
use weft_syntax::ast::{Expr, Ident};

use super::{unsupported, Builder, Construct, R};
use crate::thir::Res;

impl Builder<'_> {
    /// Evaluates `parts` in order and gives their operands. A place part
    /// skips its temporary if no later part can run code.
    fn part_operands(&mut self, parts: &[&Expr]) -> R<Vec<Operand>> {
        let mut ops = Vec::with_capacity(parts.len());
        for (x, skip) in parts.iter().zip(self.skips(parts)) {
            ops.push(self.operand_in(x, skip, true)?);
        }
        Ok(ops)
    }

    /// Writes aggregate `kind` of `parts` into `dest`.
    fn aggregate_into(&mut self, e: &Expr, kind: AggKind, parts: &[&Expr], dest: Place) -> R<()> {
        let ops = self.part_operands(parts)?;
        let origin = self.origin(e.span, Some(e.id));
        self.assign(dest, Rvalue::Aggregate(kind, ops), origin);
        Ok(())
    }

    /// Lowers a tuple `(a, b)`: `dest = Tuple(move ta, move tb)`.
    pub(super) fn tuple_into(&mut self, e: &Expr, xs: &[Expr], dest: Place) -> R<()> {
        let parts: Vec<&Expr> = xs.iter().collect();
        self.aggregate_into(e, AggKind::Tuple, &parts, dest)
    }

    /// Lowers `[a, b]`: a `Vec` aggregate, or an `Array` one if the type of
    /// `e` is an array.
    pub(super) fn array_into(&mut self, e: &Expr, xs: &[Expr], dest: Place) -> R<()> {
        let ty = self.ty(e)?;
        let kind = match (self.tys.try_get(ty), self.tys.lang(ty)) {
            (Some(Ty::Array(..)), _) => AggKind::Array,
            (_, Some((Lang::Vec, _))) => AggKind::Vec,
            _ => return unsupported(Construct::NoThir, e.span),
        };
        let parts: Vec<&Expr> = xs.iter().collect();
        self.aggregate_into(e, kind, &parts, dest)
    }

    /// Lowers a positional struct `S(x, y)`: the parts run in the order of
    /// the fields of `S` (`slots`, from the THIR), and the aggregate has them
    /// in that order.
    pub(super) fn positional_into(&mut self, e: &Expr, slots: &[&Expr], dest: Place) -> R<()> {
        let ty = self.ty(e)?;
        self.aggregate_into(e, AggKind::Struct(ty), slots, dest)
    }

    /// Lowers a variant constructor `Some(a)`: `dest = Variant(Option,
    /// Some)(move ta)`.
    pub(super) fn variant_into(
        &mut self,
        e: &Expr,
        variant: u32,
        slots: &[&Expr],
        dest: Place,
    ) -> R<()> {
        let ty = self.ty(e)?;
        self.aggregate_into(e, AggKind::Variant(ty, VariantIdx(variant)), slots, dest)
    }

    /// Lowers a struct literal `S { b: x, a: y }` (`docs/ir.md` 5.17):
    ///
    /// ```text
    /// tx := <x>; ty := <y>; dest = Struct(S)(move ty, move tx); Uninit(dest.f)
    /// ```
    ///
    /// The fields run in the written order; the aggregate has its operands
    /// in the order of the fields of `S`. A place field that the literal does
    /// not give has the operand `const ()` and gets `Uninit` after the
    /// aggregate, at each depth of its type: it has no value.
    pub(super) fn struct_lit_into(
        &mut self,
        e: &Expr,
        fields: &[(Ident, Expr)],
        dest: &Place,
    ) -> R<()> {
        let ty = self.ty(e)?;
        let names: HashMap<&str, usize> = match self.tys.try_get(ty) {
            Some(Ty::Adt(a, _)) => match self.tys.adts().get(a.index()).map(|d| &d.kind) {
                Some(AdtKind::Struct(fs)) => fs
                    .iter()
                    .enumerate()
                    .map(|(i, f)| (f.name.as_str(), i))
                    .collect(),
                _ => return unsupported(Construct::NoThir, e.span),
            },
            _ => return unsupported(Construct::NoThir, e.span),
        };
        let count = names.len();
        let mut given = Vec::with_capacity(fields.len());
        for (name, _) in fields {
            match names.get(name.name.as_str()) {
                Some(&i) => given.push(i),
                None => return unsupported(Construct::NoThir, name.span),
            }
        }
        let parts: Vec<&Expr> = fields.iter().map(|(_, x)| x).collect();
        let written = self.part_operands(&parts)?;
        let mut ops: Vec<Option<Operand>> = vec![None; count];
        for (&i, op) in given.iter().zip(written) {
            if let Some(slot) = ops.get_mut(i) {
                *slot = Some(op);
            }
        }
        let ops = ops
            .into_iter()
            .map(|o| o.unwrap_or(Operand::Const(Const::Unit)))
            .collect();
        let origin = self.origin(e.span, Some(e.id));
        self.assign(
            dest.clone(),
            Rvalue::Aggregate(AggKind::Struct(ty), ops),
            origin,
        );
        let given: Vec<u32> = given.into_iter().map(super::id_of).collect();
        self.unset_fields(dest, ty, &given, origin);
        Ok(())
    }

    /// Writes the value of a name that is not a local into `dest`: a variant
    /// with no payload is an aggregate with no operand (`None`). A function
    /// item as a value is a constant with its type arguments (`docs/ir.md`
    /// 5.23): `dest = Use(Const::Fn(f, tys))`. A constructor as a value is
    /// a type error of `typeck` (W0101, W0104), so the THIR never has one
    /// here (`docs/ir.md` 5.23).
    pub(super) fn item_into(&mut self, e: &Expr, dest: Place) -> R<()> {
        let t = self.t;
        match t.res.get(&e.id) {
            Some(Res::Variant { variant, .. }) => {
                let ty = self.ty(e)?;
                if !self.unit_variant(ty, *variant) {
                    return unsupported(Construct::NoThir, e.span);
                }
                self.aggregate_into(e, AggKind::Variant(ty, VariantIdx(*variant)), &[], dest)
            }
            Some(Res::Fn { item, targs }) => {
                let id = self.fn_id(*item, e.span)?;
                let origin = self.origin(e.span, Some(e.id));
                let c = Const::Fn(id, targs.clone());
                self.assign(dest, Rvalue::Use(Operand::Const(c)), origin);
                Ok(())
            }
            _ => unsupported(Construct::NoThir, e.span),
        }
    }

    /// Returns true if variant `v` of enum type `ty` has no payload.
    fn unit_variant(&self, ty: TyId, v: u32) -> bool {
        match self.tys.try_get(ty) {
            Some(Ty::Adt(a, _)) => match self.tys.adts().get(a.index()).map(|d| &d.kind) {
                Some(AdtKind::Enum(vs)) => vs.get(v as usize).is_some_and(|x| x.fields.is_empty()),
                _ => false,
            },
            _ => false,
        }
    }
}
