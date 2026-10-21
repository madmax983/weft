//! Expressions: literals, operators, borrows and blocks (`docs/ir.md`
//! 5.1.1, 5.9, 5.16). The places are in `place.rs`.
//!
//! An operand is read where it is written (choice A, `docs/ir.md` 5.1.1). A
//! place operand skips its temporary only if no later operand of the same
//! construct can run code.

use weft_ir::{BinOp, Const, IntTy, Operand, Place, Rvalue, TempKind, Ty, TyId, UnOp};
use weft_syntax::ast::{self, Expr, ExprKind, Lit, StrPart};

use super::{unsupported, Builder, Construct, R};

/// Returns the constant `()`.
pub(super) const fn unit() -> Operand {
    Operand::Const(Const::Unit)
}

/// Returns the operator of the IR for a binary operator of the syntax that is
/// not `&&` or `||`, and true for an arithmetic operator.
const fn bin_op(op: ast::BinOp) -> Option<(BinOp, bool)> {
    Some(match op {
        ast::BinOp::Add => (BinOp::Add, true),
        ast::BinOp::Sub => (BinOp::Sub, true),
        ast::BinOp::Mul => (BinOp::Mul, true),
        ast::BinOp::Div => (BinOp::Div, true),
        ast::BinOp::Rem => (BinOp::Rem, true),
        ast::BinOp::Eq => (BinOp::Eq, false),
        ast::BinOp::Ne => (BinOp::Ne, false),
        ast::BinOp::Lt => (BinOp::Lt, false),
        ast::BinOp::Le => (BinOp::Le, false),
        ast::BinOp::Gt => (BinOp::Gt, false),
        ast::BinOp::Ge => (BinOp::Ge, false),
        ast::BinOp::And | ast::BinOp::Or => return None,
    })
}

/// Returns the construct of an expression kind that the builder does not
/// lower yet.
const fn later(e: &ExprKind) -> Construct {
    match e {
        ExprKind::Call { .. } => Construct::Call,
        ExprKind::MethodCall { .. } => Construct::MethodCall,
        ExprKind::Range { .. } => Construct::Range,
        ExprKind::Tuple(_) => Construct::Tuple,
        ExprKind::Array(_) => Construct::Array,
        ExprKind::StructLit { .. } => Construct::StructLit,
        ExprKind::Closure { .. } => Construct::Closure,
        ExprKind::If { .. } => Construct::If,
        ExprKind::Match { .. } => Construct::Match,
        ExprKind::Handle { .. } => Construct::Handle,
        ExprKind::Scope { .. } => Construct::Scope,
        ExprKind::Binary { .. } => Construct::AndOr,
        ExprKind::Name(_) => Construct::ItemName,
        // The builder lowers these kinds before it asks for a right side.
        ExprKind::Field { .. }
        | ExprKind::Index { .. }
        | ExprKind::Unary { .. }
        | ExprKind::Lit(_)
        | ExprKind::Block(_) => Construct::NoThir,
    }
}

impl Builder<'_> {
    /// Returns the final type of expression `e`.
    pub(super) fn ty(&self, e: &Expr) -> R<TyId> {
        match self.t.expr_ty.get(&e.id) {
            Some(&t) => Ok(t),
            None => unsupported(Construct::NoThir, e.span),
        }
    }

    /// Returns the constant of `e` if `e` is a literal with no interpolation.
    /// `-128` is one literal, and so is the duration `2.s` (`docs/ir.md` 5.16).
    fn constant(&self, e: &Expr) -> R<Option<Const>> {
        match &e.kind {
            ExprKind::Field { base, name } => Ok(match (&base.kind, name.name.as_str()) {
                (ExprKind::Lit(Lit::Int(n)), "s") => Some(Const::Duration(n.saturating_mul(1000))),
                (ExprKind::Lit(Lit::Int(n)), "ms") => Some(Const::Duration(*n)),
                _ => None,
            }),
            ExprKind::Lit(Lit::Int(n)) => self.int_const(e, i128::from(*n)).map(Some),
            ExprKind::Lit(Lit::Bool(b)) => Ok(Some(Const::Bool(*b))),
            ExprKind::Lit(Lit::Unit) => Ok(Some(Const::Unit)),
            ExprKind::Lit(Lit::Str(parts)) => {
                let mut s = String::new();
                for p in parts {
                    match p {
                        StrPart::Text(t) => s.push_str(t),
                        StrPart::Interp(_) => return Ok(None),
                    }
                }
                Ok(Some(Const::Str(s)))
            }
            ExprKind::Unary {
                op: ast::UnOp::Neg,
                expr,
            } => {
                // `--128` is 128: each sign turns the value.
                let (mut x, mut neg) = (&**expr, true);
                while let ExprKind::Unary {
                    op: ast::UnOp::Neg,
                    expr: inner,
                } = &x.kind
                {
                    x = inner;
                    neg = !neg;
                }
                match &x.kind {
                    ExprKind::Lit(Lit::Int(n)) => {
                        let v = i128::from(*n);
                        self.int_const(e, if neg { -v } else { v }).map(Some)
                    }
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    /// Returns the integer constant `v` with the type of `e`.
    fn int_const(&self, e: &Expr, v: i128) -> R<Const> {
        let ty = self.ty(e)?;
        match self.tys.try_get(ty) {
            Some(Ty::Int(i)) => Ok(Const::Int(v, *i)),
            _ => unsupported(Construct::NoThir, e.span),
        }
    }

    /// Returns true if `e` cannot run code: a constant, or a path of a local
    /// and fields, through references, `Box`es and `Rc`s (`docs/ir.md` 5.1.1).
    /// A place operand before it can skip its temporary.
    pub(super) fn inert(&self, e: &Expr) -> bool {
        self.plain_path(e) || matches!(self.constant(e), Ok(Some(_)))
    }

    /// Writes the value of `e` into `dest` (`docs/ir.md` 5.1.1). A block and an
    /// operator write into `dest` itself, with no temporary between. A place
    /// is read: a copy of plain data, else a move.
    pub(super) fn into(&mut self, e: &Expr, dest: Place) -> R<()> {
        if let Some(p) = self.as_place(e)? {
            let origin = self.origin(e.span, Some(e.id));
            let op = self.read_place(p, self.value_ty(e)?, e)?;
            self.assign(dest, Rvalue::Use(op), origin);
            return Ok(());
        }
        self.value_into(e, dest)
    }

    /// Writes the value of `e` into `dest`, with no implicit dereference: a
    /// constant, a block, or a right side. The place of a place expression
    /// is for [`Builder::into`].
    pub(super) fn value_into(&mut self, e: &Expr, dest: Place) -> R<()> {
        let origin = self.origin(e.span, Some(e.id));
        if let Some(c) = self.constant(e)? {
            self.assign(dest, Rvalue::Use(Operand::Const(c)), origin);
            return Ok(());
        }
        if let ExprKind::Block(b) = &e.kind {
            return self.block_into(b, dest, false);
        }
        let rv = self.rvalue(e)?;
        self.assign(dest, rv, origin);
        Ok(())
    }

    /// Returns the right side of an operator, a borrow or an interpolation.
    fn rvalue(&mut self, e: &Expr) -> R<Rvalue> {
        match &e.kind {
            ExprKind::Unary {
                op: ast::UnOp::Ref,
                expr,
            } => self.borrow(expr),
            ExprKind::Unary { op, expr } => {
                let a = self.operand(expr, true)?;
                Ok(match op {
                    ast::UnOp::Not => Rvalue::Unary(UnOp::Not, None, a),
                    _ => Rvalue::Unary(UnOp::Neg, self.int_ty(e), a),
                })
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let Some((op, arith)) = bin_op(*op) else {
                    return unsupported(Construct::AndOr, e.span);
                };
                let skip = self.inert(rhs);
                if arith {
                    let a = self.operand(lhs, skip)?;
                    let b = self.operand(rhs, true)?;
                    Ok(Rvalue::Binary(op, self.int_ty(e), a, b))
                } else {
                    let a = self.read_operand(lhs, skip)?;
                    let b = self.read_operand(rhs, true)?;
                    Ok(Rvalue::Binary(op, None, a, b))
                }
            }
            ExprKind::Lit(Lit::Str(parts)) => {
                let mut ops = Vec::with_capacity(parts.len());
                for (i, p) in parts.iter().enumerate() {
                    match p {
                        StrPart::Text(t) => ops.push(Operand::Const(Const::Str(t.clone()))),
                        StrPart::Interp(x) => {
                            let skip = parts.iter().skip(i + 1).all(|q| match q {
                                StrPart::Text(_) => true,
                                StrPart::Interp(y) => self.inert(y),
                            });
                            ops.push(self.read_operand(x, skip)?);
                        }
                    }
                }
                Ok(Rvalue::Concat(ops))
            }
            k => unsupported(later(k), e.span),
        }
    }

    /// Returns the integer type of the operator `e` from the THIR.
    pub(super) fn int_ty(&self, e: &Expr) -> Option<IntTy> {
        self.t.int_ty.get(&e.id).copied()
    }

    /// Evaluates `e` now and gives an operand in a move position (`docs/ir.md`
    /// 5.1.1). A constant stays a constant. A place gives `t := copy p` or
    /// `t := move p`; with `skip`, no later operand can run code, and the place
    /// itself is the operand. A value gives a temporary.
    pub(super) fn operand(&mut self, e: &Expr, skip: bool) -> R<Operand> {
        if let Some(c) = self.constant(e)? {
            return Ok(Operand::Const(c));
        }
        let origin = self.origin(e.span, Some(e.id));
        if let Some(p) = self.as_place(e)? {
            let ty = self.value_ty(e)?;
            let op = self.read_place(p, ty, e)?;
            if skip {
                return Ok(op);
            }
            let t = self.temp(ty, TempKind::Operand, origin);
            self.assign(Place::local(t), Rvalue::Use(op), origin);
            return Ok(Operand::Move(Place::local(t)));
        }
        let ty = self.ty(e)?;
        let t = self.temp(ty, TempKind::Operand, origin);
        self.value_into(e, Place::local(t))?;
        Ok(Operand::Move(Place::local(t)))
    }

    /// Evaluates `e` now and gives an operand in a read position: a comparison
    /// or an interpolation (`docs/ir.md` 5.1.1, 5.16). Plain data is an operand
    /// as in [`Builder::operand`]. Another value is borrowed where it is
    /// written: `t := &p`, or `tv := <e>; t := &tv` for a value.
    fn read_operand(&mut self, e: &Expr, skip: bool) -> R<Operand> {
        let ty = self.value_ty(e)?;
        if !self.tys.not_copy(ty) {
            return self.operand(e, skip);
        }
        let origin = self.origin(e.span, Some(e.id));
        let place = if let Some(p) = self.as_place(e)? {
            p
        } else {
            let tv = self.temp(ty, TempKind::Borrowed, origin);
            self.value_into(e, Place::local(tv))?;
            Place::local(tv)
        };
        let rty = self.tys.intern(Ty::Ref(ty));
        let t = self.temp(rty, TempKind::Operand, origin);
        self.assign(Place::local(t), Rvalue::Ref(place), origin);
        Ok(Operand::Move(Place::local(t)))
    }
}
