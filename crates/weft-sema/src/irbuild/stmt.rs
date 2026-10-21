//! Blocks and statements (`docs/ir.md` 5.3, 5.4, 5.5, 5.11).

use weft_ir::{Operand, Place, Rvalue, StmtKind, TempKind};
use weft_syntax::ast::{self, AssignOp, Expr, PatternKind, Stmt, StmtKind as S};

use super::frame::closing;
use super::{unsupported, Builder, Construct, ScopeKind, R};

impl Builder<'_> {
    /// Lowers block `b` into `dest` (`docs/ir.md` 5.11):
    ///
    /// ```text
    /// Block scope { Stmt{s1} ... Stmt{sn}; into(e, dest) }; <Dead of the block locals>
    /// ```
    ///
    /// The value moves into `dest` before the block locals end. With `discard`,
    /// the tail is an expression statement and `dest` gets `()`.
    pub(super) fn block_into(&mut self, b: &ast::Block, dest: Place, discard: bool) -> R<()> {
        self.open(ScopeKind::Block, closing(b.span));
        let n = b.stmts.len();
        let mut tail = None;
        for (i, s) in b.stmts.iter().enumerate() {
            match &s.kind {
                S::Expr(e) if i + 1 == n && !discard => tail = Some(e),
                _ => self.stmt(s)?,
            }
        }
        match tail {
            Some(e) => self.into(e, dest)?,
            // A block with no tail has the value `()`. A block whose end cannot
            // run has no value.
            None if self.live => {
                let origin = self.origin(b.span, None);
                self.assign(dest, Rvalue::Use(super::expr::unit()), origin);
            }
            None => {}
        }
        self.close();
        Ok(())
    }

    /// Lowers statement `s` in a statement scope of its own.
    fn stmt(&mut self, s: &Stmt) -> R<()> {
        self.open(ScopeKind::Stmt, s.span);
        match &s.kind {
            S::Let { pat, init, .. } => self.let_stmt(pat, init.as_ref(), s)?,
            S::Expr(e) => self.expr_stmt(e)?,
            S::Assign { target, op, value } => self.assign_stmt(target, *op, value, s)?,
            S::Return(e) => self.return_stmt(e.as_ref(), s.span)?,
            S::Break => return unsupported(Construct::Break, s.span),
            S::Continue => return unsupported(Construct::Continue, s.span),
            S::While { .. } => return unsupported(Construct::While, s.span),
            S::For { .. } => return unsupported(Construct::For, s.span),
            S::Loop(_) => return unsupported(Construct::Loop, s.span),
            S::Assert(_) => return unsupported(Construct::Assert, s.span),
        }
        self.close();
        Ok(())
    }

    /// Lowers `let` (`docs/ir.md` 5.3):
    ///
    /// ```text
    /// let x = e   =>  Live(x); <into(e, x)>
    /// let _ = e   =>  t := <e>; Dead(t)
    /// ```
    fn let_stmt(&mut self, pat: &ast::Pattern, init: Option<&Expr>, s: &Stmt) -> R<()> {
        let Some(init) = init else {
            return unsupported(Construct::LetUninit, s.span);
        };
        match &pat.kind {
            PatternKind::Bind(id) => {
                let Some(&b) = self.t.binding.get(&pat.id) else {
                    return unsupported(Construct::NoThir, id.span);
                };
                // A `let` binds by value: the type of the local is the type of
                // the value, with no dereference.
                let Some(ty) = self.t.binding_of(b).map(|x| x.ty) else {
                    return unsupported(Construct::NoThir, id.span);
                };
                let by_value = self.t.pat_ty.get(&pat.id).is_none_or(|&p| p == ty)
                    && self.t.pat_adjust.get(&pat.id).is_none_or(Vec::is_empty);
                if !by_value {
                    return unsupported(Construct::LetPattern, pat.span());
                }
                let l = self.user_local(b, id.span)?;
                self.into(init, Place::local(l))
            }
            PatternKind::Wild(_) => {
                let ty = self.ty(init)?;
                let origin = self.origin(init.span, Some(init.id));
                let t = self.temp(ty, TempKind::Discarded, origin);
                self.into(init, Place::local(t))
            }
            _ => unsupported(Construct::LetPattern, pat.span()),
        }
    }

    /// Lowers an expression statement (`docs/ir.md` 5.4):
    ///
    /// ```text
    /// e;  (a value)            =>  t := <e>; Dead(t)
    /// p;  (a place of a local) =>  Mention(p)
    /// ```
    ///
    /// The statement scope ends the temporary.
    fn expr_stmt(&mut self, e: &Expr) -> R<()> {
        if let Some(p) = self.as_place(e)? {
            let origin = self.origin(e.span, Some(e.id));
            self.push(StmtKind::Mention(p), origin);
            return Ok(());
        }
        let ty = self.ty(e)?;
        let origin = self.origin(e.span, Some(e.id));
        let t = self.temp(ty, TempKind::Discarded, origin);
        self.into(e, Place::local(t))
    }

    /// Lowers an assignment to a local (`docs/ir.md` 5.5):
    ///
    /// ```text
    /// x = v   =>  t := <v>; x = move t
    /// ```
    ///
    /// The value runs first, then the target, then the store. The `Assign`
    /// drops the old value.
    fn assign_stmt(&mut self, target: &Expr, op: AssignOp, value: &Expr, s: &Stmt) -> R<()> {
        if op != AssignOp::Assign {
            return unsupported(Construct::CompoundAssign, s.span);
        }
        if !matches!(target.kind, ast::ExprKind::Name(_)) {
            return unsupported(Construct::AssignPlace, target.span);
        }
        let Some(place) = self.as_place(target)? else {
            return unsupported(Construct::AssignPlace, target.span);
        };
        let ty = self.ty(value)?;
        let origin = self.origin(value.span, Some(value.id));
        let t = self.temp(ty, TempKind::Operand, origin);
        self.into(value, Place::local(t))?;
        let origin = self.origin(s.span, None);
        self.assign(place, Rvalue::Use(Operand::Move(Place::local(t))), origin);
        Ok(())
    }
}
