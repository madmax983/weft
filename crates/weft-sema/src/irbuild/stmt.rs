//! Blocks and statements (`docs/ir.md` 5.3, 5.4, 5.5, 5.11).

use weft_ir::{BinOp, Operand, Place, Rvalue, StmtKind, TempKind};
use weft_syntax::ast::{self, AssignOp, Expr, PatternKind, Stmt, StmtKind as S};

use super::frame::{closing, Jump};
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
    pub(super) fn stmt(&mut self, s: &Stmt) -> R<()> {
        self.open(ScopeKind::Stmt, s.span);
        match &s.kind {
            S::Let { pat, init, .. } => self.let_stmt(pat, init.as_ref(), s)?,
            S::Expr(e) => self.expr_stmt(e)?,
            S::Assign { target, op, value } => self.assign_stmt(target, *op, value, s)?,
            S::Return(e) => self.return_stmt(e.as_ref(), s.span)?,
            S::Break => self.jump(Jump::Break, s.span)?,
            S::Continue => self.jump(Jump::Continue, s.span)?,
            S::While { cond, body } => self.while_loop(cond, body, s.span)?,
            S::For { pat, iter, body } => self.for_loop(pat, iter, body, s.span)?,
            S::Loop(body) => self.loop_loop(body, s.span)?,
            S::Assert(c) => self.assert_stmt(c, s.span)?,
        }
        self.close();
        Ok(())
    }

    /// Lowers `let` (`docs/ir.md` 5.3):
    ///
    /// ```text
    /// let x = e        =>  Live(x); <into(e, x)>
    /// let x: T         =>  Live(x); Uninit(x)      (a tuple: the same for each binding)
    /// let (a, b) = e   =>  t := <e>; Live(a); a = move t.0; Live(b); b = move t.1
    /// let S(a, b) = s  =>  Live(a); a = move s.0; Live(b); b = move s.1; Consume(s)
    /// let _ = e        =>  t := <e>; Dead(t)
    /// ```
    ///
    /// A `let` takes the value: a linear part under `_` moves into a
    /// temporary and ends there. `Consume` only for a struct that can be
    /// linear.
    fn let_stmt(&mut self, pat: &ast::Pattern, init: Option<&Expr>, s: &Stmt) -> R<()> {
        let Some(init) = init else {
            return self.let_uninit(pat);
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
                    return unsupported(Construct::NoThir, pat.span());
                }
                let l = self.user_local(b, id.span)?;
                self.into(init, Place::local(l))
            }
            PatternKind::Wild(_) | PatternKind::Lit(..) => {
                let ty = self.value_ty(init)?;
                let origin = self.origin(init.span, Some(init.id));
                let t = self.temp(ty, TempKind::Discarded, origin);
                self.into(init, Place::local(t))
            }
            PatternKind::Tuple(..) => {
                let ty = self.value_ty(init)?;
                let origin = self.origin(init.span, Some(init.id));
                let t = self.temp(ty, TempKind::Scrutinee, origin);
                self.into(init, Place::local(t))?;
                self.let_pattern(pat, Place::local(t), ty, s)
            }
            PatternKind::Variant { .. } => {
                let (place, ty) = if let Some(p) = self.as_place(init)? {
                    (p, self.value_ty(init)?)
                } else {
                    let ty = self.ty(init)?;
                    let origin = self.origin(init.span, Some(init.id));
                    let t = self.temp(ty, TempKind::Scrutinee, origin);
                    self.value_into(init, Place::local(t))?;
                    (Place::local(t), ty)
                };
                self.let_pattern(pat, place, ty, s)
            }
        }
    }

    /// Binds pattern `pat` of a `let` from place `q` of type `ty`. A `let`
    /// pattern never fails: a test is an error of `typeck` (W0113).
    fn let_pattern(&mut self, pat: &ast::Pattern, q: Place, ty: weft_ir::TyId, s: &Stmt) -> R<()> {
        let plan = self.plan(pat, q, ty)?;
        if plan.has_tests() {
            return unsupported(Construct::NoThir, s.span);
        }
        self.binds(&plan, true)
    }

    /// Lowers an expression statement (`docs/ir.md` 5.4):
    ///
    /// ```text
    /// e;  (a value)            =>  t := <e>; Dead(t)
    /// p;  (a place of a local) =>  Mention(p)
    /// ```
    ///
    /// The statement scope ends the temporary.
    pub(super) fn expr_stmt(&mut self, e: &Expr) -> R<()> {
        if let Some(p) = self.as_place(e)? {
            let origin = self.origin(e.span, Some(e.id));
            self.push(StmtKind::Mention(p), origin);
            return Ok(());
        }
        let ty = self.ty(e)?;
        let origin = self.origin(e.span, Some(e.id));
        let t = self.temp(ty, TempKind::Discarded, origin);
        self.value_into(e, Place::local(t))
    }

    /// Lowers an assignment (`docs/ir.md` 5.5, 5.6):
    ///
    /// ```text
    /// x = v         =>  t := <v>; x = move t
    /// p.f = v       =>  t := <v>; <place p>; p.f = move t
    /// (*r).f = v    =>  t := <v>; [Drop((*r).f)]; (*r).f = move t
    /// ```
    ///
    /// The value runs first, then the target place (its index expressions
    /// too), then the store. The `Assign` drops the old value. Behind a
    /// pointer, `Drop` comes first if the old value can be linear (V17).
    fn assign_stmt(&mut self, target: &Expr, op: AssignOp, value: &Expr, s: &Stmt) -> R<()> {
        let bin = match op {
            AssignOp::Assign => None,
            AssignOp::Add => Some(BinOp::Add),
            AssignOp::Sub => Some(BinOp::Sub),
            AssignOp::Mul => Some(BinOp::Mul),
        };
        if let Some(bin) = bin {
            return self.compound(target, bin, value, s);
        }
        let ty = self.value_ty(value)?;
        let origin = self.origin(value.span, Some(value.id));
        let t = self.temp(ty, TempKind::Operand, origin);
        self.into(value, Place::local(t))?;
        let Some(place) = self.as_place(target)? else {
            return unsupported(Construct::AssignPlace, target.span);
        };
        let origin = self.origin(s.span, None);
        // A capture of a closure body can become `(*env.k)`: its `Drop` stays
        // only then (`closure.rs`).
        let behind = place.has_deref() || self.below_capture(&place);
        if behind && self.maybe_linear(self.value_ty(target)?) {
            self.push(StmtKind::Drop(place.clone()), origin);
        }
        self.assign(place, Rvalue::Use(Operand::Move(Place::local(t))), origin);
        Ok(())
    }

    /// Lowers a compound assignment (`docs/ir.md` 5.7):
    ///
    /// ```text
    /// p += v   =>  t := <v>; t2 := Add(copy p, move t) as T; p = move t2
    /// ```
    ///
    /// `p` is the place after the implicit dereferences of the THIR, so on a
    /// reference local the store writes through it (RT9). A constant value
    /// stays a constant. A place value needs no temporary if the target place
    /// runs no code. The integer type is at the value (`Tables::int_ty`).
    fn compound(&mut self, target: &Expr, bin: BinOp, value: &Expr, s: &Stmt) -> R<()> {
        let skip = self.inert(target);
        let v = self.operand(value, skip)?;
        let Some(place) = self.as_place(target)? else {
            return unsupported(Construct::AssignPlace, target.span);
        };
        let ty = self.value_ty(target)?;
        let origin = self.origin(s.span, None);
        let t2 = self.temp(ty, TempKind::Operand, origin);
        let rv = Rvalue::Binary(bin, self.int_ty(value), Operand::Copy(place.clone()), v);
        self.assign(Place::local(t2), rv, origin);
        self.assign(place, Rvalue::Use(Operand::Move(Place::local(t2))), origin);
        Ok(())
    }
}
