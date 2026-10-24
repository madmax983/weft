//! Branches: `if`, `&&`, `||` and `match` (`docs/ir.md` 5.12, 5.13).
//!
//! Each branch writes its value into the destination itself. The temporaries
//! of the condition and of the scrutinee belong to the statement around the
//! branch. Each branch has a statement scope of its own: its temporaries end
//! at the end of the branch, before the join.
//!
//! The builder makes only forward edges here, so a block that it enters has
//! all its edges in when it enters it ([`Builder::enter`]).

use weft_ir::{Operand, Place, Rvalue, TempKind, TermKind};
use weft_syntax::ast::{self, Expr};

use super::{Builder, ScopeKind, R};

impl Builder<'_> {
    /// Lowers `if` into `dest` (`docs/ir.md` 5.12):
    ///
    /// ```text
    /// tc := <c>; Switch(tc) [1: bbA, otherwise: bbB]
    /// bbA: into(a, dest); Goto(join)      bbB: into(b, dest); Goto(join)
    /// ```
    ///
    /// A condition that is a place or a constant is the operand itself: no
    /// code can run between the read and the switch. With no `else`, the
    /// value of the `then` block is dropped (its tail place moves into a
    /// `Discarded` temporary, 5.1.3) and `dest` gets `()` on each path.
    pub(super) fn if_into(
        &mut self,
        cond: &Expr,
        then: &ast::Block,
        else_: Option<&Expr>,
        e: &Expr,
        dest: Place,
    ) -> R<()> {
        let on = self.operand(cond, true)?;
        let origin = self.origin(e.span, Some(e.id));
        let (a, b, join) = (self.new_block(), self.new_block(), self.new_block());
        self.terminate(
            TermKind::Switch {
                on,
                arms: vec![(1, super::BlockId(super::id_of(a)))],
                otherwise: super::BlockId(super::id_of(b)),
            },
            origin,
        );
        self.enter(a);
        self.open(ScopeKind::Stmt, then.span);
        if else_.is_none() {
            self.block_drop_into(then, dest.clone())?;
        } else {
            self.block_into(then, dest.clone(), false)?;
        }
        self.close();
        self.goto(join, origin);
        self.enter(b);
        match else_ {
            Some(x) => {
                self.open(ScopeKind::Stmt, x.span);
                self.into(x, dest)?;
                self.close();
            }
            None => self.assign(dest, Rvalue::Use(super::expr::unit()), origin),
        }
        self.goto(join, origin);
        self.enter(join);
        Ok(())
    }

    /// Lowers `a && b` (`and`) or `a || b` into `dest` (`docs/ir.md` 5.12):
    ///
    /// ```text
    /// a && b  =>  dest = <a>; Switch(copy dest) [0: done, otherwise: bbB]
    ///             bbB: dest = <b>; Goto(done)
    /// ```
    ///
    /// `a || b` skips `b` on `1`.
    pub(super) fn and_or_into(
        &mut self,
        and: bool,
        lhs: &Expr,
        rhs: &Expr,
        e: &Expr,
        dest: Place,
    ) -> R<()> {
        self.into(lhs, dest.clone())?;
        let origin = self.origin(e.span, Some(e.id));
        let (b, done) = (self.new_block(), self.new_block());
        self.terminate(
            TermKind::Switch {
                on: Operand::Copy(dest.clone()),
                arms: vec![(u128::from(!and), super::BlockId(super::id_of(done)))],
                otherwise: super::BlockId(super::id_of(b)),
            },
            origin,
        );
        self.enter(b);
        self.open(ScopeKind::Stmt, rhs.span);
        self.into(rhs, dest)?;
        self.close();
        self.goto(done, origin);
        self.enter(done);
        Ok(())
    }

    /// Lowers `match` into `dest` (`docs/ir.md` 5.13):
    ///
    /// ```text
    /// s := <place_or_temp e>
    /// test_i:   the tests of P_i, in pre-order; a failed test goes to test_i+1
    ///           Block scope { <bind P_i from s>; into(a_i, dest) }; Goto(join)
    /// test_n+1: Unreachable
    /// ```
    ///
    /// The first arm that matches wins. No binding and no move comes before
    /// the last test of its arm. An arm with no test that can fail ends the
    /// tests: the later arms cannot run.
    pub(super) fn match_into(
        &mut self,
        scrut: &Expr,
        arms: &[ast::Arm],
        e: &Expr,
        dest: &Place,
    ) -> R<()> {
        let origin = self.origin(e.span, Some(e.id));
        let (s, ty, temp) = if let Some(p) = self.as_place(scrut)? {
            (p, self.value_ty(scrut)?, false)
        } else {
            let ty = self.ty(scrut)?;
            let o = self.origin(scrut.span, Some(scrut.id));
            let t = self.temp(ty, TempKind::Scrutinee, o);
            self.value_into(scrut, Place::local(t))?;
            (Place::local(t), ty, true)
        };
        let join = self.new_block();
        for arm in arms {
            let plan = self.plan(&arm.pat, s.clone(), ty)?;
            let next = self.tests(&plan);
            // The arm takes the value if it moves a part of it, or if the
            // value is a temporary.
            let takes = temp || plan.moves;
            self.open(ScopeKind::Block, arm.span);
            self.binds(&plan, takes)?;
            self.open(ScopeKind::Stmt, arm.body.span);
            self.into(&arm.body, dest.clone())?;
            self.close();
            self.close();
            self.goto(join, origin);
            if let Some(n) = next {
                self.enter(n);
            } else {
                self.cur = None;
                self.live = false;
            }
        }
        // W0120 says that the arms cover each value.
        if self.cur.is_some() {
            self.terminate(TermKind::Unreachable, origin);
        }
        self.enter(join);
        Ok(())
    }
}
