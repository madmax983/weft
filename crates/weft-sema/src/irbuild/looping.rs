//! Loops: `while`, `loop` and `for` (`docs/ir.md` 5.14). The jumps are in
//! `frame.rs`.
//!
//! A loop is a cycle of the CFG. The head is a block of its own. The entry
//! edge comes first, so the head can run if the point before the loop can
//! run ([`Builder::enter`]). The back edge is a `Goto` to the head at the end
//! of each iteration. `continue` is a back edge too, and `break` goes to the
//! exit.
//!
//! Each local that gets a cell in an iteration ends in the same iteration,
//! on each path: at the end of the body, at a `continue`, at a `break`, and
//! on the exit edge of the head. So the head never gives a cell to a local
//! that has one (V5).

use weft_ir::{
    BlockId, IterSource, LocalDecl, LocalKind, Place, Proj, Rvalue, StmtKind, TempKind, TermKind,
    Ty, TyId,
};
use weft_syntax::ast::{self, Expr, ExprKind, Pattern, Span};

use super::frame::closing;
use super::{id_of, unsupported, Builder, Construct, ScopeKind, Targets, R};

impl Builder<'_> {
    /// Starts a loop at the statement at `span`: a new head block, a new exit
    /// block, and the loop scope. No edge enters the head yet: a `for` makes
    /// its iterator first.
    fn open_loop(&mut self, span: Span) -> Targets {
        let t = Targets {
            head: self.new_block(),
            exit: self.new_block(),
        };
        self.open(ScopeKind::Loop(t), closing(span));
        t
    }

    /// Goes from the current point to the head of loop `t`, and makes the
    /// head the current block.
    fn enter_head(&mut self, t: Targets, span: Span) {
        let origin = self.origin(span, None);
        self.goto(t.head, origin);
        self.enter(t.head);
    }

    /// Ends an iteration of loop `t`: the back edge to the head. Then the
    /// exit is the current block, and the loop scope closes there.
    fn close_loop(&mut self, t: Targets, body: &ast::Block) {
        let origin = self.origin(closing(body.span), None);
        self.goto(t.head, origin);
        self.enter(t.exit);
        self.close();
    }

    /// Lowers the body of a loop: a block scope with each statement in a
    /// statement scope of its own, the tail too. So the temporaries of the
    /// tail end at the end of each iteration (`docs/ir.md` 5.1.2, N5), and a
    /// tail value is discarded (5.1.3).
    fn loop_body(&mut self, b: &ast::Block) -> R<()> {
        self.open(ScopeKind::Block, closing(b.span));
        for s in &b.stmts {
            self.stmt(s)?;
        }
        self.close();
        Ok(())
    }

    /// Lowers `while c { b }` (`docs/ir.md` 5.14):
    ///
    /// ```text
    /// head:  Stmt scope { tc := <c> }; Switch(tc) [1: body, otherwise: out]
    /// out:   <Dead of the condition temporaries>; Goto(exit)
    /// body:  <Dead of the condition temporaries>; Block scope { b }; Goto(head)
    /// ```
    ///
    /// A condition that is a place or a constant is the operand itself. The
    /// loop scope opens after the condition: a `break` in the condition
    /// leaves an outer loop, as in `typeck`. With no condition temporary, the
    /// switch goes to the exit itself.
    pub(super) fn while_loop(&mut self, cond: &Expr, body: &ast::Block, span: Span) -> R<()> {
        let head = self.new_block();
        let origin = self.origin(span, None);
        self.goto(head, origin);
        self.enter(head);
        self.open(ScopeKind::Stmt, cond.span);
        let on = self.operand(cond, true)?;
        let ends = self.scopes.pop().map(|s| s.locals).unwrap_or_default();
        let co = self.origin(cond.span, Some(cond.id));
        let start = self.new_block();
        let exit = self.new_block();
        let out = if ends.is_empty() {
            exit
        } else {
            self.new_block()
        };
        self.terminate(
            TermKind::Switch {
                on,
                arms: vec![(1, BlockId(id_of(start)))],
                otherwise: BlockId(id_of(out)),
            },
            co,
        );
        if out != exit {
            self.enter(out);
            self.end_locals(&ends, co);
            self.goto(exit, co);
        }
        self.enter(start);
        self.end_locals(&ends, co);
        let t = Targets { exit, head };
        self.open(ScopeKind::Loop(t), closing(span));
        self.loop_body(body)?;
        self.close_loop(t, body);
        Ok(())
    }

    /// Lowers `loop { b }` (`docs/ir.md` 5.14):
    ///
    /// ```text
    /// head: Block scope { b }; Goto(head)
    /// ```
    ///
    /// Only a `break` goes to the exit. With no `break`, the point after the
    /// loop cannot run.
    pub(super) fn loop_loop(&mut self, body: &ast::Block, span: Span) -> R<()> {
        let t = self.open_loop(span);
        self.enter_head(t, span);
        self.loop_body(body)?;
        self.close_loop(t, body);
        Ok(())
    }

    /// Lowers `for p in e { b }` (`docs/ir.md` 5.14):
    ///
    /// ```text
    ///        it := Iter(elems <place_or_temp e>)     (or Iter(lo..hi))
    /// head:  Live(x); IterNext(it, x) -> [next: body, done: out]
    /// out:   Dead(x); Goto(exit)
    /// body:  Block scope { <bind p from x>; Block scope { b } }; Dead(x); Goto(head)
    /// exit:  Dead(it)
    /// ```
    ///
    /// The source runs before the loop: its temporaries belong to the `for`
    /// statement and end after the iterator. `x` is a temporary of an
    /// iteration scope: `break` and `continue` end it.
    pub(super) fn for_loop(
        &mut self,
        pat: &Pattern,
        iter: &Expr,
        body: &ast::Block,
        span: Span,
    ) -> R<()> {
        let (src, elem, uniq) = self.iter_source(iter)?;
        let origin = self.origin(iter.span, Some(iter.id));
        let it_ty = self.tys.intern(Ty::Iter(elem));
        let mut props = self.props(it_ty);
        props.uniq = uniq;
        let it = self.add_local(LocalDecl {
            ty: it_ty,
            kind: LocalKind::Iterator,
            name: None,
            props,
            in_place: false,
            origin,
        });
        let t = self.open_loop(span);
        self.push(StmtKind::Live(it), origin);
        self.assign(Place::local(it), Rvalue::Iter(src), origin);
        if let Some(s) = self.scopes.last_mut() {
            s.locals.push(it);
        }
        self.enter_head(t, span);
        // The iteration scope: the element `x`.
        self.open(ScopeKind::Stmt, closing(body.span));
        let x = self.temp(elem, TempKind::Scrutinee, origin);
        let (next, out) = (self.new_block(), self.new_block());
        self.terminate(
            TermKind::IterNext {
                iter: Place::local(it),
                dest: Place::local(x),
                next: BlockId(id_of(next)),
                done: BlockId(id_of(out)),
            },
            origin,
        );
        self.enter(out);
        self.end_locals(&[x], origin);
        self.goto(t.exit, origin);
        self.enter(next);
        self.open(ScopeKind::Block, closing(body.span));
        let plan = self.plan(pat, Place::local(x), elem)?;
        // A `for` pattern cannot fail: a test is an error of `typeck`.
        if plan.has_tests() {
            return unsupported(Construct::NoThir, pat.span());
        }
        self.binds(&plan, true)?;
        self.loop_body(body)?;
        self.close();
        self.close();
        self.close_loop(t, body);
        Ok(())
    }

    /// Evaluates the source of a `for` (`docs/ir.md` 5.14): the bounds of a
    /// range, or the place of the elements, of type `[T]`. Returns the source,
    /// the type of each item, and the `@ uniq` mode of the iterator (RT18):
    /// the mode of the local of the place.
    ///
    /// A scalar element is a copy, another element is a reference into the
    /// buffer (the binding mode of `typeck`).
    fn iter_source(&mut self, iter: &Expr) -> R<(IterSource, TyId, bool)> {
        if let ExprKind::Range { lo, hi } = &iter.kind {
            let elem = self.value_ty(lo)?;
            let skip = self.inert(hi);
            let a = self.operand(lo, skip)?;
            let b = self.operand(hi, true)?;
            return Ok((IterSource::Range(a, b), elem, false));
        }
        let mut p = self.place_or_temp(iter)?;
        let ty = self.value_ty(iter)?;
        let elem = match self.tys.try_get(ty) {
            Some(Ty::Slice(x) | Ty::Array(x, _)) => *x,
            _ => match self.tys.lang(ty) {
                Some((weft_ir::ty::Lang::Vec, [x])) => *x,
                _ => return unsupported(Construct::NoThir, iter.span),
            },
        };
        if !matches!(self.tys.try_get(ty), Some(Ty::Slice(_))) {
            // The verifier finds the type `[T]` of the place in the table.
            self.tys.intern(Ty::Slice(elem));
            p.proj.push(Proj::Elems);
        }
        let item = if self.scalar(elem) {
            elem
        } else {
            self.tys.intern(Ty::Ref(elem))
        };
        let uniq = self
            .locals
            .get(p.local.index())
            .is_some_and(|d| d.props.uniq);
        Ok((IterSource::Elems(p), item, uniq))
    }

    /// Returns true if a loop binds a value of type `t` by value: an integer,
    /// `bool`, `()`, `String` or `Duration` (the scalars of `typeck`).
    fn scalar(&self, t: TyId) -> bool {
        match self.tys.try_get(t) {
            Some(Ty::Int(_) | Ty::Bool | Ty::Unit) => true,
            _ => matches!(
                self.tys.lang(t),
                Some((weft_ir::ty::Lang::String | weft_ir::ty::Lang::Duration, _))
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    //! The fence logic of the jumps (`docs/ir.md` 5.1.5): a jump cannot leave
    //! a handled body, a clause or a scope body (W0315). Plan stage B10 adds
    //! the tests with real handled bodies.

    use weft_ir::{TermKind, TyTable};
    use weft_syntax::ast::Span;
    use weft_syntax::diag::Code;

    use super::super::frame::Jump;
    use super::super::unset::PlaceFields;
    use super::super::{Builder, Fence, ScopeKind, Targets};
    use crate::thir::Tables;

    /// Runs `f` on a builder of an empty body with the scopes `kinds`, from
    /// the outermost. The loop scopes have exit `bb1` and head `bb2`.
    fn with_scopes(kinds: &[ScopeKind], f: impl FnOnce(&mut Builder<'_>)) {
        let t = Tables::default();
        let mut tys = TyTable::new();
        let mut fields = PlaceFields::new(&tys);
        let unit = tys.unit();
        let span = Span { lo: 0, hi: 1 };
        let mut b = Builder::new(&t, &mut tys, &mut fields, 0, unit, span);
        b.new_block();
        b.new_block();
        for &k in kinds {
            b.open(k, span);
        }
        f(&mut b);
    }

    /// The loop scope of the tests.
    const LOOP: ScopeKind = ScopeKind::Loop(Targets { exit: 1, head: 2 });

    /// Returns the terminator of block 0.
    fn term0(b: &Builder<'_>) -> Option<TermKind> {
        b.blocks
            .first()
            .and_then(|d| d.term.as_ref().map(|t| t.kind.clone()))
    }

    #[test]
    fn a_break_out_of_a_handled_body_is_w0315() {
        let kinds = [
            ScopeKind::Frame,
            LOOP,
            ScopeKind::Fence(Fence::Handled),
            ScopeKind::Stmt,
        ];
        with_scopes(&kinds, |b| {
            assert!(b.jump(Jump::Break, Span { lo: 3, hi: 8 }).is_ok());
            assert_eq!(b.diags.len(), 1);
            let d = &b.diags[0];
            assert_eq!(d.code, Code::W0315);
            assert_eq!(d.message, "`break` cannot leave a handled body");
            assert_eq!(term0(b), Some(TermKind::Unreachable));
            assert!(!b.live);
        });
    }

    #[test]
    fn a_continue_out_of_a_scope_body_is_w0315() {
        let kinds = [ScopeKind::Frame, LOOP, ScopeKind::Fence(Fence::ScopeBody)];
        with_scopes(&kinds, |b| {
            assert!(b.jump(Jump::Continue, Span { lo: 3, hi: 8 }).is_ok());
            let msgs: Vec<&str> = b.diags.iter().map(|d| d.message.as_str()).collect();
            assert_eq!(msgs, ["`continue` cannot leave a scope body"]);
            assert_eq!(term0(b), Some(TermKind::Unreachable));
        });
    }

    #[test]
    fn a_return_out_of_a_clause_is_w0315() {
        let kinds = [ScopeKind::Frame, ScopeKind::Fence(Fence::Clause)];
        with_scopes(&kinds, |b| {
            assert!(b.return_stmt(None, Span { lo: 3, hi: 9 }).is_ok());
            let msgs: Vec<&str> = b.diags.iter().map(|d| d.message.as_str()).collect();
            assert_eq!(msgs, ["`return` cannot leave a handler clause"]);
            assert_eq!(term0(b), Some(TermKind::Unreachable));
        });
    }

    #[test]
    fn a_jump_inside_a_fence_is_valid() {
        let kinds = [
            ScopeKind::Frame,
            ScopeKind::Fence(Fence::Handled),
            LOOP,
            ScopeKind::Stmt,
        ];
        with_scopes(&kinds, |b| {
            assert!(b.jump(Jump::Break, Span { lo: 3, hi: 8 }).is_ok());
            assert!(b.diags.is_empty());
            assert_eq!(term0(b), Some(TermKind::Goto(weft_ir::BlockId(1))));
        });
    }

    #[test]
    fn a_closure_frame_stops_a_break() {
        // A closure body is a frame: a `break` in it cannot go to a loop
        // outside it. That is W0111 of `typeck`, so the THIR is wrong here.
        let kinds = [ScopeKind::Frame, LOOP, ScopeKind::Frame, ScopeKind::Stmt];
        with_scopes(&kinds, |b| {
            let r = b.jump(Jump::Break, Span { lo: 3, hi: 8 });
            assert!(r.is_err());
            assert!(b.diags.is_empty());
        });
    }

    #[test]
    fn a_jump_at_a_point_that_cannot_run_reports_nothing() {
        let kinds = [ScopeKind::Frame, LOOP, ScopeKind::Fence(Fence::Handled)];
        with_scopes(&kinds, |b| {
            b.terminate(TermKind::Unreachable, b.origin(Span { lo: 0, hi: 1 }, None));
            assert!(b.jump(Jump::Break, Span { lo: 3, hi: 8 }).is_ok());
            assert!(b.diags.is_empty());
        });
    }

    #[test]
    fn a_break_ends_the_scopes_inside_the_loop_only() {
        let kinds = [ScopeKind::Frame, LOOP, ScopeKind::Block, ScopeKind::Stmt];
        with_scopes(&kinds, |b| {
            for (i, l) in [(0, 7_u32), (1, 8), (2, 9), (3, 10)] {
                if let Some(s) = b.scopes.get_mut(i) {
                    s.locals.push(weft_ir::LocalId(l));
                }
            }
            assert!(b.jump(Jump::Break, Span { lo: 3, hi: 8 }).is_ok());
            let ends: Vec<weft_ir::StmtKind> = b
                .blocks
                .first()
                .map(|d| d.stmts.iter().map(|s| s.kind.clone()).collect())
                .unwrap_or_default();
            assert_eq!(
                ends,
                [
                    weft_ir::StmtKind::Dead(weft_ir::LocalId(10)),
                    weft_ir::StmtKind::Dead(weft_ir::LocalId(9)),
                ]
            );
        });
    }
}
