//! The frame of a body: its parameters, its value, its end, and the jumps that
//! leave scopes (`docs/ir.md` 5.1.3, 5.1.4, 5.1.5, 5.2, 5.15).

use weft_ir::{LocalDecl, LocalId, LocalKind, Origin, Place, Rvalue, StmtKind, TermKind};
use weft_syntax::ast::{self, Span};
use weft_syntax::diag::{Code, Diagnostic};

use super::{unsupported, Builder, Construct, ScopeKind, Src, R, RET};
use crate::thir::{Binder, BindingId};

/// Returns the location of the closing brace of a block at `span`.
pub(super) const fn closing(span: Span) -> Span {
    Span {
        lo: span.hi.saturating_sub(1),
        hi: span.hi,
    }
}

impl Builder<'_> {
    /// Lowers the body `src` (`docs/ir.md` 5.2):
    ///
    /// ```text
    /// params _1.._n (cells at the entry), _0
    /// bb0: <body block into _0>; <frame end>; Return
    /// ```
    pub(super) fn body(&mut self, src: &Src<'_>) -> R<()> {
        let end = closing(src.block.span);
        self.open(ScopeKind::Frame, end);
        for (i, &uniq) in src.params.iter().enumerate() {
            let l = self.param(i, uniq, src.span)?;
            self.params.push(l);
            if let Some(s) = self.scopes.last_mut() {
                s.locals.push(l);
            }
        }
        self.unset_params(src.span);
        let tail = frame_tail(src.block);
        let ret = Place::local(RET);
        let discard = tail.is_some_and(|e| self.discards(e));
        self.block_into(src.block, ret, discard)?;
        // The origin of `Return` is the expression whose value leaves the
        // frame: the tail, or the block if it has no tail (V18).
        let origin = match tail {
            Some(e) if !discard => self.origin(e.span, Some(e.id)),
            _ => self.origin(src.block.span, None),
        };
        self.close();
        if self.live {
            self.terminate(TermKind::Return, origin);
        } else if self.cur.is_some() {
            self.terminate(TermKind::Unreachable, self.origin(end, None));
        }
        Ok(())
    }

    /// Adds the local of parameter `i`. It has a cell at the entry.
    fn param(&mut self, i: usize, uniq: bool, span: Span) -> R<LocalId> {
        let k = super::id_of(i);
        let found = self
            .t
            .bindings
            .iter()
            .position(|b| b.binder == Binder::Param(k));
        let Some((b, binding)) = found.and_then(|p| {
            self.t
                .bindings
                .get(p)
                .map(|x| (BindingId(super::id_of(p)), x))
        }) else {
            return unsupported(Construct::NoThir, span);
        };
        let (ty, name) = (binding.ty, binding.name.clone());
        let mut props = self.props(ty);
        props.uniq = uniq;
        let l = self.add_local(LocalDecl {
            ty,
            kind: LocalKind::Param(k),
            name: Some(name),
            props,
            in_place: false,
            origin: self.origin(span, None),
        });
        self.vars.insert(b, l);
        Ok(l)
    }

    /// Writes `Uninit` for each place field of each by-value parameter
    /// (ADR 0007): a by-value parameter is built in place, so its place
    /// fields have no value at the entry (`irbuild/unset.rs`).
    fn unset_params(&mut self, span: Span) {
        let origin = self.origin(span, None);
        for i in 0..self.params.len() {
            let Some(&l) = self.params.get(i) else {
                continue;
            };
            let ty = self.local_ty(l);
            for path in self.fields.of(self.tys, ty).iter() {
                let place = Place {
                    local: l,
                    proj: path.proj.clone(),
                };
                self.push(StmtKind::Uninit(place), origin);
            }
        }
    }

    /// Returns true if the tail `e` of the frame body does not give the value
    /// of the frame: `_0` is `()` and the tail has another type. The body
    /// then drops the value of the tail, as an expression statement.
    fn discards(&self, e: &ast::Expr) -> bool {
        let unit = self.tys.unit();
        let tail = self.t.expr_ty.get(&e.id).copied();
        self.local_ty(RET) == unit
            && tail.is_some_and(|t| t != unit && self.tys.try_get(t) != Some(&weft_ir::Ty::Never))
    }

    /// Closes the innermost scope: `Dead` of each of its locals, in reverse
    /// order (`docs/ir.md` 5.1.3). At a point that cannot run, no statement is
    /// necessary.
    pub(super) fn close(&mut self) {
        let Some(s) = self.scopes.pop() else {
            return;
        };
        if !self.live {
            return;
        }
        let origin = self.origin(s.end, None);
        for &l in s.locals.iter().rev() {
            self.push(StmtKind::Dead(l), origin);
        }
    }

    /// Writes `Dead` of `locals` in reverse order with `origin`, if the point
    /// can run.
    pub(super) fn end_locals(&mut self, locals: &[LocalId], origin: Origin) {
        if !self.live {
            return;
        }
        for &l in locals.iter().rev() {
            self.push(StmtKind::Dead(l), origin);
        }
    }

    /// Ends the scopes from index `depth` of the stack to the innermost, for a
    /// jump out of them: `Dead` of each local of each scope, from the
    /// innermost (`docs/ir.md` 5.1.5). The scopes stay on the stack: the code
    /// after the jump closes them, at a point that cannot run.
    fn exit_to(&mut self, depth: usize, origin: Origin) {
        let ends: Vec<LocalId> = self
            .scopes
            .iter()
            .skip(depth)
            .flat_map(|s| s.locals.iter().copied())
            .collect();
        self.end_locals(&ends, origin);
    }

    /// Returns the index of the scope that jump `j` goes to (`docs/ir.md`
    /// 5.1.5): the innermost loop for `break` and `continue`, the innermost
    /// frame for `return`. A fence stops the search: the builder reports
    /// W0315 if the point can run, and gives `None`. A `break` or a
    /// `continue` with no loop in its frame is W0111 of `typeck`, so the
    /// THIR is wrong.
    fn jump_scope(&mut self, j: Jump, span: Span) -> R<Option<usize>> {
        for (i, s) in self.scopes.iter().enumerate().rev() {
            match (s.kind, j) {
                (ScopeKind::Fence(f), _) => {
                    if self.live {
                        let text = format!("`{}` cannot leave a {}", j.word(), f.name());
                        self.diags.push(Diagnostic::error(Code::W0315, text, span));
                    }
                    return Ok(None);
                }
                (ScopeKind::Loop(_), Jump::Break | Jump::Continue)
                | (ScopeKind::Frame, Jump::Return) => return Ok(Some(i)),
                (ScopeKind::Frame, _) => break,
                _ => {}
            }
        }
        unsupported(Construct::NoThir, span)
    }

    /// Lowers `break` or `continue` (`docs/ir.md` 5.14, 5.1.5): the end of
    /// each scope inside the loop, from the innermost, then `Goto` to the
    /// exit or the head. A jump out of a fence is W0315: the path ends with
    /// `Unreachable`.
    pub(super) fn jump(&mut self, j: Jump, span: Span) -> R<()> {
        let origin = self.origin(span, None);
        let Some(i) = self.jump_scope(j, span)? else {
            self.terminate(TermKind::Unreachable, origin);
            return Ok(());
        };
        let target = match self.scopes.get(i).map(|s| s.kind) {
            Some(ScopeKind::Loop(t)) => match j {
                Jump::Continue => t.head,
                _ => t.exit,
            },
            _ => return unsupported(Construct::NoThir, span),
        };
        self.exit_to(i + 1, origin);
        self.goto(target, origin);
        Ok(())
    }

    /// Lowers `return e` (`docs/ir.md` 5.15): `into(e, _0)`, the end of each
    /// scope of the frame (the parameters last), then `Return` with the
    /// origin of `e`. A `return` out of a fence is W0315: the value is a
    /// discarded expression statement, and the path ends with `Unreachable`.
    pub(super) fn return_stmt(&mut self, value: Option<&ast::Expr>, span: Span) -> R<()> {
        let Some(depth) = self.jump_scope(Jump::Return, span)? else {
            if let Some(e) = value {
                self.expr_stmt(e)?;
            }
            self.terminate(TermKind::Unreachable, self.origin(span, None));
            return Ok(());
        };
        let ret = Place::local(RET);
        let origin = if let Some(e) = value {
            self.into(e, ret)?;
            self.origin(e.span, Some(e.id))
        } else {
            let origin = self.origin(span, None);
            self.assign(ret, Rvalue::Use(super::expr::unit()), origin);
            origin
        };
        self.exit_to(depth, self.origin(span, None));
        self.terminate(TermKind::Return, origin);
        Ok(())
    }
}

/// A jump statement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Jump {
    /// `break`.
    Break,
    /// `continue`.
    Continue,
    /// `return`.
    Return,
}

impl Jump {
    /// Returns the keyword of the jump.
    const fn word(self) -> &'static str {
        match self {
            Self::Break => "break",
            Self::Continue => "continue",
            Self::Return => "return",
        }
    }
}

/// Returns the tail of block `b`: its last statement, if it is an expression.
pub(super) fn frame_tail(b: &ast::Block) -> Option<&ast::Expr> {
    match b.stmts.last().map(|s| &s.kind) {
        Some(ast::StmtKind::Expr(e)) => Some(e),
        _ => None,
    }
}
