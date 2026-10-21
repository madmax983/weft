//! The frame of a body: its parameters, its value, its end, and the jumps that
//! leave scopes (`docs/ir.md` 5.1.3, 5.1.4, 5.1.5, 5.2, 5.15).

use weft_ir::{LocalDecl, LocalId, LocalKind, Origin, Place, Rvalue, StmtKind, TermKind};
use weft_syntax::ast::{self, Span};

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

    /// Ends each open scope, from the innermost, for a jump out of the frame:
    /// `Dead` of each local of each scope (`docs/ir.md` 5.1.5). The scopes stay
    /// on the stack: the code after the jump closes them, at a point that
    /// cannot run.
    pub(super) fn exit_all(&mut self, origin: Origin) {
        let ends: Vec<LocalId> = self
            .scopes
            .iter()
            .rev()
            .flat_map(|s| s.locals.iter().rev().copied())
            .collect();
        for l in ends {
            self.push(StmtKind::Dead(l), origin);
        }
    }

    /// Lowers `return e` (`docs/ir.md` 5.15): `into(e, _0)`, the end of each
    /// scope of the frame, the end of the parameters, then `Return` with the
    /// origin of `e`.
    pub(super) fn return_stmt(&mut self, value: Option<&ast::Expr>, span: Span) -> R<()> {
        let ret = Place::local(RET);
        let origin = if let Some(e) = value {
            self.into(e, ret)?;
            self.origin(e.span, Some(e.id))
        } else {
            let origin = self.origin(span, None);
            self.assign(ret, Rvalue::Use(super::expr::unit()), origin);
            origin
        };
        self.exit_all(self.origin(span, None));
        self.terminate(TermKind::Return, origin);
        Ok(())
    }
}

/// Returns the tail of block `b`: its last statement, if it is an expression.
pub(super) fn frame_tail(b: &ast::Block) -> Option<&ast::Expr> {
    match b.stmts.last().map(|s| &s.kind) {
        Some(ast::StmtKind::Expr(e)) => Some(e),
        _ => None,
    }
}
