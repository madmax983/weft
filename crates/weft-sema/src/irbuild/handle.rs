//! `handle`, clauses and `resume` (`docs/ir.md` 5.24 to 5.27).
//!
//! A `handle` is a terminator of its site. The handled body and each clause
//! are bodies of their own, with the site as parent:
//!
//! ```text
//! dest = handle E { op_i(params) { clause_i } } in body
//!   =>  dest = handle h -> [next, unwind: C]
//! body H (Handled h):  cap _1 = the new capability of E; upvar locals; _0
//! body K_i (Clause h, op_i):  params; kont = resume; upvar locals; _0
//! ```
//!
//! The handled body runs in a new capability environment that binds `E` to
//! its capability local. A clause runs in the environment of the site,
//! without the new capability. Both name the locals of the site as upvar
//! locals (`upvar.rs`), and a jump cannot leave them (a fence, W0315).
//!
//! `resume(v)` is `tv := <v>; t = resume(kont, move tv) -> [next, unwind: C]`.
//! The cleanup chain of a clause starts with `UnwindKont` of its
//! continuation (V16).

use weft_ir::{
    BodyId, BodyKind, CapEnv, Const, HandlerDecl, HandlerId, LocalDecl, LocalId, LocalKind, OpIdx,
    Operand, Place, TermKind, Ty, TyId,
};
use weft_syntax::ast::{self, Expr};

use super::frame::{closing, frame_tail};
use super::{id_of, reborrow, unsupported, Builder, Construct, Fence, ScopeKind, R, RET};
use crate::thir::{Binder, BindingId};

impl Builder<'_> {
    /// Lowers `handle` expression `e` into `dest` (`docs/ir.md` 5.24): the
    /// handled body and the clauses as bodies, then the `Handle` terminator.
    pub(super) fn handle_into(
        &mut self,
        e: &Expr,
        clauses: &[ast::HandlerClause],
        body: &Expr,
        dest: &Place,
    ) -> R<()> {
        let t = self.t;
        let Some(info) = t.handle.get(&e.id) else {
            return unsupported(Construct::NoThir, e.span);
        };
        if info.clauses.len() != clauses.len() {
            return unsupported(Construct::NoThir, e.span);
        }
        let mut ops = Vec::with_capacity(clauses.len());
        for (c, op) in clauses.iter().zip(&info.clauses) {
            match op {
                Some(op) => ops.push(*op),
                None => return unsupported(Construct::NoThir, c.span),
            }
        }
        let ty = self.ty(e)?;
        let effect = info.effect;
        let site = self.site_for(e)?;
        // Reserve the ids: the handler, the handled body, then the clauses.
        let pending = &mut *self.d.pending;
        let hi = pending.handlers.len();
        let hid = HandlerId(pending.base_handler.saturating_add(id_of(hi)));
        pending.handlers.push(None);
        let (handled, handled_slot) = self.d.pending.reserve_body();
        let clause_ids: Vec<(BodyId, usize)> = clauses
            .iter()
            .map(|_| self.d.pending.reserve_body())
            .collect();
        // The handled body: its capability local `_1` binds the effect.
        let env = self.new_cap_env(CapEnv {
            parent: Some(self.cap_env),
            adds: vec![(effect, Place::local(LocalId(1)))],
        });
        {
            let d = reborrow(&mut self.d);
            let mut sub = Box::new(Builder::new(
                t,
                &mut *self.tys,
                &mut *self.fields,
                d,
                self.unit,
                ty,
                body.span,
            ));
            sub.body_id = handled;
            sub.parent = Some(self.body_id);
            sub.cap_env = env;
            sub.site = Some(Box::new(site.clone()));
            sub.handled_body(effect, body)?;
            self.diags.append(&mut sub.diags);
            let built = sub.finish(BodyKind::Handled(hid), body.span);
            self.d.pending.put_body(handled_slot, built);
        }
        let mut decl_clauses = Vec::with_capacity(clauses.len());
        for (ci, ((c, &op), (cid, slot))) in clauses.iter().zip(&ops).zip(clause_ids).enumerate() {
            let d = reborrow(&mut self.d);
            let mut sub = Box::new(Builder::new(
                t,
                &mut *self.tys,
                &mut *self.fields,
                d,
                self.unit,
                ty,
                c.span,
            ));
            sub.body_id = cid;
            sub.parent = Some(self.body_id);
            sub.cap_env = self.cap_env;
            sub.site = Some(Box::new(site.clone()));
            sub.clause_body(e, id_of(ci), c, (effect, op), ty)?;
            self.diags.append(&mut sub.diags);
            let built = sub.finish(BodyKind::Clause(hid, OpIdx(op)), c.span);
            self.d.pending.put_body(slot, built);
            decl_clauses.push((OpIdx(op), cid));
        }
        if let Some(slot) = self.d.pending.handlers.get_mut(hi) {
            *slot = Some(HandlerDecl {
                effect,
                clauses: decl_clauses,
                handled,
                site: self.body_id,
                multi: info.multi,
            });
        }
        // The site: the `Handle` terminator. Its `unwind` is for an abort
        // that goes past the handler.
        let origin = self.origin(e.span, Some(e.id));
        let unwind = Some(self.cleanup(origin));
        let next = self.new_block();
        self.terminate(
            TermKind::Handle {
                handler: hid,
                dest: dest.clone(),
                next: weft_ir::BlockId(id_of(next)),
                unwind,
            },
            origin,
        );
        self.enter(next);
        // The value comes from the frame of the handled body or of a clause:
        // it is built in place, as a call result (`docs/ir.md` 5.17).
        self.unset_fields(dest, ty, &[], origin);
        Ok(())
    }

    /// Lowers handled body `body` of effect `effect` (`docs/ir.md` 5.24): the
    /// capability local `_1`, then the value into `_0` and the frame end.
    /// The capability ends with the parameters, after the locals.
    fn handled_body(&mut self, effect: weft_ir::EffectId, body: &Expr) -> R<()> {
        let end = closing(body.span);
        self.open(ScopeKind::Frame, end);
        let origin = self.origin(body.span, Some(body.id));
        let ty = self.tys.intern(Ty::Cap(effect));
        let name = self
            .tys
            .effects()
            .get(effect.index())
            .map(|d| d.name.clone());
        let props = self.props(ty);
        let cap = self.add_local(LocalDecl {
            ty,
            kind: LocalKind::Cap(effect),
            name,
            props,
            in_place: false,
            origin,
        });
        if let Some(s) = self.scopes.last_mut() {
            s.locals.push(cap);
        }
        self.cap_params.push((effect, cap));
        self.caps.push((effect, Place::local(cap)));
        self.open(ScopeKind::Fence(Fence::Handled), end);
        self.value_frame(body, origin, end)
    }

    /// Lowers clause `c` (number `ci`) of `handle` expression `e` for
    /// operation `op` of `effect` (`docs/ir.md` 5.24, 5.27): the parameters,
    /// the continuation, then the value of the clause block into `_0` (of
    /// type `ty`, the type of the `handle`) and the frame end. The
    /// continuation ends after the locals, before the parameters.
    fn clause_body(
        &mut self,
        e: &Expr,
        ci: u32,
        c: &ast::HandlerClause,
        (effect, op): (weft_ir::EffectId, u32),
        ty: TyId,
    ) -> R<()> {
        let end = closing(c.body.span);
        self.open(ScopeKind::Frame, end);
        let origin = self.origin(c.span, None);
        for i in 0..c.params.len() {
            let k = id_of(i);
            let Some((b, pty, name)) = self.binder(Binder::ClauseParam(e.id, ci, k)) else {
                return unsupported(Construct::NoThir, c.span);
            };
            let props = self.props(pty);
            let l = self.add_local(LocalDecl {
                ty: pty,
                kind: LocalKind::Param(k),
                name: Some(name),
                props,
                in_place: false,
                origin,
            });
            self.vars.insert(b, l);
            self.params.push(l);
            if let Some(s) = self.scopes.last_mut() {
                s.locals.push(l);
            }
        }
        let decl = self
            .tys
            .effects()
            .get(effect.index())
            .and_then(|d| d.ops.get(op as usize))
            .map(|o| (o.multi, o.ret));
        let Some((multi, op_ret)) = decl else {
            return unsupported(Construct::NoThir, c.span);
        };
        let resume = self.binder(Binder::Resume(e.id, ci));
        let kty = match &resume {
            Some((_, kty, _)) => *kty,
            None => self.tys.intern(Ty::Cont(op_ret, ty)),
        };
        // A `multi` continuation is plain data: a closure copies it. A `once`
        // one moves (`docs/ir.md` 5.27).
        let mut props = self.props(kty);
        props.copy = multi;
        props.once = !multi;
        let k = self.add_local(LocalDecl {
            ty: kty,
            kind: LocalKind::Kont(multi),
            name: Some("resume".to_string()),
            props,
            in_place: false,
            origin,
        });
        if let Some((b, _, _)) = resume {
            self.vars.insert(b, k);
        }
        if let Some(s) = self.scopes.last_mut() {
            s.locals.push(k);
        }
        self.kont = Some(k);
        self.kont_multi = multi;
        self.unset_params(c.span);
        self.open(ScopeKind::Fence(Fence::Clause), end);
        let tail = frame_tail(&c.body);
        let discard = tail.is_some_and(|x| self.discards(x));
        self.block_into(&c.body, Place::local(RET), discard)?;
        self.ret_value = true;
        let ret_origin = match tail {
            Some(x) if !discard => self.origin(x.span, Some(x.id)),
            _ => self.origin(c.body.span, None),
        };
        while !self.scopes.is_empty() {
            self.close();
        }
        if self.live {
            self.terminate(TermKind::Return, ret_origin);
        } else if self.cur.is_some() {
            self.terminate(TermKind::Unreachable, self.origin(end, None));
        }
        Ok(())
    }

    /// Returns the binding of `binder`, its type and its name.
    fn binder(&mut self, binder: Binder) -> Option<(BindingId, TyId, String)> {
        let b = *self.d.pending.binders(self.t).get(&binder)?;
        let x = self.t.binding_of(b)?;
        Some((b, x.ty, x.name.clone()))
    }

    /// Lowers `resume(v)` with continuation binding `b` into `dest`
    /// (`docs/ir.md` 5.27): the continuation is the `Kont` local of the
    /// clause, a `Kont` field of a closure environment, or an upvar local of
    /// the continuation in a nested body.
    pub(super) fn resume_into(
        &mut self,
        e: &Expr,
        b: BindingId,
        slots: &[&Expr],
        dest: Place,
    ) -> R<()> {
        let Some(kont) = self.binding_place(b) else {
            return unsupported(Construct::NoThir, e.span);
        };
        let arg = match slots {
            [a] => self.operand(a, true)?,
            [] => Operand::Const(Const::Unit),
            _ => return unsupported(Construct::NoThir, e.span),
        };
        let origin = self.origin(e.span, Some(e.id));
        let unwind = Some(self.cleanup(origin));
        let next = self.new_block();
        self.terminate(
            TermKind::Resume {
                kont,
                arg,
                dest,
                next: weft_ir::BlockId(id_of(next)),
                unwind,
            },
            origin,
        );
        self.enter(next);
        Ok(())
    }
}
