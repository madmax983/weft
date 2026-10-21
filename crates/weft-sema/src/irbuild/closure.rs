//! Closures and rule CAPTURE (`docs/ir.md` 5.1.7, 5.22).
//!
//! A closure literal is an aggregate in the body that makes it (the maker) and
//! a body of its own. The builder builds the closure body with a builder of
//! its own, in which each captured variable is a field of the environment:
//! `env.k`. Then [`capture_mode`] reads the closure body and gives the mode of
//! each capture (rule CAPTURE):
//!
//! 1. `ByMove` if the body moves or consumes a place at or below `env.k` (an
//!    inner closure that moves the variable moves `env.k` in its aggregate);
//! 2. else `Kept` if the variable is plain data and the body borrows no place
//!    at or below `env.k` that is not behind a reference;
//! 3. else `ByRef`.
//!
//! A `ByRef` capture is `(*env.k)` in the closure body, so the builder puts the
//! `Deref` into each place of the capture after the modes are known
//! ([`Builder::rewrite_captures`]). The maker then writes the aggregate:
//!
//! ```text
//! te := Aggregate(Closure(c))(<operand of each capture>)
//!       &x (ByRef: a temporary), move x (ByMove), copy x (Kept: the cell)
//! ```
//!
//! A capture of a closure inside a closure body names the capture of the
//! maker (`env.j` or `(*env.j)`): [`weft_ir::Capture::source`] is a place.

use std::collections::{HashMap, HashSet};

use weft_ir::{
    AggKind, Body, BodyId, BodyKind, Callee, CapOperand, Capture, CaptureMode, ClosureDecl,
    ClosureId, DerefKind, FieldIdx, IterSource, LocalDecl, LocalId, LocalKind, Operand, Place,
    Proj, Props, Rvalue, StmtKind, TempKind, TermKind, Ty, TyId,
};
use weft_syntax::ast::{self, Expr, ExprKind, Lit, StrPart};

use super::frame::closing;
use super::{id_of, unsupported, Builder, Construct, Decls, ScopeKind, R, RET};
use crate::thir::{BindingId, Res};

/// The bodies and the closures that the builder makes inside one function or
/// test, before the body of the function gets its id. The ids are reserved in
/// the order of the closure literals (pre-order), so the maker of a closure
/// has a lower id than the closure body.
#[derive(Debug, Default)]
pub(super) struct Pending {
    /// The id of the body of the function or test.
    pub(super) base_body: u32,
    /// The id of the first closure.
    pub(super) base_closure: u32,
    /// The closure bodies, by id after `base_body`.
    pub(super) bodies: Vec<Option<Body>>,
    /// The closure declarations, by id from `base_closure`.
    pub(super) closures: Vec<Option<ClosureDecl>>,
}

impl Pending {
    /// Makes an empty set for the function body with id `base_body`.
    pub(super) const fn new(base_body: u32, base_closure: u32) -> Self {
        Self {
            base_body,
            base_closure,
            bodies: Vec::new(),
            closures: Vec::new(),
        }
    }

    /// Returns the declaration of closure `c`, if it is in this set.
    fn closure_mut(&mut self, c: ClosureId) -> Option<&mut ClosureDecl> {
        let i = c.index().checked_sub(self.base_closure as usize)?;
        self.closures.get_mut(i).and_then(Option::as_mut)
    }
}

/// One captured variable of a closure body.
#[derive(Clone, Debug)]
pub(super) struct Cap {
    /// The place of the variable in the maker, before the maker knows its own
    /// capture modes (`env.j` for a capture of the maker).
    source: Place,
    /// The type of the variable.
    ty: TyId,
    /// The properties of the variable in the maker.
    props: Props,
}

/// The captures of a closure body.
#[derive(Debug)]
pub(super) struct Captures {
    /// The environment local.
    pub(super) env: LocalId,
    /// The captures, in the order of the fields of the environment.
    caps: Vec<Cap>,
    /// The field of each captured binding.
    index: HashMap<BindingId, usize>,
}

impl Captures {
    /// Returns the place `env.k` of captured binding `b`.
    pub(super) fn place(&self, b: BindingId) -> Option<Place> {
        let k = *self.index.get(&b)?;
        Some(Place {
            local: self.env,
            proj: vec![Proj::Field(FieldIdx(id_of(k)))],
        })
    }

    /// Returns the field `k` if place `p` is `env.k` and nothing more.
    fn whole_field(&self, p: &Place) -> Option<usize> {
        match p.proj.as_slice() {
            [Proj::Field(k)] if p.local == self.env => Some(k.index()),
            _ => None,
        }
    }

    /// Returns the field `k` if place `p` is at or below `env.k`.
    fn field_of(&self, p: &Place) -> Option<usize> {
        match p.proj.first() {
            Some(Proj::Field(k)) if p.local == self.env => Some(k.index()),
            _ => None,
        }
    }
}

/// Returns the mode of capture `k` of a closure body (rule CAPTURE,
/// `docs/ir.md` 5.1.7), from the uses that `uses` records and the properties
/// of the variable.
const fn capture_mode(uses: Uses, copy: bool) -> CaptureMode {
    if uses.moved {
        CaptureMode::ByMove
    } else if copy && !uses.borrowed {
        CaptureMode::Kept
    } else {
        CaptureMode::ByRef
    }
}

/// What a closure body does with one capture.
#[derive(Clone, Copy, Debug, Default)]
struct Uses {
    /// A `Move` or a `Consume` of a place at or below `env.k`.
    moved: bool,
    /// A borrow of a place at or below `env.k` that is not behind a reference.
    borrowed: bool,
}

/// Returns true if a borrow of place `p` (at or below `env.k`) borrows the cell
/// of the variable: no `Deref(Ref)` is on the path after `env.k`.
fn borrows_cell(p: &Place) -> bool {
    !p.proj
        .iter()
        .skip(1)
        .any(|x| *x == Proj::Deref(DerefKind::Ref))
}

impl Builder<'_> {
    /// Returns the place of binding `b` in this body: its local, or the field
    /// of the environment that captures it.
    pub(super) fn binding_place(&self, b: BindingId) -> Option<Place> {
        if let Some(&l) = self.vars.get(&b) {
            return Some(Place::local(l));
        }
        self.closure.as_ref().and_then(|c| c.place(b))
    }

    /// Returns the type and the properties of binding `b` in this body.
    fn binding_props(&self, b: BindingId) -> Option<(Place, TyId, Props)> {
        if let Some(&l) = self.vars.get(&b) {
            let d = self.locals.get(l.index())?;
            return Some((Place::local(l), d.ty, d.props));
        }
        let c = self.closure.as_ref()?;
        let k = *c.index.get(&b)?;
        let cap = c.caps.get(k)?;
        Some((c.place(b)?, cap.ty, cap.props))
    }

    /// Returns true if a read of place `p` of type `ty` copies it: the type is
    /// plain data, and a whole local (or a whole capture) holds no `once`
    /// closure (`docs/ir.md` 5.21: a `once` closure moves at its call).
    pub(super) fn copies(&self, p: &Place, ty: TyId) -> bool {
        if self.tys.not_copy(ty) {
            return false;
        }
        self.place_props(p).is_none_or(|x| x.copy)
    }

    /// Returns the properties of a whole local or a whole capture `p`: they
    /// can hold the modes of a closure that the type does not show.
    fn place_props(&self, p: &Place) -> Option<Props> {
        if p.is_local() {
            return self.locals.get(p.local.index()).map(|d| d.props);
        }
        let c = self.closure.as_ref()?;
        let k = c.whole_field(p)?;
        c.caps.get(k).map(|x| x.props)
    }

    /// Returns true if place `p` is at or below a capture of this closure
    /// body. Its mode is not known yet: a store there gets a `Drop` first if
    /// the capture can become `ByRef` ([`Builder::rewrite_captures`] removes
    /// it otherwise).
    pub(super) fn below_capture(&self, p: &Place) -> bool {
        self.closure
            .as_ref()
            .is_some_and(|c| c.field_of(p).is_some())
    }

    /// Lowers closure literal `e` into `dest` (`docs/ir.md` 5.22).
    pub(super) fn closure_into(
        &mut self,
        e: &Expr,
        params: &[ast::Param],
        body: &Expr,
        dest: &Place,
    ) -> R<()> {
        let t = self.t;
        let Some(info) = t.closure.get(&e.id) else {
            return unsupported(Construct::NoThir, e.span);
        };
        let ty = self.ty(e)?;
        if info.params.len() != params.len() {
            return unsupported(Construct::NoThir, e.span);
        }
        // The captured variables: each name of the body that this body can
        // resolve, in the order of the first use.
        let mut caps = Vec::new();
        let mut index = HashMap::new();
        for b in free_bindings(t, body) {
            if let Some((source, ty, props)) = self.binding_props(b) {
                // Capabilities, continuations and scopes in closures come
                // with their constructs (plan stages B10, B11).
                match self.tys.try_get(ty) {
                    Some(Ty::Cap(_) | Ty::Cont(..)) => {
                        return unsupported(Construct::Handle, e.span)
                    }
                    Some(Ty::Scope) => return unsupported(Construct::Scope, e.span),
                    _ => {}
                }
                index.insert(b, caps.len());
                caps.push(Cap { source, ty, props });
            }
        }
        // Reserve the ids: the closure body after the bodies that the
        // function makes so far.
        let pending = &mut *self.d.pending;
        let (bi, ci) = (pending.bodies.len(), pending.closures.len());
        let body_id = BodyId(
            pending
                .base_body
                .saturating_add(1)
                .saturating_add(id_of(bi)),
        );
        let cid = ClosureId(pending.base_closure.saturating_add(id_of(ci)));
        pending.bodies.push(None);
        pending.closures.push(None);
        let (built, modes) = {
            let d = Decls {
                a: self.d.a,
                fns: &mut *self.d.fns,
                items: &mut *self.d.items,
                cap_envs: self.d.cap_envs,
                pending: &mut *self.d.pending,
            };
            let mut sub = Box::new(Builder::new(
                t,
                &mut *self.tys,
                &mut *self.fields,
                d,
                self.unit,
                info.ret,
                e.span,
            ));
            sub.body_id = body_id;
            sub.cap_env = self.cap_env;
            sub.closure_body(e, ty, &info.params, body, caps.clone(), index)?;
            let modes = sub.capture_modes();
            sub.rewrite_captures(&modes);
            self.diags.append(&mut sub.diags);
            let mut built = sub.finish(BodyKind::Closure(cid), e.span);
            built.parent = Some(self.body_id);
            built.cap_env = self.cap_env;
            (built, modes)
        };
        let once = caps
            .iter()
            .zip(&modes)
            .any(|(c, m)| *m == CaptureMode::ByMove && !c.props.copy);
        let decl = ClosureDecl {
            body: body_id,
            maker: self.body_id,
            captures: caps
                .iter()
                .zip(&modes)
                .map(|(c, &mode)| Capture {
                    source: c.source.clone(),
                    mode,
                })
                .collect(),
            once,
            cap_env: self.cap_env,
        };
        let pending = &mut *self.d.pending;
        if let Some(slot) = pending.bodies.get_mut(bi) {
            *slot = Some(built);
        }
        if let Some(slot) = pending.closures.get_mut(ci) {
            *slot = Some(decl);
        }
        self.made.push(cid);
        // The environment: one operand for each capture, in order.
        let origin = self.origin(e.span, Some(e.id));
        let mut ops = Vec::with_capacity(caps.len());
        for (c, &mode) in caps.iter().zip(&modes) {
            ops.push(match mode {
                CaptureMode::ByRef => {
                    let rty = self.tys.intern(Ty::Ref(c.ty));
                    let tr = self.temp(rty, TempKind::Operand, origin);
                    self.assign(Place::local(tr), Rvalue::Ref(c.source.clone()), origin);
                    Operand::Move(Place::local(tr))
                }
                CaptureMode::ByMove => Operand::Move(c.source.clone()),
                CaptureMode::Kept | CaptureMode::Cap | CaptureMode::Kont => {
                    Operand::Copy(c.source.clone())
                }
            });
        }
        self.assign(
            dest.clone(),
            Rvalue::Aggregate(AggKind::Closure(cid), ops),
            origin,
        );
        // A local that the closure goes into gets the modes of the closure.
        if dest.is_local() {
            let p = self.closure_props(ty, &caps, &modes, once);
            if let Some(d) = self.locals.get_mut(dest.local.index()) {
                d.props = join(d.props, p);
            }
        }
        Ok(())
    }

    /// Returns the properties of a closure of type `ty` with captures `caps`
    /// (`docs/ir.md` 5.22): linear if a field is linear, `once` if a `ByMove`
    /// field is not plain data (or a field is `@ uniq`), nonportable if a field
    /// is. A `once` closure is not plain data: a read of it moves it.
    fn closure_props(&self, ty: TyId, caps: &[Cap], modes: &[CaptureMode], once: bool) -> Props {
        let mut p = self.props(ty);
        for (c, &mode) in caps.iter().zip(modes) {
            let f = match mode {
                CaptureMode::ByRef => {
                    let mut f = self
                        .tys
                        .find(&Ty::Ref(c.ty))
                        .map_or(c.props, |r| self.props(r));
                    f.nonportable |= c.props.nonportable;
                    f.holds_refs = true;
                    f
                }
                _ => c.props,
            };
            p.linear |= f.linear;
            p.on_abort &= f.on_abort;
            p.nonportable |= f.nonportable;
            p.holds_refs |= f.holds_refs;
            p.generic |= f.generic;
            p.once |= f.uniq || (mode == CaptureMode::ByMove && f.once);
        }
        p.once |= once;
        p.copy = !once;
        p
    }

    /// Lowers the body of closure literal `e` of type `ty` (`docs/ir.md`
    /// 5.22): the environment `_1`, the parameters, then the value into `_0`
    /// and the frame end.
    ///
    /// ```text
    /// body c (Closure):  params _1 = env, _2 = p; _0
    ///   bb0: <body into _0>; <frame end>; Return
    /// ```
    fn closure_body(
        &mut self,
        e: &Expr,
        ty: TyId,
        params: &[BindingId],
        body: &Expr,
        caps: Vec<Cap>,
        index: HashMap<BindingId, usize>,
    ) -> R<()> {
        let end = closing(e.span);
        self.open(ScopeKind::Frame, end);
        let origin = self.origin(e.span, Some(e.id));
        let props = self.props(ty);
        let env = self.add_local(LocalDecl {
            ty,
            kind: LocalKind::Env,
            name: None,
            props,
            in_place: false,
            origin,
        });
        self.params.push(env);
        self.closure = Some(Box::new(Captures { env, caps, index }));
        for (i, &b) in params.iter().enumerate() {
            let Some(binding) = self.t.binding_of(b) else {
                return unsupported(Construct::NoThir, e.span);
            };
            let (bty, name) = (binding.ty, binding.name.clone());
            let props = self.props(bty);
            let l = self.add_local(LocalDecl {
                ty: bty,
                kind: LocalKind::Param(id_of(i)),
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
        // A by-value parameter is built in place (ADR 0007).
        for i in 1..self.params.len() {
            let Some(&l) = self.params.get(i) else {
                continue;
            };
            let lty = self.local_ty(l);
            for path in self.fields.of(self.tys, lty).iter() {
                let place = Place {
                    local: l,
                    proj: path.proj.clone(),
                };
                self.push(StmtKind::Uninit(place), origin);
            }
        }
        let ret = Place::local(RET);
        let unit = self.tys.unit();
        let bty = self.ty(body)?;
        let discard =
            self.local_ty(RET) == unit && bty != unit && self.tys.try_get(bty) != Some(&Ty::Never);
        if discard {
            self.expr_stmt_scoped(body)?;
            if self.live {
                self.assign(ret, Rvalue::Use(super::expr::unit()), origin);
            }
        } else {
            self.into(body, ret)?;
        }
        self.ret_value = true;
        // The origin of `Return` is the expression whose value leaves the
        // frame (V18): the body, or the closure if the body has no value.
        let ret_origin = if discard {
            origin
        } else {
            self.origin(body.span, Some(body.id))
        };
        self.close();
        if self.live {
            self.terminate(TermKind::Return, ret_origin);
        } else if self.cur.is_some() {
            self.terminate(TermKind::Unreachable, self.origin(end, None));
        }
        Ok(())
    }

    /// Lowers `e` as an expression statement in a statement scope of its own.
    fn expr_stmt_scoped(&mut self, e: &Expr) -> R<()> {
        self.open(ScopeKind::Stmt, e.span);
        self.expr_stmt(e)?;
        self.close();
        Ok(())
    }

    /// Returns the mode of each capture of this closure body (rule CAPTURE).
    fn capture_modes(&self) -> Vec<CaptureMode> {
        let Some(c) = self.closure.as_ref() else {
            return Vec::new();
        };
        let mut uses = vec![Uses::default(); c.caps.len()];
        let mut note = |p: &Place, moved: bool| {
            if let Some(u) = c.field_of(p).and_then(|k| uses.get_mut(k)) {
                if moved {
                    u.moved = true;
                } else if borrows_cell(p) {
                    u.borrowed = true;
                }
            }
        };
        for blk in &self.blocks {
            for s in &blk.stmts {
                match &s.kind {
                    StmtKind::Consume(p) | StmtKind::Bounds(_, Operand::Move(p)) => note(p, true),
                    StmtKind::Assign(_, rv) => match rv {
                        Rvalue::Ref(p) | Rvalue::Iter(IterSource::Elems(p)) => note(p, false),
                        _ => each_operand_rv(rv, &mut |o| {
                            if let Operand::Move(p) = o {
                                note(p, true);
                            }
                        }),
                    },
                    StmtKind::Print(ops) => {
                        for o in ops {
                            if let Operand::Move(p) = o {
                                note(p, true);
                            }
                        }
                    }
                    _ => {}
                }
            }
            if let Some(term) = &blk.term {
                each_operand_term(&term.kind, &mut |o| {
                    if let Operand::Move(p) = o {
                        note(p, true);
                    }
                });
            }
        }
        c.caps
            .iter()
            .zip(uses)
            .map(|(cap, u)| capture_mode(u, cap.props.copy))
            .collect()
    }

    /// Puts the `Deref` of each `ByRef` capture into each place of it
    /// (`env.k` becomes `(*env.k)`), also into the sources of the closures that
    /// this body makes. A `Drop` before a store into a capture that is not
    /// `ByRef` goes away: only a place behind a pointer gets one (V17).
    fn rewrite_captures(&mut self, modes: &[CaptureMode]) {
        let Some(env) = self.closure.as_ref().map(|c| c.env) else {
            return;
        };
        let by_ref: Vec<bool> = modes.iter().map(|m| *m == CaptureMode::ByRef).collect();
        let field = |p: &Place| match p.proj.first() {
            Some(Proj::Field(k)) if p.local == env => Some(k.index()),
            _ => None,
        };
        let fix = |p: &mut Place| {
            if field(p).is_some_and(|k| by_ref.get(k).copied().unwrap_or(false)) {
                p.proj.insert(1, Proj::Deref(DerefKind::Ref));
            }
        };
        for blk in &mut self.blocks {
            blk.stmts.retain(|s| match &s.kind {
                StmtKind::Drop(p) => {
                    p.has_deref()
                        || field(p).is_none_or(|k| by_ref.get(k).copied().unwrap_or(false))
                }
                _ => true,
            });
            for s in &mut blk.stmts {
                each_place_stmt(&mut s.kind, &mut |p| fix(p));
            }
            if let Some(t) = &mut blk.term {
                each_place_term(&mut t.kind, &mut |p| fix(p));
            }
        }
        for &c in &self.made {
            if let Some(d) = self.d.pending.closure_mut(c) {
                for cap in &mut d.captures {
                    fix(&mut cap.source);
                }
            }
        }
        // `&T` for each `ByRef` capture: the verifier finds the type of the
        // field in the table (V8).
        if let Some(c) = self.closure.as_ref() {
            let tys: Vec<TyId> = c
                .caps
                .iter()
                .zip(modes)
                .filter(|(_, m)| **m == CaptureMode::ByRef)
                .map(|(x, _)| x.ty)
                .collect();
            for t in tys {
                self.tys.intern(Ty::Ref(t));
            }
        }
    }
}

/// Returns the properties `a` joined with the properties `b` of a closure that
/// the same local can hold.
const fn join(a: Props, b: Props) -> Props {
    Props {
        copy: a.copy && b.copy,
        linear: a.linear || b.linear,
        on_abort: a.on_abort && b.on_abort,
        once: a.once || b.once,
        immovable: a.immovable || b.immovable,
        nonportable: a.nonportable || b.nonportable,
        uniq: a.uniq || b.uniq,
        callable: a.callable || b.callable,
        generic: a.generic || b.generic,
        holds_refs: a.holds_refs || b.holds_refs,
    }
}

/// Returns the bindings that the names of expression `e` resolve to, in the
/// order of their first use. The bindings that `e` itself makes are in the
/// list too: the maker cannot resolve them, so they are not captures.
fn free_bindings(t: &crate::thir::Tables, e: &Expr) -> Vec<BindingId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack: Vec<Node<'_>> = vec![Node::Expr(e)];
    while let Some(n) = stack.pop() {
        match n {
            Node::Expr(x) => {
                if let (ExprKind::Name(_), Some(Res::Local(b))) = (&x.kind, t.res.get(&x.id)) {
                    if seen.insert(*b) {
                        out.push(*b);
                    }
                }
                push_children(x, &mut stack);
            }
            Node::Block(b) => {
                for s in b.stmts.iter().rev() {
                    stack.push(Node::Stmt(s));
                }
            }
            Node::Stmt(s) => push_stmt(s, &mut stack),
        }
    }
    out
}

/// A node of the walk of [`free_bindings`].
#[derive(Clone, Copy)]
enum Node<'e> {
    /// An expression.
    Expr(&'e Expr),
    /// A block.
    Block(&'e ast::Block),
    /// A statement.
    Stmt(&'e ast::Stmt),
}

/// Pushes the parts of statement `s` onto `stack`, the last first.
fn push_stmt<'e>(s: &'e ast::Stmt, stack: &mut Vec<Node<'e>>) {
    use ast::StmtKind as S;
    match &s.kind {
        S::Let { init, .. } => {
            if let Some(x) = init {
                stack.push(Node::Expr(x));
            }
        }
        S::Expr(x) | S::Assert(x) => stack.push(Node::Expr(x)),
        S::Assign { target, value, .. } => {
            stack.push(Node::Expr(target));
            stack.push(Node::Expr(value));
        }
        S::Return(x) => {
            if let Some(x) = x {
                stack.push(Node::Expr(x));
            }
        }
        S::Break | S::Continue => {}
        S::While { cond, body } => {
            stack.push(Node::Block(body));
            stack.push(Node::Expr(cond));
        }
        S::For { iter, body, .. } => {
            stack.push(Node::Block(body));
            stack.push(Node::Expr(iter));
        }
        S::Loop(body) => stack.push(Node::Block(body)),
    }
}

/// Pushes the parts of expression `e` onto `stack`, the last first.
fn push_children<'e>(e: &'e Expr, stack: &mut Vec<Node<'e>>) {
    let mut v: Vec<Node<'e>> = Vec::new();
    match &e.kind {
        ExprKind::Lit(Lit::Str(parts)) => {
            for p in parts {
                if let StrPart::Interp(x) = p {
                    v.push(Node::Expr(x));
                }
            }
        }
        ExprKind::Lit(_) | ExprKind::Name(_) => {}
        ExprKind::Field { base, .. } => v.push(Node::Expr(base)),
        ExprKind::Index { base, index } => {
            v.push(Node::Expr(base));
            if let Some(i) = index {
                v.push(Node::Expr(i));
            }
        }
        ExprKind::Call {
            callee,
            args,
            trailing,
        } => {
            v.push(Node::Expr(callee));
            v.extend(args.iter().map(|a| Node::Expr(&a.value)));
            if let Some(x) = trailing {
                v.push(Node::Expr(x));
            }
        }
        ExprKind::MethodCall {
            receiver,
            args,
            trailing,
            ..
        } => {
            v.push(Node::Expr(receiver));
            v.extend(args.iter().map(|a| Node::Expr(&a.value)));
            if let Some(x) = trailing {
                v.push(Node::Expr(x));
            }
        }
        ExprKind::Unary { expr, .. } => v.push(Node::Expr(expr)),
        ExprKind::Binary { lhs, rhs, .. } => {
            v.push(Node::Expr(lhs));
            v.push(Node::Expr(rhs));
        }
        ExprKind::Range { lo, hi } => {
            v.push(Node::Expr(lo));
            v.push(Node::Expr(hi));
        }
        ExprKind::Tuple(xs) | ExprKind::Array(xs) => v.extend(xs.iter().map(Node::Expr)),
        ExprKind::StructLit { fields, .. } => v.extend(fields.iter().map(|(_, x)| Node::Expr(x))),
        ExprKind::Closure { body, .. } => v.push(Node::Expr(body)),
        ExprKind::Block(b) => v.push(Node::Block(b)),
        ExprKind::If { cond, then, else_ } => {
            v.push(Node::Expr(cond));
            v.push(Node::Block(then));
            if let Some(x) = else_ {
                v.push(Node::Expr(x));
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            v.push(Node::Expr(scrutinee));
            v.extend(arms.iter().map(|a| Node::Expr(&a.body)));
        }
        ExprKind::Handle { clauses, body, .. } => {
            v.extend(clauses.iter().map(|c| Node::Block(&c.body)));
            v.push(Node::Expr(body));
        }
        ExprKind::Scope { body, .. } => v.push(Node::Block(body)),
    }
    stack.extend(v.into_iter().rev());
}

/// Calls `f` on each operand of right side `rv`.
fn each_operand_rv(rv: &Rvalue, f: &mut impl FnMut(&Operand)) {
    match rv {
        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => f(o),
        Rvalue::Binary(_, _, a, b) | Rvalue::Iter(IterSource::Range(a, b)) => {
            f(a);
            f(b);
        }
        Rvalue::Aggregate(_, ops) | Rvalue::Concat(ops) => ops.iter().for_each(f),
        Rvalue::Ref(_) | Rvalue::Len(_) | Rvalue::Discriminant(_) | Rvalue::Iter(_) => {}
    }
}

/// Calls `f` on each operand of terminator `k`.
fn each_operand_term(k: &TermKind, f: &mut impl FnMut(&Operand)) {
    match k {
        TermKind::Switch { on, .. } => f(on),
        TermKind::Call { callee, args, .. } => {
            if let Callee::Value(o) = callee {
                f(o);
            }
            args.iter().for_each(f);
        }
        TermKind::Perform { args, .. } => args.iter().for_each(f),
        TermKind::Resume { arg, .. } => f(arg),
        TermKind::Spawn { scope, task, .. } => {
            f(scope);
            f(task);
        }
        TermKind::Join { task, .. } | TermKind::Detach { task, .. } => f(task),
        TermKind::Fork { branches, .. } => branches.iter().for_each(f),
        TermKind::Assert { cond, .. } => f(cond),
        TermKind::Goto(_)
        | TermKind::Return
        | TermKind::UnwindExit
        | TermKind::Unreachable
        | TermKind::Handle { .. }
        | TermKind::Scope { .. }
        | TermKind::ScopeWait { .. }
        | TermKind::IterNext { .. } => {}
    }
}

/// Calls `f` on each place of operand `o`.
fn op_place(o: &mut Operand, f: &mut impl FnMut(&mut Place)) {
    match o {
        Operand::Copy(p) | Operand::Move(p) => f(p),
        Operand::Const(_) => {}
    }
}

/// Calls `f` on each place of statement `k`.
fn each_place_stmt(k: &mut StmtKind, f: &mut impl FnMut(&mut Place)) {
    match k {
        StmtKind::Live(_) | StmtKind::Dead(_) | StmtKind::UnwindKont(_) => {}
        StmtKind::Assign(p, rv) => {
            f(p);
            match rv {
                Rvalue::Use(o) | Rvalue::Unary(_, _, o) => op_place(o, f),
                Rvalue::Binary(_, _, a, b) | Rvalue::Iter(IterSource::Range(a, b)) => {
                    op_place(a, f);
                    op_place(b, f);
                }
                Rvalue::Aggregate(_, ops) | Rvalue::Concat(ops) => {
                    for o in ops {
                        op_place(o, f);
                    }
                }
                Rvalue::Ref(q)
                | Rvalue::Len(q)
                | Rvalue::Discriminant(q)
                | Rvalue::Iter(IterSource::Elems(q)) => f(q),
            }
        }
        StmtKind::Drop(p)
        | StmtKind::Consume(p)
        | StmtKind::Uninit(p)
        | StmtKind::Mention(p)
        | StmtKind::UnwindValue(p, _) => f(p),
        StmtKind::Bounds(p, o) => {
            f(p);
            op_place(o, f);
        }
        StmtKind::Print(ops) => {
            for o in ops {
                op_place(o, f);
            }
        }
    }
}

/// Calls `f` on each place of terminator `k`.
fn each_place_term(k: &mut TermKind, f: &mut impl FnMut(&mut Place)) {
    match k {
        TermKind::Goto(_) | TermKind::Return | TermKind::UnwindExit | TermKind::Unreachable => {}
        TermKind::Switch { on, .. } => op_place(on, f),
        TermKind::Call {
            callee, args, dest, ..
        } => {
            if let Callee::Value(o) = callee {
                op_place(o, f);
            }
            for o in args {
                op_place(o, f);
            }
            f(dest);
        }
        TermKind::Perform {
            cap, args, dest, ..
        } => {
            if let CapOperand::Local(p) = cap {
                f(p);
            }
            for o in args {
                op_place(o, f);
            }
            f(dest);
        }
        TermKind::Resume {
            kont, arg, dest, ..
        } => {
            f(kont);
            op_place(arg, f);
            f(dest);
        }
        TermKind::Handle { dest, .. } | TermKind::Scope { dest, .. } => f(dest),
        TermKind::ScopeWait { scope, .. } => f(scope),
        TermKind::Spawn {
            scope, task, dest, ..
        } => {
            op_place(scope, f);
            op_place(task, f);
            if let Some(d) = dest {
                f(d);
            }
        }
        TermKind::Join { task, dest, .. } => {
            op_place(task, f);
            f(dest);
        }
        TermKind::Detach { task, .. } => op_place(task, f),
        TermKind::Fork { branches, dest, .. } => {
            for o in branches {
                op_place(o, f);
            }
            f(dest);
        }
        TermKind::Assert { cond, .. } => op_place(cond, f),
        TermKind::IterNext { iter, dest, .. } => {
            f(iter);
            f(dest);
        }
    }
}

/// Returns the blocks of `pending` in body order after the body of the
/// function, or `None` if a reserved body or closure has no value (a bug of
/// the builder).
pub(super) fn take_pending(pending: Pending) -> Option<(Vec<Body>, Vec<ClosureDecl>)> {
    let bodies: Option<Vec<Body>> = pending.bodies.into_iter().collect();
    let closures: Option<Vec<ClosureDecl>> = pending.closures.into_iter().collect();
    Some((bodies?, closures?))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_moved_capture_is_by_move_and_a_borrowed_plain_capture_is_by_ref() {
        let moved = Uses {
            moved: true,
            borrowed: true,
        };
        assert_eq!(capture_mode(moved, true), CaptureMode::ByMove);
        let borrowed = Uses {
            moved: false,
            borrowed: true,
        };
        assert_eq!(capture_mode(borrowed, true), CaptureMode::ByRef);
        assert_eq!(capture_mode(Uses::default(), true), CaptureMode::Kept);
        assert_eq!(capture_mode(Uses::default(), false), CaptureMode::ByRef);
    }

    #[test]
    fn a_borrow_through_a_captured_reference_does_not_borrow_the_cell() {
        let env = LocalId(1);
        let at = |proj: Vec<Proj>| Place { local: env, proj };
        assert!(borrows_cell(&at(vec![Proj::Field(FieldIdx(0))])));
        assert!(borrows_cell(&at(vec![
            Proj::Field(FieldIdx(0)),
            Proj::Field(FieldIdx(1))
        ])));
        assert!(!borrows_cell(&at(vec![
            Proj::Field(FieldIdx(0)),
            Proj::Deref(DerefKind::Ref),
            Proj::Field(FieldIdx(1))
        ])));
        assert!(borrows_cell(&at(vec![
            Proj::Field(FieldIdx(0)),
            Proj::Deref(DerefKind::Box)
        ])));
    }
}
