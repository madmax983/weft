//! `scope`, `spawn`, `join`, `detach`, `fork`, `sim.run` and `with_timeout`
//! (`docs/ir.md` 5.29, 5.30, 5.31).
//!
//! A `scope` is a terminator of its site. The scope body is a body of its
//! own, with the site as parent:
//!
//! ```text
//! dest = scope { s => body }  =>  dest = scope k -> [next, unwind: C]
//! body S (Scope k): params _1 = s (ScopeCap); TaskResult locals; upvar locals
//!   ... <body into _0>; ScopeWait(_1, orphans) -> [bb, unwind: C]; <frame end>; Return
//! ```
//!
//! The scope body waits for its tasks after its value is in `_0` and before
//! its locals end (ADR 0006). `ScopeWait` can abort, so `_0` is first in its
//! chain. The chain of each abort in the scope body cancels and joins the
//! tasks at `_1` (`UnwindValue(_1, Drop)`, `cleanup.rs`). As a handled body,
//! the scope body names the locals of the site as upvar locals (`upvar.rs`),
//! and a jump cannot leave it (a fence, W0315).
//!
//! The tasks:
//!
//! ```text
//! h = s.spawn(f)    =>  tf := <f>; spawn site_i(copy s, move tf) -> h, [next]
//! s.spawn(f);       =>  tf := <f>; spawn site_i(copy s, move tf) -> None, [next]
//! x = h.join()      =>  join(move h) -> x, [next, unwind: C]
//! h.detach()        =>  detach(move h) -> [next]; dest = ()
//! dest = fork(f, g) =>  tf := <f>; tg := <g>; dest = fork(move tf, move tg) -> [next, unwind: C]
//! ```
//!
//! A spawn in statement position gives its result to the scope: a
//! `TaskResult` local of the scope body of `s`, with a cell from the entry
//! of the scope body. `ScopeWait` gives it its value, and the frame end ends
//! it. The scope body finds these spawns before it lowers its block
//! ([`result_spawns`]), also in the closures and the bodies inside it, so
//! each chain of the scope body has the locals.
//!
//! `sim.run(seed, workers) { body }` and `with_timeout(d) { body }` are calls
//! of intrinsic functions. A `sim.run` with no `workers` gets the constant
//! argument 4.

use weft_ir::{
    BlockId, BodyKind, Callee, Const, IntTy, LocalDecl, LocalId, LocalKind, Operand, Place, Rvalue,
    ScopeDecl, ScopeId, SpawnDecl, TermKind, Ty, TyId,
};
use weft_syntax::ast::{self, Expr, ExprKind, StmtKind as S};

use super::call::{parts, slots};
use super::closure::{push_children, push_stmt, Node};
use super::frame::{closing, frame_tail};
use super::{id_of, reborrow, unsupported, Builder, Construct, Fence, ScopeKind, R, RET};
use crate::thir::{self, Binder, BindingId, Builtin, Recv, Res, Tables};

/// The number of simulated workers of a `sim.run` that does not give it
/// (ADR 0010).
const WORKERS: i128 = 4;

/// A method call on a task builtin: its receiver mode and its receiver.
type Receiver<'e> = (Recv, &'e Expr);

impl Builder<'_> {
    /// Lowers `scope` expression `e` with body `body` into `dest`
    /// (`docs/ir.md` 5.29): the scope body as a body, then the `Scope`
    /// terminator. The value comes from the frame of the scope body, as a
    /// call result: `dest` gets the `Uninit` of its place fields.
    pub(super) fn scope_into(&mut self, e: &Expr, body: &ast::Block, dest: &Place) -> R<()> {
        let t = self.t;
        let ty = self.ty(e)?;
        let Some(&b) = self.d.pending.binders(t).get(&Binder::Scope(e.id)) else {
            return unsupported(Construct::NoThir, e.span);
        };
        let site = self.site_for(e)?;
        // Reserve the ids: the scope, then the scope body.
        let pending = &mut *self.d.pending;
        let si = pending.scopes.len();
        let sid = ScopeId(pending.base_scope.saturating_add(id_of(si)));
        pending.scopes.push(None);
        pending.scope_ids.insert(e.id, sid);
        let (body_id, slot) = pending.reserve_body();
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
            sub.body_id = body_id;
            sub.parent = Some(self.body_id);
            sub.cap_env = self.cap_env;
            sub.site = Some(Box::new(site));
            sub.scope_body(b, body, sid)?;
            self.diags.append(&mut sub.diags);
            let built = sub.finish(BodyKind::Scope(sid), body.span);
            self.d.pending.put_body(slot, built);
        }
        if let Some(s) = self.d.pending.scopes.get_mut(si) {
            *s = Some(ScopeDecl {
                body: body_id,
                site: self.body_id,
            });
        }
        let origin = self.origin(e.span, Some(e.id));
        let unwind = Some(self.cleanup(origin));
        let next = self.new_block();
        self.terminate(
            TermKind::Scope {
                scope: sid,
                dest: dest.clone(),
                next: BlockId(id_of(next)),
                unwind,
            },
            origin,
        );
        self.enter(next);
        self.unset_fields(dest, ty, &[], origin);
        Ok(())
    }

    /// Lowers the body `block` of scope `sid` with scope capability binding
    /// `b` (`docs/ir.md` 5.1.4, 5.29): the scope capability `_1`, the
    /// `TaskResult` locals, then the value into `_0`, `ScopeWait`, and the
    /// frame end.
    ///
    /// The scopes: the frame (`_1` and the temporaries of the tail), the
    /// fence, a block with the `TaskResult` locals, then the block of the
    /// body. So the frame end ends the block locals, then the results, then
    /// the temporaries of the tail, then `_1`.
    fn scope_body(&mut self, b: BindingId, block: &ast::Block, sid: ScopeId) -> R<()> {
        let end = closing(block.span);
        self.open(ScopeKind::Frame, end);
        let Some(binding) = self.t.binding_of(b) else {
            return unsupported(Construct::NoThir, block.span);
        };
        let (ty, name) = (binding.ty, binding.name.clone());
        let origin = self.origin(block.span, None);
        let props = self.props(ty);
        let cap = self.add_local(LocalDecl {
            ty,
            kind: LocalKind::ScopeCap,
            name: Some(name),
            props,
            in_place: false,
            origin,
        });
        self.vars.insert(b, cap);
        self.params.push(cap);
        if let Some(s) = self.scopes.last_mut() {
            s.locals.push(cap);
        }
        self.open(ScopeKind::Fence(Fence::ScopeBody), end);
        self.open(ScopeKind::Block, end);
        let orphans = self.task_results(b, block, sid)?;
        self.open(ScopeKind::Block, end);
        let tail = frame_tail(block);
        let discard = tail.is_some_and(|x| self.discards(x));
        self.block_stmts(block, Place::local(RET), discard)?;
        // `_0` has its value: `ScopeWait` can abort, so `_0` is first in its
        // chain (`docs/ir.md` 5.1.6).
        self.ret_value = true;
        if self.live {
            let at = self.origin(end, None);
            let unwind = Some(self.cleanup(at));
            let next = self.new_block();
            self.terminate(
                TermKind::ScopeWait {
                    scope: Place::local(cap),
                    orphans,
                    next: BlockId(id_of(next)),
                    unwind,
                },
                at,
            );
            self.enter(next);
        }
        let ret_origin = match tail {
            Some(x) if !discard => self.origin(x.span, Some(x.id)),
            _ => self.origin(block.span, None),
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

    /// Adds a `TaskResult` local for each spawn on scope capability `b` in
    /// statement position in `block` (also in the closures and the bodies
    /// inside it), with `Live` at the current point (the entry), and returns
    /// them. Each one gets its spawn site now; the spawn uses it.
    fn task_results(&mut self, b: BindingId, block: &ast::Block, sid: ScopeId) -> R<Vec<LocalId>> {
        let mut out = Vec::new();
        for x in result_spawns(self.t, b, block) {
            let Some(rty) = self.task_ret(x) else {
                return unsupported(Construct::NoThir, x.span);
            };
            let origin = self.origin(x.span, Some(x.id));
            // The site has the origin of the task argument: the checker
            // names the task by it (`stealable`).
            let Some(arg) = task_arg(x) else {
                return unsupported(Construct::NoThir, x.span);
            };
            let site = self.d.pending.add_spawn(SpawnDecl {
                scope: Some(sid),
                fork: false,
                origin: self.origin(arg.span, Some(arg.id)),
            });
            self.d.pending.results.insert(x.id, site);
            // The result is a `once` value of the scope body (`docs/ir.md`
            // 5.29).
            let mut props = self.props(rty);
            props.once = true;
            let l = self.add_local(LocalDecl {
                ty: rty,
                kind: LocalKind::TaskResult(site),
                name: None,
                props,
                in_place: false,
                origin,
            });
            self.push(weft_ir::StmtKind::Live(l), origin);
            if let Some(s) = self.scopes.last_mut() {
                s.locals.push(l);
            }
            out.push(l);
        }
        Ok(out)
    }

    /// Returns the result type of the task that spawn `x` starts: `T` of
    /// its type `Task<T>`.
    fn task_ret(&self, x: &Expr) -> Option<TyId> {
        let t = *self.t.expr_ty.get(&x.id)?;
        match self.tys.try_get(t) {
            Some(Ty::Adt(_, args)) => args.first().copied(),
            _ => None,
        }
    }

    /// Returns true if `e` is a spawn: a method call `s.spawn(f)` on a scope
    /// capability.
    pub(super) fn is_spawn(&self, e: &Expr) -> bool {
        matches!(e.kind, ExprKind::MethodCall { .. })
            && matches!(
                self.t.call.get(&e.id).map(|c| &c.callee),
                Some(thir::Callee::Builtin(Builtin::Spawn))
            )
    }

    /// Lowers spawn `e` in statement position (`docs/ir.md` 5.29): the spawn
    /// has no destination, and the result goes to the scope.
    pub(super) fn spawn_stmt(&mut self, e: &Expr) -> R<()> {
        let (Some((Some(x), args, trailing)), Some(info)) = (parts(e), self.t.call.get(&e.id))
        else {
            return unsupported(Construct::NoThir, e.span);
        };
        let Some(r) = info.recv else {
            return unsupported(Construct::NoThir, e.span);
        };
        let slots = slots(info, args, trailing, e.span)?;
        self.spawn_into(e, (r, x), &slots, None)
    }

    /// Lowers spawn `e` with receiver `x` and argument `slots` (`docs/ir.md`
    /// 5.29): the scope capability is a place first, the closure is an
    /// operand, then the spawn reads the capability. With no `dest`, the
    /// spawn is in statement position: its site is the one of its
    /// `TaskResult` local, if the scope body has one for it.
    pub(super) fn spawn_into(
        &mut self,
        e: &Expr,
        (r, x): Receiver<'_>,
        slots: &[&Expr],
        dest: Option<Place>,
    ) -> R<()> {
        let [f] = slots else {
            return unsupported(Construct::NoThir, e.span);
        };
        let p = self.receiver_place(x)?;
        let task = self.operand(f, false)?;
        let scope = self.read_receiver(r.mode, p, x)?;
        let origin = self.origin(e.span, Some(e.id));
        // A spawn in statement position whose scope body found it has its
        // site already.
        let reserved = dest
            .is_none()
            .then(|| self.d.pending.results.get(&e.id).copied())
            .flatten();
        let site = if let Some(site) = reserved {
            site
        } else {
            let scope = self.scope_of(x);
            self.d.pending.add_spawn(SpawnDecl {
                scope,
                fork: false,
                origin: self.origin(f.span, Some(f.id)),
            })
        };
        let next = self.new_block();
        self.terminate(
            TermKind::Spawn {
                site,
                scope,
                task,
                dest,
                next: BlockId(id_of(next)),
            },
            origin,
        );
        self.enter(next);
        Ok(())
    }

    /// Returns the scope of scope capability expression `x`: the scope of
    /// `scope { s => .. }` if `x` names `s`. A scope capability that comes
    /// from elsewhere (a parameter) has no static scope.
    fn scope_of(&self, x: &Expr) -> Option<ScopeId> {
        if !matches!(x.kind, ExprKind::Name(_)) {
            return None;
        }
        let Some(Res::Local(b)) = self.t.res.get(&x.id) else {
            return None;
        };
        match self.t.binding_of(*b)?.binder {
            Binder::Scope(se) => self.d.pending.scope_ids.get(&se).copied(),
            _ => None,
        }
    }

    /// Lowers `h.join()` (`e`, receiver `x`) into `dest` (`docs/ir.md`
    /// 5.29): `join(move h) -> dest, [next, unwind: C]`. A failed task
    /// raises its failure at the join. The result comes from the frame of
    /// the task: `dest` gets the `Uninit` of its place fields.
    pub(super) fn join_into(
        &mut self,
        e: &Expr,
        (r, x): Receiver<'_>,
        slots: &[&Expr],
        dest: &Place,
    ) -> R<()> {
        if !slots.is_empty() {
            return unsupported(Construct::NoThir, e.span);
        }
        let p = self.receiver_place(x)?;
        let task = self.read_receiver(r.mode, p, x)?;
        let origin = self.origin(e.span, Some(e.id));
        let unwind = Some(self.cleanup(origin));
        let next = self.new_block();
        self.terminate(
            TermKind::Join {
                task,
                dest: dest.clone(),
                next: BlockId(id_of(next)),
                unwind,
            },
            origin,
        );
        self.enter(next);
        let ty = self.ty(e)?;
        self.unset_fields(dest, ty, &[], origin);
        Ok(())
    }

    /// Lowers `h.detach()` (`e`, receiver `x`) into `dest` (`docs/ir.md`
    /// 5.29): `detach(move h) -> [next]; dest = ()`. It cannot abort.
    pub(super) fn detach_into(
        &mut self,
        e: &Expr,
        (r, x): Receiver<'_>,
        slots: &[&Expr],
        dest: Place,
    ) -> R<()> {
        if !slots.is_empty() {
            return unsupported(Construct::NoThir, e.span);
        }
        let p = self.receiver_place(x)?;
        let task = self.read_receiver(r.mode, p, x)?;
        let origin = self.origin(e.span, Some(e.id));
        let next = self.new_block();
        self.terminate(
            TermKind::Detach {
                task,
                next: BlockId(id_of(next)),
            },
            origin,
        );
        self.enter(next);
        self.assign(dest, Rvalue::Use(super::expr::unit()), origin);
        Ok(())
    }

    /// Lowers `fork(f, g, ..)` (`e`, branches `slots`) into `dest`
    /// (`docs/ir.md` 5.29): each branch is an operand in written order and a
    /// spawn site with no scope; the `Fork` waits for each task and gives
    /// the tuple of the results. It can abort.
    pub(super) fn fork_into(&mut self, e: &Expr, slots: &[&Expr], dest: &Place) -> R<()> {
        let mut branches = Vec::with_capacity(slots.len());
        for (a, skip) in slots.iter().zip(self.skips(slots)) {
            branches.push(self.operand(a, skip)?);
        }
        let mut sites = Vec::with_capacity(slots.len());
        for a in slots {
            let origin = self.origin(a.span, Some(a.id));
            sites.push(self.d.pending.add_spawn(SpawnDecl {
                scope: None,
                fork: true,
                origin,
            }));
        }
        let origin = self.origin(e.span, Some(e.id));
        let unwind = Some(self.cleanup(origin));
        let next = self.new_block();
        self.terminate(
            TermKind::Fork {
                sites,
                branches,
                dest: dest.clone(),
                next: BlockId(id_of(next)),
                unwind,
            },
            origin,
        );
        self.enter(next);
        let ty = self.ty(e)?;
        self.unset_fields(dest, ty, &[], origin);
        Ok(())
    }

    /// Lowers `sim.run(seed, workers) { body }` (`e`) into `dest`
    /// (`docs/ir.md` 5.30): a call of the intrinsic `sim.run` with the
    /// arguments in parameter order. `workers = 4` when the call leaves it
    /// out is a constant argument.
    pub(super) fn sim_run_into(&mut self, e: &Expr, dest: &Place) -> R<()> {
        let (Some((_, args, trailing)), Some(info)) = (parts(e), self.t.call.get(&e.id)) else {
            return unsupported(Construct::NoThir, e.span);
        };
        let thir::Callee::Item { item, targs } = &info.callee else {
            return unsupported(Construct::NoThir, e.span);
        };
        let (item, targs) = (*item, targs.clone());
        // The argument of each parameter: `seed`, `workers`, `body`.
        let mut given: Vec<Option<&Expr>> = Vec::with_capacity(info.args.len());
        for (i, s) in info.args.iter().enumerate() {
            let k = s.map(|k| k as usize);
            let x = match k {
                Some(k) if k < args.len() => args.get(k).map(|a| &a.value),
                Some(k) if k == args.len() => trailing,
                _ => None,
            };
            match (x, i) {
                (Some(x), _) => given.push(Some(x)),
                (None, 1) => given.push(None),
                (None, _) => return unsupported(Construct::NoThir, e.span),
            }
        }
        let present: Vec<&Expr> = given.iter().flatten().copied().collect();
        let mut skips = self.skips(&present).into_iter();
        let mut ops = Vec::with_capacity(given.len());
        for x in given {
            ops.push(match x {
                Some(x) => {
                    let skip = skips.next().unwrap_or(false);
                    self.operand(x, skip)?
                }
                None => Operand::Const(Const::Int(WORKERS, IntTy::U64)),
            });
        }
        let id = self.fn_id(item, e.span)?;
        let origin = self.origin(e.span, Some(e.id));
        let unwind = self.call_can_abort(item, id).then(|| self.cleanup(origin));
        let next = self.new_block();
        self.terminate(
            TermKind::Call {
                callee: Callee::Fn(id, targs),
                args: ops,
                dest: dest.clone(),
                caps: self.cap_args(),
                next: Some(BlockId(id_of(next))),
                unwind,
            },
            origin,
        );
        self.enter(next);
        let ty = self.ty(e)?;
        self.unset_fields(dest, ty, &[], origin);
        Ok(())
    }
}

/// Returns true if `x` is a spawn on scope capability binding `b`:
/// `s.spawn(f)` where `s` names `b`.
fn spawn_on(t: &Tables, x: &Expr, b: BindingId) -> bool {
    let ExprKind::MethodCall { receiver, .. } = &x.kind else {
        return false;
    };
    matches!(
        t.call.get(&x.id).map(|c| &c.callee),
        Some(thir::Callee::Builtin(Builtin::Spawn))
    ) && matches!(receiver.kind, ExprKind::Name(_))
        && t.res.get(&receiver.id) == Some(&Res::Local(b))
}

/// Returns the task argument of spawn `x`: its one argument or its
/// trailing block.
fn task_arg(x: &Expr) -> Option<&Expr> {
    let (_, args, trailing) = parts(x)?;
    args.first().map(|a| &a.value).or(trailing)
}

/// Returns the spawns on scope capability binding `b` that the builder
/// lowers in statement position in `body` (also in the closures and the
/// bodies inside it), in source order. A statement of a block is in
/// statement position, but for the tail. The tail of a loop body and of the
/// block of an `if` with no `else` is a statement too (`looping.rs`,
/// `branch.rs`). Each spawn here reaches `Builder::expr_stmt`. The walk
/// keeps its stack on the heap.
fn result_spawns<'e>(t: &Tables, b: BindingId, body: &'e ast::Block) -> Vec<&'e Expr> {
    let mut out = Vec::new();
    // Each node, and for a block: its tail is a statement.
    let mut stack: Vec<(Node<'e>, bool)> = vec![(Node::Block(body), false)];
    let mut parts: Vec<Node<'e>> = Vec::new();
    while let Some((n, tail_stmt)) = stack.pop() {
        match n {
            Node::Block(blk) => {
                let len = blk.stmts.len();
                for (i, s) in blk.stmts.iter().enumerate() {
                    if let S::Expr(x) = &s.kind {
                        if (i + 1 < len || tail_stmt) && spawn_on(t, x, b) {
                            out.push(x);
                        }
                    }
                    stack.push((Node::Stmt(s), false));
                }
            }
            Node::Stmt(s) => match &s.kind {
                S::While { cond, body } => {
                    stack.push((Node::Expr(cond), false));
                    stack.push((Node::Block(body), true));
                }
                S::For { iter, body, .. } => {
                    stack.push((Node::Expr(iter), false));
                    stack.push((Node::Block(body), true));
                }
                S::Loop(body) => stack.push((Node::Block(body), true)),
                _ => {
                    push_stmt(s, &mut parts);
                    stack.extend(std::mem::take(&mut parts).into_iter().map(|p| (p, false)));
                }
            },
            Node::Expr(x) => {
                if let ExprKind::If {
                    cond,
                    then,
                    else_: None,
                } = &x.kind
                {
                    stack.push((Node::Expr(cond), false));
                    stack.push((Node::Block(then), true));
                    continue;
                }
                push_children(x, &mut parts);
                stack.extend(std::mem::take(&mut parts).into_iter().map(|p| (p, false)));
            }
        }
    }
    out.sort_by_key(|x| x.span.lo);
    out
}
