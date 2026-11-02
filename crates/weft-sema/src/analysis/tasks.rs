//! Tasks in the analysis (`docs/ir.md` 6.6, plan stage F18).
//!
//! A `scope` runs its scope body from the state before it: the scope body
//! splices into the component of its site (`docs/ir.md` 6.5), so the
//! states of the scope body are in the terms of the site. The value of the
//! `scope` is the value of `_0` of the scope body at its `Return`s.
//!
//! A spawn runs the task body as a run of a closure with no arguments, at
//! the spawn: the state after the spawn has the changes of the task (a may
//! analysis; the task can run at any time until the end of the scope). The
//! handle of the task holds the task site (`AbsVal::tasks`) and the value of
//! the result of the task: a `join` gives the result. A spawn statement
//! gives its result to its `TaskResult` local at `ScopeWait`.
//!
//! The task sets of the handles are may sets. A `join` ends each task of a
//! site of its handle only if no other value can hold a handle of the site
//! ([`must_join`]): each task of the site that still runs is in the handle. A handle that
//! leaves the values of the component (to a callee, behind a reference,
//! into a task, or by a `detach`) makes its site *lost* (`State::lost_tasks`):
//! a task of that site can still run, so a later `join` of a handle of the
//! site does not end it.

use std::collections::BTreeSet;

use weft_ir::{BodyId, LocalKind, Operand, Place, ScopeId, SpawnId, Ty, TyId};

use super::domain::{AbsVal, Key, PathStep, State, Tree};
use super::transfer::{self, Cx};
use crate::factgen::alpha::AlphaError;
use crate::props::ir_props;

/// The task site that stands for a task of a caller (plan stage F18).
///
/// It is the task of the handle in parameter `i` of a function body, or in
/// capture `i` of a closure body. A `join` of such a handle on each path to the
/// `Return` is the part `joins` of the summary (O3-9).
pub const fn iface(i: u32) -> SpawnId {
    SpawnId(u32::MAX - i)
}

/// The parameter or capture index of an interface site ([`iface`]).
pub const fn iface_index(s: SpawnId) -> Option<u32> {
    let d = u32::MAX - s.0;
    if d < 0x1_0000 {
        Some(d)
    } else {
        None
    }
}

/// True if type `t` is a task handle.
pub fn is_task(tys: &weft_ir::TyTable, t: TyId) -> bool {
    matches!(tys.lang(t), Some((weft_ir::ty::Lang::Task, _)))
}

/// Gives the move path `path` of local `k` of the entry state `st` the
/// interface site of index `i` ([`iface`]).
pub fn add_iface(st: &mut State, k: Key, path: &[PathStep], i: u32) {
    let mut v = AbsVal::none();
    v.tasks.insert(iface(i));
    st.add(k, path, &Tree::leaf(v));
}

/// The interface indexes of `joins` (each with the nodes where a `join`
/// ends its handle) that each path from `entry` to a node of `exits` passes
/// a node of: the must part `joins` of the summary.
pub fn must_joins(
    edges: &[(weft_facts::NodeId, weft_facts::NodeId)],
    entry: weft_facts::NodeId,
    exits: &[weft_facts::NodeId],
    joins: &[(SpawnId, weft_facts::NodeId)],
) -> Vec<u32> {
    let mut by: std::collections::BTreeMap<u32, BTreeSet<weft_facts::NodeId>> =
        std::collections::BTreeMap::new();
    for &(s, n) in joins {
        if let Some(i) = iface_index(s) {
            by.entry(i).or_default().insert(n);
        }
    }
    if by.is_empty() || exits.is_empty() {
        return Vec::new();
    }
    let mut succ: std::collections::HashMap<weft_facts::NodeId, Vec<weft_facts::NodeId>> =
        std::collections::HashMap::new();
    for &(a, b) in edges {
        succ.entry(a).or_default().push(b);
    }
    let mut out = Vec::new();
    for (i, stop) in by {
        let mut seen: BTreeSet<weft_facts::NodeId> = BTreeSet::new();
        let mut work = vec![entry];
        let mut reached = false;
        while let Some(n) = work.pop() {
            if stop.contains(&n) || !seen.insert(n) {
                continue;
            }
            if exits.contains(&n) {
                reached = true;
                break;
            }
            work.extend(succ.get(&n).into_iter().flatten().copied());
        }
        if !reached {
            out.push(i);
        }
    }
    out
}

/// The operands of call `t` of body `body` whose tasks the call ends.
///
/// In state `st` (part `joins` of the summaries, O3-9): an argument of a
/// parameter that the callee joins on each path, and a closure callee whose
/// summary joins each task handle that it captures by move.
pub fn joined_ops<'t>(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    t: &'t weft_ir::TermKind,
) -> Vec<&'t Operand> {
    match t {
        weft_ir::TermKind::Call {
            callee: weft_ir::Callee::Fn(f, _),
            args,
            ..
        } => match cx.sums.get(*f) {
            Ok(s) if !s.joins.is_empty() => args
                .iter()
                .enumerate()
                .filter(|(i, _)| u32::try_from(*i).is_ok_and(|i| s.joins.contains(&i)))
                .map(|(_, a)| a)
                .collect(),
            _ => Vec::new(),
        },
        weft_ir::TermKind::Call {
            callee: weft_ir::Callee::Value(f),
            ..
        } => {
            let Ok(v) = transfer::operand(cx, body, st, f) else {
                return Vec::new();
            };
            let fns = v.flat().fns;
            let all = !fns.is_empty()
                && fns.iter().all(|fv| match fv {
                    super::FnVal::Closure(c) | super::FnVal::Made(c) => closure_joins_all(cx, *c),
                    _ => false,
                });
            if all {
                vec![f]
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    }
}

/// True if the summary of closure `c` joins each task handle that the
/// closure captures by move, and it captures one.
fn closure_joins_all(cx: &mut Cx<'_>, c: weft_ir::ClosureId) -> bool {
    let p = cx.p;
    let Some(d) = p.closures.get(c.index()) else {
        return false;
    };
    let Ok(s) = cx.sums.closure(c) else {
        return false;
    };
    let mut any = false;
    for (k, cap) in d.captures.iter().enumerate() {
        let task = crate::factgen::alpha::place_ty(p, cx.tys, d.maker, &cap.source)
            .is_some_and(|t| is_task(cx.tys, t));
        if !task {
            continue;
        }
        if cap.mode != weft_ir::CaptureMode::ByMove
            || !u32::try_from(k).is_ok_and(|k| s.joins.contains(&k))
        {
            return false;
        }
        any = true;
    }
    any
}

/// What the run of a scope body gives ([`scope_run`]).
#[derive(Clone, Debug)]
pub struct ScopeOut {
    /// The scope body.
    pub body: BodyId,
    /// The states of the scope body.
    pub states: super::States,
    /// The join of the states at the `Return`s of the scope body, after
    /// their statements: the state at the `Exit` node.
    pub exit: Option<State>,
    /// The state after the `scope`, before its destination gets the value.
    /// It has no local of the scope body.
    pub after: State,
    /// The value of the `scope`: `_0` of the scope body.
    pub value: Tree,
    /// The join of the states where an abort leaves the scope body, with no
    /// local of the scope body.
    pub unwind: Option<State>,
}

/// The scope body of scope `k`.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if the scope does not exist.
pub fn scope_body(p: &weft_ir::Program, k: ScopeId) -> Result<BodyId, AlphaError> {
    p.scopes
        .get(k.index())
        .map(|d| d.body)
        .ok_or_else(|| AlphaError::BadPlace(format!("no scope s{}", k.0)))
}

/// The run of the scope body of scope `k` from the state `st` before the
/// `scope` (see the module).
///
/// # Errors
///
/// The errors of the transfer functions.
pub fn scope_run(cx: &mut Cx<'_>, st: &State, k: ScopeId) -> Result<ScopeOut, AlphaError> {
    let p = cx.p;
    let sb = scope_body(p, k)?;
    let sbody = p
        .body(sb)
        .ok_or_else(|| AlphaError::BadPlace(format!("no body b{}", sb.0)))?;
    let mut init = st.clone();
    // The scope capability `_1`: plain data.
    if let Some(cap) = sbody
        .locals
        .iter()
        .position(|d| d.kind == LocalKind::ScopeCap)
        .and_then(|i| u32::try_from(i).ok())
    {
        init.write(
            (sb, weft_ir::LocalId(cap)),
            &[],
            Tree::leaf(AbsVal::plain()),
        );
    }
    let (states, ends) =
        super::run_from(cx, sb, vec![(sbody.entry, init)], super::Mode::default())?;
    let mut exit: Option<State> = None;
    for s in ends.returns.values() {
        match &mut exit {
            Some(e) => {
                e.join(s);
            }
            None => exit = Some(s.clone()),
        }
    }
    let mut value = exit
        .as_ref()
        .map_or_else(Tree::none, |e| e.value((sb, sbody.ret), &[]));
    // A handle of a task of the scope in the value (a spawn as the tail of
    // the scope body): the task ended at `ScopeWait`, so the handle holds
    // only its result (as a spawn statement, the old lowering).
    let ended = !value.top.tasks.is_empty()
        && value
            .top
            .tasks
            .iter()
            .all(|s| p.spawns.get(s.index()).is_some_and(|d| d.scope == Some(k)));
    let ret_linear = sbody
        .local(sbody.ret)
        .is_none_or(|d| match cx.tys.lang(d.ty) {
            Some((weft_ir::ty::Lang::Task, args)) => {
                args.first().is_none_or(|&r| ir_props(cx.tys, r).linear)
            }
            _ => true,
        });
    if ended && !ret_linear {
        value.top.linear = false;
        value.top.empty = true;
    }
    let mine = |b: BodyId| super::clause::inside(p, b, sb);
    // A closure that the scope body makes keeps the values of the locals
    // that it captures: it can run after the `scope` (as after a `handle`).
    let captured = super::clause::captured_locals(p, sb);
    let finish = |s: &State| {
        let kept: Vec<(Key, Tree)> = captured
            .iter()
            .filter_map(|k| s.tree(*k).map(|t| (*k, t.clone())))
            .collect();
        let mut out = s.clone();
        out.remove_bodies(&mine);
        for (k, t) in kept {
            out.keep_value(k, t);
        }
        out
    };
    let after = exit.as_ref().map_or_else(|| finish(st), &finish);
    let mut unwind: Option<State> = None;
    for s in ends.unwinds.values() {
        let s = finish(s);
        match &mut unwind {
            Some(u) => {
                u.join(&s);
            }
            None => unwind = Some(s),
        }
    }
    Ok(ScopeOut {
        body: sb,
        states,
        exit,
        after,
        value,
        unwind,
    })
}

/// `Scope`: the run of the scope body; then the destination gets its
/// value. The abort edge of the `scope` gets the states where an abort
/// leaves the scope body.
///
/// # Errors
///
/// The errors of [`scope_run`].
pub fn scope(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    k: ScopeId,
    dest: &Place,
) -> Result<(), AlphaError> {
    let out = scope_run(cx, st, k)?;
    *st = out.after;
    cx.hx.abort_edge = out.unwind.map(super::clause::AbortEdge::Join);
    transfer::bind_result(cx, body, st, &[], dest, out.value)
}

/// `ScopeWait`: the tasks of the scope end. Each `TaskResult` local of
/// `orphans` gets the result of its task.
///
/// # Errors
///
/// The errors of α.
pub fn scope_wait(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    orphans: &[weft_ir::LocalId],
) -> Result<(), AlphaError> {
    let p = cx.p;
    for &l in orphans {
        let Some(LocalKind::TaskResult(site)) =
            p.body(body).and_then(|b| b.local(l)).map(|d| d.kind)
        else {
            continue;
        };
        let v = if let Some(v) = cx.hx.task_values.get(&site) {
            v.clone()
        } else {
            let t = transfer::place_ty(cx, body, &Place::local(l))?;
            Tree::leaf(AbsVal::of_type(ir_props(cx.tys, t).linear))
        };
        let k = transfer::key(p, body, l)?;
        st.write(k, &[], v);
    }
    Ok(())
}

/// The result type of the task of the task operand `task` of body `body`:
/// the result type of its function type.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] for an operand that is not a function.
pub fn task_ret(cx: &mut Cx<'_>, body: BodyId, task: &Operand) -> Result<TyId, AlphaError> {
    let t = match task {
        Operand::Copy(q) | Operand::Move(q) => Some(transfer::place_ty(cx, body, q)?),
        Operand::Const(weft_ir::Const::Fn(f, _)) => {
            return cx
                .p
                .fns
                .get(f.index())
                .map(|d| d.ret)
                .ok_or_else(|| AlphaError::BadPlace(format!("no function f{}", f.0)));
        }
        Operand::Const(_) => None,
    };
    match t.and_then(|t| cx.tys.try_get(t)) {
        Some(Ty::Fn(f)) => Ok(f.ret),
        _ => Err(AlphaError::BadPlace(
            "a task operand that is not a function".to_string(),
        )),
    }
}

/// The task sites that a value in state `st` can hold a handle of, but for
/// the move path `skip`: the values of the locals.
pub fn held_tasks(st: &State, skip: Option<(Key, &[PathStep])>) -> BTreeSet<SpawnId> {
    let mut out = BTreeSet::new();
    for (k, t) in st.trees() {
        match skip {
            Some((sk, path)) if sk == *k => {
                let mut copy = t.clone();
                copy.set(path, Tree::none());
                out.extend(copy.flat().tasks);
            }
            _ => out.extend(t.flat().tasks),
        }
    }
    out
}

/// The task sites of the values of the operands `ops`.
///
/// # Errors
///
/// The errors of α.
pub fn operand_tasks<'o>(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    ops: impl IntoIterator<Item = &'o Operand>,
) -> Result<BTreeSet<SpawnId>, AlphaError> {
    let mut out = BTreeSet::new();
    for op in ops {
        if matches!(op, Operand::Copy(_) | Operand::Move(_)) {
            out.extend(transfer::operand(cx, body, st, op)?.flat().tasks);
        }
    }
    Ok(out)
}

/// The handles in the operands `ops` leave the values of the component (a
/// callee, a store behind a reference): their sites are lost.
///
/// # Errors
///
/// The errors of α.
pub fn lose_operands<'o>(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    ops: impl IntoIterator<Item = &'o Operand>,
) -> Result<(), AlphaError> {
    let ts = operand_tasks(cx, body, st, ops)?;
    st.lose_tasks(ts);
    Ok(())
}

/// The value of a handle of type `handle_ty` of the task of site `site`
/// whose result has the value `result`: the site, and what the result
/// points into and holds.
pub fn handle_value(cx: &Cx<'_>, handle_ty: TyId, site: SpawnId, result: &Tree) -> Tree {
    let linear = ir_props(cx.tys, handle_ty).linear;
    let mut v = result.flat();
    v.tasks = BTreeSet::from([site]);
    v.linear = linear;
    v.empty = !linear;
    v.uniq = false;
    Tree::leaf(v)
}

/// The value of the result of a task of result type `ret_ty` from the value
/// `ret` of the run of the task: a type that holds no reference and no
/// function value keeps only its linear part.
pub fn task_result(cx: &Cx<'_>, ret_ty: TyId, ret: &Tree) -> Tree {
    let rp = ir_props(cx.tys, ret_ty);
    if !rp.holds_refs && !rp.callable && !crate::props::ir_has_fns(cx.tys, ret_ty) && !rp.generic {
        return Tree::leaf(AbsVal::of_type(rp.linear));
    }
    let mut v = ret.flat();
    v.tasks = BTreeSet::new();
    v.linear |= rp.linear;
    v.empty = !v.linear;
    Tree::leaf(v)
}

/// `Spawn`: the run of the task (see the module), then the handle (or the
/// `TaskResult` local of a spawn statement) gets its value.
///
/// # Errors
///
/// The errors of the transfer functions.
pub fn spawn(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, weft_ir::BlockId),
    st: &mut State,
    site: SpawnId,
    task: &Operand,
    dest: Option<&Place>,
) -> Result<(), AlphaError> {
    let p = cx.p;
    let ret_ty = task_ret(cx, body, task)?;
    let out = transfer::value_out_ty(cx, (body, block), st, task, &[], ret_ty)?;
    transfer::apply_apps(cx, st, &out.apps, true);
    // A handle that the task holds: the task can join or detach it.
    lose_operands(cx, body, st, [task])?;
    let result = task_result(cx, ret_ty, &out.ret);
    match cx.hx.task_values.get_mut(&site) {
        Some(have) => {
            have.join(&result);
        }
        None => {
            cx.hx.task_values.insert(site, result.clone());
        }
    }
    transfer::moves(p, body, st, [task])?;
    if let Some(d) = dest {
        let t = transfer::place_ty(cx, body, d)?;
        let h = handle_value(cx, t, site, &result);
        transfer::bind_result(cx, body, st, &[], d, h)
    } else {
        {
            // The `TaskResult` local of a spawn statement: no value yet
            // (`ScopeWait` gives it the result).
            let orphan = p.body(body).and_then(|b| {
                b.locals
                    .iter()
                    .position(|d| d.kind == LocalKind::TaskResult(site))
                    .and_then(|i| u32::try_from(i).ok())
            });
            if let Some(l) = orphan {
                let k = transfer::key(p, body, weft_ir::LocalId(l))?;
                st.write(k, &[], Tree::leaf(AbsVal::plain()));
            }
            Ok(())
        }
    }
}

/// `Join`: the handle moves, and the destination gets the result of each
/// task that it can hold.
///
/// # Errors
///
/// The errors of α.
pub fn join(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    task: &Operand,
    dest: &Place,
) -> Result<(), AlphaError> {
    let v = transfer::operand(cx, body, st, task)?.flat();
    let t = transfer::place_ty(cx, body, dest)?;
    let linear = ir_props(cx.tys, t).linear;
    let mut r = v;
    r.tasks = BTreeSet::new();
    r.linear = linear;
    r.empty = !linear;
    r.uniq = false;
    transfer::moves(cx.p, body, st, [task])?;
    transfer::bind_result(cx, body, st, &[], dest, Tree::leaf(r))
}

/// `Detach`: the handle moves; the task runs on, so its site is lost.
///
/// # Errors
///
/// The errors of α.
pub fn detach(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    task: &Operand,
) -> Result<(), AlphaError> {
    lose_operands(cx, body, st, [task])?;
    transfer::moves(cx.p, body, st, [task])
}

/// The task sites that a `join` of the handle operand `task` ends.
///
/// In state `st` before the `join` in body `body`: each site of the
/// handle that no other value can hold a handle of, and whose handles did
/// not leave the values of the component (V096, plan stage F18). Each task
/// of such a site that still runs has its handle in this value, and one
/// value holds one task: after the `join`, no task of the site runs.
///
/// # Errors
///
/// The errors of α.
pub fn must_join(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    task: &Operand,
) -> Result<BTreeSet<SpawnId>, AlphaError> {
    let (Operand::Copy(q) | Operand::Move(q)) = task else {
        return Ok(BTreeSet::new());
    };
    let ts = transfer::operand(cx, body, st, task)?.flat().tasks;
    let Some((k, path)) = transfer::move_path(cx.p, body, q)? else {
        return Ok(BTreeSet::new());
    };
    let others = held_tasks(st, Some((k, &path)));
    Ok(ts
        .into_iter()
        .filter(|t| !others.contains(t) && !st.lost_tasks().contains(t))
        .collect())
}
