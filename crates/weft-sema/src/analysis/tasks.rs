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

/// The interface indexes of `joins` that each path from `entry` to a node
/// of `exits` joins: a must part of the summary.
///
/// Each entry of `joins` has a node where a `join` ends its handle. The
/// exits are the `Return` nodes (part `joins`), or the nodes where an abort
/// leaves the body (part `abort_joins`, follow-up F19.3).
///
/// With no exit, `vacuous` gives each index of `joins` (no path leaves the
/// body there), else no index.
pub fn must_joins(
    edges: &[(weft_facts::NodeId, weft_facts::NodeId)],
    entry: weft_facts::NodeId,
    exits: &[weft_facts::NodeId],
    joins: &[(SpawnId, weft_facts::NodeId)],
    vacuous: bool,
) -> Vec<u32> {
    let mut by: std::collections::BTreeMap<u32, BTreeSet<weft_facts::NodeId>> =
        std::collections::BTreeMap::new();
    for &(s, n) in joins {
        if let Some(i) = iface_index(s) {
            by.entry(i).or_default().insert(n);
        }
    }
    if by.is_empty() {
        return Vec::new();
    }
    if exits.is_empty() {
        return if vacuous {
            by.into_keys().collect()
        } else {
            Vec::new()
        };
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
/// parameter that the callee joins on each path to its `Return`, and a
/// closure callee whose summary joins each task handle that it captures by
/// move. With each operand, `early`: the callee also joins the handle on
/// each path where an abort leaves it (part `abort_joins`, follow-up
/// F19.3, E-1). Then the task ends at `Main` of the call; else only on the
/// normal path, at `Ret`: an abort of the call can leave the task running.
pub fn joined_ops<'t>(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    t: &'t weft_ir::TermKind,
) -> Vec<(&'t Operand, bool)> {
    match t {
        weft_ir::TermKind::Call {
            callee: weft_ir::Callee::Fn(f, _),
            args,
            ..
        } => match cx.sums.get(*f) {
            Ok(s) if !s.joins.is_empty() => args
                .iter()
                .enumerate()
                .filter_map(|(i, a)| {
                    let i = u32::try_from(i).ok()?;
                    s.joins
                        .contains(&i)
                        .then(|| (a, s.abort_joins.contains(&i)))
                })
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
            if fns.is_empty() {
                return Vec::new();
            }
            let mut early = true;
            for fv in &fns {
                let joined = match fv {
                    super::FnVal::Closure(c) | super::FnVal::Made(c) => closure_joins_all(cx, *c),
                    _ => None,
                };
                match joined {
                    Some(e) => early &= e,
                    None => return Vec::new(),
                }
            }
            vec![(f, early)]
        }
        _ => Vec::new(),
    }
}

/// If the summary of closure `c` joins each task handle that the closure
/// captures by move, and it captures one: `Some(early)`, with `early` true
/// if the summary also joins each of them on each path of an abort (part
/// `abort_joins`, follow-up F19.3). Else `None`.
fn closure_joins_all(cx: &mut Cx<'_>, c: weft_ir::ClosureId) -> Option<bool> {
    let p = cx.p;
    let d = p.closures.get(c.index())?;
    let s = cx.sums.closure(c).ok()?;
    let mut any = false;
    let mut early = true;
    for (k, cap) in d.captures.iter().enumerate() {
        let task = crate::factgen::alpha::place_ty(p, cx.tys, d.maker, &cap.source)
            .is_some_and(|t| is_task(cx.tys, t));
        if !task {
            continue;
        }
        let k = u32::try_from(k).ok()?;
        if cap.mode != weft_ir::CaptureMode::ByMove || !s.joins.contains(&k) {
            return None;
        }
        early &= s.abort_joins.contains(&k);
        any = true;
    }
    any.then_some(early)
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
    // The scope capability `_1`: plain data (and, in a program with a spawn
    // on a scope that the spawn does not name, a reference into itself:
    // [`scope_cap_value`]).
    if let Some(cap) = sbody
        .locals
        .iter()
        .position(|d| d.kind == LocalKind::ScopeCap)
        .and_then(|i| u32::try_from(i).ok())
    {
        let v = scope_cap_value(
            cx.p,
            cx.tys,
            cx.facts,
            cx.roots,
            (sb, weft_ir::LocalId(cap)),
        )?;
        init.write((sb, weft_ir::LocalId(cap)), &[], v);
    }
    // The re-entry states of a `multi` handler outside the scope at the
    // nodes of the scope body (`Handlers::extra`, plan stage F19).
    let mut seeds = vec![(sbody.entry, init)];
    seeds.extend(cx.hx.extra.get(&sb).into_iter().flatten().cloned());
    let (states, ends) = super::run_from(cx, sb, seeds, super::Mode::default())?;
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

/// True if a spawn of program `p` does not name its scope (stage R0e).
///
/// `SpawnDecl::scope` is `None` and the site is not a `fork`: a copy of the
/// scope capability, a capability in a tuple or an `Option`, a capability
/// that a callee gives back.
pub fn unowned(p: &weft_ir::Program) -> bool {
    p.spawns.iter().any(|d| !d.fork && d.scope.is_none())
}

/// The value of the scope capability local `cap` (stage R0e).
///
/// In a program with a spawn on a scope that the spawn does not name
/// ([`unowned`]), the value points into the root of the local: the analysis
/// finds the scope of such a spawn from the references of its scope operand
/// ([`SiteScope`]), and a copy of the capability is invalid after the end of
/// the scope body (as a closure that captures the capability, RR4). In
/// another program it is plain data.
///
/// # Errors
///
/// The errors of α.
pub fn scope_cap_value(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    facts: &mut weft_facts::FnFacts,
    roots: &mut crate::factgen::alpha::Roots,
    cap: Key,
) -> Result<Tree, AlphaError> {
    let mut v = AbsVal::plain();
    if unowned(p) {
        v.refs.insert(roots.local(p, tys, facts, cap.0, cap.1)?);
    }
    Ok(Tree::leaf(v))
}

/// The scopes that the scope operand of a spawn site can be (stage R0e).
///
/// `scopes`: the scope of each scope capability local whose root a
/// reference of the operand points into. `other`: the operand has no such
/// reference, or a reference to another place (a place of the interface of
/// a closure body, a place that the analysis does not follow).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SiteScope {
    /// The scopes of the scope capability locals.
    pub scopes: BTreeSet<ScopeId>,
    /// The operand can be another value.
    pub other: bool,
}

impl SiteScope {
    /// The one scope that the operand can be, if it can be no other value.
    pub fn one(&self) -> Option<ScopeId> {
        match (self.scopes.len(), self.other) {
            (1, false) => self.scopes.iter().next().copied(),
            _ => None,
        }
    }

    /// The scope whose end ends the task (plan stage R0j): the one scope of
    /// [`Self::one`], or else the outer scope of the scopes that the operand
    /// can be, if the operand can be no other value and the body of each
    /// other scope is inside the body of that scope in one unit (through
    /// scope, handled and clause bodies).
    ///
    /// Each scope that the operand can be is live at the spawn, so the
    /// scopes are nested and the outer scope ends last: the task ends at or
    /// before the end of the outer scope. The facts end the task there. A
    /// task that ends at an inner scope runs a longer time in the facts,
    /// which is sound for each check of a task that runs.
    pub fn end(&self, p: &weft_ir::Program) -> Option<ScopeId> {
        if let Some(k) = self.one() {
            return Some(k);
        }
        if self.other || self.scopes.is_empty() {
            return None;
        }
        let body = |k: &ScopeId| p.scopes.get(k.index()).map(|d| d.body);
        self.scopes.iter().copied().find(|outer| {
            body(outer).is_some_and(|ob| {
                self.scopes
                    .iter()
                    .all(|k| body(k).is_some_and(|b| unit_inside(p, b, ob)))
            })
        })
    }
}

/// True if body `b` is body `outer` or is inside it through the parents of
/// scope, handled and clause bodies (one unit, `factgen::alpha::unit_root`).
fn unit_inside(p: &weft_ir::Program, b: BodyId, outer: BodyId) -> bool {
    let mut at = b;
    for _ in 0..=p.bodies.len() {
        if at == outer {
            return true;
        }
        let Some(x) = p.body(at) else {
            return false;
        };
        match (x.kind, x.parent) {
            (
                weft_ir::BodyKind::Handled(_)
                | weft_ir::BodyKind::Clause(..)
                | weft_ir::BodyKind::Scope(_),
                Some(up),
            ) => at = up,
            _ => return false,
        }
    }
    false
}

/// The scope of the scope capability local whose root is fact place `q`.
fn scope_of_root(
    p: &weft_ir::Program,
    facts: &weft_facts::FnFacts,
    roots: &crate::factgen::alpha::Roots,
    q: weft_facts::PlaceId,
) -> Option<ScopeId> {
    let info = facts.places.get(q.index())?;
    if info.parent.is_some() {
        return None;
    }
    let Some(crate::factgen::alpha::Role::Local((b, l))) = roots.role(info.root) else {
        return None;
    };
    let body = p.body(b)?;
    match (body.kind, body.local(l).map(|d| d.kind)) {
        (weft_ir::BodyKind::Scope(k), Some(LocalKind::ScopeCap)) => Some(k),
        _ => None,
    }
}

/// Records the scopes that the scope operand `scope` of the spawn of site
/// `site` can be in state `st` (`Handlers::site_scopes`, stage R0e), if the
/// spawn does not name its scope.
///
/// # Errors
///
/// The errors of the transfer functions.
fn note_site_scope(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    site: SpawnId,
    scope: &Operand,
) -> Result<(), AlphaError> {
    let p = cx.p;
    if !p
        .spawns
        .get(site.index())
        .is_some_and(|d| !d.fork && d.scope.is_none())
    {
        return Ok(());
    }
    let v = transfer::operand(cx, body, st, scope)?.flat();
    let mut res = SiteScope {
        other: v.refs.is_empty(),
        ..SiteScope::default()
    };
    for &q in &v.refs {
        match scope_of_root(p, cx.facts, cx.roots, q) {
            Some(k) => {
                res.scopes.insert(k);
            }
            None => res.other = true,
        }
    }
    let have = cx.hx.site_scopes.entry(site).or_default();
    have.scopes.extend(res.scopes);
    have.other |= res.other;
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
    (site, scope): (SpawnId, &Operand),
    task: &Operand,
    dest: Option<&Place>,
) -> Result<(), AlphaError> {
    let p = cx.p;
    note_site_scope(cx, body, st, site, scope)?;
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

/// `Fork`: the run of each branch as a task (as a spawn, in written order),
/// then the destination gets the tuple of the results of the branches
/// (IP6: also a tuple of units).
///
/// # Errors
///
/// The errors of the transfer functions.
pub fn fork(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, weft_ir::BlockId),
    st: &mut State,
    branches: &[Operand],
    dest: &Place,
) -> Result<(), AlphaError> {
    let mut tuple = Tree::none();
    for (i, br) in branches.iter().enumerate() {
        let ret_ty = task_ret(cx, body, br)?;
        let out = transfer::value_out_ty(cx, (body, block), st, br, &[], ret_ty)?;
        transfer::apply_apps(cx, st, &out.apps, true);
        lose_operands(cx, body, st, [br])?;
        let i = u32::try_from(i).unwrap_or(u32::MAX);
        tuple
            .kids
            .insert(PathStep::Field(i), task_result(cx, ret_ty, &out.ret));
    }
    transfer::bind_result(cx, body, st, branches, dest, tuple)
}

/// How a body runs one function value of its interface as a task, in the
/// places of the facts of the body (`super::summary::TaskHow` before the
/// interface map, plan stage F19).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RawHow {
    /// The parameter, or the capture of a closure body.
    pub param: u32,
    /// True for a capture.
    pub capture: bool,
    /// The task is a branch of a `fork`.
    pub thread: bool,
    /// Two tasks of the value can run at the same time.
    pub twice: bool,
    /// The values of the interface that the body runs while the task runs.
    pub with: BTreeSet<u32>,
    /// The places that the body changes or lends while the task runs.
    pub writes: BTreeSet<weft_facts::PlaceId>,
    /// The places that the body reads while the task runs.
    pub reads: BTreeSet<weft_facts::PlaceId>,
}

/// How the body of the facts `facts` runs the values of its interface as
/// tasks (part `runs`, plan stage F19; `task_runs` of the old inference).
///
/// `task_runs` has each task that runs a value of the interface (the task,
/// the parameter or capture, true for a capture, true for a `fork`
/// branch), and `run_at` each node that runs such a value as plain code.
/// A task runs from the nodes after its `spawned_at` node to its
/// `joined_at` nodes (the rule `active` of the spec). While it runs: a
/// second start of a task of the value is `twice`; a run of another value
/// of the interface, plain or as a task, is in `with`; the changes and
/// lends of the body are `writes`, and its reads are `reads`.
pub fn task_hows(
    facts: &weft_facts::FnFacts,
    task_runs: &[(weft_facts::TaskId, u32, bool, bool)],
    run_at: &[(u32, bool, weft_facts::NodeId)],
) -> Vec<RawHow> {
    use std::collections::{BTreeMap, HashMap};
    use weft_facts::NodeId;
    if task_runs.is_empty() {
        return Vec::new();
    }
    let mut succ: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
    for &(a, b) in &facts.cfg_edge {
        succ.entry(a).or_default().push(b);
    }
    let spawns_of = |t: weft_facts::TaskId| -> Vec<NodeId> {
        facts
            .spawned_at
            .iter()
            .filter(|(u, _)| *u == t)
            .map(|(_, n)| *n)
            .collect()
    };
    // The nodes after the start of task `t` where it still runs.
    let active_of = |t: weft_facts::TaskId| -> BTreeSet<NodeId> {
        let ends: BTreeSet<NodeId> = facts
            .joined_at
            .iter()
            .filter(|(u, _)| *u == t)
            .map(|(_, n)| *n)
            .collect();
        let mut active: BTreeSet<NodeId> = BTreeSet::new();
        let mut work: Vec<NodeId> = spawns_of(t)
            .iter()
            .flat_map(|n| succ.get(n).into_iter().flatten().copied())
            .collect();
        while let Some(q) = work.pop() {
            if !active.insert(q) || ends.contains(&q) {
                continue;
            }
            work.extend(succ.get(&q).into_iter().flatten().copied());
        }
        active
    };
    let others: BTreeSet<weft_facts::TaskId> = facts.spawned_at.iter().map(|(t, _)| *t).collect();
    let mut out: BTreeMap<(u32, bool), RawHow> = BTreeMap::new();
    for &(t, param, capture, thread) in task_runs {
        let starts = spawns_of(t);
        let active = active_of(t);
        let how = out.entry((param, capture)).or_insert_with(|| RawHow {
            param,
            capture,
            ..RawHow::default()
        });
        how.thread |= thread;
        for &(u, p2, c2, _) in task_runs {
            if spawns_of(u).iter().any(|n| active.contains(n)) {
                if (p2, c2) == (param, capture) {
                    how.twice = true;
                } else if c2 == capture {
                    how.with.insert(p2);
                }
            }
        }
        for &(p2, c2, n) in run_at {
            if active.contains(&n) && c2 == capture {
                // A run of the value itself while its task runs: two runs
                // at the same time.
                if p2 == param {
                    how.twice = true;
                } else {
                    how.with.insert(p2);
                }
            }
        }
        for &(n, q) in facts.mutates_at.iter().chain(&facts.lends_mut) {
            if active.contains(&n) {
                how.writes.insert(q);
            }
        }
        for &(n, q) in &facts.reads_at {
            if active.contains(&n) {
                how.reads.insert(q);
            }
        }
        // Another task of the body that runs at the same time as the task of
        // the value (stage R0e fix 4: `s.spawn(|| v.clear()); s.spawn(|| f())`):
        // its changes and reads are changes and reads while the value runs.
        for &u in others.iter().filter(|&&u| u != t) {
            let ss = spawns_of(u);
            let overlap = ss.iter().any(|n| active.contains(n))
                || (!starts.is_empty() && {
                    let au = active_of(u);
                    starts.iter().any(|n| au.contains(n))
                });
            if !overlap {
                continue;
            }
            how.writes.extend(
                facts
                    .task_writes
                    .iter()
                    .filter(|(x, _)| *x == u)
                    .map(|(_, q)| *q),
            );
            how.reads.extend(
                facts
                    .task_reads
                    .iter()
                    .filter(|(x, _)| *x == u)
                    .map(|(_, q)| *q),
            );
        }
    }
    // Two tasks that run at the same time conflict both ways: the second
    // one runs while the first one runs, and the other way.
    let pairs: Vec<((u32, bool), u32)> = out
        .iter()
        .flat_map(|(k, h)| h.with.iter().map(move |&j| (*k, j)))
        .collect();
    for ((i, c), j) in pairs {
        if let Some(h) = out.get_mut(&(j, c)) {
            h.with.insert(i);
        }
    }
    out.into_values().collect()
}

/// The places of the tasks that run while a body runs one function value of
/// its interface as code that is not a task.
///
/// The places are places of the facts of the body: the part
/// `super::summary::Run::during` before the interface map (stage R0e fix,
/// OR7).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RawDuring {
    /// The parameter, or the capture of a closure body.
    pub param: u32,
    /// True for a capture.
    pub capture: bool,
    /// The places that the tasks change.
    pub writes: BTreeSet<weft_facts::PlaceId>,
    /// The places that the tasks read.
    pub reads: BTreeSet<weft_facts::PlaceId>,
}

/// The entry of the value `param` (a capture with `capture`) of `out`.
fn during_entry(
    out: &mut std::collections::BTreeMap<(u32, bool), RawDuring>,
    param: u32,
    capture: bool,
) -> &mut RawDuring {
    out.entry((param, capture)).or_insert_with(|| RawDuring {
        param,
        capture,
        ..RawDuring::default()
    })
}

/// The places of the tasks that run while the body of the facts `facts`
/// runs each function value of its interface as code that is not a task
/// (part `runs`, `Run::during`; stage R0e fix, OR7).
///
/// `run_at` has each node that runs such a value (the parameter or
/// capture, true for a capture, the node). A task is active at a node from
/// the nodes after its `spawned_at` node to its `joined_at` nodes (the rule
/// `active` of the spec). The changes and reads of each task that is active
/// at a run node of a value (`task_writes`, `task_reads`) are the places of
/// the value. The tasks of `skip` do not count (the tasks that stand for
/// the code of a clause, `factgen::templates::WaitTask`). `inherited` has
/// the places that a callee gives for a value that it runs while its own
/// tasks run (the value, true for a capture, the place, true for a
/// change).
pub fn run_during(
    facts: &weft_facts::FnFacts,
    run_at: &[(u32, bool, weft_facts::NodeId)],
    inherited: &[(u32, bool, weft_facts::PlaceId, bool)],
    skip: &BTreeSet<weft_facts::TaskId>,
) -> Vec<RawDuring> {
    use std::collections::{BTreeMap, HashMap};
    use weft_facts::{NodeId, TaskId};
    let mut out: BTreeMap<(u32, bool), RawDuring> = BTreeMap::new();
    for &(param, capture, q, write) in inherited {
        let d = during_entry(&mut out, param, capture);
        if write {
            d.writes.insert(q);
        } else {
            d.reads.insert(q);
        }
    }
    if !run_at.is_empty() && !facts.spawned_at.is_empty() {
        let mut succ: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
        for &(a, b) in &facts.cfg_edge {
            succ.entry(a).or_default().push(b);
        }
        let mut ends: HashMap<TaskId, BTreeSet<NodeId>> = HashMap::new();
        for &(t, n) in &facts.joined_at {
            ends.entry(t).or_default().insert(n);
        }
        let mut starts: BTreeMap<TaskId, Vec<NodeId>> = BTreeMap::new();
        for &(t, n) in &facts.spawned_at {
            if !skip.contains(&t) {
                starts.entry(t).or_default().push(n);
            }
        }
        let runs: BTreeSet<NodeId> = run_at.iter().map(|&(_, _, n)| n).collect();
        // The tasks that are active at each run node.
        let mut on: HashMap<NodeId, Vec<TaskId>> = HashMap::new();
        for (&t, ss) in &starts {
            let none = BTreeSet::new();
            let end = ends.get(&t).unwrap_or(&none);
            let mut seen: BTreeSet<NodeId> = BTreeSet::new();
            let mut work: Vec<NodeId> = ss
                .iter()
                .flat_map(|n| succ.get(n).into_iter().flatten().copied())
                .collect();
            while let Some(q) = work.pop() {
                if !seen.insert(q) || end.contains(&q) {
                    continue;
                }
                if runs.contains(&q) {
                    on.entry(q).or_default().push(t);
                }
                work.extend(succ.get(&q).into_iter().flatten().copied());
            }
        }
        for &(param, capture, n) in run_at {
            let Some(ts) = on.get(&n) else {
                continue;
            };
            let d = during_entry(&mut out, param, capture);
            for &(t, q) in &facts.task_writes {
                if ts.contains(&t) {
                    d.writes.insert(q);
                }
            }
            for &(t, q) in &facts.task_reads {
                if ts.contains(&t) {
                    d.reads.insert(q);
                }
            }
        }
    }
    out.into_values()
        .filter(|d| !d.writes.is_empty() || !d.reads.is_empty())
        .collect()
}

/// The facts of the part `waits` that the fact generator records at the
/// nodes of a body (follow-up F19.5, issue #50).
#[derive(Clone, Debug, Default)]
pub struct WaitRaw {
    /// A part `waits` of a summary that a node applies: the node, the
    /// effect, a place that σ gives there (`None` names the effect only: a
    /// task runs, but it accesses no place that σ gives), and true for a
    /// change (else a read).
    pub places: Vec<(
        weft_facts::NodeId,
        String,
        Option<weft_facts::PlaceId>,
        bool,
    )>,
    /// A task that a run at a node starts and that can run while the node
    /// waits at an operation: a task of a value that the callee or the
    /// value itself can perform or abort after, and a task of a value that
    /// the callee runs as a task. The flag is true if code of the callee
    /// can wait after the run (`Run::then`, a task of the callee): the
    /// facts of the value do not see that wait.
    pub starts: Vec<(weft_facts::NodeId, weft_facts::TaskId, bool)>,
}

/// The places of the part `waits` of one effect: the changes and the
/// reads.
pub type WaitPlaces = (
    BTreeSet<super::summary::IPlace>,
    BTreeSet<super::summary::IPlace>,
);

/// The part `waits` of a body from its facts `facts` (follow-up F19.5,
/// issue #50).
///
/// A node of the body (one of the first `nodes` nodes) that sends an
/// effect other than `Async` past the function (`escapes_at`) waits there
/// for a handler of a caller. Each task that runs at the node can run while
/// the clause runs: a task that is active at the node and does not end
/// there (the rule `active` of the spec), and each task of `raw.starts` at
/// the node. Their changes and reads (`task_writes`, `task_reads`), and the
/// places of `raw.places` at the node, are the places of the effect.
/// `place` gives the interface place of a place of the facts; a place with
/// none is not in the part, but the effect gets its key.
pub fn waits_of(
    facts: &weft_facts::FnFacts,
    nodes: usize,
    raw: &WaitRaw,
    place: &dyn Fn(weft_facts::PlaceId) -> Option<super::summary::IPlace>,
) -> std::collections::BTreeMap<String, WaitPlaces> {
    use std::collections::{BTreeMap, HashMap};
    use weft_facts::{NodeId, PlaceId, TaskId};
    let mut out: BTreeMap<String, WaitPlaces> = BTreeMap::new();
    let mut at: BTreeMap<NodeId, BTreeSet<&str>> = BTreeMap::new();
    for (n, e) in &facts.escapes_at {
        if n.index() < nodes && e != "Async" {
            at.entry(*n).or_default().insert(e.as_str());
        }
    }
    if at.is_empty() {
        return out;
    }
    let mut succ: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
    for &(a, b) in &facts.cfg_edge {
        succ.entry(a).or_default().push(b);
    }
    let mut ends: HashMap<TaskId, BTreeSet<NodeId>> = HashMap::new();
    for &(t, n) in &facts.joined_at {
        ends.entry(t).or_default().insert(n);
    }
    let mut starts: HashMap<TaskId, Vec<NodeId>> = HashMap::new();
    for &(t, n) in &facts.spawned_at {
        starts.entry(t).or_default().push(n);
    }
    // The nodes where each task is active.
    let mut active: HashMap<TaskId, BTreeSet<NodeId>> = HashMap::new();
    for (&t, ss) in &starts {
        let none = BTreeSet::new();
        let end = ends.get(&t).unwrap_or(&none);
        let mut on: BTreeSet<NodeId> = BTreeSet::new();
        let mut work: Vec<NodeId> = ss
            .iter()
            .flat_map(|n| succ.get(n).into_iter().flatten().copied())
            .collect();
        while let Some(q) = work.pop() {
            if !on.insert(q) || end.contains(&q) {
                continue;
            }
            work.extend(succ.get(&q).into_iter().flatten().copied());
        }
        active.insert(t, on);
    }
    let base = |q: PlaceId| facts.wild_base(q).unwrap_or(q);
    let mut writes: HashMap<TaskId, Vec<PlaceId>> = HashMap::new();
    for &(t, q) in &facts.task_writes {
        writes.entry(t).or_default().push(base(q));
    }
    let mut reads: HashMap<TaskId, Vec<PlaceId>> = HashMap::new();
    for &(t, q) in &facts.task_reads {
        reads.entry(t).or_default().push(base(q));
    }
    for (n, effects) in at {
        let mut live: BTreeSet<TaskId> = active
            .iter()
            .filter(|(t, on)| on.contains(&n) && !ends.get(t).is_some_and(|e| e.contains(&n)))
            .map(|(&t, _)| t)
            .collect();
        live.extend(
            raw.starts
                .iter()
                .filter(|(m, _, _)| *m == n)
                .map(|&(_, t, _)| t),
        );
        let mut mine: WaitPlaces = (BTreeSet::new(), BTreeSet::new());
        for t in &live {
            for &q in writes.get(t).into_iter().flatten() {
                mine.0.extend(place(q));
            }
            for &q in reads.get(t).into_iter().flatten() {
                mine.1.extend(place(q));
            }
        }
        for e in effects {
            let given: Vec<(Option<PlaceId>, bool)> = raw
                .places
                .iter()
                .filter(|(m, f, _, _)| *m == n && f == e)
                .map(|&(_, _, q, w)| (q, w))
                .collect();
            if live.is_empty() && given.is_empty() {
                continue;
            }
            let ps = out.entry(e.to_string()).or_default();
            ps.0.extend(mine.0.iter().cloned());
            ps.1.extend(mine.1.iter().cloned());
            for (q, w) in given {
                let Some(q) = q else {
                    continue;
                };
                let ip = place(base(q));
                if w {
                    ps.0.extend(ip);
                } else {
                    ps.1.extend(ip);
                }
            }
        }
    }
    out
}
