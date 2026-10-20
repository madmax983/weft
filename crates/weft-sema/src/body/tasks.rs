//! What a task shares with the code around it, and how a callee runs a
//! function argument as a task.
//!
//! A task gets the facts of its captures and the copy variables that it keeps.
//! At the end of the body, each task gets the facts for work stealing
//! (`opaque`, `spawns_in`), and the body gets the `pins` and `task_runs` parts
//! of its signature. A callee can run a function argument as a task or a fork
//! branch. Its `task_runs` part says how, and the caller checks the argument
//! as a task at the call (ADR 0006).

use std::collections::{BTreeMap, BTreeSet};

use weft_facts::{TaskId, TaskKind, ARG_TASK};

use super::fnval::FnInfo;
use super::{Lower, NodeId, PlaceId, RootId, Span, Summary, Ty, Val, VarId};
use crate::TaskRun;

/// A task of the body (`Lower::task_runs`).
#[derive(Clone, Debug)]
pub(super) struct TaskRec {
    /// The task.
    pub task: TaskId,
    /// A node that starts it.
    pub node: NodeId,
    /// The summary of the function value that it runs.
    pub summary: usize,
    /// The task stands for a run of a function argument in a callee
    /// (`Lower::arg_tasks`). The call node gets the values of its captures.
    pub arg: bool,
    /// The function parameters of the function whose function values the task
    /// can run, for example from a field of the parameter.
    pub held: BTreeSet<usize>,
}

/// The places that a callee writes and reads while it runs a function argument
/// as a task (`TaskRun::writes`, `TaskRun::reads`), in the places of the caller.
pub(super) type Access = (Vec<PlaceId>, Vec<PlaceId>);

/// The places that a body writes and reads while a task runs each function
/// parameter, by parameter (`Lower::task_run_places`).
pub(super) type RunPlaces = BTreeMap<usize, (BTreeSet<PlaceId>, BTreeSet<PlaceId>)>;

/// A function argument of a call that the callee can run as a task, with the
/// places that its run at the call writes and reads.
pub(super) struct ArgRun {
    /// The argument position.
    pub pos: usize,
    /// The function value.
    pub info: FnInfo,
    /// The effect row of its type.
    pub row: Option<Vec<String>>,
    /// The places that the run writes or lends.
    pub writes: Vec<PlaceId>,
    /// The places that the run reads.
    pub reads: Vec<PlaceId>,
    /// The argument.
    pub span: Span,
    /// The function parameters of the function whose function values the
    /// argument holds, for example in a field.
    pub held: BTreeSet<usize>,
}

impl Lower<'_> {
    /// Gives task `t` the facts of the captures of the closures of summary
    /// `sum`. The task writes the places `writes`. A capture that holds a
    /// reference into a written place is a capture that the task mutates
    /// through (`mut_through`).
    pub(super) fn task_captures(&mut self, t: TaskId, sum: &Summary, writes: &[PlaceId]) {
        for &c in &sum.captures {
            self.facts.captures.push((t, c));
            let refs = self.local_of(c).map(|l| &self.locals[l]).map(|l| {
                let mut r = l.refs.clone();
                if !l.ty.is_ref() {
                    r.extend(l.root);
                }
                r
            });
            let refs = refs.unwrap_or_default();
            let through = writes.iter().any(|&m| {
                refs.iter().any(|&r| {
                    self.facts.place(r).root == self.facts.place(m).root
                        && weft_verified::places::within(
                            &self.facts.place(m).steps,
                            &self.facts.place(r).steps,
                        )
                })
            });
            if through {
                self.facts.mut_through.push((t, c));
            }
        }
        for r in self.kept_roots(sum) {
            self.facts.kept.push((t, r));
        }
    }

    /// Returns the root places of the copy variables that a task of closure
    /// summary `sum` keeps (`kept`). The closure captures them, also through a
    /// captured closure. The value is plain data, and no reference that the
    /// task holds points into it. The interpreter keeps a captured copy value
    /// readable after its scope ends (ADR 0003), so the end of the variable is
    /// not a free for the task. A reference into the variable is still invalid
    /// after the end, so the task does not keep a variable that it borrows
    /// (`Lower::borrowed_roots`).
    fn kept_roots(&self, sum: &Summary) -> Vec<PlaceId> {
        let mut seen = BTreeSet::new();
        let mut todo: Vec<VarId> = sum.captures.iter().copied().collect();
        let mut found = Vec::new();
        let mut held = BTreeSet::new();
        let mut code: Vec<(u32, u32)> = sum
            .members
            .iter()
            .map(|&m| self.closures[m].nodes)
            .collect();
        let mut rets: Vec<PlaceId> = sum.ret_refs.clone();
        while let Some(v) = todo.pop() {
            if !seen.insert(v) {
                continue;
            }
            let Some(l) = self.local_of(v) else {
                continue;
            };
            let loc = &self.locals[l];
            let parts = self.part_holders.iter().filter(|h| h.local == l);
            for &p in loc.refs.iter().chain(parts.flat_map(|h| h.refs.iter())) {
                held.insert(self.facts.place(p).root);
            }
            if let Some(s) = loc.summary {
                let c = &self.closures[s];
                todo.extend(c.captures.iter().copied());
                code.extend(c.members.iter().map(|&m| self.closures[m].nodes));
                rets.extend(c.ret_refs.iter().copied());
            }
            if !matches!(self.inf.shallow(&loc.ty), Ty::Ref(_)) && !self.may_free(&loc.ty) {
                found.extend(loc.root);
            }
        }
        held.extend(rets.iter().map(|&p| self.facts.place(p).root));
        found.retain(|&r| !held.contains(&self.facts.place(r).root));
        let roots: BTreeSet<RootId> = found.iter().map(|&r| self.facts.place(r).root).collect();
        let borrowed = self.borrowed_roots(&code, &roots);
        found.retain(|&r| !borrowed.contains(&self.facts.place(r).root));
        found
    }

    /// Returns the roots of `roots` that the code at the nodes `code` makes a
    /// reference into. A variable that gets a value there points into the root
    /// (a `let` of a borrow, a binding by reference, a temporary), or a call
    /// there gets a reference into the root.
    fn borrowed_roots(&self, code: &[(u32, u32)], roots: &BTreeSet<RootId>) -> BTreeSet<RootId> {
        let mut out = BTreeSet::new();
        if roots.is_empty() || code.is_empty() {
            return out;
        }
        let inside = |n: NodeId| code.iter().any(|&(lo, hi)| n.0 >= lo && n.0 < hi);
        let root = |p: PlaceId| self.facts.place(p).root;
        for &(n, p, _) in &self.facts.call_arg {
            if roots.contains(&root(p)) && inside(n) {
                out.insert(root(p));
            }
        }
        let mut into: BTreeMap<VarId, BTreeSet<RootId>> = BTreeMap::new();
        for &(v, p) in &self.facts.points_into {
            if roots.contains(&root(p)) {
                into.entry(v).or_default().insert(root(p));
            }
        }
        if into.is_empty() {
            return out;
        }
        for &(v, n) in &self.facts.rebound_at {
            if let Some(rs) = into.get(&v) {
                if inside(n) {
                    out.extend(rs.iter().copied());
                }
            }
        }
        out
    }

    /// The places that node `n` mutates, lends and reads from index `from` of
    /// the relations on, without the captures that the closures of summary `s`
    /// move: the run of a function argument at a call (`ArgRun`).
    pub(super) fn arg_places(
        &self,
        n: NodeId,
        s: usize,
        from: (usize, usize, usize),
    ) -> (Vec<PlaceId>, Vec<PlaceId>) {
        let moved = self.moved_capture_roots(s);
        let shared = |p: PlaceId| !moved.contains(&self.facts.place(p).root);
        let writes = self.facts.mutates_at[from.0..]
            .iter()
            .chain(&self.facts.lends_mut[from.1..])
            .filter(|&&(m, p)| m == n && shared(p))
            .map(|&(_, p)| p)
            .collect();
        let reads = self.facts.reads_at[from.2..]
            .iter()
            .filter(|&&(m, p)| m == n && shared(p))
            .map(|&(_, p)| p)
            .collect();
        (writes, reads)
    }

    /// Returns, for each position of `runs`, the places of the call that the
    /// callee writes and reads while it runs the argument: the places of its
    /// parameters in `TaskRun`, with the argument places `args`.
    pub(super) fn run_access(
        &mut self,
        runs: &BTreeMap<usize, TaskRun>,
        args: &[Vec<PlaceId>],
        split: u32,
    ) -> BTreeMap<usize, Access> {
        let mut out = BTreeMap::new();
        for (&pos, run) in runs {
            let mut w = Vec::new();
            for sp in &run.writes {
                w.extend(self.subst_place(sp, args, split));
            }
            let mut r = Vec::new();
            for sp in &run.reads {
                r.extend(self.subst_place(sp, args, split));
            }
            out.insert(pos, (w, r));
        }
        out
    }

    /// Returns, for each position of `runs`, each place that the reference
    /// arguments `args` give as a place that the callee can write while it runs
    /// the argument: code that the body does not know.
    pub(super) fn any_access(
        runs: &BTreeMap<usize, TaskRun>,
        args: &[Vec<PlaceId>],
    ) -> BTreeMap<usize, Access> {
        let all: Vec<PlaceId> = args.iter().flatten().copied().collect();
        runs.keys()
            .map(|&p| (p, (all.clone(), Vec::new())))
            .collect()
    }

    /// Returns the places that a function value that argument `v` holds can
    /// reach, if a callee made the value (`caps::MADE`): what the argument
    /// points into, and what the references at its places `ps` point into.
    pub(super) fn made_refs(
        &mut self,
        v: &Val,
        ps: &[PlaceId],
        held: &BTreeSet<super::caps::Held>,
    ) -> Vec<PlaceId> {
        let made =
            held.contains(&super::caps::MADE) || self.val_caps(v).contains(&super::caps::MADE);
        if !made {
            return Vec::new();
        }
        let mut out = v.refs.clone();
        out.extend(self.held_refs(ps));
        out.sort_unstable();
        out.dedup();
        out
    }

    /// The run of the function values that argument `pos` can hold, for
    /// example in a field. Each function value that the body stores can be one
    /// of them (`Lower::escaped`). The capabilities `held` of the argument name
    /// the function parameters whose values it can hold too. A value that a
    /// callee made can change and read the places `made` (`made_refs`).
    pub(super) fn held_run(
        &mut self,
        pos: usize,
        held: &BTreeSet<super::caps::Held>,
        made: &[PlaceId],
        span: Span,
    ) -> ArgRun {
        let mut m = Summary::default();
        for e in self.escaped.clone() {
            self.add_fn(&mut m, &e.info, e.row.as_deref());
        }
        for &p in made {
            m.lends.insert(p);
            m.reads.insert(p);
        }
        let own = |me: &Self, p: PlaceId| m.own_roots.contains(&me.facts.place(p).root);
        let writes = m
            .muts
            .iter()
            .chain(&m.lends)
            .copied()
            .filter(|&p| !own(self, p))
            .collect();
        let reads = m.reads.iter().copied().filter(|&p| !own(self, p)).collect();
        let mut params: BTreeSet<usize> = m.params.iter().chain(&m.passthrough).copied().collect();
        for mark in Self::task_marks(&self.expand_caps(held)) {
            if let super::caps::TaskMark::Param(p) = mark {
                params.insert(p);
            }
        }
        self.closures.push(m);
        let s = self.closures.len() - 1;
        ArgRun {
            pos,
            info: FnInfo {
                summary: Some(s),
                ..FnInfo::default()
            },
            row: None,
            writes,
            reads,
            span,
            held: params,
        }
    }

    /// Adds a node after the current node. It takes none of the pending uses
    /// and reads: those belong to the node before.
    fn chain(&mut self, span: Span) -> Option<NodeId> {
        let c = self.cur?;
        let n = self.facts.add_node(span, ARG_TASK, String::new());
        self.facts.cfg_edge.push((c, n));
        self.cur = Some(n);
        Some(n)
    }

    /// Node `n` reads each place that the run of argument `a` reads or writes.
    fn read_run(&mut self, n: NodeId, a: &ArgRun) {
        for &p in a.reads.iter().chain(&a.writes) {
            self.facts.reads_at.push((n, p));
        }
        // An argument that is a function parameter of the function runs here.
        if let Some((0, p)) = a.info.param {
            self.param_nodes.push((n, p));
        }
    }

    /// Makes a task of kind `kind` for the run of function argument `a`.
    /// Returns the task and the summary of the argument.
    fn arg_task(&mut self, kind: TaskKind, a: &ArgRun) -> (TaskId, usize) {
        let t = self.facts.add_task(kind, a.span);
        let s = self.value_summary(&a.info, a.row.as_deref());
        let sum = self.closures[s].clone();
        for &w in &a.writes {
            self.facts.task_writes.push((t, w));
        }
        for &r in &a.reads {
            self.facts.task_reads.push((t, r));
        }
        self.task_captures(t, &sum, &a.writes);
        (t, s)
    }

    /// A callee can run the function arguments `args` as tasks, as `runs`
    /// states for each argument position. The checks of a spawn apply at the
    /// call (ADR 0006). Each such argument runs as a task at new nodes after
    /// the call node. A fork branch of the callee is a fork task here (W0401,
    /// W0403). The task starts a second time if the callee can run it two
    /// times at one time. The nodes while it runs read what each argument
    /// that can run at the same time reads or writes (W0405). A node while it
    /// runs also writes and reads what `access` has for its position: the places
    /// that the callee accesses while the argument runs.
    pub(super) fn arg_tasks(
        &mut self,
        runs: &BTreeMap<usize, TaskRun>,
        args: &[ArgRun],
        access: &BTreeMap<usize, Access>,
        span: Span,
    ) {
        let at = |pos: usize| args.iter().position(|a| a.pos == pos);
        for (&pos, run) in runs {
            let Some(ai) = at(pos) else {
                continue;
            };
            let kind = if run.thread {
                TaskKind::Fork
            } else {
                TaskKind::Spawn
            };
            let Some(n) = self.chain(span) else {
                return;
            };
            let (t, s) = self.arg_task(kind, &args[ai]);
            self.facts.spawned_at.push((t, n));
            self.read_run(n, &args[ai]);
            self.task_runs.push(TaskRec {
                task: t,
                node: n,
                summary: s,
                arg: true,
                held: args[ai].held.clone(),
            });
            if run.twice {
                let Some(m) = self.chain(span) else {
                    return;
                };
                self.facts.spawned_at.push((t, m));
                self.read_run(m, &args[ai]);
            }
            if let Some((w, r)) = access
                .get(&pos)
                .filter(|(w, r)| !w.is_empty() || !r.is_empty())
            {
                let Some(m) = self.chain(span) else {
                    return;
                };
                // The callee changes the places as a value that can mutate them
                // does: the call node reports a mutation that needs a declaration.
                for &q in w {
                    self.facts.lends_mut.push((m, q));
                }
                for &q in r {
                    self.facts.reads_at.push((m, q));
                }
            }
            let with: Vec<usize> = run
                .with
                .iter()
                .filter_map(|&q| at(q))
                .filter(|&bi| bi != ai)
                .collect();
            for &bi in &with {
                let Some(m) = self.chain(span) else {
                    return;
                };
                self.read_run(m, &args[bi]);
            }
            let Some(e) = self.chain(span) else {
                return;
            };
            self.facts.joined_at.push((t, e));
            // The other direction, for an argument that does not run as a task
            // with this one in its own group.
            for bi in with {
                let q = args[bi].pos;
                if runs.get(&q).is_some_and(|r| r.with.contains(&pos)) {
                    continue;
                }
                let Some(m) = self.chain(span) else {
                    return;
                };
                let (u, s) = self.arg_task(TaskKind::Spawn, &args[bi]);
                self.facts.spawned_at.push((u, m));
                self.read_run(m, &args[bi]);
                self.task_runs.push(TaskRec {
                    task: u,
                    node: m,
                    summary: s,
                    arg: true,
                    held: args[bi].held.clone(),
                });
                let Some(m) = self.chain(span) else {
                    return;
                };
                self.read_run(m, &args[ai]);
                let Some(e) = self.chain(span) else {
                    return;
                };
                self.facts.joined_at.push((u, e));
            }
        }
    }

    /// The facts for work stealing at the end of the body, and the `pins` and
    /// `task_runs` parts of the signature.
    ///
    /// A task that runs a function parameter, a function value that the body
    /// does not know, or a function that can start a pinned task is `opaque`.
    /// A task that starts in the code of a task is in `spawns_in`. The body
    /// `pins` if a task is pinned for a reason other than a function
    /// parameter: a caller checks the value that it gives there.
    pub(super) fn finish_task_marks(&mut self) {
        let runs = self.task_runs.clone();
        let mut params: BTreeMap<TaskId, BTreeSet<usize>> = BTreeMap::new();
        let mut pinned: BTreeSet<TaskId> = BTreeSet::new();
        for r in &runs {
            let (t, s) = (r.task, r.summary);
            let sum = &self.closures[s];
            let mut ps: BTreeSet<usize> = sum
                .params
                .iter()
                .chain(&sum.passthrough)
                .chain(&r.held)
                .copied()
                .collect();
            // The code of the task can call a function value that the body does
            // not follow, for example one from a local container or tuple. It
            // can be each function parameter in scope there (`call_unknown`).
            let code: Vec<(u32, u32)> = sum
                .members
                .iter()
                .map(|&m| self.closures[m].nodes)
                .collect();
            let inside = |n: NodeId| code.iter().any(|&(lo, hi)| n.0 >= lo && n.0 < hi);
            ps.extend(
                self.param_nodes
                    .iter()
                    .filter(|&&(n, _)| inside(n))
                    .map(|&(_, p)| p),
            );
            let foreign = self.caller_runs.iter().any(|&n| inside(n));
            let hidden = sum.unknown
                || sum.items.iter().any(|&f| self.sigs[f].effects.pins)
                || self.runs_pin_call(sum);
            if !ps.is_empty() || hidden || foreign {
                self.facts.opaque.push(t);
            }
            if hidden {
                pinned.insert(t);
            }
            params.entry(t).or_default().extend(ps);
        }
        let inside = self.spawned_inside();
        let through: BTreeSet<(TaskId, VarId)> = self.facts.mut_through.iter().copied().collect();
        for &(t, v) in &self.facts.captures {
            let info = self.facts.var(v);
            if info.nonportable || (through.contains(&(t, v)) && !info.uniq) {
                pinned.insert(t);
            }
        }
        loop {
            let more: Vec<TaskId> = inside
                .iter()
                .filter(|(t, u)| pinned.contains(u) && !pinned.contains(t))
                .map(|&(t, _)| t)
                .collect();
            if more.is_empty() {
                break;
            }
            pinned.extend(more);
        }
        self.pins = !pinned.is_empty() || !self.pin_calls.is_empty();
        self.facts.spawns_in.extend(inside);
        let (runs, places) = self.task_runs_part(&params);
        self.task_runs_sig = runs;
        self.task_run_places = places;
    }

    /// Returns the pairs `(T, U)` where task `U` starts inside the code of task
    /// `T` (`spawns_in`).
    pub(super) fn spawned_inside(&self) -> Vec<(TaskId, TaskId)> {
        let mut inside = Vec::new();
        for r in &self.task_runs {
            for &m in &self.closures[r.summary].members {
                let (lo, hi) = self.closures[m].nodes;
                for &(u, n) in &self.facts.spawned_at {
                    if u != r.task && n.0 >= lo && n.0 < hi {
                        inside.push((r.task, u));
                    }
                }
            }
        }
        inside.sort_unstable();
        inside.dedup();
        inside
    }

    /// Returns the nodes where task `t` is active (`active(T, Q)`, as in the
    /// spec): from the nodes after a spawn node to a join node.
    pub(super) fn active_nodes(&self, t: TaskId, succ: &[Vec<NodeId>]) -> Vec<bool> {
        let ends: BTreeSet<usize> = self
            .facts
            .joined_at
            .iter()
            .filter(|(u, _)| *u == t)
            .map(|(_, p)| p.index())
            .collect();
        let mut on = vec![false; succ.len()];
        let mut todo: Vec<usize> = self
            .facts
            .spawned_at
            .iter()
            .filter(|(u, _)| *u == t)
            .flat_map(|(_, p)| succ[p.index()].iter().map(|q| q.index()))
            .collect();
        while let Some(q) = todo.pop() {
            if on[q] {
                continue;
            }
            on[q] = true;
            if !ends.contains(&q) {
                todo.extend(succ[q].iter().map(|r| r.index()));
            }
        }
        on
    }

    /// Returns true if a closure of summary `sum` calls a function that can
    /// start a pinned task (`Lower::pin_calls`).
    pub(super) fn runs_pin_call(&self, sum: &Summary) -> bool {
        sum.members.iter().any(|&m| {
            let (lo, hi) = self.closures[m].nodes;
            self.pin_calls.iter().any(|n| n.0 >= lo && n.0 < hi)
        })
    }

    /// The `task_runs` part of the signature: how the tasks of the body run the
    /// function parameters. `params` has the parameters that each task runs.
    /// Two runs are at one time if one starts while the other is active.
    ///
    /// It also returns the places that the body writes and reads while each
    /// parameter runs: at the nodes where the task is active, and in the other
    /// tasks that run at the same time.
    fn task_runs_part(
        &self,
        params: &BTreeMap<TaskId, BTreeSet<usize>>,
    ) -> (BTreeMap<usize, TaskRun>, RunPlaces) {
        let mut out: BTreeMap<usize, TaskRun> = BTreeMap::new();
        let mut places = RunPlaces::new();
        let tasks: Vec<TaskId> = params
            .iter()
            .filter(|(_, ps)| !ps.is_empty())
            .map(|(&t, _)| t)
            .collect();
        if tasks.is_empty() {
            return (out, places);
        }
        let succ = self.successors();
        let starts = |t: TaskId| -> Vec<usize> {
            self.facts
                .spawned_at
                .iter()
                .filter(|(u, _)| *u == t)
                .map(|(_, p)| p.index())
                .collect()
        };
        let act: BTreeMap<TaskId, Vec<bool>> = tasks
            .iter()
            .map(|&t| (t, self.active_nodes(t, &succ)))
            .collect();
        let st: BTreeMap<TaskId, Vec<usize>> = tasks.iter().map(|&t| (t, starts(t))).collect();
        let empty = BTreeSet::new();
        // Each task of the body, with its start nodes and active nodes.
        let all: Vec<(TaskId, Vec<usize>, Vec<bool>)> = (0..self.facts.tasks.len())
            .map(|i| {
                let u = TaskId(u32::try_from(i).unwrap_or(u32::MAX));
                (u, starts(u), self.active_nodes(u, &succ))
            })
            .collect();
        for &t in &tasks {
            let a = &act[&t];
            let ps = params.get(&t).unwrap_or(&empty);
            let again = st[&t].iter().any(|&p| a[p]);
            let at_nodes: Vec<usize> = self
                .param_nodes
                .iter()
                .filter(|(m, _)| a[m.index()])
                .map(|&(_, q)| q)
                .collect();
            let mut others: Vec<usize> = Vec::new();
            for &u in &tasks {
                let overlap =
                    u != t && (st[&u].iter().any(|&p| a[p]) || st[&t].iter().any(|&p| act[&u][p]));
                if overlap {
                    others.extend(params.get(&u).unwrap_or(&empty).iter().copied());
                }
            }
            // What the body and its other tasks access while the task runs.
            let mut writes: BTreeSet<PlaceId> = BTreeSet::new();
            let mut reads: BTreeSet<PlaceId> = BTreeSet::new();
            for &(m, q) in self.facts.mutates_at.iter().chain(&self.facts.lends_mut) {
                if a[m.index()] {
                    writes.insert(q);
                }
            }
            for &(m, q) in &self.facts.reads_at {
                if a[m.index()] {
                    reads.insert(q);
                }
            }
            for (u, ust, uact) in &all {
                let overlap =
                    *u != t && (ust.iter().any(|&p| a[p]) || st[&t].iter().any(|&p| uact[p]));
                if !overlap {
                    continue;
                }
                for &(x, q) in &self.facts.task_writes {
                    if x == *u {
                        writes.insert(q);
                    }
                }
                for &(x, q) in &self.facts.task_reads {
                    if x == *u {
                        reads.insert(q);
                    }
                }
            }
            for &p in ps {
                let e = places.entry(p).or_default();
                e.0.extend(writes.iter().copied());
                e.1.extend(reads.iter().copied());
                let run = out.entry(p).or_default();
                run.thread |= self.facts.tasks[t.index()].kind == TaskKind::Fork;
                run.twice |= again;
                for &q in at_nodes.iter().chain(&others) {
                    if q == p {
                        run.twice = true;
                    } else {
                        run.with.insert(q);
                    }
                }
            }
        }
        (out, places)
    }

    /// The `task_runs` part of the signature, with the places of the parameters
    /// that the body writes and reads while each one runs. `bases` has the root
    /// places of the parameters. A place of a local of the body is not part of
    /// it: a caller does not see it.
    pub(super) fn task_runs_with_places(&self, bases: &[Vec<PlaceId>]) -> BTreeMap<usize, TaskRun> {
        let mut out = self.task_runs_sig.clone();
        for (p, run) in &mut out {
            let Some((w, r)) = self.task_run_places.get(p) else {
                continue;
            };
            for (from, to) in [(w, &mut run.writes), (r, &mut run.reads)] {
                for &q in from {
                    let base = self.facts.wild_base(q).unwrap_or(q);
                    if let Some(sp) = self.sig_place(base, bases) {
                        if !to.contains(&sp) {
                            to.push(sp);
                        }
                    }
                }
            }
        }
        out
    }

    /// Returns the worst way to run the function arguments at the positions
    /// `fns` as tasks: on another thread, two times at one time, and at the same
    /// time as the others. Code that the body does not know runs them so.
    pub(super) fn worst_runs(fns: &[usize]) -> BTreeMap<usize, TaskRun> {
        fns.iter()
            .map(|&i| {
                let with = fns.iter().copied().filter(|&j| j != i).collect();
                (
                    i,
                    TaskRun {
                        thread: true,
                        twice: true,
                        with,
                        ..TaskRun::default()
                    },
                )
            })
            .collect()
    }

    /// Returns how function value `callee` runs the function arguments at the
    /// positions `fns` as tasks. A function item states it in its signature. A
    /// value that the body does not follow, and a closure whose task calls its
    /// parameter, can run the argument in the worst way: on another thread,
    /// two times at one time, and at the same time as the other arguments.
    pub(super) fn value_task_runs(
        &self,
        callee: &FnInfo,
        fns: &[usize],
    ) -> BTreeMap<usize, TaskRun> {
        let worst = |i: usize| TaskRun {
            thread: true,
            twice: true,
            with: fns.iter().copied().filter(|&j| j != i).collect(),
            ..TaskRun::default()
        };
        let mut out: BTreeMap<usize, TaskRun> = BTreeMap::new();
        let (unknown, tasks, items) = match callee.summary {
            Some(s) => {
                let sum = &self.closures[s];
                (
                    sum.unknown || !sum.params.is_empty(),
                    sum.tasks.to_set(),
                    sum.items.to_set(),
                )
            }
            None => (
                callee.item.is_none(),
                BTreeSet::new(),
                callee.item.into_iter().collect(),
            ),
        };
        for &i in fns {
            if unknown || tasks.contains(&i) {
                out.insert(i, worst(i));
            }
        }
        for f in items {
            for (i, run) in self.callee_task_runs(f, fns) {
                let e = out.entry(i).or_default();
                e.thread |= run.thread;
                e.twice |= run.twice;
                e.with.extend(run.with);
            }
        }
        out
    }

    /// Returns how the callee `f` runs each function argument as a task: its
    /// `task_runs` part. Foreign code can run each function argument on another
    /// thread, more than once and at the same time as the others. `http.serve`
    /// runs its handler as a task for each request, more than once at one time.
    pub(super) fn callee_task_runs(
        &self,
        f: super::FnId,
        fns: &[usize],
    ) -> BTreeMap<usize, TaskRun> {
        if !self.item_runs_tasks(f) {
            return self.sigs[f].effects.task_runs.clone();
        }
        let def = &self.prog.fns[f];
        let foreign = !def.is_std;
        fns.iter()
            .map(|&i| {
                let with = fns.iter().copied().filter(|&j| j != i).collect();
                (
                    i,
                    TaskRun {
                        thread: foreign,
                        twice: true,
                        with,
                        ..TaskRun::default()
                    },
                )
            })
            .collect()
    }
}
