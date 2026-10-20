//! Captured variables that get a new value after the closure is made.
//!
//! A closure refers to the cells of the variables that it captures (ADR 0003).
//! It reads a variable when it runs, not when it is made. The lowering of the
//! closure body uses the values that the variables have where the closure is
//! made. So each node that runs the closure joins the values that the
//! variables have at that node: their new places, their new function values
//! and their modes. A task runs while its parent goes on, so it gets each value
//! that its captured variables get after the spawn too.

use super::fnval::{FnInfo, Given, RowFn};
use super::{fn_row, Lower, NodeId, PlaceId, Summary, TaskId, Ty, Val, VarId};
use std::collections::{BTreeMap, BTreeSet};
use weft_facts::{RootId, Span};

/// A variable that a closure captures by reference, with its value where the
/// closure is made.
#[derive(Clone, Debug)]
pub(super) struct CapValue {
    /// The variable.
    pub var: VarId,
    /// The places of the value.
    pub refs: Vec<PlaceId>,
    /// The function value, with its effect row, for a variable of a function type.
    pub fn_value: Option<RowFn>,
}

/// A captured variable whose value changed since the closure was made.
struct Change {
    /// The variable.
    var: VarId,
    /// Its local.
    local: usize,
    /// The places that it had where the closure was made.
    old: Vec<PlaceId>,
    /// The places that it has now, and did not have there.
    new: Vec<PlaceId>,
    /// The hidden variables of the parts of the local (`PartHolder`). A run of
    /// the closure uses them too.
    parts: Vec<VarId>,
    /// The function value that it has now, if it is another one.
    now: Option<FnInfo>,
    /// The closure runs here, and it needs the variable to be `@ uniq`.
    uniq_need: bool,
    /// The variable is not `@ uniq` now.
    aliased: bool,
}

impl Lower<'_> {
    /// Records the variables that closure `id` captures by reference, with their
    /// values now. `owned` has the captures that the closure takes by value.
    pub(super) fn note_cap_values(&mut self, id: usize, captures: &[VarId], owned: &[VarId]) {
        let mut out = Vec::new();
        for &var in captures.iter().filter(|v| !owned.contains(v)) {
            let Some(l) = self.local_of(var) else {
                continue;
            };
            let ty = self.inf.shallow(&self.locals[l].ty);
            let fn_value = matches!(ty, Ty::Fn(_)).then(|| (self.local_fn_info(l), fn_row(&ty)));
            out.push(CapValue {
                var,
                refs: self.cap_refs_now(l).0,
                fn_value,
            });
        }
        self.cap_values.insert(id, out);
    }

    /// The places that local `l` points into now, also through its parts, and the
    /// hidden variables of its parts. At the end of the body, each part value
    /// that the local had counts, as each value of the local does.
    pub(super) fn cap_refs_now(&self, l: usize) -> (Vec<PlaceId>, Vec<VarId>) {
        let mut refs = self.locals[l].refs.clone();
        let mut vars = Vec::new();
        let holders = if self.lowered {
            &self.holder_log
        } else {
            &self.part_holders
        };
        for h in holders.iter().filter(|h| h.local == l) {
            for &p in &h.refs {
                if !refs.contains(&p) {
                    refs.push(p);
                }
            }
            if !vars.contains(&h.var) {
                vars.push(h.var);
            }
        }
        (refs, vars)
    }

    /// Records that the body runs local `l` with the places `given`. Each closure
    /// around the node that captures `l` keeps the run (`Summary::cap_runs`).
    pub(super) fn note_cap_run(&mut self, l: usize, given: &[Given]) {
        let var = self.locals[l].var;
        for si in self.capturing(l) {
            let run = (var, given.to_vec());
            if !self.sums[si].cap_runs.contains(&run) {
                self.sums[si].cap_runs.push(run);
            }
        }
    }

    /// Records that the body gives local `l` to a parameter that must be
    /// `@ uniq`. A node that runs a closure that captures `l`, where `l` is not
    /// `@ uniq`, gets W0406 (`not_uniq`).
    pub(super) fn note_cap_uniq(&mut self, l: usize, need: &super::UniqNeed) {
        let var = self.locals[l].var;
        for si in self.capturing(l) {
            let need = (var, need.clone());
            if !self.sums[si].uniq_needs.contains(&need) {
                self.sums[si].uniq_needs.push(need);
            }
        }
    }

    /// Gives the facts of a call in a closure that runs at node `n`: the call
    /// gives a captured local to a `@ uniq` parameter (`uniq_param`), and, if
    /// `aliased`, the local is not `@ uniq` at `n` (`arg_aliased`). The spec
    /// decides W0406 (`not_uniq`). The index is [`weft_facts::CLOSURE_ARG`] and
    /// more, one for each such call at `n`.
    fn closure_uniq_need(&mut self, n: NodeId, need: &super::UniqNeed, aliased: bool) {
        let at_n = self
            .facts
            .uniq_param
            .iter()
            .filter(|&&(p, i)| p == n && i >= weft_facts::CLOSURE_ARG)
            .count();
        let index = weft_facts::CLOSURE_ARG.saturating_add(u32::try_from(at_n).unwrap_or(u32::MAX));
        self.facts.uniq_param.push((n, index));
        if aliased {
            self.facts.arg_aliased.push((n, index));
        }
        let span = self.facts.node(n).span;
        self.facts.arg_sites.push(weft_facts::ArgSite {
            node: n,
            index,
            span,
            callee: need.callee.clone(),
            param: need.param.clone(),
            needs: String::new(),
            via: Some(need.local.clone()),
        });
    }

    /// The summary indexes of the open closures and clauses that capture local `l`.
    fn capturing(&self, l: usize) -> Vec<usize> {
        let depth = self.local_frame(l);
        self.frames
            .iter()
            .enumerate()
            .filter(|(fi, _)| *fi > depth)
            .filter_map(|(_, f)| f.barrier)
            .collect()
    }

    /// Returns true if place `p` is at or below place `base`.
    fn at_or_below(&self, p: PlaceId, base: PlaceId) -> bool {
        let mut at = Some(p);
        while let Some(a) = at {
            if a == base {
                return true;
            }
            at = self.facts.place(a).parent;
        }
        false
    }

    /// The places of `ps` at or below a place of `old`, moved onto each place of
    /// `new` with the same steps.
    fn rebased(&mut self, ps: &[PlaceId], old: &[PlaceId], new: &[PlaceId]) -> Vec<PlaceId> {
        let mut out = Vec::new();
        for &p in ps {
            for &o in old {
                if !self.at_or_below(p, o) {
                    continue;
                }
                for &q in new {
                    let r = self.rebase(p, o, q);
                    if !out.contains(&r) {
                        out.push(r);
                    }
                }
            }
        }
        out
    }

    /// Node `n` runs the closures of summary `s`, with the places `given`. `root`
    /// is the callee root index of the captures. For each captured variable with
    /// a value that it did not have where the closure was made, the node:
    ///
    /// - uses the variable and the hidden variables of its parts: the closure
    ///   reads them here;
    /// - mutates, reads and lends the places of the closure below the old places,
    ///   moved onto the new places;
    /// - runs the new function value where the closure runs the variable;
    /// - gives the facts of W0406 (with `at_run`) if the closure needs the
    ///   variable to be `@ uniq`: the spec reports it if the variable is not
    ///   `@ uniq` here.
    ///
    /// A captured function variable that the closure runs, and that has the same
    /// value, can run a closure whose own captures have new values. The node joins
    /// them too.
    pub(super) fn late_join(
        &mut self,
        n: NodeId,
        s: usize,
        root: u32,
        given: &[Given],
        at_run: bool,
    ) {
        let members: Vec<usize> = self.closures[s].members.iter().copied().collect();
        for c in members {
            if self.late_stack.contains(&c) {
                continue;
            }
            let changes = self.late_changes(c, at_run);
            let inner = self.late_inner(c);
            if changes.is_empty() && inner.is_empty() {
                continue;
            }
            self.late_stack.push(c);
            let sum = self.closures[c].clone();
            for ch in changes {
                if !ch.new.is_empty() || ch.now.is_some() {
                    self.facts.uses.push((ch.var, n));
                    for &h in &ch.parts {
                        self.facts.uses.push((h, n));
                    }
                    if at_run {
                        self.note_capture(ch.local);
                    }
                }
                if !ch.new.is_empty() {
                    let muts: Vec<PlaceId> = sum.muts.iter().copied().collect();
                    for q in self.rebased(&muts, &ch.old, &ch.new) {
                        self.mutate(n, q);
                        self.facts.call_mut.push((n, q, root));
                    }
                    let reads: Vec<PlaceId> = sum.reads.iter().copied().collect();
                    for q in self.rebased(&reads, &ch.old, &ch.new) {
                        self.facts.reads_at.push((n, q));
                        self.sum().reads.insert(q);
                    }
                    let lends: Vec<PlaceId> = sum.lends.iter().copied().collect();
                    for q in self.rebased(&lends, &ch.old, &ch.new) {
                        self.lend(n, q, root);
                    }
                    for &(cap, op, pos, p) in &sum.op_args {
                        for q in self.rebased(&[p], &ch.old, &ch.new) {
                            self.give_op(n, cap, op, pos, q, root);
                        }
                    }
                }
                if let Some(info) = &ch.now {
                    let row = fn_row(&self.inf.shallow(&self.locals[ch.local].ty));
                    for (v, inner) in &sum.cap_runs {
                        if *v != ch.var {
                            continue;
                        }
                        let mapped = self.map_given(&sum, inner, root, given);
                        self.apply_value(n, info, row.as_deref(), root, &mapped);
                    }
                }
                if ch.uniq_need {
                    for (v, need) in &sum.uniq_needs {
                        if *v == ch.var {
                            self.closure_uniq_need(n, need, ch.aliased);
                        }
                    }
                }
            }
            for (var, t) in inner {
                for (v, runs) in &sum.cap_runs {
                    if *v != var {
                        continue;
                    }
                    let mapped = self.map_given(&sum, runs, root, given);
                    self.late_join(n, t, root, &mapped, at_run);
                }
            }
            self.late_stack.pop();
        }
    }

    /// The places that the places `inner` of summary `sum` stand for where the
    /// summary runs with the places `given`.
    fn map_given(
        &mut self,
        sum: &Summary,
        inner: &[Given],
        root: u32,
        given: &[Given],
    ) -> Vec<Given> {
        let mut mapped = Vec::new();
        for g in inner {
            for (q, r) in self.places_of(sum, g.place, root, given) {
                mapped.push(Given {
                    pos: g.pos,
                    place: q,
                    root: r,
                });
            }
        }
        mapped
    }

    /// The captured function variables of closure `c` that the closure runs and
    /// that have the same value now. Each has the closure summary of the value.
    fn late_inner(&self, c: usize) -> Vec<(VarId, usize)> {
        let mut out = Vec::new();
        let sum = &self.closures[c];
        for cv in self.cap_values.get(&c).into_iter().flatten() {
            let Some((old, _)) = &cv.fn_value else {
                continue;
            };
            if !sum.cap_runs.iter().any(|(v, _)| *v == cv.var) {
                continue;
            }
            let Some(l) = self.local_of(cv.var) else {
                continue;
            };
            let now = self.local_fn_info(l);
            if &now != old {
                continue;
            }
            if let Some(t) = now.summary {
                out.push((cv.var, t));
            }
        }
        out
    }

    /// The captured variables of closure `c` whose values changed since the
    /// closure was made. With `at_run`, also each variable that the closure needs
    /// to be `@ uniq`.
    fn late_changes(&self, c: usize, at_run: bool) -> Vec<Change> {
        let mut out = Vec::new();
        let needs = &self.closures[c].uniq_needs;
        for cv in self.cap_values.get(&c).into_iter().flatten() {
            let Some(l) = self.local_of(cv.var) else {
                continue;
            };
            let (now_refs, parts) = self.cap_refs_now(l);
            let new: Vec<PlaceId> = now_refs
                .into_iter()
                .filter(|p| !cv.refs.contains(p))
                .collect();
            let now = match &cv.fn_value {
                Some((old, _)) => Some(self.local_fn_info(l)).filter(|f| f != old),
                None => None,
            };
            let uniq_need = at_run && needs.iter().any(|(v, _)| *v == cv.var);
            let aliased = uniq_need && !self.locals.is_uniq(l);
            if !new.is_empty() || now.is_some() || uniq_need {
                out.push(Change {
                    var: cv.var,
                    local: l,
                    old: cv.refs.clone(),
                    new,
                    parts,
                    now,
                    uniq_need,
                    aliased,
                });
            }
        }
        out
    }

    /// The places that the closures of summary `s` point into now through their
    /// captured variables, and did not where they were made. A captured function
    /// variable adds the places of its value now. A closure that leaves the body
    /// (a return or a store) points into them too.
    pub(super) fn late_refs(&self, s: usize) -> Vec<PlaceId> {
        let mut out = Vec::new();
        self.late_refs_into(s, &mut Vec::new(), &mut out);
        out
    }

    /// The places that the closures in value `v` and in its parts point into
    /// now, and did not where they were made (`late_refs`).
    pub(super) fn val_late_refs(&self, v: &Val) -> Vec<PlaceId> {
        let mut out = Vec::new();
        let mut seen = Vec::new();
        let mut work = vec![v];
        while let Some(x) = work.pop() {
            if let Some(s) = self.fn_info(x).summary {
                self.late_refs_into(s, &mut seen, &mut out);
            }
            work.extend(x.parts.iter().flatten());
        }
        out
    }

    /// Returns value `v` with the places that its function values point into
    /// now. A closure points where its captures point now (`val_late_refs`). A
    /// local holds the closures in its parts and its containers too
    /// (`held_fn_refs`). A value that leaves the body, or goes into a tuple, a
    /// struct or an array, keeps them.
    pub(super) fn with_fn_refs(&self, v: Val) -> Val {
        if !self.has_fn(&v.ty) {
            return v;
        }
        let mut v = v;
        let mut more = self.val_late_refs(&v);
        if !matches!(self.inf.shallow(&v.ty), Ty::Fn(_)) {
            more.extend(self.held_fn_refs(&v));
        }
        for p in more {
            if !v.refs.contains(&p) {
                v.refs.push(p);
            }
        }
        v
    }

    /// The places that the function values in the locals of value `v` and of its
    /// parts point into. The values are in their parts (`PartHolder`) and in
    /// their containers (`Lower::held_fns`). The new values of their captures
    /// count too.
    pub(super) fn held_fn_refs(&self, v: &Val) -> Vec<PlaceId> {
        let mut out = Vec::new();
        let mut seen = Vec::new();
        let mut work = vec![v];
        while let Some(x) = work.pop() {
            work.extend(x.parts.iter().flatten());
            let Some(l) = x.local else {
                continue;
            };
            for p in self.cap_refs_now(l).0 {
                if !out.contains(&p) {
                    out.push(p);
                }
            }
            for (_, f) in self.held_fns.iter().filter(|(m, _)| *m == l) {
                for &p in &f.refs {
                    if !out.contains(&p) {
                        out.push(p);
                    }
                }
                if let Some(s) = self.fn_info(f).summary {
                    self.late_refs_into(s, &mut seen, &mut out);
                }
            }
        }
        out
    }

    fn late_refs_into(&self, s: usize, seen: &mut Vec<usize>, out: &mut Vec<PlaceId>) {
        for &c in &self.closures[s].members {
            if seen.contains(&c) {
                continue;
            }
            seen.push(c);
            for cv in self.cap_values.get(&c).into_iter().flatten() {
                let Some(l) = self.local_of(cv.var) else {
                    continue;
                };
                for p in self.cap_refs_now(l).0 {
                    if !cv.refs.contains(&p) && !out.contains(&p) {
                        out.push(p);
                    }
                }
                if cv.fn_value.is_some() {
                    if let Some(t) = self.local_fn_info(l).summary {
                        self.late_refs_into(t, seen, out);
                    }
                }
            }
        }
    }

    /// The places that a call of a closure of summary `s` returns through the new
    /// values of its captured variables.
    pub(super) fn late_ret_refs(&mut self, s: usize) -> Vec<PlaceId> {
        let mut out = Vec::new();
        let members: Vec<usize> = self.closures[s].members.iter().copied().collect();
        for c in members {
            let rets = self.closures[c].ret_refs.clone();
            for cv in self.cap_values.get(&c).cloned().unwrap_or_default() {
                let Some(l) = self.local_of(cv.var) else {
                    continue;
                };
                let new: Vec<PlaceId> = self
                    .cap_refs_now(l)
                    .0
                    .into_iter()
                    .filter(|p| !cv.refs.contains(p))
                    .collect();
                out.extend(self.rebased(&rets, &cv.refs, &new));
            }
        }
        out
    }

    /// Returns true if a closure of summary `s` can run only once: it moves a
    /// capture, or a captured function variable has a value now that runs only
    /// once, and the closure runs that variable.
    pub(super) fn closure_once_now(&self, s: usize) -> bool {
        self.closure_is_once(s) || self.late_once(s, &mut Vec::new())
    }

    fn late_once(&self, s: usize, seen: &mut Vec<usize>) -> bool {
        for &c in &self.closures[s].members {
            if seen.contains(&c) {
                continue;
            }
            seen.push(c);
            let sum = &self.closures[c];
            for cv in self.cap_values.get(&c).into_iter().flatten() {
                let Some((old, _)) = &cv.fn_value else {
                    continue;
                };
                if !sum.cap_runs.iter().any(|(v, _)| *v == cv.var) {
                    continue;
                }
                let Some(l) = self.local_of(cv.var) else {
                    continue;
                };
                // The same value can run a closure whose captures have new values.
                let now = self.local_fn_info(l);
                if let Some(t) = now.summary {
                    if (&now != old && self.closure_is_once(t)) || self.late_once(t, seen) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Records task `t` that node `n` spawns with the closures of summary `s`.
    /// The task can run the function values that the function parameters
    /// `held` hold, for example in a field.
    pub(super) fn note_task_run(&mut self, t: TaskId, n: NodeId, s: usize, held: BTreeSet<usize>) {
        self.task_runs.push(super::tasks::TaskRec {
            task: t,
            node: n,
            summary: s,
            arg: false,
            held,
        });
    }

    /// The places that node `n` mutates, lends and reads from index `from` of the
    /// relations on: task `t`, which the node starts with the closures of
    /// summary `s`, writes and reads them. The node gives no place inside the
    /// closure of the task (`places_of`). A capture that the closure moves is in
    /// a cell of the closure, so the task does not share it.
    pub(super) fn task_places_from(
        &mut self,
        t: TaskId,
        n: NodeId,
        s: usize,
        from: (usize, usize, usize),
    ) {
        let moved = self.moved_capture_roots(s);
        let shared = |me: &Self, p: PlaceId| !moved.contains(&me.facts.place(p).root);
        let writes: Vec<PlaceId> = self.facts.mutates_at[from.0..]
            .iter()
            .chain(&self.facts.lends_mut[from.1..])
            .filter(|&&(m, p)| m == n && shared(self, p))
            .map(|&(_, p)| p)
            .collect();
        let reads: Vec<PlaceId> = self.facts.reads_at[from.2..]
            .iter()
            .filter(|&&(m, p)| m == n && shared(self, p))
            .map(|&(_, p)| p)
            .collect();
        for p in writes {
            self.facts.task_writes.push((t, p));
        }
        for p in reads {
            self.facts.task_reads.push((t, p));
        }
    }

    /// Tasks `ts` end at the node before a new node: a `join`, the end of a
    /// `fork` or a scope. A task can change what it writes at any time while it
    /// runs, so the new node changes it again (`finish_task_ends`). The tasks
    /// are not active at the new node.
    pub(super) fn end_tasks(&mut self, ts: &[TaskId], span: Span) {
        if ts.is_empty() || self.cur.is_none() {
            return;
        }
        let e = self.emit(span, weft_facts::TASK_END, String::new());
        for &t in ts {
            self.task_ends.push((t, e));
        }
    }

    /// Gives each node after the end of a task the places that the task writes,
    /// as places that it can change (`lends_mut`). A reference that the body
    /// makes while the task runs is invalid after the end, if the task changes
    /// what it points into (W0301). The body is lowered, so each task has all
    /// of its places.
    ///
    /// The writes of a task include the writes of a task that it starts in a
    /// scope outside it. That task can still run at the end node. Then its own
    /// end changes these places, and each node while it runs must not access
    /// them, so the end node leaves them out.
    pub(super) fn finish_task_ends(&mut self) {
        let mut writes: BTreeMap<TaskId, Vec<PlaceId>> = BTreeMap::new();
        for &(t, m) in &self.facts.task_writes {
            writes.entry(t).or_default().push(m);
        }
        let mut inner: BTreeMap<TaskId, Vec<TaskId>> = BTreeMap::new();
        for (t, u) in self.spawned_inside() {
            inner.entry(t).or_default().push(u);
        }
        let succ = if inner.is_empty() {
            Vec::new()
        } else {
            self.successors()
        };
        let mut active: BTreeMap<TaskId, Vec<bool>> = BTreeMap::new();
        for &(t, e) in &self.task_ends.clone() {
            let mut still: BTreeSet<PlaceId> = BTreeSet::new();
            for &u in inner.get(&t).into_iter().flatten() {
                let on = active
                    .entry(u)
                    .or_insert_with(|| self.active_nodes(u, &succ));
                if on.get(e.index()).copied().unwrap_or(false) {
                    still.extend(writes.get(&u).into_iter().flatten().copied());
                }
            }
            for &m in writes.get(&t).into_iter().flatten() {
                if !still.contains(&m) {
                    self.facts.lends_mut.push((e, m));
                }
            }
        }
    }

    /// Returns the roots of the captures that the closures of summary `s` move:
    /// the closure takes each of them into a cell of its own when it is made
    /// (ADR 0003).
    pub(super) fn moved_capture_roots(&self, s: usize) -> BTreeSet<RootId> {
        self.closures[s]
            .moved_captures
            .iter()
            .filter(|&&v| !self.is_copy_var(v))
            .filter_map(|&v| self.local_of(v))
            .filter_map(|l| self.locals[l].root)
            .map(|r| self.facts.place(r).root)
            .collect()
    }

    /// The sizes of the relations that `task_places_from` reads.
    pub(super) fn place_marks(&self) -> (usize, usize, usize) {
        (
            self.facts.mutates_at.len(),
            self.facts.lends_mut.len(),
            self.facts.reads_at.len(),
        )
    }

    /// Each task gets the values that its captured variables get while it runs.
    /// The body is lowered, so the locals have each of their values: the spawn
    /// node joins them, and the task writes and reads what they reach.
    pub(super) fn finish_task_values(&mut self) {
        for r in self.task_runs.clone() {
            let (t, n, s) = (r.task, r.node, r.summary);
            // The call node of a run of a function argument gets the values
            // (`tasks::arg_tasks`).
            if r.arg {
                continue;
            }
            let from = self.place_marks();
            self.late_join(n, s, super::roots::TASK, &[], false);
            self.task_places_from(t, n, s, from);
        }
    }
}
