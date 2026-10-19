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
use super::{fn_row, Lower, NodeId, PlaceId, TaskId, Ty, VarId};

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
    /// The function value that it has now, if it is another one.
    now: Option<FnInfo>,
    /// The closure needs it to be `@ uniq`, and it is not `@ uniq` now.
    not_uniq: bool,
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
                refs: self.locals[l].refs.clone(),
                fn_value,
            });
        }
        self.cap_values.insert(id, out);
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
    /// `@ uniq`. `text` is the text of W0406 for a node that runs a closure that
    /// captures `l`, where `l` is not `@ uniq`.
    pub(super) fn note_cap_uniq(&mut self, l: usize, text: &str) {
        let var = self.locals[l].var;
        for si in self.capturing(l) {
            let need = (var, text.to_string());
            if !self.sums[si].uniq_needs.contains(&need) {
                self.sums[si].uniq_needs.push(need);
            }
        }
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
    /// - uses the variable: the closure reads it here;
    /// - mutates, reads and lends the places of the closure below the old places,
    ///   moved onto the new places;
    /// - runs the new function value where the closure runs the variable;
    /// - reports W0406 (with `at_run`) if the closure needs the variable to be
    ///   `@ uniq` and it is not `@ uniq` here.
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
            if changes.is_empty() {
                continue;
            }
            self.late_stack.push(c);
            let sum = self.closures[c].clone();
            for ch in changes {
                if !ch.new.is_empty() || ch.now.is_some() {
                    self.facts.uses.push((ch.var, n));
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
                        let mut mapped = Vec::new();
                        for g in inner {
                            for (q, r) in self.places_of(&sum, g.place, root, given) {
                                mapped.push(Given {
                                    pos: g.pos,
                                    place: q,
                                    root: r,
                                });
                            }
                        }
                        self.apply_value(n, info, row.as_deref(), root, &mapped);
                    }
                }
                if ch.not_uniq {
                    let span = self.facts.node(n).span;
                    for (v, text) in &sum.uniq_needs {
                        if *v == ch.var {
                            self.err("W0406", text.clone(), span);
                        }
                    }
                }
            }
            self.late_stack.pop();
        }
    }

    /// The captured variables of closure `c` whose values changed since the
    /// closure was made. With `at_run`, also each variable that the closure needs
    /// to be `@ uniq` and that is not `@ uniq` now.
    fn late_changes(&self, c: usize, at_run: bool) -> Vec<Change> {
        let mut out = Vec::new();
        let needs = &self.closures[c].uniq_needs;
        for cv in self.cap_values.get(&c).into_iter().flatten() {
            let Some(l) = self.local_of(cv.var) else {
                continue;
            };
            let new: Vec<PlaceId> = self.locals[l]
                .refs
                .iter()
                .copied()
                .filter(|p| !cv.refs.contains(p))
                .collect();
            let now = match &cv.fn_value {
                Some((old, _)) => Some(self.local_fn_info(l)).filter(|f| f != old),
                None => None,
            };
            let not_uniq =
                at_run && !self.locals.is_uniq(l) && needs.iter().any(|(v, _)| *v == cv.var);
            if !new.is_empty() || now.is_some() || not_uniq {
                out.push(Change {
                    var: cv.var,
                    local: l,
                    old: cv.refs.clone(),
                    new,
                    now,
                    not_uniq,
                });
            }
        }
        out
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
                let new: Vec<PlaceId> = self.locals[l]
                    .refs
                    .iter()
                    .copied()
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
                let now = self.local_fn_info(l);
                if &now == old {
                    continue;
                }
                if let Some(t) = now.summary {
                    if self.closure_is_once(t) || self.late_once(t, seen) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Records task `t` that node `n` spawns with the closures of summary `s`.
    pub(super) fn note_task_run(&mut self, t: TaskId, n: NodeId, s: usize) {
        self.task_runs.push((t, n, s));
    }

    /// The places that node `n` mutates, lends and reads from index `from` of the
    /// relations on: task `t`, which the node starts, writes and reads them. The
    /// node gives no place inside the closure of the task (`places_of`).
    pub(super) fn task_places_from(&mut self, t: TaskId, n: NodeId, from: (usize, usize, usize)) {
        let writes: Vec<PlaceId> = self.facts.mutates_at[from.0..]
            .iter()
            .chain(&self.facts.lends_mut[from.1..])
            .filter(|(m, _)| *m == n)
            .map(|&(_, p)| p)
            .collect();
        let reads: Vec<PlaceId> = self.facts.reads_at[from.2..]
            .iter()
            .filter(|(m, _)| *m == n)
            .map(|&(_, p)| p)
            .collect();
        for p in writes {
            self.facts.task_writes.push((t, p));
        }
        for p in reads {
            self.facts.task_reads.push((t, p));
        }
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
        for (t, n, s) in self.task_runs.clone() {
            let from = self.place_marks();
            self.late_join(n, s, 700, &[], false);
            self.task_places_from(t, n, from);
        }
    }
}
