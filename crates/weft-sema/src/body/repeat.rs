//! Function values that can run more than once at one node.
//!
//! A callee can call its function parameter more than once, for example in a
//! loop. A task that a closure spawns into an outer scope then starts more than
//! once at the node that gives the closure, and the copies run at the same time.
//! The signature has a `repeats` part: the function parameters that the body can
//! call more than once.

use std::collections::BTreeSet;

use super::fnval::{Callee, FnInfo, Given};
use super::{FnId, Lower, NodeId, Val};

impl Lower<'_> {
    /// Records a call of function parameter `p` of the body at summary index `d`.
    /// A call in a loop or in a closure inside that body can run more than once.
    pub(super) fn note_param_run(&mut self, (d, p): (usize, usize)) {
        let body = if d == 0 {
            Some(0)
        } else {
            self.frames.iter().position(|f| f.barrier == Some(d))
        };
        let nested =
            body.is_none_or(|b| self.frames.iter().skip(b + 1).any(|f| f.barrier.is_some()));
        let again = nested || !self.loops.is_empty();
        let e = self.param_runs.entry((d, p)).or_insert((0, false));
        e.0 += 1;
        e.1 |= again;
    }

    /// Function value `info` can run more than once at node `n`. A parameter in it
    /// is part of `repeats`. With `restart`, a task that it spawns into an outer
    /// scope starts again at a new node after `n`, where it conflicts with the
    /// first start (W0405).
    pub(super) fn note_repeat(&mut self, n: NodeId, info: &FnInfo, restart: bool) {
        if restart {
            self.repeated.insert(n);
        }
        if let Some(dp) = info.param {
            self.param_runs.entry(dp).or_insert((0, false)).1 = true;
        }
        let Some(s) = info.summary else {
            return;
        };
        let sum = self.closures[s].clone();
        for &p in sum.passthrough.iter().chain(&sum.params) {
            self.param_runs.entry((0, p)).or_insert((0, false)).1 = true;
        }
        if sum.spawns.is_empty() || !restart || self.cur.is_none() {
            return;
        }
        let span = self.facts.node(n).span;
        let again = self.emit(span, "spawn again", "the value can run again".into());
        self.restart_tasks(again, &sum.spawns);
    }

    /// A callee can call function value `info` more than once at node `n`, with
    /// the places `given`. A value that the body does not know can be a stored
    /// value: the node can run a stored value more than once.
    pub(super) fn repeat_unknown(&mut self, n: NodeId, info: &FnInfo, given: &[Given]) {
        let unknown = match info.summary {
            Some(s) => self.closures[s].unknown,
            None => info.item.is_none() && info.param.is_none(),
        };
        if unknown {
            self.reach(n, given, true);
        }
    }

    /// Function value `info` can run more than once at node `n`, and the body is
    /// lowered. A new node after `n` starts its tasks again (W0405). `apply_stored`
    /// calls it for a stored value at a node that can run the value more than once.
    pub(super) fn restart_after(&mut self, n: NodeId, info: &FnInfo) {
        let Some(s) = info.summary else {
            return;
        };
        let spawns = self.closures[s].spawns.clone();
        if spawns.is_empty() {
            return;
        }
        let again = self.insert_after(n, "spawn again", "the value can run again".into());
        self.restart_tasks(again, &spawns);
    }

    /// Node `again` starts the tasks `spawns` again: it mutates and reads what they do.
    fn restart_tasks(&mut self, again: NodeId, spawns: &BTreeSet<super::TaskId>) {
        for &t in spawns {
            let writes: Vec<_> = self
                .facts
                .task_writes
                .iter()
                .filter(|(u, _)| *u == t)
                .map(|&(_, m)| m)
                .collect();
            let reads: Vec<_> = self
                .facts
                .task_reads
                .iter()
                .filter(|(u, _)| *u == t)
                .map(|&(_, r)| r)
                .collect();
            for m in writes {
                self.facts.mutates_at.push((again, m));
            }
            for r in reads {
                self.facts.reads_at.push((again, r));
            }
        }
    }

    /// A callee gets function value `v` at node `n` and can call it. A closure that
    /// runs only once moves there, because the callee can call it. If the callee
    /// can call it more than once, the second call is a use after that move
    /// (W0502). A callee can also drop the closure without a call. So a linear
    /// closure goes out of scope at `n` (W0601). `exactly_once` says that the
    /// callee calls it once on every path: then it does not.
    pub(super) fn give_fn(&mut self, n: NodeId, v: &Val, repeats: bool, exactly_once: bool) {
        let (Some(var), Some(s)) = (v.var, self.fn_info(v).summary) else {
            return;
        };
        if self.cur.is_none() || !self.closure_is_once(s) {
            return;
        }
        if !exactly_once && self.closure_linear(s) {
            self.facts.scope_end.push((var, n));
        }
        self.move_var(var, n);
        if repeats {
            let span = self.facts.node(n).span;
            let again = self.emit(span, "call again", "the callee can call it again".into());
            self.move_var(var, again);
        }
    }

    /// Returns true if function item `f` calls its function argument exactly once
    /// on every path: `with_timeout` runs its block once, and an abort ends it.
    pub(super) fn item_runs_once(&self, f: FnId) -> bool {
        let def = &self.prog.fns[f];
        def.is_std && def.decl.body.is_none() && def.path == "with_timeout"
    }

    /// Returns the function parameters of the body at summary index `d` that it
    /// can call more than once, and forgets the calls of that body.
    pub(super) fn take_repeats(&mut self, d: usize) -> BTreeSet<usize> {
        let keys: Vec<(usize, usize)> = self
            .param_runs
            .range((d, 0)..=(d, usize::MAX))
            .map(|(&k, _)| k)
            .collect();
        let mut out = BTreeSet::new();
        for k in keys {
            if let Some((count, again)) = self.param_runs.remove(&k) {
                if again || count > 1 {
                    out.insert(k.1);
                }
            }
        }
        out
    }

    /// Returns the function parameters of the function that it can call more than
    /// once: a stored one too, and one that is live across a node that can resume
    /// more than once (`multi_live_params`).
    pub(super) fn repeats_sig(&self) -> BTreeSet<usize> {
        let mut out: BTreeSet<usize> = self
            .param_runs
            .range((0, 0)..=(0, usize::MAX))
            .filter(|(_, &(count, again))| again || count > 1)
            .map(|(&(_, p), _)| p)
            .collect();
        out.extend(self.sums[0].stores.iter().copied());
        out.extend(self.multi_live_params());
        out
    }

    /// Returns the function parameters of the function that are live across a node
    /// that can resume more than once. The code after the node runs again for each
    /// resume, so it can call the value again or give it back again. A caller must
    /// not give a `once` value there (W0502).
    fn multi_live_params(&self) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        let Some(id) = self.self_fn else {
            return out;
        };
        let f = &self.facts;
        let clause: BTreeSet<_> = f.clause_multi.iter().copied().collect();
        let body: BTreeSet<_> = f.body_multi.iter().copied().collect();
        let mut multi: BTreeSet<NodeId> = f.multi_at.iter().copied().collect();
        multi.extend(
            f.performs_at
                .iter()
                .filter(|(_, c)| clause.contains(c))
                .map(|&(n, _)| n),
        );
        multi.extend(
            f.resumes_at
                .iter()
                .filter(|(_, c)| clause.contains(c) || body.contains(c))
                .map(|&(n, _)| n),
        );
        if multi.is_empty() {
            return out;
        }
        let n = f.nodes.len();
        let mut pred = vec![Vec::new(); n];
        for &(a, b) in &f.cfg_edge {
            pred[b.index()].push(a);
        }
        for (i, p) in self.sigs[id].params.iter().enumerate() {
            if !matches!(p.ty, super::Ty::Fn(_)) {
                continue;
            }
            let Some(var) = self.locals.get(i).map(|l| l.var) else {
                continue;
            };
            let binds: BTreeSet<NodeId> = f
                .rebound_at
                .iter()
                .filter(|(v, _)| *v == var)
                .map(|&(_, m)| m)
                .collect();
            // `live_in`: a use of the value can follow with no new value first.
            let mut live = vec![false; n];
            let mut work: Vec<NodeId> = f
                .uses
                .iter()
                .filter(|(v, _)| *v == var)
                .map(|&(_, m)| m)
                .collect();
            while let Some(q) = work.pop() {
                if std::mem::replace(&mut live[q.index()], true) {
                    continue;
                }
                for &a in &pred[q.index()] {
                    if multi.contains(&a) {
                        out.insert(i);
                    }
                    if !binds.contains(&a) {
                        work.push(a);
                    }
                }
            }
        }
        out
    }

    /// Returns true if `callee` can call its function argument `i` more than once.
    pub(super) fn callee_repeats(&self, callee: &Callee, i: usize) -> bool {
        match callee {
            Callee::Item(f) => self.item_repeats(*f, i),
            Callee::Value(info) => match info.summary {
                Some(s) => {
                    let sum = &self.closures[s];
                    sum.unknown
                        || !sum.params.is_empty()
                        || sum.repeats.contains(&i)
                        || sum.stores.contains(&i)
                        || sum.items.iter().any(|&f| self.item_repeats(f, i))
                }
                None => info.item.is_none_or(|f| self.item_repeats(f, i)),
            },
        }
    }

    /// Returns true if function item `f` can call its function argument `i` more
    /// than once. A function with no body can, except `with_timeout`.
    fn item_repeats(&self, f: FnId, i: usize) -> bool {
        let def = &self.prog.fns[f];
        if def.decl.body.is_none() {
            return !(def.is_std && def.path == "with_timeout");
        }
        self.sigs[f].effects.repeats.contains(&i)
    }
}
