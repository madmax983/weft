//! Function values that can run more than once at one node.
//!
//! A callee can call its function parameter more than once, for example in a
//! loop. A task that a closure spawns into an outer scope then starts more than
//! once at the node that gives the closure, and the copies run at the same time.
//! The signature has a `repeats` part: the function parameters that the body can
//! call more than once.

use std::collections::BTreeSet;

use super::fnval::{Callee, FnInfo};
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
        for &t in &sum.spawns {
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
    /// once: a stored one too.
    pub(super) fn repeats_sig(&self) -> BTreeSet<usize> {
        let mut out: BTreeSet<usize> = self
            .param_runs
            .range((0, 0)..=(0, usize::MAX))
            .filter(|(_, &(count, again))| again || count > 1)
            .map(|(&(_, p), _)| p)
            .collect();
        out.extend(self.sums[0].stores.iter().copied());
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
