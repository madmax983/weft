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
        // A call of a parameter of the function in a closure counts where the
        // closure runs (`repeats_sig`). Each closure around the call keeps it.
        let inner = self.frames.iter().rposition(|f| f.barrier.is_some());
        if d == 0 && nested && inner.is_some_and(|fi| self.is_closure_frame(fi)) {
            let loops = !self.loops.is_empty();
            for fi in 1..self.frames.len() {
                let Some(si) = self.frames[fi].barrier else {
                    continue;
                };
                if self.is_closure_frame(fi) {
                    let direct = Some(fi) == inner;
                    self.sums[si]
                        .param_calls
                        .push((p, !direct || loops, direct));
                }
            }
            return;
        }
        let again = nested || !self.loops.is_empty();
        let e = self.param_runs.entry((d, p)).or_insert((0, false));
        e.0 += 1;
        e.1 |= again;
    }

    /// Returns true if frame `fi` starts the body of a closure, not of a clause.
    fn is_closure_frame(&self, fi: usize) -> bool {
        self.jumps
            .iter()
            .any(|j| matches!(j, super::Jump::Closure { frame, .. } if *frame == fi))
    }

    /// A callee can run function value `v` again at node `n`, right after the run
    /// at `n`: a new node after `n` uses the value again. A change of the first run
    /// invalidates what the value captures for the second run (W0301). Returns the
    /// new node.
    pub(super) fn run_again(&mut self, n: NodeId, v: &Val) -> NodeId {
        if self.cur.is_none() {
            return n;
        }
        let span = self.facts.node(n).span;
        let again = self.emit(span, "call again", "the callee can call it again".into());
        if let Some(var) = v.var {
            self.facts.uses.push((var, again));
        }
        again
    }

    /// Returns true if closure `id` can run in the body: a node of the body, of a
    /// clause or of a closure that can run applies it, or the body stores it.
    fn closure_runs(&self, id: usize, seen: &mut Vec<usize>) -> bool {
        if seen.contains(&id) {
            return false;
        }
        seen.push(id);
        let stored = self.escaped.iter().any(|st| {
            st.info
                .summary
                .is_some_and(|s| self.closures[s].members.contains(&id))
        });
        if stored {
            return true;
        }
        for a in &self.applied {
            if !self.closures[a.summary].members.contains(&id) {
                continue;
            }
            match a.scope {
                super::fnval::Scope::Closure(y) => {
                    if self.closure_runs(y, seen) {
                        return true;
                    }
                }
                _ => return true,
            }
        }
        false
    }

    /// Returns true if closure `id` can run more than once in one run of the
    /// body. That is so if the body stores it or gives it to an operation, or
    /// runs it at two nodes. It is so for a run in a loop or at a node that can
    /// run it again. It is so for a run in a clause or in a closure that can run
    /// more than once. `path` has the closures on the way.
    fn closure_runs_again(&self, id: usize, path: &mut Vec<usize>) -> bool {
        if path.contains(&id) {
            return true;
        }
        let has = |info: &FnInfo| {
            info.summary
                .is_some_and(|s| self.closures[s].members.contains(&id))
        };
        if self.escaped.iter().any(|st| has(&st.info))
            || self.op_fn_args.iter().any(|o| has(&o.info))
        {
            return true;
        }
        path.push(id);
        let mut nodes = BTreeSet::new();
        let mut again = false;
        for a in &self.applied {
            if !self.closures[a.summary].members.contains(&id) {
                continue;
            }
            nodes.insert(a.node);
            again |= a.in_loop || self.repeated.contains(&a.node);
            again |= match a.scope {
                super::fnval::Scope::Closure(y) => self.closure_runs_again(y, path),
                super::fnval::Scope::Function => false,
                super::fnval::Scope::Open(_) | super::fnval::Scope::Clause => true,
            };
            if again {
                break;
            }
        }
        path.pop();
        again || nodes.len() > 1
    }

    /// Returns true if closure `id` runs only where the function returns it: the
    /// function returns it, or runs it only in a closure that it returns.
    fn only_returned(&self, id: usize) -> bool {
        if self.closure_runs(id, &mut Vec::new()) {
            return false;
        }
        let returned = self.rets.iter().any(|(info, _)| {
            info.summary
                .is_some_and(|s| self.closures[s].members.contains(&id))
        });
        returned
            || self
                .applied
                .iter()
                .any(|a| self.closures[a.summary].members.contains(&id))
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
        self.restart_tasks(again, &sum.spawns.to_set());
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
        self.restart_tasks(again, &spawns.to_set());
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
    /// can call it again at node `again` (`run_again`), the second call is a use
    /// after that move (W0502). A callee can also drop the closure without a call. So a linear
    /// closure goes out of scope at `n` (W0601). `exactly_once` says that the
    /// callee calls it once on every path: then it does not.
    pub(super) fn give_fn(
        &mut self,
        n: NodeId,
        v: &Val,
        again: Option<NodeId>,
        exactly_once: bool,
    ) {
        let (Some(var), Some(s)) = (v.var, self.fn_info(v).summary) else {
            return;
        };
        if self.cur.is_none() || !self.closure_once_now(s) {
            return;
        }
        if !exactly_once && self.closure_linear(s) {
            self.facts.scope_end.push((var, n));
        }
        self.move_var(var, n);
        if let Some(a) = again.filter(|&a| a != n) {
            self.move_var(var, a);
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

    /// Returns true if the body can run a stored function value more than once
    /// (`EffectSig::reach_repeats`). That is so if a node can run it more than
    /// once, or if a node is in a loop. It is so for a node in a closure that can
    /// run more than once, and if a node can come after another one.
    pub(super) fn reach_repeats(&self) -> bool {
        if self.reach_runs.1 {
            return true;
        }
        let nested = self.reaches.iter().any(|r| match r.scope {
            super::fnval::Scope::Function => false,
            super::fnval::Scope::Closure(id) => self.closure_runs_again(id, &mut Vec::new()),
            super::fnval::Scope::Open(_) | super::fnval::Scope::Clause => true,
        });
        nested || (self.reach_runs.0 > 1 && self.reaches_follow())
    }

    /// Returns true if a call of function value `info` runs a function value
    /// that it holds more than once (`Summary::repeat_runs`).
    pub(super) fn runs_held_again(&self, info: &FnInfo) -> bool {
        info.summary.is_some_and(|s| self.closures[s].repeat_runs)
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
        // A call in a closure counts if it can run more than once in one run of
        // the closure. It counts if the closure can run more than once too. A
        // call in an inner closure counts there. If the function only returns
        // the closure, the `ret` part has the call.
        for (id, c) in self.closures.iter().enumerate() {
            if c.param_calls.is_empty() || !c.members.contains(&id) || self.only_returned(id) {
                continue;
            }
            let direct: Vec<(usize, bool)> = c
                .param_calls
                .iter()
                .filter(|e| e.2)
                .map(|&(p, again, _)| (p, again))
                .collect();
            let runs_again = self.closure_runs_again(id, &mut Vec::new());
            for &(p, again) in &direct {
                if runs_again || again || direct.iter().filter(|(q, _)| *q == p).count() > 1 {
                    out.insert(p);
                }
            }
        }
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
