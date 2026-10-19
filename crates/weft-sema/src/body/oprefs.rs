//! Operation results that hold references.
//!
//! A clause gives the result of its operation with `resume`. The clauses are
//! lowered after the handled body. So the result of an operation of a local
//! handler points into a root place of its own first. At the end of the body,
//! each fact about a place below that root moves (`op_refs`). It then holds for
//! the same place below each place that the `resume`s of the clause give.
//!
//! A handler of a caller can resume with a reference into a place of the
//! caller, for example a local of the caller. The parameters do not reach that
//! place. It is below a root of its own (`env_ref`). Code of a caller can change
//! it (`finish_op_env`). That code is a clause of a handler of a caller, or a
//! function value that the body does not follow.

use super::{CapId, Lower, PlaceId, RootKind, Span};

impl Lower<'_> {
    /// Returns the places that the result of an operation `op` (`None`: any
    /// operation) of the handler behind `cap` points into. A local handler gives
    /// the root place of the result. A handler of a caller can give a reference
    /// into any place of the parameters, or into a place of the caller
    /// (`env_ref`).
    pub(super) fn op_result_refs(&mut self, cap: Option<CapId>, op: Option<usize>) -> Vec<PlaceId> {
        let Some(c) = cap else {
            let bases = self.param_bases.clone();
            let mut out: Vec<PlaceId> = bases.into_iter().map(|b| self.facts.wildcard(b)).collect();
            out.push(self.env_ref());
            return out;
        };
        if let Some(&r) = self.op_results.get(&(c, op)) {
            return vec![r];
        }
        let r = self.facts.add_root("operation result", RootKind::Local);
        self.op_results.insert((c, op), r);
        vec![r]
    }

    /// Returns a reference to any place of a caller that a handler of a caller
    /// can give. It is a wildcard place below a root of its own. The root has the
    /// kind `Arg`: code of a caller changes it, so a change needs no declaration
    /// here.
    pub(super) fn env_ref(&mut self) -> PlaceId {
        let r = if let Some(r) = self.env_root {
            r
        } else {
            let r = self.facts.add_root("a place of a caller", RootKind::Arg);
            self.env_root = Some(r);
            r
        };
        self.facts.wildcard(r)
    }

    /// Code of a caller can change the places of `env_ref`. It runs at a node that
    /// performs an operation of a handler of a caller. It also runs at a call of a
    /// function parameter or of a function value that the body does not know. Each
    /// such node lends the root, so a reference into it is not valid after the
    /// node.
    pub(super) fn finish_op_env(&mut self) {
        let Some(r) = self.env_root else {
            return;
        };
        let mut nodes: Vec<_> = self.facts.escapes_at.iter().map(|&(n, _)| n).collect();
        nodes.extend(self.caller_runs.iter().copied());
        nodes.sort();
        nodes.dedup();
        for n in nodes {
            self.facts.lends_mut.push((n, r));
        }
    }

    /// Returns the places that the result of operation `op` of the handler behind
    /// `cap` stands for: the places that the `resume`s give.
    fn op_targets(&self, cap: CapId, op: Option<usize>) -> Vec<PlaceId> {
        let mut targets: Vec<PlaceId> = Vec::new();
        for (&(c, o), ps) in &self.resumed_refs {
            if c == cap && (op.is_none() || o.is_none() || o == op) {
                targets.extend(ps.iter().copied());
            }
        }
        targets.sort();
        targets.dedup();
        targets
    }

    /// Returns `refs` with each place below the root of an operation result moved
    /// onto the places that the `resume`s give. `op_refs` does the same for the
    /// facts.
    pub(super) fn resolve_op_refs(&mut self, refs: &[PlaceId]) -> Vec<PlaceId> {
        let results: Vec<((CapId, Option<usize>), PlaceId)> =
            self.op_results.iter().map(|(&k, &r)| (k, r)).collect();
        let mut out = Vec::new();
        for &p in refs {
            let root = self.facts.place(p).root;
            let Some(&((cap, op), r)) = results
                .iter()
                .find(|(_, r)| self.facts.place(*r).root == root)
            else {
                out.push(p);
                continue;
            };
            for t in self.op_targets(cap, op) {
                out.push(self.rebase(p, r, t));
            }
        }
        out.sort();
        out.dedup();
        out
    }

    /// Checks the values that the function returns (`check_returned_refs`), with
    /// the places of the operation results that `op_refs` knows.
    pub(super) fn check_returns(&mut self) {
        for (refs, closure, span) in std::mem::take(&mut self.returned) {
            let refs = self.resolve_op_refs(&refs);
            self.check_returned_refs(&refs, closure, span);
            self.returned_places.extend(refs);
        }
    }

    /// Reports W0204 for a reference into a local of the function that the body
    /// puts behind a reference parameter. The caller keeps the reference after
    /// the return, but the local goes out of scope there.
    pub(super) fn check_stored_behind(&mut self) {
        let Some(id) = self.self_fn else {
            self.stored_behind.clear();
            return;
        };
        let fname = self.prog.fns[id].name.clone();
        let mut seen = Vec::new();
        for (behind, refs, span) in std::mem::take(&mut self.stored_behind) {
            let refs = self.resolve_op_refs(&refs);
            let (named, _) = self.split_deps(&refs);
            for r in named {
                let root = self.facts.place(r).root;
                // A reference that the caller gives goes into the `rc` object too:
                // the caller checks it (`group_stores`).
                if let super::Behind::Group(a) = behind {
                    let param = match self.param_of_root.get(&root) {
                        Some(&(0, i)) => Some(i),
                        _ => self.held_of.get(&root).copied(),
                    };
                    if let Some(i) = param {
                        self.group_stores.insert((i, a));
                    }
                }
                let info = &self.facts.roots[root.index()];
                if info.kind != RootKind::Local || seen.contains(&(behind, root)) {
                    continue;
                }
                // An operation result with no `resume` that gives a place.
                if self
                    .op_results
                    .values()
                    .any(|&x| self.facts.place(x).root == root)
                {
                    continue;
                }
                seen.push((behind, root));
                let name = info.name.clone();
                let by_value = (0..self.sigs[id].params.len()).any(|i| {
                    self.locals
                        .get(i)
                        .and_then(|l| l.root)
                        .map(|p| self.facts.place(p).root)
                        == Some(root)
                });
                let what = if name == "temporary" {
                    "a temporary value".to_string()
                } else if by_value {
                    format!("the by-value parameter `{name}`")
                } else {
                    format!("the local `{name}`")
                };
                let shown = self.facts.place(r).display.clone();
                let into = match behind {
                    super::Behind::Param(i) => {
                        let param = self.sigs[id]
                            .params
                            .get(i)
                            .map_or_else(String::new, |p| p.name.clone());
                        format!("behind the parameter `{param}`")
                    }
                    super::Behind::Group(a) => {
                        format!("into an `rc` object of type `{}`", self.prog.adts[a].name)
                    }
                };
                self.err(
                    "W0204",
                    format!("`{fname}` puts a reference into `{shown}` {into}: {what} goes out of scope at the return"),
                    span,
                );
            }
        }
    }

    /// Records that the references `refs` go behind place `p`. A place behind a
    /// reference parameter of the function keeps them for the caller
    /// (`check_stored_behind`).
    pub(super) fn note_stored_behind(&mut self, p: PlaceId, refs: &[PlaceId], span: Span) {
        let root = self.facts.place(p).root;
        let rp = self.root_place(p);
        let behind = match self.param_of_root.get(&root) {
            Some(&(0, i)) => Some(super::Behind::Param(i)),
            _ => self
                .held_of
                .get(&root)
                .map(|&i| super::Behind::Param(i))
                .or_else(|| {
                    self.groups
                        .iter()
                        .find(|(_, &g)| g == rp)
                        .map(|(&a, _)| super::Behind::Group(a))
                }),
        };
        if let (Some(b), false) = (behind, refs.is_empty()) {
            self.stored_behind.push((b, refs.to_vec(), span));
        }
    }

    /// Records the places that the `resume`s of the clause of operation `op` of
    /// the handler behind `cap` give. A place below a reference parameter of the
    /// clause is that place below each place that a node gives to the operation.
    /// Returns the places that are inside a local of the clause.
    pub(super) fn note_resumed_refs(
        &mut self,
        cap: CapId,
        op: Option<usize>,
        param_roots: &std::collections::BTreeMap<PlaceId, usize>,
        own: &std::collections::BTreeSet<weft_facts::RootId>,
    ) -> Vec<PlaceId> {
        let pending: Vec<Vec<PlaceId>> = self
            .resume_refs_pending
            .iter()
            .filter(|(c, _)| *c == cap)
            .map(|(_, rs)| rs.clone())
            .collect();
        self.resume_refs_pending.retain(|(c, _)| *c != cap);
        let mut out = Vec::new();
        let mut local = Vec::new();
        for refs in pending {
            out.extend(self.clause_refs_onto_args(&refs, param_roots, cap, op));
            for p in refs {
                if param_roots.contains_key(&self.root_place(p)) {
                    continue;
                }
                if own.contains(&self.facts.place(p).root) {
                    local.push(p);
                }
                out.push(p);
            }
        }
        out.sort();
        out.dedup();
        self.resumed_refs.entry((cap, op)).or_default().extend(out);
        local
    }

    /// Moves each fact about a place below the root place of an operation result
    /// onto the places that the `resume`s give. The facts are the references into
    /// the result, mutations, reads, arguments, lends and tasks.
    pub(super) fn op_refs(&mut self) {
        let results: Vec<((CapId, Option<usize>), PlaceId)> =
            self.op_results.iter().map(|(&k, &r)| (k, r)).collect();
        for ((cap, op), r) in results {
            let targets = self.op_targets(cap, op);
            if targets.is_empty() {
                continue;
            }
            let root = self.facts.place(r).root;
            let under = |me: &Self, p: PlaceId| me.facts.place(p).root == root;
            let pts: Vec<_> = self
                .facts
                .points_into
                .iter()
                .copied()
                .filter(|&(_, p)| under(self, p))
                .collect();
            let muts: Vec<_> = self
                .facts
                .mutates_at
                .iter()
                .copied()
                .filter(|&(_, p)| under(self, p))
                .collect();
            let reads: Vec<_> = self
                .facts
                .reads_at
                .iter()
                .copied()
                .filter(|&(_, p)| under(self, p))
                .collect();
            let cmuts: Vec<_> = self
                .facts
                .call_mut
                .iter()
                .copied()
                .filter(|&(_, p, _)| under(self, p))
                .collect();
            let cargs: Vec<_> = self
                .facts
                .call_arg
                .iter()
                .copied()
                .filter(|&(_, p, _)| under(self, p))
                .collect();
            let lends: Vec<_> = self
                .facts
                .lends_mut
                .iter()
                .copied()
                .filter(|&(_, p)| under(self, p))
                .collect();
            let treads: Vec<_> = self
                .facts
                .task_reads
                .iter()
                .copied()
                .filter(|&(_, p)| under(self, p))
                .collect();
            let twrites: Vec<_> = self
                .facts
                .task_writes
                .iter()
                .copied()
                .filter(|&(_, p)| under(self, p))
                .collect();
            let sum_muts: Vec<PlaceId> = self.sums[0]
                .muts
                .iter()
                .copied()
                .filter(|&p| under(self, p))
                .collect();
            let sum_lends: Vec<PlaceId> = self.sums[0]
                .lends
                .iter()
                .copied()
                .filter(|&p| under(self, p))
                .collect();
            let sum_lent: Vec<(usize, Option<usize>, PlaceId)> = self.sums[0]
                .lent
                .iter()
                .copied()
                .filter(|&(_, _, p)| under(self, p))
                .collect();
            for t in targets {
                for &(v, p) in &pts {
                    let q = self.rebase(p, r, t);
                    self.facts.points_into.push((v, q));
                }
                for &(n, p) in &muts {
                    let q = self.rebase(p, r, t);
                    self.facts.mutates_at.push((n, q));
                    self.sums[0].muts.insert(q);
                }
                for &(n, p) in &reads {
                    let q = self.rebase(p, r, t);
                    self.facts.reads_at.push((n, q));
                }
                for &(n, p, i) in &cmuts {
                    let q = self.rebase(p, r, t);
                    self.facts.call_mut.push((n, q, i));
                }
                for &(n, p, i) in &cargs {
                    let q = self.rebase(p, r, t);
                    self.facts.call_arg.push((n, q, i));
                }
                for &(n, p) in &lends {
                    let q = self.rebase(p, r, t);
                    self.facts.lends_mut.push((n, q));
                }
                for &(k, p) in &treads {
                    let q = self.rebase(p, r, t);
                    self.facts.task_reads.push((k, q));
                }
                for &(k, p) in &twrites {
                    let q = self.rebase(p, r, t);
                    self.facts.task_writes.push((k, q));
                }
                for &p in &sum_muts {
                    let q = self.rebase(p, r, t);
                    self.sums[0].muts.insert(q);
                }
                for &p in &sum_lends {
                    let q = self.rebase(p, r, t);
                    self.sums[0].lends.insert(q);
                }
                // A function parameter gets the places too (the `lent` part).
                for &(k, pos, p) in &sum_lent {
                    let q = self.rebase(p, r, t);
                    if !self.sums[0].lent.contains(&(k, pos, q)) {
                        self.sums[0].lent.push((k, pos, q));
                    }
                }
            }
        }
    }
}
