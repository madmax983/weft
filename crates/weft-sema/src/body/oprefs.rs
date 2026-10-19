//! Operation results that hold references.
//!
//! A clause gives the result of its operation with `resume`. The clauses are
//! lowered after the handled body. So the result of an operation of a local
//! handler points into a root place of its own first. At the end of the body,
//! each fact about a place below that root holds for the same place below each
//! place that the `resume`s of the clause give (`op_refs`).

use super::{CapId, Lower, PlaceId, RootKind};

impl Lower<'_> {
    /// Returns the places that the result of an operation `op` (`None`: any
    /// operation) of the handler behind `cap` points into. A local handler gives
    /// the root place of the result. A handler of a caller can give a reference
    /// into any place of the parameters.
    pub(super) fn op_result_refs(&mut self, cap: Option<CapId>, op: Option<usize>) -> Vec<PlaceId> {
        let Some(c) = cap else {
            let bases = self.param_bases.clone();
            return bases.into_iter().map(|b| self.facts.wildcard(b)).collect();
        };
        if let Some(&r) = self.op_results.get(&(c, op)) {
            return vec![r];
        }
        let r = self.facts.add_root("operation result", RootKind::Local);
        self.op_results.insert((c, op), r);
        vec![r]
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
    /// onto the places that the `resume`s give: references into the result,
    /// mutations, reads, arguments, lends and tasks.
    pub(super) fn op_refs(&mut self) {
        let results: Vec<((CapId, Option<usize>), PlaceId)> =
            self.op_results.iter().map(|(&k, &r)| (k, r)).collect();
        for ((cap, op), r) in results {
            let mut targets: Vec<PlaceId> = Vec::new();
            for (&(c, o), ps) in &self.resumed_refs {
                if c == cap && (op.is_none() || o.is_none() || o == op) {
                    targets.extend(ps.iter().copied());
                }
            }
            targets.sort();
            targets.dedup();
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
            }
        }
    }
}
