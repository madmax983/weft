//! Abort paths: a clause that does not resume ends the handled body.
//!
//! A clause of a local handler can end with no `resume`. Then the handled body
//! ends at the node that runs the clause, and control goes to the end of the
//! `handle`. On the way the unwinder finishes the values of the body, and it
//! cancels the tasks of the scopes that the body opened and waits for them. The
//! paths come after the whole body, because a stored function value can run a
//! clause too (`apply_stored`).

use std::collections::{BTreeMap, BTreeSet};

use super::{CapId, Lower, NodeId, TaskId};

impl Lower<'_> {
    /// Adds the abort paths of the local handlers. Then it checks the locals
    /// outside each handled body (W0313, `check_local_keeps`), on the normal path
    /// and on each abort path.
    ///
    /// A node gets a path for each handler that it can run a clause of
    /// (`Lower::cap_calls`), if a clause of the handler can end with no `resume`
    /// and the node is in the part of the graph of the handled body
    /// (`note_abort_ctx`).
    pub(super) fn finish_aborts(&mut self) {
        let handled = std::mem::take(&mut self.handled);
        // The abort nodes that leave the body of each handler, with the number of
        // locals when the body of the target starts. A local below that number
        // lives on after the abort node.
        let mut exits: BTreeMap<CapId, Vec<(NodeId, usize)>> = BTreeMap::new();
        let mut tasks: BTreeMap<usize, Vec<TaskId>> = BTreeMap::new();
        for (&t, &l) in &self.task_scope {
            tasks.entry(l).or_default().push(t);
        }
        for h in handled.iter().filter(|h| h.aborts) {
            let sources: BTreeSet<NodeId> = self
                .cap_calls
                .iter()
                .filter(|(_, c)| *c == h.cap)
                .map(|(n, _)| *n)
                .collect();
            for n in sources {
                let Some(to) = self
                    .abort_ctx
                    .get(&n)
                    .and_then(|ctx| ctx.iter().find(|a| a.cap == h.cap))
                    .cloned()
                else {
                    continue;
                };
                let at = self.facts.node(n).span;
                let u =
                    self.facts
                        .add_node(at, "abort", String::from("the clause does not resume"));
                self.facts.cfg_edge.push((n, u));
                for &v in &to.vars {
                    self.facts.unwound_at.push((v, u));
                }
                let mut ended = Vec::new();
                for l in &to.scopes {
                    for &t in tasks.get(l).into_iter().flatten() {
                        self.facts.joined_at.push((t, u));
                        ended.push(t);
                    }
                }
                // The tasks that the abort ends can have changed what they write
                // (`finish_task_ends`).
                if ended.is_empty() {
                    self.facts.cfg_edge.push((u, h.end));
                } else {
                    let e = self.facts.add_node(at, weft_facts::TASK_END, String::new());
                    self.facts.cfg_edge.push((u, e));
                    self.facts.cfg_edge.push((e, h.end));
                    self.task_ends.extend(ended.into_iter().map(|t| (t, e)));
                }
                // The path leaves the bodies of the handlers inside too, and the
                // clauses that wait for these bodies.
                for c in &to.inner {
                    if let Some(x) = handled.iter().find(|x| x.cap == *c) {
                        for &v in &x.clause_vars {
                            self.facts.unwound_at.push((v, u));
                        }
                    }
                    exits.entry(*c).or_default().push((u, h.locals));
                }
            }
        }
        for h in &handled {
            if let Some((effect, span)) = &h.keeps {
                let out = exits.get(&h.cap).map_or(&[][..], Vec::as_slice);
                self.check_local_keeps(h, effect, out, *span);
            }
        }
        self.handled = handled;
    }

    /// Adds `spared_at(V, P)` for each operation `P` of a local handler. The
    /// operation suspends the handled body only: an abort unwinds its values,
    /// and a `multi` resume copies them. A value outside the body is spared if
    /// nothing else at `P` suspends, and if no clause of the handler suspends
    /// the code outside the body. A clause does that when it performs through
    /// a handler outside its `handle`, or calls code that can (rule 1 of
    /// `proofs/effects`: the `handle` passes up the environment to the clauses).
    /// The resumes of a clause do not count: the resumed body suspends at its
    /// own nodes, where the values outside the body are live.
    pub(super) fn finish_spared(&mut self) {
        if self.local_performs.is_empty() {
            return;
        }
        let mut by_node: BTreeMap<NodeId, Vec<CapId>> = BTreeMap::new();
        for (n, c, _) in &self.local_performs {
            by_node.entry(*n).or_default().push(*c);
        }
        // The handlers whose clauses do not suspend the code outside the body.
        let contained: BTreeSet<CapId> = self
            .handled
            .iter()
            .filter(|h| {
                h.clause_nodes.iter().all(|&(a, b)| {
                    self.out_suspends.range(a..b).next().is_none()
                        && by_node
                            .range(a..b)
                            .flat_map(|(_, cs)| cs)
                            .all(|c| h.inner_caps.contains(c))
                })
            })
            .map(|h| h.cap)
            .collect();
        let mut spared = Vec::new();
        for (n, cap, vars) in &self.local_performs {
            if !self.out_suspends.contains(n) && contained.contains(cap) {
                spared.extend(vars.iter().map(|&v| (v, *n)));
            }
        }
        self.facts.spared_at.extend(spared);
    }
}
