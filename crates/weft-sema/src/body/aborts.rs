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
                self.facts.cfg_edge.push((u, h.end));
                for &v in &to.vars {
                    self.facts.unwound_at.push((v, u));
                }
                for l in &to.scopes {
                    for &t in tasks.get(l).into_iter().flatten() {
                        self.facts.joined_at.push((t, u));
                    }
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
}
