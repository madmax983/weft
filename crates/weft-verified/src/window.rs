//! The window of a late slot (plan stage R0z Z9c-B, proof P2).
//!
//! A late slot of a run node has four task nodes after `Main` and before
//! `Ret`: the start `s`, the second start `d`, the node `x` of the code that
//! runs with the task, and the end `e`. The task starts at `s` (`gen`) and
//! ends at `e` (`kill`). The rule `active` of the spec is the least fixpoint
//! of [`crate::dataflow`] for these sets, and
//! [`crate::dataflow::propagate`] computes it exactly.
//!
//! This module proves two properties of that fixpoint:
//!
//! * soundness (`lemma_slot_window_sound`): if the graph has the edges
//!   `s -> d`, `d -> x` and `x -> e`, then `d`, `x` and `e` are in the
//!   window. So the code that runs with the task (at `x`) runs while the
//!   task is active. This holds for each `gen` set that has `s`, also with
//!   the starts on the edges into `Main` (`local_code`).
//! * precision (`lemma_slot_window_exact`): if `s` is the only `gen` node,
//!   `e` is a `kill` node, and the successors of `s`, `d` and `x` are only
//!   `d`, `x` and `e`, then the window is in `{d, x, e}`. No node of the
//!   caller outside the call is in it.
//!
//! With `local_code` the `gen` set also has the predecessors of `Main`
//! (change C8 of the design review). Then the window also has `Main`, the
//! other successors of these predecessors and the abort paths of `Main`,
//! which are not killed. `lemma_slot_window_local` states that case: the
//! window is in the set of these nodes and of `s`, `d`, `x` and `e`, if
//! that set is closed (the premises). Its premise on `Main` needs the late
//! slot directly after `Main`; the refusals R-VARG and R-VCLAUSE of the fact
//! generator keep that true (no argument slot nodes and no wait handler at
//! the call). `lemma_within_closed` is the step
//! of both precision lemmas: the least fixpoint is inside each closed set.
//!
//! The proofs do not show that the fact generator builds such a graph
//! (`NodeTable::late_slot_nodes`). The tests and the oracles check that.
//!
//! `proofs/link` includes this file. `proofs/verify-all.sh` verifies it.

use vstd::prelude::*;

verus! {

/// The four nodes of a slot are nodes of the graph, and the graph has the
/// edges `s -> d`, `d -> x` and `x -> e`.
pub open spec fn spec_slot(succ: Seq<Seq<usize>>, s: int, d: int, x: int, e: int) -> bool {
    &&& 0 <= s < succ.len()
    &&& 0 <= d < succ.len()
    &&& 0 <= x < succ.len()
    &&& 0 <= e < succ.len()
    &&& crate::dataflow::spec_edge(succ, s, d)
    &&& crate::dataflow::spec_edge(succ, d, x)
    &&& crate::dataflow::spec_edge(succ, x, e)
}

/// The successors of node `p` are only `d`, `x` and `e`.
pub open spec fn spec_succs_in_slot(succ: Seq<Seq<usize>>, p: int, d: int, x: int, e: int) -> bool {
    forall|j: int|
        0 <= j < succ[p].len() ==> ((#[trigger] succ[p][j]) as int == d || succ[p][j] as int == x
            || succ[p][j] as int == e)
}

/// The least fixpoint is inside each closed set.
pub proof fn lemma_within_closed(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    a: Set<int>,
    i: int,
)
    requires
        crate::dataflow::spec_closed(succ, gen, kill, a),
        crate::dataflow::spec_in_lfp(succ, gen, kill, i),
    ensures
        a.contains(i),
{
}

/// Soundness: a task that starts at `s` is active at `d`, `x` and `e`, if
/// it does not end at `d` or `x`.
pub proof fn lemma_slot_window_sound(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    s: int,
    d: int,
    x: int,
    e: int,
)
    requires
        crate::dataflow::spec_well_formed(succ, gen, kill),
        spec_slot(succ, s, d, x, e),
        gen[s],
        !kill[d],
        !kill[x],
    ensures
        crate::dataflow::spec_in_lfp(succ, gen, kill, d),
        crate::dataflow::spec_in_lfp(succ, gen, kill, x),
        crate::dataflow::spec_in_lfp(succ, gen, kill, e),
{
    let j1 = choose|j: int| 0 <= j < succ[s].len() && succ[s][j] as int == d;
    crate::dataflow::lemma_step_sound(succ, gen, kill, s, j1);
    let j2 = choose|j: int| 0 <= j < succ[d].len() && succ[d][j] as int == x;
    crate::dataflow::lemma_step_sound(succ, gen, kill, d, j2);
    let j3 = choose|j: int| 0 <= j < succ[x].len() && succ[x][j] as int == e;
    crate::dataflow::lemma_step_sound(succ, gen, kill, x, j3);
}

/// Precision: with `s` the only `gen` node (the only start node of the
/// task), `e` a `kill` node, and no successor of `s`, `d` or `x` outside
/// the slot, the window is in `{d, x, e}`. A task with a second start at `d`
/// (`twice`) or a first start at `d` (`seq`) has another `gen` set: the
/// lemma does not state that case.
pub proof fn lemma_slot_window_exact(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    s: int,
    d: int,
    x: int,
    e: int,
    i: int,
)
    requires
        crate::dataflow::spec_well_formed(succ, gen, kill),
        spec_slot(succ, s, d, x, e),
        forall|p: int| 0 <= p < gen.len() && #[trigger] gen[p] ==> p == s,
        kill[e],
        spec_succs_in_slot(succ, s, d, x, e),
        spec_succs_in_slot(succ, d, d, x, e),
        spec_succs_in_slot(succ, x, d, x, e),
        crate::dataflow::spec_in_lfp(succ, gen, kill, i),
    ensures
        i == d || i == x || i == e,
{
    let a = Set::new(|q: int| q == d || q == x || q == e);
    assert forall|p: int, q: int|
        0 <= p < gen.len() && gen[p] && #[trigger] crate::dataflow::spec_edge(succ, p, q)
            implies a.contains(q) by {
        assert(p == s);
        let j = choose|j: int| 0 <= j < succ[p].len() && succ[p][j] as int == q;
        assert(succ[s][j] as int == q);
    }
    assert forall|p: int, q: int|
        0 <= p < kill.len() && a.contains(p) && !kill[p]
            && #[trigger] crate::dataflow::spec_edge(succ, p, q) implies a.contains(q) by {
        let j = choose|j: int| 0 <= j < succ[p].len() && succ[p][j] as int == q;
        if p == d {
            assert(succ[d][j] as int == q);
        } else {
            assert(p == x);
            assert(succ[x][j] as int == q);
        }
    }
    assert(crate::dataflow::spec_closed(succ, gen, kill, a));
    lemma_within_closed(succ, gen, kill, a, i);
}

/// Precision with `local_code` (change C8 of the design review): the `gen`
/// nodes are `s` and the predecessors `pre` of `Main` (`m`). Each node of
/// `pre` (also a `kill` node, as a `gen` node starts the task there) has
/// successors only in `pre`, `m` or `out`; `m` has successors only `s` and
/// nodes of `out` (its abort paths); each node of `out` that is not a `kill`
/// node has successors only in `out`; and no successor of `s`, `d` or `x`
/// is outside the slot. Then the window is in `pre`, `out`, and `m`, `s`,
/// `d`, `x`, `e`: no node after `Ret` of the call is in it unless the
/// premises put it in `out`. The premise on `m` holds only if the late slot
/// comes directly after `Main` (no argument slot and no wait handler before
/// it): R-VARG and R-VCLAUSE of `transfer::capture_slots` keep it so (a
/// call with a late slot has no other task node).
pub proof fn lemma_slot_window_local(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    m: int,
    s: int,
    d: int,
    x: int,
    e: int,
    pre: Set<int>,
    out: Set<int>,
    i: int,
)
    requires
        crate::dataflow::spec_well_formed(succ, gen, kill),
        spec_slot(succ, s, d, x, e),
        forall|p: int| 0 <= p < gen.len() && #[trigger] gen[p] ==> p == s || pre.contains(p),
        kill[e],
        forall|p: int, q: int|
            pre.contains(p) && #[trigger] crate::dataflow::spec_edge(succ, p, q)
                ==> pre.contains(q) || q == m || out.contains(q),
        forall|q: int|
            #[trigger] crate::dataflow::spec_edge(succ, m, q) ==> q == s || out.contains(q),
        forall|p: int, q: int|
            out.contains(p) && !kill[p] && #[trigger] crate::dataflow::spec_edge(succ, p, q)
                ==> out.contains(q),
        spec_succs_in_slot(succ, s, d, x, e),
        spec_succs_in_slot(succ, d, d, x, e),
        spec_succs_in_slot(succ, x, d, x, e),
        crate::dataflow::spec_in_lfp(succ, gen, kill, i),
    ensures
        pre.contains(i) || out.contains(i) || i == m || i == s || i == d || i == x || i == e,
{
    let a = Set::new(
        |q: int|
            pre.contains(q) || out.contains(q) || q == m || q == s || q == d || q == x || q == e,
    );
    assert forall|p: int, q: int|
        0 <= p < gen.len() && gen[p] && #[trigger] crate::dataflow::spec_edge(succ, p, q)
            implies a.contains(q) by {
        if p == s {
            let j = choose|j: int| 0 <= j < succ[p].len() && succ[p][j] as int == q;
            assert(succ[s][j] as int == q);
        } else {
            assert(pre.contains(p));
        }
    }
    assert forall|p: int, q: int|
        0 <= p < kill.len() && a.contains(p) && !kill[p]
            && #[trigger] crate::dataflow::spec_edge(succ, p, q) implies a.contains(q) by {
        if p == s || p == d || p == x {
            let j = choose|j: int| 0 <= j < succ[p].len() && succ[p][j] as int == q;
            if p == s {
                assert(succ[s][j] as int == q);
            } else if p == d {
                assert(succ[d][j] as int == q);
            } else {
                assert(succ[x][j] as int == q);
            }
        } else if p == m {
            assert(crate::dataflow::spec_edge(succ, m, q));
        } else if pre.contains(p) {
            assert(crate::dataflow::spec_edge(succ, p, q));
        } else {
            assert(out.contains(p));
        }
    }
    assert(crate::dataflow::spec_closed(succ, gen, kill, a));
    lemma_within_closed(succ, gen, kill, a, i);
}

} // verus!
#[cfg(test)]
mod tests {
    use crate::dataflow::propagate;

    /// The graph of a call with one late slot: `Main` (0), the slot nodes
    /// `s` (1), `d` (2), `x` (3), `e` (4), `Ret` (5), a node after the call
    /// (6), and an abort node of `Main` (7).
    fn call() -> Vec<Vec<usize>> {
        vec![
            vec![1, 7],
            vec![2],
            vec![3],
            vec![4],
            vec![5],
            vec![6],
            vec![],
            vec![],
        ]
    }

    #[test]
    fn the_window_of_a_slot_is_its_nodes() {
        let succ = call();
        let mut gen = vec![false; 8];
        gen[1] = true;
        let mut kill = vec![false; 8];
        kill[4] = true;
        let out = propagate(&succ, &gen, &kill);
        assert_eq!(
            out,
            vec![false, false, true, true, true, false, false, false]
        );
    }

    #[test]
    fn with_local_code_the_window_has_main_and_its_aborts() {
        let mut succ = call();
        succ.insert(0, vec![0]);
        for v in &mut succ {
            for q in v.iter_mut() {
                *q += 1;
            }
        }
        // Node 0 is the predecessor of `Main` (now node 1).
        let mut gen = vec![false; 9];
        gen[0] = true;
        gen[2] = true;
        let mut kill = vec![false; 9];
        kill[5] = true;
        let out = propagate(&succ, &gen, &kill);
        assert_eq!(
            out,
            vec![false, true, true, true, true, true, false, false, true]
        );
    }
}
