//! One verified gen/kill propagation for every checker analysis.
//!
//! The Datalog spec has rules of this shape:
//!
//! ```text
//! invalid(R, Q) :- invalidated_at(R, P), cfg_edge(P, Q).
//! invalid(R, Q) :- invalid(R, P), cfg_edge(P, Q), !rebound_at(R, P).
//! ```
//!
//! For one subject `R`, `invalid` is the least set `S` such that:
//! the successors of each `gen` node are in `S`, and the successors of each
//! node in `S` that is not a `kill` node are in `S`.
//! [`propagate`] computes exactly that least fixpoint. Backward analyses use it
//! on the reversed graph.
//!
//! `proofs/link` includes this file. It proves that the W0301 fixpoint is the
//! invalid set of the B1 CFG model (`proofs/link/src/dataflow_link.rs`). Run
//! `proofs/link/verify.sh` after a change to a spec in this file.

use vstd::prelude::*;

verus! {

/// The graph has an edge from `p` to `q`.
pub open spec fn spec_edge(succ: Seq<Seq<usize>>, p: int, q: int) -> bool {
    0 <= p < succ.len() && exists|j: int| 0 <= j < succ[p].len() && succ[p][j] as int == q
}

/// The set `s` is closed under the two rules.
pub open spec fn spec_closed(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    s: Set<int>,
) -> bool {
    &&& forall|p: int, q: int|
        0 <= p < gen.len() && gen[p] && #[trigger] spec_edge(succ, p, q) ==> s.contains(q)
    &&& forall|p: int, q: int|
        0 <= p < kill.len() && s.contains(p) && !kill[p] && #[trigger] spec_edge(succ, p, q)
            ==> s.contains(q)
}

/// Node `i` is in the least closed set.
pub open spec fn spec_in_lfp(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    i: int,
) -> bool {
    forall|s: Set<int>| #[trigger] spec_closed(succ, gen, kill, s) ==> s.contains(i)
}

/// The inputs describe one graph with `n` nodes.
pub open spec fn spec_well_formed(succ: Seq<Seq<usize>>, gen: Seq<bool>, kill: Seq<bool>) -> bool {
    &&& gen.len() == succ.len()
    &&& kill.len() == succ.len()
    &&& forall|p: int, j: int|
        0 <= p < succ.len() && 0 <= j < succ[p].len() ==> (#[trigger] succ[p][j]) < succ.len()
}

/// The view of an adjacency list.
pub open spec fn spec_view(succ: &Vec<Vec<usize>>) -> Seq<Seq<usize>> {
    Seq::new(succ.len() as nat, |i: int| succ[i]@)
}

/// The set of marked nodes.
pub open spec fn spec_marked(out: Seq<bool>) -> Set<int> {
    vstd::set_lib::set_int_range(0, out.len() as int).filter(|i: int| out[i])
}

/// Every successor of node `p` is marked.
pub open spec fn spec_succs_marked(succ: Seq<Seq<usize>>, out: Seq<bool>, p: int) -> bool {
    forall|j: int| 0 <= j < succ[p].len() ==> out[#[trigger] succ[p][j] as int]
}

/// The number of unmarked nodes.
pub open spec fn spec_count_unmarked(out: Seq<bool>) -> nat
    decreases out.len(),
{
    if out.len() == 0 {
        0
    } else {
        spec_count_unmarked(out.drop_last()) + if out.last() {
            0nat
        } else {
            1nat
        }
    }
}

/// The invariant of the worklist loops in [`propagate`]:
///
/// - each marked node is in the least fixpoint (soundness);
/// - each node in the worklist is marked;
/// - the successors of each `gen` node below `seeded` are marked;
/// - the successors of each marked non-`kill` node are marked, unless the node
///   is in the worklist or is the node `active` that the loop processes now.
pub open spec fn spec_work_inv(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    out: Seq<bool>,
    work: Seq<usize>,
    seeded: int,
    active: int,
) -> bool {
    &&& spec_well_formed(succ, gen, kill)
    &&& out.len() == succ.len()
    &&& out.len() <= usize::MAX
    &&& seeded <= out.len()
    &&& forall|i: int| 0 <= i < out.len() && #[trigger] out[i] ==> spec_in_lfp(succ, gen, kill, i)
    &&& forall|w: int|
        0 <= w < work.len() ==> (#[trigger] work[w] as int) < out.len() && out[work[w] as int]
    &&& forall|p: int| 0 <= p < seeded && gen[p] ==> #[trigger] spec_succs_marked(succ, out, p)
    &&& forall|x: int|
        0 <= x < out.len() && x != active && out[x] && !kill[x] && !work.contains(x as usize)
            ==> #[trigger] spec_succs_marked(succ, out, x)
}

/// A node is in the marked set if and only if it is marked.
pub proof fn lemma_marked_contains(out: Seq<bool>)
    ensures
        forall|i: int| #[trigger] spec_marked(out).contains(i) == (0 <= i < out.len() && out[i]),
{
    vstd::set_lib::lemma_int_range(0, out.len() as int);
}

/// Marking an unmarked node removes one unmarked node.
pub proof fn lemma_count_unmarked_mark(out: Seq<bool>, q: int)
    requires
        0 <= q < out.len(),
        !out[q],
    ensures
        spec_count_unmarked(out.update(q, true)) + 1 == spec_count_unmarked(out),
    decreases out.len(),
{
    let u = out.update(q, true);
    if q == out.len() - 1 {
        assert(u.drop_last() =~= out.drop_last());
    } else {
        lemma_count_unmarked_mark(out.drop_last(), q);
        assert(u.drop_last() =~= out.drop_last().update(q, true));
    }
}

/// One rule step is sound: a successor of a `gen` node, or of a non-`kill` node
/// in the least fixpoint, is in the least fixpoint.
pub proof fn lemma_step_sound(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    p: int,
    j: int,
)
    requires
        spec_well_formed(succ, gen, kill),
        0 <= p < succ.len(),
        0 <= j < succ[p].len(),
        gen[p] || (!kill[p] && spec_in_lfp(succ, gen, kill, p)),
    ensures
        spec_in_lfp(succ, gen, kill, succ[p][j] as int),
{
    let q = succ[p][j] as int;
    assert(spec_edge(succ, p, q));
    assert forall|s: Set<int>| #[trigger] spec_closed(succ, gen, kill, s) implies s.contains(q) by {
        if !gen[p] {
            assert(s.contains(p));
        }
    }
}

/// A push keeps every element and adds the pushed one.
pub proof fn lemma_push_contains(before: Seq<usize>, after: Seq<usize>, q: usize)
    requires
        after == before.push(q),
    ensures
        after.contains(q),
        forall|x: usize| #[trigger] before.contains(x) ==> after.contains(x),
{
    assert(after[before.len() as int] == q);
    assert forall|x: usize| #[trigger] before.contains(x) implies after.contains(x) by {
        let k = choose|k: int| 0 <= k < before.len() && before[k] == x;
        assert(after[k] == x);
    }
}

/// A pop removes only the last element.
pub proof fn lemma_pop_contains(before: Seq<usize>, after: Seq<usize>, p: usize)
    requires
        before.len() > 0,
        after == before.subrange(0, before.len() - 1),
        p == before[before.len() - 1],
    ensures
        forall|x: usize| #[trigger] before.contains(x) ==> after.contains(x) || x == p,
{
    assert forall|x: usize| #[trigger] before.contains(x) implies after.contains(x) || x == p by {
        let k = choose|k: int| 0 <= k < before.len() && before[k] == x;
        if k < before.len() - 1 {
            assert(after[k] == x);
        }
    }
}

/// Marking a node of the least fixpoint and pushing it keeps the invariant, and
/// removes one unmarked node.
pub proof fn lemma_mark_and_push(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    out: Seq<bool>,
    work: Seq<usize>,
    seeded: int,
    active: int,
    q: usize,
)
    requires
        spec_work_inv(succ, gen, kill, out, work, seeded, active),
        q < out.len(),
        !out[q as int],
        spec_in_lfp(succ, gen, kill, q as int),
    ensures
        spec_work_inv(succ, gen, kill, out.update(q as int, true), work.push(q), seeded, active),
        spec_count_unmarked(out.update(q as int, true)) + 1 == spec_count_unmarked(out),
{
    let new_out = out.update(q as int, true);
    let new_work = work.push(q);
    lemma_count_unmarked_mark(out, q as int);
    lemma_push_contains(work, new_work, q);
    assert forall|x: int|
        0 <= x < succ.len() && spec_succs_marked(succ, out, x) implies #[trigger] spec_succs_marked(
        succ,
        new_out,
        x,
    ) by {
        assert forall|j: int| 0 <= j < succ[x].len() implies new_out[#[trigger] succ[x][j]
            as int] by {
            assert(out[succ[x][j] as int]);
        }
    }
    assert forall|w: int| 0 <= w < new_work.len() implies (#[trigger] new_work[w] as int)
        < new_out.len() && new_out[new_work[w] as int] by {
        if w < work.len() {
            assert(new_work[w] == work[w]);
        }
    }
}

/// Popping the last node of the worklist keeps the invariant if the loop makes
/// the popped node the active node.
pub proof fn lemma_pop(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    out: Seq<bool>,
    before: Seq<usize>,
    after: Seq<usize>,
    p: usize,
)
    requires
        spec_work_inv(succ, gen, kill, out, before, succ.len() as int, -1),
        before.len() > 0,
        after == before.subrange(0, before.len() - 1),
        p == before[before.len() - 1],
    ensures
        spec_work_inv(succ, gen, kill, out, after, succ.len() as int, p as int),
        p < out.len(),
        out[p as int],
{
    lemma_pop_contains(before, after, p);
    assert forall|w: int| 0 <= w < after.len() implies (#[trigger] after[w] as int) < out.len()
        && out[after[w] as int] by {
        assert(after[w] == before[w]);
    }
}

/// The marked set is closed when the successors of every `gen` node and of every
/// marked non-`kill` node are marked.
pub proof fn lemma_marked_closed(
    succ: Seq<Seq<usize>>,
    gen: Seq<bool>,
    kill: Seq<bool>,
    out: Seq<bool>,
)
    requires
        spec_well_formed(succ, gen, kill),
        out.len() == succ.len(),
        forall|p: int| 0 <= p < succ.len() && gen[p] ==> #[trigger] spec_succs_marked(succ, out, p),
        forall|p: int|
            0 <= p < succ.len() && out[p] && !kill[p] ==> #[trigger] spec_succs_marked(
                succ,
                out,
                p,
            ),
    ensures
        spec_closed(succ, gen, kill, spec_marked(out)),
{
    let m = spec_marked(out);
    lemma_marked_contains(out);
    assert forall|p: int, q: int|
        0 <= p < gen.len() && gen[p] && #[trigger] spec_edge(succ, p, q) implies m.contains(q) by {
        let j = choose|j: int| 0 <= j < succ[p].len() && succ[p][j] as int == q;
        assert(spec_succs_marked(succ, out, p));
        assert(out[succ[p][j] as int]);
    }
    assert forall|p: int, q: int|
        0 <= p < kill.len() && m.contains(p) && !kill[p] && #[trigger] spec_edge(succ, p, q)
            implies m.contains(q) by {
        let j = choose|j: int| 0 <= j < succ[p].len() && succ[p][j] as int == q;
        assert(spec_succs_marked(succ, out, p));
        assert(out[succ[p][j] as int]);
    }
}

/// When the worklist is empty, the marked nodes are exactly the least fixpoint.
pub proof fn lemma_done(succ: Seq<Seq<usize>>, gen: Seq<bool>, kill: Seq<bool>, out: Seq<bool>)
    requires
        spec_work_inv(succ, gen, kill, out, Seq::empty(), succ.len() as int, -1),
    ensures
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == spec_in_lfp(succ, gen, kill, i),
{
    let none = Seq::<usize>::empty();
    assert forall|p: int|
        0 <= p < succ.len() && out[p] && !kill[p] implies #[trigger] spec_succs_marked(
        succ,
        out,
        p,
    ) by {
        assert(!none.contains(p as usize));
    }
    lemma_marked_closed(succ, gen, kill, out);
    lemma_marked_contains(out);
    let m = spec_marked(out);
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == spec_in_lfp(
        succ,
        gen,
        kill,
        i,
    ) by {
        if !out[i] {
            assert(!m.contains(i));
        }
    }
}

/// Computes the least fixpoint of the gen/kill rules.
///
/// `succ[p]` lists the successors of node `p`. The result marks node `i` if and
/// only if `i` is in the least closed set.
pub fn propagate(succ: &Vec<Vec<usize>>, gen: &Vec<bool>, kill: &Vec<bool>) -> (out: Vec<bool>)
    requires
        spec_well_formed(spec_view(succ), gen@, kill@),
    ensures
        out.len() == succ.len(),
        forall|i: int|
            0 <= i < out.len() ==> #[trigger] out[i] == spec_in_lfp(
                spec_view(succ),
                gen@,
                kill@,
                i,
            ),
{
    let ghost sv = spec_view(succ);
    let n = succ.len();
    let mut out: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            out.len() == k,
            forall|i: int| 0 <= i < k ==> !out[i],
        decreases n - k,
    {
        out.push(false);
        k += 1;
    }
    let mut work: Vec<usize> = Vec::new();
    // Seed: mark the successors of each `gen` node.
    let mut p: usize = 0;
    while p < n
        invariant
            p <= n,
            n == succ.len(),
            sv == spec_view(succ),
            spec_work_inv(sv, gen@, kill@, out@, work@, p as int, -1),
        decreases n - p,
    {
        if gen[p] {
            let row = &succ[p];
            assert(row@ == sv[p as int]);
            let mut j: usize = 0;
            while j < row.len()
                invariant
                    p < n,
                    gen[p as int],
                    j <= row.len(),
                    row@ == sv[p as int],
                    n == succ.len(),
                    sv == spec_view(succ),
                    spec_work_inv(sv, gen@, kill@, out@, work@, p as int, -1),
                    forall|jj: int| 0 <= jj < j ==> out[#[trigger] sv[p as int][jj] as int],
                decreases row.len() - j,
            {
                let q = row[j];
                if !out[q] {
                    proof {
                        lemma_step_sound(sv, gen@, kill@, p as int, j as int);
                        lemma_mark_and_push(sv, gen@, kill@, out@, work@, p as int, -1, q);
                    }
                    out.set(q, true);
                    work.push(q);
                }
                j += 1;
            }
            assert(spec_succs_marked(sv, out@, p as int));
        }
        p += 1;
    }
    // Propagate: process the worklist until it is empty.
    while work.len() > 0
        invariant
            n == succ.len(),
            sv == spec_view(succ),
            spec_work_inv(sv, gen@, kill@, out@, work@, n as int, -1),
        decreases 2 * spec_count_unmarked(out@) + work.len(),
    {
        let ghost before = work@;
        match work.pop() {
            None => {},
            Some(p) => {
                proof {
                    lemma_pop(sv, gen@, kill@, out@, before, work@, p);
                }
                if !kill[p] {
                    let ghost bound = 2 * spec_count_unmarked(out@) + work.len();
                    let row = &succ[p];
                    assert(row@ == sv[p as int]);
                    let mut j: usize = 0;
                    while j < row.len()
                        invariant
                            p < n,
                            !kill[p as int],
                            out[p as int],
                            j <= row.len(),
                            row@ == sv[p as int],
                            n == succ.len(),
                            sv == spec_view(succ),
                            spec_work_inv(sv, gen@, kill@, out@, work@, n as int, p as int),
                            forall|jj: int| 0 <= jj < j ==> out[#[trigger] sv[p as int][jj] as int],
                            2 * spec_count_unmarked(out@) + work.len() <= bound,
                        decreases row.len() - j,
                    {
                        let q = row[j];
                        if !out[q] {
                            proof {
                                lemma_step_sound(sv, gen@, kill@, p as int, j as int);
                                lemma_mark_and_push(
                                    sv,
                                    gen@,
                                    kill@,
                                    out@,
                                    work@,
                                    n as int,
                                    p as int,
                                    q,
                                );
                            }
                            out.set(q, true);
                            work.push(q);
                        }
                        j += 1;
                    }
                    assert(spec_succs_marked(sv, out@, p as int));
                }
            },
        }
    }
    proof {
        assert(work@ =~= Seq::<usize>::empty());
        lemma_done(sv, gen@, kill@, out@);
    }
    out
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// A reference least fixpoint by naive iteration.
    fn naive(succ: &[Vec<usize>], gen: &[bool], kill: &[bool]) -> Vec<bool> {
        let n = succ.len();
        let mut s = vec![false; n];
        loop {
            let mut changed = false;
            for p in 0..n {
                if gen[p] || (s[p] && !kill[p]) {
                    for &q in &succ[p] {
                        if !s[q] {
                            s[q] = true;
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                return s;
            }
        }
    }

    #[test]
    fn chain_stops_at_kill() {
        // 0 -> 1 -> 2 -> 3, gen at 0, kill at 2
        let succ = vec![vec![1], vec![2], vec![3], vec![]];
        let out = propagate(
            &succ,
            &vec![true, false, false, false],
            &vec![false, false, true, false],
        );
        assert_eq!(out, vec![false, true, true, false]);
    }

    #[test]
    fn loop_reaches_gen_node_itself() {
        // 0 -> 1 -> 0
        let succ = vec![vec![1], vec![0]];
        let out = propagate(&succ, &vec![true, false], &vec![false, false]);
        assert_eq!(out, vec![true, true]);
    }

    proptest! {
        #[test]
        fn matches_naive_fixpoint(
            n in 1usize..12,
            edges in proptest::collection::vec((0usize..12, 0usize..12), 0..40),
            gens in proptest::collection::vec(any::<bool>(), 12),
            kills in proptest::collection::vec(any::<bool>(), 12),
        ) {
            let mut succ = vec![Vec::new(); n];
            for (a, b) in edges {
                succ[a % n].push(b % n);
            }
            let gen: Vec<bool> = gens[..n].to_vec();
            let kill: Vec<bool> = kills[..n].to_vec();
            prop_assert_eq!(propagate(&succ, &gen, &kill), naive(&succ, &gen, &kill));
        }
    }
}
