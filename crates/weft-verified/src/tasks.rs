//! The composition of the how of a task slot (plan stage R0z Z9c-A, proof P1).
//!
//! A call slot runs a function value as a task. The fact generator joins
//! what it knows about the task: the flags (`thread`, `twice`, `many`,
//! `seq`, `foreign`), the values of the interface that run at the same time
//! (`with`), and the places that the callee changes (`writes`) and reads
//! (`reads`). Sema adds the values that run with the task outside its
//! window to the how with [`compose`] (`analysis::tasks::add_with`).
//!
//! [`compose`] is that join. It proves:
//!
//! * no flag is lost: each flag of the result is the `or` of the flags;
//! * no entry is lost: an entry is in a set of the result if and only if it
//!   is in that set of one of the two hows (also for sets that are not
//!   sorted);
//! * the result of two sorted hows is sorted (strictly increasing sets);
//! * each how is within the result (`spec_le`), and the composition is
//!   monotone (`lemma_compose_monotone`).
//!
//! The proof does not show that the inputs are complete: that the fact
//! generator gives each value that can run with the task. The oracles test
//! that (`docs/ir.md` 9.8).
//!
//! `proofs/link` includes this file. `proofs/verify-all.sh` verifies it.

use vstd::prelude::*;

verus! {

/// `x` is one of the first `n` entries of `s`.
pub open spec fn spec_has(s: Seq<u32>, n: int, x: u32) -> bool {
    exists|k: int| 0 <= k < n && #[trigger] s[k] == x
}

/// `x` is an entry of `s`.
pub open spec fn spec_in(s: Seq<u32>, x: u32) -> bool {
    spec_has(s, s.len() as int, x)
}

/// The entries of `s` are in strictly increasing order.
pub open spec fn spec_sorted(s: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

/// Each entry of `a` is an entry of `b`.
pub open spec fn spec_subset(a: Seq<u32>, b: Seq<u32>) -> bool {
    forall|x: u32| spec_in(a, x) ==> spec_in(b, x)
}

/// The entries of `r` are the entries of `a` and the entries of `b`.
pub open spec fn spec_union(a: Seq<u32>, b: Seq<u32>, r: Seq<u32>) -> bool {
    forall|x: u32| #[trigger] spec_in(r, x) <==> (spec_in(a, x) || spec_in(b, x))
}

/// The how of a task slot. The sets are sorted and have no duplicates.
pub struct SlotHow {
    /// The task is on another thread (a `fork` branch).
    pub thread: bool,
    /// Two tasks of the value can run at the same time.
    pub twice: bool,
    /// The callee can run the value more than once.
    pub many: bool,
    /// The tasks of the callee can run the value more than once on one path.
    pub seq: bool,
    /// The callee is code of a caller (the worst way).
    pub foreign: bool,
    /// The values (parameters) that run while the task runs.
    pub with: Vec<u32>,
    /// The places that the callee changes while the task runs.
    pub writes: Vec<u32>,
    /// The places that the callee reads while the task runs.
    pub reads: Vec<u32>,
}

/// How `a` is within how `b`: each flag of `a` is a flag of `b`, and each
/// entry of a set of `a` is an entry of that set of `b`.
pub open spec fn spec_le(a: &SlotHow, b: &SlotHow) -> bool {
    &&& (a.thread ==> b.thread)
    &&& (a.twice ==> b.twice)
    &&& (a.many ==> b.many)
    &&& (a.seq ==> b.seq)
    &&& (a.foreign ==> b.foreign)
    &&& spec_subset(a.with@, b.with@)
    &&& spec_subset(a.writes@, b.writes@)
    &&& spec_subset(a.reads@, b.reads@)
}

/// `r` is the composition of `a` and `b`: the `or` of each flag and the
/// union of each set.
pub open spec fn spec_composed(a: &SlotHow, b: &SlotHow, r: &SlotHow) -> bool {
    &&& r.thread == (a.thread || b.thread)
    &&& r.twice == (a.twice || b.twice)
    &&& r.many == (a.many || b.many)
    &&& r.seq == (a.seq || b.seq)
    &&& r.foreign == (a.foreign || b.foreign)
    &&& spec_union(a.with@, b.with@, r.with@)
    &&& spec_union(a.writes@, b.writes@, r.writes@)
    &&& spec_union(a.reads@, b.reads@, r.reads@)
}

/// The sets of how `h` are sorted.
pub open spec fn spec_how_sorted(h: &SlotHow) -> bool {
    spec_sorted(h.with@) && spec_sorted(h.writes@) && spec_sorted(h.reads@)
}

/// One more entry of a prefix.
pub proof fn lemma_has_next(s: Seq<u32>, n: int, x: u32)
    requires
        0 <= n < s.len(),
    ensures
        spec_has(s, n + 1, x) <==> (spec_has(s, n, x) || s[n] == x),
{
    if spec_has(s, n + 1, x) {
        let k = choose|k: int| 0 <= k < n + 1 && #[trigger] s[k] == x;
        if k < n {
            assert(0 <= k < n && s[k] == x);
        } else {
            assert(k == n);
        }
    }
    if spec_has(s, n, x) {
        let k = choose|k: int| 0 <= k < n && #[trigger] s[k] == x;
        assert(0 <= k < n + 1 && s[k] == x);
    }
    if s[n] == x {
        assert(0 <= n < n + 1 && s[n] == x);
    }
}

/// The entries of a sequence with one more entry at its end.
pub proof fn lemma_has_push(s: Seq<u32>, v: u32, x: u32)
    ensures
        spec_in(s.push(v), x) <==> (spec_in(s, x) || v == x),
{
    let t = s.push(v);
    assert(t.len() == s.len() + 1);
    assert(t[s.len() as int] == v);
    lemma_has_next(t, s.len() as int, x);
    if spec_has(t, s.len() as int, x) {
        let k = choose|k: int| 0 <= k < s.len() && #[trigger] t[k] == x;
        assert(t[k] == s[k]);
        assert(0 <= k < s.len() && s[k] == x);
    }
    if spec_in(s, x) {
        let k = choose|k: int| 0 <= k < s.len() && #[trigger] s[k] == x;
        assert(t[k] == s[k]);
        assert(0 <= k < s.len() && t[k] == x);
    }
}

/// The union of the sets `a` and `b`, in one pass over both.
///
/// No entry is lost and no entry is added. For sorted sets the result is
/// sorted (and has no duplicates); for other sets it still has each entry.
pub fn union(a: &[u32], b: &[u32]) -> (r: Vec<u32>)
    ensures
        spec_union(a@, b@, r@),
        spec_sorted(a@) && spec_sorted(b@) ==> spec_sorted(r@),
{
    let mut r: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a.len() || j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            forall|x: u32|
                #[trigger] spec_in(r@, x) <==> (spec_has(a@, i as int, x) || spec_has(b@, j as int, x)),
            spec_sorted(a@) && spec_sorted(b@) ==> spec_sorted(r@),
            spec_sorted(a@) && spec_sorted(b@) ==> forall|k: int|
                0 <= k < r@.len() ==> (i < a.len() ==> r@[k] < a@[i as int]) && (j < b.len()
                    ==> r@[k] < b@[j as int]),
        decreases a.len() - i + b.len() - j,
    {
        let ghost r0 = r@;
        let ghost i0 = i as int;
        let ghost j0 = j as int;
        // The next entry: of `a`, of `b`, or of both (one copy of an entry
        // that both sets have).
        let (v, ta, tb) = if j >= b.len() || (i < a.len() && a[i] < b[j]) {
            (a[i], true, false)
        } else if i >= a.len() || b[j] < a[i] {
            (b[j], false, true)
        } else {
            (a[i], true, true)
        };
        assert(ta || tb);
        assert(ta ==> i0 < a@.len() && v == a@[i0]);
        assert(tb ==> j0 < b@.len() && v == b@[j0]);
        assert(ta && !tb && j0 < b@.len() ==> v < b@[j0]);
        assert(tb && !ta && i0 < a@.len() ==> v < a@[i0]);
        r.push(v);
        let ni: usize = if ta {
            i + 1
        } else {
            i
        };
        let nj: usize = if tb {
            j + 1
        } else {
            j
        };
        proof {
            assert(r@ == r0.push(v));
            assert forall|x: u32|
                #[trigger] spec_in(r@, x) <==> (spec_has(a@, ni as int, x) || spec_has(b@, nj as int, x)) by {
                lemma_has_push(r0, v, x);
                if ta {
                    lemma_has_next(a@, i0, x);
                }
                if tb {
                    lemma_has_next(b@, j0, x);
                }
            }
            if spec_sorted(a@) && spec_sorted(b@) {
                assert forall|k: int|
                    0 <= k < r@.len() implies (ni < a.len() ==> r@[k] < a@[ni as int]) && (nj
                        < b.len() ==> r@[k] < b@[nj as int]) by {
                    if k < r0.len() {
                        assert(r@[k] == r0[k]);
                    } else {
                        assert(r@[k] == v);
                    }
                    if ta && ni < a.len() {
                        assert(a@[i0] < a@[ni as int]);
                    }
                    if tb && nj < b.len() {
                        assert(b@[j0] < b@[nj as int]);
                    }
                }
                assert forall|p: int, q: int| 0 <= p < q < r@.len() implies r@[p] < r@[q] by {
                    assert(r@[p] == r0[p]);
                    if q < r0.len() {
                        assert(r@[q] == r0[q]);
                    } else {
                        assert(r@[q] == v);
                    }
                }
            }
        }
        i = ni;
        j = nj;
    }
    r
}

/// The composition of the slot hows `a` and `b`: the `or` of each flag and
/// the union of each set. Each how is within the result.
pub fn compose(a: &SlotHow, b: &SlotHow) -> (r: SlotHow)
    ensures
        spec_composed(a, b, &r),
        spec_how_sorted(a) && spec_how_sorted(b) ==> spec_how_sorted(&r),
        spec_le(a, &r),
        spec_le(b, &r),
{
    let r = SlotHow {
        thread: a.thread || b.thread,
        twice: a.twice || b.twice,
        many: a.many || b.many,
        seq: a.seq || b.seq,
        foreign: a.foreign || b.foreign,
        with: union(a.with.as_slice(), b.with.as_slice()),
        writes: union(a.writes.as_slice(), b.writes.as_slice()),
        reads: union(a.reads.as_slice(), b.reads.as_slice()),
    };
    proof {
        assert forall|x: u32| spec_in(a.with@, x) || spec_in(b.with@, x) implies spec_in(
            r.with@,
            x,
        ) by {}
        assert forall|x: u32| spec_in(a.writes@, x) || spec_in(b.writes@, x) implies spec_in(
            r.writes@,
            x,
        ) by {}
        assert forall|x: u32| spec_in(a.reads@, x) || spec_in(b.reads@, x) implies spec_in(
            r.reads@,
            x,
        ) by {}
    }
    r
}

/// The composition is monotone: hows within hows give a composition within
/// the composition.
pub proof fn lemma_compose_monotone(
    a: &SlotHow,
    b: &SlotHow,
    r: &SlotHow,
    a2: &SlotHow,
    b2: &SlotHow,
    r2: &SlotHow,
)
    requires
        spec_composed(a, b, r),
        spec_composed(a2, b2, r2),
        spec_le(a, a2),
        spec_le(b, b2),
    ensures
        spec_le(r, r2),
{
    assert forall|x: u32| spec_in(r.with@, x) implies spec_in(r2.with@, x) by {
        if spec_in(a.with@, x) {
            assert(spec_in(a2.with@, x));
        } else {
            assert(spec_in(b2.with@, x));
        }
    }
    assert forall|x: u32| spec_in(r.writes@, x) implies spec_in(r2.writes@, x) by {
        if spec_in(a.writes@, x) {
            assert(spec_in(a2.writes@, x));
        } else {
            assert(spec_in(b2.writes@, x));
        }
    }
    assert forall|x: u32| spec_in(r.reads@, x) implies spec_in(r2.reads@, x) by {
        if spec_in(a.reads@, x) {
            assert(spec_in(a2.reads@, x));
        } else {
            assert(spec_in(b2.reads@, x));
        }
    }
}

/// The composition with an empty how keeps the how.
pub proof fn lemma_compose_empty(a: &SlotHow, e: &SlotHow, r: &SlotHow)
    requires
        spec_composed(a, e, r),
        !e.thread && !e.twice && !e.many && !e.seq && !e.foreign,
        e.with@.len() == 0,
        e.writes@.len() == 0,
        e.reads@.len() == 0,
    ensures
        spec_le(r, a),
        spec_le(a, r),
{
    assert forall|x: u32| !spec_in(e.with@, x) && !spec_in(e.writes@, x) && !spec_in(
        e.reads@,
        x,
    ) by {}
}

} // verus!

impl SlotHow {
    /// The empty how: no flag and empty sets.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            thread: false,
            twice: false,
            many: false,
            seq: false,
            foreign: false,
            with: Vec::new(),
            writes: Vec::new(),
            reads: Vec::new(),
        }
    }
}

impl Default for SlotHow {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn set(v: &[u32]) -> Vec<u32> {
        let mut v = v.to_vec();
        v.sort_unstable();
        v.dedup();
        v
    }

    #[test]
    fn compose_keeps_each_flag_and_entry() {
        let a = SlotHow {
            twice: true,
            with: vec![1, 3],
            writes: vec![2],
            ..SlotHow::new()
        };
        let b = SlotHow {
            thread: true,
            with: vec![0, 3, 4],
            reads: vec![7],
            ..SlotHow::new()
        };
        let r = compose(&a, &b);
        assert!(r.thread && r.twice && !r.many && !r.seq && !r.foreign);
        assert_eq!(r.with, vec![0, 1, 3, 4]);
        assert_eq!(r.writes, vec![2]);
        assert_eq!(r.reads, vec![7]);
    }

    proptest! {
        #[test]
        fn union_is_the_sorted_union(a in proptest::collection::vec(0u32..20, 0..10),
                                     b in proptest::collection::vec(0u32..20, 0..10)) {
            let (a, b) = (set(&a), set(&b));
            let mut both = a.clone();
            both.extend(&b);
            prop_assert_eq!(union(&a, &b), set(&both));
        }

        #[test]
        fn union_of_unsorted_sets_keeps_each_entry(a in proptest::collection::vec(0u32..20, 0..10),
                                                  b in proptest::collection::vec(0u32..20, 0..10)) {
            let r = union(&a, &b);
            for x in a.iter().chain(&b) {
                prop_assert!(r.contains(x));
            }
            for x in &r {
                prop_assert!(a.contains(x) || b.contains(x));
            }
        }
    }
}
