//! The place algebra.
//!
//! A place is a root plus a sequence of steps. The checker compares two places
//! only when they have the same root, so this module works on step sequences.
//!
//! Rule 3 of the design: a `mut(m)` invalidates a reference to `p` when `m` is a
//! strict prefix of `p` and `p` crosses at least one unstable step after `m`.

use vstd::prelude::*;

verus! {

/// The kind of one step in a place.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum StepKind {
    /// A struct field or a tuple index.
    Field { id: u32 },
    /// An enum variant payload.
    Variant { id: u32 },
    /// Any element of a collection or an array.
    Elem,
    /// One side of a split: `[..k]` (`hi == false`) or `[k..]` (`hi == true`).
    Seg { split: u32, hi: bool },
    /// The target of a pointer type, such as `Box` or a declared pointer.
    Deref,
}

/// One step in a place, with its stability.
///
/// The type that owns the step declares the stability. The calculus does not fix
/// a list of stable steps.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Step {
    /// The kind of step.
    pub kind: StepKind,
    /// True if a mutation can move or free what is behind this step.
    pub unstable: bool,
}

/// Two steps at the same position can name the same memory.
pub open spec fn spec_step_alias(a: Step, b: Step) -> bool {
    match (a.kind, b.kind) {
        (StepKind::Field { id: x }, StepKind::Field { id: y }) => x == y,
        (StepKind::Variant { id: x }, StepKind::Variant { id: y }) => x == y,
        (StepKind::Elem, StepKind::Elem) => true,
        (StepKind::Elem, StepKind::Seg { .. }) => true,
        (StepKind::Seg { .. }, StepKind::Elem) => true,
        (StepKind::Seg { split: s1, hi: h1 }, StepKind::Seg { split: s2, hi: h2 }) => s1 != s2 || h1
            == h2,
        (StepKind::Deref, StepKind::Deref) => true,
        _ => false,
    }
}

/// Step `a` names a subset of the memory that step `b` names.
pub open spec fn spec_step_within(a: Step, b: Step) -> bool {
    match (a.kind, b.kind) {
        (StepKind::Field { id: x }, StepKind::Field { id: y }) => x == y,
        (StepKind::Variant { id: x }, StepKind::Variant { id: y }) => x == y,
        (StepKind::Elem, StepKind::Elem) => true,
        (StepKind::Seg { .. }, StepKind::Elem) => true,
        (StepKind::Seg { split: s1, hi: h1 }, StepKind::Seg { split: s2, hi: h2 }) => s1 == s2 && h1
            == h2,
        (StepKind::Deref, StepKind::Deref) => true,
        _ => false,
    }
}

/// `m` can be a prefix of `p`: each step of `m` can alias the step of `p` at the same position.
pub open spec fn spec_may_prefix(m: Seq<Step>, p: Seq<Step>) -> bool {
    m.len() <= p.len() && forall|i: int|
        #![trigger m[i]]
        #![trigger p[i]]
        0 <= i < m.len() ==> spec_step_alias(m[i], p[i])
}

/// `p` has an unstable step at position `from` or later.
pub open spec fn spec_crosses_unstable(from: int, p: Seq<Step>) -> bool {
    exists|i: int| from <= i < p.len() && #[trigger] p[i].unstable
}

/// Rule 3: a mutation of `m` invalidates a reference to `p`.
pub open spec fn spec_invalidates(m: Seq<Step>, p: Seq<Step>) -> bool {
    m.len() < p.len() && spec_may_prefix(m, p) && spec_crosses_unstable(m.len() as int, p)
}

/// `p` is inside or equal to `d`. A declared `mut(d)` covers a mutation of `p`.
pub open spec fn spec_within(p: Seq<Step>, d: Seq<Step>) -> bool {
    d.len() <= p.len() && forall|i: int|
        #![trigger p[i]]
        #![trigger d[i]]
        0 <= i < d.len() ==> spec_step_within(p[i], d[i])
}

/// `p` and `q` can share memory.
pub open spec fn spec_overlaps(p: Seq<Step>, q: Seq<Step>) -> bool {
    spec_may_prefix(p, q) || spec_may_prefix(q, p)
}

/// Returns true if two steps at the same position can name the same memory.
pub fn step_alias(a: &Step, b: &Step) -> (r: bool)
    ensures
        r == spec_step_alias(*a, *b),
{
    match (a.kind, b.kind) {
        (StepKind::Field { id: x }, StepKind::Field { id: y }) => x == y,
        (StepKind::Variant { id: x }, StepKind::Variant { id: y }) => x == y,
        (StepKind::Elem, StepKind::Elem) => true,
        (StepKind::Elem, StepKind::Seg { .. }) => true,
        (StepKind::Seg { .. }, StepKind::Elem) => true,
        (StepKind::Seg { split: s1, hi: h1 }, StepKind::Seg { split: s2, hi: h2 }) => s1 != s2 || h1
            == h2,
        (StepKind::Deref, StepKind::Deref) => true,
        _ => false,
    }
}

/// Returns true if step `a` names a subset of the memory that step `b` names.
pub fn step_within(a: &Step, b: &Step) -> (r: bool)
    ensures
        r == spec_step_within(*a, *b),
{
    match (a.kind, b.kind) {
        (StepKind::Field { id: x }, StepKind::Field { id: y }) => x == y,
        (StepKind::Variant { id: x }, StepKind::Variant { id: y }) => x == y,
        (StepKind::Elem, StepKind::Elem) => true,
        (StepKind::Seg { .. }, StepKind::Elem) => true,
        (StepKind::Seg { split: s1, hi: h1 }, StepKind::Seg { split: s2, hi: h2 }) => s1 == s2 && h1
            == h2,
        (StepKind::Deref, StepKind::Deref) => true,
        _ => false,
    }
}

/// Returns true if `m` can be a prefix of `p`.
pub fn may_prefix(m: &[Step], p: &[Step]) -> (r: bool)
    ensures
        r == spec_may_prefix(m@, p@),
{
    if m.len() > p.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < m.len()
        invariant
            i <= m.len(),
            m.len() <= p.len(),
            forall|j: int|
                #![trigger m@[j]]
                #![trigger p@[j]]
                0 <= j < i ==> spec_step_alias(m@[j], p@[j]),
        decreases m.len() - i,
    {
        if !step_alias(&m[i], &p[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// Returns true if `p` has an unstable step at position `from` or later.
pub fn crosses_unstable(from: usize, p: &[Step]) -> (r: bool)
    ensures
        r == spec_crosses_unstable(from as int, p@),
{
    let mut i: usize = from;
    while i < p.len()
        invariant
            from <= i,
            forall|j: int| from <= j < i && j < p.len() ==> !(#[trigger] p@[j]).unstable,
        decreases p.len() - i,
    {
        if p[i].unstable {
            return true;
        }
        i += 1;
    }
    proof {
        assert forall|j: int| from <= j < p.len() implies !(#[trigger] p@[j]).unstable by {}
    }
    false
}

/// Rule 3. Returns true if a mutation of `m` invalidates a reference to `p`.
pub fn invalidates(m: &[Step], p: &[Step]) -> (r: bool)
    ensures
        r == spec_invalidates(m@, p@),
{
    m.len() < p.len() && may_prefix(m, p) && crosses_unstable(m.len(), p)
}

/// Returns true if `p` is inside or equal to `d`.
pub fn within(p: &[Step], d: &[Step]) -> (r: bool)
    ensures
        r == spec_within(p@, d@),
{
    if d.len() > p.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < d.len()
        invariant
            i <= d.len(),
            d.len() <= p.len(),
            forall|j: int|
                #![trigger p@[j]]
                #![trigger d@[j]]
                0 <= j < i ==> spec_step_within(p@[j], d@[j]),
        decreases d.len() - i,
    {
        if !step_within(&p[i], &d[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// Returns true if `p` and `q` can share memory.
pub fn overlaps(p: &[Step], q: &[Step]) -> (r: bool)
    ensures
        r == spec_overlaps(p@, q@),
{
    may_prefix(p, q) || may_prefix(q, p)
}

/// Returns the steps of `a` followed by the steps of `b`.
///
/// Effect substitution uses this to put a callee place under a caller place.
pub fn concat(a: &[Step], b: &[Step]) -> (r: Vec<Step>)
    ensures
        r@ == a@ + b@,
{
    let mut r: Vec<Step> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            r@ == a@.subrange(0, i as int),
        decreases a.len() - i,
    {
        r.push(a[i]);
        assert(a@.subrange(0, i + 1) =~= a@.subrange(0, i as int).push(a@[i as int]));
        i += 1;
    }
    assert(a@.subrange(0, a.len() as int) =~= a@);
    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            r@ == a@ + b@.subrange(0, j as int),
        decreases b.len() - j,
    {
        r.push(b[j]);
        assert(a@ + b@.subrange(0, j + 1) =~= (a@ + b@.subrange(0, j as int)).push(b@[j as int]));
        j += 1;
    }
    assert(b@.subrange(0, b.len() as int) =~= b@);
    r
}

// ---------------------------------------------------------------------------
// Lemmas: the rules of the design hold for the algebra.
// ---------------------------------------------------------------------------

/// Step aliasing is symmetric.
pub proof fn lemma_step_alias_symmetric(a: Step, b: Step)
    ensures
        spec_step_alias(a, b) == spec_step_alias(b, a),
{
}

/// Rule 4: a mutation of `p` never invalidates a reference to `p` itself.
pub proof fn lemma_no_self_invalidation(p: Seq<Step>)
    ensures
        !spec_invalidates(p, p),
{
}

/// Rule 4: references into stable parts of `m` survive a mutation of `m`.
pub proof fn lemma_stable_suffix_survives(m: Seq<Step>, p: Seq<Step>)
    requires
        forall|i: int| m.len() <= i < p.len() ==> !(#[trigger] p[i]).unstable,
    ensures
        !spec_invalidates(m, p),
{
}

/// Disjoint places never invalidate each other.
pub proof fn lemma_disjoint_no_invalidation(m: Seq<Step>, p: Seq<Step>)
    requires
        !spec_overlaps(m, p),
    ensures
        !spec_invalidates(m, p),
{
}

/// A mutation deeper inside `m` invalidates no more than a mutation of `m`.
///
/// This justifies the wildcard: `mut(w..)` invalidates exactly what `mut(w)` does.
pub proof fn lemma_deeper_mutation_weaker(m: Seq<Step>, s: Seq<Step>, p: Seq<Step>)
    requires
        spec_invalidates(m + s, p),
    ensures
        spec_invalidates(m, p),
{
    assert forall|i: int|
        #![trigger m[i]]
        #![trigger p[i]]
        0 <= i < m.len() implies spec_step_alias(m[i], p[i]) by {
        assert((m + s)[i] == m[i]);
    }
    let k = choose|k: int| (m + s).len() <= k < p.len() && #[trigger] p[k].unstable;
    assert(m.len() <= k);
}

/// Step inclusion implies step aliasing.
pub proof fn lemma_step_within_alias(a: Step, b: Step)
    requires
        spec_step_within(a, b),
    ensures
        spec_step_alias(a, b),
{
}

/// A covered mutation overlaps its cover.
pub proof fn lemma_within_overlaps(p: Seq<Step>, d: Seq<Step>)
    requires
        spec_within(p, d),
    ensures
        spec_may_prefix(d, p),
{
    assert forall|i: int|
        #![trigger d[i]]
        #![trigger p[i]]
        0 <= i < d.len() implies spec_step_alias(d[i], p[i]) by {
        lemma_step_within_alias(p[i], d[i]);
    }
}

/// Signature soundness: if `m` is inside the declared place `d`, then each reference
/// that `m` invalidates is also invalidated by `d`. A caller can use the signature.
pub proof fn lemma_cover_invalidates_more(m: Seq<Step>, d: Seq<Step>, p: Seq<Step>)
    requires
        spec_within(m, d),
        spec_invalidates(m, p),
    ensures
        spec_invalidates(d, p),
{
    assert forall|i: int|
        #![trigger d[i]]
        #![trigger p[i]]
        0 <= i < d.len() implies spec_step_alias(d[i], p[i]) by {
        assert(spec_step_within(m[i], d[i]));
        assert(spec_step_alias(m[i], p[i]));
    }
    let k = choose|k: int| m.len() <= k < p.len() && #[trigger] p[k].unstable;
    assert(d.len() <= k);
}

/// Inclusion is transitive.
pub proof fn lemma_within_transitive(a: Seq<Step>, b: Seq<Step>, c: Seq<Step>)
    requires
        spec_within(a, b),
        spec_within(b, c),
    ensures
        spec_within(a, c),
{
    assert forall|i: int|
        #![trigger a[i]]
        #![trigger c[i]]
        0 <= i < c.len() implies spec_step_within(a[i], c[i]) by {
        assert(spec_step_within(a[i], b[i]));
        assert(spec_step_within(b[i], c[i]));
    }
}

/// The two sides of one split never overlap.
pub proof fn lemma_split_sides_disjoint(base: Seq<Step>, split: u32, u1: bool, u2: bool)
    ensures
        !spec_overlaps(
            base.push(Step { kind: StepKind::Seg { split, hi: false }, unstable: u1 }),
            base.push(Step { kind: StepKind::Seg { split, hi: true }, unstable: u2 }),
        ),
{
    let lo = base.push(Step { kind: StepKind::Seg { split, hi: false }, unstable: u1 });
    let hi = base.push(Step { kind: StepKind::Seg { split, hi: true }, unstable: u2 });
    assert(!spec_step_alias(lo[base.len() as int], hi[base.len() as int]));
    assert(!spec_step_alias(hi[base.len() as int], lo[base.len() as int]));
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    const fn f(id: u32) -> Step {
        Step {
            kind: StepKind::Field { id },
            unstable: false,
        }
    }
    const fn elem() -> Step {
        Step {
            kind: StepKind::Elem,
            unstable: true,
        }
    }
    const fn seg(split: u32, hi: bool) -> Step {
        Step {
            kind: StepKind::Seg { split, hi },
            unstable: true,
        }
    }
    const fn variant(id: u32) -> Step {
        Step {
            kind: StepKind::Variant { id },
            unstable: true,
        }
    }

    #[test]
    fn push_invalidates_element_refs() {
        // mut(world.entities) vs &Entity in world.entities[]
        assert!(invalidates(&[f(0)], &[f(0), elem()]));
    }

    #[test]
    fn element_mutation_keeps_element_refs() {
        // mut(world.entities[]) vs &Entity in world.entities[]
        assert!(!invalidates(&[f(0), elem()], &[f(0), elem()]));
    }

    #[test]
    fn stable_and_disjoint_places_survive() {
        // mut(world.score) vs world.entities[]
        assert!(!invalidates(&[f(2)], &[f(0), elem()]));
        // mut(world) vs &u32 in world.score
        assert!(!invalidates(&[], &[f(2)]));
    }

    #[test]
    fn payload_refs_die_when_enum_changes() {
        // mut(world.entities[]) vs world.entities[].weapon.Some
        assert!(invalidates(
            &[f(0), elem()],
            &[f(0), elem(), f(3), variant(1)]
        ));
        // different variants do not alias
        assert!(!overlaps(&[variant(0)], &[variant(1)]));
    }

    #[test]
    fn split_sides_are_disjoint_but_inside_elements() {
        let lo = [f(0), seg(7, false)];
        let hi = [f(0), seg(7, true)];
        assert!(!overlaps(&lo, &hi));
        assert!(overlaps(&lo, &[f(0), elem()]));
        assert!(within(&lo, &[f(0), elem()]));
        assert!(!within(&[f(0), elem()], &lo));
        assert!(overlaps(&[f(0), seg(7, false)], &[f(0), seg(8, true)]));
    }

    #[test]
    fn within_is_prefix_inclusion() {
        assert!(within(&[f(0), elem(), f(1)], &[f(0)]));
        assert!(within(&[f(0)], &[f(0)]));
        assert!(!within(&[f(0)], &[f(0), elem()]));
        assert!(!within(&[f(1)], &[f(0)]));
    }

    #[test]
    fn concat_appends_steps() {
        assert_eq!(concat(&[f(0), elem()], &[f(1)]), vec![f(0), elem(), f(1)]);
        assert_eq!(concat(&[], &[f(1)]), vec![f(1)]);
        assert_eq!(concat(&[f(0)], &[]), vec![f(0)]);
    }

    #[test]
    fn crosses_unstable_counts_from_offset() {
        assert!(crosses_unstable(0, &[f(0), elem()]));
        assert!(!crosses_unstable(2, &[f(0), elem()]));
        assert!(!crosses_unstable(5, &[f(0)]));
    }
}
