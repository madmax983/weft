//! # L1. Places: the exec place algebra and the B3 layout model
//!
//! The exec core (`crates/weft-verified/src/places.rs`) has rule 3 as
//! `spec_invalidates` and `invalidates`. The B3 layout model
//! (`proofs/borrowing/src/layout.rs`) has the Weft rule as `lkills`.
//!
//! This file defines an embedding of exec places into model places and
//! proves:
//!
//! * `thm_lkills_implies_invalidates`: for all places, if the model kills a
//!   reference, then rule 3 invalidates it. This is the soundness direction.
//! * `thm_invalidates_exact`: if the steps do not alias falsely
//!   (`alias_exact`), rule 3 is equal to the model kill predicate.
//! * `lemma_typed_alias_exact`: places without split steps whose stability
//!   comes from their type have no false alias.
//! * `invalidates_in_model`: the exec function that the checker calls
//!   (`invalidates`, through its postcondition) computes the model predicate.
//!
//! The embedding: a stable step becomes a `Field` step. An unstable variant
//! step becomes a `Variant` step. Each other unstable step (an element, a
//! split side, a pointer target) becomes a child group (`Kid`). An injective
//! code (`kind_code`) gives each step kind its own field number or label.

use vstd::prelude::*;
use crate::places::{
    Step, StepKind, spec_invalidates, spec_may_prefix, spec_crosses_unstable, spec_step_alias,
    invalidates,
};
use crate::layout::{PStep, LPlace, flat, flat_hops, lkills, unstable};
use crate::model::Local;

verus! {

// ---------------------------------------------------------------------------
// The embedding
// ---------------------------------------------------------------------------

/// The first code after the codes of `Field` steps. Each `u32` id is below it.
pub open spec fn code_base() -> nat {
    0x1_0000_0000
}

/// An injective code for each step kind.
pub open spec fn kind_code(k: StepKind) -> nat {
    match k {
        StepKind::Field { id } => id as nat,
        StepKind::Variant { id } => code_base() + id as nat,
        StepKind::Elem => 2 * code_base(),
        StepKind::Deref => 2 * code_base() + 1,
        StepKind::Seg { split, hi } => 2 * code_base() + 2 + 2 * (split as nat) + if hi {
            1nat
        } else {
            0nat
        },
    }
}

/// The model step of an exec step. The stability of the exec step selects
/// the model step: the model makes `Field` steps stable and all others unstable.
pub open spec fn emb_step(s: Step) -> PStep {
    if !s.unstable {
        PStep::Field(kind_code(s.kind))
    } else {
        match s.kind {
            StepKind::Variant { id } => PStep::Variant(id as nat),
            _ => PStep::Kid(kind_code(s.kind)),
        }
    }
}

/// The model path of an exec path.
pub open spec fn emb_path(p: Seq<Step>) -> Seq<PStep> {
    p.map_values(|s: Step| emb_step(s))
}

/// The structured model place of a flat model path. A `Kid` step closes a
/// hop. The other steps go into the inline tail. The B3 checker builds
/// places in the same way (`lpost`: `Field` and `Variant` extend the tail,
/// `Child` adds a hop).
pub open spec fn to_lplace(root: Local, ps: Seq<PStep>) -> LPlace
    decreases ps.len(),
{
    if ps.len() == 0 {
        LPlace { root, hops: Seq::empty(), tail: Seq::empty() }
    } else {
        let p0 = to_lplace(root, ps.drop_last());
        match ps.last() {
            PStep::Kid(l) => LPlace { root, hops: p0.hops.push((p0.tail, l)), tail: Seq::empty() },
            st => LPlace { root, hops: p0.hops, tail: p0.tail.push(st) },
        }
    }
}

/// The model place of an exec place (a root and a path).
pub open spec fn lplace(root: Local, p: Seq<Step>) -> LPlace {
    to_lplace(root, emb_path(p))
}

// ---------------------------------------------------------------------------
// Properties of the embedding
// ---------------------------------------------------------------------------

/// The code is injective.
pub proof fn lemma_kind_code_injective(a: StepKind, b: StepKind)
    ensures
        kind_code(a) == kind_code(b) ==> a == b,
{
}

/// The embedding is injective.
pub proof fn lemma_emb_step_injective(a: Step, b: Step)
    ensures
        emb_step(a) == emb_step(b) ==> a == b,
{
    lemma_kind_code_injective(a.kind, b.kind);
}

/// The model stability of an embedded step is the exec stability.
pub proof fn lemma_emb_step_unstable(s: Step)
    ensures
        unstable(emb_step(s)) == s.unstable,
{
}

/// The steps of the hops after one more hop.
pub proof fn lemma_flat_hops_push(hops: Seq<(Seq<PStep>, crate::model::Label)>, h: (Seq<PStep>, crate::model::Label))
    ensures
        flat_hops(hops.push(h)) == flat_hops(hops) + h.0 + seq![PStep::Kid(h.1)],
{
    assert(hops.push(h).drop_last() =~= hops);
}

/// The structured place has exactly the flat path it was made from.
pub proof fn lemma_flat_to_lplace(root: Local, ps: Seq<PStep>)
    ensures
        flat(to_lplace(root, ps)) == ps,
        to_lplace(root, ps).root == root,
        forall|j: int| 0 <= j < to_lplace(root, ps).tail.len() ==> !(#[trigger] to_lplace(root, ps).tail[j] is Kid),
    decreases ps.len(),
{
    if ps.len() > 0 {
        let p0 = to_lplace(root, ps.drop_last());
        lemma_flat_to_lplace(root, ps.drop_last());
        match ps.last() {
            PStep::Kid(l) => {
                lemma_flat_hops_push(p0.hops, (p0.tail, l));
                assert(flat(to_lplace(root, ps)) =~= ps.drop_last() + seq![PStep::Kid(l)]);
                assert(ps.drop_last() + seq![PStep::Kid(l)] =~= ps);
            },
            st => {
                assert(flat(to_lplace(root, ps)) =~= flat(p0).push(st));
                assert(ps.drop_last().push(st) =~= ps);
                let t = to_lplace(root, ps).tail;
                assert forall|j: int| 0 <= j < t.len() implies !(#[trigger] t[j] is Kid) by {
                    if j < p0.tail.len() {
                        assert(t[j] == p0.tail[j]);
                    }
                }
            },
        }
    }
}

/// The flat path of an embedded exec place is the embedded path.
pub proof fn lemma_flat_lplace(root: Local, p: Seq<Step>)
    ensures
        flat(lplace(root, p)) == emb_path(p),
        lplace(root, p).root == root,
        emb_path(p).len() == p.len(),
{
    lemma_flat_to_lplace(root, emb_path(p));
}

// ---------------------------------------------------------------------------
// Theorems
// ---------------------------------------------------------------------------

/// **Soundness direction, for all places.** If the model kills a reference
/// at `(rp, p)` after a mutation of `(rm, m)`, then the roots are equal and
/// rule 3 invalidates the reference. Thus the checker kills at least what
/// the model kills.
pub proof fn thm_lkills_implies_invalidates(rm: Local, m: Seq<Step>, rp: Local, p: Seq<Step>)
    ensures
        lkills(lplace(rm, m), lplace(rp, p)) ==> rm == rp && spec_invalidates(m, p),
{
    lemma_flat_lplace(rm, m);
    lemma_flat_lplace(rp, p);
    if lkills(lplace(rm, m), lplace(rp, p)) {
        let fm = emb_path(m);
        let fp = emb_path(p);
        assert(fm.is_prefix_of(fp));
        assert forall|i: int|
            #![trigger m[i]]
            #![trigger p[i]]
            0 <= i < m.len() implies spec_step_alias(m[i], p[i]) by {
            assert(fm[i] == fp[i]);
            lemma_emb_step_injective(m[i], p[i]);
        }
        let j = choose|j: int| fm.len() <= j < fp.len() && #[trigger] unstable(fp[j]);
        lemma_emb_step_unstable(p[j]);
        assert(p[j].unstable);
        assert(spec_crosses_unstable(m.len() as int, p));
    }
}

/// At each position, if the steps before it are equal and the two steps can
/// alias, then they are equal. This excludes the aliases of split steps
/// (`[..k]` and `[j..]` can alias) and steps whose stability differs.
pub open spec fn alias_exact(m: Seq<Step>, p: Seq<Step>) -> bool {
    forall|i: int|
        0 <= i < m.len() && i < p.len() && m.subrange(0, i) == p.subrange(0, i)
            && #[trigger] spec_step_alias(m[i], p[i]) ==> m[i] == p[i]
}

/// With `alias_exact`, a possible prefix is an exact prefix.
pub proof fn lemma_may_prefix_exact(m: Seq<Step>, p: Seq<Step>, i: int)
    requires
        spec_may_prefix(m, p),
        alias_exact(m, p),
        0 <= i <= m.len(),
    ensures
        m.subrange(0, i) == p.subrange(0, i),
    decreases i,
{
    if i > 0 {
        lemma_may_prefix_exact(m, p, i - 1);
        assert(spec_step_alias(m[i - 1], p[i - 1]));
        assert(m[i - 1] == p[i - 1]);
        assert(m.subrange(0, i) =~= m.subrange(0, i - 1).push(m[i - 1]));
        assert(p.subrange(0, i) =~= p.subrange(0, i - 1).push(p[i - 1]));
    }
}

/// **Exactness.** Without false aliases, rule 3 on equal roots is exactly
/// the model kill predicate on the embedded places.
pub proof fn thm_invalidates_exact(rm: Local, m: Seq<Step>, rp: Local, p: Seq<Step>)
    requires
        alias_exact(m, p),
    ensures
        (rm == rp && spec_invalidates(m, p)) == lkills(lplace(rm, m), lplace(rp, p)),
{
    thm_lkills_implies_invalidates(rm, m, rp, p);
    lemma_flat_lplace(rm, m);
    lemma_flat_lplace(rp, p);
    if rm == rp && spec_invalidates(m, p) {
        let fm = emb_path(m);
        let fp = emb_path(p);
        lemma_may_prefix_exact(m, p, m.len() as int);
        assert(fm =~= fp.subrange(0, fm.len() as int)) by {
            assert forall|i: int| 0 <= i < fm.len() implies #[trigger] fm[i] == fp.subrange(0, fm.len() as int)[i] by {
                assert(m.subrange(0, m.len() as int)[i] == p.subrange(0, m.len() as int)[i]);
            }
        }
        assert(fm.is_prefix_of(fp));
        let k = choose|k: int| m.len() <= k < p.len() && #[trigger] p[k].unstable;
        lemma_emb_step_unstable(p[k]);
        assert(unstable(fp[k]));
    }
}

/// The stability of each step of `p` is a function `stab` of the steps
/// before it and of its kind. Sema has this property: the steps before a
/// position fix the type there, and the type fixes the stability.
pub open spec fn typed_by(stab: spec_fn(Seq<Step>, StepKind) -> bool, p: Seq<Step>) -> bool {
    forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].unstable == stab(p.subrange(0, i), p[i].kind)
}

/// The path has no split step.
pub open spec fn no_seg(p: Seq<Step>) -> bool {
    forall|i: int| 0 <= i < p.len() ==> !(#[trigger] p[i].kind is Seg)
}

/// Places without split steps, typed by the same stability function, have
/// no false alias.
pub proof fn lemma_typed_alias_exact(stab: spec_fn(Seq<Step>, StepKind) -> bool, m: Seq<Step>, p: Seq<Step>)
    requires
        typed_by(stab, m),
        typed_by(stab, p),
        no_seg(m),
        no_seg(p),
    ensures
        alias_exact(m, p),
{
    assert forall|i: int|
        0 <= i < m.len() && i < p.len() && m.subrange(0, i) == p.subrange(0, i)
            && #[trigger] spec_step_alias(m[i], p[i]) implies m[i] == p[i] by {
        assert(!(m[i].kind is Seg));
        assert(!(p[i].kind is Seg));
        assert(m[i].kind == p[i].kind);
        assert(m[i].unstable == stab(m.subrange(0, i), m[i].kind));
        assert(p[i].unstable == stab(p.subrange(0, i), p[i].kind));
    }
}

/// **Exactness for typed places.** The corollary of the two results above.
pub proof fn thm_invalidates_exact_typed(
    stab: spec_fn(Seq<Step>, StepKind) -> bool,
    rm: Local,
    m: Seq<Step>,
    rp: Local,
    p: Seq<Step>,
)
    requires
        typed_by(stab, m),
        typed_by(stab, p),
        no_seg(m),
        no_seg(p),
    ensures
        (rm == rp && spec_invalidates(m, p)) == lkills(lplace(rm, m), lplace(rp, p)),
{
    lemma_typed_alias_exact(stab, m, p);
    thm_invalidates_exact(rm, m, rp, p);
}

// ---------------------------------------------------------------------------
// The exec function
// ---------------------------------------------------------------------------

/// The place comparison of the checker (`Ctx::invalidates` in
/// `crates/weft-check/src/rules.rs`): the same root, then the verified
/// `invalidates`. The proof uses only the postcondition of `invalidates`.
pub fn invalidates_in_model(rm: u32, m: &[Step], rp: u32, p: &[Step]) -> (r: bool)
    ensures
        r == (rm == rp && spec_invalidates(m@, p@)),
        lkills(lplace(rm as nat, m@), lplace(rp as nat, p@)) ==> r,
        alias_exact(m@, p@) ==> (r == lkills(lplace(rm as nat, m@), lplace(rp as nat, p@))),
{
    let r = rm == rp && invalidates(m, p);
    proof {
        thm_lkills_implies_invalidates(rm as nat, m@, rp as nat, p@);
        if alias_exact(m@, p@) {
            thm_invalidates_exact(rm as nat, m@, rp as nat, p@);
        }
    }
    r
}

} // verus!
