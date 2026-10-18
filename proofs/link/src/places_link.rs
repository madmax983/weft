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
//! * `thm_split_sound` and `thm_split_exact`: for split places, rule 3 is the
//!   model kill predicate on the coarse places (each split side read as the
//!   elements step), minus the pairs with the two sides of one split.
//! * `thm_rule3_layout_sound`: the B3 checker with rule 3 as its kill rule
//!   accepts less than the B3 checker. Thus, by `layout_soundness`, no run of
//!   a program that it accepts has UB.
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
use crate::layout::{
    PStep, LPlace, LSState, LInstr, Schema, LState, flat, flat_hops, lkills, unstable, lpost, lss_at, lcheck,
    linstr_ok, lkilled, lsurvivors, is_ltrace, lub, linitial, wf_schema, lwf,
};
use crate::layout_proof::{linv, layout_soundness, layout_soundness_from_start, lemma_flat_hops_push};
use crate::model::{Local, Var};

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
// Split steps
// ---------------------------------------------------------------------------
//
// The B3 model has no split steps. A split side `[..k]` or `[k..]` names a
// part of the elements at the same position (`spec_step_within`). Thus the
// model sees a split side as the elements step: `coarse` replaces each split
// side with an `Elem` step of the same stability. The model cannot express
// that the two sides of one split are disjoint. Rule 3 adds exactly this
// fact (`opposite_sides`). The theorems below fix the alias table of split
// steps: `Elem` aliases each side, sides of different splits alias, and only
// the two sides of one split do not alias.

/// The step, with a split side replaced by the elements step. The stability
/// does not change.
pub open spec fn coarse_step(s: Step) -> Step {
    match s.kind {
        StepKind::Seg { .. } => Step { kind: StepKind::Elem, unstable: s.unstable },
        _ => s,
    }
}

/// The path, with each split side replaced by the elements step.
pub open spec fn coarse(p: Seq<Step>) -> Seq<Step> {
    p.map_values(|s: Step| coarse_step(s))
}

/// The two steps are the two sides of one split. They name disjoint memory.
pub open spec fn opposite_sides(a: Step, b: Step) -> bool {
    match (a.kind, b.kind) {
        (StepKind::Seg { split: s1, hi: h1 }, StepKind::Seg { split: s2, hi: h2 }) => s1 == s2 && h1 != h2,
        _ => false,
    }
}

/// No position before the end of `m` has the two sides of one split.
pub open spec fn no_opposite(m: Seq<Step>, p: Seq<Step>) -> bool {
    forall|i: int|
        #![trigger m[i]]
        #![trigger p[i]]
        0 <= i < m.len() && i < p.len() ==> !opposite_sides(m[i], p[i])
}

/// The alias table of one step pair, against the model view. If the model
/// views of two steps are equal and the steps are not the two sides of one
/// split, the steps can alias. Two steps that can alias are not the two
/// sides of one split, and their model views can alias. Each step aliases
/// itself.
pub proof fn lemma_coarse_step_alias(a: Step, b: Step)
    ensures
        coarse_step(a) == coarse_step(b) && !opposite_sides(a, b) ==> spec_step_alias(a, b),
        spec_step_alias(a, b) ==> !opposite_sides(a, b),
        spec_step_alias(a, b) ==> spec_step_alias(coarse_step(a), coarse_step(b)),
        coarse_step(a).unstable == a.unstable,
        !(coarse_step(a).kind is Seg),
        spec_step_alias(a, a),
{
}

/// The coarse path has the same length, no split step, and the coarse steps.
pub proof fn lemma_coarse(p: Seq<Step>)
    ensures
        coarse(p).len() == p.len(),
        no_seg(coarse(p)),
        forall|i: int| 0 <= i < p.len() ==> #[trigger] coarse(p)[i] == coarse_step(p[i]),
{
    assert forall|i: int| 0 <= i < coarse(p).len() implies !(#[trigger] coarse(p)[i].kind is Seg) by {
        lemma_coarse_step_alias(p[i], p[i]);
    }
}

/// The model kill predicate gives equal steps on the prefix: the embedding
/// is injective.
pub proof fn lemma_lkills_prefix(rm: Local, m: Seq<Step>, rp: Local, p: Seq<Step>)
    requires
        lkills(lplace(rm, m), lplace(rp, p)),
    ensures
        rm == rp,
        m.len() < p.len(),
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i] == p[i],
        spec_crosses_unstable(m.len() as int, p),
{
    lemma_flat_lplace(rm, m);
    lemma_flat_lplace(rp, p);
    let fm = emb_path(m);
    let fp = emb_path(p);
    assert(fm.is_prefix_of(fp));
    assert forall|i: int| 0 <= i < m.len() implies #[trigger] m[i] == p[i] by {
        assert(fm[i] == fp[i]);
        lemma_emb_step_injective(m[i], p[i]);
    }
    let j = choose|j: int| fm.len() <= j < fp.len() && #[trigger] unstable(fp[j]);
    lemma_emb_step_unstable(p[j]);
    assert(p[j].unstable);
}

/// **Split places, soundness direction, for all places.** If the model kills
/// the coarse reference after a mutation of the coarse place, and no
/// position has the two sides of one split, then rule 3 invalidates the
/// reference. For example, `mut(v[])` kills a reference into `v[..k]`, and
/// `mut(v[..i])` kills a reference into `v[j..]` of another split.
pub proof fn thm_split_sound(rm: Local, m: Seq<Step>, rp: Local, p: Seq<Step>)
    ensures
        lkills(lplace(rm, coarse(m)), lplace(rp, coarse(p))) && no_opposite(m, p) ==> rm == rp && spec_invalidates(
            m,
            p,
        ),
{
    if lkills(lplace(rm, coarse(m)), lplace(rp, coarse(p))) && no_opposite(m, p) {
        lemma_coarse(m);
        lemma_coarse(p);
        lemma_lkills_prefix(rm, coarse(m), rp, coarse(p));
        assert forall|i: int|
            #![trigger m[i]]
            #![trigger p[i]]
            0 <= i < m.len() implies spec_step_alias(m[i], p[i]) by {
            assert(coarse(m)[i] == coarse(p)[i]);
            lemma_coarse_step_alias(m[i], p[i]);
        }
        let j = choose|j: int| m.len() <= j < p.len() && #[trigger] coarse(p)[j].unstable;
        lemma_coarse_step_alias(p[j], p[j]);
        assert(p[j].unstable);
    }
}

/// Rule 3 on the places implies rule 3 on the coarse places, and no
/// position has the two sides of one split.
pub proof fn lemma_invalidates_coarse(m: Seq<Step>, p: Seq<Step>)
    requires
        spec_invalidates(m, p),
    ensures
        spec_invalidates(coarse(m), coarse(p)),
        no_opposite(m, p),
{
    lemma_coarse(m);
    lemma_coarse(p);
    let cm = coarse(m);
    let cp = coarse(p);
    assert forall|i: int|
        #![trigger cm[i]]
        #![trigger cp[i]]
        0 <= i < cm.len() implies spec_step_alias(cm[i], cp[i]) by {
        assert(spec_step_alias(m[i], p[i]));
        lemma_coarse_step_alias(m[i], p[i]);
    }
    assert forall|i: int|
        #![trigger m[i]]
        #![trigger p[i]]
        0 <= i < m.len() && i < p.len() implies !opposite_sides(m[i], p[i]) by {
        assert(spec_step_alias(m[i], p[i]));
        lemma_coarse_step_alias(m[i], p[i]);
    }
    let k = choose|k: int| m.len() <= k < p.len() && #[trigger] p[k].unstable;
    lemma_coarse_step_alias(p[k], p[k]);
    assert(cp[k].unstable);
}

/// **Split places, exactness.** If the coarse places have no false alias,
/// then rule 3 is exactly the model kill predicate on the coarse places,
/// minus the pairs with the two sides of one split.
pub proof fn thm_split_exact(rm: Local, m: Seq<Step>, rp: Local, p: Seq<Step>)
    requires
        alias_exact(coarse(m), coarse(p)),
    ensures
        (rm == rp && spec_invalidates(m, p)) == (lkills(lplace(rm, coarse(m)), lplace(rp, coarse(p))) && no_opposite(
            m,
            p,
        )),
{
    thm_split_sound(rm, m, rp, p);
    if rm == rp && spec_invalidates(m, p) {
        lemma_invalidates_coarse(m, p);
        thm_invalidates_exact(rm, coarse(m), rp, coarse(p));
    }
}

/// **Split places, typed.** Sema gives a split side the stability of the
/// elements step of its type. If the coarse places are typed by one
/// stability function, the exactness above holds.
pub proof fn thm_split_exact_typed(
    stab: spec_fn(Seq<Step>, StepKind) -> bool,
    rm: Local,
    m: Seq<Step>,
    rp: Local,
    p: Seq<Step>,
)
    requires
        typed_by(stab, coarse(m)),
        typed_by(stab, coarse(p)),
    ensures
        (rm == rp && spec_invalidates(m, p)) == (lkills(lplace(rm, coarse(m)), lplace(rp, coarse(p))) && no_opposite(
            m,
            p,
        )),
{
    lemma_coarse(m);
    lemma_coarse(p);
    lemma_typed_alias_exact(stab, coarse(m), coarse(p));
    thm_split_exact(rm, m, rp, p);
}

// ---------------------------------------------------------------------------
// Rule 3 as the kill rule of the B3 checker
// ---------------------------------------------------------------------------
//
// The theorems above compare two predicates. This section puts rule 3 into
// the B3 checker in place of `lkills`, and gets the B3 soundness theorem for
// that checker. The checker reads a model place as an exec place through a
// decoding `d` of steps. Each decoding that keeps the stability works: a
// `Field` step becomes a stable step, a `Variant` or `Kid` step becomes an
// unstable step.

/// The decoding `d` keeps the stability of each model step.
pub open spec fn keeps_stab(d: spec_fn(PStep) -> Step) -> bool {
    forall|st: PStep| #[trigger] d(st).unstable == unstable(st)
}

/// A decoding that keeps the stability: a field, a variant, or the elements.
pub open spec fn dec_canonical() -> spec_fn(PStep) -> Step {
    |st: PStep|
        match st {
            PStep::Field(f) => Step { kind: StepKind::Field { id: f as u32 }, unstable: false },
            PStep::Variant(v) => Step { kind: StepKind::Variant { id: v as u32 }, unstable: true },
            PStep::Kid(l) => Step { kind: StepKind::Elem, unstable: true },
        }
}

/// The canonical decoding keeps the stability.
pub proof fn lemma_dec_canonical()
    ensures
        keeps_stab(dec_canonical()),
{
}

/// The exec path of a model path, through the decoding `d`.
pub open spec fn dpath(d: spec_fn(PStep) -> Step, ps: Seq<PStep>) -> Seq<Step> {
    ps.map_values(|st: PStep| d(st))
}

/// Rule 3 on two model places, through the decoding `d`.
pub open spec fn rkills(d: spec_fn(PStep) -> Step, p: LPlace, q: LPlace) -> bool {
    p.root == q.root && spec_invalidates(dpath(d, flat(p)), dpath(d, flat(q)))
}

/// A call with the arguments `args` kills the reference at `q` by rule 3.
pub open spec fn rkilled(d: spec_fn(PStep) -> Step, ss: LSState, args: Seq<(Var, bool)>, q: LPlace) -> bool {
    exists|k: int| 0 <= k < args.len() && args[k].1 && #[trigger] rkills(d, ss.vars[args[k].0], q)
}

/// The references that survive a call by rule 3.
pub open spec fn rsurvivors(d: spec_fn(PStep) -> Step, ss: LSState, args: Seq<(Var, bool)>) -> Map<Var, LPlace> {
    Map::new(ss.vars.dom().filter(|v: Var| !rkilled(d, ss, args, ss.vars[v])), |v: Var| ss.vars[v])
}

/// The checker state after `i`, with rule 3 as the kill rule.
pub open spec fn rpost(d: spec_fn(PStep) -> Step, ss: LSState, i: LInstr) -> LSState {
    match i {
        LInstr::Call { args } => LSState { vars: rsurvivors(d, ss, args), ..ss },
        _ => lpost(ss, i),
    }
}

/// The checker state before instruction `k`, with rule 3 as the kill rule.
pub open spec fn rss_at(d: spec_fn(PStep) -> Step, ss0: LSState, prog: Seq<LInstr>, k: nat) -> LSState
    decreases k,
{
    if k == 0 {
        ss0
    } else {
        rpost(d, rss_at(d, ss0, prog, (k - 1) as nat), prog[k - 1])
    }
}

/// The B3 checker with rule 3 as the kill rule accepts each instruction.
pub open spec fn rcheck(d: spec_fn(PStep) -> Step, sc: Schema, ss0: LSState, prog: Seq<LInstr>) -> bool {
    forall|k: nat| k < prog.len() ==> #[trigger] linstr_ok(sc, rss_at(d, ss0, prog, k), prog[k as int])
}

/// The checker state `a` has the locals and types of `b`, and a part of its references.
pub open spec fn sub_lss(a: LSState, b: LSState) -> bool {
    &&& a.locals == b.locals
    &&& a.lty == b.lty
    &&& a.vars.submap_of(b.vars)
}

/// Rule 3 kills at least what `lkills` kills, through each decoding that
/// keeps the stability.
pub proof fn lemma_lkills_rkills(d: spec_fn(PStep) -> Step, p: LPlace, q: LPlace)
    requires
        keeps_stab(d),
        lkills(p, q),
    ensures
        rkills(d, p, q),
{
    let fp = flat(p);
    let fq = flat(q);
    let dp = dpath(d, fp);
    let dq = dpath(d, fq);
    assert(fp.is_prefix_of(fq));
    assert forall|i: int|
        #![trigger dp[i]]
        #![trigger dq[i]]
        0 <= i < dp.len() implies spec_step_alias(dp[i], dq[i]) by {
        assert(fq.subrange(0, fp.len() as int)[i] == fq[i]);
        assert(fp[i] == fq[i]);
        lemma_coarse_step_alias(dp[i], dp[i]);
    }
    let j = choose|j: int| fp.len() <= j < fq.len() && #[trigger] unstable(fq[j]);
    assert(d(fq[j]).unstable);
    assert(dq[j].unstable);
}

/// A reference of the part has the same place in the whole.
pub proof fn lemma_sub_get(a: Map<Var, LPlace>, b: Map<Var, LPlace>, v: Var)
    requires
        a.submap_of(b),
        a.contains_key(v),
    ensures
        b.contains_key(v),
        b[v] == a[v],
{
    assert(b.dom().contains(v));
    assert(a[v] == b[v]);
}

/// The checker accepts more in a state with more references.
pub proof fn lemma_linstr_ok_mono(sc: Schema, a: LSState, b: LSState, i: LInstr)
    requires
        sub_lss(a, b),
        linstr_ok(sc, a, i),
    ensures
        linstr_ok(sc, b, i),
{
    match i {
        LInstr::Field { src, .. } => {
            lemma_sub_get(a.vars, b.vars, src);
        },
        LInstr::Variant { src, .. } => {
            lemma_sub_get(a.vars, b.vars, src);
        },
        LInstr::Child { src, .. } => {
            lemma_sub_get(a.vars, b.vars, src);
        },
        LInstr::Read { src, .. } => {
            lemma_sub_get(a.vars, b.vars, src);
        },
        LInstr::Write { src, .. } => {
            lemma_sub_get(a.vars, b.vars, src);
        },
        LInstr::Call { args } => {
            assert forall|k: int| 0 <= k < args.len() implies b.vars.contains_key(#[trigger] args[k].0) by {
                lemma_sub_get(a.vars, b.vars, args[k].0);
            }
        },
        _ => {},
    }
}

/// One step keeps `sub_lss`: the rule-3 state stays a part of the B3 state.
pub proof fn lemma_rpost_mono(d: spec_fn(PStep) -> Step, sc: Schema, a: LSState, b: LSState, i: LInstr)
    requires
        keeps_stab(d),
        sub_lss(a, b),
        linstr_ok(sc, a, i),
    ensures
        sub_lss(rpost(d, a, i), lpost(b, i)),
{
    let ra = rpost(d, a, i);
    let lb = lpost(b, i);
    match i {
        LInstr::Call { args } => {
            assert forall|v: Var| #[trigger] ra.vars.dom().contains(v) implies lb.vars.dom().contains(v)
                && ra.vars[v] == lb.vars[v] by {
                assert(a.vars.contains_key(v));
                assert(!rkilled(d, a, args, a.vars[v]));
                lemma_sub_get(a.vars, b.vars, v);
                if lkilled(b, args, b.vars[v]) {
                    let k = choose|k: int|
                        0 <= k < args.len() && args[k].1 && #[trigger] lkills(b.vars[args[k].0], b.vars[v]);
                    assert(a.vars.contains_key(args[k].0));
                    lemma_sub_get(a.vars, b.vars, args[k].0);
                    lemma_lkills_rkills(d, a.vars[args[k].0], a.vars[v]);
                    assert(rkilled(d, a, args, a.vars[v]));
                }
            }
        },
        LInstr::Copy { dst, src } => {
            assert forall|v: Var| #[trigger] ra.vars.dom().contains(v) implies lb.vars.dom().contains(v)
                && ra.vars[v] == lb.vars[v] by {
                if v != dst {
                    assert(a.vars.contains_key(v));
                    lemma_sub_get(a.vars, b.vars, v);
                }
                if a.vars.contains_key(src) {
                    lemma_sub_get(a.vars, b.vars, src);
                }
            }
        },
        LInstr::Borrow { dst, .. } => {
            assert forall|v: Var| #[trigger] ra.vars.dom().contains(v) implies lb.vars.dom().contains(v)
                && ra.vars[v] == lb.vars[v] by {
                if v != dst {
                    assert(a.vars.contains_key(v));
                    lemma_sub_get(a.vars, b.vars, v);
                }
            }
        },
        LInstr::Field { dst, src, .. } => {
            lemma_sub_get(a.vars, b.vars, src);
            assert forall|v: Var| #[trigger] ra.vars.dom().contains(v) implies lb.vars.dom().contains(v)
                && ra.vars[v] == lb.vars[v] by {
                if v != dst {
                    assert(a.vars.contains_key(v));
                    lemma_sub_get(a.vars, b.vars, v);
                }
            }
        },
        LInstr::Variant { dst, src, .. } => {
            lemma_sub_get(a.vars, b.vars, src);
            assert forall|v: Var| #[trigger] ra.vars.dom().contains(v) implies lb.vars.dom().contains(v)
                && ra.vars[v] == lb.vars[v] by {
                if v != dst {
                    assert(a.vars.contains_key(v));
                    lemma_sub_get(a.vars, b.vars, v);
                }
            }
        },
        LInstr::Child { dst, src, .. } => {
            lemma_sub_get(a.vars, b.vars, src);
            assert forall|v: Var| #[trigger] ra.vars.dom().contains(v) implies lb.vars.dom().contains(v)
                && ra.vars[v] == lb.vars[v] by {
                if v != dst {
                    assert(a.vars.contains_key(v));
                    lemma_sub_get(a.vars, b.vars, v);
                }
            }
        },
        _ => {},
    }
}

/// Along the program, the rule-3 checker state is a part of the B3 state.
pub proof fn lemma_rss_sub(d: spec_fn(PStep) -> Step, sc: Schema, ss0: LSState, prog: Seq<LInstr>, k: nat)
    requires
        keeps_stab(d),
        rcheck(d, sc, ss0, prog),
        k <= prog.len(),
    ensures
        sub_lss(rss_at(d, ss0, prog, k), lss_at(ss0, prog, k)),
    decreases k,
{
    if k == 0 {
        assert(ss0.vars.submap_of(ss0.vars));
    } else {
        let km = (k - 1) as nat;
        lemma_rss_sub(d, sc, ss0, prog, km);
        assert(linstr_ok(sc, rss_at(d, ss0, prog, km), prog[km as int]));
        lemma_rpost_mono(d, sc, rss_at(d, ss0, prog, km), lss_at(ss0, prog, km), prog[km as int]);
    }
}

/// **The rule-3 checker accepts less than the B3 checker.** If the B3
/// checker with rule 3 as the kill rule accepts a program, the B3 checker
/// accepts it.
pub proof fn thm_rcheck_lcheck(d: spec_fn(PStep) -> Step, sc: Schema, ss0: LSState, prog: Seq<LInstr>)
    requires
        keeps_stab(d),
        rcheck(d, sc, ss0, prog),
    ensures
        lcheck(sc, ss0, prog),
{
    assert forall|k: nat| k < prog.len() implies #[trigger] linstr_ok(sc, lss_at(ss0, prog, k), prog[k as int]) by {
        lemma_rss_sub(d, sc, ss0, prog, k);
        lemma_linstr_ok_mono(sc, rss_at(d, ss0, prog, k), lss_at(ss0, prog, k), prog[k as int]);
    }
}

/// **Rule 3 is a sound kill rule for B3.** If the B3 checker with rule 3
/// as the kill rule accepts a program, then no run of it has UB: no use
/// after free, no type confusion, and no access outside the layout of a
/// type (by `layout_soundness`).
pub proof fn thm_rule3_layout_sound(
    d: spec_fn(PStep) -> Step,
    sc: Schema,
    ss0: LSState,
    prog: Seq<LInstr>,
    trace: Seq<LState>,
)
    requires
        keeps_stab(d),
        linv(sc, trace[0], ss0),
        rcheck(d, sc, ss0, prog),
        is_ltrace(sc, prog, trace),
    ensures
        forall|k: int| 0 <= k < trace.len() && k < prog.len() ==> !#[trigger] lub(sc, trace[k], prog[k]),
{
    thm_rcheck_lcheck(d, sc, ss0, prog);
    layout_soundness(sc, ss0, prog, trace);
}

/// The same from a fresh start: a consistent schema, a well-formed heap,
/// and no references yet.
pub proof fn thm_rule3_layout_sound_from_start(
    d: spec_fn(PStep) -> Step,
    sc: Schema,
    prog: Seq<LInstr>,
    trace: Seq<LState>,
)
    requires
        keeps_stab(d),
        wf_schema(sc),
        lwf(sc, trace[0]),
        rcheck(d, sc, linitial(trace[0]), prog),
        is_ltrace(sc, prog, trace),
    ensures
        forall|k: int| 0 <= k < trace.len() && k < prog.len() ==> !#[trigger] lub(sc, trace[k], prog[k]),
{
    thm_rcheck_lcheck(d, sc, linitial(trace[0]), prog);
    layout_soundness_from_start(sc, prog, trace);
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
        lkills(lplace(rm as nat, coarse(m@)), lplace(rp as nat, coarse(p@))) && no_opposite(m@, p@) ==> r,
        alias_exact(coarse(m@), coarse(p@)) ==> (r == (lkills(lplace(rm as nat, coarse(m@)), lplace(rp as nat, coarse(p@)))
            && no_opposite(m@, p@))),
{
    let r = rm == rp && invalidates(m, p);
    proof {
        thm_lkills_implies_invalidates(rm as nat, m@, rp as nat, p@);
        if alias_exact(m@, p@) {
            thm_invalidates_exact(rm as nat, m@, rp as nat, p@);
        }
        thm_split_sound(rm as nat, m@, rp as nat, p@);
        if alias_exact(coarse(m@), coarse(p@)) {
            thm_split_exact(rm as nat, m@, rp as nat, p@);
        }
    }
    r
}

} // verus!
