//! B3 sanity checks, on one schema:
//!
//! ```text
//! struct World { score: int, players: List<Elem>, items: List<Elem>, state: State }
//! enum State { Pair(int, int), Idle(int) }        // inline: tag slot + payload
//! ```
//!
//! * Field-sensitive footprint: `shuffle(mut w.players)` keeps `&w.items[i]`
//!   valid and kills `&w.players[j]`. A concrete run frees the player.
//! * Inline enum: `set_state(mut w.state)` kills a reference into the `Pair`
//!   payload. A concrete run switches the variant: a type confusion.
//! * Type stability: `update(mut w)` keeps `&w.score` and `&w.state`.
//! * Out of bounds: a read of field 9 of `World` is rejected, and it is UB.
//! * The hypotheses of `layout_soundness_from_start` are satisfiable.

#![allow(non_snake_case)]

use vstd::prelude::*;
use crate::model::*;
use crate::soundness::*;
use crate::layout::*;
use crate::layout_proof::*;

verus! {

// ---------------------------------------------------------------------------
// The schema
// ---------------------------------------------------------------------------

/// The type of a primitive.
pub open spec fn PRIM() -> Ty { 0 }
/// The type `(int, int)`.
pub open spec fn PAIR() -> Ty { 1 }
/// The inline enum `State { Pair(int, int), Idle(int) }`.
pub open spec fn STATE() -> Ty { 2 }
/// The type of a list element.
pub open spec fn ELEM() -> Ty { 3 }
/// The type of an inline list header.
pub open spec fn LIST() -> Ty { 4 }
/// The type `World`.
pub open spec fn WORLD() -> Ty { 5 }

/// The child group of the players (owned under `World.players`).
pub open spec fn PLAYERS() -> Label { 0 }
/// The child group of the items (owned under `World.items`).
pub open spec fn ITEMS() -> Label { 1 }

/// The local `w`.
pub open spec fn W() -> Local { 0 }

/// The reference variable `rw`.
pub open spec fn RW() -> Var { 0 }
/// The reference variable `rp`.
pub open spec fn RP() -> Var { 1 }
/// The reference variable `ri`.
pub open spec fn RI() -> Var { 2 }
/// The reference variable `it`.
pub open spec fn IT() -> Var { 3 }
/// The reference variable `pl`.
pub open spec fn PL() -> Var { 4 }
/// The reference variable `rs`.
pub open spec fn RS() -> Var { 5 }
/// The reference variable `pa`.
pub open spec fn PA() -> Var { 6 }
/// The reference variable `sc`.
pub open spec fn SC() -> Var { 7 }

/// A field step.
pub open spec fn Fd(i: nat) -> PStep {
    PStep::Field(i)
}

/// A variant step.
pub open spec fn Vr(i: nat) -> PStep {
    PStep::Variant(i)
}

/// No child groups.
pub open spec fn no_kids() -> Map<Label, (Seq<PStep>, Ty)> {
    Map::empty()
}

/// The layout of a primitive.
pub open spec fn prim_def() -> TyDef {
    TyDef { size: 1, shape: Shape::Prim, kids: no_kids() }
}

/// The layout of `(int, int)`.
pub open spec fn pair_def() -> TyDef {
    TyDef { size: 2, shape: Shape::Struct { fields: seq![(0nat, PRIM()), (1nat, PRIM())] }, kids: no_kids() }
}

/// The layout of `State`: a tag slot and a payload of two slots.
pub open spec fn state_def() -> TyDef {
    TyDef { size: 3, shape: Shape::Enum { variants: seq![PAIR(), PRIM()] }, kids: no_kids() }
}

/// The layout of a list element or a list header.
pub open spec fn elem_def() -> TyDef {
    TyDef { size: 1, shape: Shape::Struct { fields: seq![(0nat, PRIM())] }, kids: no_kids() }
}

/// The fields of `World`: `score`, `players`, `items`, `state`.
pub open spec fn world_fields() -> Seq<(nat, Ty)> {
    seq![(0nat, PRIM()), (1nat, LIST()), (2nat, LIST()), (3nat, STATE())]
}

/// The child groups of `World`.
pub open spec fn world_kids() -> Map<Label, (Seq<PStep>, Ty)> {
    map![PLAYERS() => (seq![Fd(1)], ELEM()), ITEMS() => (seq![Fd(2)], ELEM())]
}

/// The layout of `World`.
pub open spec fn world_def() -> TyDef {
    TyDef { size: 6, shape: Shape::Struct { fields: world_fields() }, kids: world_kids() }
}

/// The schema of the examples.
pub open spec fn wsc() -> Schema {
    map![
        PRIM() => prim_def(),
        PAIR() => pair_def(),
        STATE() => state_def(),
        ELEM() => elem_def(),
        LIST() => elem_def(),
        WORLD() => world_def()
    ]
}

/// The schema is consistent.
pub proof fn lemma_wsc_ok()
    ensures
        wf_schema(wsc()),
{
    let sc = wsc();
    assert(sc.dom() =~= set![0nat, 1, 2, 3, 4, 5]);
    assert forall|t: Ty| #[trigger] sc.contains_key(t) implies ty_ok(sc, t) by {
        if t == PAIR() {
            let fs = seq![(0nat, PRIM()), (1nat, PRIM())];
            assert forall|f: int, g: int| 0 <= f < fs.len() && 0 <= g < fs.len() && f != g implies #[trigger] fs[f].0
                + sc[fs[f].1].size <= #[trigger] fs[g].0 || fs[g].0 + sc[fs[g].1].size <= fs[f].0 by {}
        } else if t == WORLD() {
            let fs = world_fields();
            assert forall|f: int| 0 <= f < fs.len() implies sc.contains_key(#[trigger] fs[f].1) && fs[f].0
                + sc[fs[f].1].size <= sc[t].size by {}
            assert forall|f: int, g: int| 0 <= f < fs.len() && 0 <= g < fs.len() && f != g implies #[trigger] fs[f].0
                + sc[fs[f].1].size <= #[trigger] fs[g].0 || fs[g].0 + sc[fs[g].1].size <= fs[f].0 by {}
            assert forall|l: Label| #[trigger] world_kids().contains_key(l) implies sc.contains_key(world_kids()[l].1) by {}
        } else if t == STATE() {
            let vs = seq![PAIR(), PRIM()];
            assert forall|v: int| 0 <= v < vs.len() implies sc.contains_key(#[trigger] vs[v]) && 1 + sc[vs[v]].size
                <= sc[t].size by {}
        } else if t == ELEM() || t == LIST() {
            let fs = seq![(0nat, PRIM())];
            assert forall|f: int, g: int| 0 <= f < fs.len() && 0 <= g < fs.len() && f != g implies #[trigger] fs[f].0
                + sc[fs[f].1].size <= #[trigger] fs[g].0 || fs[g].0 + sc[fs[g].1].size <= fs[f].0 by {}
        }
    }
}

// ---------------------------------------------------------------------------
// Places and the kill rule
// ---------------------------------------------------------------------------

/// The place `w.tail`.
pub open spec fn at(tail: Seq<PStep>) -> LPlace {
    LPlace { root: W(), hops: Seq::empty(), tail }
}

/// The place `w.seg.Kid(l)`.
pub open spec fn kid_of(seg: Seq<PStep>, l: Label) -> LPlace {
    LPlace { root: W(), hops: seq![(seg, l)], tail: Seq::empty() }
}

proof fn lemma_flat_at(tail: Seq<PStep>)
    ensures
        flat(at(tail)) == tail,
{
    assert(flat(at(tail)) =~= tail);
}

proof fn lemma_flat_kid(seg: Seq<PStep>, l: Label)
    ensures
        flat(kid_of(seg, l)) == seg + seq![PStep::Kid(l)],
{
    let hops = seq![(seg, l)];
    assert(hops.drop_last() =~= Seq::<(Seq<PStep>, Label)>::empty());
    assert(flat_hops(Seq::<(Seq<PStep>, Label)>::empty()) == Seq::<PStep>::empty());
    assert(hops.last() == (seg, l));
    assert(flat_hops(hops) =~= seg + seq![PStep::Kid(l)]);
    assert(flat(kid_of(seg, l)) =~= seg + seq![PStep::Kid(l)]);
}

/// The kill rule on the places of the examples.
proof fn lemma_kills_facts()
    ensures
        // mut(w.players) kills w.players.Kid(players), and keeps the rest
        lkills(at(seq![Fd(1)]), kid_of(seq![Fd(1)], PLAYERS())),
        !lkills(at(seq![Fd(1)]), kid_of(seq![Fd(2)], ITEMS())),
        !lkills(at(seq![Fd(1)]), at(seq![])),
        !lkills(at(seq![Fd(1)]), at(seq![Fd(1)])),
        !lkills(at(seq![Fd(1)]), at(seq![Fd(2)])),
        // mut(w.state) kills w.state.Variant(0), and keeps the rest
        lkills(at(seq![Fd(3)]), at(seq![Fd(3), Vr(0)])),
        !lkills(at(seq![Fd(3)]), at(seq![])),
        !lkills(at(seq![Fd(3)]), at(seq![Fd(3)])),
        // mut(w) keeps references into stable parts of w
        !lkills(at(seq![]), at(seq![])),
        !lkills(at(seq![]), at(seq![Fd(0)])),
        !lkills(at(seq![]), at(seq![Fd(3)])),
{
    lemma_flat_at(seq![Fd(1)]);
    lemma_flat_at(seq![Fd(2)]);
    lemma_flat_at(seq![Fd(3)]);
    lemma_flat_at(seq![Fd(0)]);
    lemma_flat_at(seq![Fd(3), Vr(0)]);
    lemma_flat_at(seq![]);
    lemma_flat_kid(seq![Fd(1)], PLAYERS());
    lemma_flat_kid(seq![Fd(2)], ITEMS());
    let fp = seq![Fd(1)] + seq![PStep::Kid(PLAYERS())];
    assert(fp =~= seq![Fd(1), PStep::Kid(PLAYERS())]);
    assert(seq![Fd(1)] =~= fp.subrange(0, 1));
    assert(unstable(fp[1]));
    let fi = seq![Fd(2)] + seq![PStep::Kid(ITEMS())];
    assert(fi[0] == Fd(2));
    assert(fi.subrange(0, 1)[0] == Fd(2));
    assert(seq![Fd(2)].subrange(0, 1)[0] == Fd(2));
    assert(seq![Fd(1)] =~= seq![Fd(1)].subrange(0, 1));
    assert(seq![Fd(3)] =~= seq![Fd(3), Vr(0)].subrange(0, 1));
    assert(unstable(seq![Fd(3), Vr(0)][1]));
    assert(seq![Fd(3)] =~= seq![Fd(3)].subrange(0, 1));
    assert(Seq::<PStep>::empty() =~= seq![Fd(0)].subrange(0, 0));
    assert(Seq::<PStep>::empty() =~= seq![Fd(3)].subrange(0, 0));
    assert(!unstable(seq![Fd(0)][0]));
    assert(!unstable(seq![Fd(3)][0]));
}

// ---------------------------------------------------------------------------
// Programs and the checker
// ---------------------------------------------------------------------------

/// The checker state at the start: the local `w` of type `World`.
pub open spec fn lss0() -> LSState {
    LSState { locals: set![W()], lty: map![W() => WORLD()], vars: Map::empty() }
}

/// A checker state with the variables `vars`.
pub open spec fn lsv(vars: Map<Var, LPlace>) -> LSState {
    LSState { vars, ..lss0() }
}

proof fn lemma_alloc_kid(seg: Seq<PStep>, l: Label)
    requires
        world_kids().contains_key(l),
        world_kids()[l].0 == seg,
    ensures
        alloc_ty(wsc(), WORLD(), seq![(seg, l)]) == Some(world_kids()[l].1),
{
    let hops = seq![(seg, l)];
    assert(hops.drop_last() =~= Seq::<(Seq<PStep>, Label)>::empty());
    assert(alloc_ty(wsc(), WORLD(), hops.drop_last()) == Some(WORLD()));
    assert(hops.last() == (seg, l));
}

proof fn lemma_types()
    ensures
        place_ty(wsc(), lss0(), at(seq![])) == Some(WORLD()),
        place_ty(wsc(), lss0(), at(seq![Fd(0)])) == Some(PRIM()),
        place_ty(wsc(), lss0(), at(seq![Fd(3)])) == Some(STATE()),
        place_alloc_ty(wsc(), lss0(), at(seq![Fd(1)])) == Some(WORLD()),
        place_alloc_ty(wsc(), lss0(), at(seq![Fd(2)])) == Some(WORLD()),
        place_ty(wsc(), lss0(), kid_of(seq![Fd(2)], ITEMS())) == Some(ELEM()),
        sview(wsc(), ELEM(), seq![Fd(0)]) == Some(PRIM()),
        sview(wsc(), WORLD(), seq![Fd(0)]) == Some(PRIM()),
        sview(wsc(), PRIM(), seq![]) == Some(PRIM()),
        sview(wsc(), WORLD(), seq![Fd(9)]) is None,
        sstep(wsc(), WORLD(), Fd(1)) is Some,
        sstep(wsc(), WORLD(), Fd(2)) is Some,
        sstep(wsc(), WORLD(), Fd(0)) is Some,
        sstep(wsc(), WORLD(), Fd(3)) is Some,
        sstep(wsc(), STATE(), Vr(0)) is Some,
        field_only(seq![Fd(0)]),
        field_only(Seq::<PStep>::empty()),
{
    let sc = wsc();
    assert(alloc_ty(sc, WORLD(), Seq::empty()) == Some(WORLD()));
    assert(seq![Fd(0)].drop_first() =~= Seq::<PStep>::empty());
    assert(seq![Fd(3)].drop_first() =~= Seq::<PStep>::empty());
    assert(seq![Fd(9)][0] == Fd(9));
    lemma_alloc_kid(seq![Fd(2)], ITEMS());
    assert(place_ty(sc, lss0(), at(seq![Fd(0)])) == sview(sc, WORLD(), seq![Fd(0)]));
    assert(sstep(sc, WORLD(), Fd(0)) == Some(PRIM()));
    assert(sstep(sc, WORLD(), Fd(3)) == Some(STATE()));
    assert(sstep(sc, ELEM(), Fd(0)) == Some(PRIM()));
    assert(place_ty(sc, lss0(), at(seq![Fd(3)])) == sview(sc, WORLD(), seq![Fd(3)]));
    assert(seq![Fd(3)][0] == Fd(3));
    assert(sview(sc, STATE(), Seq::empty()) == Some(STATE()));
    assert(sview(sc, WORLD(), seq![Fd(3)]) == sview(sc, STATE(), seq![Fd(3)].drop_first()));
}

// ---- A. Field-sensitive footprint ------------------------------------------

/// ```text
/// 0: rw = &w
/// 1: rp = &rw.players
/// 2: ri = &rw.items
/// 3: it = &ri[i]               // place w.items.Kid(items)
/// 4: pl = &rp[j]               // place w.players.Kid(players)
/// 5: shuffle(mut rp)           // footprint: w.players and its kids only
/// ```
pub open spec fn fs_prefix() -> Seq<LInstr> {
    seq![
        LInstr::Borrow { dst: RW(), x: W() },
        LInstr::Field { dst: RP(), src: RW(), f: 1 },
        LInstr::Field { dst: RI(), src: RW(), f: 2 },
        LInstr::Child { dst: IT(), src: RI(), label: ITEMS() },
        LInstr::Child { dst: PL(), src: RP(), label: PLAYERS() },
        LInstr::Call { args: seq![(RP(), true)] },
    ]
}

/// After the call, `it` is still valid.
pub open spec fn fs_ok() -> Seq<LInstr> {
    fs_prefix().push(LInstr::Read { src: IT(), path: seq![Fd(0)] })
}

/// After the call, `pl` is used: rejected.
pub open spec fn fs_bad() -> Seq<LInstr> {
    fs_prefix().push(LInstr::Read { src: PL(), path: seq![Fd(0)] })
}

proof fn lemma_lss_prefix(ss: LSState, p: Seq<LInstr>, q: Seq<LInstr>, k: nat)
    requires
        k <= p.len() <= q.len(),
        forall|j: int| 0 <= j < p.len() ==> p[j] == q[j],
    ensures
        lss_at(ss, p, k) == lss_at(ss, q, k),
    decreases k,
{
    if k > 0 {
        lemma_lss_prefix(ss, p, q, (k - 1) as nat);
    }
}

proof fn lemma_fs_states() -> (sts: Seq<LSState>)
    ensures
        sts.len() == 7,
        forall|k: nat| k < 7 ==> #[trigger] lss_at(lss0(), fs_bad(), k) == sts[k as int],
        forall|k: nat| k < 6 ==> #[trigger] linstr_ok(wsc(), sts[k as int], fs_bad()[k as int]),
        sts[6].vars == map![RW() => at(seq![]), RP() => at(seq![Fd(1)]), RI() => at(seq![Fd(2)]), IT() => kid_of(seq![Fd(2)], ITEMS())],
        sts[6].lty == lss0().lty,
{
    let p = fs_bad();
    let sc = wsc();
    let s0 = lss0();
    let s1 = lpost(s0, p[0]);
    let s2 = lpost(s1, p[1]);
    let s3 = lpost(s2, p[2]);
    let s4 = lpost(s3, p[3]);
    let s5 = lpost(s4, p[4]);
    let s6 = lpost(s5, p[5]);
    lemma_types();
    lemma_kills_facts();
    assert(Seq::<PStep>::empty().push(Fd(1)) =~= seq![Fd(1)]);
    assert(Seq::<PStep>::empty().push(Fd(2)) =~= seq![Fd(2)]);
    assert(Seq::<(Seq<PStep>, Label)>::empty().push((seq![Fd(2)], ITEMS())) =~= seq![(seq![Fd(2)], ITEMS())]);
    assert(Seq::<(Seq<PStep>, Label)>::empty().push((seq![Fd(1)], PLAYERS())) =~= seq![(seq![Fd(1)], PLAYERS())]);
    assert(s1.vars =~= map![RW() => at(seq![])]);
    assert(s2.vars =~= map![RW() => at(seq![]), RP() => at(seq![Fd(1)])]);
    assert(s3.vars =~= map![RW() => at(seq![]), RP() => at(seq![Fd(1)]), RI() => at(seq![Fd(2)])]);
    assert(s4.vars[IT()] == kid_of(seq![Fd(2)], ITEMS()));
    assert(s4.vars =~= map![RW() => at(seq![]), RP() => at(seq![Fd(1)]), RI() => at(seq![Fd(2)]), IT() => kid_of(seq![Fd(2)], ITEMS())]);
    assert(s5.vars[PL()] == kid_of(seq![Fd(1)], PLAYERS()));
    assert(s5.vars =~= map![RW() => at(seq![]), RP() => at(seq![Fd(1)]), RI() => at(seq![Fd(2)]), IT() => kid_of(seq![Fd(2)], ITEMS()), PL() => kid_of(seq![Fd(1)], PLAYERS())]);
    let args = p[5]->Call_args;
    assert(args[0] == (RP(), true));
    assert(s5.vars[args[0].0] == at(seq![Fd(1)]));
    assert(lkilled(s5, args, kid_of(seq![Fd(1)], PLAYERS())));
    assert(!lkilled(s5, args, at(seq![])));
    assert(!lkilled(s5, args, at(seq![Fd(1)])));
    assert(!lkilled(s5, args, at(seq![Fd(2)])));
    assert(!lkilled(s5, args, kid_of(seq![Fd(2)], ITEMS())));
    assert(s6.vars =~= map![RW() => at(seq![]), RP() => at(seq![Fd(1)]), RI() => at(seq![Fd(2)]), IT() => kid_of(seq![Fd(2)], ITEMS())]);
    let sts = seq![s0, s1, s2, s3, s4, s5, s6];
    assert forall|k: nat| k < 7 implies #[trigger] lss_at(s0, p, k) == sts[k as int] by {
        assert(lss_at(s0, p, 0) == s0);
        assert(lss_at(s0, p, 1) == s1);
        assert(lss_at(s0, p, 2) == s2);
        assert(lss_at(s0, p, 3) == s3);
        assert(lss_at(s0, p, 4) == s4);
        assert(lss_at(s0, p, 5) == s5);
        assert(lss_at(s0, p, 6) == s6);
    }
    assert(world_kids()[ITEMS()].0 == seq![Fd(2)]);
    assert(world_kids()[PLAYERS()].0 == seq![Fd(1)]);
    assert forall|k: nat| k < 6 implies #[trigger] linstr_ok(sc, sts[k as int], p[k as int]) by {
        if k == 5 {
            assert(s5.vars.contains_key(args[0].0));
        }
    }
    sts
}

/// The checker accepts `fs_ok`.
pub proof fn example_fs_ok()
    ensures
        lcheck(wsc(), lss0(), fs_ok()),
{
    let sts = lemma_fs_states();
    let p = fs_ok();
    lemma_types();
    assert forall|k: nat| k < p.len() implies #[trigger] linstr_ok(wsc(), lss_at(lss0(), p, k), p[k as int]) by {
        lemma_lss_prefix(lss0(), fs_prefix(), p, k);
        lemma_lss_prefix(lss0(), fs_prefix(), fs_bad(), k);
        if k < 6 {
            assert(p[k as int] == fs_bad()[k as int]);
        } else {
            lemma_lss_prefix(lss0(), fs_prefix(), p, 6);
            lemma_lss_prefix(lss0(), fs_prefix(), fs_bad(), 6);
            assert(lss_at(lss0(), p, 6) == sts[6]);
            assert(sts[6].vars[IT()] == kid_of(seq![Fd(2)], ITEMS()));
            assert(place_ty(wsc(), sts[6], kid_of(seq![Fd(2)], ITEMS())) == place_ty(wsc(), lss0(), kid_of(seq![Fd(2)], ITEMS())));
        }
    }
}

/// The checker rejects `fs_bad`: `shuffle(mut w.players)` kills `pl`.
pub proof fn example_fs_rejected()
    ensures
        !lcheck(wsc(), lss0(), fs_bad()),
{
    let sts = lemma_fs_states();
    assert(lss_at(lss0(), fs_bad(), 6) == sts[6]);
    assert(!sts[6].vars.contains_key(PL()));
    assert(!linstr_ok(wsc(), lss_at(lss0(), fs_bad(), 6), fs_bad()[6]));
}

// ---- B. Inline enum: no type confusion -------------------------------------

/// ```text
/// 0: rw = &w
/// 1: rs = &rw.state
/// 2: if let Pair(..) = *rs { pa = &payload }   // place w.state.Variant(0)
/// 3: set_state(mut rs)                         // may switch the variant
/// ```
pub open spec fn en_prefix() -> Seq<LInstr> {
    seq![
        LInstr::Borrow { dst: RW(), x: W() },
        LInstr::Field { dst: RS(), src: RW(), f: 3 },
        LInstr::Variant { dst: PA(), src: RS(), v: 0 },
        LInstr::Call { args: seq![(RS(), true)] },
    ]
}

/// After the call, read `w.score`: accepted.
pub open spec fn en_ok() -> Seq<LInstr> {
    en_prefix().push(LInstr::Read { src: RW(), path: seq![Fd(0)] })
}

/// After the call, read the second field of the `Pair` payload: rejected.
pub open spec fn en_bad() -> Seq<LInstr> {
    en_prefix().push(LInstr::Read { src: PA(), path: seq![Fd(1)] })
}

proof fn lemma_en_states() -> (sts: Seq<LSState>)
    ensures
        sts.len() == 5,
        forall|k: nat| k < 5 ==> #[trigger] lss_at(lss0(), en_bad(), k) == sts[k as int],
        forall|k: nat| k < 4 ==> #[trigger] linstr_ok(wsc(), sts[k as int], en_bad()[k as int]),
        sts[4].vars == map![RW() => at(seq![]), RS() => at(seq![Fd(3)])],
        sts[4].lty == lss0().lty,
{
    let p = en_bad();
    let sc = wsc();
    let s0 = lss0();
    let s1 = lpost(s0, p[0]);
    let s2 = lpost(s1, p[1]);
    let s3 = lpost(s2, p[2]);
    let s4 = lpost(s3, p[3]);
    lemma_types();
    lemma_kills_facts();
    assert(Seq::<PStep>::empty().push(Fd(3)) =~= seq![Fd(3)]);
    assert(seq![Fd(3)].push(Vr(0)) =~= seq![Fd(3), Vr(0)]);
    assert(s1.vars =~= map![RW() => at(seq![])]);
    assert(s2.vars =~= map![RW() => at(seq![]), RS() => at(seq![Fd(3)])]);
    assert(s3.vars[PA()] == at(seq![Fd(3), Vr(0)]));
    assert(s3.vars =~= map![RW() => at(seq![]), RS() => at(seq![Fd(3)]), PA() => at(seq![Fd(3), Vr(0)])]);
    let args = p[3]->Call_args;
    assert(args[0] == (RS(), true));
    assert(s3.vars[args[0].0] == at(seq![Fd(3)]));
    assert(lkilled(s3, args, at(seq![Fd(3), Vr(0)])));
    assert(!lkilled(s3, args, at(seq![])));
    assert(!lkilled(s3, args, at(seq![Fd(3)])));
    assert(s4.vars =~= map![RW() => at(seq![]), RS() => at(seq![Fd(3)])]);
    let sts = seq![s0, s1, s2, s3, s4];
    assert forall|k: nat| k < 5 implies #[trigger] lss_at(s0, p, k) == sts[k as int] by {
        assert(lss_at(s0, p, 0) == s0);
        assert(lss_at(s0, p, 1) == s1);
        assert(lss_at(s0, p, 2) == s2);
        assert(lss_at(s0, p, 3) == s3);
        assert(lss_at(s0, p, 4) == s4);
    }
    assert forall|k: nat| k < 4 implies #[trigger] linstr_ok(sc, sts[k as int], p[k as int]) by {
        if k == 2 {
            assert(place_ty(sc, s2, at(seq![Fd(3)])) == Some(STATE()));
        }
        if k == 3 {
            assert(s3.vars.contains_key(args[0].0));
        }
    }
    sts
}

/// The checker accepts `en_ok`.
pub proof fn example_en_ok()
    ensures
        lcheck(wsc(), lss0(), en_ok()),
{
    let sts = lemma_en_states();
    let p = en_ok();
    lemma_types();
    assert forall|k: nat| k < p.len() implies #[trigger] linstr_ok(wsc(), lss_at(lss0(), p, k), p[k as int]) by {
        lemma_lss_prefix(lss0(), en_prefix(), p, k);
        lemma_lss_prefix(lss0(), en_prefix(), en_bad(), k);
        if k < 4 {
            assert(p[k as int] == en_bad()[k as int]);
        } else {
            lemma_lss_prefix(lss0(), en_prefix(), p, 4);
            lemma_lss_prefix(lss0(), en_prefix(), en_bad(), 4);
            assert(lss_at(lss0(), p, 4) == sts[4]);
            assert(place_ty(wsc(), sts[4], at(seq![])) == place_ty(wsc(), lss0(), at(seq![])));
        }
    }
}

/// The checker rejects `en_bad`: `set_state(mut w.state)` kills `pa`.
pub proof fn example_en_rejected()
    ensures
        !lcheck(wsc(), lss0(), en_bad()),
{
    let sts = lemma_en_states();
    assert(lss_at(lss0(), en_bad(), 4) == sts[4]);
    assert(!sts[4].vars.contains_key(PA()));
    assert(!linstr_ok(wsc(), lss_at(lss0(), en_bad(), 4), en_bad()[4]));
}

// ---- C. Type stability -----------------------------------------------------

/// ```text
/// 0: rw = &w
/// 1: sc = &rw.score
/// 2: rs = &rw.state
/// 3: update(mut rw)        // kills only places inside w through an unstable step
/// 4: read *sc              // still valid
/// 5: if let Pair(..) = *rs { pa = &payload }   // rs is still valid
/// ```
pub open spec fn stable() -> Seq<LInstr> {
    seq![
        LInstr::Borrow { dst: RW(), x: W() },
        LInstr::Field { dst: SC(), src: RW(), f: 0 },
        LInstr::Field { dst: RS(), src: RW(), f: 3 },
        LInstr::Call { args: seq![(RW(), true)] },
        LInstr::Read { src: SC(), path: seq![] },
        LInstr::Variant { dst: PA(), src: RS(), v: 0 },
    ]
}

/// The checker accepts `stable`.
pub proof fn example_stable_ok()
    ensures
        lcheck(wsc(), lss0(), stable()),
{
    let p = stable();
    let sc = wsc();
    let s0 = lss0();
    let s1 = lpost(s0, p[0]);
    let s2 = lpost(s1, p[1]);
    let s3 = lpost(s2, p[2]);
    let s4 = lpost(s3, p[3]);
    let s5 = lpost(s4, p[4]);
    lemma_types();
    lemma_kills_facts();
    assert(Seq::<PStep>::empty().push(Fd(0)) =~= seq![Fd(0)]);
    assert(Seq::<PStep>::empty().push(Fd(3)) =~= seq![Fd(3)]);
    assert(s1.vars =~= map![RW() => at(seq![])]);
    assert(s3.vars =~= map![RW() => at(seq![]), SC() => at(seq![Fd(0)]), RS() => at(seq![Fd(3)])]);
    let args = p[3]->Call_args;
    assert(args[0] == (RW(), true));
    assert(s3.vars[args[0].0] == at(seq![]));
    assert(!lkilled(s3, args, at(seq![])));
    assert(!lkilled(s3, args, at(seq![Fd(0)])));
    assert(!lkilled(s3, args, at(seq![Fd(3)])));
    assert(s4.vars =~= s3.vars);
    assert(s5 == s4);
    assert(place_ty(sc, s4, at(seq![Fd(0)])) == Some(PRIM()));
    assert(place_ty(sc, s5, at(seq![Fd(3)])) == Some(STATE()));
    assert forall|k: nat| k < p.len() implies #[trigger] linstr_ok(sc, lss_at(s0, p, k), p[k as int]) by {
        assert(lss_at(s0, p, 0) == s0);
        assert(lss_at(s0, p, 1) == s1);
        assert(lss_at(s0, p, 2) == s2);
        assert(lss_at(s0, p, 3) == s3);
        assert(lss_at(s0, p, 4) == s4);
        assert(lss_at(s0, p, 5) == s5);
        if k == 3 {
            assert(s3.vars.contains_key(args[0].0));
        }
    }
}

// ---- D. Out of bounds ------------------------------------------------------

/// ```text
/// 0: rw = &w
/// 1: read rw.field9        // World has 4 fields
/// ```
pub open spec fn oob() -> Seq<LInstr> {
    seq![LInstr::Borrow { dst: RW(), x: W() }, LInstr::Read { src: RW(), path: seq![Fd(9)] }]
}

/// The checker rejects `oob`.
pub proof fn example_oob_rejected()
    ensures
        !lcheck(wsc(), lss0(), oob()),
{
    let p = oob();
    let s1 = lpost(lss0(), p[0]);
    lemma_types();
    assert(s1.vars[RW()] == at(seq![]));
    assert(lss_at(lss0(), p, 1) == s1) by {
        assert(lss_at(lss0(), p, 0) == lss0());
    }
    assert(place_ty(wsc(), s1, at(seq![])) == Some(WORLD()));
    assert(!linstr_ok(wsc(), s1, p[1]));
}

// ---------------------------------------------------------------------------
// Concrete runs
// ---------------------------------------------------------------------------

/// A world with the data `data` and its player at `pa`.
pub open spec fn world_with(data: Seq<int>, pa: Addr) -> Obj {
    Obj { stamp: 0, ty: WORLD(), data, kids: seq![(PLAYERS(), pa), (ITEMS(), 2nat)] }
}

/// A list element.
pub open spec fn elem(stamp: Stamp, v: int) -> Obj {
    Obj { stamp, ty: ELEM(), data: seq![v], kids: seq![] }
}

/// A world at address 0, its player at `pa`, and its item at address 2.
pub open spec fn wheap(data: Seq<int>, pa: Addr, ps: Stamp, pv: int) -> Heap {
    map![0nat => world_with(data, pa), pa => elem(ps, pv), 2nat => elem(2, 7)]
}

/// The data of the world at the start: the state is `Pair(5, 6)`.
pub open spec fn data0() -> Seq<int> {
    seq![10, 1, 1, 0, 5, 6]
}

/// The start state of the runs.
pub open spec fn lst0() -> LState {
    LState { heap: wheap(data0(), 1, 1, 100), locals: map![W() => 0nat], vars: Map::empty(), next_stamp: 3 }
}

proof fn lemma_wheap_wf(data: Seq<int>, pa: Addr, ps: Stamp, pv: int, n: Stamp)
    requires
        data.len() == 6,
        pa != 0 && pa != 2,
        ps != 0 && ps != 2,
        ps < n,
        2 < n,
    ensures
        heap_wf(wheap(data, pa, ps, pv), map![W() => 0nat], n),
        layout_wf(wsc(), wheap(data, pa, ps, pv)),
{
    let h = wheap(data, pa, ps, pv);
    let sc = wsc();
    assert(h.dom() =~= set![0nat, pa, 2nat]);
    assert forall|b: Addr, i: int, c: Addr| #[trigger] owns(h, b, i, c) implies b == 0 && ((i == 0 && c == pa) || (i == 1
        && c == 2)) by {}
    let d = DState { heap: h, locals: map![W() => 0nat], vars: Map::empty(), clos: Map::empty(), next_stamp: n };
    assert(wf(d));
    assert forall|a: Addr| #[trigger] h.contains_key(a) implies {
        &&& sc.contains_key(h[a].ty)
        &&& h[a].data.len() == sc[h[a].ty].size
        &&& forall|i: int|
            0 <= i < h[a].kids.len() ==> sc[h[a].ty].kids.contains_key(#[trigger] h[a].kids[i].0)
                && h[h[a].kids[i].1].ty == sc[h[a].ty].kids[h[a].kids[i].0].1
    } by {
        if a == 0 {
            assert forall|i: int| 0 <= i < h[a].kids.len() implies sc[h[a].ty].kids.contains_key(#[trigger] h[a].kids[i].0)
                && h[h[a].kids[i].1].ty == sc[h[a].ty].kids[h[a].kids[i].0].1 by {
                assert(i == 0 || i == 1);
            }
        }
    }
}

/// A pointer into the world at the inline path `fp`.
pub open spec fn wptr(fp: Seq<PStep>) -> IPtr {
    IPtr { addr: 0, stamp: 0, ty: WORLD(), fp }
}

/// A pointer to the list element at `a`.
pub open spec fn eptr(a: Addr, stamp: Stamp) -> IPtr {
    IPtr { addr: a, stamp, ty: ELEM(), fp: Seq::empty() }
}

/// The start state with the variables `vars`.
pub open spec fn lsw(vars: Map<Var, IPtr>) -> LState {
    LState { vars, ..lst0() }
}

proof fn lemma_world_views(data: Seq<int>)
    requires
        data.len() == 6,
    ensures
        view(wsc(), WORLD(), data, 0, seq![]) == Some((WORLD(), 0nat)),
        view(wsc(), WORLD(), data, 0, seq![Fd(0)]) == Some((PRIM(), 0nat)),
        view(wsc(), WORLD(), data, 0, seq![Fd(1)]) is Some,
        view(wsc(), WORLD(), data, 0, seq![Fd(2)]) is Some,
        view(wsc(), WORLD(), data, 0, seq![Fd(3)]) == Some((STATE(), 3nat)),
        data[3] == 0 ==> view(wsc(), WORLD(), data, 0, seq![Fd(3), Vr(0)]) is Some,
        data[3] != 0 ==> view(wsc(), WORLD(), data, 0, seq![Fd(3), Vr(0)]) is None,
        view(wsc(), WORLD(), data, 0, seq![Fd(9)]) is None,
{
    let sc = wsc();
    reveal_with_fuel(view, 3);
    assert(seq![Fd(0)].drop_first() =~= Seq::<PStep>::empty());
    assert(seq![Fd(1)].drop_first() =~= Seq::<PStep>::empty());
    assert(seq![Fd(2)].drop_first() =~= Seq::<PStep>::empty());
    assert(seq![Fd(3)].drop_first() =~= Seq::<PStep>::empty());
    assert(seq![Fd(9)][0] == Fd(9));
    let fv = seq![Fd(3), Vr(0)];
    assert(fv[0] == Fd(3));
    assert(fv.drop_first() =~= seq![Vr(0)]);
    assert(seq![Vr(0)].drop_first() =~= Seq::<PStep>::empty());
    assert(dstep(sc, WORLD(), data, 0, Fd(3)) == Some((STATE(), 3nat)));
    assert(dstep(sc, WORLD(), data, 0, Fd(0)) == Some((PRIM(), 0nat)));
    assert(view(sc, STATE(), data, 3, seq![Vr(0)]) == match dstep(sc, STATE(), data, 3, Vr(0)) {
        Some(r) => view(sc, r.0, data, r.1, seq![Vr(0)].drop_first()),
        None => None,
    });
    if data[3] == 0 {
        assert(dstep(sc, STATE(), data, 3, Vr(0)) == Some((PAIR(), 4nat)));
    }
}

/// `ptr` is valid now in state `s`, and its allocation is `o`.
proof fn lemma_ilive(s: LState, p: IPtr)
    requires
        s.heap.contains_key(p.addr),
        s.heap[p.addr].stamp == p.stamp,
        s.heap[p.addr].ty == p.ty,
        view(wsc(), p.ty, s.heap[p.addr].data, 0, p.fp) is Some,
    ensures
        ilive(wsc(), s, p),
{
}

// ---- A. `shuffle(mut w.players)` frees the player ----------------------------

/// The variables before `shuffle`.
pub open spec fn fs_vars5() -> Map<Var, IPtr> {
    map![RW() => wptr(seq![]), RP() => wptr(seq![Fd(1)]), RI() => wptr(seq![Fd(2)]), IT() => eptr(2, 2), PL() => eptr(1, 1)]
}

/// After `shuffle`: the old player is freed, and a new player (stamp 3) is at address 3.
pub open spec fn fs_heap6() -> Heap {
    wheap(data0(), 3, 3, 200)
}

/// The concrete run of `fs_bad`.
pub open spec fn fs_trace() -> Seq<LState> {
    seq![
        lst0(),
        lsw(map![RW() => wptr(seq![])]),
        lsw(map![RW() => wptr(seq![]), RP() => wptr(seq![Fd(1)])]),
        lsw(map![RW() => wptr(seq![]), RP() => wptr(seq![Fd(1)]), RI() => wptr(seq![Fd(2)])]),
        lsw(map![RW() => wptr(seq![]), RP() => wptr(seq![Fd(1)]), RI() => wptr(seq![Fd(2)]), IT() => eptr(2, 2)]),
        lsw(fs_vars5()),
        LState { heap: fs_heap6(), next_stamp: 4, ..lsw(fs_vars5()) },
    ]
}

proof fn lemma_shuffle_effect()
    ensures
        lcallee_effect(wsc(), lsw(fs_vars5()), lptrs(lsw(fs_vars5()), fs_bad()[5]->Call_args), fs_heap6(), 4),
{
    let sc = wsc();
    let s = lsw(fs_vars5());
    let args = fs_bad()[5]->Call_args;
    let ps = lptrs(s, args);
    let h = s.heap;
    let h2 = fs_heap6();
    assert(fs_bad()[5] == fs_prefix()[5]);
    assert(args.len() == 1 && args[0] == (RP(), true));
    assert(ps.len() == 1);
    assert(ps[0] == (wptr(seq![Fd(1)]), true));
    assert(ps[0].0.addr == 0 && ps[0].1);
    assert(mut_target(ps, 0));
    lemma_wheap_wf(data0(), 3, 3, 200, 4);
    assert(LState { heap: h2, next_stamp: 4, ..s }.locals == map![W() => 0nat]);
    // the old player is below `w.players`, through a kid that `w.players` owns
    let r = seq![(PLAYERS(), 0nat)];
    assert(r.drop_last() =~= Seq::<Step>::empty());
    assert(resolve(h, 0, Seq::<Step>::empty()) == Some(0nat));
    assert(kid_at(h, 0, r.last()) == Some(1nat));
    assert(resolve(h, 0, r) == Some(1nat));
    assert(seq![Fd(1)].is_prefix_of(world_kids()[PLAYERS()].0)) by {
        assert(seq![Fd(1)] =~= world_kids()[PLAYERS()].0.subrange(0, 1));
    }
    assert(owned_under(sc, h[0].ty, r[0].0, ps[0].0.fp));
    assert(fbelow(sc, h, ps[0].0.addr, ps[0].0.fp, 1));
    assert(full_fp(sc, h, ps, 1));
    assert(kid_mut(sc, h, ps, 0, PLAYERS())) by {
        assert(owned_under(sc, h[0].ty, PLAYERS(), ps[0].0.fp));
    }
    assert(h.dom() =~= set![0nat, 1nat, 2nat]);
    assert(h2.dom() =~= set![0nat, 3nat, 2nat]);
    assert forall|a: Addr| #[trigger] h.contains_key(a) && !full_fp(sc, h, ps, a) && mut_target(ps, a) implies {
        &&& h2.contains_key(a)
        &&& h2[a].stamp == h[a].stamp
        &&& h2[a].ty == h[a].ty
        &&& forall|j: int|
            0 <= j < h[a].data.len() && !in_mut_region(sc, h, ps, a, j) ==> #[trigger] h2[a].data[j] == h[a].data[j]
        &&& forall|i: int|
            0 <= i < h[a].kids.len() && !kid_mut(sc, h, ps, a, h[a].kids[i].0) ==> i < h2[a].kids.len()
                && #[trigger] h2[a].kids[i] == h[a].kids[i]
    } by {
        assert(a == 0);
        assert forall|i: int| 0 <= i < h[a].kids.len() && !kid_mut(sc, h, ps, a, h[a].kids[i].0) implies i < h2[a].kids.len()
            && #[trigger] h2[a].kids[i] == h[a].kids[i] by {
            assert(i == 0 || i == 1);
        }
    }
}

/// A concrete run of `fs_bad`: `shuffle` frees the player that `pl` points to,
/// and the read of `pl` is a use after free.
pub proof fn example_fs_bad_is_ub()
    ensures
        is_ltrace(wsc(), fs_bad(), fs_trace()),
        lwf(wsc(), fs_trace()[0]),
        lub(wsc(), fs_trace()[6], fs_bad()[6]),
{
    let sc = wsc();
    let p = fs_bad();
    let t = fs_trace();
    lemma_wheap_wf(data0(), 1, 1, 100, 3);
    lemma_world_views(data0());
    lemma_shuffle_effect();
    assert(Seq::<PStep>::empty().push(Fd(1)) =~= seq![Fd(1)]);
    assert(Seq::<PStep>::empty().push(Fd(2)) =~= seq![Fd(2)]);
    assert forall|k: int| 0 <= k < t.len() - 1 implies lstep(sc, #[trigger] t[k], p[k], t[k + 1]) by {
        let s = t[k];
        if k == 0 {
            assert(s.vars.insert(RW(), lptr_to(s.heap, s.locals[W()])) =~= t[1].vars);
        } else if k == 1 {
            lemma_ilive(s, wptr(seq![]));
            assert(s.vars.insert(RP(), wptr(seq![Fd(1)])) =~= t[2].vars);
        } else if k == 2 {
            lemma_ilive(s, wptr(seq![]));
            assert(s.vars.insert(RI(), wptr(seq![Fd(2)])) =~= t[3].vars);
        } else if k == 3 {
            lemma_ilive(s, wptr(seq![Fd(2)]));
            assert(kid_at(s.heap, s.vars[RI()].addr, (ITEMS(), 1nat)) == Some(2nat));
            assert(s.vars.insert(IT(), lptr_to(s.heap, 2)) =~= t[4].vars);
        } else if k == 4 {
            lemma_ilive(s, wptr(seq![Fd(1)]));
            assert(kid_at(s.heap, s.vars[RP()].addr, (PLAYERS(), 0nat)) == Some(1nat));
            assert(s.vars.insert(PL(), lptr_to(s.heap, 1)) =~= t[5].vars);
        } else {
            let args = p[5]->Call_args;
            lemma_ilive(s, wptr(seq![Fd(1)]));
            assert forall|j: int| 0 <= j < args.len() implies !#[trigger] ldangling(sc, s, args[j].0) by {
                assert(j == 0);
            }
        }
    }
    assert(!fs_heap6().contains_key(1nat));
}

// ---- B. `set_state(mut w.state)` switches the variant ----------------------

/// The variables before `set_state`.
pub open spec fn en_vars3() -> Map<Var, IPtr> {
    map![RW() => wptr(seq![]), RS() => wptr(seq![Fd(3)]), PA() => wptr(seq![Fd(3), Vr(0)])]
}

/// After `set_state`: the state is `Idle(42)`, tag 1 at slot 3.
pub open spec fn data_idle() -> Seq<int> {
    seq![10, 1, 1, 1, 42, 6]
}

/// The concrete run of `en_bad`.
pub open spec fn en_trace() -> Seq<LState> {
    seq![
        lst0(),
        lsw(map![RW() => wptr(seq![])]),
        lsw(map![RW() => wptr(seq![]), RS() => wptr(seq![Fd(3)])]),
        lsw(en_vars3()),
        LState { heap: wheap(data_idle(), 1, 1, 100), ..lsw(en_vars3()) },
    ]
}

proof fn lemma_set_state_effect()
    ensures
        lcallee_effect(wsc(), lsw(en_vars3()), lptrs(lsw(en_vars3()), en_bad()[3]->Call_args), wheap(data_idle(), 1, 1, 100), 3),
{
    let sc = wsc();
    let s = lsw(en_vars3());
    let args = en_bad()[3]->Call_args;
    let ps = lptrs(s, args);
    let h = s.heap;
    let h2 = wheap(data_idle(), 1, 1, 100);
    assert(en_bad()[3] == en_prefix()[3]);
    assert(args.len() == 1 && args[0] == (RS(), true));
    assert(ps.len() == 1);
    assert(ps[0] == (wptr(seq![Fd(3)]), true));
    assert(ps[0].0.addr == 0 && ps[0].1);
    assert(mut_target(ps, 0));
    lemma_wheap_wf(data_idle(), 1, 1, 100, 3);
    lemma_world_views(data0());
    assert(LState { heap: h2, next_stamp: 3, ..s }.locals == map![W() => 0nat]);
    assert(h.dom() =~= set![0nat, 1nat, 2nat]);
    assert(h2.dom() =~= set![0nat, 1nat, 2nat]);
    // slots 3..6 are the region of `w.state`
    assert forall|j: int| 3 <= j < 6 implies #[trigger] in_mut_region(sc, h, ps, 0, j) by {
        assert(in_region(sc, h[0], ps[0].0.fp, j));
    }
    assert forall|a: Addr| #[trigger] h.contains_key(a) && !full_fp(sc, h, ps, a) && mut_target(ps, a) implies {
        &&& h2.contains_key(a)
        &&& h2[a].stamp == h[a].stamp
        &&& h2[a].ty == h[a].ty
        &&& forall|j: int|
            0 <= j < h[a].data.len() && !in_mut_region(sc, h, ps, a, j) ==> #[trigger] h2[a].data[j] == h[a].data[j]
        &&& forall|i: int|
            0 <= i < h[a].kids.len() && !kid_mut(sc, h, ps, a, h[a].kids[i].0) ==> i < h2[a].kids.len()
                && #[trigger] h2[a].kids[i] == h[a].kids[i]
    } by {
        assert(a == 0);
        assert forall|j: int| 0 <= j < h[a].data.len() && !in_mut_region(sc, h, ps, a, j) implies #[trigger] h2[a].data[j]
            == h[a].data[j] by {
            assert(j < 3 || j == 5);
        }
    }
}

proof fn lemma_en_steps()
    ensures
        forall|k: int| 0 <= k < 4 ==> lstep(wsc(), #[trigger] en_trace()[k], en_bad()[k], en_trace()[k + 1]),
        lstep(wsc(), en_trace()[4], en_ok()[4], en_trace()[4]),
        lub(wsc(), en_trace()[4], en_bad()[4]),
        lwf(wsc(), en_trace()[0]),
{
    let sc = wsc();
    let p = en_bad();
    let t = en_trace();
    lemma_wheap_wf(data0(), 1, 1, 100, 3);
    lemma_world_views(data0());
    lemma_world_views(data_idle());
    lemma_set_state_effect();
    assert(Seq::<PStep>::empty().push(Fd(3)) =~= seq![Fd(3)]);
    assert(seq![Fd(3)].push(Vr(0)) =~= seq![Fd(3), Vr(0)]);
    assert forall|k: int| 0 <= k < 4 implies lstep(sc, #[trigger] t[k], p[k], t[k + 1]) by {
        let s = t[k];
        if k == 0 {
            assert(s.vars.insert(RW(), lptr_to(s.heap, s.locals[W()])) =~= t[1].vars);
        } else if k == 1 {
            lemma_ilive(s, wptr(seq![]));
            assert(s.vars.insert(RS(), wptr(seq![Fd(3)])) =~= t[2].vars);
        } else if k == 2 {
            lemma_ilive(s, wptr(seq![Fd(3)]));
            assert(s.vars.insert(PA(), wptr(seq![Fd(3), Vr(0)])) =~= t[3].vars);
        } else {
            let args = p[3]->Call_args;
            lemma_ilive(s, wptr(seq![Fd(3)]));
            assert forall|j: int| 0 <= j < args.len() implies !#[trigger] ldangling(sc, s, args[j].0) by {
                assert(j == 0);
            }
        }
    }
    let s4 = t[4];
    lemma_ilive(s4, wptr(seq![]));
    assert(seq![] + seq![Fd(0)] =~= seq![Fd(0)]);
    assert(slot(sc, s4, wptr(seq![]), seq![Fd(0)]) == Some(0nat));
    assert(!ilive(sc, s4, wptr(seq![Fd(3), Vr(0)])));
}

/// A concrete run of `en_bad`: `set_state` switches the state to `Idle`, and
/// the read through `pa` would read the `Pair` payload: a type confusion.
pub proof fn example_en_bad_is_ub()
    ensures
        is_ltrace(wsc(), en_bad(), en_trace()),
        lwf(wsc(), en_trace()[0]),
        lub(wsc(), en_trace()[4], en_bad()[4]),
{
    lemma_en_steps();
}

/// A run of `en_ok` meets every hypothesis of `layout_soundness_from_start`,
/// so the theorem applies to it.
pub proof fn example_layout_soundness_applies()
    ensures
        exists|trace: Seq<LState>|
            #![trigger is_ltrace(wsc(), en_ok(), trace)]
            {
                &&& is_ltrace(wsc(), en_ok(), trace)
                &&& wf_schema(wsc())
                &&& lwf(wsc(), trace[0])
                &&& lcheck(wsc(), linitial(trace[0]), en_ok())
                &&& trace.len() == 6
                &&& forall|k: int| 0 <= k < 5 ==> !#[trigger] lub(wsc(), trace[k], en_ok()[k])
            },
{
    hide(lstep);
    hide(lub);
    hide(lcheck);
    hide(wf_schema);
    hide(lwf);
    hide(en_vars3);
    lemma_en_steps();
    lemma_wsc_ok();
    example_en_ok();
    let t = en_trace();
    let trace = t.push(t[4]);
    assert(is_ltrace(wsc(), en_ok(), trace)) by {
        assert forall|k: int| 0 <= k < trace.len() - 1 implies lstep(wsc(), #[trigger] trace[k], en_ok()[k], trace[k + 1]) by {
            if k < 4 {
                assert(trace[k] == t[k] && trace[k + 1] == t[k + 1]);
                assert(en_ok()[k] == en_bad()[k]);
            } else {
                assert(trace[4] == t[4] && trace[5] == t[4]);
            }
        }
    }
    assert(linitial(trace[0]) == lss0()) by {
        assert(lst0().locals.dom() =~= set![W()]);
        assert(linitial(lst0()).lty =~= map![W() => WORLD()]);
    }
    layout_soundness_from_start(wsc(), en_ok(), trace);
}

// ---- D. Out of bounds is UB ------------------------------------------------

/// A concrete run of `oob`: the read of field 9 is outside the layout of
/// `World`, so it is UB.
pub proof fn example_oob_is_ub()
    ensures
        is_ltrace(wsc(), oob(), seq![lst0(), lsw(map![RW() => wptr(seq![])])]),
        lub(wsc(), lsw(map![RW() => wptr(seq![])]), oob()[1]),
{
    let s = lst0();
    lemma_world_views(data0());
    assert(s.vars.insert(RW(), lptr_to(s.heap, s.locals[W()])) =~= map![RW() => wptr(seq![])]);
    assert(seq![] + seq![Fd(9)] =~= seq![Fd(9)]);
}

} // verus!
