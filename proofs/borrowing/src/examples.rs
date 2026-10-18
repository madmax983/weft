//! Sanity checks: the checker accepts the programs from the group-borrowing
//! write-up (including ones Rust's borrow checker rejects), rejects the
//! unsafe ones, and the invalidation rule is *necessary*: the rejected
//! program really can dereference a freed allocation.

#![allow(non_snake_case)]

use vstd::prelude::*;
use crate::model::*;
use crate::soundness::*;

verus! {

// local
/// The local `d`.
pub open spec fn D() -> Local { 0 }

// labels (child groups of Entity)
/// The child group `rings` of an entity.
pub open spec fn RINGS() -> Label { 0 }
/// The child group `armor` of an entity.
pub open spec fn ARMOR() -> Label { 1 }

// reference variables
/// The reference variable `rd`.
pub open spec fn RD() -> Var { 0 }
/// The reference variable `ring`.
pub open spec fn RING() -> Var { 1 }
/// The reference variable `arm`.
pub open spec fn ARM() -> Var { 2 }
/// The reference variable `a`.
pub open spec fn A() -> Var { 3 }
/// The reference variable `b`.
pub open spec fn B() -> Var { 4 }

/// The checker state at the start: the local `d`, no references.
pub open spec fn ss0() -> SState {
    SState { locals: Set::empty().insert(D()), vars: Map::empty(), clos: Map::empty() }
}

/// The group `root.path`.
pub open spec fn g(root: Local, path: Seq<Label>) -> Group {
    Group { root, path }
}

// ---------------------------------------------------------------------------
// 1. `d.damage(10)` keeps references to `d` alive but kills `ring_ref`.
// ---------------------------------------------------------------------------

/// The safe prefix: `d.damage(10)`, then `d.hp`.
pub open spec fn damage_prefix() -> Seq<Instr> {
    seq![
        Instr::Borrow { dst: RD(), x: D() },                    // rd   = &d          : d
        Instr::Child { dst: RING(), src: RD(), label: RINGS() }, // ring = &d.rings[i] : d.rings*
        Instr::Read { src: RING(), field: 0 },
        Instr::Call { args: seq![(RD(), true)], ret: None },    // d.damage(10)
        Instr::Read { src: RD(), field: 0 },                    // d.hp: still fine
    ]
}

/// The prefix, then a read of `ring` after `d.damage(10)`.
pub open spec fn damage_bad() -> Seq<Instr> {
    damage_prefix().push(Instr::Read { src: RING(), field: 0 })  // ring: use-after-free!
}

proof fn lemma_damage_states() -> (sts: Seq<SState>)
    ensures
        sts.len() == 6,
        forall|k: nat| k < 6 ==> #[trigger] ss_at(ss0(), damage_bad(), k) == sts[k as int],
        sts[1].vars == map![RD() => g(D(), seq![])],
        sts[2].vars == map![RD() => g(D(), seq![]), RING() => g(D(), seq![RINGS()])],
        sts[4].vars == map![RD() => g(D(), seq![])],
        sts[3] == sts[2],
        sts[5] == sts[4],
{
    let p = damage_bad();
    let s0 = ss0();
    let s1 = post(s0, p[0]);
    let s2 = post(s1, p[1]);
    let s3 = post(s2, p[2]);
    let s4 = post(s3, p[3]);
    let s5 = post(s4, p[4]);
    assert(s1.vars =~= map![RD() => g(D(), seq![])]);
    assert(s2.vars =~= map![RD() => g(D(), seq![]), RING() => g(D(), seq![RINGS()])]);
    assert(s3 == s2);
    let args = seq![(RD(), true)];
    let gs = arg_groups(s3, args);
    assert(seq![RINGS()].subrange(0, 0) =~= Seq::<Label>::empty());
    assert(strict_child(g(D(), seq![RINGS()]), g(D(), seq![])));
    assert(gs[0] == (g(D(), seq![]), true));
    assert(strict_child(s3.vars[RING()], gs[0].0));
    assert(killed(gs, s3.vars[RING()]));
    assert(!strict_child(g(D(), seq![]), g(D(), seq![])));
    assert(!killed(gs, s3.vars[RD()]));
    assert(s4.vars =~= map![RD() => g(D(), seq![])]);
    assert(s4.clos =~= Map::<CVar, Seq<(Group, bool)>>::empty());
    let sts = seq![s0, s1, s2, s3, s4, s5];
    assert forall|k: nat| k < 6 implies #[trigger] ss_at(s0, p, k) == sts[k as int] by {
        assert(ss_at(s0, p, 0) == s0);
        assert(ss_at(s0, p, 1) == s1);
        assert(ss_at(s0, p, 2) == s2);
        assert(ss_at(s0, p, 3) == s3);
        assert(ss_at(s0, p, 4) == s4);
        assert(ss_at(s0, p, 5) == s5);
    }
    sts
}

/// The safe prefix passes the checker.
pub proof fn example_damage_ok()
    ensures
        check(ss0(), damage_prefix()),
{
    let sts = lemma_damage_states();
    let p = damage_prefix();
    assert forall|k: nat| k < p.len() implies #[trigger] instr_ok(ss_at(ss0(), p, k), p[k as int]) by {
        assert(ss_at(ss0(), p, k) == ss_at(ss0(), damage_bad(), k)) by {
            lemma_ss_at_prefix(ss0(), p, damage_bad(), k);
        }
        assert(ss_at(ss0(), damage_bad(), k) == sts[k as int]);
        if k == 3 {
            let args = seq![(RD(), true)];
            assert(p[3] == Instr::Call { args, ret: None });
            assert(sts[3].vars.contains_key(args[0].0));
        }
    }
}

/// Using `ring_ref` after `d.damage(10)` is rejected.
pub proof fn example_damage_rejected()
    ensures
        !check(ss0(), damage_bad()),
{
    let sts = lemma_damage_states();
    assert(ss_at(ss0(), damage_bad(), 5) == sts[5]);
    assert(!instr_ok(ss_at(ss0(), damage_bad(), 5), damage_bad()[5]));
}

/// A program and its extension have the same checker states on the common prefix.
pub proof fn lemma_ss_at_prefix(ss: SState, p: Seq<Instr>, q: Seq<Instr>, k: nat)
    requires
        k <= p.len() <= q.len(),
        forall|j: int| 0 <= j < p.len() ==> p[j] == q[j],
    ensures
        ss_at(ss, p, k) == ss_at(ss, q, k),
    decreases k,
{
    if k > 0 {
        lemma_ss_at_prefix(ss, p, q, (k - 1) as nat);
    }
}

// ---------------------------------------------------------------------------
// 2. The invalidation rule is necessary: `damage_bad` really does hit UB.
// ---------------------------------------------------------------------------

/// An entity with one ring.
pub open spec fn entity() -> Obj {
    Obj { stamp: 0, ty: 0, data: seq![100], kids: seq![(RINGS(), 1nat)] }
}

/// A ring.
pub open spec fn ring() -> Obj {
    Obj { stamp: 1, ty: 1, data: seq![5], kids: seq![] }
}

/// The entity after `damage`: no rings.
pub open spec fn damaged() -> Obj {
    Obj { stamp: 0, ty: 0, data: seq![90], kids: seq![] }
}

/// The start state: the entity at address 0, its ring at address 1.
pub open spec fn st0() -> DState {
    DState {
        heap: map![0nat => entity(), 1nat => ring()],
        locals: map![D() => 0nat],
        vars: Map::empty(),
        clos: Map::empty(),
        next_stamp: 2,
    }
}

/// The start state is well-formed.
pub proof fn lemma_st0_wf()
    ensures
        wf(st0()),
{
    let h = st0().heap;
    assert(h.dom() =~= set![0nat, 1nat]);
    assert forall|b: Addr, i: int, c: Addr| #[trigger] owns(h, b, i, c) implies b == 0 && i == 0 && c == 1 by {}
}

/// The state after `rd = &d`.
pub open spec fn t1() -> DState {
    DState { vars: map![RD() => ptr_to(st0().heap, 0)], ..st0() }
}

/// The state after `ring = &d.rings[0]`.
pub open spec fn t2() -> DState {
    DState { vars: map![RD() => ptr_to(st0().heap, 0), RING() => ptr_to(st0().heap, 1)], ..st0() }
}

/// The heap after `damage` freed the ring.
pub open spec fn h_damaged() -> Heap {
    map![0nat => damaged()]
}

/// The state after `d.damage(10)`.
pub open spec fn t4() -> DState {
    DState { heap: h_damaged(), ..t2() }
}

/// The arguments of `d.damage(10)`.
pub open spec fn damage_args() -> Seq<(Var, bool)> {
    seq![(RD(), true)]
}

/// The first three steps of the concrete run.
pub proof fn lemma_damage_steps_0_2()
    ensures
        step(st0(), damage_bad()[0], t1()),
        step(t1(), damage_bad()[1], t2()),
        step(t2(), damage_bad()[2], t2()),
{
    let p = damage_bad();
    assert(st0().vars.insert(RD(), ptr_to(st0().heap, 0)) =~= t1().vars);
    assert(kid_at(t1().heap, t1().vars[RD()].addr, (RINGS(), 0nat)) == Some(1nat));
    assert(t1().vars.insert(RING(), ptr_to(st0().heap, 1)) =~= t2().vars);
    assert(p[1] == Instr::Child { dst: RING(), src: RD(), label: RINGS() });
}

/// From any state with the heap of `st0`, a callee with one mutable argument
/// that points to `d` may free the ring. This is the effect of `d.damage(10)`.
pub proof fn lemma_free_ring_effect(s: DState, ps: Seq<(Ptr, bool)>)
    requires
        s.heap == st0().heap,
        s.locals == st0().locals,
        s.next_stamp == 2,
        ps.len() == 1,
        ps[0] == (ptr_to(st0().heap, 0), true),
    ensures
        callee_effect(s, ps, h_damaged(), 2),
{
    let h2 = h_damaged();
    let s4 = DState { heap: h2, next_stamp: 2, ..s };
    assert(h2.dom() =~= set![0nat]);
    assert forall|b: Addr, i: int, c: Addr| !#[trigger] owns(h2, b, i, c) by {}
    assert(wf(s4));
    assert(ps[0].0.addr == 0 && ps[0].1);
    assert(is_mut_root(ps, 0));
    let r1 = seq![(RINGS(), 0nat)];
    assert(r1.drop_last() =~= Seq::<Step>::empty());
    assert(resolve(s.heap, 0, Seq::<Step>::empty()) == Some(0nat));
    assert(resolve(s.heap, 0, r1) == Some(1nat));
    assert(below(s.heap, 0, 1));
    assert(below_mut(s.heap, ps, 1));
    assert(s.heap.dom() =~= set![0nat, 1nat]);
    assert forall|a: Addr| #[trigger] s.heap.contains_key(a) implies footprint(s.heap, ps, a) by {
        if a == 1 {
            assert(below_mut(s.heap, ps, 1));
        }
    }
    assert forall|m: Addr| is_mut_root(ps, m) implies m == 0 by {}
}

/// The effect of `d.damage(10)` in the concrete run frees the ring.
pub proof fn lemma_damage_effect()
    ensures
        callee_effect(t2(), arg_ptrs(t2(), damage_args()), h_damaged(), 2),
{
    let ps = arg_ptrs(t2(), damage_args());
    assert(ps[0] == (ptr_to(st0().heap, 0), true));
    lemma_free_ring_effect(t2(), ps);
}

/// The step of `d.damage(10)` in the concrete run.
pub proof fn lemma_damage_step_3()
    ensures
        step(t2(), damage_bad()[3], t4()),
{
    let args = damage_args();
    lemma_damage_effect();
    assert(damage_bad()[3] == Instr::Call { args, ret: None });
    assert forall|k: int| 0 <= k < args.len() implies !#[trigger] dangling(t2(), args[k].0) by {
        assert(k == 0);
    }
    let ps = arg_ptrs(t2(), args);
    assert(call_result(t2(), ps, None, h_damaged(), 2, t4()));
    assert(call_step(t2(), ps, None, t4()));
    let i = Instr::Call { args, ret: None };
    let s = t2();
    let s2 = t4();
    assert((forall|k: int| 0 <= k < args.len() ==> !#[trigger] dangling(s, args[k].0)));
    assert(i is Call);
    assert(i->Call_args == args);
    assert(i->Call_ret == None::<Ret>);
    assert(step(s, i, s2));
}

/// The read of `d.hp` steps, and the read of `ring` is UB.
pub proof fn lemma_damage_steps_4_5()
    ensures
        step(t4(), damage_bad()[4], t4()),
        ub(t4(), damage_bad()[5]),
{
    assert(damage_bad()[5] == Instr::Read { src: RING(), field: 0 });
    assert(!t4().heap.contains_key(1nat));
}

/// A concrete execution of the rejected program in which `damage` frees the
/// ring: without the invalidation rule, this would be a use-after-free.
pub proof fn example_damage_bad_is_ub() -> (trace: Seq<DState>)
    ensures
        is_trace(damage_bad(), trace),
        trace[0] == st0(),
        wf(trace[0]),
        trace.len() == 6,
        ub(trace[5], damage_bad()[5]),
{
    hide(step);
    hide(wf);
    hide(ub);
    hide(st0);
    hide(t1);
    hide(t2);
    hide(t4);
    lemma_st0_wf();
    lemma_damage_steps_0_2();
    lemma_damage_step_3();
    lemma_damage_steps_4_5();
    let p = damage_bad();
    let trace = seq![st0(), t1(), t2(), t2(), t4(), t4()];
    assert(trace[0] == st0() && trace[1] == t1() && trace[2] == t2() && trace[3] == t2()
        && trace[4] == t4() && trace[5] == t4());
    assert forall|k: int| 0 <= k < trace.len() - 1 implies step(#[trigger] trace[k], p[k], trace[k + 1]) by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else {}
    }
    trace
}

/// The same execution, cut before the offending read, satisfies every
/// hypothesis of the soundness theorem (so they are jointly satisfiable), and
/// the theorem certifies it UB-free.
pub proof fn example_soundness_applies()
    ensures
        exists|trace: Seq<DState>|
            #![trigger is_trace(damage_prefix(), trace)]
            is_trace(damage_prefix(), trace) && trace.len() == 6 && forall|k: int|
                0 <= k < 5 ==> !#[trigger] ub(trace[k], damage_prefix()[k]),
{
    hide(step);
    let trace = example_damage_bad_is_ub();
    let p = damage_prefix();
    assert forall|j: int| 0 <= j < p.len() implies #[trigger] p[j] == damage_bad()[j] by {}
    assert(is_trace(p, trace)) by {
        assert forall|k: int| 0 <= k < trace.len() - 1 implies step(#[trigger] trace[k], p[k], trace[k + 1]) by {
            assert(step(trace[k], damage_bad()[k], trace[k + 1]));
        }
    }
    example_damage_ok();
    lemma_st0_wf();
    assert(initial_sstate(trace[0]) == ss0()) by {
        assert(st0().locals.dom() =~= Set::empty().insert(D()));
    }
    soundness_from_start(p, trace);
}

// ---------------------------------------------------------------------------
// 3. Mutable aliasing: `attack(entities[i], entities[j])` with i == j allowed.
//    Rust rejects two simultaneous `&mut` here; group borrowing accepts, and
//    both references stay usable afterwards.
// ---------------------------------------------------------------------------

/// The child group `entities`.
pub open spec fn ENTS() -> Label { 2 }

/// `attack(entities[i], entities[j])` with two mutable references that may alias.
pub open spec fn attack() -> Seq<Instr> {
    seq![
        Instr::Borrow { dst: RD(), x: D() },
        Instr::Child { dst: A(), src: RD(), label: ENTS() },   // a = &entities[rand()]
        Instr::Child { dst: B(), src: RD(), label: ENTS() },   // b = &entities[rand()]
        Instr::Call { args: seq![(A(), true), (B(), true)], ret: None },  // attack(a, b)
        Instr::Read { src: A(), field: 0 },
        Instr::Read { src: B(), field: 0 },
    ]
}

/// The checker accepts `attack` (Rust rejects it).
pub proof fn example_mutable_aliasing_ok()
    ensures
        check(ss0(), attack()),
{
    let p = attack();
    let s0 = ss0();
    let s1 = post(s0, p[0]);
    let s2 = post(s1, p[1]);
    let s3 = post(s2, p[2]);
    let s4 = post(s3, p[3]);
    let s5 = post(s4, p[4]);
    let ge = g(D(), seq![ENTS()]);
    assert(s1.vars =~= map![RD() => g(D(), seq![])]);
    assert(s3.vars =~= map![RD() => g(D(), seq![]), A() => ge, B() => ge]);
    let args = seq![(A(), true), (B(), true)];
    let gs = arg_groups(s3, args);
    assert(gs[0] == (ge, true) && gs[1] == (ge, true));
    assert(!strict_child(g(D(), seq![]), ge));
    assert(!strict_child(ge, ge));
    assert(!killed(gs, ge));
    assert(!killed(gs, g(D(), seq![])));
    assert(s4.vars =~= s3.vars);
    assert(s4.clos =~= s3.clos);
    assert(s5 == s4);
    assert forall|k: nat| k < p.len() implies #[trigger] instr_ok(ss_at(s0, p, k), p[k as int]) by {
        assert(ss_at(s0, p, 0) == s0);
        assert(ss_at(s0, p, 1) == s1);
        assert(ss_at(s0, p, 2) == s2);
        assert(ss_at(s0, p, 3) == s3);
        assert(ss_at(s0, p, 4) == s4);
        assert(ss_at(s0, p, 5) == s5);
    }
}

// ---------------------------------------------------------------------------
// 4. `power_up_ring(d, d.rings[0])`: mutating a child group (d.rings*) leaves
//    references into a sibling child group (d.armor*) valid.
// ---------------------------------------------------------------------------

/// `power_up_ring(d, mut d.rings[0])`, then reads of `arm` and `ring`.
pub open spec fn power_up() -> Seq<Instr> {
    seq![
        Instr::Borrow { dst: RD(), x: D() },
        Instr::Child { dst: RING(), src: RD(), label: RINGS() },
        Instr::Child { dst: ARM(), src: RD(), label: ARMOR() },
        Instr::Call { args: seq![(RD(), false), (RING(), true)], ret: None },
        Instr::Read { src: ARM(), field: 0 },
        Instr::Read { src: RING(), field: 0 },
    ]
}

/// The checker accepts `power_up`: a sibling child group stays valid.
pub proof fn example_power_up_ok()
    ensures
        check(ss0(), power_up()),
{
    let p = power_up();
    let s0 = ss0();
    let s1 = post(s0, p[0]);
    let s2 = post(s1, p[1]);
    let s3 = post(s2, p[2]);
    let s4 = post(s3, p[3]);
    let s5 = post(s4, p[4]);
    let gd = g(D(), seq![]);
    let gr = g(D(), seq![RINGS()]);
    let ga = g(D(), seq![ARMOR()]);
    assert(s1.vars =~= map![RD() => gd]);
    assert(s2.vars =~= map![RD() => gd, RING() => gr]);
    assert(s3.vars =~= map![RD() => gd, RING() => gr, ARM() => ga]);
    let args = seq![(RD(), false), (RING(), true)];
    let gs = arg_groups(s3, args);
    assert(gs[0] == (gd, false) && gs[1] == (gr, true));
    assert(!strict_child(ga, gr)) by {
        assert(ga.path.subrange(0, 1) =~= seq![ARMOR()]);
    }
    assert(!killed(gs, ga));
    assert(!killed(gs, gr));
    assert(!killed(gs, gd));
    assert(s4.vars =~= s3.vars);
    assert(s4.clos =~= s3.clos);
    assert(s5 == s4);
    assert forall|k: nat| k < p.len() implies #[trigger] instr_ok(ss_at(s0, p, k), p[k as int]) by {
        assert(ss_at(s0, p, 0) == s0);
        assert(ss_at(s0, p, 1) == s1);
        assert(ss_at(s0, p, 2) == s2);
        assert(ss_at(s0, p, 3) == s3);
        assert(ss_at(s0, p, 4) == s4);
        assert(ss_at(s0, p, 5) == s5);
    }
}

} // verus!
