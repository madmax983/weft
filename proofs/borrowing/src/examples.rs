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
pub open spec fn D() -> Local { 0 }

// labels (child groups of Entity)
pub open spec fn RINGS() -> Label { 0 }
pub open spec fn ARMOR() -> Label { 1 }

// reference variables
pub open spec fn RD() -> Var { 0 }
pub open spec fn RING() -> Var { 1 }
pub open spec fn ARM() -> Var { 2 }
pub open spec fn A() -> Var { 3 }
pub open spec fn B() -> Var { 4 }

pub open spec fn ss0() -> SState {
    SState { locals: Set::empty().insert(D()), vars: Map::empty() }
}

pub open spec fn g(root: Local, path: Seq<Label>) -> Group {
    Group { root, path }
}

// ---------------------------------------------------------------------------
// 1. `d.damage(10)` keeps references to `d` alive but kills `ring_ref`.
// ---------------------------------------------------------------------------

pub open spec fn damage_prefix() -> Seq<Instr> {
    seq![
        Instr::Borrow { dst: RD(), x: D() },                    // rd   = &d          : d
        Instr::Child { dst: RING(), src: RD(), label: RINGS() }, // ring = &d.rings[i] : d.rings*
        Instr::Read { src: RING(), field: 0 },
        Instr::Call { args: seq![(RD(), true)], ret: None },    // d.damage(10)
        Instr::Read { src: RD(), field: 0 },                    // d.hp: still fine
    ]
}

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
    assert(seq![RINGS()].subrange(0, 0) =~= Seq::<Label>::empty());
    assert(strict_child(g(D(), seq![RINGS()]), g(D(), seq![])));
    assert(s3.vars[args[0].0] == g(D(), seq![]));
    assert(killed(s3, args, s3.vars[RING()]));
    assert(!strict_child(g(D(), seq![]), g(D(), seq![])));
    assert(!killed(s3, args, s3.vars[RD()]));
    assert(s4.vars =~= map![RD() => g(D(), seq![])]);
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

proof fn lemma_ss_at_prefix(ss: SState, p: Seq<Instr>, q: Seq<Instr>, k: nat)
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

pub open spec fn entity() -> Obj {
    Obj { stamp: 0, ty: 0, data: seq![100], kids: seq![(RINGS(), 1nat)] }
}

pub open spec fn ring() -> Obj {
    Obj { stamp: 1, ty: 1, data: seq![5], kids: seq![] }
}

pub open spec fn damaged() -> Obj {
    Obj { stamp: 0, ty: 0, data: seq![90], kids: seq![] }
}

pub open spec fn st0() -> DState {
    DState {
        heap: map![0nat => entity(), 1nat => ring()],
        locals: map![D() => 0nat],
        vars: Map::empty(),
        next_stamp: 2,
    }
}

proof fn lemma_st0_wf()
    ensures
        wf(st0()),
{
    let h = st0().heap;
    assert(h.dom() =~= set![0nat, 1nat]);
    assert forall|b: Addr, i: int, c: Addr| #[trigger] owns(h, b, i, c) implies b == 0 && i == 0 && c == 1 by {}
}

pub open spec fn t1() -> DState {
    DState { vars: map![RD() => ptr_to(st0().heap, 0)], ..st0() }
}

pub open spec fn t2() -> DState {
    DState { vars: map![RD() => ptr_to(st0().heap, 0), RING() => ptr_to(st0().heap, 1)], ..st0() }
}

pub open spec fn h_damaged() -> Heap {
    map![0nat => damaged()]
}

pub open spec fn t4() -> DState {
    DState { heap: h_damaged(), ..t2() }
}

pub open spec fn damage_args() -> Seq<(Var, bool)> {
    seq![(RD(), true)]
}

proof fn lemma_damage_steps_0_2()
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

proof fn lemma_damage_effect()
    ensures
        callee_effect(t2(), damage_args(), h_damaged(), 2),
{
    let args = damage_args();
    let t2 = t2();
    let h2 = h_damaged();
    let t4 = DState { heap: h2, locals: t2.locals, vars: t2.vars, next_stamp: 2 };
    assert(h2.dom() =~= set![0nat]);
    assert forall|b: Addr, i: int, c: Addr| !#[trigger] owns(h2, b, i, c) by {}
    assert(wf(t4));
    assert(t2.vars[args[0].0].addr == 0);
    assert(is_mut_root(t2, args, 0));
    let r1 = seq![(RINGS(), 0nat)];
    assert(r1.drop_last() =~= Seq::<Step>::empty());
    assert(resolve(t2.heap, 0, Seq::<Step>::empty()) == Some(0nat));
    assert(resolve(t2.heap, 0, r1) == Some(1nat));
    assert(below(t2.heap, 0, 1));
    assert(below_mut(t2, args, 1));
    assert(t2.heap.dom() =~= set![0nat, 1nat]);
    assert forall|a: Addr| #[trigger] t2.heap.contains_key(a) implies footprint(t2, args, a) by {
        if a == 1 {
            assert(below_mut(t2, args, 1));
        }
    }
    assert forall|m: Addr| is_mut_root(t2, args, m) implies m == 0 by {}
}

proof fn lemma_damage_step_3()
    ensures
        step(t2(), damage_bad()[3], t4()),
{
    let args = damage_args();
    lemma_damage_effect();
    assert(damage_bad()[3] == Instr::Call { args, ret: None });
    assert forall|k: int| 0 <= k < args.len() implies !#[trigger] dangling(t2(), args[k].0) by {
        assert(k == 0);
    }
    assert(call_result(t2(), args, None, h_damaged(), 2, t4()));
    assert(exists|h2: Heap, n2: Stamp|
        #[trigger] callee_effect(t2(), args, h2, n2) && call_result(t2(), args, None, h2, n2, t4()));
    let i = Instr::Call { args, ret: None };
    let s = t2();
    let s2 = t4();
    assert((forall|k: int| 0 <= k < args.len() ==> !#[trigger] dangling(s, args[k].0)));
    assert(exists|h2: Heap, n2: Stamp|
        #[trigger] callee_effect(s, args, h2, n2) && call_result(s, args, None, h2, n2, s2));
    assert(i is Call);
    assert(i->Call_args == args);
    assert(i->Call_ret == None::<Ret>);
    assert(step(s, i, s2));
}

proof fn lemma_damage_steps_4_5()
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

pub open spec fn ENTS() -> Label { 2 }

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
    assert(!strict_child(g(D(), seq![]), ge));
    assert(!strict_child(ge, ge));
    assert(!killed(s3, args, ge));
    assert(!killed(s3, args, g(D(), seq![])));
    assert(s4.vars =~= s3.vars);
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
    assert(!strict_child(ga, gr)) by {
        assert(ga.path.subrange(0, 1) =~= seq![ARMOR()]);
    }
    assert(!killed(s3, args, ga));
    assert(!killed(s3, args, gr));
    assert(!killed(s3, args, gd));
    assert(s4.vars =~= s3.vars);
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
