//! B4 sanity checks.
//!
//! * Accepted: task 0 runs `power_up(mut ring)` (group `d.rings*`), task 1
//!   writes `armor.hp` (group `d.armor*`). The groups do not overlap.
//! * Rejected: task 0 runs `d.damage(10)` (group `d`), task 1 reads `ring`
//!   (group `d.rings*`). Each task alone passes the checker, but `d` is a
//!   prefix of `d.rings*`, so the separation rule fails.
//! * The rule is necessary: in a concrete interleaving of the rejected pair,
//!   task 0 frees the ring that task 1 reaches (a data race), and then task 1
//!   reads it (UB).
//! * The hypotheses of `task_soundness` are satisfiable: an interleaving of
//!   the accepted pair meets all of them.

#![allow(non_snake_case)]

use vstd::prelude::*;
use crate::model::*;
use crate::soundness::*;
use crate::examples::*;
use crate::progress::*;
use crate::tasks::*;

verus! {

/// The group `d`.
pub open spec fn gd() -> Group {
    g(D(), seq![])
}

/// The group `d.rings*`.
pub open spec fn gr() -> Group {
    g(D(), seq![RINGS()])
}

/// The group `d.armor*`.
pub open spec fn ga() -> Group {
    g(D(), seq![ARMOR()])
}

/// A checker state with the variables `vars`.
pub open spec fn sv(vars: Map<Var, Group>) -> SState {
    SState { vars, ..ss0() }
}

/// A task with the variables `vars` at the program counter `pc`.
pub open spec fn task_of(vars: Map<Var, Ptr>, pc: nat) -> Task {
    Task { vars, clos: Map::empty(), pc }
}

// ---------------------------------------------------------------------------
// Programs
// ---------------------------------------------------------------------------

/// Task 0 of the accepted pair: `power_up(mut ring)`.
pub open spec fn pa() -> Seq<Instr> {
    seq![Instr::Call { args: seq![(RING(), true)], ret: None }]
}

/// Task 1 of the accepted pair: `armor.hp = 7`.
pub open spec fn pb() -> Seq<Instr> {
    seq![Instr::Write { src: ARM(), field: 0, val: 7 }]
}

/// Task 0 of the rejected pair: `d.damage(10)`.
pub open spec fn pa_bad() -> Seq<Instr> {
    seq![Instr::Call { args: seq![(RD(), true)], ret: None }]
}

/// Task 1 of the rejected pair: `read ring`.
pub open spec fn pb_bad() -> Seq<Instr> {
    seq![Instr::Read { src: RING(), field: 0 }]
}

proof fn lemma_groups()
    ensures
        !overlap(gr(), ga()),
        !overlap(ga(), gr()),
        overlap(gd(), gr()),
        !strict_child(gr(), gr()),
        !strict_child(ga(), ga()),
{
    assert(seq![RINGS()][0] != seq![ARMOR()][0]);
    assert(!seq![RINGS()].is_prefix_of(seq![ARMOR()])) by {
        assert(seq![ARMOR()].subrange(0, 1)[0] == ARMOR());
    }
    assert(!seq![ARMOR()].is_prefix_of(seq![RINGS()])) by {
        assert(seq![RINGS()].subrange(0, 1)[0] == RINGS());
    }
    assert(Seq::<Label>::empty().is_prefix_of(seq![RINGS()])) by {
        assert(Seq::<Label>::empty() =~= seq![RINGS()].subrange(0, 0));
    }
}

/// Each task passes the checker on its own.
pub proof fn example_tasks_checked()
    ensures
        check(sv(map![RING() => gr()]), pa()),
        check(sv(map![ARM() => ga()]), pb()),
        check(sv(map![RD() => gd()]), pa_bad()),
        check(sv(map![RING() => gr()]), pb_bad()),
{
    let s = sv(map![RING() => gr()]);
    assert(instr_ok(s, pa()[0])) by {
        let args = pa()[0]->Call_args;
        assert(s.vars.contains_key(args[0].0));
    }
    assert(ss_at(s, pa(), 0) == s);
    let sb = sv(map![ARM() => ga()]);
    assert(ss_at(sb, pb(), 0) == sb);
    let sd = sv(map![RD() => gd()]);
    assert(instr_ok(sd, pa_bad()[0])) by {
        let args = pa_bad()[0]->Call_args;
        assert(sd.vars.contains_key(args[0].0));
    }
    assert(ss_at(sd, pa_bad(), 0) == sd);
    assert(ss_at(s, pb_bad(), 0) == s);
}

/// The accepted pair follows the separation rule, in both directions.
pub proof fn example_separated()
    ensures
        separated(sv(map![RING() => gr()]), pa(), sv(map![ARM() => ga()]), pb()),
        separated(sv(map![ARM() => ga()]), pb(), sv(map![RING() => gr()]), pa()),
{
    lemma_groups();
    let sa = sv(map![RING() => gr()]);
    let sb = sv(map![ARM() => ga()]);
    // the checker states of each task, before and after its instruction
    let args = pa()[0]->Call_args;
    let gs = arg_groups(sa, args);
    assert(gs =~= seq![(gr(), true)]);
    assert(!killed(gs, gr()));
    assert(post(sa, pa()[0]).vars =~= sa.vars);
    assert(post(sa, pa()[0]).clos =~= sa.clos);
    assert(ss_at(sa, pa(), 1) == post(ss_at(sa, pa(), 0), pa()[0]));
    assert(ss_at(sa, pa(), 0) == sa);
    assert(ss_at(sb, pb(), 1) == post(ss_at(sb, pb(), 0), pb()[0]));
    assert(ss_at(sb, pb(), 0) == sb);
    assert forall|m: nat, h: Group| m <= 1 && #[trigger] held(ss_at(sa, pa(), m), h) implies h == gr() by {
        assert(ss_at(sa, pa(), m) == sa);
    }
    assert forall|m: nat, h: Group| m <= 1 && #[trigger] held(ss_at(sb, pb(), m), h) implies h == ga() by {
        assert(ss_at(sb, pb(), m) == sb);
    }
    assert forall|k: nat, m: nat, gg: Group, h: Group|
        k < pa().len() && m <= pb().len() && #[trigger] mut_group(ss_at(sa, pa(), k), pa()[k as int], gg) && #[trigger] held(
            ss_at(sb, pb(), m),
            h,
        ) implies !overlap(gg, h) by {
        assert(k == 0);
        assert(eff_groups(sa, pa()[0]) == gs);
        assert(gg == gr());
    }
    assert forall|k: nat, m: nat, gg: Group, h: Group|
        k < pb().len() && m <= pa().len() && #[trigger] mut_group(ss_at(sb, pb(), k), pb()[k as int], gg) && #[trigger] held(
            ss_at(sa, pa(), m),
            h,
        ) implies !overlap(gg, h) by {
        assert(k == 0);
        assert(eff_groups(sb, pb()[0]) =~= seq![(ga(), true)]);
        assert(gg == ga());
    }
}

/// The rejected pair breaks the separation rule: `d` overlaps `d.rings*`.
pub proof fn example_not_separated()
    ensures
        !separated(sv(map![RD() => gd()]), pa_bad(), sv(map![RING() => gr()]), pb_bad()),
{
    lemma_groups();
    let sa = sv(map![RD() => gd()]);
    let sb = sv(map![RING() => gr()]);
    let args = pa_bad()[0]->Call_args;
    assert(ss_at(sa, pa_bad(), 0) == sa);
    assert(ss_at(sb, pb_bad(), 0) == sb);
    let eg = eff_groups(sa, pa_bad()[0]);
    assert(eg[0] == (gd(), true));
    assert(eg.len() == 1 && eg[0].1 && eg[0].0 == gd());
    assert(mut_group(sa, pa_bad()[0], gd()));
    assert(mut_group(ss_at(sa, pa_bad(), 0), pa_bad()[0], gd()));
    assert(sb.vars.contains_key(RING()) && sb.vars[RING()] == gr());
    assert(held(ss_at(sb, pb_bad(), 0), gr()));
}

// ---------------------------------------------------------------------------
// A data race and a UB in the rejected pair
// ---------------------------------------------------------------------------

/// Task 0 holds `rd`, task 1 holds `ring`, on the heap of `st0`.
pub open spec fn tbad0() -> TState {
    TState {
        heap: st0().heap,
        locals: st0().locals,
        next_stamp: 2,
        t0: task_of(map![RD() => ptr_to(st0().heap, 0)], 0),
        t1: task_of(map![RING() => ptr_to(st0().heap, 1)], 0),
    }
}

/// After task 0 ran `d.damage(10)`: the ring is freed.
pub open spec fn tbad1() -> TState {
    TState { heap: h_damaged(), t0: task_of(map![RD() => ptr_to(st0().heap, 0)], 1), ..tbad0() }
}

/// A concrete interleaving of the rejected pair: task 0 frees the ring that
/// task 1 reaches (a data race), then the read of task 1 is UB.
pub proof fn example_race_is_ub()
    ensures
        is_itrace(pa_bad(), pb_bad(), seq![0nat], seq![tbad0(), tbad1()]),
        inv(tview(tbad0(), 0), sv(map![RD() => gd()])),
        inv(tview(tbad0(), 1), sv(map![RING() => gr()])),
        writes(tview(tbad0(), 0), pa_bad()[0], 1),
        reach(tview(tbad0(), 1), sv(map![RING() => gr()]), 1),
        ub(tview(tbad1(), 1), pb_bad()[tbad1().t1.pc as int]),
{
    lemma_st0_wf();
    let ts = tbad0();
    let d = tview(ts, 0);
    let args = pa_bad()[0]->Call_args;
    let ps = arg_ptrs(d, args);
    assert(ps[0] == (ptr_to(st0().heap, 0), true));
    lemma_free_ring_effect(d, ps);
    let d2 = DState { heap: h_damaged(), next_stamp: 2, ..d };
    assert(call_result(d, ps, None, h_damaged(), 2, d2));
    assert(call_step(d, ps, None, d2));
    assert forall|k: int| 0 <= k < args.len() implies !#[trigger] dangling(d, args[k].0) by {
        assert(k == 0);
    }
    assert(step(d, pa_bad()[0], d2));
    assert(merge(ts, 0, d2) == tbad1());
    assert(tstep(pa_bad(), pb_bad(), ts, 0, tbad1()));
    // the invariants of the two tasks
    let e = Seq::<Step>::empty();
    assert(labels(e) =~= Seq::<Label>::empty());
    assert(resolve(d.heap, d.locals[D()], e) == Some(0nat));
    assert(ref_ok(d, gd(), RD()));
    assert(sv(map![RD() => gd()]).locals =~= d.locals.dom());
    let d1 = tview(ts, 1);
    let r1 = seq![(RINGS(), 0nat)];
    assert(r1.drop_last() =~= e);
    assert(resolve(d1.heap, d1.locals[D()], r1) == Some(1nat));
    assert(labels(r1) =~= seq![RINGS()]);
    assert(ref_ok(d1, gr(), RING()));
    // the race: the call can free the ring, and task 1 reaches it
    assert(resolve(d.heap, 0, r1) == Some(1nat));
    assert(below(d.heap, 0, 1));
    assert(is_mut_root(ps, 0));
    assert(below_mut(d.heap, ps, 1));
    assert(resolve(d1.heap, d1.vars[RING()].addr, e) == Some(1nat));
    assert(reaches_from(d1.heap, d1.vars[RING()].addr, 1));
    assert(!h_damaged().contains_key(1nat));
}

// ---------------------------------------------------------------------------
// The theorem applies to the accepted pair
// ---------------------------------------------------------------------------

/// An entity with a ring and an armor.
pub open spec fn entity3() -> Obj {
    Obj { stamp: 0, ty: 0, data: seq![100], kids: seq![(RINGS(), 1nat), (ARMOR(), 2nat)] }
}

/// An armor.
pub open spec fn armor() -> Obj {
    Obj { stamp: 2, ty: 2, data: seq![3], kids: seq![] }
}

/// The heap with the entity, its ring and its armor.
pub open spec fn h3() -> Heap {
    map![0nat => entity3(), 1nat => ring(), 2nat => armor()]
}

/// The start state of the accepted pair.
pub open spec fn tok0() -> TState {
    TState {
        heap: h3(),
        locals: map![D() => 0nat],
        next_stamp: 3,
        t0: task_of(map![RING() => ptr_to(h3(), 1)], 0),
        t1: task_of(map![ARM() => ptr_to(h3(), 2)], 0),
    }
}

/// After task 0 ran `power_up(mut ring)` (a callee that changes nothing).
pub open spec fn tok1() -> TState {
    TState { t0: task_of(map![RING() => ptr_to(h3(), 1)], 1), ..tok0() }
}

/// The heap after the write of `armor.hp`.
pub open spec fn h3w() -> Heap {
    h3().insert(2nat, Obj { data: armor().data.update(0, 7), ..armor() })
}

/// After task 1 wrote `armor.hp = 7`.
pub open spec fn tok2() -> TState {
    TState { heap: h3w(), t1: task_of(map![ARM() => ptr_to(h3(), 2)], 1), ..tok1() }
}

/// The interleaving of the accepted pair.
pub open spec fn tok_trace() -> Seq<TState> {
    seq![tok0(), tok1(), tok2()]
}

proof fn lemma_h3_wf()
    ensures
        wf(tview(tok0(), 0)),
{
    let h = h3();
    assert(h.dom() =~= set![0nat, 1nat, 2nat]);
    assert forall|b: Addr, i: int, c: Addr| #[trigger] owns(h, b, i, c) implies b == 0 && ((i == 0 && c == 1) || (i == 1
        && c == 2)) by {}
}

proof fn lemma_tok_inv()
    ensures
        inv(tview(tok0(), 0), sv(map![RING() => gr()])),
        inv(tview(tok0(), 1), sv(map![ARM() => ga()])),
{
    lemma_h3_wf();
    let d0 = tview(tok0(), 0);
    let d1 = tview(tok0(), 1);
    let e = Seq::<Step>::empty();
    assert(resolve(h3(), 0, e) == Some(0nat));
    let r1 = seq![(RINGS(), 0nat)];
    assert(r1.drop_last() =~= e);
    assert(resolve(d0.heap, d0.locals[D()], r1) == Some(1nat));
    assert(labels(r1) =~= seq![RINGS()]);
    assert(ref_ok(d0, gr(), RING()));
    let r2 = seq![(ARMOR(), 1nat)];
    assert(r2.drop_last() =~= e);
    assert(resolve(d1.heap, d1.locals[D()], r2) == Some(2nat));
    assert(labels(r2) =~= seq![ARMOR()]);
    assert(ref_ok(d1, ga(), ARM()));
    assert(sv(map![RING() => gr()]).locals =~= d0.locals.dom());
}

proof fn lemma_tok_steps()
    ensures
        is_itrace(pa(), pb(), seq![0nat, 1nat], tok_trace()),
{
    lemma_h3_wf();
    // task 0: the callee changes nothing
    let d = tview(tok0(), 0);
    let args = pa()[0]->Call_args;
    let ps = arg_ptrs(d, args);
    assert(ps[0] == (ptr_to(h3(), 1), true));
    assert forall|k: int| 0 <= k < ps.len() implies d.heap.contains_key(#[trigger] ps[k].0.addr) by {
        assert(k == 0);
    }
    lemma_identity_effect(d, ps);
    assert(call_result(d, ps, None, d.heap, d.next_stamp, d));
    assert(call_step(d, ps, None, d));
    assert forall|k: int| 0 <= k < args.len() implies !#[trigger] dangling(d, args[k].0) by {
        assert(k == 0);
    }
    assert(step(d, pa()[0], d));
    assert(merge(tok0(), 0, d) == tok1());
    assert(tstep(pa(), pb(), tok0(), 0, tok1()));
    // task 1: the write
    let d1 = tview(tok1(), 1);
    let d2 = DState { heap: h3w(), ..d1 };
    assert(step(d1, pb()[0], d2));
    assert(merge(tok1(), 1, d2) == tok2());
    assert(tstep(pa(), pb(), tok1(), 1, tok2()));
    let trace = seq![tok0(), tok1(), tok2()];
    let sched = seq![0nat, 1nat];
    assert forall|k: int| 0 <= k < sched.len() implies tstep(pa(), pb(), #[trigger] trace[k], sched[k], trace[k + 1]) by {
        if k == 0 {} else {}
    }
}

/// An interleaving of the accepted pair meets every hypothesis of
/// `task_soundness`, so the theorem applies to it.
pub proof fn example_task_soundness_applies()
    ensures
        forall|k: int, t: nat|
            0 <= k < 3 && t < 2 && #[trigger] task(tok_trace()[k], t).pc < prog_of(pa(), pb(), t).len() ==> !ub(
                tview(tok_trace()[k], t),
                prog_of(pa(), pb(), t)[task(tok_trace()[k], t).pc as int],
            ),
{
    lemma_tok_inv();
    lemma_tok_steps();
    example_tasks_checked();
    example_separated();
    assert(tok_trace()[0] == tok0());
    task_soundness(pa(), pb(), sv(map![RING() => gr()]), sv(map![ARM() => ga()]), seq![0nat, 1nat], tok_trace());
}

} // verus!
