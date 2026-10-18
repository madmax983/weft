//! B1 sanity checks: loops.
//!
//! * `loop_ok` binds `ring` inside the loop. The checker accepts it.
//! * `loop_bad` binds `ring` before the loop. The back edge brings the state
//!   after `d.damage(10)`, where `ring` is killed, so the join kills `ring`.
//!   No annotation makes the checker accept it.
//! * The rule is necessary: a concrete run of `loop_bad` reads the freed ring.
//! * The hypotheses of `cfg_soundness_from_start` are satisfiable: a run of
//!   `loop_ok` that takes the back edge meets all of them.

#![allow(non_snake_case)]

use vstd::prelude::*;
use crate::model::*;
use crate::soundness::*;
use crate::examples::*;
use crate::cfg::*;

verus! {

/// A CFG node.
pub open spec fn cnode(instr: Instr, succs: Seq<nat>) -> Node {
    Node { instr, succs }
}

/// `read ring`.
pub open spec fn read_ring() -> Instr {
    Instr::Read { src: RING(), field: 0 }
}

/// `d.damage(10)`: a call with `rd` as a mutable argument.
pub open spec fn damage_call() -> Instr {
    Instr::Call { args: seq![(RD(), true)], ret: None }
}

/// ```text
/// 0: rd = &d
/// 1: ring = &d.rings[i]       <- loop head
/// 2: read ring
/// 3: d.damage(10)             -> 1 (loop) or 4 (exit)
/// 4: read rd
/// ```
pub open spec fn loop_ok() -> Cfg {
    seq![
        cnode(Instr::Borrow { dst: RD(), x: D() }, seq![1nat]),
        cnode(Instr::Child { dst: RING(), src: RD(), label: RINGS() }, seq![2nat]),
        cnode(read_ring(), seq![3nat]),
        cnode(damage_call(), seq![1nat, 4nat]),
        cnode(Instr::Read { src: RD(), field: 0 }, seq![]),
    ]
}

/// ```text
/// 0: rd = &d
/// 1: ring = &d.rings[i]
/// 2: read ring                <- loop head: use after free on iteration 2
/// 3: d.damage(10)             -> 2 (loop) or 4 (exit)
/// 4: read rd
/// ```
pub open spec fn loop_bad() -> Cfg {
    seq![
        cnode(Instr::Borrow { dst: RD(), x: D() }, seq![1nat]),
        cnode(Instr::Child { dst: RING(), src: RD(), label: RINGS() }, seq![2nat]),
        cnode(read_ring(), seq![3nat]),
        cnode(damage_call(), seq![2nat, 4nat]),
        cnode(Instr::Read { src: RD(), field: 0 }, seq![]),
    ]
}

/// A checker state with the locals of `ss0` and no closure values.
pub open spec fn sd(vars: Map<Var, Group>) -> SState {
    SState { vars, ..ss0() }
}

/// The group `d`.
pub open spec fn gd() -> Group {
    g(D(), seq![])
}

/// The group `d.rings*`.
pub open spec fn gr() -> Group {
    g(D(), seq![RINGS()])
}

/// The fixpoint of the intersection join for `loop_ok`.
pub open spec fn ann_ok() -> Seq<SState> {
    seq![
        sd(map![]),
        sd(map![RD() => gd()]),
        sd(map![RD() => gd(), RING() => gr()]),
        sd(map![RD() => gd(), RING() => gr()]),
        sd(map![RD() => gd()]),
    ]
}

proof fn lemma_kill_ring(ss: SState)
    requires
        ss.vars.contains_key(RD()),
        ss.vars[RD()] == gd(),
    ensures
        killed(arg_groups(ss, damage_call()->Call_args), gr()),
        !killed(arg_groups(ss, damage_call()->Call_args), gd()),
{
    let args = damage_call()->Call_args;
    let gs = arg_groups(ss, args);
    assert(gs[0] == (gd(), true));
    assert(gr().path.subrange(0, 0) =~= Seq::<Label>::empty());
    assert(strict_child(gr(), gs[0].0));
    assert(!strict_child(gd(), gd()));
}

/// The checker accepts `loop_ok`.
pub proof fn example_loop_ok()
    ensures
        cfg_check(loop_ok(), ss0(), ann_ok()),
{
    let c = loop_ok();
    let a = ann_ok();
    let p0 = post(a[0], c[0].instr);
    let p1 = post(a[1], c[1].instr);
    let p3 = post(a[3], c[3].instr);
    assert(p0.vars =~= map![RD() => gd()]);
    assert(seq![].push(RINGS()) =~= seq![RINGS()]);
    assert(p1.vars =~= map![RD() => gd(), RING() => gr()]);
    lemma_kill_ring(a[3]);
    assert(p3.vars =~= map![RD() => gd()]);
    assert forall|n: int| 0 <= n < c.len() implies #[trigger] instr_ok(a[n], c[n].instr) by {
        if n == 3 {
            assert(a[3].vars.contains_key(seq![(RD(), true)][0].0));
        }
    }
    assert forall|n: int, j: int| 0 <= n < c.len() && 0 <= j < c[n].succs.len() implies #[trigger] c[n].succs[j]
        < c.len() && sub_state(a[c[n].succs[j] as int], post(a[n], c[n].instr)) by {
        if n == 3 {
            assert(j == 0 || j == 1);
        }
    }
}

proof fn lemma_damage_call_needs_rd(ss: SState)
    requires
        instr_ok(ss, damage_call()),
    ensures
        ss.vars.contains_key(RD()),
{
    let args = damage_call()->Call_args;
    assert(args[0].0 == RD());
    assert(ss.vars.contains_key(args[0].0));
}

proof fn lemma_loop_bad_rejected(ann: Seq<SState>)
    ensures
        !cfg_check(loop_bad(), ss0(), ann),
{
    if cfg_check(loop_bad(), ss0(), ann) {
        let c = loop_bad();
        let args = damage_call()->Call_args;
        // edge 0 -> 1, and node 1 needs `rd`
        assert(c[0].succs[0] == 1);
        assert(sub_state(ann[1], post(ann[0], c[0].instr)));
        assert(c[0].instr == Instr::Borrow { dst: RD(), x: D() });
        assert(c[1].instr == Instr::Child { dst: RING(), src: RD(), label: RINGS() });
        assert(instr_ok(ann[1], c[1].instr));
        assert(ann[1].vars.contains_key(RD()));
        let p0 = post(ann[0], c[0].instr);
        assert(p0.vars[RD()] == gd());
        assert(ann[1].vars.submap_of(p0.vars));
        assert(p0.vars.dom().contains(RD()));
        assert(ann[1].vars[RD()] == gd());
        // edge 1 -> 2
        assert(c[1].succs[0] == 2);
        let p1 = post(ann[1], c[1].instr);
        assert(sub_state(ann[2], p1));
        assert(p1.vars[RING()] == gr()) by {
            assert(seq![].push(RINGS()) =~= seq![RINGS()]);
        }
        assert(p1.vars[RD()] == gd());
        // edge 2 -> 3 (a read changes nothing), and node 3 needs `rd`
        assert(c[2].succs[0] == 3);
        assert(sub_state(ann[3], post(ann[2], c[2].instr)));
        assert(c[2].instr == read_ring());
        assert(c[3].instr == Instr::Call { args, ret: None });
        lemma_damage_call_needs_rd(ann[3]);
        assert(ann[3].vars.dom().contains(RD()));
        assert(post(ann[2], c[2].instr) == ann[2]);
        assert(ann[2].vars.dom().contains(RD()));
        assert(p1.vars.dom().contains(RD()));
        assert(ann[2].vars[RD()] == gd());
        assert(ann[3].vars[RD()] == gd());
        // back edge 3 -> 2: `ring` must survive `d.damage(10)`
        assert(c[3].succs[0] == 2);
        assert(sub_state(ann[2], post(ann[3], c[3].instr)));
        assert(instr_ok(ann[2], c[2].instr));
        assert(ann[2].vars.contains_key(RING()));
        assert(post(ann[3], c[3].instr).vars.contains_key(RING()));
        assert(ann[3].vars.dom().contains(RING()));
        assert(p1.vars.dom().contains(RING()));
        assert(ann[2].vars[RING()] == gr());
        assert(ann[3].vars[RING()] == gr());
        lemma_kill_ring(ann[3]);
        assert(killed(arg_groups(ann[3], args), ann[3].vars[RING()]));
    }
}

/// No annotation makes the checker accept `loop_bad`.
pub proof fn example_loop_bad_rejected()
    ensures
        forall|ann: Seq<SState>| !#[trigger] cfg_check(loop_bad(), ss0(), ann),
{
    assert forall|ann: Seq<SState>| !#[trigger] cfg_check(loop_bad(), ss0(), ann) by {
        lemma_loop_bad_rejected(ann);
    }
}

/// A concrete run of `loop_bad`: `damage` frees the ring, the loop goes back,
/// and the read of `ring` is a use after free.
pub proof fn example_loop_bad_is_ub() -> (r: (Seq<nat>, Seq<DState>))
    ensures
        is_cfg_trace(loop_bad(), r.0, r.1),
        r.1[0] == st0(),
        wf(r.1[0]),
        r.1.len() == 5,
        r.0[4] == 2,
        ub(r.1[4], loop_bad()[r.0[4] as int].instr),
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
    let c = loop_bad();
    let p = damage_bad();
    assert(c[0].instr == p[0] && c[1].instr == p[1] && c[2].instr == p[2] && c[3].instr == p[3]
        && c[2].instr == p[5]);
    let path = seq![0nat, 1, 2, 3, 2];
    let trace = seq![st0(), t1(), t2(), t2(), t4()];
    assert forall|k: int| 0 <= k < trace.len() - 1 implies step(#[trigger] trace[k], c[path[k] as int].instr, trace[k + 1])
        && c[path[k] as int].succs.contains(path[k + 1]) by {
        if k == 3 {
            assert(c[3].succs[0] == 2);
        } else {
            assert(c[path[k] as int].succs[0] == path[k + 1]);
        }
    }
    (path, trace)
}

/// A run of `loop_ok` that takes the back edge meets every hypothesis of
/// `cfg_soundness_from_start`, so the theorem applies to it.
pub proof fn example_cfg_soundness_applies()
    ensures
        exists|path: Seq<nat>, trace: Seq<DState>|
            #![trigger is_cfg_trace(loop_ok(), path, trace)]
            {
                &&& is_cfg_trace(loop_ok(), path, trace)
                &&& wf(trace[0])
                &&& cfg_check(loop_ok(), initial_sstate(trace[0]), ann_ok())
                &&& trace.len() == 5
                &&& path[4] == 1
                &&& forall|k: int| 0 <= k < 5 ==> !#[trigger] ub(trace[k], loop_ok()[path[k] as int].instr)
            },
{
    let (path0, trace) = example_loop_bad_is_ub();
    reveal(step);
    let c = loop_ok();
    let path = seq![0nat, 1, 2, 3, 1];
    assert(c[3].succs[0] == 1);
    assert forall|k: int| 0 <= k < trace.len() - 1 implies step(#[trigger] trace[k], c[path[k] as int].instr, trace[k + 1])
        && c[path[k] as int].succs.contains(path[k + 1]) by {
        assert(c[path[k] as int].instr == loop_bad()[path0[k] as int].instr);
        assert(step(trace[k], loop_bad()[path0[k] as int].instr, trace[k + 1]));
        assert(c[path[k] as int].succs[0] == path[k + 1]);
    }
    assert(is_cfg_trace(c, path, trace));
    example_loop_ok();
    assert(initial_sstate(trace[0]) == ss0()) by {
        reveal(st0);
        assert(st0().locals.dom() =~= Set::empty().insert(D()));
    }
    cfg_soundness_from_start(c, ann_ok(), path, trace);
}

} // verus!
