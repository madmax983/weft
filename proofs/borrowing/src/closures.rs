//! # B2. Captured references: closures, effect handlers, continuations
//!
//! A closure value is code plus a list of captured `(reference, is_mut)`.
//! An effect handler and a continuation are closure values too.
//! `MkClosure` copies the captured pointers into the value. `Invoke` is a call
//! whose argument list is the explicit arguments plus the captured pointers.
//! `perform` and `resume` are invokes; `resume` consumes the continuation.
//! The checker treats a closure value as a reference into each group of its
//! captures: a call that kills one of them kills the value (`clos_survivors`).
//!
//! The soundness theorems (`soundness_from_start`, `cfg_soundness`) cover these
//! instructions. This file proves that a perform is checked and executed like
//! a plain call that also passes the handler's captured references
//! (`lemma_perform_is_call`), and gives sanity checks.

#![allow(non_snake_case)]

use vstd::prelude::*;
use crate::model::*;
use crate::soundness::*;
use crate::examples::*;

verus! {

// ---------------------------------------------------------------------------
// A perform is a call with the handler's footprint
// ---------------------------------------------------------------------------

/// The variables `cvars` hold the captured pointers of `clo`, in order, and
/// the checker gives them the groups of the captures.
pub open spec fn caps_in_vars(s: DState, ss: SState, clo: CVar, cvars: Seq<Var>) -> bool {
    &&& cvars.len() == s.clos[clo].len()
    &&& cvars.len() == ss.clos[clo].len()
    &&& forall|j: int|
        0 <= j < cvars.len() ==> {
            &&& s.vars.contains_key(#[trigger] cvars[j])
            &&& s.vars[cvars[j]] == s.clos[clo][j].0
            &&& ss.vars.contains_key(cvars[j])
            &&& ss.vars[cvars[j]] == ss.clos[clo][j].0
            &&& s.clos[clo][j].1 == ss.clos[clo][j].1
        }
}

/// The captured references of `clo` as explicit call arguments.
pub open spec fn cap_args(ss: SState, clo: CVar, cvars: Seq<Var>) -> Seq<(Var, bool)> {
    Seq::new(cvars.len(), |j: int| (cvars[j], ss.clos[clo][j].1))
}

proof fn lemma_all_index(ss: SState, h: CVar, args: Seq<(Var, bool)>, cvars: Seq<Var>)
    requires
        cvars.len() == ss.clos[h].len(),
    ensures
        forall|k: int| 0 <= k < args.len() ==> #[trigger] (args + cap_args(ss, h, cvars))[k] == args[k],
        forall|k: int|
            args.len() <= k < args.len() + cvars.len() ==> #[trigger] (args + cap_args(ss, h, cvars))[k] == (
                cvars[k - args.len()],
                ss.clos[h][k - args.len()].1,
            ),
        (args + cap_args(ss, h, cvars)).len() == args.len() + cvars.len(),
{
    let ca = cap_args(ss, h, cvars);
    assert forall|k: int| args.len() <= k < args.len() + cvars.len() implies #[trigger] (args + ca)[k] == (
        cvars[k - args.len()],
        ss.clos[h][k - args.len()].1,
    ) by {
        assert((args + ca)[k] == ca[k - args.len()]);
    }
}

proof fn lemma_all_ptrs(s: DState, ss: SState, h: CVar, args: Seq<(Var, bool)>, cvars: Seq<Var>)
    requires
        caps_in_vars(s, ss, h, cvars),
    ensures
        arg_ptrs(s, args + cap_args(ss, h, cvars)) == invoke_ptrs(s, h, args),
        arg_groups(ss, args + cap_args(ss, h, cvars)) == invoke_groups(ss, h, args),
{
    let all = args + cap_args(ss, h, cvars);
    let n = args.len() as int;
    lemma_all_index(ss, h, args, cvars);
    assert(arg_ptrs(s, all) =~= invoke_ptrs(s, h, args)) by {
        assert forall|k: int| 0 <= k < all.len() implies #[trigger] arg_ptrs(s, all)[k] == invoke_ptrs(s, h, args)[k] by {
            if k >= n {
                assert(all[k] == (cvars[k - n], ss.clos[h][k - n].1));
                assert(s.vars[cvars[k - n]] == s.clos[h][k - n].0);
            }
        }
    }
    assert(arg_groups(ss, all) =~= invoke_groups(ss, h, args)) by {
        assert forall|k: int| 0 <= k < all.len() implies #[trigger] arg_groups(ss, all)[k] == invoke_groups(ss, h, args)[k] by {
            if k >= n {
                assert(all[k] == (cvars[k - n], ss.clos[h][k - n].1));
                assert(ss.vars[cvars[k - n]] == ss.clos[h][k - n].0);
            }
        }
    }
}

/// The captured variables are not dangling iff the captured pointers are live.
proof fn lemma_all_live(s: DState, ss: SState, h: CVar, args: Seq<(Var, bool)>, cvars: Seq<Var>)
    requires
        caps_in_vars(s, ss, h, cvars),
    ensures
        (forall|k: int|
            0 <= k < (args + cap_args(ss, h, cvars)).len() ==> !#[trigger] dangling(s, (args + cap_args(ss, h, cvars))[k].0))
            <==> ((forall|k: int| 0 <= k < args.len() ==> !#[trigger] dangling(s, args[k].0)) && caps_live(s, h)),
{
    let all = args + cap_args(ss, h, cvars);
    let n = args.len() as int;
    lemma_all_index(ss, h, args, cvars);
    if forall|k: int| 0 <= k < all.len() ==> !#[trigger] dangling(s, all[k].0) {
        assert forall|k: int| 0 <= k < args.len() implies !#[trigger] dangling(s, args[k].0) by {
            assert(!dangling(s, all[k].0));
        }
        assert forall|j: int| 0 <= j < s.clos[h].len() implies live(s, #[trigger] s.clos[h][j].0) by {
            assert(all[n + j] == (cvars[j], ss.clos[h][j].1));
            assert(!dangling(s, all[n + j].0));
        }
    }
    if (forall|k: int| 0 <= k < args.len() ==> !#[trigger] dangling(s, args[k].0)) && caps_live(s, h) {
        assert forall|k: int| 0 <= k < all.len() implies !#[trigger] dangling(s, all[k].0) by {
            if k >= n {
                assert(all[k] == (cvars[k - n], ss.clos[h][k - n].1));
                assert(live(s, s.clos[h][k - n].0));
            }
        }
    }
}

/// The captured variables are valid for the checker.
proof fn lemma_all_valid(s: DState, ss: SState, h: CVar, args: Seq<(Var, bool)>, cvars: Seq<Var>)
    requires
        caps_in_vars(s, ss, h, cvars),
    ensures
        (forall|k: int|
            0 <= k < (args + cap_args(ss, h, cvars)).len() ==> ss.vars.contains_key(#[trigger] (args + cap_args(ss, h, cvars))[k].0))
            <==> (forall|k: int| 0 <= k < args.len() ==> ss.vars.contains_key(#[trigger] args[k].0)),
{
    let all = args + cap_args(ss, h, cvars);
    let n = args.len() as int;
    lemma_all_index(ss, h, args, cvars);
    if forall|k: int| 0 <= k < args.len() ==> ss.vars.contains_key(#[trigger] args[k].0) {
        assert forall|k: int| 0 <= k < all.len() implies ss.vars.contains_key(#[trigger] all[k].0) by {
            if k < n {
                assert(all[k] == args[k]);
            } else {
                assert(all[k] == (cvars[k - n], ss.clos[h][k - n].1));
            }
        }
    }
    if forall|k: int| 0 <= k < all.len() ==> ss.vars.contains_key(#[trigger] all[k].0) {
        assert forall|k: int| 0 <= k < args.len() implies ss.vars.contains_key(#[trigger] args[k].0) by {
            assert(all[k] == args[k]);
        }
    }
}

/// **A perform is a call with the handler's footprint.** If the variables
/// `cvars` hold the captured references of handler `h`, then
/// `perform(h, args, ret)` and `Call { args: args + cap_args(..), ret }` have
/// the same steps and the same UB, and the checker accepts and updates them
/// in the same way.
pub proof fn lemma_perform_is_call(
    s: DState,
    ss: SState,
    h: CVar,
    args: Seq<(Var, bool)>,
    ret: Option<Ret>,
    cvars: Seq<Var>,
    s2: DState,
)
    requires
        s.clos.contains_key(h),
        ss.clos.contains_key(h),
        caps_in_vars(s, ss, h, cvars),
    ensures
        step(s, perform(h, args, ret), s2) <==> step(s, Instr::Call { args: args + cap_args(ss, h, cvars), ret }, s2),
        ub(s, perform(h, args, ret)) <==> ub(s, Instr::Call { args: args + cap_args(ss, h, cvars), ret }),
        instr_ok(ss, perform(h, args, ret)) <==> instr_ok(ss, Instr::Call { args: args + cap_args(ss, h, cvars), ret }),
        post(ss, perform(h, args, ret)) == post(ss, Instr::Call { args: args + cap_args(ss, h, cvars), ret }),
{
    lemma_all_ptrs(s, ss, h, args, cvars);
    lemma_all_live(s, ss, h, args, cvars);
    lemma_all_valid(s, ss, h, args, cvars);
    assert(consume(s, h, false) == s);
    assert(consume_s(ss, h, false) == ss);
}

// ---------------------------------------------------------------------------
// Sanity checks
// ---------------------------------------------------------------------------

// closure variables
/// The closure variable of the handler.
pub open spec fn H() -> CVar { 0 }
/// The closure variable of a plain closure.
pub open spec fn F() -> CVar { 1 }
/// The closure variable of a continuation.
pub open spec fn K() -> CVar { 2 }

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

proof fn lemma_groups()
    ensures
        strict_child(gr(), gd()),
        strict_child(ga(), gd()),
        !strict_child(gd(), gd()),
        !strict_child(gr(), gr()),
        !strict_child(gd(), gr()),
        !strict_child(ga(), gr()),
{
    assert(gr().path.subrange(0, 0) =~= Seq::<Label>::empty());
    assert(ga().path.subrange(0, 0) =~= Seq::<Label>::empty());
    assert(ga().path.subrange(0, 1) =~= seq![ARMOR()]);
}

// ---- 1. A handler that captures `mut d` kills `ring` at each perform ------

/// ```text
/// 0: rd = &d
/// 1: ring = &d.rings[i]
/// 2: h = handler capturing (rd, mut)     // the handler changes d
/// 3: perform(h)                          // a call with h's footprint: kills d.rings*
/// ```
pub open spec fn handler_prefix() -> Seq<Instr> {
    seq![
        Instr::Borrow { dst: RD(), x: D() },
        Instr::Child { dst: RING(), src: RD(), label: RINGS() },
        Instr::MkClosure { clo: H(), caps: seq![(RD(), true)] },
        perform(H(), seq![], None),
    ]
}

/// After the perform, `d` is still valid.
pub open spec fn handler_ok() -> Seq<Instr> {
    handler_prefix().push(Instr::Read { src: RD(), field: 0 })
}

/// After the perform, `ring` is used: rejected.
pub open spec fn handler_bad() -> Seq<Instr> {
    handler_prefix().push(Instr::Read { src: RING(), field: 0 })
}

proof fn lemma_handler_states() -> (sts: Seq<SState>)
    ensures
        sts.len() == 5,
        forall|k: nat| k < 5 ==> #[trigger] ss_at(ss0(), handler_bad(), k) == sts[k as int],
        sts[2].vars == map![RD() => gd(), RING() => gr()],
        sts[3].clos == map![H() => seq![(gd(), true)]],
        sts[4].vars == map![RD() => gd()],
{
    let p = handler_bad();
    let s0 = ss0();
    let s1 = post(s0, p[0]);
    let s2 = post(s1, p[1]);
    let s3 = post(s2, p[2]);
    let s4 = post(s3, p[3]);
    lemma_groups();
    assert(s1.vars =~= map![RD() => gd()]);
    assert(seq![].push(RINGS()) =~= seq![RINGS()]);
    assert(s2.vars =~= map![RD() => gd(), RING() => gr()]);
    let caps = p[2]->MkClosure_caps;
    assert(arg_groups(s2, caps) =~= seq![(gd(), true)]);
    assert(s3.clos =~= map![H() => seq![(gd(), true)]]);
    assert(s3.vars == s2.vars);
    let gs = invoke_groups(s3, H(), p[3]->Invoke_args);
    assert(gs =~= seq![(gd(), true)]);
    assert(killed(gs, gr())) by {
        assert(strict_child(gr(), gs[0].0));
    }
    assert(!killed(gs, gd()));
    assert(s4.vars =~= map![RD() => gd()]);
    let sts = seq![s0, s1, s2, s3, s4];
    assert forall|k: nat| k < 5 implies #[trigger] ss_at(s0, p, k) == sts[k as int] by {
        assert(ss_at(s0, p, 0) == s0);
        assert(ss_at(s0, p, 1) == s1);
        assert(ss_at(s0, p, 2) == s2);
        assert(ss_at(s0, p, 3) == s3);
        assert(ss_at(s0, p, 4) == s4);
    }
    sts
}

/// The checker accepts `handler_ok`.
pub proof fn example_handler_ok()
    ensures
        check(ss0(), handler_ok()),
{
    let sts = lemma_handler_states();
    let p = handler_ok();
    assert forall|k: nat| k < p.len() implies #[trigger] instr_ok(ss_at(ss0(), p, k), p[k as int]) by {
        lemma_ss_at_prefix(ss0(), handler_prefix(), p, k);
        lemma_ss_at_prefix(ss0(), handler_prefix(), handler_bad(), k);
        if k < 4 {
            assert(ss_at(ss0(), p, k) == sts[k as int]);
        } else {
            lemma_ss_at_prefix(ss0(), handler_prefix(), p, 4);
            lemma_ss_at_prefix(ss0(), handler_prefix(), handler_bad(), 4);
            assert(ss_at(ss0(), p, 4) == sts[4]);
        }
        if k == 2 {
            let caps = p[2]->MkClosure_caps;
            assert(sts[2].vars.contains_key(caps[0].0));
        }
        if k == 3 {
            assert(sts[3].clos.contains_key(H()));
        }
    }
}

/// The checker rejects `handler_bad`: the perform kills `ring`.
pub proof fn example_handler_rejected()
    ensures
        !check(ss0(), handler_bad()),
{
    let sts = lemma_handler_states();
    assert(ss_at(ss0(), handler_bad(), 4) == sts[4]);
    assert(!instr_ok(ss_at(ss0(), handler_bad(), 4), handler_bad()[4]));
}

/// The pointer to `d` in `st0`.
pub open spec fn ptr_d() -> Ptr {
    ptr_to(st0().heap, 0)
}

/// The pointer to the ring in `st0`.
pub open spec fn ptr_ring() -> Ptr {
    ptr_to(st0().heap, 1)
}

/// The state after `h = handler capturing (rd, mut)`.
pub open spec fn t2h() -> DState {
    DState { clos: map![H() => seq![(ptr_d(), true)]], ..t2() }
}

/// The state after `perform(h)`: the handler freed the ring.
pub open spec fn t4h() -> DState {
    DState { heap: h_damaged(), ..t2h() }
}

proof fn lemma_handler_steps()
    ensures
        step(t2(), handler_bad()[2], t2h()),
        step(t2h(), handler_bad()[3], t4h()),
        step(t4h(), handler_ok()[4], t4h()),
        ub(t4h(), handler_bad()[4]),
{
    let p = handler_bad();
    let caps = p[2]->MkClosure_caps;
    assert(t2().vars.contains_key(caps[0].0));
    assert(arg_ptrs(t2(), caps) =~= seq![(ptr_d(), true)]);
    assert(t2().clos.insert(H(), arg_ptrs(t2(), caps)) =~= t2h().clos);
    assert(step(t2(), p[2], t2h()));
    let s = t2h();
    let ps = invoke_ptrs(s, H(), p[3]->Invoke_args);
    assert(ps =~= seq![(ptr_d(), true)]);
    lemma_free_ring_effect(s, ps);
    assert(call_result(s, ps, None, h_damaged(), 2, t4h()));
    assert(call_step(consume(s, H(), false), ps, None, t4h()));
    assert(caps_live(s, H())) by {
        assert(s.clos[H()][0].0 == ptr_d());
    }
    assert(step(t2h(), p[3], t4h()));
    assert(!t4h().heap.contains_key(1nat));
}

/// A concrete run of `handler_bad`: the handler frees the ring, and the read
/// of `ring` is a use after free. So the perform must kill `ring`.
pub proof fn example_handler_bad_is_ub() -> (trace: Seq<DState>)
    ensures
        is_trace(handler_bad(), trace),
        trace == seq![st0(), t1(), t2(), t2h(), t4h()],
        trace[0] == st0(),
        wf(trace[0]),
        trace.len() == 5,
        ub(trace[4], handler_bad()[4]),
{
    hide(step);
    hide(wf);
    hide(ub);
    hide(st0);
    hide(t1);
    hide(t2);
    hide(t2h);
    hide(t4h);
    lemma_st0_wf();
    lemma_damage_steps_0_2();
    lemma_handler_steps();
    let p = handler_bad();
    assert(p[0] == damage_bad()[0] && p[1] == damage_bad()[1]);
    let trace = seq![st0(), t1(), t2(), t2h(), t4h()];
    assert forall|k: int| 0 <= k < trace.len() - 1 implies step(#[trigger] trace[k], p[k], trace[k + 1]) by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else {}
    }
    trace
}

/// A run of `handler_ok` meets every hypothesis of `soundness_from_start`,
/// so the theorem applies to a program with a handler and a perform.
pub proof fn example_handler_soundness_applies()
    ensures
        exists|trace: Seq<DState>|
            #![trigger is_trace(handler_ok(), trace)]
            is_trace(handler_ok(), trace) && trace.len() == 6 && forall|k: int|
                0 <= k < 5 ==> !#[trigger] ub(trace[k], handler_ok()[k]),
{
    hide(step);
    let t = example_handler_bad_is_ub();
    lemma_handler_steps();
    let p = handler_ok();
    let trace = t.push(t4h());
    assert forall|j: int| 0 <= j < 4 implies #[trigger] p[j] == handler_bad()[j] by {}
    assert(is_trace(p, trace)) by {
        assert forall|k: int| 0 <= k < trace.len() - 1 implies step(#[trigger] trace[k], p[k], trace[k + 1]) by {
            if k < 4 {
                assert(trace[k] == t[k] && trace[k + 1] == t[k + 1]);
                assert(step(t[k], handler_bad()[k], t[k + 1]));
            } else {
                assert(trace[4] == t4h() && trace[5] == t4h());
            }
        }
    }
    example_handler_ok();
    lemma_st0_wf();
    assert(initial_sstate(trace[0]) == ss0()) by {
        assert(st0().locals.dom() =~= Set::empty().insert(D()));
    }
    soundness_from_start(p, trace);
}

// ---- 2. A closure is killed when one of its captures is killed --------------

/// ```text
/// 0: rd = &d
/// 1: ring = &d.rings[i]
/// 2: f = closure capturing (ring, imm)   // f points into d.rings*
/// 3: d.damage(10)                        // kills ring, and so kills f
/// 4: f()                                 // rejected
/// ```
pub open spec fn closure_bad() -> Seq<Instr> {
    seq![
        Instr::Borrow { dst: RD(), x: D() },
        Instr::Child { dst: RING(), src: RD(), label: RINGS() },
        Instr::MkClosure { clo: F(), caps: seq![(RING(), false)] },
        Instr::Call { args: seq![(RD(), true)], ret: None },
        Instr::Invoke { clo: F(), args: seq![], ret: None, once: false },
    ]
}

/// The checker rejects `closure_bad`.
pub proof fn example_closure_rejected()
    ensures
        !check(ss0(), closure_bad()),
{
    let p = closure_bad();
    let s0 = ss0();
    let s1 = post(s0, p[0]);
    let s2 = post(s1, p[1]);
    let s3 = post(s2, p[2]);
    let s4 = post(s3, p[3]);
    lemma_groups();
    assert(s1.vars =~= map![RD() => gd()]);
    assert(seq![].push(RINGS()) =~= seq![RINGS()]);
    assert(s2.vars =~= map![RD() => gd(), RING() => gr()]);
    let caps = p[2]->MkClosure_caps;
    assert(arg_groups(s2, caps) =~= seq![(gr(), false)]);
    assert(s3.clos =~= map![F() => seq![(gr(), false)]]);
    let gs = arg_groups(s3, p[3]->Call_args);
    assert(gs[0] == (gd(), true));
    assert(killed(gs, gr())) by {
        assert(strict_child(gr(), gs[0].0));
    }
    assert(caps_killed(gs, s3.clos[F()])) by {
        assert(s3.clos[F()][0].0 == gr());
    }
    assert(!s4.clos.contains_key(F()));
    assert(ss_at(s0, p, 4) == s4) by {
        assert(ss_at(s0, p, 0) == s0);
        assert(ss_at(s0, p, 1) == s1);
        assert(ss_at(s0, p, 2) == s2);
        assert(ss_at(s0, p, 3) == s3);
    }
    assert(!instr_ok(s4, p[4]));
}

/// The state after `f = closure capturing (ring, imm)`.
pub open spec fn t2f() -> DState {
    DState { clos: map![F() => seq![(ptr_ring(), false)]], ..t2() }
}

/// The state after `d.damage(10)`: the ring is freed.
pub open spec fn t4f() -> DState {
    DState { heap: h_damaged(), ..t2f() }
}

proof fn lemma_closure_steps()
    ensures
        step(t2(), closure_bad()[2], t2f()),
        step(t2f(), closure_bad()[3], t4f()),
        ub(t4f(), closure_bad()[4]),
{
    let p = closure_bad();
    let caps = p[2]->MkClosure_caps;
    assert(t2().vars.contains_key(caps[0].0));
    assert(arg_ptrs(t2(), caps) =~= seq![(ptr_ring(), false)]);
    assert(t2().clos.insert(F(), arg_ptrs(t2(), caps)) =~= t2f().clos);
    let s = t2f();
    let args = p[3]->Call_args;
    let ps = arg_ptrs(s, args);
    assert(ps[0] == (ptr_d(), true));
    lemma_free_ring_effect(s, ps);
    assert(call_result(s, ps, None, h_damaged(), 2, t4f()));
    assert(call_step(s, ps, None, t4f()));
    assert forall|k: int| 0 <= k < args.len() implies !#[trigger] dangling(s, args[k].0) by {
        assert(k == 0);
    }
    assert(step(t2f(), p[3], t4f()));
    assert(!t4f().heap.contains_key(1nat));
    assert(!live(t4f(), t4f().clos[F()][0].0));
    assert(!caps_live(t4f(), F()));
}

/// A concrete run of `closure_bad`: `d.damage(10)` frees the ring that `f`
/// captured, and `f()` passes a dangling pointer. So the call must kill `f`.
pub proof fn example_closure_bad_is_ub() -> (trace: Seq<DState>)
    ensures
        is_trace(closure_bad(), trace),
        trace == seq![st0(), t1(), t2(), t2f(), t4f()],
        trace[0] == st0(),
        wf(trace[0]),
        trace.len() == 5,
        ub(trace[4], closure_bad()[4]),
{
    hide(step);
    hide(wf);
    hide(ub);
    hide(st0);
    hide(t1);
    hide(t2);
    hide(t2f);
    hide(t4f);
    lemma_st0_wf();
    lemma_damage_steps_0_2();
    lemma_closure_steps();
    let p = closure_bad();
    assert(p[0] == damage_bad()[0] && p[1] == damage_bad()[1]);
    let trace = seq![st0(), t1(), t2(), t2f(), t4f()];
    assert forall|k: int| 0 <= k < trace.len() - 1 implies step(#[trigger] trace[k], p[k], trace[k + 1]) by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else {}
    }
    trace
}

// ---- 3. A closure that changes `d.rings*` keeps `d.armor*` valid ------------

/// ```text
/// 0: rd = &d
/// 1: ring = &d.rings[i]
/// 2: arm = &d.armor[j]
/// 3: f = closure capturing (ring, mut)   // f = || power_up(ring)
/// 4: f()                                 // kills only strict children of d.rings*
/// 5: read arm
/// 6: read ring
/// ```
pub open spec fn closure_ok() -> Seq<Instr> {
    seq![
        Instr::Borrow { dst: RD(), x: D() },
        Instr::Child { dst: RING(), src: RD(), label: RINGS() },
        Instr::Child { dst: ARM(), src: RD(), label: ARMOR() },
        Instr::MkClosure { clo: F(), caps: seq![(RING(), true)] },
        Instr::Invoke { clo: F(), args: seq![], ret: None, once: false },
        Instr::Read { src: ARM(), field: 0 },
        Instr::Read { src: RING(), field: 0 },
    ]
}

/// The checker accepts `closure_ok`.
pub proof fn example_closure_ok()
    ensures
        check(ss0(), closure_ok()),
{
    let p = closure_ok();
    let s0 = ss0();
    let s1 = post(s0, p[0]);
    let s2 = post(s1, p[1]);
    let s3 = post(s2, p[2]);
    let s4 = post(s3, p[3]);
    let s5 = post(s4, p[4]);
    let s6 = post(s5, p[5]);
    lemma_groups();
    assert(s1.vars =~= map![RD() => gd()]);
    assert(seq![].push(RINGS()) =~= seq![RINGS()]);
    assert(seq![].push(ARMOR()) =~= seq![ARMOR()]);
    assert(s3.vars =~= map![RD() => gd(), RING() => gr(), ARM() => ga()]);
    let caps = p[3]->MkClosure_caps;
    assert(arg_groups(s3, caps) =~= seq![(gr(), true)]);
    assert(s4.clos =~= map![F() => seq![(gr(), true)]]);
    let gs = invoke_groups(s4, F(), p[4]->Invoke_args);
    assert(gs =~= seq![(gr(), true)]);
    assert(!killed(gs, gd()));
    assert(!killed(gs, gr()));
    assert(!killed(gs, ga()));
    assert(!caps_killed(gs, s4.clos[F()])) by {
        assert(s4.clos[F()] =~= seq![(gr(), true)]);
    }
    assert(s5.vars =~= s4.vars);
    assert(s5.clos =~= s4.clos);
    assert(s6 == s5);
    assert forall|k: nat| k < p.len() implies #[trigger] instr_ok(ss_at(s0, p, k), p[k as int]) by {
        assert(ss_at(s0, p, 0) == s0);
        assert(ss_at(s0, p, 1) == s1);
        assert(ss_at(s0, p, 2) == s2);
        assert(ss_at(s0, p, 3) == s3);
        assert(ss_at(s0, p, 4) == s4);
        assert(ss_at(s0, p, 5) == s5);
        assert(ss_at(s0, p, 6) == s6);
        if k == 3 {
            assert(s3.vars.contains_key(caps[0].0));
        }
    }
}

// ---- 4. A one-shot continuation cannot be resumed twice ---------------------

/// ```text
/// 0: rd = &d
/// 1: k = continuation capturing (rd, mut)
/// 2: resume(k)
/// 3: resume(k)        // rejected: the first resume consumed k
/// ```
pub open spec fn resume_twice() -> Seq<Instr> {
    seq![
        Instr::Borrow { dst: RD(), x: D() },
        Instr::MkClosure { clo: K(), caps: seq![(RD(), true)] },
        resume(K(), seq![], None),
        resume(K(), seq![], None),
    ]
}

/// The checker rejects `resume_twice`.
pub proof fn example_resume_twice_rejected()
    ensures
        !check(ss0(), resume_twice()),
{
    let p = resume_twice();
    let s0 = ss0();
    let s1 = post(s0, p[0]);
    let s2 = post(s1, p[1]);
    let s3 = post(s2, p[2]);
    assert(s2.clos.dom() =~= set![K()]);
    assert(consume_s(s2, K(), true).clos =~= Map::<CVar, Seq<(Group, bool)>>::empty());
    assert(!s3.clos.contains_key(K()));
    assert(ss_at(s0, p, 3) == s3) by {
        assert(ss_at(s0, p, 0) == s0);
        assert(ss_at(s0, p, 1) == s1);
        assert(ss_at(s0, p, 2) == s2);
    }
    assert(!instr_ok(s3, p[3]));
}

} // verus!
