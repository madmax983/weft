//! # B5. Progress
//!
//! `soundness.rs` proves preservation and no UB. This file proves progress:
//! if the checker accepts an instruction in a state that satisfies the
//! invariant, then the instruction can step, or it stops at a defined, safe
//! abort (`aborts`). An abort is a failed runtime check. It is never UB
//! (`lemma_no_ub`). Main theorem: `progress`.

use vstd::prelude::*;
use crate::model::*;
use crate::soundness::*;
use crate::cfg::*;
use crate::examples::*;

verus! {

// ---------------------------------------------------------------------------
// Abort cases
// ---------------------------------------------------------------------------

/// The current heap has no allocation at the path that `ret` asks for, so
/// the callee cannot return the reference (for example `get(list, i)` with
/// `i` out of range).
pub open spec fn no_result(h: Heap, ps: Seq<(Ptr, bool)>, ret: Option<Ret>) -> bool {
    match ret {
        None => false,
        Some(r) => forall|route: Route|
            labels(route) == r.path ==> !(#[trigger] resolve(h, ps[r.arg as int].0.addr, route) is Some),
    }
}

/// The defined, safe abort cases. Each one is a runtime check that fails on
/// live data:
/// * `Child`: the index is out of range (the child group has no element now);
/// * `Read`, `Write`: the field index is out of range of the inline data.
///   This model has no static types, so the checker cannot exclude it here.
///   `layout.rs` (B3) adds types; there it is UB, and the checker excludes it;
/// * `Call`, `Invoke`: the callee must return a reference at a path that
///   does not exist in the current heap, so the callee aborts.
pub open spec fn aborts(s: DState, i: Instr) -> bool {
    match i {
        Instr::Child { src, label, .. } => !dangling(s, src) && forall|idx: nat|
            #[trigger] kid_at(s.heap, s.vars[src].addr, (label, idx)) is None,
        Instr::Read { src, field } => !dangling(s, src) && field >= s.heap[s.vars[src].addr].data.len(),
        Instr::Write { src, field, .. } => !dangling(s, src) && field >= s.heap[s.vars[src].addr].data.len(),
        Instr::Call { args, ret } => {
            &&& forall|k: int| 0 <= k < args.len() ==> !#[trigger] dangling(s, args[k].0)
            &&& no_result(s.heap, arg_ptrs(s, args), ret)
        },
        Instr::Invoke { clo, args, ret, .. } => {
            &&& s.clos.contains_key(clo)
            &&& forall|k: int| 0 <= k < args.len() ==> !#[trigger] dangling(s, args[k].0)
            &&& caps_live(s, clo)
            &&& no_result(s.heap, invoke_ptrs(s, clo, args), ret)
        },
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// A route from an allocation in a well-formed heap ends at an allocation.
pub proof fn lemma_resolve_in_heap(s: DState, a: Addr, r: Route, c: Addr)
    requires
        wf(s),
        s.heap.contains_key(a),
        resolve(s.heap, a, r) == Some(c),
    ensures
        s.heap.contains_key(c),
{
    if r.len() > 0 {
        let b = lemma_resolve_owner(s.heap, a, r, c);
        assert(s.heap.contains_key(s.heap[b].kids[r.last().1 as int].1));
    }
}

/// The callee that does nothing is a valid callee.
pub proof fn lemma_identity_effect(s: DState, ps: Seq<(Ptr, bool)>)
    requires
        wf(s),
        forall|k: int| 0 <= k < ps.len() ==> s.heap.contains_key(#[trigger] ps[k].0.addr),
    ensures
        callee_effect(s, ps, s.heap, s.next_stamp),
{
    assert(DState { heap: s.heap, next_stamp: s.next_stamp, ..s } == s);
    assert forall|m: Addr| is_mut_root(ps, m) && !below_mut(s.heap, ps, m) implies #[trigger] s.heap.contains_key(m)
        && s.heap[m].stamp == s.heap[m].stamp && s.heap[m].ty == s.heap[m].ty by {
        let k = choose|k: int| 0 <= k < ps.len() && ps[k].1 && #[trigger] ps[k].0.addr == m;
        assert(s.heap.contains_key(ps[k].0.addr));
    }
}

/// A call with live argument pointers can step, or the callee aborts.
proof fn lemma_call_progress(s: DState, s1: DState, ps: Seq<(Ptr, bool)>, ret: Option<Ret>)
    requires
        wf(s1),
        forall|k: int| 0 <= k < ps.len() ==> live(s1, #[trigger] ps[k].0),
        match ret {
            None => true,
            Some(r) => r.arg < ps.len(),
        },
        s1.heap == s.heap,
    ensures
        (exists|s2: DState| #[trigger] call_step(s1, ps, ret, s2)) || no_result(s.heap, ps, ret),
{
    assert forall|k: int| 0 <= k < ps.len() implies s1.heap.contains_key(#[trigger] ps[k].0.addr) by {
        assert(live(s1, ps[k].0));
    }
    lemma_identity_effect(s1, ps);
    let h = s1.heap;
    let n = s1.next_stamp;
    match ret {
        None => {
            let s2 = DState { heap: h, next_stamp: n, ..s1 };
            assert(call_result(s1, ps, ret, h, n, s2));
            assert(call_step(s1, ps, ret, s2));
        },
        Some(r) => {
            if !no_result(s.heap, ps, ret) {
                let a = ps[r.arg as int].0.addr;
                let route = choose|route: Route| labels(route) == r.path && (#[trigger] resolve(h, a, route) is Some);
                let c = resolve(h, a, route)->0;
                assert(live(s1, ps[r.arg as int].0));
                lemma_resolve_in_heap(s1, a, route, c);
                let s2 = DState { heap: h, vars: s1.vars.insert(r.dst, ptr_to(h, c)), next_stamp: n, ..s1 };
                assert(call_result(s1, ps, ret, h, n, s2));
                assert(call_step(s1, ps, ret, s2));
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Main theorem
// ---------------------------------------------------------------------------

/// **Progress.** If the checker accepts instruction `i` in a state that
/// satisfies the invariant, then `i` has no UB, and `i` can step or `i`
/// aborts safely.
pub proof fn progress(s: DState, ss: SState, i: Instr)
    requires
        inv(s, ss),
        instr_ok(ss, i),
    ensures
        !ub(s, i),
        (exists|s2: DState| #[trigger] step(s, i, s2)) || aborts(s, i),
{
    lemma_no_ub(s, ss, i);
    match i {
        Instr::Borrow { dst, x } => {
            assert(s.locals.dom().contains(x));
            let s2 = DState { vars: s.vars.insert(dst, ptr_to(s.heap, s.locals[x])), ..s };
            assert(step(s, i, s2));
        },
        Instr::Child { dst, src, label } => {
            assert(ref_ok(s, ss.vars[src], src));
            if !aborts(s, i) {
                let idx = choose|idx: nat| !(#[trigger] kid_at(s.heap, s.vars[src].addr, (label, idx)) is None);
                let res = kid_at(s.heap, s.vars[src].addr, (label, idx));
                let s2 = DState { vars: s.vars.insert(dst, ptr_to(s.heap, res->0)), ..s };
                assert(step(s, i, s2));
            }
        },
        Instr::Copy { dst, src } => {
            let s2 = DState {
                vars: if s.vars.contains_key(src) {
                    s.vars.insert(dst, s.vars[src])
                } else {
                    s.vars.remove(dst)
                },
                ..s
            };
            assert(step(s, i, s2));
        },
        Instr::Read { src, field } => {
            assert(ref_ok(s, ss.vars[src], src));
            if !aborts(s, i) {
                assert(step(s, i, s));
            }
        },
        Instr::Write { src, field, val } => {
            assert(ref_ok(s, ss.vars[src], src));
            if !aborts(s, i) {
                let a = s.vars[src].addr;
                let o = s.heap[a];
                let s2 = DState { heap: s.heap.insert(a, Obj { data: o.data.update(field as int, val), ..o }), ..s };
                assert(step(s, i, s2));
            }
        },
        Instr::Call { args, ret } => {
            let ps = arg_ptrs(s, args);
            assert forall|k: int| 0 <= k < args.len() implies !#[trigger] dangling(s, args[k].0) by {
                assert(ss.vars.contains_key(args[k].0));
            }
            assert forall|k: int| 0 <= k < ps.len() implies live(s, #[trigger] ps[k].0) by {
                assert(!dangling(s, args[k].0));
            }
            lemma_call_progress(s, s, ps, ret);
            if exists|s2: DState| call_step(s, ps, ret, s2) {
                let s2 = choose|s2: DState| call_step(s, ps, ret, s2);
                assert(step(s, i, s2));
            }
        },
        Instr::MkClosure { clo, caps } => {
            assert forall|k: int| 0 <= k < caps.len() implies #[trigger] s.vars.contains_key(caps[k].0) by {
                assert(ss.vars.contains_key(caps[k].0));
            }
            let s2 = DState { clos: s.clos.insert(clo, arg_ptrs(s, caps)), ..s };
            assert(step(s, i, s2));
        },
        Instr::Invoke { clo, args, ret, once } => {
            let ps = invoke_ptrs(s, clo, args);
            let s1 = consume(s, clo, once);
            let pa = arg_ptrs(s, args);
            let pc = s.clos[clo];
            assert(args_ok(s, ss.clos[clo], pc));
            assert forall|k: int| 0 <= k < args.len() implies !#[trigger] dangling(s, args[k].0) by {
                assert(ss.vars.contains_key(args[k].0));
            }
            assert(caps_live(s, clo)) by {
                assert forall|j: int| 0 <= j < pc.len() implies live(s, #[trigger] pc[j].0) by {
                    assert(ptr_ok(s, ss.clos[clo][j].0, pc[j].0));
                }
            }
            assert forall|k: int| 0 <= k < ps.len() implies live(s1, #[trigger] ps[k].0) by {
                if k < pa.len() {
                    assert(ps[k] == pa[k]);
                    assert(!dangling(s, args[k].0));
                } else {
                    assert(ps[k] == pc[k - pa.len()]);
                }
            }
            assert(wf(s1));
            lemma_call_progress(s, s1, ps, ret);
            if exists|s2: DState| call_step(s1, ps, ret, s2) {
                let s2 = choose|s2: DState| call_step(s1, ps, ret, s2);
                assert(step(s, i, s2));
            }
        },
    }
}

/// **Progress for straight-line programs.** Each run of a checked program
/// can go on until the program ends, or until a safe abort.
pub proof fn progress_trace(ss0: SState, prog: Seq<Instr>, trace: Seq<DState>)
    requires
        inv(trace[0], ss0),
        check(ss0, prog),
        is_trace(prog, trace),
        trace.len() <= prog.len(),
    ensures
        (exists|s2: DState| #[trigger] step(trace.last(), prog[trace.len() - 1], s2)) || aborts(
            trace.last(),
            prog[trace.len() - 1],
        ),
{
    let k = (trace.len() - 1) as nat;
    lemma_inv_along(ss0, prog, trace, k);
    assert(instr_ok(ss_at(ss0, prog, k), prog[k as int]));
    progress(trace[k as int], ss_at(ss0, prog, k), prog[k as int]);
}

/// **Progress for CFGs.** A run that the checker accepts can go on along
/// each successor edge, until it reaches an exit or a safe abort.
pub proof fn cfg_progress(cfg: Cfg, ss0: SState, ann: Seq<SState>, path: Seq<nat>, trace: Seq<DState>)
    requires
        inv(trace[0], ss0),
        cfg_check(cfg, ss0, ann),
        is_cfg_trace(cfg, path, trace),
    ensures
        aborts(trace.last(), cfg[path.last() as int].instr) || exists|s2: DState|
            #[trigger] step(trace.last(), cfg[path.last() as int].instr, s2) && forall|m: nat|
                cfg[path.last() as int].succs.contains(m) ==> #[trigger] is_cfg_trace(cfg, path.push(m), trace.push(s2)),
{
    let k = (trace.len() - 1) as int;
    let n = path[k] as int;
    lemma_cfg_inv_along(cfg, ss0, ann, path, trace, k as nat);
    assert(path[k] < cfg.len());
    assert(instr_ok(ann[n], cfg[n].instr));
    progress(trace[k], ann[n], cfg[n].instr);
    if !aborts(trace.last(), cfg[n].instr) {
        let s2 = choose|s2: DState| step(trace.last(), cfg[n].instr, s2);
        assert forall|m: nat| cfg[n].succs.contains(m) implies #[trigger] is_cfg_trace(cfg, path.push(m), trace.push(s2)) by {
            let j = choose|j: int| 0 <= j < cfg[n].succs.len() && cfg[n].succs[j] == m;
            assert(cfg[n].succs[j] < cfg.len());
            let p2 = path.push(m);
            let t2 = trace.push(s2);
            assert forall|i: int| 0 <= i < p2.len() implies #[trigger] p2[i] < cfg.len() by {
                if i < path.len() {
                    assert(p2[i] == path[i]);
                }
            }
            assert forall|i: int| 0 <= i < t2.len() - 1 implies step(#[trigger] t2[i], cfg[p2[i] as int].instr, t2[i + 1])
                && cfg[p2[i] as int].succs.contains(p2[i + 1]) by {
                if i < k {
                    assert(t2[i] == trace[i] && t2[i + 1] == trace[i + 1]);
                    assert(p2[i] == path[i] && p2[i + 1] == path[i + 1]);
                } else {
                    assert(i == k);
                    assert(t2[i] == trace.last() && t2[i + 1] == s2);
                    assert(p2[i] == path[k] && p2[i + 1] == m);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Sanity checks
// ---------------------------------------------------------------------------

/// A checker state with `rd` valid in the group `d`.
pub open spec fn ss_rd() -> SState {
    SState { vars: map![RD() => g(D(), seq![])], ..ss0() }
}

/// `ring = &d.rings[i]`.
pub open spec fn child_ring() -> Instr {
    Instr::Child { dst: RING(), src: RD(), label: RINGS() }
}

/// `read ring`.
pub open spec fn read_ring() -> Instr {
    Instr::Read { src: RING(), field: 0 }
}

proof fn lemma_inv_rd(s: DState)
    requires
        wf(s),
        s.locals == st0().locals,
        s.vars.contains_key(RD()),
        s.vars[RD()] == ptr_to(st0().heap, 0),
        s.heap.contains_key(0),
        s.heap[0].stamp == 0,
        s.heap[0].ty == 0,
        s.clos == Map::<CVar, Seq<(Ptr, bool)>>::empty(),
    ensures
        inv(s, ss_rd()),
{
    let e = Seq::<Step>::empty();
    assert(labels(e) =~= Seq::<Label>::empty());
    assert(resolve(s.heap, s.locals[D()], e) == Some(0nat));
    assert(ref_ok(s, g(D(), seq![]), RD()));
    assert(ss_rd().locals =~= s.locals.dom());
}

/// The hypotheses of `progress` hold for `ring = &d.rings[i]` in state `t1`,
/// and the instruction steps.
pub proof fn example_progress_step()
    ensures
        inv(t1(), ss_rd()),
        instr_ok(ss_rd(), child_ring()),
        step(t1(), child_ring(), t2()),
        !aborts(t1(), child_ring()),
{
    lemma_st0_wf();
    lemma_inv_rd(t1());
    lemma_damage_steps_0_2();
    assert(damage_bad()[1] == child_ring());
    assert(kid_at(t1().heap, t1().vars[RD()].addr, (RINGS(), 0nat)) is Some);
}

/// After `d.damage(10)` freed the ring, the checker still accepts
/// `ring = &d.rings[i]`, but no step exists: the index is out of range, and
/// the run aborts safely.
pub proof fn example_progress_abort()
    ensures
        inv(t4(), ss_rd()),
        instr_ok(ss_rd(), child_ring()),
        aborts(t4(), child_ring()),
        forall|s2: DState| !#[trigger] step(t4(), child_ring(), s2),
{
    lemma_damage_effect();
    assert(t4() == DState { heap: h_damaged(), next_stamp: 2, ..t2() });
    lemma_inv_rd(t4());
}

/// Progress needs the checker: in `t4` the checker rejects `read ring`, and
/// `read ring` has no step, is not an abort, and is UB.
pub proof fn example_no_progress_without_check()
    ensures
        !instr_ok(ss_rd(), read_ring()),
        forall|s2: DState| !#[trigger] step(t4(), read_ring(), s2),
        !aborts(t4(), read_ring()),
        ub(t4(), read_ring()),
{
    assert(!t4().heap.contains_key(1nat));
}

} // verus!
