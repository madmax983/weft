//! # B4. Task separation
//!
//! Two tasks run interleaved on one shared heap. Each task has its own
//! reference variables, closure values and program counter, and runs its own
//! straight-line program. A scheduler picks the task for each step.
//!
//! The rule (`separated`): no group in the mutable footprint of one task
//! overlaps a group that the other task holds. Two groups overlap if they have
//! the same root and the path of one is a prefix of the path of the other.
//!
//! Main theorem (`task_soundness`): in each interleaving, no step has UB, and
//! no step of one task writes or frees memory that the valid references of the
//! other task reach (no data race). The proof reuses the frame lemma
//! `lemma_ptr_survives`.

use vstd::prelude::*;
use crate::model::*;
use crate::soundness::*;

verus! {

// ---------------------------------------------------------------------------
// Interleaved execution
// ---------------------------------------------------------------------------

/// The private part of a task.
pub struct Task {
    pub vars: Map<Var, Ptr>,
    pub clos: Map<CVar, Seq<(Ptr, bool)>>,
    pub pc: nat,
}

/// Two tasks and the shared heap.
pub struct TState {
    pub heap: Heap,
    pub locals: Map<Local, Addr>,
    pub next_stamp: Stamp,
    pub t0: Task,
    pub t1: Task,
}

/// The private part of task `t`.
pub open spec fn task(ts: TState, t: nat) -> Task {
    if t == 0 {
        ts.t0
    } else {
        ts.t1
    }
}

/// The state that task `t` sees.
pub open spec fn tview(ts: TState, t: nat) -> DState {
    DState {
        heap: ts.heap,
        locals: ts.locals,
        vars: task(ts, t).vars,
        clos: task(ts, t).clos,
        next_stamp: ts.next_stamp,
    }
}

/// Task `t` made the step to `d2`: the shared parts and its own part change.
pub open spec fn merge(ts: TState, t: nat, d2: DState) -> TState {
    let tk = Task { vars: d2.vars, clos: d2.clos, pc: task(ts, t).pc + 1 };
    if t == 0 {
        TState { heap: d2.heap, next_stamp: d2.next_stamp, t0: tk, ..ts }
    } else {
        TState { heap: d2.heap, next_stamp: d2.next_stamp, t1: tk, ..ts }
    }
}

/// The program of task `t`.
pub open spec fn prog_of(p0: Seq<Instr>, p1: Seq<Instr>, t: nat) -> Seq<Instr> {
    if t == 0 {
        p0
    } else {
        p1
    }
}

/// One step of task `t`.
pub open spec fn tstep(p0: Seq<Instr>, p1: Seq<Instr>, ts: TState, t: nat, ts2: TState) -> bool {
    let p = prog_of(p0, p1, t);
    let pc = task(ts, t).pc;
    &&& t < 2
    &&& pc < p.len()
    &&& exists|d2: DState| #[trigger] step(tview(ts, t), p[pc as int], d2) && ts2 == merge(ts, t, d2)
}

/// An interleaving: `sched[k]` is the task that makes step `k`.
pub open spec fn is_itrace(p0: Seq<Instr>, p1: Seq<Instr>, sched: Seq<nat>, trace: Seq<TState>) -> bool {
    &&& trace.len() == sched.len() + 1
    &&& trace[0].t0.pc == 0
    &&& trace[0].t1.pc == 0
    &&& forall|k: int| 0 <= k < sched.len() ==> tstep(p0, p1, #[trigger] trace[k], sched[k], trace[k + 1])
}

// ---------------------------------------------------------------------------
// The separation rule
// ---------------------------------------------------------------------------

/// The argument groups of the mutable part of instruction `i`.
pub open spec fn eff_groups(ss: SState, i: Instr) -> Seq<(Group, bool)> {
    match i {
        Instr::Call { args, .. } => arg_groups(ss, args),
        Instr::Invoke { clo, args, .. } => invoke_groups(ss, clo, args),
        Instr::Write { src, .. } => seq![(ss.vars[src], true)],
        _ => seq![],
    }
}

/// `g` is in the mutable footprint of instruction `i`.
pub open spec fn mut_group(ss: SState, i: Instr, g: Group) -> bool {
    exists|k: int| 0 <= k < eff_groups(ss, i).len() && eff_groups(ss, i)[k].1 && #[trigger] eff_groups(ss, i)[k].0 == g
}

/// The task holds a reference, or a captured reference, in group `g`.
pub open spec fn held(ss: SState, g: Group) -> bool {
    ||| exists|v: Var| ss.vars.contains_key(v) && #[trigger] ss.vars[v] == g
    ||| exists|c: CVar, j: int| ss.clos.contains_key(c) && 0 <= j < ss.clos[c].len() && #[trigger] ss.clos[c][j].0 == g
}

/// Two groups overlap: the same root, and one path is a prefix of the other.
pub open spec fn overlap(a: Group, b: Group) -> bool {
    a.root == b.root && (a.path.is_prefix_of(b.path) || b.path.is_prefix_of(a.path))
}

/// **The task separation rule.** No mutable footprint group of task `a`, at
/// any of its instructions, overlaps a group that task `b` holds at any point.
pub open spec fn separated(ssa: SState, pa: Seq<Instr>, ssb: SState, pb: Seq<Instr>) -> bool {
    forall|k: nat, m: nat, g: Group, h: Group|
        k < pa.len() && m <= pb.len() && #[trigger] mut_group(ss_at(ssa, pa, k), pa[k as int], g) && #[trigger] held(
            ss_at(ssb, pb, m),
            h,
        ) ==> !overlap(g, h)
}

// ---------------------------------------------------------------------------
// Data races
// ---------------------------------------------------------------------------

/// A route leads from `m` to `a` (`a` is `m` or below `m`).
pub open spec fn reaches_from(h: Heap, m: Addr, a: Addr) -> bool {
    exists|r: Route| #[trigger] resolve(h, m, r) == Some(a)
}

/// The step of `i` can change or free allocation `a`.
pub open spec fn writes(s: DState, i: Instr, a: Addr) -> bool {
    match i {
        Instr::Write { src, .. } => a == s.vars[src].addr,
        Instr::Call { args, .. } => footprint(s.heap, arg_ptrs(s, args), a),
        Instr::Invoke { clo, args, .. } => footprint(s.heap, invoke_ptrs(s, clo, args), a),
        _ => false,
    }
}

/// A valid reference, or a valid captured reference, of the task reaches `a`.
pub open spec fn reach(s: DState, ss: SState, a: Addr) -> bool {
    ||| exists|v: Var| ss.vars.contains_key(v) && #[trigger] reaches_from(s.heap, s.vars[v].addr, a)
    ||| exists|c: CVar, j: int|
        ss.clos.contains_key(c) && 0 <= j < ss.clos[c].len() && #[trigger] reaches_from(s.heap, s.clos[c][j].0.addr, a)
}

/// No data race: the step of `i` writes nothing that the other task reaches.
pub open spec fn race_free(s: DState, i: Instr, so: DState, sso: SState) -> bool {
    forall|a: Addr| #[trigger] writes(s, i, a) ==> !reach(so, sso, a)
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// Steps keep the locals.
pub proof fn lemma_step_locals(s: DState, i: Instr, s2: DState)
    requires
        step(s, i, s2),
    ensures
        s2.locals == s.locals,
{
    match i {
        Instr::Call { args, ret } => {
            let (h2, n2) = choose|h2: Heap, n2: Stamp|
                #[trigger] callee_effect(s, arg_ptrs(s, args), h2, n2) && call_result(s, arg_ptrs(s, args), ret, h2, n2, s2);
        },
        Instr::Invoke { clo, args, ret, once } => {
            let s1 = consume(s, clo, once);
            let ps = invoke_ptrs(s, clo, args);
            let (h2, n2) = choose|h2: Heap, n2: Stamp| #[trigger] callee_effect(s1, ps, h2, n2) && call_result(s1, ps, ret, h2, n2, s2);
        },
        _ => {},
    }
}

/// Two valid pointers that both reach `a` have overlapping groups (unique routes).
pub proof fn lemma_shared_overlap(s: DState, g1: Group, p1: Ptr, g2: Group, p2: Ptr, a: Addr)
    requires
        wf(s),
        ptr_ok(s, g1, p1),
        ptr_ok(s, g2, p2),
        reaches_from(s.heap, p1.addr, a),
        reaches_from(s.heap, p2.addr, a),
    ensures
        overlap(g1, g2),
{
    let h = s.heap;
    let t1 = choose|r: Route| #[trigger] resolve(h, p1.addr, r) == Some(a);
    let t2 = choose|r: Route| #[trigger] resolve(h, p2.addr, r) == Some(a);
    let r1 = choose|r: Route| labels(r) == g1.path && #[trigger] resolve(h, s.locals[g1.root], r) == Some(p1.addr);
    let r2 = choose|r: Route| labels(r) == g2.path && #[trigger] resolve(h, s.locals[g2.root], r) == Some(p2.addr);
    lemma_resolve_concat(h, s.locals[g1.root], r1, t1, p1.addr);
    lemma_resolve_concat(h, s.locals[g2.root], r2, t2, p2.addr);
    lemma_resolve_unique(h, s.locals[g1.root], s.locals[g2.root], r1 + t1, r2 + t2, a);
    assert(g1.root == g2.root);
    lemma_labels_concat(r1, t1);
    lemma_labels_concat(r2, t2);
    let all = g1.path + labels(t1);
    assert(all == g2.path + labels(t2));
    if g1.path.len() <= g2.path.len() {
        assert(g1.path =~= g2.path.subrange(0, g1.path.len() as int)) by {
            assert forall|j: int| 0 <= j < g1.path.len() implies g1.path[j] == g2.path[j] by {
                assert(all[j] == g1.path[j]);
                assert(all[j] == g2.path[j]);
            }
        }
    } else {
        assert(g2.path =~= g1.path.subrange(0, g2.path.len() as int)) by {
            assert forall|j: int| 0 <= j < g2.path.len() implies g1.path[j] == g2.path[j] by {
                assert(all[j] == g1.path[j]);
                assert(all[j] == g2.path[j]);
            }
        }
    }
}

/// The mutable part of an accepted instruction passes pointers that match its groups.
proof fn lemma_eff_ok(s: DState, ss: SState, i: Instr)
    requires
        inv(s, ss),
        instr_ok(ss, i),
        i is Call || i is Invoke || i is Write,
    ensures
        args_ok(
            s,
            eff_groups(ss, i),
            match i {
                Instr::Call { args, .. } => arg_ptrs(s, args),
                Instr::Invoke { clo, args, .. } => invoke_ptrs(s, clo, args),
                Instr::Write { src, .. } => seq![(s.vars[src], true)],
                _ => seq![],
            },
        ),
{
    match i {
        Instr::Call { args, .. } => {
            lemma_args_ok_vars(s, ss, args);
        },
        Instr::Invoke { clo, args, .. } => {
            lemma_args_ok_vars(s, ss, args);
            lemma_args_ok_concat(s, arg_groups(ss, args), arg_ptrs(s, args), ss.clos[clo], s.clos[clo]);
        },
        Instr::Write { src, .. } => {
            assert(ref_ok(s, ss.vars[src], src));
            let gs = seq![(ss.vars[src], true)];
            let ps = seq![(s.vars[src], true)];
            assert forall|k: int| 0 <= k < gs.len() implies gs[k].1 == ps[k].1 && ptr_ok(s, #[trigger] gs[k].0, ps[k].0) by {
                assert(k == 0);
            }
        },
        _ => {},
    }
}

/// A pointer of the other task is valid in the view of the stepping task (same heap and locals).
proof fn lemma_other_reach(so: DState, sso: SState, s: DState, a: Addr) -> (r: (Group, Ptr))
    requires
        inv(so, sso),
        reach(so, sso, a),
        s.heap == so.heap,
        s.locals == so.locals,
    ensures
        held(sso, r.0),
        ptr_ok(s, r.0, r.1),
        reaches_from(s.heap, r.1.addr, a),
{
    if exists|v: Var| sso.vars.contains_key(v) && #[trigger] reaches_from(so.heap, so.vars[v].addr, a) {
        let v = choose|v: Var| sso.vars.contains_key(v) && #[trigger] reaches_from(so.heap, so.vars[v].addr, a);
        assert(ref_ok(so, sso.vars[v], v));
        lemma_ptr_ok_transfer(so, s, sso.vars[v], so.vars[v]);
        assert(held(sso, sso.vars[v]));
        (sso.vars[v], so.vars[v])
    } else {
        let (c, j) = choose|c: CVar, j: int|
            sso.clos.contains_key(c) && 0 <= j < sso.clos[c].len() && #[trigger] reaches_from(so.heap, so.clos[c][j].0.addr, a);
        assert(args_ok(so, sso.clos[c], so.clos[c]));
        assert(ptr_ok(so, sso.clos[c][j].0, so.clos[c][j].0));
        lemma_ptr_ok_transfer(so, s, sso.clos[c][j].0, so.clos[c][j].0);
        assert(held(sso, sso.clos[c][j].0));
        (sso.clos[c][j].0, so.clos[c][j].0)
    }
}

/// **No data race at one step.** If the separation rule holds for
/// instruction `i`, then its step writes nothing that the other task reaches.
pub proof fn lemma_race_free(s: DState, ss: SState, i: Instr, so: DState, sso: SState)
    requires
        inv(s, ss),
        inv(so, sso),
        instr_ok(ss, i),
        s.heap == so.heap,
        s.locals == so.locals,
        sep_at(ss, i, sso),
    ensures
        race_free(s, i, so, sso),
{
    assert forall|a: Addr| #[trigger] writes(s, i, a) implies !reach(so, sso, a) by {
        if reach(so, sso, a) {
            let (gh, ph) = lemma_other_reach(so, sso, s, a);
            let gs = eff_groups(ss, i);
            lemma_eff_ok(s, ss, i);
            let ps = match i {
                Instr::Call { args, .. } => arg_ptrs(s, args),
                Instr::Invoke { clo, args, .. } => invoke_ptrs(s, clo, args),
                Instr::Write { src, .. } => seq![(s.vars[src], true)],
                _ => seq![],
            };
            // the mutable argument whose footprint holds `a`
            let k = if i is Write {
                0int
            } else {
                if is_mut_root(ps, a) {
                    choose|k: int| 0 <= k < ps.len() && ps[k].1 && #[trigger] ps[k].0.addr == a
                } else {
                    let m = choose|m: Addr| is_mut_root(ps, m) && #[trigger] below(s.heap, m, a);
                    choose|k: int| 0 <= k < ps.len() && ps[k].1 && #[trigger] ps[k].0.addr == m
                }
            };
            assert(0 <= k < ps.len() && ps[k].1);
            assert(reaches_from(s.heap, ps[k].0.addr, a)) by {
                if ps[k].0.addr == a {
                    assert(resolve(s.heap, a, Seq::<Step>::empty()) == Some(a));
                } else {
                    let m = ps[k].0.addr;
                    assert(below(s.heap, m, a));
                }
            }
            assert(ptr_ok(s, gs[k].0, ps[k].0));
            lemma_shared_overlap(s, gs[k].0, ps[k].0, gh, ph, a);
            assert(mut_group(ss, i, gs[k].0));
        }
    }
}

/// A killed group overlaps a mutable footprint group.
proof fn lemma_killed_overlap(gs: Seq<(Group, bool)>, g: Group) -> (k: int)
    requires
        killed(gs, g),
    ensures
        0 <= k < gs.len(),
        gs[k].1,
        overlap(gs[k].0, g),
{
    let k = choose|k: int| 0 <= k < gs.len() && gs[k].1 && #[trigger] strict_child(g, gs[k].0);
    assert(gs[k].0.path.is_prefix_of(g.path));
    k
}

/// The separation rule for one instruction and the other task.
pub open spec fn sep_at(ss: SState, i: Instr, sso: SState) -> bool {
    forall|g: Group, h: Group| #[trigger] mut_group(ss, i, g) && #[trigger] held(sso, h) ==> !overlap(g, h)
}

/// A call does not kill a group that the other task holds.
proof fn lemma_not_killed(ss: SState, i: Instr, gs: Seq<(Group, bool)>, sso: SState, g: Group)
    requires
        sep_at(ss, i, sso),
        held(sso, g),
        gs == eff_groups(ss, i),
    ensures
        !killed(gs, g),
{
    if killed(gs, g) {
        let k = lemma_killed_overlap(gs, g);
        assert(mut_group(ss, i, gs[k].0));
    }
}

/// One pointer of the other task stays valid across a call or an invoke (frame lemma).
proof fn lemma_other_ptr_call(s: DState, ss: SState, i: Instr, s2: DState, so: DState, sso: SState, g: Group, p: Ptr)
    requires
        inv(s, ss),
        instr_ok(ss, i),
        step(s, i, s2),
        i is Call || i is Invoke,
        s.heap == so.heap,
        s.locals == so.locals,
        sep_at(ss, i, sso),
        held(sso, g),
        ptr_ok(s, g, p),
    ensures
        ptr_ok(DState { heap: s2.heap, next_stamp: s2.next_stamp, ..so }, g, p),
{
    let so2 = DState { heap: s2.heap, next_stamp: s2.next_stamp, ..so };
    lemma_eff_ok(s, ss, i);
    match i {
        Instr::Call { args, ret } => {
            let gs = arg_groups(ss, args);
            let ps = arg_ptrs(s, args);
            let (h2, n2) = choose|h2: Heap, n2: Stamp|
                #[trigger] callee_effect(s, ps, h2, n2) && call_result(s, ps, ret, h2, n2, s2);
            lemma_not_killed(ss, i, gs, sso, g);
            lemma_ptr_survives(s, gs, ps, h2, n2, g, p);
            lemma_ptr_ok_transfer(DState { heap: h2, next_stamp: n2, ..s }, so2, g, p);
        },
        Instr::Invoke { clo, args, ret, once } => {
            let gs = invoke_groups(ss, clo, args);
            let ps = invoke_ptrs(s, clo, args);
            let s1 = consume(s, clo, once);
            lemma_args_ok_transfer_pub(s, s1, gs, ps);
            lemma_ptr_ok_transfer(s, s1, g, p);
            let (h2, n2) = choose|h2: Heap, n2: Stamp|
                #[trigger] callee_effect(s1, ps, h2, n2) && call_result(s1, ps, ret, h2, n2, s2);
            lemma_not_killed(ss, i, gs, sso, g);
            lemma_ptr_survives(s1, gs, ps, h2, n2, g, p);
            lemma_ptr_ok_transfer(DState { heap: h2, next_stamp: n2, ..s1 }, so2, g, p);
        },
        _ => {},
    }
}

/// One pointer of the other task stays valid across any step that follows the separation rule.
proof fn lemma_other_ptr(s: DState, ss: SState, i: Instr, s2: DState, so: DState, sso: SState, g: Group, p: Ptr)
    requires
        inv(s, ss),
        instr_ok(ss, i),
        step(s, i, s2),
        s.heap == so.heap,
        s.locals == so.locals,
        sep_at(ss, i, sso),
        held(sso, g),
        ptr_ok(so, g, p),
    ensures
        ptr_ok(DState { heap: s2.heap, next_stamp: s2.next_stamp, ..so }, g, p),
{
    let so2 = DState { heap: s2.heap, next_stamp: s2.next_stamp, ..so };
    lemma_ptr_ok_transfer(so, s, g, p);
    lemma_step_locals(s, i, s2);
    match i {
        Instr::Write { src, field, val } => {
            let h = s.heap;
            let h2 = s2.heap;
            assert(h2.dom() =~= h.dom());
            assert forall|r: Route, a0: Addr| #[trigger] resolve(h2, a0, r) == resolve(h, a0, r) by {
                lemma_resolve_same_kids(h, h2, a0, r);
            }
            let r = choose|r: Route| labels(r) == g.path && #[trigger] resolve(h, s.locals[g.root], r) == Some(p.addr);
            assert(resolve(so2.heap, so2.locals[g.root], r) == Some(p.addr));
        },
        Instr::Call { .. } => {
            lemma_other_ptr_call(s, ss, i, s2, so, sso, g, p);
        },
        Instr::Invoke { .. } => {
            lemma_other_ptr_call(s, ss, i, s2, so, sso, g, p);
        },
        _ => {
            lemma_ptr_ok_transfer(s, so2, g, p);
        },
    }
}

/// The other task keeps its invariant when the stepping task follows the separation rule.
pub proof fn lemma_other_task(s: DState, ss: SState, i: Instr, s2: DState, so: DState, sso: SState)
    requires
        inv(s, ss),
        inv(so, sso),
        instr_ok(ss, i),
        step(s, i, s2),
        s.heap == so.heap,
        s.locals == so.locals,
        s.next_stamp == so.next_stamp,
        sep_at(ss, i, sso),
    ensures
        inv(DState { heap: s2.heap, next_stamp: s2.next_stamp, ..so }, sso),
{
    let so2 = DState { heap: s2.heap, next_stamp: s2.next_stamp, ..so };
    lemma_preserve(s, ss, i, s2);
    lemma_step_locals(s, i, s2);
    assert(wf(so2));
    assert forall|v: Var| #[trigger] sso.vars.contains_key(v) implies ref_ok(so2, sso.vars[v], v) by {
        assert(ref_ok(so, sso.vars[v], v));
        assert(held(sso, sso.vars[v]));
        lemma_other_ptr(s, ss, i, s2, so, sso, sso.vars[v], so.vars[v]);
    }
    assert forall|c: CVar| #[trigger] sso.clos.contains_key(c) implies so2.clos.contains_key(c) && args_ok(so2, sso.clos[c], so2.clos[c]) by {
        assert(args_ok(so, sso.clos[c], so.clos[c]));
        assert forall|j: int| 0 <= j < sso.clos[c].len() implies sso.clos[c][j].1 == so2.clos[c][j].1 && ptr_ok(so2, #[trigger] sso.clos[c][j].0, so2.clos[c][j].0) by {
            assert(ptr_ok(so, sso.clos[c][j].0, so.clos[c][j].0));
            assert(held(sso, sso.clos[c][j].0));
            lemma_other_ptr(s, ss, i, s2, so, sso, sso.clos[c][j].0, so.clos[c][j].0);
        }
    }
}

proof fn lemma_args_ok_transfer_pub(s: DState, s2: DState, gs: Seq<(Group, bool)>, ps: Seq<(Ptr, bool)>)
    requires
        args_ok(s, gs, ps),
        s2.heap == s.heap,
        s2.locals == s.locals,
    ensures
        args_ok(s2, gs, ps),
{
    assert forall|k: int| 0 <= k < gs.len() implies gs[k].1 == ps[k].1 && ptr_ok(s2, #[trigger] gs[k].0, ps[k].0) by {
        lemma_ptr_ok_transfer(s, s2, gs[k].0, ps[k].0);
    }
}

// ---------------------------------------------------------------------------
// Main theorem
// ---------------------------------------------------------------------------

/// The other task.
pub open spec fn other(t: nat) -> nat {
    if t == 0 {
        1
    } else {
        0
    }
}

/// The checker state of task `t` at its program counter.
pub open spec fn tss(ss0: SState, ss1: SState, p0: Seq<Instr>, p1: Seq<Instr>, ts: TState, t: nat) -> SState {
    if t == 0 {
        ss_at(ss0, p0, ts.t0.pc)
    } else {
        ss_at(ss1, p1, ts.t1.pc)
    }
}

/// The invariant of an interleaved state: the view of each task satisfies
/// `inv` with the checker state at its program counter.
pub open spec fn tinv(ss0: SState, ss1: SState, p0: Seq<Instr>, p1: Seq<Instr>, ts: TState) -> bool {
    &&& ts.t0.pc <= p0.len()
    &&& ts.t1.pc <= p1.len()
    &&& inv(tview(ts, 0), tss(ss0, ss1, p0, p1, ts, 0))
    &&& inv(tview(ts, 1), tss(ss0, ss1, p0, p1, ts, 1))
}

proof fn lemma_sep_at(
    ss0: SState,
    ss1: SState,
    p0: Seq<Instr>,
    p1: Seq<Instr>,
    ts: TState,
    t: nat,
)
    requires
        separated(ss0, p0, ss1, p1),
        separated(ss1, p1, ss0, p0),
        t < 2,
        ts.t0.pc <= p0.len(),
        ts.t1.pc <= p1.len(),
        task(ts, t).pc < prog_of(p0, p1, t).len(),
    ensures
        sep_at(
            tss(ss0, ss1, p0, p1, ts, t),
            prog_of(p0, p1, t)[task(ts, t).pc as int],
            tss(ss0, ss1, p0, p1, ts, other(t)),
        ),
{
    let ss = tss(ss0, ss1, p0, p1, ts, t);
    let i = prog_of(p0, p1, t)[task(ts, t).pc as int];
    let sso = tss(ss0, ss1, p0, p1, ts, other(t));
    assert forall|g: Group, h: Group| #[trigger] mut_group(ss, i, g) && #[trigger] held(sso, h) implies !overlap(g, h) by {
        if t == 0 {
            assert(mut_group(ss_at(ss0, p0, ts.t0.pc), p0[ts.t0.pc as int], g));
            assert(held(ss_at(ss1, p1, ts.t1.pc), h));
        } else {
            assert(mut_group(ss_at(ss1, p1, ts.t1.pc), p1[ts.t1.pc as int], g));
            assert(held(ss_at(ss0, p0, ts.t0.pc), h));
        }
    }
}

/// A step of either task keeps the interleaved invariant.
proof fn lemma_tinv_step(
    ss0: SState,
    ss1: SState,
    p0: Seq<Instr>,
    p1: Seq<Instr>,
    ts: TState,
    t: nat,
    ts2: TState,
)
    requires
        tinv(ss0, ss1, p0, p1, ts),
        check(ss0, p0),
        check(ss1, p1),
        separated(ss0, p0, ss1, p1),
        separated(ss1, p1, ss0, p0),
        tstep(p0, p1, ts, t, ts2),
    ensures
        tinv(ss0, ss1, p0, p1, ts2),
{
    let p = prog_of(p0, p1, t);
    let pc = task(ts, t).pc;
    let i = p[pc as int];
    let d = tview(ts, t);
    let d2 = choose|d2: DState| #[trigger] step(d, i, d2) && ts2 == merge(ts, t, d2);
    let ss = tss(ss0, ss1, p0, p1, ts, t);
    let o = other(t);
    let so = tview(ts, o);
    let sso = tss(ss0, ss1, p0, p1, ts, o);
    if t == 0 {
        assert(instr_ok(ss_at(ss0, p0, pc), p0[pc as int]));
    } else {
        assert(instr_ok(ss_at(ss1, p1, pc), p1[pc as int]));
    }
    assert(instr_ok(ss, i));
    lemma_step_locals(d, i, d2);
    lemma_preserve(d, ss, i, d2);
    lemma_sep_at(ss0, ss1, p0, p1, ts, t);
    lemma_other_task(d, ss, i, d2, so, sso);
    assert(tview(ts2, t) == d2);
    assert(tview(ts2, o) == DState { heap: d2.heap, next_stamp: d2.next_stamp, ..so });
    assert(tss(ss0, ss1, p0, p1, ts2, t) == post(ss, i));
    assert(tss(ss0, ss1, p0, p1, ts2, o) == sso);
}

proof fn lemma_tinv_along(
    ss0: SState,
    ss1: SState,
    p0: Seq<Instr>,
    p1: Seq<Instr>,
    sched: Seq<nat>,
    trace: Seq<TState>,
    k: nat,
)
    requires
        inv(tview(trace[0], 0), ss0),
        inv(tview(trace[0], 1), ss1),
        check(ss0, p0),
        check(ss1, p1),
        separated(ss0, p0, ss1, p1),
        separated(ss1, p1, ss0, p0),
        is_itrace(p0, p1, sched, trace),
        k < trace.len(),
    ensures
        tinv(ss0, ss1, p0, p1, trace[k as int]),
    decreases k,
{
    if k == 0 {
        assert(ss_at(ss0, p0, 0) == ss0);
        assert(ss_at(ss1, p1, 0) == ss1);
    } else {
        let km = (k - 1) as int;
        lemma_tinv_along(ss0, ss1, p0, p1, sched, trace, km as nat);
        assert(tstep(p0, p1, trace[km], sched[km], trace[km + 1]));
        lemma_tinv_step(ss0, ss1, p0, p1, trace[km], sched[km], trace[km + 1]);
    }
}

/// **Task separation.** If the checker accepts each task, and the tasks
/// follow the separation rule, then in each interleaving no pending
/// instruction has UB, and none writes or frees memory that the valid
/// references of the other task reach (no data race).
pub proof fn task_soundness(
    p0: Seq<Instr>,
    p1: Seq<Instr>,
    ss0: SState,
    ss1: SState,
    sched: Seq<nat>,
    trace: Seq<TState>,
)
    requires
        inv(tview(trace[0], 0), ss0),
        inv(tview(trace[0], 1), ss1),
        check(ss0, p0),
        check(ss1, p1),
        separated(ss0, p0, ss1, p1),
        separated(ss1, p1, ss0, p0),
        is_itrace(p0, p1, sched, trace),
    ensures
        forall|k: int, t: nat|
            0 <= k < trace.len() && t < 2 && #[trigger] task(trace[k], t).pc < prog_of(p0, p1, t).len() ==> {
                let i = prog_of(p0, p1, t)[task(trace[k], t).pc as int];
                &&& !ub(tview(trace[k], t), i)
                &&& race_free(tview(trace[k], t), i, tview(trace[k], other(t)), tss(ss0, ss1, p0, p1, trace[k], other(t)))
            },
{
    assert forall|k: int, t: nat|
        0 <= k < trace.len() && t < 2 && #[trigger] task(trace[k], t).pc < prog_of(p0, p1, t).len() implies {
            let i = prog_of(p0, p1, t)[task(trace[k], t).pc as int];
            &&& !ub(tview(trace[k], t), i)
            &&& race_free(tview(trace[k], t), i, tview(trace[k], other(t)), tss(ss0, ss1, p0, p1, trace[k], other(t)))
        } by {
        let ts = trace[k];
        lemma_tinv_along(ss0, ss1, p0, p1, sched, trace, k as nat);
        let pc = task(ts, t).pc;
        let i = prog_of(p0, p1, t)[pc as int];
        let ss = tss(ss0, ss1, p0, p1, ts, t);
        if t == 0 {
            assert(instr_ok(ss_at(ss0, p0, pc), p0[pc as int]));
        } else {
            assert(instr_ok(ss_at(ss1, p1, pc), p1[pc as int]));
        }
        lemma_no_ub(tview(ts, t), ss, i);
        lemma_sep_at(ss0, ss1, p0, p1, ts, t);
        lemma_race_free(tview(ts, t), ss, i, tview(ts, other(t)), tss(ss0, ss1, p0, p1, ts, other(t)));
    }
}

} // verus!
