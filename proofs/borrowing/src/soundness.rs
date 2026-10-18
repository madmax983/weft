//! # Soundness of group borrowing
//!
//! Main theorem (`soundness`): if a program passes the group-borrowing
//! checker, then no execution of it — for any choice of indices and any
//! well-behaved callees — ever dereferences a dangling reference.
//!
//! The proof is progress + preservation for the invariant `inv`: every
//! reference the checker considers valid is live, *and* is reachable from its
//! group's root local along a route whose labels are exactly the group's path.
//! The key facts are
//!   * ownership is a forest, so every allocation has exactly one route from
//!     a root (`lemma_resolve_unique`); hence an allocation a callee could
//!     free (a strict descendant of a mutable argument) sits in a strict child
//!     group of that argument's group, which is exactly what the checker kills
//!     (`lemma_survivor_not_below`);
//!   * everything else lies outside the callee's footprint, so its route and
//!     its allocation are untouched (`lemma_route_preserved`).

use vstd::prelude::*;
use crate::model::*;

verus! {

// ---------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------

pub open spec fn reaches(s: DState, g: Group, a: Addr) -> bool {
    exists|r: Route| labels(r) == g.path && #[trigger] resolve(s.heap, s.locals[g.root], r) == Some(a)
}

/// Reference variable `v`, which the checker believes is valid in group `g`, really is.
pub open spec fn ref_ok(s: DState, g: Group, v: Var) -> bool {
    &&& s.vars.contains_key(v)
    &&& s.locals.contains_key(g.root)
    &&& live(s, s.vars[v])
    &&& reaches(s, g, s.vars[v].addr)
}

pub open spec fn inv(s: DState, ss: SState) -> bool {
    &&& wf(s)
    &&& ss.locals == s.locals.dom()
    &&& forall|v: Var| #[trigger] ss.vars.contains_key(v) ==> ref_ok(s, ss.vars[v], v)
}

// ---------------------------------------------------------------------------
// Routes
// ---------------------------------------------------------------------------

proof fn lemma_resolve_push(h: Heap, a: Addr, r: Route, st: Step)
    ensures
        resolve(h, a, r.push(st)) == match resolve(h, a, r) {
            Some(b) => kid_at(h, b, st),
            None => None,
        },
{
    assert(r.push(st).drop_last() =~= r);
}

proof fn lemma_resolve_concat(h: Heap, a: Addr, r1: Route, r2: Route, b: Addr)
    requires
        resolve(h, a, r1) == Some(b),
    ensures
        resolve(h, a, r1 + r2) == resolve(h, b, r2),
    decreases r2.len(),
{
    if r2.len() == 0 {
        assert(r1 + r2 =~= r1);
    } else {
        let r2p = r2.drop_last();
        let st = r2.last();
        lemma_resolve_concat(h, a, r1, r2p, b);
        assert(r1 + r2 =~= (r1 + r2p).push(st));
        assert(r2 =~= r2p.push(st));
        lemma_resolve_push(h, a, r1 + r2p, st);
        lemma_resolve_push(h, b, r2p, st);
    }
}

proof fn lemma_labels_push(r: Route, st: Step)
    ensures
        labels(r.push(st)) == labels(r).push(st.0),
{
    assert(labels(r.push(st)) =~= labels(r).push(st.0));
}

proof fn lemma_labels_concat(r1: Route, r2: Route)
    ensures
        labels(r1 + r2) == labels(r1) + labels(r2),
{
    assert(labels(r1 + r2) =~= labels(r1) + labels(r2));
}

proof fn lemma_resolve_owner(h: Heap, a: Addr, r: Route, c: Addr) -> (b: Addr)
    requires
        r.len() > 0,
        resolve(h, a, r) == Some(c),
    ensures
        resolve(h, a, r.drop_last()) == Some(b),
        kid_at(h, b, r.last()) == Some(c),
        owns(h, b, r.last().1 as int, c),
        h[b].kids[r.last().1 as int].0 == r.last().0,
{
    resolve(h, a, r.drop_last())->0
}

/// Ownership is a forest: an allocation has at most one route from the roots.
proof fn lemma_resolve_unique(h: Heap, ra: Addr, rb: Addr, r1: Route, r2: Route, c: Addr)
    requires
        unique_owners(h),
        unowned(h, ra),
        unowned(h, rb),
        resolve(h, ra, r1) == Some(c),
        resolve(h, rb, r2) == Some(c),
    ensures
        ra == rb,
        r1 == r2,
    decreases r1.len(),
{
    if r1.len() == 0 {
        if r2.len() > 0 {
            let b2 = lemma_resolve_owner(h, rb, r2, c);
            assert(owns(h, b2, r2.last().1 as int, ra));
        }
    } else if r2.len() == 0 {
        let b1 = lemma_resolve_owner(h, ra, r1, c);
        assert(owns(h, b1, r1.last().1 as int, rb));
    } else {
        let b1 = lemma_resolve_owner(h, ra, r1, c);
        let b2 = lemma_resolve_owner(h, rb, r2, c);
        assert(b1 == b2 && r1.last().1 == r2.last().1);
        lemma_resolve_unique(h, ra, rb, r1.drop_last(), r2.drop_last(), b1);
        assert(r1 =~= r1.drop_last().push(r1.last()));
        assert(r2 =~= r2.drop_last().push(r2.last()));
    }
}

/// Resolution only depends on the heap's domain and kid edges.
proof fn lemma_resolve_same_kids(h: Heap, h2: Heap, a: Addr, r: Route)
    requires
        h2.dom() == h.dom(),
        forall|b: Addr| #[trigger] h.contains_key(b) ==> h2[b].kids == h[b].kids,
    ensures
        resolve(h2, a, r) == resolve(h, a, r),
    decreases r.len(),
{
    if r.len() > 0 {
        lemma_resolve_same_kids(h, h2, a, r.drop_last());
    }
}

// ---------------------------------------------------------------------------
// Helpers for transporting facts between states
// ---------------------------------------------------------------------------

proof fn lemma_ref_ok_transfer(s: DState, s2: DState, g: Group, v: Var, v2: Var)
    requires
        ref_ok(s, g, v),
        s2.heap == s.heap,
        s2.locals == s.locals,
        s2.vars.contains_key(v2),
        s2.vars[v2] == s.vars[v],
    ensures
        ref_ok(s2, g, v2),
{
    let r = choose|r: Route|
        labels(r) == g.path && #[trigger] resolve(s.heap, s.locals[g.root], r) == Some(s.vars[v].addr);
    assert(resolve(s2.heap, s2.locals[g.root], r) == Some(s2.vars[v2].addr));
}

proof fn lemma_wf_transfer(s: DState, s2: DState)
    requires
        wf(s),
        s2.heap == s.heap,
        s2.locals == s.locals,
        s2.next_stamp == s.next_stamp,
    ensures
        wf(s2),
{
}

// ---------------------------------------------------------------------------
// Calls
// ---------------------------------------------------------------------------

/// A reference the checker keeps alive across a call is not inside the
/// callee's reach: otherwise, by uniqueness of routes, its group would be a
/// strict child group of a mutable argument's group.
proof fn lemma_survivor_not_below(s: DState, ss: SState, args: Seq<(Var, bool)>, v: Var)
    requires
        inv(s, ss),
        forall|k: int| 0 <= k < args.len() ==> ss.vars.contains_key(#[trigger] args[k].0),
        ss.vars.contains_key(v),
        !killed(ss, args, ss.vars[v]),
    ensures
        !below_mut(s, args, s.vars[v].addr),
{
    let c = s.vars[v].addr;
    if below_mut(s, args, c) {
        let m = choose|m: Addr| is_mut_root(s, args, m) && #[trigger] below(s.heap, m, c);
        let tau = choose|r: Route| r.len() > 0 && #[trigger] resolve(s.heap, m, r) == Some(c);
        let k = choose|k: int| 0 <= k < args.len() && args[k].1 && #[trigger] s.vars[args[k].0].addr == m;
        let w = args[k].0;
        let gw = ss.vars[w];
        let gv = ss.vars[v];
        assert(ref_ok(s, gw, w));
        assert(ref_ok(s, gv, v));
        let rw = choose|r: Route|
            labels(r) == gw.path && #[trigger] resolve(s.heap, s.locals[gw.root], r) == Some(m);
        let rv = choose|r: Route|
            labels(r) == gv.path && #[trigger] resolve(s.heap, s.locals[gv.root], r) == Some(c);
        lemma_resolve_concat(s.heap, s.locals[gw.root], rw, tau, m);
        lemma_resolve_unique(s.heap, s.locals[gw.root], s.locals[gv.root], rw + tau, rv, c);
        assert(gw.root == gv.root);
        lemma_labels_concat(rw, tau);
        assert(gv.path == gw.path + labels(tau));
        assert(gv.path.subrange(0, gw.path.len() as int) =~= gw.path);
        assert(strict_child(gv, gw));
        assert(killed(ss, args, gv));
    }
}

/// Routes that avoid the callee's footprint survive the call.
proof fn lemma_route_preserved(
    s: DState,
    args: Seq<(Var, bool)>,
    h2: Heap,
    n2: Stamp,
    a: Addr,
    r: Route,
    c: Addr,
)
    requires
        callee_effect(s, args, h2, n2),
        resolve(s.heap, a, r) == Some(c),
        !below_mut(s, args, c),
    ensures
        resolve(h2, a, r) == Some(c),
    decreases r.len(),
{
    if r.len() > 0 {
        let rp = r.drop_last();
        let st = r.last();
        let b = lemma_resolve_owner(s.heap, a, r, c);
        if is_mut_root(s, args, b) {
            let w = Seq::<Step>::empty().push(st);
            lemma_resolve_push(s.heap, b, Seq::empty(), st);
            assert(resolve(s.heap, b, w) == Some(c));
            assert(below(s.heap, b, c));
        }
        if below_mut(s, args, b) {
            let m = choose|m: Addr| is_mut_root(s, args, m) && #[trigger] below(s.heap, m, b);
            let q = choose|q: Route| q.len() > 0 && #[trigger] resolve(s.heap, m, q) == Some(b);
            lemma_resolve_push(s.heap, m, q, st);
            assert(resolve(s.heap, m, q.push(st)) == Some(c));
            assert(below(s.heap, m, c));
        }
        assert(!footprint(s, args, b));
        assert(s.heap.contains_key(b));
        assert(h2.contains_key(b) && h2[b] == s.heap[b]);
        lemma_route_preserved(s, args, h2, n2, a, rp, b);
        assert(kid_at(h2, b, st) == kid_at(s.heap, b, st));
    }
}

proof fn lemma_survivor_ok(s: DState, ss: SState, args: Seq<(Var, bool)>, h2: Heap, n2: Stamp, v: Var)
    requires
        inv(s, ss),
        forall|k: int| 0 <= k < args.len() ==> ss.vars.contains_key(#[trigger] args[k].0),
        callee_effect(s, args, h2, n2),
        ss.vars.contains_key(v),
        !killed(ss, args, ss.vars[v]),
    ensures
        ref_ok(DState { heap: h2, locals: s.locals, vars: s.vars, next_stamp: n2 }, ss.vars[v], v),
{
    let sm = DState { heap: h2, locals: s.locals, vars: s.vars, next_stamp: n2 };
    let g = ss.vars[v];
    let c = s.vars[v].addr;
    assert(ref_ok(s, g, v));
    let r = choose|r: Route| labels(r) == g.path && #[trigger] resolve(s.heap, s.locals[g.root], r) == Some(c);
    lemma_survivor_not_below(s, ss, args, v);
    lemma_route_preserved(s, args, h2, n2, s.locals[g.root], r, c);
    assert(resolve(sm.heap, sm.locals[g.root], r) == Some(c));
    assert(s.heap.contains_key(c));
    if !footprint(s, args, c) {
        assert(h2.contains_key(c) && h2[c] == s.heap[c]);
    } else {
        assert(is_mut_root(s, args, c));
        assert(h2.contains_key(c));
    }
    assert(live(sm, sm.vars[v]));
}

proof fn lemma_preserve_call(s: DState, ss: SState, args: Seq<(Var, bool)>, ret: Option<Ret>, s2: DState)
    requires
        inv(s, ss),
        instr_ok(ss, Instr::Call { args, ret }),
        step(s, Instr::Call { args, ret }, s2),
    ensures
        inv(s2, post(ss, Instr::Call { args, ret })),
{
    let (h2, n2) = choose|h2: Heap, n2: Stamp|
        #[trigger] callee_effect(s, args, h2, n2) && call_result(s, args, ret, h2, n2, s2);
    let sm = DState { heap: h2, locals: s.locals, vars: s.vars, next_stamp: n2 };
    let sv = survivors(ss, args);
    let ss2 = post(ss, Instr::Call { args, ret });
    assert forall|v: Var| #[trigger] sv.contains_key(v) implies ref_ok(sm, sv[v], v) by {
        lemma_survivor_ok(s, ss, args, h2, n2, v);
    }
    assert(wf(sm));
    match ret {
        None => {
            assert(s2 == sm);
            assert(ss2.vars == sv);
        },
        Some(rt) => {
            let route = choose|route: Route|
                {
                    let res = #[trigger] resolve(h2, s.vars[args[rt.arg as int].0].addr, route);
                    &&& labels(route) == rt.path
                    &&& res is Some
                    &&& h2.contains_key(res->0)
                    &&& s2 == DState {
                        heap: h2,
                        locals: s.locals,
                        vars: s.vars.insert(rt.dst, ptr_to(h2, res->0)),
                        next_stamp: n2,
                    }
                };
            let w = args[rt.arg as int].0;
            let aw = s.vars[w].addr;
            let c = resolve(h2, aw, route)->0;
            let gw = ss.vars[w];
            // the argument the result is derived from survives the call
            assert(ss.vars.contains_key(w));
            assert(sv.contains_key(w));
            assert(ref_ok(sm, gw, w));
            let rw = choose|r: Route|
                labels(r) == gw.path && #[trigger] resolve(h2, s.locals[gw.root], r) == Some(aw);
            lemma_resolve_concat(h2, s.locals[gw.root], rw, route, aw);
            lemma_labels_concat(rw, route);
            let gd = Group { root: gw.root, path: gw.path + rt.path };
            assert(ss2.vars == sv.insert(rt.dst, gd));
            assert(resolve(s2.heap, s2.locals[gd.root], rw + route) == Some(s2.vars[rt.dst].addr));
            assert(ref_ok(s2, gd, rt.dst));
            assert forall|v: Var| #[trigger] ss2.vars.contains_key(v) implies ref_ok(s2, ss2.vars[v], v) by {
                if v != rt.dst {
                    lemma_ref_ok_transfer(sm, s2, sv[v], v, v);
                }
            }
            lemma_wf_transfer(sm, s2);
        },
    }
}

// ---------------------------------------------------------------------------
// Preservation and progress
// ---------------------------------------------------------------------------

proof fn lemma_preserve(s: DState, ss: SState, i: Instr, s2: DState)
    requires
        inv(s, ss),
        instr_ok(ss, i),
        step(s, i, s2),
    ensures
        inv(s2, post(ss, i)),
{
    let ss2 = post(ss, i);
    match i {
        Instr::Borrow { dst, x } => {
            lemma_wf_transfer(s, s2);
            let a = s.locals[x];
            let g = Group { root: x, path: Seq::empty() };
            assert(labels(Seq::<Step>::empty()) =~= Seq::<Label>::empty());
            assert(resolve(s2.heap, s2.locals[x], Seq::<Step>::empty()) == Some(a));
            assert(ref_ok(s2, g, dst));
            assert forall|v: Var| #[trigger] ss2.vars.contains_key(v) implies ref_ok(s2, ss2.vars[v], v) by {
                if v != dst {
                    lemma_ref_ok_transfer(s, s2, ss.vars[v], v, v);
                }
            }
        },
        Instr::Child { dst, src, label } => {
            lemma_wf_transfer(s, s2);
            let idx = choose|idx: nat|
                {
                    let res = #[trigger] kid_at(s.heap, s.vars[src].addr, (label, idx));
                    res is Some && s2 == DState { vars: s.vars.insert(dst, ptr_to(s.heap, res->0)), ..s }
                };
            let st: Step = (label, idx);
            let gs = ss.vars[src];
            let a = s.vars[src].addr;
            let c = kid_at(s.heap, a, st)->0;
            assert(ref_ok(s, gs, src));
            let rs = choose|r: Route|
                labels(r) == gs.path && #[trigger] resolve(s.heap, s.locals[gs.root], r) == Some(a);
            lemma_resolve_push(s.heap, s.locals[gs.root], rs, st);
            lemma_labels_push(rs, st);
            assert(s.heap.contains_key(c));
            let g = Group { root: gs.root, path: gs.path.push(label) };
            assert(resolve(s2.heap, s2.locals[g.root], rs.push(st)) == Some(s2.vars[dst].addr));
            assert(ref_ok(s2, g, dst));
            assert forall|v: Var| #[trigger] ss2.vars.contains_key(v) implies ref_ok(s2, ss2.vars[v], v) by {
                if v != dst {
                    lemma_ref_ok_transfer(s, s2, ss.vars[v], v, v);
                }
            }
        },
        Instr::Copy { dst, src } => {
            lemma_wf_transfer(s, s2);
            assert forall|v: Var| #[trigger] ss2.vars.contains_key(v) implies ref_ok(s2, ss2.vars[v], v) by {
                if v == dst {
                    lemma_ref_ok_transfer(s, s2, ss.vars[src], src, dst);
                } else {
                    lemma_ref_ok_transfer(s, s2, ss.vars[v], v, v);
                }
            }
        },
        Instr::Read { .. } => {},
        Instr::Write { src, field, val } => {
            let a = s.vars[src].addr;
            let h = s.heap;
            let h2 = s2.heap;
            assert(h2.dom() =~= h.dom());
            assert forall|b: Addr| #[trigger] h.contains_key(b) implies h2[b].kids == h[b].kids
                && h2[b].stamp == h[b].stamp && h2[b].ty == h[b].ty by {}
            assert forall|b: Addr, j: int, c: Addr| #[trigger] owns(h2, b, j, c) == owns(h, b, j, c) by {}
            assert forall|r: Route, a0: Addr| #[trigger] resolve(h2, a0, r) == resolve(h, a0, r) by {
                lemma_resolve_same_kids(h, h2, a0, r);
            }
            assert(wf(s2));
            assert forall|v: Var| #[trigger] ss2.vars.contains_key(v) implies ref_ok(s2, ss2.vars[v], v) by {
                let g = ss.vars[v];
                assert(ref_ok(s, g, v));
                let r = choose|r: Route|
                    labels(r) == g.path && #[trigger] resolve(s.heap, s.locals[g.root], r) == Some(
                        s.vars[v].addr,
                    );
                assert(resolve(s2.heap, s2.locals[g.root], r) == Some(s2.vars[v].addr));
            }
        },
        Instr::Call { args, ret } => {
            lemma_preserve_call(s, ss, args, ret, s2);
        },
    }
}

proof fn lemma_no_ub(s: DState, ss: SState, i: Instr)
    requires
        inv(s, ss),
        instr_ok(ss, i),
    ensures
        !ub(s, i),
{
    match i {
        Instr::Call { args, .. } => {
            assert forall|k: int| 0 <= k < args.len() implies !#[trigger] dangling(s, args[k].0) by {
                assert(ss.vars.contains_key(args[k].0));
            }
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Main theorem
// ---------------------------------------------------------------------------

proof fn lemma_inv_along(ss0: SState, prog: Seq<Instr>, trace: Seq<DState>, k: nat)
    requires
        inv(trace[0], ss0),
        check(ss0, prog),
        is_trace(prog, trace),
        k < trace.len(),
    ensures
        inv(trace[k as int], ss_at(ss0, prog, k)),
    decreases k,
{
    if k > 0 {
        let km = (k - 1) as nat;
        lemma_inv_along(ss0, prog, trace, km);
        assert(instr_ok(ss_at(ss0, prog, km), prog[km as int]));
        assert(step(trace[km as int], prog[km as int], trace[k as int]));
        lemma_preserve(trace[km as int], ss_at(ss0, prog, km), prog[km as int], trace[k as int]);
    }
}

/// **Soundness of group borrowing.** Every execution of a checked program is
/// free of dangling-reference dereferences (use-after-free, and use of a
/// reused address holding a different allocation or type).
pub proof fn soundness(ss0: SState, prog: Seq<Instr>, trace: Seq<DState>)
    requires
        inv(trace[0], ss0),
        check(ss0, prog),
        is_trace(prog, trace),
    ensures
        forall|k: int| 0 <= k < trace.len() && k < prog.len() ==> !#[trigger] ub(trace[k], prog[k]),
{
    assert forall|k: int| 0 <= k < trace.len() && k < prog.len() implies !#[trigger] ub(trace[k], prog[k]) by {
        lemma_inv_along(ss0, prog, trace, k as nat);
        assert(instr_ok(ss_at(ss0, prog, k as nat), prog[k]));
        lemma_no_ub(trace[k], ss_at(ss0, prog, k as nat), prog[k]);
    }
}

pub open spec fn initial_sstate(s0: DState) -> SState {
    SState { locals: s0.locals.dom(), vars: Map::empty() }
}

/// Soundness from a fresh start: any well-formed initial heap, no references yet.
pub proof fn soundness_from_start(prog: Seq<Instr>, trace: Seq<DState>)
    requires
        is_trace(prog, trace),
        wf(trace[0]),
        check(initial_sstate(trace[0]), prog),
    ensures
        forall|k: int| 0 <= k < trace.len() && k < prog.len() ==> !#[trigger] ub(trace[k], prog[k]),
{
    assert(inv(trace[0], initial_sstate(trace[0])));
    soundness(initial_sstate(trace[0]), prog, trace);
}

} // verus!
