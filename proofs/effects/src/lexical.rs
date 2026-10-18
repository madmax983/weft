//! # E1 (effect safety) and E4 (lexical resolution)

use vstd::prelude::*;
use crate::model::*;
use crate::checker::*;
use crate::scope::*;
use crate::scope_steps::*;

verus! {

// ---------------------------------------------------------------------------
// One state
// ---------------------------------------------------------------------------

/// In a state with `inv_a`, a checked program has no structural error, no
/// unhandled perform, no dead capability, and no resume without a continuation.
pub proof fn lemma_no_struct_error(prog: Prog, s: State)
    requires
        check(prog),
        inv_a(prog, s),
    ensures
        !err_malformed(prog, s),
        !err_unhandled(prog, s),
        !err_dead_cap(prog, s),
        !err_no_k(prog, s),
{
    if top_code(s) {
        let f = tf(s);
        let st = s.stack;
        let t = st.len() - 1;
        lemma_top_ok(prog, s);
        lemma_instr_ok(prog, f);
        let ss = ss_of(prog, f);
        match instr_at(prog, f) {
            Instr::Call { block, caps } => {
                assert(block_ok(prog, block));
                assert forall|j: int| 0 <= j < prog.blocks[block].sig.rets.len() implies #[trigger] prog.blocks[block].sig.rets[j]
                    < caps.len() by {}
                assert(call_ok_dyn(prog, f, block, caps));
            },
            Instr::Handle { body, .. } => {
                assert(handle_ok_dyn(prog, f, body));
            },
            Instr::Perform { cap, op } => {
                let c = f.env[cap as int];
                assert(f.env.contains(c));
                assert(reaches(s, st[t], c));
                assert(hid_in(st, 0, t, c));
                let m = choose|m: int| 0 <= m < t && 0 <= m < st.len() && #[trigger] is_handler(st[m], c);
                assert(on_stack(st, c));
                assert(s.hinfo.contains_key(c));
                assert(hinfo_ok(prog, s, s.hinfo[c]));
                assert(handled(prog, s, f, cap, op));
                assert(clause_ok(prog, s, s.hinfo[c], op as int));
            },
            Instr::Resume => {
                assert(f.k is Some);
            },
            _ => {},
        }
    }
}

// ---------------------------------------------------------------------------
// Traces
// ---------------------------------------------------------------------------

/// `inv_a` holds at every state of an execution of a checked program.
pub proof fn lemma_inv_a_trace(prog: Prog, tr: Seq<State>, i: int)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
        0 <= i < tr.len(),
    ensures
        inv_a(prog, tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_a_init(prog);
    } else {
        lemma_inv_a_trace(prog, tr, i - 1);
        assert(step(prog, tr[i - 1], tr[i]));
        lemma_a_step(prog, tr[i - 1], tr[i]);
    }
}

/// **E1. Effect safety.** No execution of a checked program reaches a perform
/// with no matching live handler (or a malformed instruction).
pub proof fn e1_effect_safety(prog: Prog, tr: Seq<State>)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
    ensures
        forall|i: int|
            0 <= i < tr.len() ==> !#[trigger] err_unhandled(prog, tr[i]) && !err_malformed(prog, tr[i]),
{
    assert forall|i: int| 0 <= i < tr.len() implies !#[trigger] err_unhandled(prog, tr[i]) && !err_malformed(
        prog,
        tr[i],
    ) by {
        lemma_inv_a_trace(prog, tr, i);
        lemma_no_struct_error(prog, tr[i]);
    }
}

// ---------------------------------------------------------------------------
// Handler instances
// ---------------------------------------------------------------------------

/// The handler instance that the `handle` at the top of `s` records.
pub open spec fn recorded(prog: Prog, s: State) -> HInfo {
    match instr_at(prog, tf(s)) {
        Instr::Handle { eff, clauses, .. } => HInfo { eff, clauses, env: tf(s).env },
        _ => HInfo { eff: 0, clauses: Seq::empty(), env: Seq::empty() },
    }
}

/// Step `m` of `tr` is the `handle` that mints capability `c`.
pub open spec fn minted_at(prog: Prog, tr: Seq<State>, m: int, c: HId) -> bool {
    0 <= m < tr.len() - 1 && step_handle(prog, tr[m], tr[m + 1]) && tr[m].next_h == c
}

/// A step keeps every handler instance, and only a `handle` adds one (the
/// next id, with what it records).
pub proof fn lemma_hinfo_step(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        step(prog, s, s2),
    ensures
        forall|h: HId| #[trigger] s.hinfo.contains_key(h) ==> s2.hinfo.contains_key(h) && s2.hinfo[h] == s.hinfo[h],
        forall|h: HId|
            #[trigger] s2.hinfo.contains_key(h) && !s.hinfo.contains_key(h) ==> step_handle(prog, s, s2)
                && h == s.next_h && s2.hinfo[h] == recorded(prog, s),
        s2.next_h >= s.next_h,
        step_handle(prog, s, s2) ==> s2.next_h == s.next_h + 1,
{
    if step_handle(prog, s, s2) {
        assert(!s.hinfo.contains_key(s.next_h));
    } else if step_perform(prog, s, s2) {
        match instr_at(prog, tf(s)) {
            Instr::Perform { cap, op } => {
                let j = choose|j: int|
                    #[trigger] perform_ok_dyn(prog, s, cap, op, j) && s2 == do_perform(
                        prog,
                        s,
                        tf(s).env[cap as int],
                        op,
                        j,
                    );
            },
            _ => {},
        }
    } else if step_cancel(prog, s, s2) {
        match instr_at(prog, tf(s)) {
            Instr::Perform { cap, op } => {
                let j = choose|j: int| #[trigger] perform_ok_dyn(prog, s, cap, op, j) && s2 == do_cancel(s, j);
            },
            _ => {},
        }
    } else if step_unwind_abort(s, s2) {
        let sl = choose|sl: Slot|
            #[trigger] max_slot(pf(s).slots, sl) && slot_live(s, pf(s), sl)
                && s.res[pf(s).slots[sl]].on_abort && s2 == do_abort(s, sl);
    }
}

/// Handler instances never change along an execution.
pub proof fn lemma_hinfo_stable(prog: Prog, tr: Seq<State>, a: int, b: int, c: HId)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
        0 <= a <= b < tr.len(),
        tr[a].hinfo.contains_key(c),
    ensures
        tr[b].hinfo.contains_key(c),
        tr[b].hinfo[c] == tr[a].hinfo[c],
    decreases b - a,
{
    if b > a {
        lemma_hinfo_stable(prog, tr, a, b - 1, c);
        lemma_inv_a_trace(prog, tr, b - 1);
        assert(step(prog, tr[b - 1], tr[b]));
        lemma_hinfo_step(prog, tr[b - 1], tr[b]);
    }
}

/// The next handler id never decreases.
pub proof fn lemma_next_h_mono(prog: Prog, tr: Seq<State>, a: int, b: int)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
        0 <= a <= b < tr.len(),
    ensures
        tr[b].next_h >= tr[a].next_h,
    decreases b - a,
{
    if b > a {
        lemma_next_h_mono(prog, tr, a, b - 1);
        lemma_inv_a_trace(prog, tr, b - 1);
        assert(step(prog, tr[b - 1], tr[b]));
        lemma_hinfo_step(prog, tr[b - 1], tr[b]);
    }
}

/// Every handler instance of a state was minted by an earlier `handle` step,
/// which recorded it.
pub proof fn lemma_minted(prog: Prog, tr: Seq<State>, i: int, c: HId) -> (m: int)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
        0 <= i < tr.len(),
        tr[i].hinfo.contains_key(c),
    ensures
        m < i,
        minted_at(prog, tr, m, c),
        tr[m + 1].hinfo[c] == recorded(prog, tr[m]),
        tr[i].hinfo[c] == recorded(prog, tr[m]),
    decreases i,
{
    assert(i > 0) by {
        if i == 0 {
            assert(!init(prog).hinfo.contains_key(c));
        }
    }
    lemma_inv_a_trace(prog, tr, i - 1);
    assert(step(prog, tr[i - 1], tr[i]));
    lemma_hinfo_step(prog, tr[i - 1], tr[i]);
    if tr[i - 1].hinfo.contains_key(c) {
        lemma_minted(prog, tr, i - 1, c)
    } else {
        i - 1
    }
}

/// A capability is minted once.
pub proof fn lemma_minted_unique(prog: Prog, tr: Seq<State>, m1: int, m2: int, c: HId)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
        minted_at(prog, tr, m1, c),
        minted_at(prog, tr, m2, c),
    ensures
        m1 == m2,
{
    if m1 < m2 {
        lemma_inv_a_trace(prog, tr, m1);
        lemma_hinfo_step(prog, tr[m1], tr[m1 + 1]);
        lemma_next_h_mono(prog, tr, m1 + 1, m2);
    } else if m2 < m1 {
        lemma_inv_a_trace(prog, tr, m2);
        lemma_hinfo_step(prog, tr[m2], tr[m2 + 1]);
        lemma_next_h_mono(prog, tr, m2 + 1, m1);
    }
}

/// Step `i` performs through capability `c` (operation `op`), and the clause
/// that runs is clause `op` of the handler instance minted at step `m`, in the
/// environment of that handle site. The continuation starts at the topmost
/// handler frame of `c`, whatever other handlers are closer on the stack.
pub open spec fn resolves_to(prog: Prog, tr: Seq<State>, i: int, m: int) -> bool {
    let s = tr[i];
    let f = tf(s);
    match instr_at(prog, f) {
        Instr::Perform { cap, op } => {
            let c = f.env[cap as int];
            let hi = recorded(prog, tr[m]);
            &&& minted_at(prog, tr, m, c)
            &&& m < i
            &&& tr[i + 1].stack.last() == Frame::Code(
                CFrame { block: hi.clauses[op as int], pc: 0, env: hi.env, slots: Map::empty(), k: Some(s.next_k) },
            )
            &&& exists|j: int|
                topmost(s.stack, c, j) && #[trigger] tr[i + 1].konts[s.next_k].frames[0] == s.stack[j]
                    && s.stack[j] == Frame::Handler(c)
        },
        _ => false,
    }
}

/// **E4. Lexical resolution.** (1) A checked program never performs through a
/// capability whose handler is gone. (2) For each perform step through `c`,
/// there is exactly one step `m` (a `handle`) that minted `c`, and the clause
/// that runs is the one that `handle` bound, in its environment.
pub proof fn e4_lexical_resolution(prog: Prog, tr: Seq<State>)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
    ensures
        forall|i: int| 0 <= i < tr.len() ==> !#[trigger] err_dead_cap(prog, tr[i]),
        forall|i: int|
            0 <= i < tr.len() - 1 && #[trigger] step_perform(prog, tr[i], tr[i + 1]) ==> exists|m: int|
                resolves_to(prog, tr, i, m) && forall|m2: int|
                    #[trigger] minted_at(prog, tr, m2, tf(tr[i]).env[instr_at(prog, tf(tr[i]))->Perform_cap as int])
                        ==> m2 == m,
{
    assert forall|i: int| 0 <= i < tr.len() implies !#[trigger] err_dead_cap(prog, tr[i]) by {
        lemma_inv_a_trace(prog, tr, i);
        lemma_no_struct_error(prog, tr[i]);
    }
    assert forall|i: int| 0 <= i < tr.len() - 1 && #[trigger] step_perform(prog, tr[i], tr[i + 1]) implies exists|m: int|
        resolves_to(prog, tr, i, m) && forall|m2: int|
            #[trigger] minted_at(prog, tr, m2, tf(tr[i]).env[instr_at(prog, tf(tr[i]))->Perform_cap as int])
                ==> m2 == m by {
        let s = tr[i];
        let f = tf(s);
        lemma_inv_a_trace(prog, tr, i);
        match instr_at(prog, f) {
            Instr::Perform { cap, op } => {
                let c = f.env[cap as int];
                let j = choose|j: int|
                    #[trigger] perform_ok_dyn(prog, s, cap, op, j) && tr[i + 1] == do_perform(prog, s, c, op, j);
                assert(s.hinfo.contains_key(c));
                let m = lemma_minted(prog, tr, i, c);
                let st2 = s.stack.subrange(0, j).push(Frame::Code(clause_frame(s, c, op, s.next_k)));
                assert(tr[i + 1].stack == st2);
                assert(st2.last() == Frame::Code(clause_frame(s, c, op, s.next_k)));
                assert(tr[i + 1].konts[s.next_k].frames == captured(s, j));
                assert(captured(s, j)[0] == s.stack[j]);
                assert(s.stack[j] == Frame::Handler(c));
                assert(resolves_to(prog, tr, i, m));
                assert forall|m2: int| #[trigger] minted_at(prog, tr, m2, c) implies m2 == m by {
                    lemma_minted_unique(prog, tr, m, m2, c);
                }
            },
            _ => {},
        }
    }
}

} // verus!
