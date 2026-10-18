//! # E2 (one-shot), E3 (abort safety), E5 (multi-shot), and soundness

use vstd::prelude::*;
use crate::model::*;
use crate::checker::*;
use crate::scope::*;
use crate::scope_steps::*;
use crate::lexical::*;
use crate::own::*;
use crate::own_steps::*;

verus! {

// ---------------------------------------------------------------------------
// Invariants along an execution
// ---------------------------------------------------------------------------

/// Both invariants hold at every state of an execution of a checked program.
pub proof fn lemma_inv_trace(prog: Prog, tr: Seq<State>, i: int)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
        0 <= i < tr.len(),
    ensures
        inv_a(prog, tr[i]),
        inv_b(prog, tr[i]),
    decreases i,
{
    if i == 0 {
        lemma_a_init(prog);
        lemma_b_init(prog);
    } else {
        lemma_inv_trace(prog, tr, i - 1);
        assert(step(prog, tr[i - 1], tr[i]));
        lemma_a_step(prog, tr[i - 1], tr[i]);
        lemma_b_step(prog, tr[i - 1], tr[i]);
    }
}

/// With both invariants, no ownership error is possible.
pub proof fn lemma_no_own_error(prog: Prog, s: State)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
    ensures
        !err_resume_used(prog, s),
        !err_overwrite(prog, s),
        !err_use_moved(prog, s),
        !err_consumed_twice(prog, s),
        !err_leak(prog, s),
        !err_unwind_dead(s),
        !err_no_on_abort(s),
{
    if at_instr(prog, s) {
        let f = tf(s);
        let p = Pos::Stk((s.stack.len() - 1) as nat);
        lemma_top_ok(prog, s);
        lemma_instr_ok(prog, f);
        assert(ocode(s, p));
        assert(pos_ok(prog, s, p));
        let lin = ss_of(prog, f).lin;
        match instr_at(prog, f) {
            Instr::Acquire { slot, .. } => {
                if f.slots.contains_key(slot) {
                    assert(lin.contains_key(slot));
                }
            },
            Instr::Consume { slot } => {
                assert(lin.contains_key(slot));
            },
            Instr::Resume => {
                assert(k_link(prog, s, f));
            },
            Instr::Return => {
                if nonempty(f.slots) {
                    let sl = choose|sl: Slot| f.slots.contains_key(sl);
                    assert(lin.contains_key(sl));
                }
            },
            _ => {},
        }
    }
    if unwinding(s) && s.pending.last() is Code {
        let f = pf(s);
        let p = Pos::Pnd((s.pending.len() - 1) as nat);
        assert(ocode(s, p));
        assert(pos_ok(prog, s, p));
        assert forall|sl: Slot| #[trigger] max_slot(f.slots, sl) implies slot_live(s, f, sl) && s.res[f.slots[sl]].on_abort by {
            assert(f.slots.contains_key(sl));
            assert(ss_of(prog, f).lin.contains_key(sl));
        }
    }
}

/// **Soundness.** No execution of a checked program reaches an error state.
pub proof fn soundness(prog: Prog, tr: Seq<State>)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
    ensures
        forall|i: int| 0 <= i < tr.len() ==> !#[trigger] error(prog, tr[i]),
{
    assert forall|i: int| 0 <= i < tr.len() implies !#[trigger] error(prog, tr[i]) by {
        lemma_inv_trace(prog, tr, i);
        lemma_no_struct_error(prog, tr[i]);
        lemma_no_own_error(prog, tr[i]);
    }
}

// ---------------------------------------------------------------------------
// Machine facts
// ---------------------------------------------------------------------------

/// A step keeps every continuation (frames and mode), and never makes a used
/// continuation usable again.
pub proof fn lemma_konts_step(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        step(prog, s, s2),
    ensures
        forall|k: KId| #[trigger] s.konts.contains_key(k) ==> s2.konts.contains_key(k)
            && s2.konts[k].multi == s.konts[k].multi && s2.konts[k].frames == s.konts[k].frames
            && (s.konts[k].used ==> s2.konts[k].used),
{
    if step_perform(prog, s, s2) {
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
                assert(!s.konts.contains_key(s.next_k));
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

/// A step keeps every resource, and a finalized resource never changes.
/// Only a consume makes a resource consumed, and only the unwinder makes one aborted.
pub proof fn lemma_res_step(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        step(prog, s, s2),
    ensures
        forall|r: ResId| #[trigger] s.res.contains_key(r) ==> s2.res.contains_key(r),
        forall|r: ResId|
            #[trigger] s.res.contains_key(r) && s.res[r].st != RState::Live ==> s2.res[r] == s.res[r],
        forall|r: ResId|
            #[trigger] live(s, r) && s2.res[r].st == RState::Aborted ==> step_unwind_abort(s, s2)
                && s.res[r].on_abort,
        forall|r: ResId| #[trigger] live(s, r) && s2.res[r].st == RState::Consumed ==> step_consume(prog, s, s2),
        forall|r: ResId|
            #[trigger] s2.res.contains_key(r) && !s.res.contains_key(r) ==> step_acquire(prog, s, s2)
                && s2.res[r].st == RState::Live,
{
    if step_acquire(prog, s, s2) {
        assert(!s.res.contains_key(s.next_res));
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
        let r0 = pf(s).slots[sl];
        assert forall|r: ResId| #[trigger] live(s, r) && s2.res[r].st == RState::Aborted implies s.res[r].on_abort by {
            assert(r == r0);
        }
    }
}

/// A fresh `once` continuation is rooted: some stack or pending frame owns
/// it, directly or through older continuations. So a final state has none.
pub proof fn lemma_no_fresh_at_final(prog: Prog, s: State, kid: KId)
    requires
        inv_a(prog, s),
        inv_b(prog, s),
        final_state(s),
        fresh_once(s, kid),
    ensures
        false,
    decreases s.next_k - kid,
{
    let p = choose|p: Pos| #[trigger] holdsk(s, p, kid);
    match p {
        Pos::Knt(k2, i) => {
            assert(kid < k2);
            assert(fresh_once(s, k2));
            assert(k2 < s.next_k);
            lemma_no_fresh_at_final(prog, s, k2);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// E2. One-shot safety
// ---------------------------------------------------------------------------

/// Step `i` resumes continuation `kid`.
pub open spec fn resumes(prog: Prog, tr: Seq<State>, i: int, kid: KId) -> bool {
    0 <= i < tr.len() - 1 && step_resume(prog, tr[i], tr[i + 1]) && tf(tr[i]).k == Some(kid)
}

/// The use flag never goes back, and the mode never changes.
pub proof fn lemma_used_mono(prog: Prog, tr: Seq<State>, a: int, b: int, kid: KId)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
        0 <= a <= b < tr.len(),
        tr[a].konts.contains_key(kid),
    ensures
        tr[b].konts.contains_key(kid),
        tr[b].konts[kid].multi == tr[a].konts[kid].multi,
        tr[a].konts[kid].used ==> tr[b].konts[kid].used,
    decreases b - a,
{
    if b > a {
        lemma_used_mono(prog, tr, a, b - 1, kid);
        lemma_inv_trace(prog, tr, b - 1);
        assert(step(prog, tr[b - 1], tr[b]));
        lemma_konts_step(prog, tr[b - 1], tr[b]);
    }
}

/// **E2. One-shot safety.** (1) A checked program never resumes a `once`
/// continuation that was already resumed or dropped. (2) In any execution, a
/// `once` continuation is resumed by at most one step.
pub proof fn e2_one_shot_safety(prog: Prog, tr: Seq<State>)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
    ensures
        forall|i: int| 0 <= i < tr.len() ==> !#[trigger] err_resume_used(prog, tr[i]),
        forall|i: int, j: int, kid: KId|
            #[trigger] resumes(prog, tr, i, kid) && #[trigger] resumes(prog, tr, j, kid) && !tr[i].konts[kid].multi
                ==> i == j,
{
    assert forall|i: int| 0 <= i < tr.len() implies !#[trigger] err_resume_used(prog, tr[i]) by {
        lemma_inv_trace(prog, tr, i);
        lemma_no_own_error(prog, tr[i]);
    }
    assert forall|i: int, j: int, kid: KId|
        #[trigger] resumes(prog, tr, i, kid) && #[trigger] resumes(prog, tr, j, kid) && !tr[i].konts[kid].multi implies i
        == j by {
        if i < j {
            assert(tr[i + 1].konts[kid].used);
            lemma_used_mono(prog, tr, i + 1, j, kid);
        } else if j < i {
            lemma_used_mono(prog, tr, j, i, kid);
            assert(tr[j + 1].konts[kid].used);
            lemma_used_mono(prog, tr, j + 1, i, kid);
        }
    }
}

// ---------------------------------------------------------------------------
// E3. Abort safety
// ---------------------------------------------------------------------------

/// A finalized resource stays as it is.
pub proof fn lemma_final_stable(prog: Prog, tr: Seq<State>, a: int, b: int, r: ResId)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
        0 <= a <= b < tr.len(),
        tr[a].res.contains_key(r),
        tr[a].res[r].st != RState::Live,
    ensures
        tr[b].res.contains_key(r),
        tr[b].res[r] == tr[a].res[r],
    decreases b - a,
{
    if b > a {
        lemma_final_stable(prog, tr, a, b - 1, r);
        lemma_inv_trace(prog, tr, b - 1);
        assert(step(prog, tr[b - 1], tr[b]));
        lemma_res_step(prog, tr[b - 1], tr[b]);
    }
}

/// **E3. Abort safety.**
/// (1) No linear error: no leak at a normal return, no overwrite, no use after
///     move or after finalization, and the unwinder never meets a value
///     without `on abort` or a finalized value.
/// (2) Each resource is finalized at most once: once consumed or aborted, it
///     never changes.
/// (3) `on abort` runs only from the unwinder (and only for a type that
///     declares it); a consume happens only on the normal path. The machine
///     starts to unwind only when a clause drops a fresh `once` continuation,
///     or at a cancellation.
/// (4) No leak: at the end of the execution, no resource is live. So each
///     resource ends consumed or aborted, exactly once.
pub proof fn e3_abort_safety(prog: Prog, tr: Seq<State>)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
    ensures
        forall|i: int|
            0 <= i < tr.len() ==> !#[trigger] err_leak(prog, tr[i]) && !err_overwrite(prog, tr[i])
                && !err_use_moved(prog, tr[i]) && !err_consumed_twice(prog, tr[i]) && !err_unwind_dead(tr[i])
                && !err_no_on_abort(tr[i]),
        forall|i: int, j: int, r: ResId|
            0 <= i <= j < tr.len() && #[trigger] tr[i].res.contains_key(r) && tr[i].res[r].st != RState::Live
                ==> #[trigger] tr[j].res.contains_key(r) && tr[j].res[r] == tr[i].res[r],
        forall|i: int, r: ResId|
            0 <= i < tr.len() - 1 && #[trigger] live(tr[i], r) && tr[i + 1].res[r].st == RState::Aborted
                ==> step_unwind_abort(tr[i], tr[i + 1]) && unwinding(tr[i]) && tr[i].res[r].on_abort,
        forall|i: int, r: ResId|
            0 <= i < tr.len() - 1 && #[trigger] live(tr[i], r) && tr[i + 1].res[r].st == RState::Consumed
                ==> step_consume(prog, tr[i], tr[i + 1]) && running(tr[i]),
        forall|i: int|
            0 <= i < tr.len() - 1 && !unwinding(tr[i]) && #[trigger] unwinding(tr[i + 1]) ==> (step_return(
                prog,
                tr[i],
                tr[i + 1],
            ) && holds_fresh(tr[i], tf(tr[i]))) || step_cancel(prog, tr[i], tr[i + 1]),
        forall|i: int, r: ResId|
            0 <= i < tr.len() && final_state(tr[i]) && #[trigger] tr[i].res.contains_key(r) ==> tr[i].res[r].st
                != RState::Live,
{
    assert forall|i: int| 0 <= i < tr.len() implies !#[trigger] err_leak(prog, tr[i]) && !err_overwrite(prog, tr[i])
        && !err_use_moved(prog, tr[i]) && !err_consumed_twice(prog, tr[i]) && !err_unwind_dead(tr[i])
        && !err_no_on_abort(tr[i]) by {
        lemma_inv_trace(prog, tr, i);
        lemma_no_own_error(prog, tr[i]);
    }
    assert forall|i: int, j: int, r: ResId|
        0 <= i <= j < tr.len() && #[trigger] tr[i].res.contains_key(r) && tr[i].res[r].st != RState::Live implies #[trigger] tr[j].res.contains_key(
        r,
    ) && tr[j].res[r] == tr[i].res[r] by {
        lemma_final_stable(prog, tr, i, j, r);
    }
    assert forall|i: int, r: ResId|
        0 <= i < tr.len() - 1 && #[trigger] live(tr[i], r) && tr[i + 1].res[r].st == RState::Aborted implies step_unwind_abort(
        tr[i],
        tr[i + 1],
    ) && unwinding(tr[i]) && tr[i].res[r].on_abort by {
        lemma_inv_trace(prog, tr, i);
        assert(step(prog, tr[i], tr[i + 1]));
        lemma_res_step(prog, tr[i], tr[i + 1]);
    }
    assert forall|i: int, r: ResId|
        0 <= i < tr.len() - 1 && #[trigger] live(tr[i], r) && tr[i + 1].res[r].st == RState::Consumed implies step_consume(
        prog,
        tr[i],
        tr[i + 1],
    ) && running(tr[i]) by {
        lemma_inv_trace(prog, tr, i);
        assert(step(prog, tr[i], tr[i + 1]));
        lemma_res_step(prog, tr[i], tr[i + 1]);
    }
    assert forall|i: int| 0 <= i < tr.len() - 1 && !unwinding(tr[i]) && #[trigger] unwinding(tr[i + 1]) implies (step_return(
        prog,
        tr[i],
        tr[i + 1],
    ) && holds_fresh(tr[i], tf(tr[i]))) || step_cancel(prog, tr[i], tr[i + 1]) by {
        let s = tr[i];
        let s2 = tr[i + 1];
        assert(step(prog, s, s2));
        if step_perform(prog, s, s2) {
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
        }
    }
    assert forall|i: int, r: ResId| 0 <= i < tr.len() && final_state(tr[i]) && #[trigger] tr[i].res.contains_key(r) implies tr[i].res[r].st
        != RState::Live by {
        let s = tr[i];
        lemma_inv_trace(prog, tr, i);
        if s.res[r].st == RState::Live {
            assert(live(s, r));
            let p = choose|p: Pos| #[trigger] holds(s, p, r);
            match p {
                Pos::Knt(k, m) => {
                    lemma_no_fresh_at_final(prog, s, k);
                },
                _ => {},
            }
        }
    }
}

// ---------------------------------------------------------------------------
// E5. Multi-shot restriction
// ---------------------------------------------------------------------------

/// **E5. Multi-shot restriction.** (1) Every `multi` continuation holds only
/// clean frames: no linear value, and no fresh `once` continuation. So (2) a
/// resume of a `multi` continuation, however often it happens, pushes frames
/// that hold no resource and no fresh `once` continuation. (3) At every state,
/// no resource and no fresh `once` continuation has two owners (no duplicate).
pub proof fn e5_multi_shot_restriction(prog: Prog, tr: Seq<State>)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
    ensures
        forall|i: int, k: KId|
            0 <= i < tr.len() && #[trigger] tr[i].konts.contains_key(k) && tr[i].konts[k].multi ==> all_clean(
                prog,
                tr[i],
                tr[i].konts[k].frames,
            ),
        forall|i: int, m: int|
            0 <= i < tr.len() - 1 && step_resume(prog, tr[i], tr[i + 1]) && tr[i].konts[tf(tr[i]).k->0].multi && 0
                <= m < tr[i].konts[tf(tr[i]).k->0].frames.len() && #[trigger] tr[i].konts[tf(tr[i]).k->0].frames[m] is Code
                ==> {
                let g = tr[i].konts[tf(tr[i]).k->0].frames[m]->Code_0;
                !nonempty(g.slots) && !holds_fresh(tr[i], g)
            },
        forall|i: int| 0 <= i < tr.len() ==> #[trigger] b_unique_res(tr[i]) && b_unique_k(tr[i]),
{
    assert forall|i: int, k: KId|
        0 <= i < tr.len() && #[trigger] tr[i].konts.contains_key(k) && tr[i].konts[k].multi implies all_clean(
        prog,
        tr[i],
        tr[i].konts[k].frames,
    ) by {
        lemma_inv_trace(prog, tr, i);
    }
    assert forall|i: int, m: int|
        0 <= i < tr.len() - 1 && step_resume(prog, tr[i], tr[i + 1]) && tr[i].konts[tf(tr[i]).k->0].multi && 0 <= m
            < tr[i].konts[tf(tr[i]).k->0].frames.len() && #[trigger] tr[i].konts[tf(tr[i]).k->0].frames[m] is Code implies {
        let g = tr[i].konts[tf(tr[i]).k->0].frames[m]->Code_0;
        !nonempty(g.slots) && !holds_fresh(tr[i], g)
    } by {
        let s = tr[i];
        let kid = tf(s).k->0;
        lemma_inv_trace(prog, tr, i);
        assert(all_clean(prog, s, s.konts[kid].frames));
        let g = s.konts[kid].frames[m]->Code_0;
        assert(clean(prog, s, g));
        assert(kont_ok(prog, s, s.konts[kid]));
        assert(frame_ok(prog, s, s.konts[kid].frames[m]));
        if g.k is Some {
            assert(k_link(prog, s, g));
        }
    }
    assert forall|i: int| 0 <= i < tr.len() implies #[trigger] b_unique_res(tr[i]) && b_unique_k(tr[i]) by {
        lemma_inv_trace(prog, tr, i);
    }
}

} // verus!
