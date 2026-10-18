//! # Progress: the error predicates name every stuck state
//!
//! For any state (reachable or not), if it is not final and not an error,
//! the machine can step. With `soundness`, a checked program never gets stuck
//! before it ends.

use vstd::prelude::*;
use crate::model::*;
use crate::checker::*;
use crate::scope_steps::*;
use crate::safety::*;

verus! {

/// A map with an entry has a slot that holds its newest resource.
pub proof fn lemma_max_slot_exists(m: Map<Slot, ResId>) -> (sl: Slot)
    requires
        nonempty(m),
    ensures
        max_slot(m, sl),
    decreases m.dom().len(),
{
    let sl0 = choose|sl: Slot| m.contains_key(sl);
    let m2 = m.remove(sl0);
    vstd::map::lemma_map_remove_domain(m, sl0);
    vstd::set::lemma_set_remove_len(m.dom(), sl0);
    if nonempty(m2) {
        let sl1 = lemma_max_slot_exists(m2);
        assert(m2[sl1] == m[sl1]);
        if m[sl0] <= m[sl1] {
            assert forall|sl2: Slot| #[trigger] m.contains_key(sl2) implies m[sl2] <= m[sl1] by {
                if sl2 != sl0 {
                    assert(m2.contains_key(sl2));
                }
            }
            sl1
        } else {
            assert forall|sl2: Slot| #[trigger] m.contains_key(sl2) implies m[sl2] <= m[sl0] by {
                if sl2 != sl0 {
                    assert(m2.contains_key(sl2));
                }
            }
            sl0
        }
    } else {
        assert forall|sl2: Slot| #[trigger] m.contains_key(sl2) implies m[sl2] <= m[sl0] by {
            if sl2 != sl0 {
                assert(m2.contains_key(sl2));
            }
        }
        sl0
    }
}

/// **Progress.** A state that is not final and not an error has a next state.
pub proof fn progress(prog: Prog, s: State)
    requires
        !final_state(s),
        !error(prog, s),
    ensures
        exists|s2: State| step(prog, s, s2),
{
    if unwinding(s) {
        if s.pending.last() is Handler {
            let s2 = State { pending: s.pending.drop_last(), ..s };
            assert(step_unwind_pop(s, s2));
            assert(step(prog, s, s2));
        } else if holds_fresh(s, pf(s)) {
            assert(step_unwind_drop(s, do_drop(s)));
            assert(step(prog, s, do_drop(s)));
        } else if nonempty(pf(s).slots) {
            let sl = lemma_max_slot_exists(pf(s).slots);
            assert(slot_live(s, pf(s), sl));
            assert(s.res[pf(s).slots[sl]].on_abort);
            assert(step_unwind_abort(s, do_abort(s, sl)));
            assert(step(prog, s, do_abort(s, sl)));
        } else {
            let s2 = State { pending: s.pending.drop_last(), ..s };
            assert(step_unwind_pop(s, s2));
            assert(step(prog, s, s2));
        }
    } else if s.stack.last() is Handler {
        let s2 = State { stack: s.stack.drop_last(), ..s };
        assert(step_pop(s, s2));
        assert(step(prog, s, s2));
    } else {
        let f = tf(s);
        assert(code_ok(prog, f));
        match instr_at(prog, f) {
            Instr::Acquire { slot, on_abort } => {
                assert(step_acquire(prog, s, do_acquire(s, slot, on_abort)));
                assert(step(prog, s, do_acquire(s, slot, on_abort)));
            },
            Instr::Consume { slot } => {
                assert(step_consume(prog, s, do_consume(s, slot)));
                assert(step(prog, s, do_consume(s, slot)));
            },
            Instr::Call { block, caps } => {
                assert(step_call(prog, s, do_call(prog, s, block, caps)));
                assert(step(prog, s, do_call(prog, s, block, caps)));
            },
            Instr::Handle { eff, clauses, body } => {
                assert(step_handle(prog, s, do_handle(prog, s, eff, clauses, body)));
                assert(step(prog, s, do_handle(prog, s, eff, clauses, body)));
            },
            Instr::Perform { cap, op } => {
                let c = f.env[cap as int];
                assert(handled(prog, s, f, cap, op));
                let j = lemma_topmost_exists(s.stack, c);
                let i = instr_at(prog, f);
                assert(perform_ok_dyn(prog, s, i->Perform_cap, i->Perform_op, j));
                let s2 = do_perform(prog, s, f.env[i->Perform_cap as int], i->Perform_op, j);
                assert(exists|j2: int|
                    #[trigger] perform_ok_dyn(prog, s, i->Perform_cap, i->Perform_op, j2) && s2 == do_perform(
                        prog,
                        s,
                        tf(s).env[i->Perform_cap as int],
                        i->Perform_op,
                        j2,
                    ));
                assert(step_perform(prog, s, s2));
                assert(step(prog, s, s2));
            },
            Instr::Resume => {
                assert(step_resume(prog, s, do_resume(s)));
                assert(step(prog, s, do_resume(s)));
            },
            Instr::Return => {
                assert(step_return(prog, s, do_return(s)));
                assert(step(prog, s, do_return(s)));
            },
        }
    }
}

/// **No stuck state.** Each state of an execution of a checked program is
/// final, or it has a next state.
pub proof fn no_stuck(prog: Prog, tr: Seq<State>)
    requires
        check(prog),
        is_trace(prog, tr),
        tr[0] == init(prog),
    ensures
        forall|i: int|
            #![trigger tr[i]]
            0 <= i < tr.len() ==> final_state(tr[i]) || exists|s2: State| #[trigger] step(prog, tr[i], s2),
{
    soundness(prog, tr);
    assert forall|i: int| #![trigger tr[i]] 0 <= i < tr.len() implies final_state(tr[i]) || exists|s2: State| #[trigger] step(
        prog,
        tr[i],
        s2,
    ) by {
        assert(!error(prog, tr[i]));
        if !final_state(tr[i]) {
            progress(prog, tr[i]);
        }
    }
}

} // verus!
