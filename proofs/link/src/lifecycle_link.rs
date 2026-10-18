//! # L3. Lifecycle: the exec state machines and the effects model
//!
//! The interpreter keeps one exec record per continuation (`Continuation`)
//! and per linear value (`Linear`), from
//! `crates/weft-verified/src/lifecycle.rs`. The effects model
//! (`proofs/effects/src/model.rs`) keeps a `Kont` record per continuation
//! and a `Res` record per linear resource.
//!
//! `kont_rel` and `lin_rel` relate an exec record to a model record. Each
//! function below calls one exec operation and proves, from the
//! postcondition of that operation only:
//!
//! * the exec operation succeeds only where the model step is allowed, and
//!   the new exec record is related to the model record after that step;
//! * where the model step is an error, the exec operation fails and does
//!   not change the record.
//!
//! The steps are the model functions themselves: `do_perform`, `do_resume`,
//! `do_return`, `do_drop`, `do_acquire`, `do_consume` and `do_abort`.
//!
//! One difference is proved, not hidden: `drop_now` on a fresh `multi`
//! continuation reports an abort. The model does not unwind a `multi`
//! continuation (`holds_fresh` is false). E5 says that such a continuation
//! holds no linear value and no fresh `once` continuation, so the unwind has
//! nothing to finalize. This file does not prove that consequence.

use vstd::prelude::*;
use crate::lifecycle::{Continuation, ContState, ContError, Linear, LinState, LinError};
use crate::effects_model::{
    State, Kont, Prog, Res, RState, Mode, Instr, HId, Slot, at_instr, instr_at, tf, pf, op_mode,
    do_perform, resume_ok_dyn, do_resume, step_resume, err_resume_used, do_return, step_return,
    holds_fresh, nonempty, unwinding, do_drop, step_unwind_drop, do_acquire, step_acquire,
    do_consume, step_consume, slot_live, err_consumed_twice, do_abort, step_unwind_abort, max_slot,
    err_unwind_dead, err_no_on_abort,
};

verus! {

// ---------------------------------------------------------------------------
// Continuations
// ---------------------------------------------------------------------------

/// The model record `kt` is the record of the exec continuation `c`.
///
/// * `Fresh`: the same mode, not used.
/// * `Resumed`: the same mode. A `once` record is used. A `multi` record
///   stays usable (the model never marks it used).
/// * `Dropped`: the record cannot resume again in the model, or it is a
///   `multi` record that the model does not drop. The postcondition of
///   `drop_now` does not keep the mode after an abort, so this case does not
///   use `c.multi`.
pub open spec fn kont_rel(c: Continuation, kt: Kont) -> bool {
    match c.state {
        ContState::Fresh => kt.multi == c.multi && !kt.used,
        ContState::Resumed => kt.multi == c.multi && kt.used == !c.multi,
        ContState::Dropped => kt.multi || kt.used,
    }
}

/// A perform makes a continuation. The exec record of `Continuation::new`
/// is related to the record that `do_perform` adds.
pub fn perform_linked(
    multi: bool,
    Ghost(prog): Ghost<Prog>,
    Ghost(s): Ghost<State>,
    Ghost(c): Ghost<HId>,
    Ghost(op): Ghost<nat>,
    Ghost(j): Ghost<int>,
) -> (k: Continuation)
    requires
        multi == (op_mode(prog, s, c, op) == Mode::Multi),
    ensures
        k.state == ContState::Fresh,
        do_perform(prog, s, c, op, j).konts.contains_key(s.next_k),
        kont_rel(k, do_perform(prog, s, c, op, j).konts[s.next_k]),
{
    Continuation::new(multi)
}

/// **Resume.** A successful exec resume is the model step `step_resume`. A
/// resume that the model calls an error (`err_resume_used`) fails in exec.
pub fn resume_linked(k: &mut Continuation, Ghost(prog): Ghost<Prog>, Ghost(s): Ghost<State>) -> (r: Result<(), ContError>)
    requires
        at_instr(prog, s),
        instr_at(prog, tf(s)) is Resume,
        tf(s).k is Some,
        s.konts.contains_key(tf(s).k->0),
        kont_rel(*old(k), s.konts[tf(s).k->0]),
    ensures
        r is Ok ==> step_resume(prog, s, do_resume(s)) && do_resume(s).konts.contains_key(tf(s).k->0)
            && kont_rel(*final(k), do_resume(s).konts[tf(s).k->0]),
        r is Err ==> *final(k) == *old(k),
        err_resume_used(prog, s) ==> r is Err,
        old(k).state != ContState::Dropped ==> (r is Ok <==> resume_ok_dyn(s, tf(s))),
{
    k.resume()
}

/// **Return of a clause.** The exec drop is the drop in `do_return`. For a
/// `once` continuation, the exec reports an abort exactly when the model
/// sends the captured frames to the unwinder.
pub fn return_linked(k: &mut Continuation, Ghost(prog): Ghost<Prog>, Ghost(s): Ghost<State>) -> (aborts: bool)
    requires
        at_instr(prog, s),
        instr_at(prog, tf(s)) is Return,
        !nonempty(tf(s).slots),
        tf(s).k is Some,
        s.konts.contains_key(tf(s).k->0),
        kont_rel(*old(k), s.konts[tf(s).k->0]),
    ensures
        step_return(prog, s, do_return(s)),
        do_return(s).konts.contains_key(tf(s).k->0),
        kont_rel(*final(k), do_return(s).konts[tf(s).k->0]),
        holds_fresh(s, tf(s)) ==> aborts && do_return(s).pending == s.pending + s.konts[tf(s).k->0].frames,
        !old(k).multi ==> (aborts == holds_fresh(s, tf(s))),
        old(k).multi ==> !holds_fresh(s, tf(s)),
        old(k).multi && old(k).state == ContState::Fresh ==> aborts,
        aborts ==> final(k).state == ContState::Dropped,
        !aborts ==> *final(k) == *old(k),
{
    k.drop_now()
}

/// **Unwind of a clause frame.** The exec drop is the model step
/// `step_unwind_drop`. If the model does not drop, the model record stays
/// related.
pub fn unwind_drop_linked(k: &mut Continuation, Ghost(s): Ghost<State>) -> (aborts: bool)
    requires
        unwinding(s),
        s.pending.last() is Code,
        pf(s).k is Some,
        s.konts.contains_key(pf(s).k->0),
        kont_rel(*old(k), s.konts[pf(s).k->0]),
    ensures
        holds_fresh(s, pf(s)) ==> aborts && step_unwind_drop(s, do_drop(s)) && do_drop(s).konts.contains_key(
            pf(s).k->0,
        ) && kont_rel(*final(k), do_drop(s).konts[pf(s).k->0]),
        !holds_fresh(s, pf(s)) ==> kont_rel(*final(k), s.konts[pf(s).k->0]),
        !old(k).multi ==> (aborts == holds_fresh(s, pf(s))),
        old(k).multi ==> !holds_fresh(s, pf(s)),
        old(k).multi && old(k).state == ContState::Fresh ==> aborts,
        aborts ==> final(k).state == ContState::Dropped,
        !aborts ==> *final(k) == *old(k),
{
    k.drop_now()
}

// ---------------------------------------------------------------------------
// Linear values
// ---------------------------------------------------------------------------

/// The model resource `r` has the state of the exec record `l`.
pub open spec fn lin_rel(l: Linear, r: Res) -> bool {
    match l.state {
        LinState::Live => r.st == RState::Live,
        LinState::Consumed => r.st == RState::Consumed,
        LinState::Aborted => r.st == RState::Aborted,
    }
}

/// **Acquire.** The exec record of `Linear::new` is related to the resource
/// that `do_acquire` adds.
pub fn acquire_linked(Ghost(prog): Ghost<Prog>, Ghost(s): Ghost<State>, Ghost(slot): Ghost<Slot>, Ghost(on_abort): Ghost<bool>) -> (l: Linear)
    requires
        at_instr(prog, s),
        instr_at(prog, tf(s)) == (Instr::Acquire { slot, on_abort }),
        !tf(s).slots.contains_key(slot),
    ensures
        step_acquire(prog, s, do_acquire(s, slot, on_abort)),
        do_acquire(s, slot, on_abort).res.contains_key(s.next_res),
        lin_rel(l, do_acquire(s, slot, on_abort).res[s.next_res]),
{
    Linear::new()
}

/// **Consume.** A successful exec consume is the model step `step_consume`.
/// A consume that the model calls an error (`err_consumed_twice`) fails in
/// exec and does not change the record.
pub fn consume_linked(l: &mut Linear, Ghost(prog): Ghost<Prog>, Ghost(s): Ghost<State>, Ghost(slot): Ghost<Slot>) -> (r: Result<(), LinError>)
    requires
        at_instr(prog, s),
        instr_at(prog, tf(s)) == (Instr::Consume { slot }),
        tf(s).slots.contains_key(slot),
        s.res.contains_key(tf(s).slots[slot]),
        lin_rel(*old(l), s.res[tf(s).slots[slot]]),
    ensures
        r is Ok <==> slot_live(s, tf(s), slot),
        r is Ok ==> step_consume(prog, s, do_consume(s, slot)) && do_consume(s, slot).res.contains_key(
            tf(s).slots[slot],
        ) && lin_rel(*final(l), do_consume(s, slot).res[tf(s).slots[slot]]),
        r is Err ==> err_consumed_twice(prog, s) && *final(l) == *old(l),
{
    l.consume()
}

/// **Unwind of a linear value.** The unwinder takes the newest value `sl`
/// of the top pending frame. The exec record runs `on abort` exactly when
/// the model resource is live. Then the exec step is the model step
/// `step_unwind_abort` if the type has `on abort`. Else the model state is
/// the error `err_no_on_abort`: the exec record has no `on abort` flag, and
/// the checker rule (E3) must exclude this case. If the exec does not run
/// `on abort`, the model state is the error `err_unwind_dead`, and the exec
/// record does not change.
pub fn unwind_linked(l: &mut Linear, Ghost(s): Ghost<State>, Ghost(sl): Ghost<Slot>) -> (run: bool)
    requires
        unwinding(s),
        s.pending.last() is Code,
        !holds_fresh(s, pf(s)),
        max_slot(pf(s).slots, sl),
        s.res.contains_key(pf(s).slots[sl]),
        lin_rel(*old(l), s.res[pf(s).slots[sl]]),
    ensures
        run == slot_live(s, pf(s), sl),
        run && s.res[pf(s).slots[sl]].on_abort ==> step_unwind_abort(s, do_abort(s, sl))
            && do_abort(s, sl).res.contains_key(pf(s).slots[sl]) && lin_rel(
            *final(l),
            do_abort(s, sl).res[pf(s).slots[sl]],
        ),
        run && !s.res[pf(s).slots[sl]].on_abort ==> err_no_on_abort(s),
        !run ==> err_unwind_dead(s) && *final(l) == *old(l),
{
    l.unwind()
}

} // verus!
