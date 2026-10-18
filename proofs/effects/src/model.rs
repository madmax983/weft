//! # Weft algebraic effects: the abstract machine
//!
//! This file defines the dynamic semantics. `checker.rs` defines the static rules.
//!
//! * A program is a map from block ids to blocks. A block has a signature and
//!   a straight-line instruction sequence.
//! * The state has a stack of frames. A frame is a code frame or a handler frame.
//! * `Handle` mints a fresh handler id `c`. The id is the capability. The body
//!   receives `c` in its capability environment `env`. A call passes
//!   capabilities explicitly (capability passing). A perform names a capability
//!   by index into `env`, so it reaches the handler that minted it (lexical).
//! * `Perform` captures the frames from the handler frame up to the top as a
//!   continuation. The clause runs in place of the handler frame.
//! * `Resume` puts the captured frames back. A `once` continuation becomes
//!   used. A `multi` continuation stays usable: each resume copies its frames.
//! * A clause that returns without resuming a `once` continuation aborts it.
//!   The captured frames go to the unwinder (`pending`). The unwinder runs
//!   `on abort` for each live linear value, top frame first, newest value first.
//! * `Cancel` models task cancellation at a suspension point: the perform
//!   aborts at once, with the same unwinding.
//!
//! Every stuck state that is an error has a named error predicate (`error`).

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

pub type EffId = nat;

pub type BlockId = nat;

/// A local variable that holds a linear value.
pub type Slot = nat;

pub type ResId = nat;

/// A continuation id.
pub type KId = nat;

/// A handler instance id. It is also the capability for that instance.
pub type HId = nat;

// ---------------------------------------------------------------------------
// Programs
// ---------------------------------------------------------------------------

/// How often a continuation of an operation can resume.
pub enum Mode {
    Once,
    Multi,
}

/// A block signature.
/// * `caps`: the effect of each capability parameter (the effect row).
/// * `rets`: the parameters that the block returns, as closures that capture
///   them. Each entry is an index into `caps`.
/// * `kmode`: `Some(m)` for a clause block. It receives a continuation of mode `m`.
pub struct Sig {
    pub caps: Seq<EffId>,
    pub rets: Seq<nat>,
    pub kmode: Option<Mode>,
}

pub enum Instr {
    /// Create a linear value in `slot`. `on_abort` tells if its type declares `on abort`.
    Acquire { slot: Slot, on_abort: bool },
    /// Consume the linear value in `slot`.
    Consume { slot: Slot },
    /// Call `block`. Capability parameter `j` of the callee is `env[caps[j]]`.
    Call { block: BlockId, caps: Seq<nat> },
    /// `handle eff { clauses } in body`. Clause `o` handles operation `o`.
    Handle { eff: EffId, clauses: Seq<BlockId>, body: BlockId },
    /// Perform operation `op` through capability `env[cap]`.
    Perform { cap: nat, op: nat },
    /// Resume the continuation of this clause frame.
    Resume,
    /// Return. A clause that returns before it resumes drops its continuation.
    Return,
}

pub struct Block {
    pub sig: Sig,
    pub code: Seq<Instr>,
}

pub struct Prog {
    /// Each effect is a sequence of operations, each `once` or `multi`.
    pub effs: Map<EffId, Seq<Mode>>,
    pub blocks: Map<BlockId, Block>,
    pub main: BlockId,
}

// ---------------------------------------------------------------------------
// States
// ---------------------------------------------------------------------------

pub enum RState {
    Live,
    Consumed,
    Aborted,
}

/// A linear resource.
pub struct Res {
    pub st: RState,
    pub on_abort: bool,
}

/// A code frame.
/// * `env`: the capability environment (handler ids).
/// * `slots`: the linear values that this frame owns.
/// * `k`: the continuation of a clause frame.
pub struct CFrame {
    pub block: BlockId,
    pub pc: nat,
    pub env: Seq<HId>,
    pub slots: Map<Slot, ResId>,
    pub k: Option<KId>,
}

pub enum Frame {
    Code(CFrame),
    /// A handler frame. It delimits the continuations of its handler instance.
    Handler(HId),
}

/// What a `Handle` step records for a handler instance. It never changes.
/// `env` is the capability environment at the handle site. The clauses run in it.
pub struct HInfo {
    pub eff: EffId,
    pub clauses: Seq<BlockId>,
    pub env: Seq<HId>,
}

/// A captured continuation. Frame 0 is the handler frame. The last frame performed.
pub struct Kont {
    pub frames: Seq<Frame>,
    pub multi: bool,
    pub used: bool,
}

pub struct State {
    pub stack: Seq<Frame>,
    /// Frames that the unwinder must still finalize. Top is last.
    pub pending: Seq<Frame>,
    pub res: Map<ResId, Res>,
    pub konts: Map<KId, Kont>,
    pub hinfo: Map<HId, HInfo>,
    pub next_res: nat,
    pub next_k: nat,
    pub next_h: nat,
}

/// The initial state: one frame for `main`, no capabilities.
pub open spec fn init(prog: Prog) -> State {
    State {
        stack: seq![
            Frame::Code(
                CFrame {
                    block: prog.main,
                    pc: 0,
                    env: Seq::empty(),
                    slots: Map::empty(),
                    k: None,
                },
            ),
        ],
        pending: Seq::empty(),
        res: Map::empty(),
        konts: Map::empty(),
        hinfo: Map::empty(),
        next_res: 0,
        next_k: 0,
        next_h: 0,
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// The machine runs code: nothing waits for the unwinder.
pub open spec fn running(s: State) -> bool {
    s.pending.len() == 0 && s.stack.len() > 0
}

/// The unwinder has work.
pub open spec fn unwinding(s: State) -> bool {
    s.pending.len() > 0
}

/// The program completed (normally or after aborts).
pub open spec fn final_state(s: State) -> bool {
    s.stack.len() == 0 && s.pending.len() == 0
}

/// The machine runs and the top frame is a code frame.
pub open spec fn top_code(s: State) -> bool {
    running(s) && s.stack.last() is Code
}

/// The top code frame.
pub open spec fn tf(s: State) -> CFrame {
    s.stack.last()->Code_0
}

/// The block and pc of `f` exist.
pub open spec fn code_ok(prog: Prog, f: CFrame) -> bool {
    prog.blocks.contains_key(f.block) && f.pc < prog.blocks[f.block].code.len()
}

/// The instruction at the pc of `f`.
pub open spec fn instr_at(prog: Prog, f: CFrame) -> Instr {
    prog.blocks[f.block].code[f.pc as int]
}

/// The machine runs, and the top code frame is at a valid instruction.
pub open spec fn at_instr(prog: Prog, s: State) -> bool {
    top_code(s) && code_ok(prog, tf(s))
}

/// `f` with its pc moved to the next instruction.
pub open spec fn adv(f: CFrame) -> CFrame {
    CFrame { pc: f.pc + 1, ..f }
}

/// The stack with its top frame replaced by `f`.
pub open spec fn upd_top(s: State, f: CFrame) -> Seq<Frame> {
    s.stack.update(s.stack.len() - 1, Frame::Code(f))
}

/// The map holds at least one entry.
pub open spec fn nonempty(m: Map<Slot, ResId>) -> bool {
    exists|sl: Slot| m.contains_key(sl)
}

/// `fr` is the handler frame of instance `h`.
pub open spec fn is_handler(fr: Frame, h: HId) -> bool {
    fr is Handler && fr->Handler_0 == h
}

/// A handler frame of `h` is on `st`.
pub open spec fn on_stack(st: Seq<Frame>, h: HId) -> bool {
    exists|j: int| 0 <= j < st.len() && #[trigger] is_handler(st[j], h)
}

/// `j` is the topmost handler frame of `h` on `st`.
pub open spec fn topmost(st: Seq<Frame>, h: HId, j: int) -> bool {
    &&& 0 <= j < st.len()
    &&& is_handler(st[j], h)
    &&& forall|j2: int| j < j2 < st.len() ==> !#[trigger] is_handler(st[j2], h)
}

/// `kid` is a `once` continuation that nobody resumed or dropped yet.
pub open spec fn fresh_once(s: State, kid: KId) -> bool {
    s.konts.contains_key(kid) && !s.konts[kid].multi && !s.konts[kid].used
}

/// Frame `f` holds a fresh `once` continuation.
pub open spec fn holds_fresh(s: State, f: CFrame) -> bool {
    f.k is Some && fresh_once(s, f.k->0)
}

/// `sl` holds the newest resource of `m` (the unwinder takes it first).
pub open spec fn max_slot(m: Map<Slot, ResId>, sl: Slot) -> bool {
    m.contains_key(sl) && forall|sl2: Slot| #[trigger] m.contains_key(sl2) ==> m[sl2] <= m[sl]
}

/// The top pending frame, when it is a code frame.
pub open spec fn pf(s: State) -> CFrame {
    s.pending.last()->Code_0
}

// ---------------------------------------------------------------------------
// Steps
// ---------------------------------------------------------------------------

/// The body returned: remove its handler frame.
pub open spec fn step_pop(s: State, s2: State) -> bool {
    running(s) && s.stack.last() is Handler && s2 == State { stack: s.stack.drop_last(), ..s }
}

/// The state after `acquire`: a fresh live resource in the slot.
pub open spec fn do_acquire(s: State, slot: Slot, on_abort: bool) -> State {
    let f = tf(s);
    State {
        stack: upd_top(s, CFrame { slots: f.slots.insert(slot, s.next_res), ..adv(f) }),
        res: s.res.insert(s.next_res, Res { st: RState::Live, on_abort }),
        next_res: s.next_res + 1,
        ..s
    }
}

/// Step: `acquire` into an empty slot.
pub open spec fn step_acquire(prog: Prog, s: State, s2: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Acquire { slot, on_abort } => !tf(s).slots.contains_key(slot) && s2 == do_acquire(
            s,
            slot,
            on_abort,
        ),
        _ => false,
    }
}

/// The state after `consume`: the resource is consumed and the slot is empty.
pub open spec fn do_consume(s: State, slot: Slot) -> State {
    let f = tf(s);
    let r = f.slots[slot];
    State {
        stack: upd_top(s, CFrame { slots: f.slots.remove(slot), ..adv(f) }),
        res: s.res.insert(r, Res { st: RState::Consumed, ..s.res[r] }),
        ..s
    }
}

/// The resource in `slot` of `f` is live.
pub open spec fn slot_live(s: State, f: CFrame, slot: Slot) -> bool {
    f.slots.contains_key(slot) && s.res.contains_key(f.slots[slot]) && s.res[f.slots[slot]].st
        == RState::Live
}

/// Step: `consume` a live resource.
pub open spec fn step_consume(prog: Prog, s: State, s2: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Consume { slot } => slot_live(s, tf(s), slot) && s2 == do_consume(s, slot),
        _ => false,
    }
}

/// The call names an existing block and existing capabilities.
pub open spec fn call_ok_dyn(prog: Prog, f: CFrame, block: BlockId, caps: Seq<nat>) -> bool {
    &&& prog.blocks.contains_key(block)
    &&& forall|j: int| 0 <= j < caps.len() ==> #[trigger] caps[j] < f.env.len()
    &&& forall|j: int|
        0 <= j < prog.blocks[block].sig.rets.len() ==> #[trigger] prog.blocks[block].sig.rets[j]
            < caps.len()
}

/// The capabilities that a callee returns (as closures) to its caller.
pub open spec fn call_rets(prog: Prog, env: Seq<HId>, block: BlockId, caps: Seq<nat>) -> Seq<HId> {
    let rets = prog.blocks[block].sig.rets;
    Seq::new(rets.len(), |j: int| env[caps[rets[j] as int] as int])
}

/// The environment of a callee.
pub open spec fn call_env(env: Seq<HId>, caps: Seq<nat>) -> Seq<HId> {
    Seq::new(caps.len(), |j: int| env[caps[j] as int])
}

/// A call. The model adds the returned capabilities to the caller at once.
/// The caller is suspended until the callee returns, so this is the same as
/// adding them at the return.
pub open spec fn do_call(prog: Prog, s: State, block: BlockId, caps: Seq<nat>) -> State {
    let f = tf(s);
    let callee = CFrame {
        block,
        pc: 0,
        env: call_env(f.env, caps),
        slots: Map::empty(),
        k: None,
    };
    let f2 = CFrame { env: f.env + call_rets(prog, f.env, block, caps), ..adv(f) };
    State { stack: upd_top(s, f2).push(Frame::Code(callee)), ..s }
}

/// Step: a call with existing capabilities.
pub open spec fn step_call(prog: Prog, s: State, s2: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Call { block, caps } => call_ok_dyn(prog, tf(s), block, caps) && s2 == do_call(
            prog,
            s,
            block,
            caps,
        ),
        _ => false,
    }
}

/// The body exists and its returned capabilities exist.
pub open spec fn handle_ok_dyn(prog: Prog, f: CFrame, body: BlockId) -> bool {
    &&& prog.blocks.contains_key(body)
    &&& forall|j: int|
        0 <= j < prog.blocks[body].sig.rets.len() ==> #[trigger] prog.blocks[body].sig.rets[j]
            <= f.env.len()
}

/// The capabilities that a handle body returns (as closures) to the handle site.
pub open spec fn handle_rets(prog: Prog, benv: Seq<HId>, body: BlockId) -> Seq<HId> {
    let rets = prog.blocks[body].sig.rets;
    Seq::new(rets.len(), |j: int| benv[rets[j] as int])
}

/// `handle`: mint the fresh capability `c`, push the handler frame and the body.
pub open spec fn do_handle(
    prog: Prog,
    s: State,
    eff: EffId,
    clauses: Seq<BlockId>,
    body: BlockId,
) -> State {
    let f = tf(s);
    let c = s.next_h;
    let benv = f.env.push(c);
    let f2 = CFrame { env: f.env + handle_rets(prog, benv, body), ..adv(f) };
    let b = CFrame { block: body, pc: 0, env: benv, slots: Map::empty(), k: None };
    State {
        stack: upd_top(s, f2).push(Frame::Handler(c)).push(Frame::Code(b)),
        hinfo: s.hinfo.insert(c, HInfo { eff, clauses, env: f.env }),
        next_h: c + 1,
        ..s
    }
}

/// Step: `handle`.
pub open spec fn step_handle(prog: Prog, s: State, s2: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Handle { eff, clauses, body } => handle_ok_dyn(prog, tf(s), body) && s2 == do_handle(
            prog,
            s,
            eff,
            clauses,
            body,
        ),
        _ => false,
    }
}

/// The capability exists, its handler frame is on the stack, and the effect
/// of the handler declares the operation.
pub open spec fn handled(prog: Prog, s: State, f: CFrame, cap: nat, op: nat) -> bool {
    let c = f.env[cap as int];
    &&& cap < f.env.len()
    &&& on_stack(s.stack, c)
    &&& s.hinfo.contains_key(c)
    &&& prog.effs.contains_key(s.hinfo[c].eff)
    &&& op < prog.effs[s.hinfo[c].eff].len()
    &&& op < s.hinfo[c].clauses.len()
}

/// The perform can start: it is handled, `j` is the topmost handler frame of
/// the capability, and the clause block exists.
pub open spec fn perform_ok_dyn(prog: Prog, s: State, cap: nat, op: nat, j: int) -> bool {
    let f = tf(s);
    let c = f.env[cap as int];
    &&& handled(prog, s, f, cap, op)
    &&& topmost(s.stack, c, j)
    &&& prog.blocks.contains_key(s.hinfo[c].clauses[op as int])
}

/// The continuation that a perform captures: the frames from the handler
/// frame `j` up to the top. The top frame continues after the perform.
pub open spec fn captured(s: State, j: int) -> Seq<Frame> {
    s.stack.subrange(j, s.stack.len() - 1).push(Frame::Code(adv(tf(s))))
}

/// The clause frame for operation `op` of handler instance `c`. It runs the
/// clause that `c`'s handle site bound, in the environment of that site.
pub open spec fn clause_frame(s: State, c: HId, op: nat, kid: KId) -> CFrame {
    CFrame {
        block: s.hinfo[c].clauses[op as int],
        pc: 0,
        env: s.hinfo[c].env,
        slots: Map::empty(),
        k: Some(kid),
    }
}

/// The mode of operation `op` of handler instance `c`.
pub open spec fn op_mode(prog: Prog, s: State, c: HId, op: nat) -> Mode {
    prog.effs[s.hinfo[c].eff][op as int]
}

/// `perform`: capture the continuation and run the clause in place of the handler frame.
pub open spec fn do_perform(prog: Prog, s: State, c: HId, op: nat, j: int) -> State {
    State {
        stack: s.stack.subrange(0, j).push(Frame::Code(clause_frame(s, c, op, s.next_k))),
        konts: s.konts.insert(
            s.next_k,
            Kont { frames: captured(s, j), multi: op_mode(prog, s, c, op) == Mode::Multi, used: false },
        ),
        next_k: s.next_k + 1,
        ..s
    }
}

/// Step: `perform` through a live handler.
pub open spec fn step_perform(prog: Prog, s: State, s2: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Perform { cap, op } => exists|j: int|
            #[trigger] perform_ok_dyn(prog, s, cap, op, j) && s2 == do_perform(
                prog,
                s,
                tf(s).env[cap as int],
                op,
                j,
            ),
        _ => false,
    }
}

/// Cancellation at a suspension point: abort the continuation of the perform
/// at once. Its frames go to the unwinder. The handle site continues.
pub open spec fn do_cancel(s: State, j: int) -> State {
    State { stack: s.stack.subrange(0, j), pending: s.pending + captured(s, j), ..s }
}

/// Step: cancellation at a perform.
pub open spec fn step_cancel(prog: Prog, s: State, s2: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Perform { cap, op } => exists|j: int|
            #[trigger] perform_ok_dyn(prog, s, cap, op, j) && s2 == do_cancel(s, j),
        _ => false,
    }
}

/// The clause frame has a continuation that it can resume.
pub open spec fn resume_ok_dyn(s: State, f: CFrame) -> bool {
    f.k is Some && s.konts.contains_key(f.k->0) && (s.konts[f.k->0].multi || !s.konts[f.k->0].used)
}

/// `resume`: push the captured frames. A `multi` continuation pushes a copy.
pub open spec fn do_resume(s: State) -> State {
    let f = tf(s);
    let kid = f.k->0;
    let kt = s.konts[kid];
    State {
        stack: upd_top(s, adv(f)) + kt.frames,
        konts: if kt.multi {
            s.konts
        } else {
            s.konts.insert(kid, Kont { used: true, ..kt })
        },
        ..s
    }
}

/// Step: `resume` a usable continuation.
pub open spec fn step_resume(prog: Prog, s: State, s2: State) -> bool {
    at_instr(prog, s) && instr_at(prog, tf(s)) is Resume && resume_ok_dyn(s, tf(s)) && s2
        == do_resume(s)
}

/// `return`. A clause frame with a fresh `once` continuation drops it: the
/// captured frames go to the unwinder (abort).
pub open spec fn do_return(s: State) -> State {
    let f = tf(s);
    if holds_fresh(s, f) {
        let kid = f.k->0;
        State {
            stack: s.stack.drop_last(),
            pending: s.pending + s.konts[kid].frames,
            konts: s.konts.insert(kid, Kont { used: true, ..s.konts[kid] }),
            ..s
        }
    } else {
        State { stack: s.stack.drop_last(), ..s }
    }
}

/// Step: `return` with no live linear value.
pub open spec fn step_return(prog: Prog, s: State, s2: State) -> bool {
    at_instr(prog, s) && instr_at(prog, tf(s)) is Return && !nonempty(tf(s).slots) && s2
        == do_return(s)
}

/// Unwinder: remove a handler frame, or a code frame with nothing left to finalize.
pub open spec fn step_unwind_pop(s: State, s2: State) -> bool {
    &&& unwinding(s)
    &&& (s.pending.last() is Handler || (!holds_fresh(s, pf(s)) && !nonempty(pf(s).slots)))
    &&& s2 == State { pending: s.pending.drop_last(), ..s }
}

/// The state after the unwinder drops the continuation of the top pending frame.
pub open spec fn do_drop(s: State) -> State {
    let f = pf(s);
    let kid = f.k->0;
    State {
        pending: s.pending.update(s.pending.len() - 1, Frame::Code(CFrame { k: None, ..f }))
            + s.konts[kid].frames,
        konts: s.konts.insert(kid, Kont { used: true, ..s.konts[kid] }),
        ..s
    }
}

/// Unwinder: a frame holds a fresh `once` continuation. Drop it: its frames
/// go on top of the pending frames, so the unwinder finalizes them first.
pub open spec fn step_unwind_drop(s: State, s2: State) -> bool {
    unwinding(s) && s.pending.last() is Code && holds_fresh(s, pf(s)) && s2 == do_drop(s)
}

/// The state after the unwinder runs `on abort` for the value in slot `sl`.
pub open spec fn do_abort(s: State, sl: Slot) -> State {
    let f = pf(s);
    let r = f.slots[sl];
    State {
        pending: s.pending.update(
            s.pending.len() - 1,
            Frame::Code(CFrame { slots: f.slots.remove(sl), ..f }),
        ),
        res: s.res.insert(r, Res { st: RState::Aborted, ..s.res[r] }),
        ..s
    }
}

/// Unwinder: run `on abort` for the newest live linear value of the top pending frame.
pub open spec fn step_unwind_abort(s: State, s2: State) -> bool {
    &&& unwinding(s)
    &&& s.pending.last() is Code
    &&& !holds_fresh(s, pf(s))
    &&& exists|sl: Slot|
        #[trigger] max_slot(pf(s).slots, sl) && slot_live(s, pf(s), sl)
            && s.res[pf(s).slots[sl]].on_abort && s2 == do_abort(s, sl)
}

/// One machine step.
pub open spec fn step(prog: Prog, s: State, s2: State) -> bool {
    ||| step_pop(s, s2)
    ||| step_acquire(prog, s, s2)
    ||| step_consume(prog, s, s2)
    ||| step_call(prog, s, s2)
    ||| step_handle(prog, s, s2)
    ||| step_perform(prog, s, s2)
    ||| step_cancel(prog, s, s2)
    ||| step_resume(prog, s, s2)
    ||| step_return(prog, s, s2)
    ||| step_unwind_pop(s, s2)
    ||| step_unwind_drop(s, s2)
    ||| step_unwind_abort(s, s2)
}

/// An execution: each state steps to the next.
pub open spec fn is_trace(prog: Prog, tr: Seq<State>) -> bool {
    &&& tr.len() >= 1
    &&& forall|i: int| 0 <= i < tr.len() - 1 ==> step(prog, #[trigger] tr[i], tr[i + 1])
}

// ---------------------------------------------------------------------------
// Errors (stuck states that are bugs)
// ---------------------------------------------------------------------------

/// The code is malformed: no block, no instruction, an unknown callee, body
/// or clause, or an index past the end of a capability list.
pub open spec fn err_malformed(prog: Prog, s: State) -> bool {
    top_code(s) && (!code_ok(prog, tf(s)) || match instr_at(prog, tf(s)) {
        Instr::Call { block, caps } => !call_ok_dyn(prog, tf(s), block, caps),
        Instr::Handle { body, .. } => !handle_ok_dyn(prog, tf(s), body),
        Instr::Perform { cap, op } => handled(prog, s, tf(s), cap, op) && !prog.blocks.contains_key(
            s.hinfo[tf(s).env[cap as int]].clauses[op as int],
        ),
        _ => false,
    })
}

/// E1. A perform with no matching live handler: no such capability, its
/// handler frame is not on the stack, or the effect does not declare the operation.
pub open spec fn err_unhandled(prog: Prog, s: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Perform { cap, op } => !handled(prog, s, tf(s), cap, op),
        _ => false,
    }
}

/// E4. A perform through a capability whose handler is gone.
pub open spec fn err_dead_cap(prog: Prog, s: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Perform { cap, .. } => cap < tf(s).env.len() && !on_stack(
            s.stack,
            tf(s).env[cap as int],
        ),
        _ => false,
    }
}

/// E2. A resume of a `once` continuation that already resumed or was dropped.
pub open spec fn err_resume_used(prog: Prog, s: State) -> bool {
    let f = tf(s);
    at_instr(prog, s) && instr_at(prog, f) is Resume && f.k is Some && s.konts.contains_key(f.k->0)
        && !s.konts[f.k->0].multi && s.konts[f.k->0].used
}

/// A resume in a frame that has no continuation.
pub open spec fn err_no_k(prog: Prog, s: State) -> bool {
    let f = tf(s);
    at_instr(prog, s) && instr_at(prog, f) is Resume && (f.k is None || !s.konts.contains_key(
        f.k->0,
    ))
}

/// An acquire into a slot that holds a linear value (the old value leaks).
pub open spec fn err_overwrite(prog: Prog, s: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Acquire { slot, .. } => tf(s).slots.contains_key(slot),
        _ => false,
    }
}

/// A consume of an empty slot (use after move).
pub open spec fn err_use_moved(prog: Prog, s: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Consume { slot } => !tf(s).slots.contains_key(slot),
        _ => false,
    }
}

/// E3/E5. A consume of a resource that is not live: it was consumed or
/// aborted before (for example, through a duplicated frame).
pub open spec fn err_consumed_twice(prog: Prog, s: State) -> bool {
    at_instr(prog, s) && match instr_at(prog, tf(s)) {
        Instr::Consume { slot } => tf(s).slots.contains_key(slot) && !slot_live(s, tf(s), slot),
        _ => false,
    }
}

/// E3. A normal return with a live linear value (a leak).
pub open spec fn err_leak(prog: Prog, s: State) -> bool {
    at_instr(prog, s) && instr_at(prog, tf(s)) is Return && nonempty(tf(s).slots)
}

/// E3/E5. The unwinder finds a resource that is not live (finalized twice).
pub open spec fn err_unwind_dead(s: State) -> bool {
    &&& unwinding(s)
    &&& s.pending.last() is Code
    &&& !holds_fresh(s, pf(s))
    &&& exists|sl: Slot| #[trigger] max_slot(pf(s).slots, sl) && !slot_live(s, pf(s), sl)
}

/// E3. The unwinder must abort a live linear value whose type has no `on abort`.
pub open spec fn err_no_on_abort(s: State) -> bool {
    &&& unwinding(s)
    &&& s.pending.last() is Code
    &&& !holds_fresh(s, pf(s))
    &&& exists|sl: Slot|
        #[trigger] max_slot(pf(s).slots, sl) && slot_live(s, pf(s), sl)
            && !s.res[pf(s).slots[sl]].on_abort
}

/// The state is an error.
pub open spec fn error(prog: Prog, s: State) -> bool {
    ||| err_malformed(prog, s)
    ||| err_unhandled(prog, s)
    ||| err_dead_cap(prog, s)
    ||| err_resume_used(prog, s)
    ||| err_no_k(prog, s)
    ||| err_overwrite(prog, s)
    ||| err_use_moved(prog, s)
    ||| err_consumed_twice(prog, s)
    ||| err_leak(prog, s)
    ||| err_unwind_dead(s)
    ||| err_no_on_abort(s)
}

} // verus!
