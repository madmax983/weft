//! # The static checker
//!
//! The checker walks each block once. Its state (`SS`) at each pc holds
//! * `env`: the effect of each capability in scope (rule a),
//! * `lin`: the live linear slots, each with its `on abort` flag (rule c),
//! * `k`: the continuation is still usable (rule b: `resume` consumes a `once` `k`).
//!
//! Rules at suspension points (a call, a handle, a resume, a perform). A
//! suspension point "passes up" some capabilities: the frames above can
//! perform through them, and such a perform captures this frame.
//! * Abort rule: if a passed-up capability has a `once` operation, the
//!   continuation can abort, so each live linear value must declare `on abort`.
//! * Multi rule: if a passed-up capability has a `multi` operation, the frame
//!   can be copied, so it must hold no linear value and no usable `once` continuation.
//! * Escape rule (d): a handle body cannot return its own capability.

use vstd::prelude::*;
use crate::model::*;

verus! {

/// The checker state at one program point.
pub struct SS {
    pub env: Seq<EffId>,
    pub lin: Map<Slot, bool>,
    pub k: bool,
}

/// The checker state at the start of a block.
pub open spec fn entry(sig: Sig) -> SS {
    SS { env: sig.caps, lin: Map::empty(), k: sig.kmode is Some }
}

/// Effect `e` is declared and has an operation of mode `m`.
pub open spec fn has_mode(prog: Prog, e: EffId, m: Mode) -> bool {
    prog.effs.contains_key(e) && exists|o: int|
        0 <= o < prog.effs[e].len() && #[trigger] prog.effs[e][o] == m
}

/// One of the effects `es` has an operation of mode `m`.
pub open spec fn any_mode(prog: Prog, es: Seq<EffId>, m: Mode) -> bool {
    exists|j: int| 0 <= j < es.len() && #[trigger] has_mode(prog, es[j], m)
}

/// Abort rule: each live linear value declares `on abort`.
pub open spec fn all_abortable(ss: SS) -> bool {
    forall|sl: Slot| #[trigger] ss.lin.contains_key(sl) ==> ss.lin[sl]
}

/// Multi rule: no live linear value, and no usable `once` continuation.
pub open spec fn all_many(sig: Sig, ss: SS) -> bool {
    &&& forall|sl: Slot| !#[trigger] ss.lin.contains_key(sl)
    &&& !(ss.k && sig.kmode == Some(Mode::Once))
}

/// The rules for a suspension point that passes up capabilities of effects
/// `ups`. `after` is the checker state while the frame is suspended.
pub open spec fn susp_ok(prog: Prog, sig: Sig, after: SS, ups: Seq<EffId>) -> bool {
    &&& any_mode(prog, ups, Mode::Once) ==> all_abortable(after)
    &&& any_mode(prog, ups, Mode::Multi) ==> all_many(sig, after)
}

/// The effects of the capabilities that a callee returns.
pub open spec fn call_ret_effs(prog: Prog, env: Seq<EffId>, block: BlockId, caps: Seq<nat>) -> Seq<EffId> {
    let rets = prog.blocks[block].sig.rets;
    Seq::new(rets.len(), |j: int| env[caps[rets[j] as int] as int])
}

/// The effects of the capabilities that a handle body returns.
pub open spec fn handle_ret_effs(prog: Prog, env: Seq<EffId>, eff: EffId, body: BlockId) -> Seq<EffId> {
    let rets = prog.blocks[body].sig.rets;
    Seq::new(rets.len(), |j: int| env.push(eff)[rets[j] as int])
}

/// The checker state after instruction `i`.
pub open spec fn post(prog: Prog, sig: Sig, ss: SS, i: Instr) -> SS {
    match i {
        Instr::Acquire { slot, on_abort } => SS { lin: ss.lin.insert(slot, on_abort), ..ss },
        Instr::Consume { slot } => SS { lin: ss.lin.remove(slot), ..ss },
        Instr::Call { block, caps } => SS { env: ss.env + call_ret_effs(prog, ss.env, block, caps), ..ss },
        Instr::Handle { eff, body, .. } => SS {
            env: ss.env + handle_ret_effs(prog, ss.env, eff, body),
            ..ss
        },
        Instr::Perform { .. } => ss,
        Instr::Resume => SS {
            k: if sig.kmode == Some(Mode::Once) {
                false
            } else {
                ss.k
            },
            ..ss
        },
        Instr::Return => ss,
    }
}

/// The checker state before instruction `pc` of block `b`.
pub open spec fn ss_at(prog: Prog, b: BlockId, pc: nat) -> SS
    decreases pc,
{
    if pc == 0 {
        entry(prog.blocks[b].sig)
    } else {
        post(
            prog,
            prog.blocks[b].sig,
            ss_at(prog, b, (pc - 1) as nat),
            prog.blocks[b].code[pc - 1],
        )
    }
}

/// The signature of each clause of `handle eff { clauses }` at a site with
/// capability effects `env`.
pub open spec fn clause_sig_ok(prog: Prog, env: Seq<EffId>, eff: EffId, clauses: Seq<BlockId>) -> bool {
    forall|o: int|
        0 <= o < clauses.len() ==> prog.blocks.contains_key(#[trigger] clauses[o])
            && prog.blocks[clauses[o]].sig == (Sig {
            caps: env,
            rets: Seq::empty(),
            kmode: Some(prog.effs[eff][o]),
        })
}

/// The rules for one instruction in a block with signature `sig`.
pub open spec fn instr_ok(prog: Prog, sig: Sig, ss: SS, i: Instr) -> bool {
    match i {
        // (c) no overwrite of a live linear value
        Instr::Acquire { slot, .. } => !ss.lin.contains_key(slot),
        // (c) consume only a live linear value
        Instr::Consume { slot } => ss.lin.contains_key(slot),
        // (a) the callee's row is in scope; (c) and multi rule at the call
        Instr::Call { block, caps } => {
            &&& prog.blocks.contains_key(block)
            &&& prog.blocks[block].sig.kmode is None
            &&& caps.len() == prog.blocks[block].sig.caps.len()
            &&& forall|j: int|
                0 <= j < caps.len() ==> #[trigger] caps[j] < ss.env.len() && ss.env[caps[j] as int]
                    == prog.blocks[block].sig.caps[j]
            &&& susp_ok(prog, sig, post(prog, sig, ss, i), prog.blocks[block].sig.caps)
        },
        // (a) the handle adds a capability for `eff`; (d) the body cannot return it
        Instr::Handle { eff, clauses, body } => {
            &&& prog.effs.contains_key(eff)
            &&& clauses.len() == prog.effs[eff].len()
            &&& clause_sig_ok(prog, ss.env, eff, clauses)
            &&& prog.blocks.contains_key(body)
            &&& prog.blocks[body].sig.caps == ss.env.push(eff)
            &&& prog.blocks[body].sig.kmode is None
            &&& forall|j: int|
                0 <= j < prog.blocks[body].sig.rets.len() ==> #[trigger] prog.blocks[body].sig.rets[j]
                    < ss.env.len()
            &&& susp_ok(prog, sig, post(prog, sig, ss, i), ss.env)
        },
        // (a) a capability for the effect is in scope; (c) and multi rule at the perform
        Instr::Perform { cap, op } => {
            &&& cap < ss.env.len()
            &&& prog.effs.contains_key(ss.env[cap as int])
            &&& op < prog.effs[ss.env[cap as int]].len()
            &&& prog.effs[ss.env[cap as int]][op as int] == Mode::Once ==> all_abortable(ss)
            &&& prog.effs[ss.env[cap as int]][op as int] == Mode::Multi ==> all_many(sig, ss)
        },
        // (b) the continuation is still usable
        Instr::Resume => {
            &&& ss.k
            &&& sig.kmode is Some
            &&& susp_ok(prog, sig, post(prog, sig, ss, i), ss.env)
        },
        // (c) every linear value is consumed on the normal path
        Instr::Return => forall|sl: Slot| !#[trigger] ss.lin.contains_key(sl),
    }
}

/// The rules for one block.
pub open spec fn block_ok(prog: Prog, b: BlockId) -> bool {
    let blk = prog.blocks[b];
    &&& blk.code.len() > 0
    &&& blk.code.last() is Return
    &&& forall|j: int| 0 <= j < blk.sig.rets.len() ==> #[trigger] blk.sig.rets[j] < blk.sig.caps.len()
    &&& forall|pc: nat|
        pc < blk.code.len() ==> #[trigger] instr_ok(prog, blk.sig, ss_at(prog, b, pc), blk.code[pc as int])
}

/// The checker accepts the program.
pub open spec fn check(prog: Prog) -> bool {
    &&& prog.blocks.contains_key(prog.main)
    &&& prog.blocks[prog.main].sig == (Sig { caps: Seq::empty(), rets: Seq::empty(), kmode: None })
    &&& forall|b: BlockId| prog.blocks.contains_key(b) ==> #[trigger] block_ok(prog, b)
}

} // verus!
