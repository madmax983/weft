//! The analysis of the `ir` pipeline (`docs/ir.md` 6.6).
//!
//! The analysis gives the abstract values that the templates of the fact
//! generator read (`crate::factgen`): for each point of a body, the places
//! that each value can point into, the function values that it can be, its
//! linear part, and the move paths that can and must hold a value
//! ([`domain`]). The transfer functions ([`transfer`]) give the state after
//! each statement and terminator.
//!
//! [`run`] is the driver: a worklist over the blocks of a body in reverse
//! post-order. It joins the state of each edge into the state at the entry
//! of its target, and visits the target again if that state changed. Stage
//! F3 has no widening (stage F10): a body whose states still change after
//! [`VISITS`] visits of one block gives an error.
//!
//! The summaries (`docs/ir.md` 6.7) carry what a body does across a call:
//! [`summary`] holds them, [`sig`] makes them from signatures and projects
//! them onto the `EffectSig` of today, [`apply`] applies them at a run node,
//! [`summarize`] makes them from the facts of a body, [`unknown`] is the run
//! node of an operation of a caller, and [`callgraph`] runs the summaries of
//! the bodies to their fixpoint, callees first (the effect inference of the
//! `ir` pipeline, `docs/ir.md` 6.8).

pub mod apply;
pub mod callgraph;
pub mod domain;
pub mod sig;
pub mod summarize;
pub mod summary;
pub mod transfer;
pub mod unknown;

use std::collections::BTreeSet;

use weft_ir::{BlockId, BodyId};

pub use domain::{AbsVal, FnVal, Key, PathStep, State, Tree};
pub use summary::{Summaries, Summary};
pub use transfer::Cx;

use crate::factgen::alpha::AlphaError;

/// The most visits of one block. A loop needs widening (stage F10).
pub const VISITS: usize = 64;

/// The states of one body: the state at the entry of each block that the
/// entry reaches and that is a *join* block.
///
/// A join block is the entry block, or a block with no edge in or with more
/// than one (normal and `unwind` edges). In a body with a back edge, each
/// block is a join block. The state at the entry of another block is the
/// state on its one edge in: the user of the states computes it from the
/// state of its predecessor ([`edges`]). So a long chain of blocks
/// (each call, each node of a cleanup chain) keeps no state for each block,
/// and the memory is not the number of blocks times the number of locals.
#[derive(Clone, Debug, Default)]
pub struct States {
    /// The state at the entry of each join block, by block index. `None`
    /// for a block that the entry does not reach, and for a block that is
    /// not a join block.
    entry: Vec<Option<State>>,
    /// True for each join block, by block index.
    join: Vec<bool>,
}

impl States {
    /// The state at the entry of block `b`, if `b` is a join block that the
    /// entry of the body reaches.
    pub fn at(&self, b: BlockId) -> Option<&State> {
        self.entry.get(b.index()).and_then(Option::as_ref)
    }

    /// True if block `b` is a join block: the states keep its entry state.
    pub fn is_join(&self, b: BlockId) -> bool {
        self.join.get(b.index()).copied().unwrap_or(true)
    }
}

/// The edges out of a block and the state on each one.
///
/// `st` is the state after the statements of block `blk_id` of body `body`:
/// an `unwind` edge gets the state before the terminator `term`, a normal
/// edge the state after it.
///
/// # Errors
///
/// The errors of the transfer function of the terminator.
pub fn edges(
    cx: &mut Cx<'_>,
    body: BodyId,
    blk_id: BlockId,
    term: &weft_ir::TermKind,
    mut st: State,
) -> Result<Vec<(BlockId, State)>, AlphaError> {
    let mut out: Vec<(BlockId, State)> = Vec::new();
    if let Some(u) = term.unwind() {
        out.push((u, st.clone()));
    }
    transfer::term(cx, body, blk_id, &mut st, term)?;
    for s in term.normal_successors() {
        out.push((s, st.clone()));
    }
    Ok(out)
}

/// The join blocks of body `b` (see [`States`]): the entry, each block with
/// a number of edges in other than one, and each block if the body has a
/// back edge (an edge to a block whose `rank` is not higher).
fn join_blocks(b: &weft_ir::Body, rank: &[usize]) -> Vec<bool> {
    let mut ins = vec![0usize; b.blocks.len()];
    let mut back = false;
    for (bi, blk) in b.blocks.iter().enumerate() {
        let from = rank.get(bi).copied().unwrap_or(usize::MAX);
        let succs = blk
            .term
            .kind
            .unwind()
            .into_iter()
            .chain(blk.term.kind.normal_successors());
        for to in succs {
            if let Some(n) = ins.get_mut(to.index()) {
                *n += 1;
            }
            let r = rank.get(to.index()).copied().unwrap_or(usize::MAX);
            if from != usize::MAX && r <= from {
                back = true;
            }
        }
    }
    let mut out: Vec<bool> = ins.iter().map(|&n| back || n != 1).collect();
    if let Some(e) = out.get_mut(b.entry.index()) {
        *e = true;
    }
    out
}

/// Runs the analysis of body `body` from the state `init` at its entry.
///
/// A normal successor of a block gets the state after its terminator. The
/// cleanup block of a terminator that can abort gets the state before it:
/// an abort leaves the destination with no new value.
///
/// # Errors
///
/// The errors of the transfer functions, and [`AlphaError::Later`] if a
/// block needs more than [`VISITS`] visits (a loop: widening is stage F10).
pub fn run(cx: &mut Cx<'_>, body: BodyId, init: State) -> Result<States, AlphaError> {
    run_with(cx, body, init, false)
}

/// [`run`] that keeps the state of each block.
///
/// It keeps the state at the entry of each block that the entry reaches,
/// also of a block that is not a join block (for tests and tools: the
/// memory is the number of blocks times the size of a state).
///
/// # Errors
///
/// The errors of [`run`].
pub fn run_all(cx: &mut Cx<'_>, body: BodyId, init: State) -> Result<States, AlphaError> {
    run_with(cx, body, init, true)
}

/// [`run`], with `all`: keep the state of each block.
fn run_with(cx: &mut Cx<'_>, body: BodyId, init: State, all: bool) -> Result<States, AlphaError> {
    let p = cx.p;
    let b = p
        .bodies
        .get(body.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no body b{}", body.0)))?;
    let order = weft_ir::order::reverse_post_order(b);
    let mut rank = vec![usize::MAX; b.blocks.len()];
    for (i, blk) in order.iter().enumerate() {
        if let Some(r) = rank.get_mut(blk.index()) {
            *r = i;
        }
    }
    let join = join_blocks(b, &rank);
    let mut out = States {
        entry: vec![None; b.blocks.len()],
        join,
    };
    let mut visits = vec![0usize; b.blocks.len()];
    let mut work: BTreeSet<usize> = BTreeSet::new();
    if let Some(e) = out.entry.get_mut(b.entry.index()) {
        *e = Some(init);
        work.insert(rank.get(b.entry.index()).copied().unwrap_or(0));
    }
    while let Some(r) = work.pop_first() {
        let Some(&blk_id) = order.get(r) else {
            continue;
        };
        let Some(blk) = b.blocks.get(blk_id.index()) else {
            continue;
        };
        // The state of a block that is not a join block goes to its one
        // successor edge and is not kept: a body with no back edge visits
        // each block once, after each of its predecessors.
        let keep = all || out.is_join(blk_id);
        let Some(mut st) = (match out.entry.get_mut(blk_id.index()) {
            Some(slot) if keep => slot.clone(),
            Some(slot) => slot.take(),
            None => None,
        }) else {
            continue;
        };
        if let Some(v) = visits.get_mut(blk_id.index()) {
            *v += 1;
            if *v > VISITS {
                return Err(AlphaError::Later("a loop (widening, stage F10)"));
            }
        }
        for s in &blk.stmts {
            transfer::stmt(cx, body, &mut st, &s.kind)?;
        }
        for (to, s) in edges(cx, body, blk_id, &blk.term.kind, st)? {
            let Some(slot) = out.entry.get_mut(to.index()) else {
                continue;
            };
            let changed = if let Some(have) = slot {
                have.join(&s)
            } else {
                *slot = Some(s);
                true
            };
            if changed {
                if let Some(&tr) = rank.get(to.index()) {
                    work.insert(tr);
                }
            }
        }
    }
    Ok(out)
}
