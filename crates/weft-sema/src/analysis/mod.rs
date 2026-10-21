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

pub mod domain;
pub mod transfer;

use std::collections::BTreeSet;

use weft_ir::{BlockId, BodyId};

pub use domain::{AbsVal, FnVal, Key, PathStep, State, Tree};
pub use transfer::Cx;

use crate::factgen::alpha::AlphaError;

/// The most visits of one block. A loop needs widening (stage F10).
pub const VISITS: usize = 64;

/// The states of one body: the state at the entry of each block that the
/// entry reaches.
#[derive(Clone, Debug, Default)]
pub struct States {
    /// The state at the entry of each block, by block index. `None` for a
    /// block that the entry does not reach.
    entry: Vec<Option<State>>,
}

impl States {
    /// The state at the entry of block `b`, if the entry of the body reaches
    /// it.
    pub fn at(&self, b: BlockId) -> Option<&State> {
        self.entry.get(b.index()).and_then(Option::as_ref)
    }
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
    let mut out = States {
        entry: vec![None; b.blocks.len()],
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
        let Some(mut st) = out.at(blk_id).cloned() else {
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
        let mut edges: Vec<(BlockId, State)> = Vec::new();
        if let Some(u) = blk.term.kind.unwind() {
            edges.push((u, st.clone()));
        }
        transfer::term(cx, body, &mut st, &blk.term.kind)?;
        for s in blk.term.kind.normal_successors() {
            edges.push((s, st.clone()));
        }
        for (to, s) in edges {
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
