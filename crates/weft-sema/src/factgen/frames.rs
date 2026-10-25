//! Frames in the facts (`docs/ir.md` 6.5): the abort destinations of each
//! node.
//!
//! Each terminator that can abort has a set of destinations ([`Dest`]):
//!
//! - past the function ([`Dest::Past`]): an abort that no local handler of
//!   the component stops;
//! - a local handler ([`Dest::Handler`]): the handler of a `handle` of the
//!   component. With `value`, a clause of the handler ends with no `resume`,
//!   and its value binds to the destination of the `handle` before the
//!   frames unwind (the `AbortValue` phase).
//!
//! The rules of `docs/ir.md` 6.5 ([`destinations`]):
//!
//! - a `Call` of a function item aborts as its summary says: an effect
//!   through the capability of a caller goes to the handler of the effect in
//!   the capability environment of the call; a failure of the runtime
//!   (`raises`) goes to the `Fail` handler of that environment; an `assert`
//!   goes past the function. A call whose summary cannot abort has no
//!   destination: the fact generator does not emit its abort edge.
//! - `Join` and `Fork` abort past the function when the task is cancelled.
//!   A child failure is `Fail.fail` through the capability environment at
//!   the node: to the local `Fail` handler (its clause cannot resume, W0504,
//!   so it gives a value), or past the function. `ScopeWait` is the same,
//!   with the environment of the `Scope` site.
//! - `Assert`, `Scope`, a `perform` through the capability of a caller and
//!   a `resume` abort past the function. A `perform` through the capability
//!   of a local handler aborts to that handler.
//!
//! The node table (`super::nodes::NodeTable`) makes one copy of each cleanup
//! block for each destination that reaches it ([`super::nodes::NodeKey::dest`]),
//! and the abort phases of each terminator for each of its destinations.
//!
//! Plan stage F7 makes the destinations. The splices that join the cleanup
//! chain of a handled body or of a scope body to its site (F14, F18), the
//! `Landing` of a handler, the clauses that can end with no `resume` and
//! `spared_at` (F15) come later. Until then a `perform` through a local
//! handler counts as an abort with a value, and a capability of a closure
//! environment counts as one of a caller.

use std::collections::BTreeMap;

use weft_ir::{
    BlockId, BodyId, BodyKind, Callee, CapArgs, CapEnvId, CapOperand, HandlerId, Program, TermKind,
    TyTable,
};

use super::nodes::PAST;
use crate::analysis::summary::{Abort, CapIface};
use crate::analysis::Summaries;

/// The identity of the effect of a failure (`Fail`).
pub const FAIL: &str = "Fail";

/// The destination id of the first handler: the id of handler `h` is
/// `FIRST_HANDLER + h`.
pub const FIRST_HANDLER: u32 = 2;

/// An abort destination (`docs/ir.md` 6.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Dest {
    /// Past the function: no local handler stops the abort.
    Past,
    /// A local handler.
    Handler {
        /// The handler.
        handler: HandlerId,
        /// A clause ends with no `resume`: its value binds to the destination
        /// of the `handle` (the `AbortValue` phase).
        value: bool,
    },
}

impl Dest {
    /// The id of the destination in [`super::nodes::NodeKey::dest`].
    pub const fn id(self) -> u32 {
        match self {
            Self::Past => PAST,
            Self::Handler { handler, .. } => FIRST_HANDLER.saturating_add(handler.0),
        }
    }

    /// True if the abort binds the value of a clause before the frames
    /// unwind.
    pub const fn value(self) -> bool {
        match self {
            Self::Past => false,
            Self::Handler { value, .. } => value,
        }
    }
}

/// The identity of effect `e`.
fn identity(tys: &TyTable, e: weft_ir::EffectId) -> Option<&str> {
    tys.effects().get(e.index()).map(|d| d.identity.as_str())
}

/// The destination of an abort of the effect with identity `effect` in the
/// capability environment `env`.
///
/// It is the handler of the first environment of
/// the chain that adds the effect, if a handled body adds it; else past the
/// function. With `value`, the clause gives a value.
pub fn resolve(p: &Program, tys: &TyTable, env: CapEnvId, effect: &str, value: bool) -> Dest {
    let mut at = Some(env);
    // The chain has at most one environment for each id.
    for _ in 0..=p.cap_envs.len() {
        let Some(id) = at else { break };
        let Some(e) = p.cap_envs.get(id.index()) else {
            break;
        };
        if e.adds
            .iter()
            .any(|(x, _)| identity(tys, *x) == Some(effect))
        {
            // The handled body that opens the environment names its handler.
            // A closure environment holds a captured capability: the closure
            // can run where the analysis cannot see (stage F14).
            let handler = p.bodies.iter().find_map(|b| match b.kind {
                BodyKind::Handled(h) if b.cap_env == id => Some(h),
                _ => None,
            });
            return handler.map_or(Dest::Past, |handler| Dest::Handler { handler, value });
        }
        at = e.parent;
    }
    Dest::Past
}

/// The capability environment of body `body`.
fn env_of(p: &Program, body: BodyId) -> Option<CapEnvId> {
    p.bodies.get(body.index()).map(|b| b.cap_env)
}

/// The capability environment of the `Scope` site of the scope body `body`:
/// a child failure at `ScopeWait` goes there (`scope_fail_unwind`).
fn site_env_of(p: &Program, body: BodyId) -> Option<CapEnvId> {
    match p.bodies.get(body.index())?.kind {
        BodyKind::Scope(s) => p.scopes.get(s.index()).and_then(|d| env_of(p, d.site)),
        _ => env_of(p, body),
    }
}

/// The destinations of terminator `t` of body `body` (`docs/ir.md` 6.5).
/// A terminator that cannot abort has none.
pub fn destinations(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    body: BodyId,
    t: &TermKind,
) -> Vec<Dest> {
    if t.unwind().is_none() {
        return Vec::new();
    }
    let mut out = Vec::new();
    // A child failure: `Fail.fail` through the environment `env`.
    let fails = |env: Option<CapEnvId>| env.map_or(Dest::Past, |e| resolve(p, tys, e, FAIL, true));
    match t {
        TermKind::Call {
            callee: Callee::Fn(f, _),
            caps,
            ..
        } => {
            let env = match caps {
                CapArgs::Lexical(e) => Some(*e),
                CapArgs::Root => None,
            };
            let through =
                |effect: &str| env.map_or(Dest::Past, |e| resolve(p, tys, e, effect, true));
            let intrinsic = p.fns.get(f.index()).is_some_and(|d| d.intrinsic.is_some());
            match sums.get(*f) {
                Ok(sum) if !intrinsic => {
                    for a in &sum.aborts {
                        out.push(match a {
                            Abort::Perform(pf) => match pf.cap {
                                CapIface::Row => through(&pf.effect),
                                CapIface::Cap(_) => Dest::Past,
                            },
                            Abort::Raises => through(FAIL),
                            Abort::Assert => Dest::Past,
                        });
                    }
                }
                // `sim.run`, `with_timeout` (a timeout is a failure at the
                // call, 5.31), or a callee with no summary: each way.
                _ => {
                    out.push(Dest::Past);
                    out.push(through(FAIL));
                }
            }
        }
        TermKind::Perform {
            cap: CapOperand::Local(place),
            ..
        } => {
            // The perform resolves its effect in its lexical environment. A
            // field of a closure environment holds a captured capability.
            let effect = cap_effect(p, tys, body, place);
            out.push(match (effect, env_of(p, body)) {
                (Some(e), Some(env)) => resolve(p, tys, env, e, true),
                _ => Dest::Past,
            });
        }
        TermKind::Join { .. } | TermKind::Fork { .. } => {
            out.push(Dest::Past);
            out.push(fails(env_of(p, body)));
        }
        TermKind::ScopeWait { .. } => {
            out.push(Dest::Past);
            out.push(fails(site_env_of(p, body)));
        }
        _ => out.push(Dest::Past),
    }
    out.sort();
    out.dedup();
    out
}

/// The identity of the effect of the capability in the whole local `place`
/// of body `body` (a capability local or an upvar local of one).
fn cap_effect<'t>(
    p: &Program,
    tys: &'t TyTable,
    body: BodyId,
    place: &weft_ir::Place,
) -> Option<&'t str> {
    if !place.proj.is_empty() {
        return None;
    }
    let ty = p
        .bodies
        .get(body.index())?
        .locals
        .get(place.local.index())?
        .ty;
    match tys.try_get(ty) {
        Some(weft_ir::Ty::Cap(e)) => identity(tys, *e),
        _ => None,
    }
}

/// The destinations of each terminator of some bodies.
#[derive(Clone, Debug, Default)]
pub struct Frames {
    /// The destinations of the terminator of each block.
    by: BTreeMap<(BodyId, BlockId), Vec<Dest>>,
}

impl Frames {
    /// The destinations of each terminator of body `body`, with the
    /// summaries `sums` of the callees ([`destinations`]).
    pub fn of_body(p: &Program, tys: &TyTable, sums: &Summaries, body: BodyId) -> Self {
        let mut f = Self::default();
        f.add(body, p, |t| destinations(p, tys, sums, body, t));
        f
    }

    /// Each terminator of body `body` that has a cleanup block aborts past
    /// the function, with no value. For the parts of the fact generator
    /// that do not need the summaries (the skeleton of plan stage F2).
    pub fn past(p: &Program, body: BodyId) -> Self {
        let mut f = Self::default();
        f.add(body, p, |t| {
            if t.unwind().is_some() {
                vec![Dest::Past]
            } else {
                Vec::new()
            }
        });
        f
    }

    /// Adds the destinations `dests` of each terminator of body `body`.
    fn add(&mut self, body: BodyId, p: &Program, dests: impl Fn(&TermKind) -> Vec<Dest>) {
        let Some(b) = p.bodies.get(body.index()) else {
            return;
        };
        for (i, blk) in b.blocks.iter().enumerate() {
            if blk.cleanup {
                continue;
            }
            let ds = dests(&blk.term.kind);
            if !ds.is_empty() {
                let block = BlockId(u32::try_from(i).unwrap_or(u32::MAX));
                self.by.insert((body, block), ds);
            }
        }
    }

    /// The destinations of the terminator of block `block` of body `body`.
    pub fn dests(&self, body: BodyId, block: BlockId) -> &[Dest] {
        self.by.get(&(body, block)).map_or(&[], Vec::as_slice)
    }
}
