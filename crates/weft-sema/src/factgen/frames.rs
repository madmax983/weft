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
//! - A `Call` of a function value aborts past the function, through the
//!   `Fail` handler of the capability environment of the call, and to the
//!   handler there of each effect that the value can perform (plan stage
//!   F17.2: a function item or a parameter runs with the handlers of the
//!   call).
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
//! Plan stage F7 makes the destinations. Stage F14 joins the cleanup chain of
//! a handled body to its site ([`Frames::of_bodies`]: a `handle` aborts where
//! its handled body aborts past its handler), and gives the node that runs
//! a clause the aborts of the clause past its handler. Stage F15 keeps the
//! abort to a local handler only if a clause that the node runs can end with
//! no `resume` (`clause::lands`); [`clause_handlers`] gives the handlers
//! whose clauses a node runs. Until then a capability of a closure
//! environment counts as one of a caller. Stage F18: a `scope` aborts where
//! its scope body aborts, and past the function.

use std::collections::BTreeMap;

use weft_ir::{
    BlockId, BodyId, BodyKind, Callee, CapArgs, CapEnvId, CapOperand, HandlerId, Program, TermKind,
    TyTable,
};

use super::nodes::PAST;
use crate::analysis::clause;
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

/// True if the program declares an operation that is `multi`.
pub fn has_multi_ops(tys: &TyTable) -> bool {
    tys.effects().iter().any(|e| e.ops.iter().any(|o| o.multi))
}

/// True if terminator `t` of body `body` can wait at a `multi` operation of
/// a handler of a caller (OL-R2a, plan stage F16).
///
/// The handler can resume it more than once: then the code after it runs
/// again, up to the `Return` of the body, from a copy of the frames of the
/// body (the re-entry edges of `docs/ir.md` 6.5).
///
/// It is a `perform` of a `multi` operation through the row; a call of a
/// function whose summary performs a `multi` operation through the row that
/// no local handler handles, or that can resume more than once for another
/// reason; a call of a function value whose type states a row with a
/// `multi` operation. The analysis adds the run nodes whose function values
/// can resume more than once (`clause::Handlers::dyn_rows`).
/// Only in a program that declares a `multi` operation and a handler (a
/// program with no handler, group D off, has no `resume`).
pub fn row_multi(p: &Program, tys: &TyTable, sums: &Summaries, body: BodyId, t: &TermKind) -> bool {
    // A program with no handler cannot resume a continuation more than once.
    if p.handlers.is_empty() || !has_multi_ops(tys) {
        return false;
    }
    let multi_effect = |id: &str| {
        tys.effects()
            .iter()
            .any(|e| e.identity == id && e.ops.iter().any(|o| o.multi))
    };
    match t {
        TermKind::Perform {
            cap: CapOperand::Row(e),
            op,
            ..
        } => tys
            .effects()
            .get(e.index())
            .and_then(|d| d.ops.get(op.index()))
            .is_some_and(|o| o.multi),

        TermKind::Call {
            callee: Callee::Fn(f, _),
            caps,
            ..
        } => {
            let env = match caps {
                CapArgs::Lexical(e) => Some(*e),
                CapArgs::Root => None,
            };
            // An effect that a local handler with no clause for an operation
            // passes on to a caller goes past the function too (stage R0d,
            // `clause::serving_all`).
            let past = |effect: &str| {
                env.is_none_or(|e| match resolve(p, tys, e, effect, true) {
                    Dest::Past => true,
                    Dest::Handler { handler, .. } => clause::serving_all(p, tys, handler).1,
                })
            };
            match sums.get(*f) {
                Ok(s) => {
                    let mut multi_ops = s
                        .performs
                        .iter()
                        .filter(|pf| multi_effect(&pf.effect))
                        .peekable();
                    let explained = multi_ops.peek().is_some();
                    let by_row = s.performs.iter().any(|pf| {
                        matches!(pf.cap, CapIface::Row)
                            && multi_effect(&pf.effect)
                            && past(&pf.effect)
                    });
                    by_row || (s.multi && !explained)
                }
                Err(_) => true,
            }
        }
        TermKind::Call {
            callee: Callee::Value(f),
            ..
        } => {
            let ty = p.body(body).and_then(|b| match f {
                weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q) if q.proj.is_empty() => {
                    b.local(q.local).map(|d| d.ty)
                }
                _ => None,
            });
            // A value with no stated row, or that runs a function value of
            // its own: the analysis finds the summaries that it applies
            // (`clause::Handlers::dyn_rows`).
            match ty.and_then(|t| tys.try_get(t)) {
                Some(weft_ir::Ty::Fn(fty)) => fty.row.as_ref().is_some_and(|row| {
                    row.iter().any(|e| {
                        tys.effects()
                            .get(e.index())
                            .is_some_and(|d| d.ops.iter().any(|o| o.multi))
                    })
                }),
                _ => false,
            }
        }
        _ => false,
    }
}

/// The blocks of closure body `body` whose terminator performs through a
/// captured capability whose handler can resume more than once (hole
/// C1-H4, follow-up C1.3).
///
/// The clause runs where a caller runs the closure, and a second resume
/// runs the code of the closure after the perform again. The blocks after
/// such a node are in a cycle for the runs of the values of the interface
/// (`Run::many`: the caller runs them again), but they get no re-entry edge:
/// the copy of the frames gives a value that the closure moved a new copy.
pub fn captured_multi_nodes(p: &Program, tys: &TyTable, body: BodyId) -> Vec<BlockId> {
    // A handled body or a clause inside the closure body performs through
    // the environment of the closure too (stage R0d).
    let Some((c, _)) = super::alpha::unit_closure(p, body).and_then(|cb| p.closure_of(cb)) else {
        return Vec::new();
    };
    let Some(b) = p.body(body) else {
        return Vec::new();
    };
    b.blocks
        .iter()
        .enumerate()
        .filter(|(_, blk)| !blk.cleanup)
        .filter(|(_, blk)| match &blk.term.kind {
            TermKind::Perform {
                cap: CapOperand::Local(place),
                op,
                ..
            } => clause::captured_cap(p, tys, body, place)
                .map(|(k, _)| k)
                .or_else(|| clause::passes_to_capture(p, body, place, *op).map(|(k, _)| k))
                .and_then(|k| clause::capture_handler(p, c, k))
                .and_then(|h| clause::serving(p, h, *op))
                .is_some_and(|h| clause::multi_twice(p, h)),
            // A run of a function value, if a closure that the closure body
            // made captures a capability of a `multi` handler of the closure
            // again (stage R0d): the value can be that closure.
            TermKind::Call {
                callee: Callee::Value(_),
                ..
            } if recaptures_multi(p, tys, c) => true,
            // A call in the handled body of a handler of the closure that
            // passes an operation on out of the closure, to a capture of a
            // `multi` handler (stage R0d): the callee can perform it.
            TermKind::Call { .. } => passes_out_multi(p, tys, c, body),
            _ => false,
        })
        .map(|(i, _)| BlockId(u32::try_from(i).unwrap_or(u32::MAX)))
        .collect()
}

/// True if body `body` of closure `c` is inside the handled body of a
/// handler of the closure that passes an operation on out of the closure
/// to a capture whose handler (or a handler that serves an operation that it
/// passes on) can resume more than once (stage R0d).
fn passes_out_multi(p: &Program, tys: &TyTable, c: weft_ir::ClosureId, body: BodyId) -> bool {
    let Some(cb) = p.closures.get(c.index()).map(|d| d.body) else {
        return false;
    };
    p.handlers.iter().enumerate().any(|(i, d)| {
        let h = HandlerId(u32::try_from(i).unwrap_or(u32::MAX));
        super::alpha::unit_root(p, d.handled) == cb
            && clause::inside(p, body, d.handled)
            && clause::serving_paths(p, tys, h).iter().any(|s| match *s {
                clause::Served::Capture(x, k) if x == cb => clause::capture_handler(p, c, k)
                    .is_some_and(|ch| {
                        clause::serving_all(p, tys, ch)
                            .0
                            .iter()
                            .any(|&y| clause::multi_twice(p, y))
                    }),
                _ => false,
            })
    })
}

/// True if a closure that the body of closure `c` (or a body inside it)
/// makes captures a `Cap` capture of `c` again whose handler, or a handler
/// that serves an operation that it passes on, can resume more than once
/// (stage R0d).
fn recaptures_multi(p: &Program, tys: &TyTable, c: weft_ir::ClosureId) -> bool {
    let Some(cb) = p.closures.get(c.index()).map(|d| d.body) else {
        return false;
    };
    p.closures.iter().any(|d| {
        super::alpha::unit_root(p, d.maker) == cb
            && d.captures.iter().any(|cap| {
                cap.mode == weft_ir::CaptureMode::Cap
                    && super::alpha::env_capture(p, d.maker, &cap.source)
                        .filter(|(oc, _, m)| *oc == c && *m == weft_ir::CaptureMode::Cap)
                        .and_then(|(_, k, _)| clause::capture_handler(p, c, k))
                        .is_some_and(|h| {
                            clause::serving_all(p, tys, h)
                                .0
                                .iter()
                                .any(|&x| clause::multi_twice(p, x))
                        })
            })
    })
}

/// The blocks of body `body` whose terminator can wait at a `multi`
/// operation of a handler of a caller ([`row_multi`]).
pub fn row_multi_nodes(p: &Program, tys: &TyTable, sums: &Summaries, body: BodyId) -> Vec<BlockId> {
    let Some(b) = p.body(body) else {
        return Vec::new();
    };
    if p.handlers.is_empty() || !has_multi_ops(tys) {
        return Vec::new();
    }
    b.blocks
        .iter()
        .enumerate()
        .filter(|(_, blk)| !blk.cleanup && row_multi(p, tys, sums, body, &blk.term.kind))
        .map(|(i, _)| BlockId(u32::try_from(i).unwrap_or(u32::MAX)))
        .collect()
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

/// Each destination of an abort of the effect `effect` from a function
/// value in the capability environment `env` (HENV-SHADOW).
///
/// The facts do not know the handler environment of the value
/// ([`henv_unknown`]).
///
/// A closure runs with the handlers where it was made. If a call made it in
/// the handled body of a local handler H of the effect, and it runs in the
/// handled body of an inner handler H2 of the same effect, its perform goes
/// to H, not to H2. So the result has the handler of each handled body on
/// the chain of `env` that adds the effect, up to the first environment
/// that adds it and is not a handled body (a captured capability: past the
/// function from there), and past the function. The first one is
/// [`resolve`].
pub fn resolve_all(
    p: &Program,
    tys: &TyTable,
    env: CapEnvId,
    effect: &str,
    value: bool,
) -> Vec<Dest> {
    let mut out = Vec::new();
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
            let handler = p.bodies.iter().find_map(|b| match b.kind {
                BodyKind::Handled(h) if b.cap_env == id => Some(h),
                _ => None,
            });
            match handler {
                Some(handler) => out.push(Dest::Handler { handler, value }),
                None => break,
            }
        }
        at = e.parent;
    }
    out.push(Dest::Past);
    out
}

/// The destinations of an abort of the effect with identity `effect` in the
/// capability environment `env` of call `at` (a body and its terminator),
/// which can run a function value (HENV-SHADOW).
///
/// It is [`resolve`], or each destination of [`resolve_all`] if the chain has
/// more than one local handler of the effect and the call can run a value
/// whose handler environment is not known for the effect
/// ([`henv_unknown`]). The check runs only if the chain has more than one
/// such handler.
///
/// A known value goes to [`resolve`] and, at a run of a function value,
/// past the function: a function item runs with the handlers of the run
/// node (the innermost local handler), and a closure of a caller performs
/// past the function.
pub fn run_dests(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    at: (BodyId, &TermKind),
    env: CapEnvId,
    effect: &str,
) -> Vec<Dest> {
    let mut all = resolve_all(p, tys, env, effect, true);
    let handlers = all
        .iter()
        .filter(|d| matches!(d, Dest::Handler { .. }))
        .count();
    if handlers < 2 || !henv_unknown(p, tys, sums, at, env, effect) {
        all.truncate(1);
    }
    all
}

/// The first environment on the chain of `env` that adds the capability of
/// `effect`, with the place of the capability there.
pub fn adding_env(
    p: &Program,
    tys: &TyTable,
    env: CapEnvId,
    effect: &str,
) -> Option<(CapEnvId, weft_ir::Place)> {
    let mut at = Some(env);
    for _ in 0..=p.cap_envs.len() {
        let id = at?;
        let e = p.cap_envs.get(id.index())?;
        if let Some((_, q)) = e
            .adds
            .iter()
            .find(|(x, _)| identity(tys, *x) == Some(effect))
        {
            return Some((id, q.clone()));
        }
        at = e.parent;
    }
    None
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
///
/// A local handler is a destination only if a clause that the terminator
/// runs can end with no resume point (`clause::lands`, plan stage F15): the
/// clause of the operation for a `perform`, a clause of the handler for a
/// call. A clause that resumes on each path gives no abort to its handler.
pub fn destinations(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    body: BodyId,
    t: &TermKind,
) -> Vec<Dest> {
    let op = match t {
        TermKind::Perform { op, .. } => Some(*op),
        _ => None,
    };
    reach(p, tys, sums, body, t, true)
        .into_iter()
        .filter(|d| match d {
            Dest::Handler { handler, .. } => clause::handler_lands(p, *handler, op),
            Dest::Past => true,
        })
        .collect()
}

/// True if each effect of the row of call `t` goes to a local handler.
///
/// The call is a call of a function item whose summary performs effects
/// through the capability of a caller, and each such effect goes to a local
/// handler (plan stage F15): the call runs the clauses of the operations
/// itself.
pub fn row_local(p: &Program, tys: &TyTable, sums: &Summaries, t: &TermKind) -> bool {
    let TermKind::Call {
        callee: Callee::Fn(f, _),
        caps: CapArgs::Lexical(env),
        ..
    } = t
    else {
        return false;
    };
    let Ok(sum) = sums.get(*f) else {
        return false;
    };
    let mut row = sum
        .performs
        .iter()
        .filter(|pf| matches!(pf.cap, CapIface::Row))
        .peekable();
    row.peek().is_some()
        && row.all(|pf| {
            matches!(
                resolve(p, tys, *env, &pf.effect, true),
                Dest::Handler { .. }
            )
        })
}

/// The local handlers whose clauses terminator `t` of body `body` runs.
///
/// They are the handler of a `perform` through a local capability, and each
/// local handler that a call performs through or fails to. The clauses run
/// also if they resume on each path ([`destinations`] has no abort to them
/// then).
pub fn clause_handlers(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    body: BodyId,
    t: &TermKind,
) -> Vec<HandlerId> {
    handlers_of(reach(p, tys, sums, body, t, true))
}

/// [`clause_handlers`] with no handler that only the function values reach.
///
/// Such a handler is the local `Fail` handler of a failure of a function
/// value that the terminator or a callee runs, or a handler whose
/// capability a closure captures. The analysis tells if a value that the
/// terminator runs can reach it (`clause::run_handlers`, issues #57 and
/// #58).
pub fn own_clause_handlers(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    body: BodyId,
    t: &TermKind,
) -> Vec<HandlerId> {
    handlers_of(reach(p, tys, sums, body, t, false))
}

/// The handlers of the destinations `ds`, sorted, each one time.
fn handlers_of(ds: Vec<Dest>) -> Vec<HandlerId> {
    let mut out: Vec<HandlerId> = ds
        .into_iter()
        .filter_map(|d| match d {
            Dest::Handler { handler, .. } => Some(handler),
            Dest::Past => None,
        })
        .collect();
    out.sort();
    out.dedup();
    out
}

/// The destinations of terminator `t` of body `body` if each clause can end
/// with no resume point: a [`Dest::Handler`] is a handler whose clauses the
/// terminator runs. With `full`, also the destinations of the function
/// values that the terminator or a callee runs: the local `Fail` handler of
/// the call, and each active handler whose capability a closure captures. With no `full`, the
/// analysis tells which of them the values at the node reach
/// (`clause::run_handlers`, issues #57 and #58).
fn reach(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    body: BodyId,
    t: &TermKind,
    full: bool,
) -> Vec<Dest> {
    if t.unwind().is_none() {
        return Vec::new();
    }
    let mut out: Vec<Dest> = Vec::new();
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
            let intrinsic = p.fns.get(f.index()).is_some_and(|d| d.intrinsic.is_some());
            // A function value of an argument that the callee runs performs
            // through the handlers where it was made (HENV-SHADOW): each
            // local handler of the chain of the call.
            let through = |effect: &str| match env {
                Some(e) if !intrinsic => run_dests(p, tys, sums, (body, t), e, effect),
                Some(e) => vec![resolve(p, tys, e, effect, true)],
                None => vec![Dest::Past],
            };
            match sums.get(*f) {
                Ok(sum) if !intrinsic => {
                    // A function value that the callee runs can abort in
                    // each way (stage F12, part `runs`).
                    if !sum.runs.is_empty() {
                        out.push(Dest::Past);
                        if full {
                            out.extend(through(FAIL));
                        }
                    }
                    for a in &sum.aborts {
                        match a {
                            Abort::Perform(pf) => match pf.cap {
                                CapIface::Row => out.extend(through(&pf.effect)),
                                CapIface::Cap(_) => out.push(Dest::Past),
                            },
                            Abort::Raises => out.extend(through(FAIL)),
                            Abort::Assert => out.push(Dest::Past),
                        }
                    }
                }
                // `sim.run`, `with_timeout` (a timeout is a failure at the
                // call, 5.31), or a callee with no summary: each way.
                _ => {
                    out.push(Dest::Past);
                    out.extend(through(FAIL));
                }
            }
        }
        TermKind::Perform {
            cap: CapOperand::Local(place),
            op,
            ..
        } => {
            // The perform goes to the handler that serves its operation: a
            // handler with no clause for it passes it on (stage R0d,
            // `clause::serving`), maybe to a caller. A field of a closure
            // environment holds a captured capability.
            match clause::perform_target(p, body, place, *op) {
                Some(Some(handler)) => out.push(Dest::Handler {
                    handler,
                    value: true,
                }),
                Some(None) => out.push(Dest::Past),
                None => {
                    let effect = cap_effect(p, tys, body, place);
                    out.push(match (effect, env_of(p, body)) {
                        (Some(e), Some(env)) => resolve(p, tys, env, e, true),
                        _ => Dest::Past,
                    });
                }
            }
        }
        TermKind::Join { .. } | TermKind::Fork { .. } => {
            out.push(Dest::Past);
            out.push(fails(env_of(p, body)));
        }
        // A scope with no task cannot fail or be cancelled at its end (plan
        // stage F18, as the old lowering).
        TermKind::ScopeWait { .. } => {
            let k = match p.bodies.get(body.index()).map(|b| b.kind) {
                Some(BodyKind::Scope(k)) => Some(k),
                _ => None,
            };
            // A spawn that does not name its scope can start a task in each
            // scope (stage R0e).
            if k.is_none_or(|k| p.spawns.iter().any(|d| d.scope == Some(k)))
                || crate::analysis::tasks::unowned(p)
            {
                out.push(Dest::Past);
                out.push(fails(site_env_of(p, body)));
            }
        }
        // A function item or a function parameter runs with the handlers of
        // the call: an effect of its row goes to the handler of the effect in
        // the capability environment of the call, and a failure of the
        // runtime goes to the `Fail` handler there (plan stage F17.2,
        // D-FNVAL-ROW). A closure runs with the handlers where it was made:
        // its effects can go past the function too. A closure that a call
        // made (also through a field, a container or a clause) can hold a
        // local handler that is not the innermost one of its effect at the
        // run node: each local handler of the chain gets the effect
        // (HENV-SHADOW, [`henv_unknown`]).
        TermKind::Call {
            callee: Callee::Value(f),
            caps: CapArgs::Lexical(e),
            ..
        } => {
            let to = |effect: &str| run_dests(p, tys, sums, (body, t), *e, effect);
            out.push(Dest::Past);
            if full {
                out.extend(to(FAIL));
            }
            for effect in value_effects(p, tys, sums, body, f, *e) {
                out.extend(to(&effect));
            }
        }
        _ => out.push(Dest::Past),
    }
    // A call does not name the operation: a handler with no clause for an
    // operation passes it on to the handler that serves it, out of the
    // closure, or to a caller (stage R0d, `clause::serving_paths`).
    if matches!(t, TermKind::Call { .. }) {
        out = out
            .into_iter()
            .flat_map(|d| served_dests(p, tys, d))
            .collect();
    }
    // A run of a function value can run a closure that performs through a
    // captured capability of a local handler: the node runs the clauses of
    // the handler (plan stage F16).
    if full && runs_values(p, tys, sums, body, t) {
        for h in clause::captured_handlers(p, tys) {
            let active = p
                .handlers
                .get(h.index())
                .is_some_and(|d| clause::spliced_into(p, body, d.handled));
            if active {
                out.push(Dest::Handler {
                    handler: h,
                    value: true,
                });
            }
        }
    }
    out.sort();
    out.dedup();
    out
}

/// The destinations of destination `d` of a call with each operation of the
/// effect of its handler (stage R0d): the handler that serves each operation
/// (`clause::serving_path`), and past the function for an operation that
/// passes on to a caller or out of the closure.
fn served_dests(p: &Program, tys: &TyTable, d: Dest) -> Vec<Dest> {
    match d {
        Dest::Past => vec![Dest::Past],
        Dest::Handler { handler, value } => clause::serving_paths(p, tys, handler)
            .into_iter()
            .map(|s| match s {
                clause::Served::Local(x) => Dest::Handler { handler: x, value },
                clause::Served::Capture(..) | clause::Served::Caller => Dest::Past,
            })
            .collect(),
    }
}

/// The effects of local handlers that a run of the function value `f` of
/// body `body` can perform through the capability environment `env` of the
/// call (plan stage F17.2, D-FNVAL-ROW).
///
/// The handled bodies on the chain of `env` give the local handlers. A
/// value whose type states a row can perform the effects of the row. A
/// value with no stated row passes the effects of the call through: each
/// effect of a local handler, except for a value that only a closure can
/// give (a closure runs with the handlers where it was made), if the
/// closure captures no function value (`plain_closures`).
fn value_effects(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    body: BodyId,
    f: &weft_ir::Operand,
    env: CapEnvId,
) -> Vec<String> {
    let local = local_effects(p, tys, env);
    if local.is_empty() {
        return local;
    }
    let q = match f {
        weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q) if q.proj.is_empty() => q,
        _ => return local,
    };
    let ty = p.body(body).and_then(|b| b.local(q.local)).map(|d| d.ty);
    match ty.and_then(|t| tys.try_get(t)) {
        Some(weft_ir::Ty::Fn(fty)) => match &fty.row {
            Some(row) => row
                .iter()
                .filter_map(|&e| identity(tys, e))
                .filter(|e| local.iter().any(|x| x == e))
                .map(str::to_string)
                .collect(),
            // A closure that captures a function value runs it with the
            // handlers where that value was made (HENV-SHADOW).
            None if closure_only(p, Some(sums), body, q.local, 0)
                && plain_closures(p, tys, sums, body, q.local, 0) =>
            {
                Vec::new()
            }
            None => local,
        },
        _ => local,
    }
}

/// The identities of the effects that a handled body on the chain of
/// capability environment `env` handles, and that no inner environment of
/// the chain adds first.
fn local_effects(p: &Program, tys: &TyTable, env: CapEnvId) -> Vec<String> {
    let mut seen: Vec<String> = Vec::new();
    let mut out = Vec::new();
    let mut at = Some(env);
    for _ in 0..=p.cap_envs.len() {
        let Some(id) = at else { break };
        let Some(e) = p.cap_envs.get(id.index()) else {
            break;
        };
        let handled = p
            .bodies
            .iter()
            .any(|b| matches!(b.kind, BodyKind::Handled(_)) && b.cap_env == id);
        for (x, _) in &e.adds {
            let Some(name) = identity(tys, *x) else {
                continue;
            };
            if seen.iter().any(|s| s == name) {
                continue;
            }
            seen.push(name.to_string());
            if handled {
                out.push(name.to_string());
            }
        }
        at = e.parent;
    }
    out
}

/// True if terminator `t` of body `body` is a call of a function value
/// that only a closure can give (`closure_only`): the analysis knows the
/// summaries that it applies.
pub fn runs_closure(p: &Program, body: BodyId, t: &TermKind) -> bool {
    match t {
        TermKind::Call {
            callee: Callee::Value(weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q)),
            ..
        } if q.proj.is_empty() => closure_only(p, None, body, q.local, 0),
        _ => false,
    }
}

/// True if call `at` can run a function value whose handler environment
/// the facts do not know (HENV-SHADOW).
///
/// `at` is a body and its terminator; `env` is the capability environment
/// of the call, and `effect` is the identity of the effect.
///
/// A closure runs with the handlers where it was made (the interpreter
/// takes the handler environment of the closure value). A closure that a
/// call made in the handled body of a local handler H of an effect, and
/// that runs in the handled body of an inner handler H2 of the same
/// effect, performs to H, not to H2. Then each local handler of the chain
/// of the run node gets the effect ([`resolve_all`]).
///
/// The handler environment is known for these values only:
///
/// - a constant (a function item: it runs with the handlers of the run
///   node);
/// - a local that can only hold closures of this function or closures that
///   perform nothing (`closure_only`): such a closure captures the
///   capability of each local handler that it performs through;
/// - a parameter of a function or a closure that gets no other value
///   (`entry_param`): the value existed before the frame, so its handler
///   environment holds no handler of the frame;
/// - a value that was made in this run of the handled body of the innermost
///   local handler of the effect at the call (`made_under`), also through a
///   field or an element: the chain of its maker goes through that handler
///   first.
///
/// The call can run each function value of its arguments (a callee whose
/// summary runs a value, or a function value), and the callee itself for a
/// call of a function value. Each other value counts: for example the result
/// of an operation (a value that a clause gives), or the result of a call in
/// the handled body of an outer handler (`q02`).
pub fn henv_unknown(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    at: (BodyId, &TermKind),
    env: CapEnvId,
    effect: &str,
) -> bool {
    let (body, t) = at;
    let TermKind::Call { callee, args, .. } = t else {
        return false;
    };
    let Some(b) = p.body(body) else {
        return true;
    };
    let inner = match resolve(p, tys, env, effect, true) {
        Dest::Handler { handler, .. } => Some(handler),
        Dest::Past => None,
    };
    let unknown = |op: &weft_ir::Operand| match op {
        weft_ir::Operand::Const(_) => false,
        weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q) => {
            let fns = b
                .local(q.local)
                .is_none_or(|d| crate::props::ir_has_fns(tys, d.ty));
            let whole = q.proj.is_empty()
                && ((closure_only(p, Some(sums), body, q.local, 0)
                    && plain_closures(p, tys, sums, body, q.local, 0))
                    || entry_param(p, body, q.local));
            let made =
                inner.is_some_and(|h| made_under(p, tys, sums, (body, q.local), h, effect, 0));
            fns && !whole && !made
        }
    };
    let runs_args = match callee {
        Callee::Value(f) if unknown(f) => return true,
        Callee::Value(_) => true,
        Callee::Fn(f, _) => sums
            .get(*f)
            .map_or(true, |s| !s.runs.is_empty() || s.unknown_runs),
    };
    runs_args && args.iter().any(unknown)
}

/// The bodies that can write a local of body `owner`: the body itself and
/// the bodies that name locals of a parent as upvar locals (clauses,
/// handled bodies and scope bodies).
fn writers(p: &Program, owner: BodyId) -> impl Iterator<Item = (BodyId, &weft_ir::Body)> {
    p.bodies
        .iter()
        .enumerate()
        .map(|(i, b)| (BodyId(u32::try_from(i).unwrap_or(u32::MAX)), b))
        .filter(move |(id, b)| *id == owner || b.kind.has_upvars())
}

/// True if body `b` runs in each run of handled body `handled`: it is that
/// body, or a handled body, a clause or a scope body inside it (no closure
/// body and no function body between them).
fn in_run_of(p: &Program, b: BodyId, handled: BodyId) -> bool {
    let mut at = b;
    for _ in 0..=p.bodies.len() {
        if at == handled {
            return true;
        }
        let Some(x) = p.body(at) else {
            return false;
        };
        match (x.kind, x.parent) {
            (BodyKind::Handled(_) | BodyKind::Clause(..) | BodyKind::Scope(_), Some(up)) => at = up,
            _ => return false,
        }
    }
    false
}

/// True if each value that local `at.1` of body `at.0` can hold was made in
/// this run of the handled body of local handler `h`, by code whose
/// capability environment sends the effect with identity `effect` to `h`
/// first (HENV-SHADOW). Then the effect of such a value goes to `h` (or past
/// the function), as [`resolve`] at a run node inside `h` says.
///
/// The local belongs to a body that runs in each run of the handled body
/// (`in_run_of`), so its values do not outlive the run of the handler. Each
/// whole write of it is a constant, a copy of a local with the same property
/// (also of a field or an element of it), an aggregate (also a new closure:
/// its operands are its captures, and it captures the capabilities that it
/// performs through) whose operands with a function part have the same
/// property, or the result of a call of a function item with an IR body
/// through such an environment whose result can be closures that the callee
/// makes and function items only (part `ret.fns`, not empty: a declaration
/// such as `Vec.pop` gives no part). No write of a part, no reference to the
/// local, and no closure that shares its cell (`shares_cell`): a callee or
/// the closure could put another value into it.
fn made_under(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    at: (BodyId, weft_ir::LocalId),
    h: HandlerId,
    effect: &str,
    depth: usize,
) -> bool {
    if depth > COPY_DEPTH {
        return false;
    }
    let Ok(owner) = super::alpha::owner_local(p, at.0, at.1) else {
        return false;
    };
    let Some(handled) = p.handlers.get(h.index()).map(|d| d.handled) else {
        return false;
    };
    if !in_run_of(p, owner.0, handled) {
        return false;
    }
    let is_owner = |b: BodyId, q: &weft_ir::Place| {
        super::alpha::owner_local(p, b, q.local).ok() == Some(owner)
    };
    let maker = |t: &TermKind| match t {
        TermKind::Call {
            callee: Callee::Fn(f, _),
            caps: CapArgs::Lexical(e),
            ..
        } => {
            let body = p
                .fns
                .get(f.index())
                .is_some_and(|d| d.body.is_some() && d.intrinsic.is_none());
            body && matches!(resolve(p, tys, *e, effect, true), Dest::Handler { handler, .. } if handler == h)
                && sums.get(*f).is_ok_and(|s| {
                    !s.ret.fns.is_empty()
                        && s.ret.fns.iter().all(|x| {
                            matches!(
                                x,
                                crate::analysis::summary::RetFn::Made(_)
                                    | crate::analysis::summary::RetFn::Item(..)
                            )
                        })
                })
        }
        _ => false,
    };
    if shares_cell(p, owner) {
        return false;
    }
    let mut any = false;
    for (bid, b) in writers(p, owner.0) {
        // An operand of an aggregate: a value with a function part must
        // have the same property.
        let part_ok = |op: &weft_ir::Operand| match op {
            weft_ir::Operand::Const(_) => true,
            weft_ir::Operand::Copy(src) | weft_ir::Operand::Move(src) => {
                b.local(src.local)
                    .is_some_and(|d| !crate::props::ir_has_fns(tys, d.ty))
                    || made_under(p, tys, sums, (bid, src.local), h, effect, depth + 1)
            }
        };
        for blk in &b.blocks {
            for s in &blk.stmts {
                let weft_ir::StmtKind::Assign(q, rv) = &s.kind else {
                    continue;
                };
                if matches!(rv, weft_ir::Rvalue::Ref(src) if is_owner(bid, src)) {
                    return false;
                }
                if !is_owner(bid, q) {
                    continue;
                }
                if !q.proj.is_empty() {
                    return false;
                }
                any = true;
                let ok = match rv {
                    weft_ir::Rvalue::Aggregate(_, ops) => ops.iter().all(&part_ok),
                    weft_ir::Rvalue::Use(op) => part_ok(op),
                    _ => false,
                };
                if !ok {
                    return false;
                }
            }
            if let Some(q) = term_dest(&blk.term.kind).filter(|q| is_owner(bid, q)) {
                if !q.proj.is_empty() || !maker(&blk.term.kind) {
                    return false;
                }
                any = true;
            }
        }
    }
    any
}

/// True if a capture of mode `mode` shares the cell of its variable.
const fn sharing(mode: weft_ir::CaptureMode) -> bool {
    !matches!(
        mode,
        weft_ir::CaptureMode::ByMove | weft_ir::CaptureMode::Cap
    )
}

/// True if a closure shares the cell of local `owner` (a `ByRef`, `Kept` or
/// `Kont` capture of it) and can write the cell (`writes_capture`)
/// (HENV-SHADOW).
fn shares_cell(p: &Program, owner: (BodyId, weft_ir::LocalId)) -> bool {
    p.closures.iter().any(|c| {
        c.captures.iter().enumerate().any(|(k, cap)| {
            sharing(cap.mode)
                && super::alpha::owner_local(p, c.maker, cap.source.local).ok() == Some(owner)
                && writes_capture(p, c, k)
        })
    })
}

/// True if the body of closure `c` (or a body with upvar locals inside it)
/// can write capture `k` of its environment: a write of a place below
/// `env.k`, a reference to such a place, or a closure that captures such a
/// place again and shares its cell.
fn writes_capture(p: &Program, c: &weft_ir::ClosureDecl, k: usize) -> bool {
    let Some(env) = p.body(c.body).and_then(|b| {
        b.locals
            .iter()
            .position(|d| matches!(d.kind, weft_ir::LocalKind::Env))
            .and_then(|i| u32::try_from(i).ok())
            .map(weft_ir::LocalId)
    }) else {
        return true;
    };
    let at_k = |b: BodyId, q: &weft_ir::Place| {
        super::alpha::owner_local(p, b, q.local).ok() == Some((c.body, env))
            && matches!(q.proj.first(), Some(weft_ir::Proj::Field(i)) if i.index() == k)
    };
    let in_bodies = writers(p, c.body).any(|(bid, b)| {
        b.blocks.iter().any(|blk| {
            blk.stmts.iter().any(|s| match &s.kind {
                weft_ir::StmtKind::Assign(q, rv) => {
                    at_k(bid, q) || matches!(rv, weft_ir::Rvalue::Ref(src) if at_k(bid, src))
                }
                _ => false,
            }) || term_dest(&blk.term.kind).is_some_and(|q| at_k(bid, q))
        })
    });
    in_bodies
        || p.closures.iter().any(|d| {
            d.captures
                .iter()
                .any(|cap| sharing(cap.mode) && at_k(d.maker, &cap.source))
        })
}

/// True if the closures that local `l` of body `body` can hold (the local
/// is `closure_only`) capture no value with a function part other than a
/// local with the same property, and no closure shares the cell of the
/// local (`shares_cell`). A closure captures the capability of each local
/// handler that it performs through, but another function value that it
/// captures runs with the handlers where that value was made (HENV-SHADOW).
fn plain_closures(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    body: BodyId,
    l: weft_ir::LocalId,
    depth: usize,
) -> bool {
    if depth > COPY_DEPTH {
        return false;
    }
    let Ok(owner) = super::alpha::owner_local(p, body, l) else {
        return false;
    };
    if shares_cell(p, owner) {
        return false;
    }
    let is_owner = |b: BodyId, q: &weft_ir::Place| {
        super::alpha::owner_local(p, b, q.local).ok() == Some(owner)
    };
    writers(p, owner.0).all(|(bid, b)| {
        b.blocks.iter().all(|blk| {
            blk.stmts.iter().all(|s| match &s.kind {
                weft_ir::StmtKind::Assign(q, rv) if is_owner(bid, q) => match rv {
                    weft_ir::Rvalue::Aggregate(weft_ir::AggKind::Closure(_), ops) => {
                        ops.iter().all(|op| match op {
                            weft_ir::Operand::Const(_) => true,
                            weft_ir::Operand::Copy(src) | weft_ir::Operand::Move(src) => {
                                b.local(src.local)
                                    .is_some_and(|d| !crate::props::ir_has_fns(tys, d.ty))
                                    || (src.proj.is_empty()
                                        && closure_only(p, Some(sums), bid, src.local, 0)
                                        && plain_closures(p, tys, sums, bid, src.local, depth + 1))
                            }
                        })
                    }
                    weft_ir::Rvalue::Use(
                        weft_ir::Operand::Copy(src) | weft_ir::Operand::Move(src),
                    ) => plain_closures(p, tys, sums, bid, src.local, depth + 1),
                    _ => true,
                },
                _ => true,
            })
        })
    })
}

/// True if local `l` of body `body` is a parameter of a function or a
/// closure (also through upvar locals) that no statement and no terminator
/// of the program writes: its value is the value of the call. Only the body
/// of the parameter and the bodies with upvar locals can write it.
fn entry_param(p: &Program, body: BodyId, l: weft_ir::LocalId) -> bool {
    let Ok(owner) = super::alpha::owner_local(p, body, l) else {
        return false;
    };
    let param = p.body(owner.0).is_some_and(|b| {
        matches!(b.kind, BodyKind::Fn(_) | BodyKind::Closure(_))
            && b.local(owner.1)
                .is_some_and(|d| matches!(d.kind, weft_ir::LocalKind::Param(_)))
    });
    if !param {
        return false;
    }
    let writes = |b: BodyId, q: &weft_ir::Place| {
        super::alpha::owner_local(p, b, q.local).ok() == Some(owner)
    };
    !writers(p, owner.0).any(|(bid, b)| {
        b.blocks.iter().any(|blk| {
            blk.stmts.iter().any(|s| match &s.kind {
                weft_ir::StmtKind::Assign(q, _) => writes(bid, q),
                _ => false,
            }) || term_dest(&blk.term.kind).is_some_and(|q| writes(bid, q))
        })
    })
}

/// The most copies of a function value that [`closure_only`] follows.
const COPY_DEPTH: usize = 8;

/// True if local `l` of body `body` can only hold closures: each value that
/// goes into the local (or a local of a parent body that it names) is a new
/// closure or a copy of a local that can only hold closures. With the
/// summaries `sums`, the result of a call of a function whose result can
/// only be closures that call and perform nothing ([`inert`]) counts too
/// (the closure runs with the handlers of the call that made it). A
/// parameter, another result of a terminator or another value can be a
/// function item.
fn closure_only(
    p: &Program,
    sums: Option<&Summaries>,
    body: BodyId,
    l: weft_ir::LocalId,
    depth: usize,
) -> bool {
    if depth > COPY_DEPTH {
        return false;
    }
    let Ok(owner) = super::alpha::owner_local(p, body, l) else {
        return false;
    };
    let is_owner = |b: BodyId, q: &weft_ir::Place| {
        q.proj.is_empty() && super::alpha::owner_local(p, b, q.local).ok() == Some(owner)
    };
    let param = p
        .body(owner.0)
        .and_then(|b| b.local(owner.1))
        .is_none_or(|d| {
            !matches!(
                d.kind,
                weft_ir::LocalKind::User | weft_ir::LocalKind::Temp(_)
            )
        });
    if param {
        return false;
    }
    let mut any = false;
    for (i, b) in p.bodies.iter().enumerate() {
        let bid = BodyId(u32::try_from(i).unwrap_or(u32::MAX));
        for blk in &b.blocks {
            for s in &blk.stmts {
                let weft_ir::StmtKind::Assign(q, rv) = &s.kind else {
                    continue;
                };
                if !is_owner(bid, q) {
                    continue;
                }
                any = true;
                let ok = match rv {
                    weft_ir::Rvalue::Aggregate(weft_ir::AggKind::Closure(_), _) => true,
                    weft_ir::Rvalue::Use(
                        weft_ir::Operand::Copy(src) | weft_ir::Operand::Move(src),
                    ) if src.proj.is_empty() => closure_only(p, sums, bid, src.local, depth + 1),
                    _ => false,
                };
                if !ok {
                    return false;
                }
            }
            if term_dest(&blk.term.kind).is_some_and(|q| is_owner(bid, q)) {
                if !makes_inert(p, sums, &blk.term.kind) {
                    return false;
                }
                any = true;
            }
        }
    }
    any
}

/// True if terminator `t` is a call of a function whose result can only be
/// closures that call and perform nothing ([`inert`]).
fn makes_inert(p: &Program, sums: Option<&Summaries>, t: &TermKind) -> bool {
    let (
        Some(sums),
        TermKind::Call {
            callee: Callee::Fn(f, _),
            ..
        },
    ) = (sums, t)
    else {
        return false;
    };
    sums.get(*f).is_ok_and(|s| {
        !s.ret.fns.is_empty()
            && s.ret.fns.iter().all(|x| match x {
                crate::analysis::summary::RetFn::Made(c) => inert(p, *c),
                _ => false,
            })
    })
}

/// True if the body of closure `c` has no call, no perform and no other
/// terminator that can run code of another body or suspend.
fn inert(p: &Program, c: weft_ir::ClosureId) -> bool {
    p.closures
        .get(c.index())
        .and_then(|d| p.body(d.body))
        .is_some_and(|b| {
            b.blocks.iter().all(|blk| {
                matches!(
                    blk.term.kind,
                    TermKind::Goto(_)
                        | TermKind::Switch { .. }
                        | TermKind::Return
                        | TermKind::UnwindExit
                        | TermKind::Unreachable
                        | TermKind::Assert { .. }
                )
            })
        })
}

/// The destination place of terminator `t`, if it has one.
const fn term_dest(t: &TermKind) -> Option<&weft_ir::Place> {
    match t {
        TermKind::Call { dest, .. }
        | TermKind::Perform { dest, .. }
        | TermKind::Resume { dest, .. }
        | TermKind::Handle { dest, .. }
        | TermKind::Scope { dest, .. }
        | TermKind::Join { dest, .. }
        | TermKind::Fork { dest, .. }
        | TermKind::IterNext { dest, .. } => Some(dest),
        TermKind::Spawn { dest, .. } => dest.as_ref(),
        _ => None,
    }
}

/// True if terminator `t` of body `body` can run a function value: a call
/// of a function value, or a call of a function whose summary runs one or
/// whose arguments can hold one (plan stage F16).
pub fn runs_values(
    p: &Program,
    tys: &TyTable,
    sums: &Summaries,
    body: BodyId,
    t: &TermKind,
) -> bool {
    match t {
        TermKind::Call {
            callee: Callee::Value(_),
            ..
        } => true,
        TermKind::Call {
            callee: Callee::Fn(f, _),
            args,
            ..
        } => {
            if sums.get(*f).map_or(true, |s| !s.runs.is_empty()) {
                return true;
            }
            let Some(b) = p.body(body) else {
                return true;
            };
            args.iter().any(|a| match a {
                weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q) => b
                    .local(q.local)
                    .is_none_or(|d| crate::props::ir_has_fns(tys, d.ty)),
                weft_ir::Operand::Const(_) => false,
            })
        }
        _ => false,
    }
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

/// The number of [`super::nodes::Phase::Task`] nodes of a call for each
/// value that the callee runs as a task (plan stage F19).
pub const TASK_NODES: usize = 4;

/// The number of task nodes of a call for each wait handler (follow-up F19.5).
///
/// The [`super::nodes::Phase::Task`] nodes of a local handler of
/// [`Frames::wait_handlers`]: the start of the task that stands for the
/// tasks that can run while the clause runs, the node of the reads of the
/// clause, where it ends; the start of the task of the changes of the
/// clause, and the node of the reads of the tasks, where it ends
/// (`templates::WaitTask`).
pub const WAIT_NODES: usize = 4;

/// The entries of the part `runs` of summary `s` that the body runs as a
/// task, in order: a run node applies each at its task nodes.
pub fn task_runs(
    s: &crate::analysis::Summary,
) -> impl Iterator<Item = (usize, &crate::analysis::summary::Run)> {
    s.runs
        .iter()
        .enumerate()
        .filter(|(_, r)| r.task && !r.capture)
}

/// True if a perform through `cap` of operation `op` in body `body` goes to
/// a handler of a caller, as `templates::perform` takes it (stage R0h).
///
/// It is a perform through the row, an operation that a local handler with no
/// clause passes on, and a captured capability whose handlers pass it on.
pub fn perform_to_caller(
    p: &Program,
    tys: &TyTable,
    body: BodyId,
    cap: &CapOperand,
    op: weft_ir::OpIdx,
) -> bool {
    match cap {
        CapOperand::Row(_) => true,
        CapOperand::Local(c) => {
            if clause::passes_to_caller(p, body, c, op).is_some() {
                return true;
            }
            if clause::passes_to_capture(p, body, c, op).is_some() {
                return false;
            }
            let Some((k, _)) = clause::captured_cap(p, tys, body, c) else {
                return false;
            };
            super::alpha::unit_closure(p, body)
                .and_then(|cb| p.closure_of(cb))
                .and_then(|(cl, _)| clause::capture_handler(p, cl, k))
                .and_then(|h| clause::serving(p, h, op))
                .is_none()
        }
    }
}

/// The arguments of a call of a function value that can hold a function
/// value (stage R0f): each one has [`TASK_NODES`] task nodes, in order. A
/// place with a projection counts.
pub fn value_task_args(
    p: &Program,
    tys: &TyTable,
    body: BodyId,
    args: &[weft_ir::Operand],
) -> Vec<u32> {
    let decl = |q: &weft_ir::Place| {
        p.bodies
            .get(body.index())
            .and_then(|b| b.locals.get(q.local.index()))
            .map(|d| d.ty)
    };
    args.iter()
        .enumerate()
        .filter(|(_, op)| match op {
            weft_ir::Operand::Const(_) => false,
            weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q) => {
                !q.proj.is_empty() || decl(q).is_none_or(|t| crate::props::ir_has_fns(tys, t))
            }
        })
        .map(|(i, _)| u32::try_from(i).unwrap_or(u32::MAX))
        .collect()
}

/// The destinations of each terminator of some bodies.
#[derive(Clone, Debug, Default)]
pub struct Frames {
    /// The destinations of the terminator of each block.
    by: BTreeMap<(BodyId, BlockId), Vec<Dest>>,
    /// The local handlers whose clauses the terminator of each block runs
    /// ([`clause_handlers`]).
    runs: BTreeMap<(BodyId, BlockId), Vec<HandlerId>>,
    /// The handlers whose clauses can run more than once in one run of the
    /// handled body ([`Frames::runs_twice`]).
    twice: std::collections::BTreeSet<HandlerId>,
    /// The nodes of the handled body of each `multi` handler that run a
    /// clause that can resume more than once ([`Frames::reentries`]).
    reentry: BTreeMap<HandlerId, Vec<(BodyId, BlockId)>>,
    /// The number of [`super::nodes::Phase::Task`] nodes of the call of
    /// each block whose callee runs a function value as a task (plan stage
    /// F19, `docs/ir.md` 6.7).
    tasks: BTreeMap<(BodyId, BlockId), u32>,
    /// The local handlers whose clauses the call of each block runs while a
    /// task of the call can run (follow-up F19.5): [`WAIT_NODES`] more
    /// [`super::nodes::Phase::Task`] nodes for each, after the nodes of
    /// `tasks` ([`Frames::wait_handlers`]).
    waits: BTreeMap<(BodyId, BlockId), Vec<HandlerId>>,
    /// The performs through the capability of a local handler whose clause
    /// has no `resume` (plan stage F19): they do not go on to their next
    /// block (`fail` of a local `Fail` handler).
    noreturn: std::collections::BTreeSet<(BodyId, BlockId)>,
}

impl Frames {
    /// The number of [`super::nodes::Phase::Task`] nodes of the call of
    /// block `block` of body `body`.
    pub fn task_nodes(&self, body: BodyId, block: BlockId) -> u32 {
        let waits = self.waits.get(&(body, block)).map_or(0, Vec::len);
        let waits = u32::try_from(waits.saturating_mul(WAIT_NODES)).unwrap_or(u32::MAX);
        self.run_task_nodes(body, block).saturating_add(waits)
    }

    /// The number of [`super::nodes::Phase::Task`] nodes of the call of
    /// block `block` of body `body` for the values that the callee runs as
    /// tasks: the first nodes of [`Frames::task_nodes`].
    pub fn run_task_nodes(&self, body: BodyId, block: BlockId) -> u32 {
        self.tasks.get(&(body, block)).copied().unwrap_or(0)
    }

    /// The local handlers whose clauses the call of block `block` of body
    /// `body` runs while a task of the call can run (follow-up F19.5, issue
    /// #50). The call has [`WAIT_NODES`] [`super::nodes::Phase::Task`]
    /// nodes for each, in order, after the nodes of
    /// [`Frames::run_task_nodes`] (`templates::WaitTask`).
    pub fn wait_handlers(&self, body: BodyId, block: BlockId) -> &[HandlerId] {
        self.waits.get(&(body, block)).map_or(&[], Vec::as_slice)
    }

    /// True if the terminator of block `block` of body `body` is a perform
    /// whose clause has no `resume`: it has no normal successor.
    pub fn no_return(&self, body: BodyId, block: BlockId) -> bool {
        self.noreturn.contains(&(body, block))
    }

    /// The destinations of each terminator of body `body`, with the
    /// summaries `sums` of the callees ([`destinations`]).
    pub fn of_body(p: &Program, tys: &TyTable, sums: &Summaries, body: BodyId) -> Self {
        let mut f = Self::default();
        f.add(body, p, |t| destinations(p, tys, sums, body, t));
        f.add_tasks(p, tys, sums, &[body]);
        f
    }

    /// The [`super::nodes::Phase::Task`] nodes of each call of the bodies
    /// `bodies` whose callee runs a function value as a task: four for each
    /// such entry of the part `runs` of the summary of the callee (the
    /// start of the task, its second start, the code that runs at the same
    /// time, its end; plan stage F19, `docs/ir.md` 6.7). Then
    /// [`WAIT_NODES`] for each local handler of [`Frames::wait_handlers`]
    /// (follow-up F19.5).
    fn add_tasks(&mut self, p: &Program, tys: &TyTable, sums: &Summaries, bodies: &[BodyId]) {
        for &body in bodies {
            let Some(b) = p.bodies.get(body.index()) else {
                continue;
            };
            for (i, blk) in b.blocks.iter().enumerate() {
                if blk.cleanup {
                    continue;
                }
                let block = BlockId(u32::try_from(i).unwrap_or(u32::MAX));
                if crate::analysis::clause::perform_never_returns(p, body, &blk.term.kind) {
                    self.noreturn.insert((body, block));
                }
                // A call that runs a clause of a local handler while a task
                // of the call can run: a task of the callee (part `waits`),
                // a task that a value of the call starts (part `runs`), or a
                // value of a function value (follow-up F19.5).
                let waits = match &blk.term.kind {
                    TermKind::Call {
                        callee: Callee::Fn(f, _),
                        ..
                    } => sums
                        .get(*f)
                        .is_ok_and(|s| !s.waits.is_empty() || !s.runs.is_empty()),
                    TermKind::Call { .. } => true,
                    _ => false,
                };
                if waits {
                    let hs = clause_handlers(p, tys, sums, body, &blk.term.kind);
                    if !hs.is_empty() {
                        self.waits.insert((body, block), hs);
                    }
                }
                let k = match &blk.term.kind {
                    TermKind::Call {
                        callee: Callee::Fn(f, _),
                        ..
                    } => sums.get(*f).map_or(0, |s| task_runs(s).count()),
                    TermKind::Call { args, .. } => value_task_args(p, tys, body, args).len(),
                    // A perform of an operation of a handler of a caller: the
                    // code of the clause can run a function value of an
                    // argument as a task (stage R0h).
                    TermKind::Perform { cap, op, args, .. }
                        if perform_to_caller(p, tys, body, cap, *op) =>
                    {
                        value_task_args(p, tys, body, args).len()
                    }
                    _ => continue,
                };
                if k > 0 {
                    let n = u32::try_from(k.saturating_mul(TASK_NODES)).unwrap_or(u32::MAX);
                    self.tasks.insert((body, block), n);
                }
            }
        }
    }

    /// The destinations of each terminator of the bodies `bodies` of a
    /// component (plan stage F14). A `handle` aborts where an abort of its
    /// handled body goes past its handler: the handled body splices into
    /// the site, so its cleanup chain goes on in the cleanup chain of the
    /// site (`docs/ir.md` 6.5). A `handle` whose handled body cannot abort
    /// past the handler has no abort edge.
    pub fn of_bodies(p: &Program, tys: &TyTable, sums: &Summaries, bodies: &[BodyId]) -> Self {
        let mut f = Self::default();
        // A handled body has a higher id than its site: the destinations of
        // its terminators are known before the `handle`.
        let mut order: Vec<BodyId> = bodies.to_vec();
        order.sort();
        order.dedup();
        for &body in order.iter().rev() {
            let Some(b) = p.bodies.get(body.index()) else {
                continue;
            };
            for (i, blk) in b.blocks.iter().enumerate() {
                if blk.cleanup {
                    continue;
                }
                let block = BlockId(u32::try_from(i).unwrap_or(u32::MAX));
                let ds = match &blk.term.kind {
                    TermKind::Handle {
                        handler, unwind, ..
                    } => {
                        if unwind.is_none() {
                            Vec::new()
                        } else {
                            f.past_handler(p, *handler)
                        }
                    }
                    // A `scope` aborts where an abort of its scope body goes,
                    // and past the function (a cancel, plan stage F18).
                    TermKind::Scope { scope, unwind, .. } => {
                        if unwind.is_none() {
                            Vec::new()
                        } else {
                            f.past_scope(p, *scope)
                        }
                    }
                    t => {
                        let hs = clause_handlers(p, tys, sums, body, t);
                        if !hs.is_empty() {
                            f.runs.insert((body, block), hs);
                        }
                        destinations(p, tys, sums, body, t)
                    }
                };
                if !ds.is_empty() {
                    f.by.insert((body, block), ds);
                }
            }
        }
        f.add_tasks(p, tys, sums, &order);
        f.clause_aborts(p, &order);
        f.twice = f.twice_of(p);
        for (&(body, block), hs) in &f.runs {
            for &h in hs {
                let hb = p.handlers.get(h.index()).map(|d| d.handled);
                if hb.is_some_and(|hb| crate::analysis::clause::spliced_into(p, body, hb))
                    && crate::analysis::clause::multi_twice(p, h)
                {
                    f.reentry.entry(h).or_default().push((body, block));
                }
            }
        }
        f
    }

    /// The nodes of the handled body of handler `h` that run a clause that
    /// can resume more than once (a `multi` operation, plan stage F16): a
    /// later `resume` runs the code after each of them again. The fact
    /// generator links `Post` of the `handle` to the `Copy` node of each
    /// (the re-entry edges, `docs/ir.md` 6.5).
    pub fn reentries(&self, h: HandlerId) -> &[(BodyId, BlockId)] {
        self.reentry.get(&h).map_or(&[], Vec::as_slice)
    }

    /// The handled body of the outermost local handler whose later `resume`
    /// runs the terminator of block `block` of body `body` again
    /// ([`Self::reentries`]): the frames up to it are copied.
    pub fn reentry_root(&self, p: &Program, body: BodyId, block: BlockId) -> Option<BodyId> {
        self.reentry
            .iter()
            .filter(|(_, v)| v.contains(&(body, block)))
            .filter_map(|(h, _)| p.handlers.get(h.index()).map(|d| d.handled))
            .min()
    }

    /// True if a clause of handler `h` can run more than once in one run
    /// of its handled body: the code of each run after its `resume` runs at
    /// the end of the handled body, so `Post` runs that code once for each
    /// run (a cycle through a `Copy` node of the `handle`, plan stages F15
    /// and F16).
    pub fn runs_twice(&self, h: HandlerId) -> bool {
        self.twice.contains(&h)
    }

    /// The handlers whose clauses can run more than once in one run of the
    /// handled body: two nodes run a clause of the handler, or one node in
    /// a cycle of the handled body (also through the `handle`s on the way,
    /// [`run_weight`]), or one node in a clause.
    fn twice_of(&self, p: &Program) -> std::collections::BTreeSet<HandlerId> {
        let mut by: BTreeMap<HandlerId, Vec<(BodyId, BlockId)>> = BTreeMap::new();
        for (k, hs) in &self.runs {
            for &h in hs {
                let at = by.entry(h).or_default();
                if at.last() != Some(k) {
                    at.push(*k);
                }
            }
        }
        let mut w = Weights {
            p,
            by,
            cyc: BTreeMap::new(),
            count: BTreeMap::new(),
            handles: BTreeMap::new(),
        };
        let hs: std::collections::BTreeSet<HandlerId> =
            self.runs.values().flatten().copied().collect();
        hs.into_iter().filter(|&h| w.count(h, 0) > 1).collect()
    }

    /// Adds the aborts of the clauses to the nodes that run them. A clause
    /// can abort past its handler: to a handler outside the clause, or past
    /// the function. The abort starts at the node of the handled body that
    /// runs the clause (a `perform`, or a call that performs), and the
    /// frames of the handled body unwind too. A `handle` then gets the new
    /// destinations of its handled body. The loop stops when nothing
    /// changes (one round for each level of nesting).
    fn clause_aborts(&mut self, p: &Program, order: &[BodyId]) {
        for _ in 0..=order.len() {
            let mut changed = false;
            for &body in order.iter().rev() {
                let Some(b) = p.bodies.get(body.index()) else {
                    continue;
                };
                for (i, blk) in b.blocks.iter().enumerate() {
                    if blk.cleanup {
                        continue;
                    }
                    let block = BlockId(u32::try_from(i).unwrap_or(u32::MAX));
                    let old = self.dests(body, block).to_vec();
                    let mut ds = old.clone();
                    match &blk.term.kind {
                        TermKind::Handle {
                            handler,
                            unwind: Some(_),
                            ..
                        } => ds.extend(self.past_handler(p, *handler)),
                        TermKind::Perform { .. } | TermKind::Call { .. } => {
                            let hs = self.runs.get(&(body, block)).cloned().unwrap_or_default();
                            for h in hs {
                                ds.extend(self.past_clauses(p, h));
                            }
                        }
                        _ => {}
                    }
                    ds.sort();
                    ds.dedup();
                    if ds != old {
                        self.by.insert((body, block), ds);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// The destinations of the aborts of the clauses of handler `h` that go
    /// past the clause: an abort to a handler outside the clause, or past
    /// the function. The abort of a `resume` is an abort of the handled
    /// body: the nodes of the handled body have it.
    fn past_clauses(&self, p: &Program, h: HandlerId) -> Vec<Dest> {
        let Some(hd) = p.handlers.get(h.index()) else {
            return vec![Dest::Past];
        };
        let mut out = Vec::new();
        for &(_, c) in &hd.clauses {
            let Some(cb) = p.bodies.get(c.index()) else {
                continue;
            };
            for (i, blk) in cb.blocks.iter().enumerate() {
                if blk.cleanup || matches!(blk.term.kind, TermKind::Resume { .. }) {
                    continue;
                }
                let block = BlockId(u32::try_from(i).unwrap_or(u32::MAX));
                out.extend(self.dests(c, block).iter().copied().filter(|d| {
                    match d {
                        Dest::Past => true,
                        Dest::Handler { handler, .. } => {
                            *handler != h
                                && p.handlers
                                    .get(handler.index())
                                    .is_none_or(|x| !crate::analysis::clause::inside(p, x.site, c))
                        }
                    }
                }));
            }
        }
        out
    }

    /// The handled bodies that an abort of a re-run of the handled body of
    /// handler `h` unwinds (plan stage F16): a `resume` of a clause of `h`
    /// after the first one runs the rest of the handled body again, so the
    /// `Post` node of the `handle` can abort where the handled body can. An
    /// abort to `h` unwinds the handled body of `h`, an abort to an outer
    /// local handler the handled bodies up to it. None if an abort can go
    /// past the function (no variable is spared).
    pub fn rerun_spares(&self, p: &Program, h: HandlerId) -> Option<Vec<BodyId>> {
        let mut out = vec![p.handlers.get(h.index())?.handled];
        for d in self.past_handler(p, h) {
            match d {
                Dest::Past => return None,
                Dest::Handler { handler, .. } => out.push(p.handlers.get(handler.index())?.handled),
            }
        }
        out.sort();
        out.dedup();
        Some(out)
    }

    /// The destinations of the aborts of the handled body of handler `h`
    /// (and of the bodies that it splices) that go past `h`.
    fn past_handler(&self, p: &Program, h: HandlerId) -> Vec<Dest> {
        let Some(hb) = p.handlers.get(h.index()).map(|d| d.handled) else {
            return vec![Dest::Past];
        };
        let mut out: Vec<Dest> = self
            .by
            .range((hb, BlockId(0))..=(hb, BlockId(u32::MAX)))
            .flat_map(|(_, ds)| ds.iter().copied())
            .filter(|d| !matches!(d, Dest::Handler { handler, .. } if *handler == h))
            .collect();
        out.sort();
        out.dedup();
        out
    }

    /// The destinations of the abort of the scope body of scope `k`: each
    /// destination of a terminator of the scope body, and past the
    /// function (plan stage F18).
    fn past_scope(&self, p: &Program, k: weft_ir::ScopeId) -> Vec<Dest> {
        let Some(sb) = p.scopes.get(k.index()).map(|d| d.body) else {
            return vec![Dest::Past];
        };
        let mut out: Vec<Dest> = self
            .by
            .range((sb, BlockId(0))..=(sb, BlockId(u32::MAX)))
            .flat_map(|(_, ds)| ds.iter().copied())
            .collect();
        out.push(Dest::Past);
        out.sort();
        out.dedup();
        out
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

/// The blocks of body `b` that are in a cycle of its normal edges.
///
/// A block is in a cycle if its strongly connected component has more than
/// one block, or if it is its own successor. The components come from one
/// pass of Tarjan's algorithm (stage C1.4: a walk from each block was
/// quadratic in a body with many blocks, `s5/h4000.wf`).
fn cyclic(b: &weft_ir::Body) -> std::collections::BTreeSet<BlockId> {
    let n = b.blocks.len();
    let succ: Vec<Vec<usize>> = b
        .blocks
        .iter()
        .map(|x| {
            x.term
                .kind
                .normal_successors()
                .into_iter()
                .map(BlockId::index)
                .filter(|&j| j < n)
                .collect()
        })
        .collect();
    cyclic_of(&succ)
        .into_iter()
        .map(|w| BlockId(u32::try_from(w).unwrap_or(u32::MAX)))
        .collect()
}

/// The nodes of the graph `succ` (the successors of each node) that are in
/// a cycle ([`cyclic`]).
fn cyclic_of(succ: &[Vec<usize>]) -> std::collections::BTreeSet<usize> {
    let n = succ.len();
    let mut out = std::collections::BTreeSet::new();
    let none = usize::MAX;
    let mut index = vec![none; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next = 0usize;
    for root in 0..n {
        if index.get(root).copied() != Some(none) {
            continue;
        }
        // The frames of the walk: a block and the index of its next edge.
        let mut walk: Vec<(usize, usize)> = vec![(root, 0)];
        if let (Some(i), Some(l), Some(o)) = (
            index.get_mut(root),
            low.get_mut(root),
            on_stack.get_mut(root),
        ) {
            *i = next;
            *l = next;
            *o = true;
        }
        next += 1;
        stack.push(root);
        while let Some(&(v, e)) = walk.last() {
            if let Some(&w) = edges_of(succ, v).get(e) {
                if let Some(top) = walk.last_mut() {
                    top.1 += 1;
                }
                let wi = index.get(w).copied().unwrap_or(none);
                if wi == none {
                    if let (Some(i), Some(l), Some(o)) =
                        (index.get_mut(w), low.get_mut(w), on_stack.get_mut(w))
                    {
                        *i = next;
                        *l = next;
                        *o = true;
                    }
                    next += 1;
                    stack.push(w);
                    walk.push((w, 0));
                } else if on_stack.get(w).copied().unwrap_or(false) {
                    let lv = low.get(v).copied().unwrap_or(0).min(wi);
                    if let Some(l) = low.get_mut(v) {
                        *l = lv;
                    }
                }
                continue;
            }
            walk.pop();
            let lv = low.get(v).copied().unwrap_or(0);
            if let Some(&(u, _)) = walk.last() {
                let lu = low.get(u).copied().unwrap_or(0).min(lv);
                if let Some(l) = low.get_mut(u) {
                    *l = lu;
                }
            }
            if Some(lv) == index.get(v).copied() {
                let mut comp = Vec::new();
                while let Some(w) = stack.pop() {
                    if let Some(o) = on_stack.get_mut(w) {
                        *o = false;
                    }
                    comp.push(w);
                    if w == v {
                        break;
                    }
                }
                let looped = comp.len() > 1 || edges_of(succ, v).contains(&v);
                if looped {
                    out.extend(comp);
                }
            }
        }
    }
    out
}

/// The successors of block `v` in `succ`.
fn edges_of(succ: &[Vec<usize>], v: usize) -> &[usize] {
    succ.get(v).map_or(&[], Vec::as_slice)
}

/// The number of runs of the clauses of each handler in one run of its
/// handled body, capped at 2 ([`Frames::runs_twice`]).
struct Weights<'a> {
    /// The program.
    p: &'a Program,
    /// The nodes that run a clause of each handler, in the order of
    /// [`Frames::runs`].
    by: BTreeMap<HandlerId, Vec<(BodyId, BlockId)>>,
    /// The cyclic blocks of each body.
    cyc: BTreeMap<BodyId, std::collections::BTreeSet<BlockId>>,
    /// The count of each handler, once known.
    count: BTreeMap<HandlerId, u32>,
    /// The first block of each body (not a cleanup block) whose terminator
    /// is the `handle` of each handler, once known.
    handles: BTreeMap<BodyId, BTreeMap<HandlerId, usize>>,
}

impl Weights<'_> {
    /// How many times (at most 2) a clause of handler `h` can run in one
    /// run of its handled body: the sum over the nodes that run it.
    /// `depth` bounds the walk through the clauses of other handlers.
    fn count(&mut self, h: HandlerId, depth: usize) -> u32 {
        if let Some(&c) = self.count.get(&h) {
            return c;
        }
        let Some(hb) = self.p.handlers.get(h.index()).map(|d| d.handled) else {
            return 2;
        };
        let nodes: Vec<(BodyId, BlockId)> = self.by.get(&h).cloned().unwrap_or_default();
        let mut c = 0u32;
        for at in nodes {
            c = c.saturating_add(self.weight(at, hb, depth));
            if c > 1 {
                break;
            }
        }
        let c = c.min(2);
        self.count.insert(h, c);
        c
    }

    /// How many times (at most 2) the node at (`body`, `block`) can run in
    /// one run of the handled body `hb`: 2 if it is in a cycle of its body,
    /// or the `handle` of a handled body on the way to `hb` is; in a clause
    /// of another handler on the way, the count of that handler; else 1.
    fn weight(&mut self, (body, block): (BodyId, BlockId), hb: BodyId, depth: usize) -> u32 {
        let p = self.p;
        let (mut b, mut blk) = (body, block);
        let mut times = 1u32;
        for _ in 0..=p.bodies.len() {
            let Some(d) = p.bodies.get(b.index()) else {
                return 2;
            };
            let cyclic = self.cyc.entry(b).or_insert_with(|| cyclic(d));
            if cyclic.contains(&blk) {
                return 2;
            }
            if b == hb {
                return times.min(2);
            }
            let (h2, site) = match (d.kind, d.parent) {
                (BodyKind::Handled(h2), Some(site)) => (h2, site),
                (BodyKind::Clause(h2, _), _) if depth < p.handlers.len() => {
                    // The clause of handler `h2` runs once for each run of
                    // it; its handle is in the handled body of `hb` or above.
                    times = times.saturating_mul(self.count(h2, depth + 1));
                    if times > 1 {
                        return 2;
                    }
                    let Some(site) = p.handlers.get(h2.index()).map(|x| x.site) else {
                        return 2;
                    };
                    (h2, site)
                }
                _ => return 2,
            };
            let Some(sb) = p.bodies.get(site.index()) else {
                return 2;
            };
            let at = self.handles.entry(site).or_insert_with(|| {
                let mut m: BTreeMap<HandlerId, usize> = BTreeMap::new();
                for (i, x) in sb.blocks.iter().enumerate() {
                    if let (false, TermKind::Handle { handler, .. }) = (x.cleanup, &x.term.kind) {
                        m.entry(*handler).or_insert(i);
                    }
                }
                m
            });
            let Some(&i) = at.get(&h2) else {
                return 2;
            };
            b = site;
            blk = BlockId(u32::try_from(i).unwrap_or(u32::MAX));
        }
        2
    }
}

#[cfg(test)]
mod tests {
    use super::cyclic_of;

    /// The nodes in a cycle, with a walk from each node (the first form of
    /// [`super::cyclic`]).
    fn cyclic_slow(succ: &[Vec<usize>]) -> std::collections::BTreeSet<usize> {
        let mut out = std::collections::BTreeSet::new();
        for start in 0..succ.len() {
            let mut seen = vec![false; succ.len()];
            let mut work: Vec<usize> = succ[start].clone();
            while let Some(x) = work.pop() {
                if x == start {
                    out.insert(start);
                    break;
                }
                if std::mem::replace(&mut seen[x], true) {
                    continue;
                }
                work.extend(succ[x].iter().copied());
            }
        }
        out
    }

    /// Tarjan's components give the nodes of the walks on random graphs.
    #[test]
    fn cyclic_nodes_are_the_nodes_of_the_walks() {
        let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
        let mut next = |m: u64| {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            usize::try_from((seed >> 33) % m).unwrap_or(0)
        };
        for _ in 0..500 {
            let n = 1 + next(12);
            let edges = next(30);
            let mut succ = vec![Vec::new(); n];
            for _ in 0..edges {
                let a = next(n as u64);
                let b = next(n as u64);
                succ[a].push(b);
            }
            assert_eq!(cyclic_of(&succ), cyclic_slow(&succ), "{succ:?}");
        }
    }
}
