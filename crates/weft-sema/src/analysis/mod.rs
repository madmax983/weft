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
//! of its target, and visits the target again if that state changed. At a
//! loop head (the target of a back edge) the join widens ([`widen`], stage
//! F10), so the states of a loop are stable after a finite number of
//! visits.
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
pub mod clause;
pub mod domain;
pub mod sig;
pub mod summarize;
pub mod summary;
pub mod tasks;
pub mod transfer;
pub mod unknown;
pub mod widen;

use std::collections::BTreeSet;

use weft_ir::{BlockId, BodyId};

pub use domain::{AbsVal, FnVal, Key, PathStep, State, Tree};
pub use summary::{Summaries, Summary};
pub use transfer::Cx;

use crate::factgen::alpha::AlphaError;

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
/// edge the state after it. A terminator that runs a clause gives its
/// `unwind` edge the state of the clause where it aborts (plan stage F15):
/// a `perform` through a local capability the states of the clause alone,
/// a call that runs clauses the join of both.
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
    let before = term.unwind().map(|u| (u, st.clone()));
    cx.hx.abort_edge = None;
    cx.hx.no_normal = false;
    transfer::term(cx, body, blk_id, &mut st, term)?;
    // A `scope` whose scope body stops at a resume point of a clause on
    // each path (plan stage R0z Z5): no normal successor in this run.
    let stopped = std::mem::take(&mut cx.hx.no_normal);
    // A node that runs a clause that can resume more than once: a later
    // `resume` runs the code after it again (plan stage F16).
    clause::note_reentry(cx, body, blk_id, term, &st);
    // A node of a clause that can wait at a `multi` operation of a caller:
    // a later `resume` goes on with the heap after the previous run (stage
    // R0k-c2, E5).
    if let Some(h) = cx.hx.row_heap.get(&(body, blk_id)) {
        st.join_heap(h);
    }
    // A node of a clause inside the handled body of a local `multi`
    // handler (C8): the locals outside the handled body as at the later
    // `resume`.
    if let Some((s, hb)) = cx.hx.row_join.get(&(body, blk_id)) {
        let p = cx.p;
        let hb = *hb;
        st.join_values_but(s, &|b| clause::inside(p, b, hb));
        st.join_heap(s);
    }
    // A terminator that runs a clause: the abort edge gets the state of the
    // clause where it aborts (plan stage F15, `clause::AbortEdge`).
    let hook = cx.hx.abort_edge.take();
    if let Some((u, mut s)) = before {
        match hook {
            Some(clause::AbortEdge::Replace(a)) => s = a,
            Some(clause::AbortEdge::Join(a)) => {
                s.join(&a);
            }
            None => {}
        }
        // A task handle that the terminator takes leaves the values on the
        // abort edge too, unless the callee joins it on each path of an
        // abort (follow-up F19.3, E-1).
        transfer::lose_given(cx, body, &mut s, term, true);
        clause::note_past(cx, body, term, &s);
        out.push((u, s));
    }
    // A test of a dispatch (plan stage R0z Z6): the edge to the arm gets the
    // state with only the closures of the arm in the value, the next edge
    // the state with the other closures. An edge with no closure left gets
    // no state: the code there does not run.
    if let Some(d) = cx.p.dispatch_at(body, blk_id) {
        if let Some(i) = d.arms.iter().position(|a| a.test == blk_id) {
            let arm = d.arms.get(i).cloned();
            let next = d.arms.get(i + 1).map_or(d.miss, |n| n.test);
            if let (Some(arm), false) = (arm, stopped) {
                cx.hx.dispatch_reached.insert((body, blk_id));
                if i == 0 {
                    let all: Vec<weft_ir::ClosureId> = d
                        .arms
                        .iter()
                        .flat_map(|a| a.closures.iter().copied())
                        .collect();
                    if !transfer::dispatch_known(cx.p, body, &st, &d.value, &|c| all.contains(&c))?
                    {
                        cx.hx.dispatch_miss.insert((body, blk_id));
                    }
                }
                let value = d.value.clone();
                let into = transfer::dispatch_cut(cx.p, body, &st, &value, &|c| {
                    arm.closures.contains(&c)
                })?;
                if let Some(s) = into {
                    cx.hx.dispatch_live.insert((body, arm.entry));
                    out.push((arm.entry, s));
                }
                if let Some(s) = transfer::dispatch_cut(cx.p, body, &st, &value, &|c| {
                    !arm.closures.contains(&c)
                })? {
                    out.push((next, s));
                }
                return Ok(out);
            }
        }
    }
    // A perform whose clause has no `resume` does not go on (plan stage
    // F19).
    if !stopped && !clause::perform_never_returns(cx.p, body, term) {
        for s in term.normal_successors() {
            out.push((s, st.clone()));
        }
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
/// loop head needs more than [`widen::visit_bound`] visits (a bug of the
/// widening).
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

/// What [`run_from`] gives besides the states.
#[derive(Clone, Debug, Default)]
pub struct Ends {
    /// The state after the statements of each `Resume` block (before its
    /// terminator) that the run stopped at (plan stage F14: the resume
    /// points of a clause).
    pub resumes: std::collections::BTreeMap<BlockId, State>,
    /// The state after the statements of each `Return` block of the normal
    /// path (before its terminator).
    pub returns: std::collections::BTreeMap<BlockId, State>,
    /// The state after the statements of each `UnwindExit` block: an abort
    /// that leaves the body (plan stage F15).
    pub unwinds: std::collections::BTreeMap<BlockId, State>,
}

/// How [`run_from`] runs.
#[derive(Clone, Copy, Debug, Default)]
pub struct Mode {
    /// Keep the state of each block, not only of the join blocks.
    pub all: bool,
    /// A `Resume` terminator ends the run: its state goes to
    /// [`Ends::resumes`], and its successors get no state (the code of a
    /// clause before its first resume point, plan stage F14).
    pub stop_at_resume: bool,
}

/// The number of runs of a body that the analysis does to find the states
/// of the re-runs after a `multi` operation of a caller (OL-R2a, plan stage
/// F16).
const ROW_ROUNDS: usize = 8;

/// [`run`], with `all`: keep the state of each block.
///
/// A node of the body that can wait at a `multi` operation of a handler of
/// a caller (`crate::factgen::frames::row_multi`, OL-R2a) runs the code
/// after it again for each later `resume`, from a copy of the frames of the
/// body: the run goes on from the block after the node with the state of
/// the node and the heap slots at the `Return`s of the body, until these
/// states do not change. The state of each re-entry goes to
/// `clause::Handlers::reentry` (the `Copy` node of the facts).
///
/// # Errors
///
/// The errors of [`run_from`], and [`AlphaError::Later`] for such a node in
/// a handled body or a clause (not in scope).
fn run_with(cx: &mut Cx<'_>, body: BodyId, init: State, all: bool) -> Result<States, AlphaError> {
    let p = cx.p;
    let b = p
        .bodies
        .get(body.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no body b{}", body.0)))?;
    let mode = Mode {
        all,
        stop_at_resume: false,
    };
    let saved = std::mem::take(&mut cx.hx.rows);
    let r = run_rows(cx, (body, b), &[(b.entry, init)], mode);
    cx.hx.rows = saved;
    r
}

/// The runs of [`run_with`].
///
/// A node of a clause that runs below the body (a clause of a handler of
/// the body, or a clause inside such a clause:
/// `crate::factgen::handlers::clause_chain`) that can wait at a `multi`
/// operation of a handler of a caller (stage R0k-c2) gets the heap slots of
/// the `Return`s of the body in `clause::Handlers::row_heap`: a later
/// `resume` runs the rest of the clause again after the previous run (E5).
/// The run of the clause body itself (its facts) runs again from the block
/// after each such node of the clause, as the body does for its own nodes.
fn run_rows(
    cx: &mut Cx<'_>,
    (body, b): (BodyId, &weft_ir::Body),
    first: &[(BlockId, State)],
    mode: Mode,
) -> Result<States, AlphaError> {
    let p = cx.p;
    let mut again: std::collections::BTreeMap<BlockId, State> = std::collections::BTreeMap::new();
    let root = matches!(
        b.kind,
        weft_ir::BodyKind::Fn(_) | weft_ir::BodyKind::Test(_) | weft_ir::BodyKind::Closure(_)
    );
    let in_chain = |rb: BodyId| {
        crate::factgen::handlers::clause_chain(p, rb).is_some_and(|c| c.contains(&body))
    };
    let clause = matches!(b.kind, weft_ir::BodyKind::Clause(..)) && in_chain(body);
    for round in 0..=ROW_ROUNDS {
        let mut seeds = first.to_vec();
        seeds.extend(again.iter().map(|(x, s)| (*x, s.clone())));
        let (states, ends) = run_from(cx, body, seeds, mode)?;
        let rows = std::mem::take(&mut cx.hx.rows);
        if rows.is_empty() {
            return Ok(states);
        }
        // The nodes of the body and of the handled bodies that splice into
        // it (`own`), and the nodes of the clauses that run below the body
        // (`below`). Any other node: not in scope.
        let mut own = Vec::new();
        let mut below = Vec::new();
        for r in rows {
            // A run of a parameter of the clause where the run of the
            // function, with the values that the nodes that run the clause
            // give, finds no row (plan stage R0z Z7, [`code_row`]): no row.
            let in_clause = crate::factgen::handlers::clause_chain(p, r.0).is_some();
            if clause
                && crate::factgen::handlers::splice_root(p, r.0) == body
                && code_row(p, cx.tys, cx.sums, cx.hx, (r.0, r.1))
            {
                continue;
            }
            // A node of a clause that only the analysis finds (a run of a
            // function value that can resume more than once,
            // `clause::Handlers::dyn_rows`): the facts have no re-entry of
            // the nodes that run the clause for it (they come from the
            // nodes of `frames::row_multi` before the analysis). This run is
            // pending. The fact generator then runs the analysis of the
            // program again with the node as a row of its clause (plan stage
            // R0z Z7, `crate::factgen::frames::ClauseDynRows`), and in that
            // run it is a row before the analysis.
            if in_clause && !static_row(cx, r.0, r.1) {
                crate::factgen::frames::note_clause_dyn_row(r.0, r.1);
                if env_can_hold_refs(cx, (r.0, r.1), &r.3, clause) {
                    crate::factgen::frames::refuse_clause_dyn_row(r.0, r.1);
                }
                note_row_pending();
                return Ok(states);
            }
            if crate::factgen::handlers::splice_root(p, r.0) == body {
                own.push(r);
            } else if (root || clause) && in_chain(r.0) {
                below.push(r);
            } else {
                note_row_pending();
                return Ok(states);
            }
        }
        if !root && !clause && !own.is_empty() {
            note_row_pending();
            return Ok(states);
        }
        let mut ret: Option<State> = None;
        if root {
            for s in ends.returns.values() {
                if let Some(r) = &mut ret {
                    r.join_heap(s);
                } else {
                    let mut h = State::new();
                    h.join_heap(s);
                    ret = Some(h);
                }
            }
        }
        let mut changed = false;
        // The nodes of the clauses below the body: the heap at the `Return`s
        // of the body joins at their normal edges (`super::edges`), and at
        // their `Copy` nodes.
        if root {
            let h = ret.clone().unwrap_or_default();
            for (rb, block, _, st) in below {
                if let Some(have) = cx.hx.row_heap.get_mut(&(rb, block)) {
                    changed |= have.join_heap(&h);
                } else {
                    cx.hx.row_heap.insert((rb, block), h.clone());
                    changed = true;
                }
                let mut s = st;
                s.join_heap(&h);
                join_reentry(cx, (rb, block), &s);
            }
        }
        for (rb, block, next, st) in own {
            let mut s = st;
            if root {
                if let Some(r) = &ret {
                    s.join_heap(r);
                }
            } else {
                // A node of the clause body: the heap that the run of the
                // body found (the facts of a clause come after the analysis
                // of its function).
                let Some(h) = cx.hx.row_heap.get(&(rb, block)) else {
                    note_row_pending();
                    return Ok(states);
                };
                s.join_heap(h);
            }
            join_reentry(cx, (rb, block), &s);
            if rb == body {
                if let Some(have) = again.get_mut(&next) {
                    changed |= have.join(&s);
                } else {
                    again.insert(next, s);
                    changed = true;
                }
            } else {
                let seeds = cx.hx.extra.entry(rb).or_default();
                changed |= clause::join_seed_list(seeds, next, &s);
            }
        }
        if !changed {
            return Ok(states);
        }
        let _ = round;
    }
    let _ = p;
    Err(AlphaError::Later(
        "a body whose re-runs after a `multi` operation do not end (stage F16)",
    ))
}

/// True if a function value that the run node `at` runs, or gives to its
/// callee, can hold references in its environment, in the state `st` at the
/// node, or if an argument of the run can hold references (plan stage R0z
/// Z7, review rounds 3 and 4).
///
/// Then the copy of the frame of the value at the re-entry of the row
/// (`crate::factgen::handlers::copy_node`) points into each place below the
/// references of the environment (a wildcard), and a change of such a place
/// after the run gives a false W0301 (`fixes/r0z7/t3_capture_v_push_after_ok`;
/// main gives the same W0301 for a row of a call of a known closure, issue
/// #79). So such a row stays pending (`crate::factgen::frames::
/// refuse_clause_dyn_row`). A value that the analysis does not know (code of
/// a caller, a capture, the result of a run) counts as one that can, and so
/// does a node with no function value in the state. In the run of the facts
/// of a clause (`clause`), a parameter of the clause does not count: the run
/// of the function decides with the values that the performs give.
fn env_can_hold_refs(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, BlockId),
    st: &State,
    clause: bool,
) -> bool {
    let p = cx.p;
    let Some(t) = p
        .body(body)
        .and_then(|b| b.blocks.get(block.index()))
        .map(|blk| blk.term.kind.clone())
    else {
        return true;
    };
    let weft_ir::TermKind::Call { callee, args, .. } = &t else {
        return true;
    };
    // An argument that is a reference, or whose type holds a reference or a
    // function value, flows into the run too (the copy of the frame of the
    // value holds it: `fixes/r0z7/m1_clause_ref_arg_ok`).
    let tys0 = &*cx.tys;
    let arg_refs = args.iter().any(|a| match a {
        weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q) => {
            !q.proj.is_empty()
                || p.body(body).and_then(|b| b.local(q.local)).is_none_or(|l| {
                    crate::analysis::sig::is_ref(tys0, l.ty)
                        || crate::analysis::sig::holds_refs(tys0, l.ty)
                        || matches!(tys0.try_get(l.ty), Some(weft_ir::Ty::Fn(_)))
                })
        }
        weft_ir::Operand::Const(_) => false,
    });
    if arg_refs {
        return true;
    }
    let mut ops: Vec<&weft_ir::Operand> = args.iter().collect();
    if let weft_ir::Callee::Value(f) = callee {
        ops.push(f);
    }
    let mut fns: Vec<FnVal> = Vec::new();
    for o in ops {
        match transfer::operand(cx, body, st, o) {
            Ok(v) => fns.extend(v.flat().fns.iter().cloned()),
            Err(_) => return true,
        }
    }
    if fns.is_empty() {
        return true;
    }
    let tys = &*cx.tys;
    fns.iter().any(|f| match f {
        FnVal::Item(..) => false,
        FnVal::Closure(c) | FnVal::Made(c) => p.closures.get(c.index()).is_none_or(|d| {
            d.captures.iter().any(|cap| {
                cap.mode == weft_ir::CaptureMode::ByRef
                    || !cap.source.proj.is_empty()
                    || p.body(d.maker)
                        .and_then(|m| m.local(cap.source.local))
                        .is_none_or(|l| {
                            crate::analysis::sig::is_ref(tys, l.ty)
                                || crate::analysis::sig::holds_refs(tys, l.ty)
                                || matches!(tys.try_get(l.ty), Some(weft_ir::Ty::Fn(_)))
                        })
            })
        }),
        // In the facts of a clause a parameter holds the values that the
        // nodes that run the clause give: the run of the function sees them
        // at the same node.
        FnVal::Param(_) | FnVal::ParamResult(_) => !clause,
        _ => true,
    })
}

/// True if the terminator of block `block` of body `body` is a node of
/// `crate::factgen::frames::row_multi` (a row that the facts know before the
/// analysis), or a run node of a clause that an earlier run of the analysis
/// found (`crate::factgen::frames::ClauseDynRows`, plan stage R0z Z7).
fn static_row(cx: &Cx<'_>, body: BodyId, block: BlockId) -> bool {
    static_row_of(cx.p, cx.tys, cx.sums, body, block)
}

/// [`static_row`] with the parts of the context.
fn static_row_of(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    sums: &Summaries,
    body: BodyId,
    block: BlockId,
) -> bool {
    crate::factgen::frames::clause_dyn_row(body, block)
        || p.body(body)
            .and_then(|b| b.blocks.get(block.index()))
            .is_some_and(|blk| {
                crate::factgen::frames::row_multi(p, tys, sums, body, &blk.term.kind)
            })
}

/// True if node `at` of a clause body (or of a body that splices into it)
/// is a run node that only the facts of the clause find as a node that can
/// resume more than once, and only as code of a caller for a value of the
/// interface (plan stage R0z Z7).
///
/// The values of the interface of the clause are its parameters. The nodes
/// that run the clause give their values: the run of the body that has the
/// handler runs the clause with these values (`clause::run_clause`,
/// `clause::post_run`). If that run finds no row at the node (no heap of
/// `clause::Handlers::row_heap`, and the run did not note the node as a
/// pending row, `crate::factgen::frames::clause_dyn_found`), no value that a
/// node gives there can
/// resume more than once. So the node is no row of the clause and no
/// `multi` point, as for a run of a known value. A node that the facts know
/// as a row before the analysis ([`static_row`]), or where a summary of a
/// value that is not of the interface can resume more than once
/// (`clause::Handlers::real_rows`), stays a row.
pub(crate) fn code_row(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    sums: &Summaries,
    hx: &clause::Handlers,
    at: (BodyId, BlockId),
) -> bool {
    let cb = crate::factgen::handlers::splice_root(p, at.0);
    let Some(weft_ir::BodyKind::Clause(h, _)) = p.body(cb).map(|b| &b.kind) else {
        return false;
    };
    let ran = hx.info(*h).is_some_and(|i| i.seeds.contains_key(&cb));
    ran && hx.dyn_rows.contains(&at)
        && !hx.real_rows.contains(&at)
        && !hx.row_heap.contains_key(&at)
        && !crate::factgen::frames::clause_dyn_found(at.0, at.1)
        && !static_row_of(p, tys, sums, at.0, at.1)
}

/// Notes a node that can wait at a `multi` operation of a handler of a
/// caller where the facts have no re-entry for it: the program is in scope
/// only if the `ir` pipeline rejects it (stage R0g).
fn note_row_pending() {
    clause::note_pending(crate::factgen::Unsupported {
        group: crate::irbuild::scope::Group::D,
        reason: "a `multi` operation of a handler of a caller in a clause (stage F16)".to_string(),
    });
}

/// Joins the state `s` into the re-entry state of node `at`
/// (`clause::Handlers::reentry`).
fn join_reentry(cx: &mut Cx<'_>, at: (BodyId, BlockId), s: &State) {
    match cx.hx.reentry.get_mut(&at) {
        Some((have, _)) => {
            have.join(s);
        }
        None => {
            cx.hx.reentry.insert(at, (s.clone(), Tree::none()));
        }
    }
}

/// Runs the analysis of body `body` from the states `seeds` at some blocks.
///
/// A seed is the entry block, or a block after a resume point of a clause
/// (plan stage F14). The run has the mode `mode`. Returns the states and the
/// states at the ends of the run ([`Ends`]).
///
/// # Errors
///
/// The errors of [`run`].
pub fn run_from(
    cx: &mut Cx<'_>,
    body: BodyId,
    seeds: Vec<(BlockId, State)>,
    mode: Mode,
) -> Result<(States, Ends), AlphaError> {
    let p = cx.p;
    let b = p
        .bodies
        .get(body.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no body b{}", body.0)))?;
    let all = mode.all;
    let order = weft_ir::order::reverse_post_order(b);
    let rank = widen::ranks(b);
    let mut join = join_blocks(b, &rank);
    let is_head = widen::heads(b, &rank);
    let mut heads: Vec<Option<widen::Head>> = vec![None; b.blocks.len()];
    let mut work: BTreeSet<usize> = BTreeSet::new();
    let mut entry: Vec<Option<State>> = vec![None; b.blocks.len()];
    for (blk, init) in seeds {
        // A seed block keeps its state: more than one state can come in.
        if let Some(j) = join.get_mut(blk.index()) {
            *j = true;
        }
        let Some(e) = entry.get_mut(blk.index()) else {
            continue;
        };
        if let Some(have) = e {
            have.join(&init);
        } else {
            if is_head.get(blk.index()).copied().unwrap_or(false) {
                if let Some(h) = heads.get_mut(blk.index()) {
                    *h = Some(widen::Head::new(&init));
                }
            }
            *e = Some(init);
        }
        work.insert(rank.get(blk.index()).copied().unwrap_or(0));
    }
    let mut out = States { entry, join };
    let mut ends = Ends::default();
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
        for s in &blk.stmts {
            transfer::stmt(cx, body, &mut st, &s.kind)?;
        }
        if matches!(blk.term.kind, weft_ir::TermKind::UnwindExit) {
            match ends.unwinds.get_mut(&blk_id) {
                Some(have) => {
                    have.join(&st);
                }
                None => {
                    ends.unwinds.insert(blk_id, st.clone());
                }
            }
        }
        if !blk.cleanup {
            match blk.term.kind {
                weft_ir::TermKind::Return => {
                    ends.returns.insert(blk_id, st.clone());
                }
                weft_ir::TermKind::Resume { .. } if mode.stop_at_resume => {
                    ends.resumes.insert(blk_id, st);
                    continue;
                }
                // A runtime resume node (plan stage R0z Z4b) is a resume
                // point of the clause.
                weft_ir::TermKind::Call { .. }
                    if mode.stop_at_resume && cx.p.resume_run_at(body, blk_id).is_some() =>
                {
                    ends.resumes.insert(blk_id, st);
                    continue;
                }
                _ => {}
            }
        }
        for (to, s) in edges(cx, body, blk_id, &blk.term.kind, st)? {
            let Some(slot) = out.entry.get_mut(to.index()) else {
                continue;
            };
            let head = heads.get_mut(to.index());
            let changed = match (slot, head) {
                (Some(have), Some(Some(h))) => {
                    // A loop head: the join widens (`widen`).
                    let old = have.clone();
                    if have.join(&s) {
                        if !widen::widen(cx.facts, cx.roots, have, &old, h, b.locals.len()) {
                            return Err(AlphaError::Later("a loop that the widening does not end"));
                        }
                        *have != old
                    } else {
                        false
                    }
                }
                (Some(have), _) => have.join(&s),
                (slot, head) => {
                    if is_head.get(to.index()).copied().unwrap_or(false) {
                        if let Some(h) = head {
                            *h = Some(widen::Head::new(&s));
                        }
                    }
                    *slot = Some(s);
                    true
                }
            };
            if changed {
                if let Some(&tr) = rank.get(to.index()) {
                    work.insert(tr);
                }
            }
        }
    }
    Ok((out, ends))
}
