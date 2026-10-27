//! Handlers in the analysis (`docs/ir.md` 6.5, 6.7; plan stage F14).
//!
//! A `handle` runs its handled body once (V15), so the analysis runs the
//! handled body as a part of the run of its site: the state before the
//! `handle`, with the capability, is the state at the entry of the handled
//! body ([`handle_run`]).
//!
//! A perform through the capability of a local handler runs the clause of
//! its operation. The clause runs while the handled body waits at the
//! perform, so the analysis runs the code of the clause before its first
//! resume point (the `pre` part) from the state at the perform, with the
//! parameters of the clause bound to the values of the arguments
//! ([`perform_run`]). The state after the perform is the join of the states
//! at the resume points of the clause, and the result of the perform is the
//! join of the values that the clause gives to `resume`. A clause that ends
//! with no `resume` aborts to its handler: the state of such an end joins the
//! state after the `handle`, and the abort edge of the perform gets it
//! ([`AbortEdge`], plan stage F15). A clause that resumes on each path never
//! aborts to its handler ([`lands`]).
//!
//! A call that runs a clause gives each parameter of the clause the places
//! that the callee can give it ([`given`], plan stage F15): the places that
//! the arguments reach, and the callee frame if the callee can give a place
//! of its frame.
//!
//! When the handled body returns, a `resume` of each clause that ran gives
//! back the value of the handled body, and the code of the clause after its
//! resume point runs (the `post` part): the analysis runs each clause from
//! the blocks after its resume points, with the locals of the clause from
//! the state at the resume point and the other locals from the state at the
//! end of the handled body. The value of the `handle` is the value of the
//! handled body and the value of each clause.
//!
//! The facts of a clause body are a component of the facts of its function
//! (`crate::factgen`), as a closure body is. Their analysis starts from the
//! join of the states at the performs that run the clause ([`Info::seeds`]),
//! and a `resume` there gives back the value of the handled body and the
//! state at its end ([`resume`]).
//!
//! Not yet: a handler of an effect with a `multi` operation (re-entry
//! edges, stage F16).

use std::collections::BTreeMap;

use weft_ir::{BlockId, BodyId, BodyKind, HandlerId, LocalKind, Operand, Place, Program, TermKind};

use super::domain::{AbsVal, State, Tree};

/// The result of a transfer function.
type R = Result<(), AlphaError>;
use super::transfer::{self, Cx};
use super::{run_from, Mode, States};
use crate::factgen::alpha::AlphaError;

/// The blocks where a run starts, with the state there.
type Seeds = Vec<(BlockId, State)>;

/// The number of runs of the code of the clauses after their resume points
/// that the analysis does to find what a `resume` gives back: a clause
/// value can be the result of `resume` in another run of a clause.
const POST_ROUNDS: usize = 8;

/// What the analysis keeps about the handlers of one component, and the
/// run nodes of the clauses in the facts.
#[derive(Clone, Debug, Default)]
pub struct Handlers {
    /// The handlers whose handled body runs now, the innermost last.
    open: Vec<Open>,
    /// What the runs of each handler found (a join over the runs).
    info: BTreeMap<HandlerId, Info>,
    /// The nodes where the code of a clause runs (`crate::factgen::handlers`).
    pub runs: Vec<ClauseRun>,
    /// The `Main` node of each `Resume` of a clause in the facts, with the
    /// handler and the clause body.
    pub resumes: Vec<(weft_facts::NodeId, HandlerId, BodyId)>,
    /// The handler id and the capability id of each handler in the facts.
    pub ids: BTreeMap<HandlerId, (weft_facts::HandlerId, weft_facts::CapId)>,
    /// The `Exit` and `Post` nodes of each `handle` in the facts.
    pub ends: Vec<(HandlerId, weft_facts::NodeId, weft_facts::NodeId)>,
    /// The `Landing` node of each `handle` in the facts.
    pub landings: Vec<(HandlerId, weft_facts::NodeId)>,
    /// The state of the abort edge of the terminator that the analysis ran
    /// last, if it ran a clause (`super::edges` takes it).
    pub abort_edge: Option<AbortEdge>,
    /// For each body: the locals that a path from the entry to the
    /// terminator of each block can assign (one bit set for each block;
    /// `crate::factgen::handlers::unassigned`).
    pub assigned: BTreeMap<BodyId, Vec<Vec<u64>>>,
}

/// The state of the abort edge of a terminator that runs a clause.
///
/// It is the state of the clause where it aborts (plan stage F15), to its
/// handler (it ends with no `resume`) or past it, with no local of the
/// clause.
#[derive(Clone, Debug)]
pub enum AbortEdge {
    /// A `perform` through a local capability: it aborts only where the
    /// clause aborts.
    Replace(State),
    /// A call: the callee can abort too, so the state before the call
    /// joins.
    Join(State),
}

/// A node where the code of a clause runs (plan stage F14).
///
/// A perform through the capability of a local handler runs the code of the
/// clause before its first resume point, and the `Post` node of a `handle`
/// runs the code after its resume points.
#[derive(Clone, Debug)]
pub struct ClauseRun {
    /// The node.
    pub node: weft_facts::NodeId,
    /// The handler.
    pub handler: HandlerId,
    /// The clause body.
    pub clause: BodyId,
    /// The code after the resume points (`Post`), else the code before them.
    pub post: bool,
    /// σ of each parameter of the clause: the places of the argument
    /// (empty at `Post`: the places of each perform of the clause).
    pub args: Vec<Vec<weft_facts::PlaceId>>,
    /// What the references behind each argument point into.
    pub helds: Vec<Vec<weft_facts::PlaceId>>,
    /// The handle places `h.*` of the `Rc` handles on the way to each
    /// argument: a reference through a handle depends on it (ADR 0003).
    pub deps: Vec<Vec<weft_facts::PlaceId>>,
    /// The body of the node.
    pub at: BodyId,
    /// The handled bodies of the local handlers that each abort of the node
    /// goes to, if each abort goes to one (none if one can go past the
    /// function): the variables outside them are spared (`spared_at`).
    pub spares: Option<Vec<BodyId>>,
    /// The parameter whose root each parameter of the clause has in
    /// `call_mut`: a parameter of the operation with an `in` place has the
    /// root of the parameter of its place (R3RT7). Empty: its own root.
    pub ins: Vec<usize>,
    /// The node is a call: σ of each parameter is the places that the call
    /// gives (`given`, plan stage F15), not an argument of the node. Each
    /// given place of an argument has the callee root of its parameter: a
    /// change below it has that root in `call_mut`.
    pub given: Option<Vec<(weft_facts::PlaceId, u32)>>,
}

/// A handler whose handled body runs now.
#[derive(Clone, Debug)]
struct Open {
    /// The handler.
    handler: HandlerId,
    /// The state at each resume point of a clause that a perform ran: the
    /// clause body, the block and the state after its statements.
    resumes: Vec<(BodyId, BlockId, State)>,
    /// The join of the states where a clause ended with no `resume`, with
    /// no local of the clause.
    landing: Option<State>,
    /// The join of the values of the clauses that ended with no `resume`.
    landing_value: Tree,
}

/// What the runs of one handler found.
#[derive(Clone, Debug, Default)]
pub struct Info {
    /// For each clause body: the join of the states at the performs that
    /// run it, after the moves of the arguments (the parameters of the clause
    /// do not have a value there).
    pub seeds: BTreeMap<BodyId, State>,
    /// The join of the states at the `Return` of the handled body.
    pub exit: Option<State>,
    /// What a `resume` gives back: the value of the handled body, and the
    /// value of each clause after a `resume`.
    pub resumed: Tree,
    /// For each clause body: the join of the values of its parameters at
    /// the nodes that run it (the places of the arguments). The facts of
    /// the clause give each parameter these places besides its own root,
    /// so a value of the clause in a place of the site has places of the
    /// site (plan stage F15).
    pub params: BTreeMap<BodyId, Vec<Tree>>,
}

impl Handlers {
    /// What the runs of handler `h` found, if a run found something.
    pub fn info(&self, h: HandlerId) -> Option<&Info> {
        self.info.get(&h)
    }

    /// The open handler `h`, if its handled body runs now.
    fn open_mut(&mut self, h: HandlerId) -> Option<&mut Open> {
        self.open.iter_mut().rev().find(|o| o.handler == h)
    }
}

/// True if body `b` is body `root` or a body inside it: the parent chain of
/// `b` reaches `root`.
pub fn inside(p: &Program, b: BodyId, root: BodyId) -> bool {
    let mut at = Some(b);
    for _ in 0..=p.bodies.len() {
        let Some(x) = at else {
            return false;
        };
        if x == root {
            return true;
        }
        at = p.bodies.get(x.index()).and_then(|d| d.parent);
    }
    false
}

/// The handler of the capability in `place` of body `body`.
///
/// `place` is a whole capability local of a handled body, or an upvar local
/// of one. `None` for another place (a capability in the environment of a
/// closure).
pub fn cap_handler(p: &Program, body: BodyId, place: &Place) -> Option<HandlerId> {
    if !place.proj.is_empty() {
        return None;
    }
    let (ob, ol) = crate::factgen::alpha::owner_local(p, body, place.local).ok()?;
    let b = p.body(ob)?;
    match (b.kind, b.local_kind(ol)?) {
        (BodyKind::Handled(h), LocalKind::Cap(_)) => Some(h),
        _ => None,
    }
}

/// The handler, the clause body and the mode (`multi`) of a continuation.
///
/// `place` of body `body` is a whole continuation local of a clause, or an
/// upvar local of one. `None` for another place (a continuation in the
/// environment of a closure).
pub fn kont_handler(p: &Program, body: BodyId, place: &Place) -> Option<(HandlerId, BodyId, bool)> {
    if !place.proj.is_empty() {
        return None;
    }
    let (ob, ol) = crate::factgen::alpha::owner_local(p, body, place.local).ok()?;
    let b = p.body(ob)?;
    match (b.kind, b.kont) {
        (BodyKind::Clause(h, _), Some((k, multi))) if k == ol => Some((h, ob, multi)),
        _ => None,
    }
}

/// The clause body of operation `op` of handler `h`.
pub fn clause_of(p: &Program, h: HandlerId, op: weft_ir::OpIdx) -> Option<BodyId> {
    p.handlers
        .get(h.index())?
        .clauses
        .iter()
        .find(|(o, _)| *o == op)
        .map(|(_, b)| *b)
}

/// True if clause body `cb` can end with no resume point: a path from its
/// entry reaches a `Return` with no `Resume` on the way (plan stage F15).
///
/// Such an end aborts to the handler of the clause: its value binds to the
/// destination of the `handle`, and the frames of the handled body unwind.
/// A clause that resumes on each path to its `Return` never aborts to its
/// handler, so a perform of its operation has no abort edge to the handler.
/// The test is on the blocks of the clause body: a `resume` in a body
/// inside the clause is not a resume point here (stage F16), so the clause
/// counts as one that can end with no resume point.
pub fn lands(p: &Program, cb: BodyId) -> bool {
    let Some(b) = p.body(cb) else {
        return true;
    };
    let mut seen = vec![false; b.blocks.len()];
    let mut work = vec![b.entry];
    while let Some(at) = work.pop() {
        match seen.get_mut(at.index()) {
            Some(s) if !*s => *s = true,
            _ => continue,
        }
        let Some(blk) = b.blocks.get(at.index()) else {
            continue;
        };
        if blk.cleanup {
            continue;
        }
        match blk.term.kind {
            TermKind::Return => return true,
            TermKind::Resume { .. } => {}
            ref t => work.extend(t.normal_successors()),
        }
    }
    false
}

/// True if a clause of handler `h` can end with no resume point
/// ([`lands`]). With `op`, only the clause of that operation.
pub fn handler_lands(p: &Program, h: HandlerId, op: Option<weft_ir::OpIdx>) -> bool {
    let Some(hd) = p.handlers.get(h.index()) else {
        return true;
    };
    hd.clauses
        .iter()
        .filter(|(o, _)| op.is_none_or(|x| x == *o))
        .any(|&(_, c)| lands(p, c))
}

/// The handler `h`, or [`AlphaError::Later`] for a handler of a later
/// stage.
fn handler(p: &Program, h: HandlerId) -> Result<&weft_ir::HandlerDecl, AlphaError> {
    let hd = p
        .handlers
        .get(h.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no handler h{}", h.0)))?;
    if hd.multi {
        return Err(AlphaError::Later(
            "a handler of an effect with a `multi` operation (stage F16)",
        ));
    }
    Ok(hd)
}

/// The body `b`.
fn body_of(p: &Program, b: BodyId) -> Result<&weft_ir::Body, AlphaError> {
    p.body(b)
        .ok_or_else(|| AlphaError::BadPlace(format!("no body b{}", b.0)))
}

/// The state at the entry of the handled body of handler `h`: the state
/// `st` before the `handle`, and the capability. The value of the
/// capability local holds the root of the local (`docs/ir.md` 6.3).
///
/// # Errors
///
/// The errors of α.
pub fn handled_entry(cx: &mut Cx<'_>, st: &State, h: HandlerId) -> Result<State, AlphaError> {
    let p = cx.p;
    let hd = handler(p, h)?;
    let hb = hd.handled;
    let hbody = body_of(p, hb)?;
    let mut init = st.clone();
    for &(_, c) in &hbody.caps {
        let r = cx.roots.local(p, cx.tys, cx.facts, hb, c)?;
        let mut v = AbsVal::plain();
        v.caps.insert(r);
        init.write((hb, c), &[], Tree::leaf(v));
    }
    Ok(init)
}

/// What the run of a `handle` gives ([`handle_run`]).
#[derive(Clone, Debug)]
pub struct HandleOut {
    /// The states of the handled body.
    pub states: States,
    /// The join of the states at the `Return` of the handled body, after its
    /// statements: the state at the `Exit` node.
    pub exit: Option<State>,
    /// The state after the `handle`, before its destination gets the value:
    /// the end of the handled body, the code of the clauses after their
    /// resume points, and the clauses that end with no `resume`. It has no
    /// local of the handled body or of a clause.
    pub after: State,
    /// The value of the `handle`.
    pub value: Tree,
    /// The join of the states where a clause ended with no `resume` (the
    /// state at the `Landing` node), with no local of a clause.
    pub landing: Option<State>,
}

/// The run of a `handle` of handler `h` in body `body`, from the state `st`
/// before it (see the module text).
///
/// # Errors
///
/// The errors of the transfer functions, and [`AlphaError::Later`] for a
/// handler of a later stage.
pub fn handle_run(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    h: HandlerId,
) -> Result<HandleOut, AlphaError> {
    let p = cx.p;
    let hd = handler(p, h)?;
    let hb = hd.handled;
    let hbody = body_of(p, hb)?;
    let init = handled_entry(cx, st, h)?;
    cx.hx.open.push(Open {
        handler: h,
        resumes: Vec::new(),
        landing: None,
        landing_value: Tree::none(),
    });
    let run = run_from(cx, hb, vec![(hbody.entry, init)], Mode::default());
    let open = cx.hx.open.pop();
    let (states, ends) = run?;
    let open = open.ok_or_else(|| AlphaError::BadPlace("no open handler".to_string()))?;
    let mut exit: Option<State> = None;
    for s in ends.returns.values() {
        match &mut exit {
            Some(e) => {
                e.join(s);
            }
            None => exit = Some(s.clone()),
        }
    }
    let body_value = exit
        .as_ref()
        .map_or_else(Tree::none, |e| e.value((hb, hbody.ret), &[]));
    // The code of each clause after its resume points: a `resume` gives back
    // the value of the handled body, or the value of a clause that resumed
    // (a nested run of a clause).
    let mut resumed = body_value.clone();
    let mut post: Vec<State> = Vec::new();
    let mut clause_values = Tree::none();
    if let Some(ex) = &exit {
        for _ in 0..POST_ROUNDS {
            post.clear();
            let mut vals = Tree::none();
            for (cb, seeds) in post_seeds(cx, &open.resumes, ex, &resumed)? {
                let ret = body_of(p, cb)?.ret;
                let (_, ends) = run_from(cx, cb, seeds, Mode::default())?;
                for s in ends.returns.into_values() {
                    vals.join(&s.value((cb, ret), &[]));
                    post.push(s);
                }
            }
            let mut all = body_value.clone();
            all.join(&vals);
            clause_values = vals;
            if all == resumed {
                break;
            }
            resumed = all;
        }
    }
    let landing = open.landing.clone();
    let mut after: Option<State> = exit.clone();
    for s in post.iter().chain(open.landing.iter()) {
        match &mut after {
            Some(a) => {
                a.join(s);
            }
            None => after = Some(s.clone()),
        }
    }
    let mut after = after.unwrap_or_else(|| st.clone());
    let clauses: Vec<BodyId> = hd.clauses.iter().map(|(_, c)| *c).collect();
    // A closure that the handled body makes keeps the values of the locals
    // that it captures (`Kept`, `ByRef`): it can run after the `handle`.
    let captured: Vec<(super::Key, Tree)> = captured_locals(p, hb)
        .into_iter()
        .filter_map(|k| after.tree(k).map(|t| (k, t.clone())))
        .collect();
    after.remove_bodies(&|b| inside(p, b, hb) || clauses.iter().any(|&c| inside(p, b, c)));
    for (k, t) in captured {
        after.keep_value(k, t);
    }
    let mut value = body_value;
    value.join(&clause_values);
    value.join(&open.landing_value);
    let info = cx.hx.info.entry(h).or_default();
    if let Some(ex) = &exit {
        match &mut info.exit {
            Some(e) => {
                e.join(ex);
            }
            None => info.exit = Some(ex.clone()),
        }
    }
    info.resumed.join(&resumed);
    let _ = body;
    Ok(HandleOut {
        states,
        exit,
        after,
        value,
        landing,
    })
}

/// The locals of handled body `hb` (and of the bodies inside it) that a
/// closure made inside it captures `Kept` or `ByRef`.
pub(crate) fn captured_locals(p: &Program, hb: BodyId) -> Vec<super::Key> {
    let mut out = Vec::new();
    for c in &p.closures {
        if !inside(p, c.maker, hb) {
            continue;
        }
        for cap in &c.captures {
            if !matches!(
                cap.mode,
                weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef
            ) {
                continue;
            }
            if let Ok(k) = crate::factgen::alpha::owner_local(p, c.maker, cap.source.local) {
                if inside(p, k.0, hb) {
                    out.push(k);
                }
            }
        }
    }
    out.sort();
    out.dedup();
    out
}

/// The seeds of the runs of the clauses after their resume points: for each
/// clause body, the block after each resume point with the state there (the
/// locals of the clause from the state at the resume point, the other
/// locals from the state `exit` at the end of the handled body, and the
/// destination of the `resume` with the value `resumed`).
///
/// # Errors
///
/// The errors of α.
fn post_seeds(
    cx: &mut Cx<'_>,
    resumes: &[(BodyId, BlockId, State)],
    exit: &State,
    resumed: &Tree,
) -> Result<Vec<(BodyId, Seeds)>, AlphaError> {
    let p = cx.p;
    let mut by: BTreeMap<BodyId, Seeds> = BTreeMap::new();
    for (cb, rb, sr) in resumes {
        let cbody = body_of(p, *cb)?;
        let Some(TermKind::Resume {
            kont,
            arg,
            dest,
            next,
            ..
        }) = cbody.blocks.get(rb.index()).map(|b| &b.term.kind)
        else {
            continue;
        };
        let mut s = sr.clone();
        resume_with(cx, *cb, &mut s, (kont, arg, dest), Some(exit), resumed)?;
        by.entry(*cb).or_default().push((*next, s));
    }
    Ok(by.into_iter().collect())
}

/// The transfer of a `Resume` of body `body` in state `st`: the argument
/// moves, a `once` continuation moves, the locals that are not of the clause
/// get their values from the state `exit` at the end of the handled body
/// (if the handled body can end), joined with their values in `st` (in the
/// terms of the clause), and the destination gets the value `resumed`.
///
/// # Errors
///
/// The errors of α.
fn resume_with(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    (kont, arg, dest): (&Place, &Operand, &Place),
    exit: Option<&State>,
    resumed: &Tree,
) -> Result<(), AlphaError> {
    let p = cx.p;
    let (_, cb, multi) = kont_handler(p, body, kont)
        .ok_or(AlphaError::Later("a continuation in a closure (stage F16)"))?;
    transfer::moves(p, body, st, [arg])?;
    if !multi {
        if let Some((k, path)) = transfer::move_path(p, body, kont)? {
            st.clear(k, &path);
        }
    }
    if let Some(ex) = exit {
        let mut after = ex.with_bodies_of(st, &|b| inside(p, b, cb));
        after.join_values_but(st, &|b| inside(p, b, cb));
        *st = after;
    }
    transfer::bind_result(cx, body, st, &[], dest, resumed.clone())
}

/// The transfer of a `handle` of handler `h` in body `body`: the run of the
/// handled body and of the clauses ([`handle_run`]), then the destination
/// gets the value of the `handle`.
///
/// # Errors
///
/// The errors of [`handle_run`].
pub fn handle(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    h: HandlerId,
    dest: &Place,
) -> Result<(), AlphaError> {
    let out = handle_run(cx, body, st, h)?;
    *st = out.after;
    transfer::bind_result(cx, body, st, &[], dest, out.value)
}

/// What a perform through the capability of a local handler gives
/// ([`perform_run`]).
#[derive(Clone, Debug)]
pub struct PerformOut {
    /// The handler.
    pub handler: HandlerId,
    /// The clause body.
    pub clause: BodyId,
    /// The value of each argument.
    pub args: Vec<Tree>,
    /// The state after the perform, before its destination gets the value.
    pub after: State,
    /// The result of the perform: the join of the values that the clause
    /// gives to `resume`.
    pub value: Tree,
    /// The value of the clause where it ends with no `resume`: the value of
    /// the `handle` after the abort to the handler.
    pub landing: Tree,
    /// The state of the clause where it aborts (`AbortEdge`).
    pub abort: Option<State>,
}

/// The run of a clause at a perform of body `body` (see the module text).
///
/// The perform is of operation `op` through the capability `cap` of a local
/// handler, with the arguments `args`, from the state `st` before it.
///
/// # Errors
///
/// The errors of the transfer functions, and [`AlphaError::Later`] for a
/// capability that the analysis does not know (a capability in the
/// environment of a closure) and for a handler of a later stage.
pub fn perform_run(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &State,
    cap: &Place,
    op: weft_ir::OpIdx,
    args: &[Operand],
) -> Result<PerformOut, AlphaError> {
    let p = cx.p;
    let h = cap_handler(p, body, cap).ok_or(AlphaError::Later(
        "a perform through a captured capability (stage F16)",
    ))?;
    handler(p, h)?;
    let cb = clause_of(p, h, op).ok_or_else(|| {
        AlphaError::BadPlace(format!("handler h{} has no clause of an operation", h.0))
    })?;
    let mut vals = Vec::with_capacity(args.len());
    for a in args {
        vals.push(transfer::operand(cx, body, st, a)?);
    }
    let mut s0 = st.clone();
    transfer::moves(p, body, &mut s0, args)?;
    let run = run_clause(cx, h, cb, (&s0, None), &vals)?;
    // A clause with no resume point: the code after the perform does not
    // run, and any state is right there.
    let after = run.after.unwrap_or(s0);
    Ok(PerformOut {
        handler: h,
        clause: cb,
        args: vals,
        after,
        value: run.value,
        landing: run.landing,
        abort: run.abort,
    })
}

/// The run of clause body `cb` of handler `h` from the state `s0`, with the
/// values `vals` of its parameters, up to its resume points.
///
/// What the run of a clause up to its resume points gives ([`run_clause`]).
#[derive(Clone, Debug)]
struct ClauseOut {
    /// The join of the states at the resume points with no local of the
    /// clause (none if the clause has no resume point).
    after: Option<State>,
    /// The join of the values that the clause gives to `resume`.
    value: Tree,
    /// The join of the values of the clause where it ends with no `resume`.
    landing: Tree,
    /// The join of the states where the clause aborts: where it ends with no
    /// `resume`, and where an abort leaves it (its `UnwindExit`), with no
    /// local of the clause (plan stage F15).
    abort: Option<State>,
}

/// The run of clause body `cb` of handler `h` from the state `s0`, with the
/// values `vals` of its parameters, up to its resume points
/// ([`ClauseOut`]). The state `s0` joins the seed of the facts of the
/// clause; the open run of the handler gets the states at the resume
/// points and at each end with no `resume`.
///
/// # Errors
///
/// The errors of the transfer functions.
fn run_clause(
    cx: &mut Cx<'_>,
    h: HandlerId,
    cb: BodyId,
    (s0, frame): (&State, Option<weft_facts::PlaceId>),
    vals: &[Tree],
) -> Result<ClauseOut, AlphaError> {
    let p = cx.p;
    let cbody = body_of(p, cb)?;
    // The heap slot of the callee frame (`Given::state`) holds only while
    // the clause runs: the states that leave the run do not have it.
    let clean = |st: &State| -> State {
        let mut st = st.clone();
        if let Some(f) = frame {
            st.map_behind(&mut |q, refs| {
                let hit = q == f && !refs.is_empty();
                if hit {
                    refs.clear();
                }
                hit
            });
        }
        st
    };
    {
        let s0 = clean(s0);
        let info = cx.hx.info.entry(h).or_default();
        match info.seeds.get_mut(&cb) {
            Some(s) => {
                s.join(&s0);
            }
            None => {
                info.seeds.insert(cb, s0);
            }
        }
        let ps = info.params.entry(cb).or_default();
        for (i, v) in vals.iter().enumerate() {
            match ps.get_mut(i) {
                Some(have) => {
                    have.join(v);
                }
                None => ps.push(v.clone()),
            }
        }
    }
    let mut init = s0.clone();
    for (i, &l) in cbody.params.iter().enumerate() {
        let v = vals.get(i).cloned().unwrap_or_else(Tree::none);
        init.write(transfer::key(p, cb, l)?, &[], v);
    }
    if let Some((k, _)) = cbody.kont {
        init.write((cb, k), &[], Tree::leaf(AbsVal::plain()));
    }
    let mode = Mode {
        all: false,
        stop_at_resume: true,
    };
    let (_, ends) = run_from(cx, cb, vec![(cbody.entry, init)], mode)?;
    let mine = |b: BodyId| inside(p, b, cb);
    let mut after: Option<State> = None;
    let mut value = Tree::none();
    for (rb, sr) in &ends.resumes {
        if let Some(TermKind::Resume { arg, .. }) =
            cbody.blocks.get(rb.index()).map(|b| &b.term.kind)
        {
            value.join(&transfer::operand(cx, cb, sr, arg)?);
        }
        let sr = clean(sr);
        let mut s = sr.clone();
        s.remove_bodies(&mine);
        match &mut after {
            Some(a) => {
                a.join(&s);
            }
            None => after = Some(s),
        }
        if let Some(o) = cx.hx.open_mut(h) {
            o.resumes.push((cb, *rb, sr));
        }
    }
    // A clause that ends with no `resume` aborts to its handler.
    let mut landing = Tree::none();
    let mut abort: Option<State> = None;
    let mut add = |s: &State| match &mut abort {
        Some(a) => {
            a.join(s);
        }
        None => abort = Some(s.clone()),
    };
    for sret in ends.returns.values() {
        let v = sret.value((cb, cbody.ret), &[]);
        landing.join(&v);
        let mut s = clean(sret);
        s.remove_bodies(&mine);
        add(&s);
        if let Some(o) = cx.hx.open_mut(h) {
            o.landing_value.join(&v);
            match &mut o.landing {
                Some(l) => {
                    l.join(&s);
                }
                None => o.landing = Some(s),
            }
        }
    }
    // An abort that leaves the clause (past its handler).
    for su in ends.unwinds.values() {
        let mut s = clean(su);
        s.remove_bodies(&mine);
        add(&s);
    }
    Ok(ClauseOut {
        after,
        value,
        landing,
        abort,
    })
}

/// The local handlers whose clauses a call can run.
///
/// They are the handlers that call `t` of body `body` performs through or
/// fails to (an effect of the row of the callee, or a failure, that
/// resolves to a handler of the component,
/// `crate::factgen::frames::clause_handlers`), also if their clauses resume
/// on each path.
pub fn call_handlers(cx: &Cx<'_>, body: BodyId, t: &TermKind) -> Vec<HandlerId> {
    crate::factgen::frames::clause_handlers(cx.p, cx.tys, cx.sums, body, t)
}

/// True if clause body `cb` has a resume point (a `Resume` of its own
/// blocks).
fn has_resume(p: &Program, cb: BodyId) -> bool {
    p.body(cb).is_some_and(|b| {
        b.blocks
            .iter()
            .any(|blk| !blk.cleanup && matches!(blk.term.kind, TermKind::Resume { .. }))
    })
}

/// True if a call can run the clauses of handler `h` (plan stage F15).
///
/// No parameter and no result of an operation of a clause of the handler
/// holds a function value or a value of a type parameter, and a result
/// holds no reference if the clause can resume: the values that a clause
/// gives back to the callee hold no place of the site. A parameter can
/// hold a reference: it points into the places that the callee gives
/// ([`given`]).
pub fn given_ops(p: &Program, tys: &weft_ir::TyTable, h: HandlerId) -> bool {
    let Some(hd) = p.handlers.get(h.index()) else {
        return false;
    };
    let Some(e) = tys.effects().get(hd.effect.index()) else {
        return false;
    };
    let no_fns = |t: weft_ir::TyId| {
        let pr = crate::props::ir_props(tys, t);
        !pr.generic && !pr.callable && !crate::props::ir_has_fns(tys, t)
    };
    hd.clauses.iter().all(|&(op, c)| {
        e.ops.get(op.index()).is_some_and(|o| {
            o.params.iter().all(|&t| no_fns(t))
                && no_fns(o.ret)
                && (!crate::props::ir_props(tys, o.ret).holds_refs || !has_resume(p, c))
        })
    })
}

/// True if a parameter of an operation of a clause of handler `h` can hold
/// a reference: a call that runs the clause gives it places ([`given`]).
pub fn gives_refs(p: &Program, tys: &weft_ir::TyTable, h: HandlerId) -> bool {
    let Some(hd) = p.handlers.get(h.index()) else {
        return false;
    };
    let Some(e) = tys.effects().get(hd.effect.index()) else {
        return false;
    };
    hd.clauses.iter().any(|(op, _)| {
        e.ops.get(op.index()).is_some_and(|o| {
            o.params
                .iter()
                .any(|&t| crate::props::ir_props(tys, t).holds_refs)
        })
    })
}

/// The places that a call gives to the parameters of the clauses that it
/// runs (plan stage F15).
///
/// The callee performs through the capability of a caller, so the arguments
/// of the operation are places that it can name: a local of its frame (the
/// callee frame root of the call, `docs/ir.md` 6.3, which ends at the
/// `FrameEnd` of the call and on each abort path; only if the summary of
/// the callee says that it can give one, `Summary::gives_frame`), and the
/// places that the
/// arguments of the call reach (the places of each argument, the places
/// that its references point into, the places that the references behind
/// them point into, and the `rc` groups that they reach). Each one is a
/// wildcard place: the callee can
/// give a place below it. `st` is the state before call `t` of block
/// `block` of body `body`. Empty for a call of a function value (it runs
/// no local clause).
///
/// # Errors
///
/// The errors of σ.
pub fn given(
    cx: &mut Cx<'_>,
    body: BodyId,
    block: BlockId,
    st: &State,
    t: &TermKind,
) -> Result<Given, AlphaError> {
    let TermKind::Call {
        callee: weft_ir::Callee::Fn(f, targs),
        args,
        ..
    } = t
    else {
        return Ok(Given::default());
    };
    let p = cx.p;
    let decl = p
        .fns
        .get(f.index())
        .ok_or_else(|| AlphaError::BadPlace(format!("no function f{}", f.0)))?;
    let inst = transfer::run_inst(body, block);
    let s = super::apply::sigma(cx, body, st, decl, targs, args, inst)?;
    // The callee frame root, if the callee can give a place of its frame
    // to an operation (`Summary::gives_frame`).
    let gives = cx.sums.get(*f).map_or(true, |x| x.gives_frame);
    let frame = gives.then(|| cx.roots.frame(cx.facts, inst, &decl.name));
    // The `rc` objects that the arguments reach: a place in one is a place
    // of the group root of its type, not a place below the argument.
    let mut groups = Vec::new();
    for &t in &s.tys {
        for inner in transfer::rc_inners(cx.tys, t) {
            groups.push(cx.roots.group(cx.tys, cx.facts, inner));
        }
    }
    // The places of each argument, with the callee root of its parameter
    // (`call_arg`): a change through a place that the callee gives is a
    // change through that parameter (W0312, as for a call).
    let sum_roots: Vec<u32> = cx
        .sums
        .get(*f)
        .map(|x| x.params.iter().map(|q| q.root).collect())
        .unwrap_or_default();
    let mut roots: Vec<(weft_facts::PlaceId, u32)> = Vec::new();
    for i in 0..args.len() {
        let root = sum_roots
            .get(i)
            .copied()
            .unwrap_or_else(|| crate::body::roots::param(i));
        let of = |v: &Vec<Vec<weft_facts::PlaceId>>| v.get(i).cloned().unwrap_or_default();
        for q in of(&s.args)
            .into_iter()
            .chain(of(&s.values))
            .chain(of(&s.helds))
        {
            roots.push((cx.facts.wildcard(q), root));
        }
    }
    roots.sort();
    roots.dedup();
    let mut places: Vec<weft_facts::PlaceId> = roots
        .iter()
        .map(|&(q, _)| q)
        .chain(
            groups
                .into_iter()
                .chain(frame)
                .map(|q| cx.facts.wildcard(q)),
        )
        .collect();
    places.sort();
    places.dedup();
    let mut deps: Vec<weft_facts::PlaceId> = s.deps.into_iter().flatten().collect();
    deps.sort();
    deps.dedup();
    let frame = frame.map(|q| cx.facts.wildcard(q));
    Ok(Given {
        places,
        deps,
        roots,
        frame,
    })
}

/// The places that a call gives to the clauses that it runs ([`given`]).
#[derive(Clone, Debug, Default)]
pub struct Given {
    /// The wildcard places that a parameter of a clause can point into.
    pub places: Vec<weft_facts::PlaceId>,
    /// The handle places `h.*` of the `Rc` handles on the way to the
    /// arguments of the call.
    pub deps: Vec<weft_facts::PlaceId>,
    /// The given places of the arguments, each with the callee root of its
    /// parameter.
    pub roots: Vec<(weft_facts::PlaceId, u32)>,
    /// The wildcard place of the callee frame root, if the callee can give
    /// a place of its frame.
    pub frame: Option<weft_facts::PlaceId>,
}

impl Given {
    /// The state `st` where the clauses run: a reference that the callee
    /// keeps in its frame can point into each given place (a parameter of
    /// a clause can point into a local of the callee that holds one).
    pub fn state(&self, st: &State) -> State {
        let mut out = st.clone();
        if let Some(f) = self.frame {
            out.store_behind(f, self.places.iter().copied());
        }
        out
    }

    /// The value of each parameter of clause body `cb`: a parameter whose
    /// type can hold a reference points into the given places.
    ///
    /// # Errors
    ///
    /// Returns [`AlphaError::BadPlace`] for a clause body that does not
    /// exist.
    pub fn values(&self, cx: &Cx<'_>, cb: BodyId) -> Result<Vec<Tree>, AlphaError> {
        let b = body_of(cx.p, cb)?;
        Ok(b.params
            .iter()
            .map(|&l| {
                let refs = b
                    .local(l)
                    .is_some_and(|d| crate::props::ir_props(cx.tys, d.ty).holds_refs);
                if refs {
                    Tree::leaf(AbsVal::refs(self.places.iter().copied()))
                } else {
                    Tree::leaf(AbsVal::plain())
                }
            })
            .collect())
    }

    /// σ of each parameter of clause body `cb` in the facts: the given
    /// places for a parameter whose type can hold a reference (its places
    /// and what the references behind it point into), else none.
    pub fn sigma(
        &self,
        p: &Program,
        tys: &weft_ir::TyTable,
        cb: BodyId,
    ) -> (Vec<Vec<weft_facts::PlaceId>>, Vec<Vec<weft_facts::PlaceId>>) {
        let Some(b) = p.body(cb) else {
            return (Vec::new(), Vec::new());
        };
        let mut args = Vec::new();
        let mut deps = Vec::new();
        for &l in &b.params {
            let refs = b
                .local(l)
                .is_some_and(|d| crate::props::ir_props(tys, d.ty).holds_refs);
            args.push(if refs {
                self.places.clone()
            } else {
                Vec::new()
            });
            deps.push(if refs { self.deps.clone() } else { Vec::new() });
        }
        (args, deps)
    }
}

/// The values of the clauses of the local handlers that a call aborts to.
///
/// For each local handler that call `t` of body `body` can abort to: the
/// values of its clauses where they end with no `resume`, from the state
/// `st` before the call (the value of the `handle` after the abort).
///
/// # Errors
///
/// The errors of the transfer functions.
pub fn call_landings(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, BlockId),
    st: &State,
    t: &TermKind,
) -> Result<Vec<(HandlerId, Tree)>, AlphaError> {
    let p = cx.p;
    let mut out = Vec::new();
    let hs = call_handlers(cx, body, t);
    if hs.is_empty() {
        return Ok(out);
    }
    let gv = given(cx, body, block, st, t)?;
    for h in hs {
        handler(p, h)?;
        let clauses: Vec<BodyId> = p
            .handlers
            .get(h.index())
            .map(|d| d.clauses.iter().map(|(_, c)| *c).collect())
            .unwrap_or_default();
        let mut v = Tree::none();
        let s0 = gv.state(st);
        for cb in clauses {
            let vals = gv.values(cx, cb)?;
            v.join(&run_clause(cx, h, cb, (&s0, gv.frame), &vals)?.landing);
        }
        out.push((h, v));
    }
    Ok(out)
}

/// The clauses that a call runs (plan stages F14, F15).
///
/// After the transfer of call `t` of block `block` of body `body`, each
/// clause of each local handler that the callee can perform through (or
/// fail to) runs up to its resume points from the state `st` after the
/// call. A parameter that can hold a reference points into the places that
/// the call gives ([`given`], from the state `before` the call). The state
/// after the call is the join of `st` and the states at the resume points.
///
/// # Errors
///
/// The errors of the transfer functions, and [`AlphaError::Later`] for a
/// clause whose operation gives a function value or a reference back to
/// the callee ([`given_ops`]).
pub fn call_clauses(
    cx: &mut Cx<'_>,
    (body, block): (BodyId, BlockId),
    before: Option<&State>,
    st: &mut State,
    t: &TermKind,
) -> R {
    let p = cx.p;
    let hs = call_handlers(cx, body, t);
    if hs.is_empty() {
        return Ok(());
    }
    let start = st.clone();
    let gv = given(cx, body, block, before.unwrap_or(&start), t)?;
    let mut abort: Option<State> = None;
    for h in hs {
        handler(p, h)?;
        if !given_ops(p, cx.tys, h) {
            return Err(AlphaError::Later(GIVES_BACK));
        }
        let clauses: Vec<BodyId> = p
            .handlers
            .get(h.index())
            .map(|d| d.clauses.iter().map(|(_, c)| *c).collect())
            .unwrap_or_default();
        let s0 = gv.state(&start);
        for cb in clauses {
            let vals = gv.values(cx, cb)?;
            let run = run_clause(cx, h, cb, (&s0, gv.frame), &vals)?;
            if let Some(a) = run.after {
                st.join(&a);
            }
            if let Some(x) = run.abort {
                match &mut abort {
                    Some(a) => {
                        a.join(&x);
                    }
                    None => abort = Some(x),
                }
            }
        }
    }
    // The abort edge of the call: the state before it, and the states of
    // the clauses where they abort.
    cx.hx.abort_edge = abort.map(AbortEdge::Join);
    Ok(())
}

/// Why a call that runs a clause is not in scope ([`given_ops`]).
pub const GIVES_BACK: &str = "a call that runs a clause of a local handler whose operation gives a function value or a reference back to the callee (stage F16)";

/// True if call `t` of body `body` runs a clause of a local handler.
pub fn runs_clauses(cx: &Cx<'_>, body: BodyId, t: &TermKind) -> bool {
    matches!(t, TermKind::Call { .. }) && !call_handlers(cx, body, t).is_empty()
}

/// The transfer of a perform through the capability `cap` of a local
/// handler: the run of the clause ([`perform_run`]), then the destination
/// gets the result.
///
/// # Errors
///
/// The errors of [`perform_run`].
pub fn perform_local(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    (cap, op, args): (&Place, weft_ir::OpIdx, &[Operand]),
    dest: &Place,
) -> Result<(), AlphaError> {
    let out = perform_run(cx, body, st, cap, op, args)?;
    let abort = out.abort.map(AbortEdge::Replace);
    *st = out.after;
    transfer::bind_result(cx, body, st, &[], dest, out.value)?;
    // The abort edge of the perform: the states of the clause where it
    // aborts (`super::edges` takes it).
    cx.hx.abort_edge = abort;
    Ok(())
}

/// The transfer of a `Resume` in the facts of a clause body (its component).
///
/// The destination gets what a `resume` of the handler gives back, and the
/// locals that are not of the clause get the state at the end of the
/// handled body ([`Info`]).
///
/// # Errors
///
/// The errors of α, and [`AlphaError::Later`] for a continuation that the
/// analysis does not know (a continuation in the environment of a closure).
pub fn resume(
    cx: &mut Cx<'_>,
    body: BodyId,
    st: &mut State,
    (kont, arg, dest): (&Place, &Operand, &Place),
) -> Result<(), AlphaError> {
    let p = cx.p;
    let (h, _, _) = kont_handler(p, body, kont)
        .ok_or(AlphaError::Later("a continuation in a closure (stage F16)"))?;
    handler(p, h)?;
    let info = cx.hx.info(h).cloned().unwrap_or_default();
    resume_with(
        cx,
        body,
        st,
        (kont, arg, dest),
        info.exit.as_ref(),
        &info.resumed,
    )
}
