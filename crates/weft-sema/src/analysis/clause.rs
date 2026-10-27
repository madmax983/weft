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
//! with no `resume` aborts to its handler (stage F15 makes the edges of the
//! abort; the state of such an end joins the state after the `handle`).
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
    after.remove_bodies(&|b| inside(p, b, hb) || clauses.iter().any(|&c| inside(p, b, c)));
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
    let (after, value, landing) = run_clause(cx, h, cb, &s0, &vals)?;
    // A clause with no resume point: the code after the perform does not
    // run, and any state is right there.
    let after = after.unwrap_or(s0);
    Ok(PerformOut {
        handler: h,
        clause: cb,
        args: vals,
        after,
        value,
        landing,
    })
}

/// The run of clause body `cb` of handler `h` from the state `s0`, with the
/// values `vals` of its parameters, up to its resume points.
///
/// Returns the join of the states at the resume points with no local of the
/// clause (none if the clause has no resume point), and the join of the
/// values that the clause gives to `resume`. The state `s0` joins the seed
/// of the facts of the clause; the open run of the handler gets the states
/// at the resume points and at each end with no `resume`.
///
/// # Errors
///
/// The errors of the transfer functions.
fn run_clause(
    cx: &mut Cx<'_>,
    h: HandlerId,
    cb: BodyId,
    s0: &State,
    vals: &[Tree],
) -> Result<(Option<State>, Tree, Tree), AlphaError> {
    let p = cx.p;
    let cbody = body_of(p, cb)?;
    {
        let info = cx.hx.info.entry(h).or_default();
        match info.seeds.get_mut(&cb) {
            Some(s) => {
                s.join(s0);
            }
            None => {
                info.seeds.insert(cb, s0.clone());
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
        let mut s = sr.clone();
        s.remove_bodies(&mine);
        match &mut after {
            Some(a) => {
                a.join(&s);
            }
            None => after = Some(s),
        }
        if let Some(o) = cx.hx.open_mut(h) {
            o.resumes.push((cb, *rb, sr.clone()));
        }
    }
    // A clause that ends with no `resume` aborts to its handler.
    let mut landing = Tree::none();
    for sret in ends.returns.values() {
        let v = sret.value((cb, cbody.ret), &[]);
        landing.join(&v);
        let mut s = sret.clone();
        s.remove_bodies(&mine);
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
    Ok((after, value, landing))
}

/// The local handlers whose clauses a call can run.
///
/// They are the handlers of the destinations of the aborts of call `t` of
/// body `body` (an effect of the row of the callee, or a failure, that
/// resolves to a handler of the
/// component, `crate::factgen::frames`).
pub fn call_handlers(cx: &Cx<'_>, body: BodyId, t: &TermKind) -> Vec<HandlerId> {
    let mut out: Vec<HandlerId> =
        crate::factgen::frames::destinations(cx.p, cx.tys, cx.sums, body, t)
            .into_iter()
            .filter_map(|d| match d {
                crate::factgen::frames::Dest::Handler { handler, .. } => Some(handler),
                crate::factgen::frames::Dest::Past => None,
            })
            .collect();
    out.sort();
    out.dedup();
    out
}

/// True if the operations of the clauses of handler `h` hold no reference.
///
/// No parameter and no result of an operation of a clause of the handler
/// can hold a reference, a function value or a value of a type parameter: a
/// call that runs the clause does not need the places of the arguments that
/// the callee gives (plan stage F14).
pub fn plain_ops(p: &Program, tys: &weft_ir::TyTable, h: HandlerId) -> bool {
    let Some(hd) = p.handlers.get(h.index()) else {
        return false;
    };
    let Some(e) = tys.effects().get(hd.effect.index()) else {
        return false;
    };
    let plain = |t: weft_ir::TyId| {
        let pr = crate::props::ir_props(tys, t);
        !pr.holds_refs && !pr.generic && !pr.callable && !crate::props::ir_has_fns(tys, t)
    };
    hd.clauses.iter().all(|(op, _)| {
        e.ops
            .get(op.index())
            .is_some_and(|o| o.params.iter().all(|&t| plain(t)) && plain(o.ret))
    })
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
    body: BodyId,
    st: &State,
    t: &TermKind,
) -> Result<Vec<(HandlerId, Tree)>, AlphaError> {
    let p = cx.p;
    let mut out = Vec::new();
    for h in call_handlers(cx, body, t) {
        handler(p, h)?;
        let clauses: Vec<BodyId> = p
            .handlers
            .get(h.index())
            .map(|d| d.clauses.iter().map(|(_, c)| *c).collect())
            .unwrap_or_default();
        let mut v = Tree::none();
        for cb in clauses {
            let n = body_of(p, cb)?.params.len();
            let vals = vec![Tree::leaf(AbsVal::plain()); n];
            let (_, _, landing) = run_clause(cx, h, cb, st, &vals)?;
            v.join(&landing);
        }
        out.push((h, v));
    }
    Ok(out)
}

/// The clauses that a call runs (plan stage F14).
///
/// After the transfer of call `t` of body `body`, each clause of each local
/// handler that the
/// callee can perform through (or fail to) runs up to its resume points
/// from the state `st` after the call, with parameters that hold no
/// reference. The state after the call is the join of `st` and the states
/// at the resume points.
///
/// # Errors
///
/// The errors of the transfer functions, and [`AlphaError::Later`] for a
/// clause whose operation has a parameter or a result with a reference.
pub fn call_clauses(cx: &mut Cx<'_>, body: BodyId, st: &mut State, t: &TermKind) -> R {
    let p = cx.p;
    let hs = call_handlers(cx, body, t);
    if hs.is_empty() {
        return Ok(());
    }
    let start = st.clone();
    for h in hs {
        handler(p, h)?;
        if !plain_ops(p, cx.tys, h) {
            return Err(AlphaError::Later(
                "a call that runs a clause of a local handler whose operation has a reference (stage F15)",
            ));
        }
        let clauses: Vec<BodyId> = p
            .handlers
            .get(h.index())
            .map(|d| d.clauses.iter().map(|(_, c)| *c).collect())
            .unwrap_or_default();
        for cb in clauses {
            let n = body_of(p, cb)?.params.len();
            let vals = vec![Tree::leaf(AbsVal::plain()); n];
            let (after, _, _) = run_clause(cx, h, cb, &start, &vals)?;
            if let Some(a) = after {
                st.join(&a);
            }
        }
    }
    Ok(())
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
    *st = out.after;
    transfer::bind_result(cx, body, st, &[], dest, out.value)
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
