//! Handlers in the facts (`docs/ir.md` 6.2 to 6.5 and 6.7; plan stage F14).
//!
//! - A `handle` has the nodes `Main`, `Exit` and `Post`. Its handled body
//!   splices into the component of its site between `Main` and `Exit`
//!   (`super::nodes::NodeTable::splice`). `Main` gives the handler its id,
//!   and the capability local of the handled body binds there
//!   ([`handle_main`]). At `Exit` the value of the handled body is used and
//!   the value of the `handle` binds to its destination ([`handle_exit`]).
//!   At `Post` the code of each clause after its resume points runs
//!   ([`handle_post`]).
//! - A perform through the capability of a local handler is checked as a
//!   call: its arguments are call arguments with the roots of the
//!   parameters, and the node gets the code of the clause before its first
//!   resume point ([`perform_local`]).
//! - A clause body is a component of the facts of its function: a node
//!   `clause entry` where its parameters and its continuation bind
//!   ([`clause_entry`]), then its nodes. A `Resume` uses the continuation
//!   (W0501 for a second `resume` of a `once` continuation) and gives back
//!   what the analysis says ([`resume`]).
//! - [`project`]: after the facts of each component of the function, the
//!   facts of the nodes of each clause go to the nodes that run the clause.
//!   The nodes of a clause from its entry up to and with its resume points
//!   are the `pre` part: their facts go to each perform that runs the clause,
//!   with the places of the parameters of the clause mapped to the places of
//!   the arguments (σ). The nodes after a resume point are the `post` part:
//!   their facts go to the `Post` node of the `handle`, with σ of each
//!   perform. A variable or a place of a local of the clause stays in the
//!   clause. A change of a place of the site by a clause is checked against
//!   the arguments of the perform (W0312, as a call). At each `Resume` the
//!   rest of the handled body runs: the `Resume` node lends each place that
//!   the handled body changes after a perform of the clause, and frees each
//!   place that it frees there, also through the parameters of the clause.
//! - A call that runs a clause (plan stages F14, F15) is a run node of the
//!   clause too: σ of a parameter is the places that the call gives
//!   (`clause::given`), and a change through it has the callee root of the
//!   argument that reaches it ([`call_clauses`]).
//! - A clause that can run more than once runs its `post` part at `Post`
//!   once for each run (`Post` is in a cycle through a `Copy` node); an
//!   abort to a local handler binds the captured locals that no path
//!   assigned ([`unbound_at_aborts`], plan stage F15).
//! - A `multi` resume runs the code after each node that runs its clause
//!   again: an edge from `Post` to the `Copy` node of the node, where the
//!   locals of the copied frames get new values ([`copy_node`], plan stage
//!   F16).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use weft_facts::{CapId, FnFacts, HandlerInfo, NodeId, PlaceId, VarId};
use weft_ir::{BlockId, BodyId, BodyKind, HandlerId, Place, Program, TermKind, TyTable};

use super::alpha::{AlphaError, Role, Roots};
use super::nodes::{NodeKey, NodeTable, Phase, NORMAL, TERM};
use super::templates::{bind_dest, deep_uses, named_refs, operand_moves, CallNodes, Em, Stored};
use super::vars::{VarKey, Vars};
use crate::analysis::clause::{self, inside, ClauseRun, Handlers};
use crate::analysis::domain::{State, Tree};
use crate::analysis::transfer;

/// The result of a template.
type R = Result<(), AlphaError>;

/// The nodes of the component by body, and the bodies below each body: the
/// passes over the clauses read these, not the whole node table (a function
/// with many `handle`s, `s5/h4000.wf`).
struct Index {
    /// The nodes of each body.
    by_body: HashMap<BodyId, Vec<(NodeKey, NodeId)>>,
    /// The bodies whose parent is each body.
    kids: HashMap<BodyId, Vec<BodyId>>,
}

impl Index {
    /// The index of the node table `table`.
    fn new(p: &Program, table: &NodeTable) -> Self {
        let mut by_body: HashMap<BodyId, Vec<(NodeKey, NodeId)>> = HashMap::new();
        for (k, &n) in table.iter() {
            by_body.entry(k.body).or_default().push((*k, n));
        }
        let mut kids: HashMap<BodyId, Vec<BodyId>> = HashMap::new();
        for (i, b) in p.bodies.iter().enumerate() {
            if let Some(parent) = b.parent {
                kids.entry(parent)
                    .or_default()
                    .push(BodyId(u32::try_from(i).unwrap_or(u32::MAX)));
            }
        }
        Self { by_body, kids }
    }

    /// Body `b` and each body below it (`inside(p, x, b)`).
    fn subtree(&self, b: BodyId) -> Vec<BodyId> {
        let mut out = vec![b];
        let mut i = 0;
        while let Some(&x) = out.get(i) {
            i += 1;
            out.extend(self.kids.get(&x).into_iter().flatten().copied());
        }
        out
    }

    /// The nodes of the bodies `bodies`.
    fn nodes<'a>(&'a self, bodies: &'a [BodyId]) -> impl Iterator<Item = &'a (NodeKey, NodeId)> {
        bodies
            .iter()
            .flat_map(|b| self.by_body.get(b).into_iter().flatten())
    }

    /// The nodes of the bodies that splice into the component below body
    /// `hb` (with `hb`): the nodes of a handled body and of the handled
    /// bodies inside it.
    fn spliced_nodes(&self, p: &Program, hb: BodyId, normal: bool) -> HashSet<NodeId> {
        let bodies: Vec<BodyId> = self
            .subtree(hb)
            .into_iter()
            .filter(|&b| splice_root(p, b) != b)
            .collect();
        self.nodes(&bodies)
            .filter(|(k, _)| !normal || k.dest == NORMAL)
            .map(|(_, n)| *n)
            .collect()
    }
}

/// The body that the nodes of body `b` splice into: the site of a handled
/// body (through each handled body on the way), or `b` itself.
pub fn splice_root(p: &Program, b: BodyId) -> BodyId {
    let mut at = b;
    for _ in 0..=p.bodies.len() {
        let Some(x) = p.bodies.get(at.index()) else {
            return at;
        };
        match (x.kind, x.parent) {
            (BodyKind::Handled(_), Some(site)) => at = site,
            _ => return at,
        }
    }
    at
}

/// The bodies whose nodes splice into body `root` (`root` first), in the
/// order of their ids.
pub fn spliced(p: &Program, comp: &[BodyId], root: BodyId) -> Vec<BodyId> {
    let mut out: Vec<BodyId> = comp
        .iter()
        .copied()
        .filter(|&b| b == root || splice_root(p, b) == root)
        .collect();
    out.sort();
    out.dedup();
    out
}

/// The handler id and the capability id of handler `h` in the facts: made
/// at the first use.
fn ids(em: &mut Em<'_>, h: HandlerId) -> (weft_facts::HandlerId, CapId) {
    if let Some(&x) = em.hx.ids.get(&h) {
        return x;
    }
    let hd = em.p.handlers.get(h.index());
    let effect = hd
        .and_then(|d| em.tys.effects().get(d.effect.index()))
        .map(|e| e.identity.clone())
        .unwrap_or_default();
    let span = hd.and_then(|d| em.p.bodies.get(d.handled.index())).map_or(
        weft_facts::Span { lo: 0, hi: 0 },
        |b| weft_facts::Span {
            lo: b.origin.span.lo,
            hi: b.origin.span.hi,
        },
    );
    let hid = weft_facts::HandlerId(u32::try_from(em.facts.handlers.len()).unwrap_or(u32::MAX));
    em.facts.handlers.push(HandlerInfo {
        effect,
        sim_root: false,
        span,
    });
    let cap = em.facts.add_cap();
    em.hx.ids.insert(h, (hid, cap));
    (hid, cap)
}

/// `Handle` `Main` (`docs/ir.md` 6.4): the handler gets its id
/// (`handler(H, E)`), and the capability local of the handled body binds.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] for a handler that does not exist.
pub fn handle_main(em: &mut Em<'_>, n: NodeId, h: HandlerId) -> R {
    ids(em, h);
    let hb =
        em.p.handlers
            .get(h.index())
            .map(|d| d.handled)
            .ok_or_else(|| AlphaError::BadPlace(format!("no handler h{}", h.0)))?;
    // A clause that can resume a `multi` continuation more than once: each
    // node that runs it is a `multi` point (`multi_at`, W0503).
    if clause::multi_twice(em.p, h) {
        let (_, cap) = ids(em, h);
        em.facts.clause_multi.push(cap);
    }
    let caps: Vec<_> =
        em.p.body(hb)
            .map(|b| b.caps.iter().map(|(_, l)| *l).collect())
            .unwrap_or_default();
    for c in caps {
        if let Some(s) = em.vars.get(&VarKey::S(hb, c)) {
            em.facts.rebound_at.push((s, n));
            em.facts.empty_at.push((s, n));
        }
    }
    Ok(())
}

/// `Handle` `Exit` (`docs/ir.md` 6.4).
///
/// `_0` of the handled body is used, and the value `value` of the `handle`
/// binds to its destination `dest` (a place of the site), in the state `st`
/// at the end of the handled body.
///
/// # Errors
///
/// The errors of α.
pub fn handle_exit(
    em: &mut Em<'_>,
    n: NodeId,
    st: &State,
    h: HandlerId,
    dest: &Place,
    value: &Tree,
) -> R {
    let hb =
        em.p.handlers
            .get(h.index())
            .map(|d| d.handled)
            .ok_or_else(|| AlphaError::BadPlace(format!("no handler h{}", h.0)))?;
    if let Some(ret) = em.p.body(hb).map(|b| b.ret) {
        let k = transfer::key(em.p, hb, ret)?;
        if let Some(s) = em.s_var(k) {
            em.facts.uses.push((s, n));
            // The value leaves the handled body (to a `resume` of a clause,
            // or to the destination): a linear value of `_0` ends there, so
            // a re-run of a `multi` handler gives `_0` a new one.
            if em.facts.var(s).linear {
                em.facts.moved_at.push((s, n));
            }
        }
        let vars = em.vars;
        em.facts.uses.extend(
            vars.parts_of(k.0, k.1)
                .iter()
                .filter(|(kind, _, _)| *kind == super::vars::PartKind::H)
                .map(|(_, _, v)| (*v, n)),
        );
    }
    bind_dest(em, n, st, dest, value)
}

/// `Handle` `Post` (`docs/ir.md` 6.4).
///
/// The code of each clause after its resume points runs at each node of
/// `posts` ([`project`]): `Post` (in a cycle if a clause can run more than
/// once, plan stages F15 and F16). The frames of the clauses end at each
/// one.
pub fn handle_post(
    em: &mut Em<'_>,
    exit: Option<NodeId>,
    posts: &[NodeId],
    (h, spares): (HandlerId, Option<Vec<BodyId>>),
) {
    let clauses: Vec<BodyId> =
        em.p.handlers
            .get(h.index())
            .map(|d| d.clauses.iter().map(|(_, c)| *c).collect())
            .unwrap_or_default();
    for &n in posts {
        for &clause in &clauses {
            em.hx.runs.push(ClauseRun {
                node: n,
                handler: h,
                clause,
                post: true,
                args: Vec::new(),
                helds: Vec::new(),
                deps: Vec::new(),
                at: em.body,
                spares: spares.clone(),
                ins: Vec::new(),
                given: None,
            });
        }
    }
    if let Some(&first) = posts.first() {
        for &n in posts {
            em.hx.ends.push((h, exit.unwrap_or(first), n));
        }
    }
}

/// A `Perform` through the capability of a local handler (`docs/ir.md` 6.4,
/// 6.7): its nodes `Main` and `Ret`.
///
/// - `Main`: a read of the capability; the operands; each argument is a
///   call argument with the root of its parameter (`call_arg`, a read of its
///   places); `performs_at` of the capability; `may_abort`; the code of the
///   clause before its first resume point ([`project`]).
/// - `Ret`: the result (what the clause gives to `resume`) binds to `dest`,
///   in the state after the code of the clause.
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for a function value that the perform
/// gives to the handler (stage F16), and the errors of α and of the
/// analysis.
pub fn perform_local(
    em: &mut Em<'_>,
    nodes: &CallNodes,
    st: &State,
    block: BlockId,
    t: &TermKind,
) -> R {
    let TermKind::Perform {
        cap: weft_ir::CapOperand::Local(cap),
        op,
        args,
        dest,
        ..
    } = t
    else {
        return Err(AlphaError::BadPlace(
            "a perform through the capability of a caller".to_string(),
        ));
    };
    let body = em.body;
    // A function value that the perform gives to the clause (O3-7, plan
    // stage F16): the parameter of the clause holds it in the facts of the
    // clause (`Info::params`), so a run of it in the clause changes the
    // places of its environment there, and the changes reach the perform
    // with the code of the clause.
    let out = clause::perform_run(&mut em.cx(), body, st, cap, *op, args)?;
    let n = nodes.main;
    // The perform reads the capability.
    operand_moves(
        em,
        n,
        st,
        &weft_ir::Operand::Copy(cap.clone()),
        false,
        false,
    )?;
    for a in args {
        operand_moves(em, n, st, a, false, true)?;
        let v = transfer::operand(&mut em.cx(), body, st, a)?;
        let refs = named_refs(em, v.flat().refs);
        deep_uses(em, n, st, a, &refs)?;
    }
    let params: Vec<(weft_ir::TyId, weft_ir::TyId)> =
        em.p.body(out.clause)
            .map(|b| {
                b.params
                    .iter()
                    .filter_map(|&l| b.local(l).map(|d| (d.ty, d.ty)))
                    .collect()
            })
            .unwrap_or_default();
    let inst = transfer::run_inst(body, block);
    let s = crate::analysis::apply::sigma_with(&mut em.cx(), body, st, &params, args, inst)?;
    // A parameter of the operation with an `in` place has the root of the
    // parameter of its place, and its argument must point inside the place
    // (W0203), as for a function (R3RT7).
    let places = op_places(em, out.clause);
    let ins = in_roots(&places, s.args.len());
    for (i, ps) in s.args.iter().enumerate() {
        let root = crate::body::roots::param(ins.get(i).copied().unwrap_or(i));
        for &q in ps {
            em.facts.reads_at.push((n, q));
            em.facts.call_arg.push((n, q, root));
        }
    }
    check_in_places(em, (n, out.clause), &s, args, &places)?;
    // A function value that the perform gives to the clause: the places of
    // its environment are an argument (O3-7, plan stage F16; a change of the
    // clause there is W0312, as for a call).
    for (i, a) in args.iter().enumerate() {
        if transfer::reach_fns(&mut em.cx(), body, st, a)?.is_empty() {
            continue;
        }
        let root = crate::body::roots::fn_arg(i);
        let mut refs: Vec<PlaceId> = transfer::operand(&mut em.cx(), body, st, a)?
            .flat()
            .refs
            .into_iter()
            .collect();
        refs.extend(transfer::reach_refs(&mut em.cx(), body, st, a)?);
        refs.sort();
        refs.dedup();
        for q in refs {
            em.facts.reads_at.push((n, q));
            em.facts.call_arg.push((n, q, root));
        }
    }
    let (_, cap_id) = ids(em, out.handler);
    em.facts.performs_at.push((n, cap_id));
    if nodes.may_abort {
        em.facts.may_abort.push(n);
    }
    // The value of the `handle` binds at the `AbortValue` node of the abort
    // to the handler: the value of the clause where it ends with no `resume`
    // (the frames of the handled body unwind after it, `docs/ir.md` 6.5).
    let own = super::frames::FIRST_HANDLER.saturating_add(out.handler.0);
    if let Some((_, av)) = nodes.values.iter().find(|(d, _)| *d == own) {
        bind_handle(em, *av, &out.after, out.handler, &out.landing)?;
    }
    let spared = spares(em, body, t);
    em.hx.runs.push(ClauseRun {
        node: n,
        handler: out.handler,
        clause: out.clause,
        post: false,
        args: s.args,
        helds: s.helds,
        deps: s.deps,
        at: body,
        spares: spared,
        ins,
        given: None,
    });
    if let Some(r) = nodes.ret {
        // A `multi` resume gives the perform the values of the later
        // `resume`s too (plan stage F16).
        let mut value = out.value.clone();
        if let Some((_, v)) = em.hx.reentry.get(&(body, block)) {
            value.join(v);
        }
        bind_dest(em, r, &out.after, dest, &value)?;
    }
    Ok(())
}

/// The operation of clause `clause` in the program of the old lowering (an
/// effect of the IR has the index of its effect there).
fn op_def<'a>(em: &Em<'a>, clause: BodyId) -> Option<&'a crate::program::OpDef> {
    let Some(weft_ir::BodyKind::Clause(h, op)) = em.p.body(clause).map(|b| b.kind) else {
        return None;
    };
    let e = em.p.handlers.get(h.index())?.effect;
    em.sema.effects.get(e.index())?.ops.get(op.index())
}

/// The `in` place of each parameter of the operation of clause `clause`, if
/// it states one (R3RT7).
fn op_places(em: &Em<'_>, clause: BodyId) -> Vec<Option<crate::program::SigPlace>> {
    op_def(em, clause)
        .map(|o| o.places.clone())
        .unwrap_or_default()
}

/// The parameter whose root each of `n` parameters has: a parameter with an
/// `in` place has the root of the parameter of its place, as a parameter of
/// a function (ADR 0005).
fn in_roots(places: &[Option<crate::program::SigPlace>], n: usize) -> Vec<usize> {
    (0..n)
        .map(|i| {
            let mut j = i;
            for _ in 0..=n {
                match places.get(j).and_then(Option::as_ref).map(|sp| &sp.root) {
                    Some(crate::program::SigRoot::Param(k)) if *k != j => j = *k,
                    _ => break,
                }
            }
            j
        })
        .collect()
}

/// W0203 at the perform node `n` that runs clause `clause`: the argument of
/// a parameter with an `in` place points inside the place (`param_in`,
/// `arg_at`, R3RT7), as the checks of a call do
/// (`crate::analysis::apply::check_args`).
///
/// # Errors
///
/// The errors of α.
fn check_in_places(
    em: &mut Em<'_>,
    (n, clause): (NodeId, BodyId),
    s: &crate::analysis::apply::Sigma,
    args: &[weft_ir::Operand],
    places: &[Option<crate::program::SigPlace>],
) -> R {
    if places.iter().all(Option::is_none) {
        return Ok(());
    }
    let Some(op) = op_def(em, clause) else {
        return Ok(());
    };
    let mut sum = crate::analysis::Summary::default();
    for (i, sp) in places.iter().enumerate() {
        sum.params.push(crate::analysis::summary::ParamIface {
            name: op
                .param_names
                .get(i)
                .cloned()
                .unwrap_or_else(|| format!("parameter {i}")),
            root: crate::body::roots::param(i),
            in_place: sp.as_ref().map(crate::analysis::sig::sig_place),
        });
    }
    let at = em.facts.node(n).span;
    let spans: Vec<weft_facts::Span> = args
        .iter()
        .map(|a| super::templates::operand_span(em, a, at))
        .collect();
    let site = crate::analysis::apply::Site {
        callee: &op.name,
        spans,
        bases: vec![Vec::new(); args.len()],
    };
    crate::analysis::apply::check_args(&mut em.cx(), n, &sum, s, &site)
}

/// The handled bodies of the local handlers of the aborts of a terminator.
///
/// They are the handlers that each abort of terminator `t` of body `body`
/// goes to, if each abort goes to one (none if an abort can go past the
/// function, `super::frames`).
fn spares(em: &Em<'_>, body: BodyId, t: &TermKind) -> Option<Vec<BodyId>> {
    let ds = super::frames::destinations(em.p, em.tys, em.sums, body, t);
    let mut out = Vec::new();
    for d in ds {
        match d {
            super::frames::Dest::Handler { handler, .. } => {
                out.push(em.p.handlers.get(handler.index())?.handled);
            }
            super::frames::Dest::Past => return None,
        }
    }
    // The handler of a clause that resumes on each path is no destination
    // (plan stage F15), but the node still suspends the handled body: the
    // values inside it are not spared (ADR 0005).
    for h in super::frames::clause_handlers(em.p, em.tys, em.sums, body, t) {
        out.push(em.p.handlers.get(h.index())?.handled);
    }
    out.sort();
    out.dedup();
    Some(out)
}

/// A call that runs clauses of local handlers (plan stages F14, F15).
///
/// Its `Main` node performs through the capability of each handler
/// (no `escapes_at` of the effect of the handler), and the code of each
/// clause before its resume points runs there ([`project`]). σ of a
/// parameter of a clause that can hold a reference is the places that the
/// call gives (`clause::given`: the callee frame root and what the
/// arguments reach); a change through it is no change of an argument of
/// the call (no `call_mut`: the callee gives the place, as it lends a place
/// to an operation of a caller).
pub fn call_clauses(em: &mut Em<'_>, nodes: &CallNodes, st: &State, t: &TermKind) -> R {
    let n = nodes.main;
    let body = em.body;
    let block = em.at.0;
    // The value of the `handle` binds at the `AbortValue` node of an abort
    // to its handler.
    let landings = clause::call_landings(&mut em.cx(), (body, block), st, t)?;
    for (h, v) in landings {
        if let Some((_, av)) = nodes
            .values
            .iter()
            .find(|(d, _)| *d == super::frames::FIRST_HANDLER.saturating_add(h.0))
        {
            bind_handle(em, *av, st, h, &v)?;
        }
    }
    let hs = clause::call_handlers(&em.cx(), body, t);
    let gv = if hs.is_empty() {
        clause::Given::default()
    } else {
        clause::given(&mut em.cx(), body, block, st, t)?
    };
    for h in hs {
        let (_, cap) = ids(em, h);
        em.facts.performs_at.push((n, cap));
        // The effect of the handler does not leave the function there: the
        // local handler handles it (W0702, W0805).
        let effect =
            em.p.handlers
                .get(h.index())
                .and_then(|d| em.tys.effects().get(d.effect.index()))
                .map(|e| e.identity.clone());
        if let Some(e) = effect {
            let at = |x: &NodeId| *x == n || Some(*x) == nodes.ret;
            em.facts.escapes_at.retain(|(x, f)| !at(x) || *f != e);
        }
        let clauses: Vec<BodyId> =
            em.p.handlers
                .get(h.index())
                .map(|d| d.clauses.iter().map(|(_, c)| *c).collect())
                .unwrap_or_default();
        for clause in clauses {
            let (args, deps) = gv.sigma(em.p, em.tys, clause);
            em.hx.runs.push(ClauseRun {
                node: n,
                handler: h,
                clause,
                post: false,
                helds: args.clone(),
                args,
                deps,
                at: body,
                spares: None,
                ins: Vec::new(),
                given: Some(gv.roots.clone()),
            });
        }
    }
    Ok(())
}

/// The locals of body `body` that no path from its entry to the terminator
/// of block `block` assigns (plan stage F15). The sets are computed once
/// for each body (`Handlers::assigned`).
fn unassigned(
    p: &Program,
    hx: &mut Handlers,
    body: BodyId,
    block: BlockId,
) -> Vec<weft_ir::LocalId> {
    let Some(b) = p.body(body) else {
        return Vec::new();
    };
    let words = b.locals.len().div_ceil(64);
    let sets = hx.assigned.entry(body).or_insert_with(|| {
        let set = |v: &mut [u64], l: weft_ir::LocalId| {
            if let Some(w) = v.get_mut(l.index() / 64) {
                *w |= 1u64 << (l.index() % 64);
            }
        };
        // The locals that each block assigns before its terminator, and
        // what its terminator gives to its normal successors.
        let mut own: Vec<Vec<u64>> = vec![vec![0; words]; b.blocks.len()];
        let mut out_term: Vec<Vec<u64>> = vec![vec![0; words]; b.blocks.len()];
        for (i, blk) in b.blocks.iter().enumerate() {
            for st in &blk.stmts {
                if let weft_ir::StmtKind::Assign(q, _) = &st.kind {
                    if let Some(v) = own.get_mut(i) {
                        set(v, q.local);
                    }
                }
            }
            let dest = match &blk.term.kind {
                TermKind::Call { dest, .. }
                | TermKind::Perform { dest, .. }
                | TermKind::Resume { dest, .. }
                | TermKind::Handle { dest, .. }
                | TermKind::IterNext { dest, .. } => Some(dest.local),
                _ => None,
            };
            if let (Some(l), Some(v)) = (dest, out_term.get_mut(i)) {
                set(v, l);
            }
        }
        // A forward may analysis: the set at the terminator of a block is
        // the join of the sets of its predecessors and its own statements.
        let mut at: Vec<Vec<u64>> = own.clone();
        let mut work: Vec<usize> = (0..b.blocks.len()).collect();
        while let Some(i) = work.pop() {
            let Some(blk) = b.blocks.get(i) else {
                continue;
            };
            let mut give = at.get(i).cloned().unwrap_or_default();
            for (g, t) in give.iter_mut().zip(out_term.get(i).into_iter().flatten()) {
                *g |= *t;
            }
            for s in blk.term.kind.successors() {
                let Some(dst) = at.get_mut(s.index()) else {
                    continue;
                };
                let mut grew = false;
                for (d, g) in dst.iter_mut().zip(&give) {
                    let n = *d | *g;
                    grew |= n != *d;
                    *d = n;
                }
                if grew {
                    work.push(s.index());
                }
            }
        }
        at
    });
    let Some(set) = sets.get(block.index()) else {
        return Vec::new();
    };
    (0..b.locals.len())
        .filter(|&i| set.get(i / 64).is_some_and(|w| w & (1u64 << (i % 64)) == 0))
        .map(|i| weft_ir::LocalId(u32::try_from(i).unwrap_or(u32::MAX)))
        .collect()
}

/// The locals that bind at the `AbortValue` nodes of an abort.
///
/// `values` are the `AbortValue` nodes of the terminator of block `block` of
/// the body of `em` (an abort to a local handler, plan stage F15): each local
/// of the body that no path to the terminator assigns holds no reference
/// on the abort path, so it binds there (`rebound_at`). A closure that
/// the handled body made on another path can run after the `Landing`, and
/// the analysis joins its value with the values of the other paths
/// (`s5r/p/scale400.wf`): its use of a captured local is no use of an old
/// reference. Only a local that a closure captures (`Kept`, `ByRef`) and
/// that can hold a reference.
pub fn unbound_at_aborts(em: &mut Em<'_>, block: BlockId, values: &[(u32, NodeId)]) {
    if values.is_empty() {
        return;
    }
    let body = em.body;
    let p = em.p;
    let captured: HashSet<weft_ir::LocalId> = clause::captured_locals(p, body)
        .into_iter()
        .filter(|k| k.0 == body)
        .map(|k| k.1)
        .collect();
    if captured.is_empty() {
        return;
    }
    let ls = unassigned(p, em.hx, body, block);
    for l in ls.into_iter().filter(|l| captured.contains(l)) {
        // Only a local that can hold a reference: it gets no linear part
        // there (`empty_at`).
        let refs = p
            .body(body)
            .and_then(|b| b.local(l))
            .is_some_and(|d| d.props.holds_refs || crate::props::ir_has_fns(em.tys, d.ty));
        let Some(v) = em.vars.get(&VarKey::S(body, l)).filter(|_| refs) else {
            continue;
        };
        for &(_, n) in values {
            em.facts.rebound_at.push((v, n));
            em.facts.empty_at.push((v, n));
        }
    }
}

/// The value `v` of the `handle` of handler `h` binds to its destination at
/// node `n` (the `AbortValue` node of an abort to the handler, plan stage
/// F15 in its first form), in the state `st`.
///
/// # Errors
///
/// The errors of α.
fn bind_handle(em: &mut Em<'_>, n: NodeId, st: &State, h: HandlerId, v: &Tree) -> R {
    let Some(site) = em.p.handlers.get(h.index()).map(|d| d.site) else {
        return Ok(());
    };
    let dest = em.p.body(site).and_then(|b| {
        b.blocks.iter().find_map(|blk| match &blk.term.kind {
            TermKind::Handle { handler, dest, .. } if *handler == h && !blk.cleanup => {
                Some(dest.clone())
            }
            _ => None,
        })
    });
    let Some(dest) = dest else {
        return Ok(());
    };
    let saved = em.body;
    em.body = site;
    let r = bind_dest(em, n, st, &dest, v);
    em.body = saved;
    r
}

/// A `Resume` of a clause (`docs/ir.md` 6.4, plan stage F14): its nodes
/// `Main` and `Ret`.
///
/// - `Main`: the operand; a use of the continuation, and its move for a
///   `once` continuation (W0501); `resumes_at` of the capability;
///   `may_abort`; the rest of the handled body ([`project`]).
/// - `Ret`: the value of the handled body (or of a clause that resumed)
///   binds to `dest`.
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for a continuation that the fact generator
/// does not know (in a closure, or in a body inside the clause), and the
/// errors of α.
pub fn resume(em: &mut Em<'_>, nodes: &CallNodes, st: &State, t: &TermKind) -> R {
    let TermKind::Resume {
        kont, arg, dest, ..
    } = t
    else {
        return Err(AlphaError::BadPlace("not a resume".to_string()));
    };
    let body = em.body;
    let (h, cb, multi) = clause::kont_handler(em.p, body, kont)
        .ok_or(AlphaError::Later("a captured continuation (stage F16)"))?;
    if cb != body {
        return Err(AlphaError::Later(
            "a `resume` in a body inside the clause (stage F16)",
        ));
    }
    let n = nodes.main;
    operand_moves(em, n, st, arg, false, true)?;
    // The `resume` reads the continuation, and a `once` continuation moves
    // (W0501).
    operand_moves(
        em,
        n,
        st,
        &weft_ir::Operand::Copy(kont.clone()),
        false,
        false,
    )?;
    let k = em.key(kont.local)?;
    if let (Some(s), false) = (em.s_var(k), multi) {
        em.facts.moved_at.push((s, n));
    }
    let (_, cap_id) = ids(em, h);
    em.facts.resumes_at.push((n, cap_id));
    if nodes.may_abort {
        em.facts.may_abort.push(n);
    }
    em.hx.resumes.push((n, h, cb));
    if let Some(r) = nodes.ret {
        let resumed = em.hx.info(h).map_or_else(Tree::none, |i| i.resumed.clone());
        bind_dest(em, r, st, dest, &resumed)?;
    }
    Ok(())
}

/// The `Copy` node `c` of a node of a handled body that runs a clause that
/// can resume more than once (`docs/ir.md` 6.5, plan stage F16).
///
/// A later `resume` runs the code after the node again, from a copy of the
/// frames of the handled body (`copy_frames` of the machine). Each
/// variable of a local of the copied frames whose value at the node points
/// only into the copied frames gets `rebound_at` and `empty_at`: the copy
/// is a new value. A variable that points outside them (a place of the
/// site, a parameter) keeps its state, so a reference that the first run
/// invalidates stays invalid in the second run (J4). A linear variable
/// gets no `empty_at`: the copy holds a copy of the linear value (W0503 at
/// the node). The node is terminator `t` of block `block` of the body of
/// `em` (a perform, or a call that runs the clause, or a node that waits
/// at a `multi` operation of a caller), and `st` is the state before it:
/// the frames are copied while the node waits. For a call, the
/// callee frame is a copied frame too, and the callee runs its code after
/// the perform again: the changes and the frees of the call apply again at
/// `c`.
pub fn copy_node(
    em: &mut Em<'_>,
    (c, main): (NodeId, NodeId),
    (block, root): (BlockId, BodyId),
    st: &State,
    t: &TermKind,
) {
    let p = em.p;
    let body = em.body;
    // The copied frames: the frames of body `root` (the handled body of a
    // local handler, or the body of a function or of a closure for a
    // handler of a caller), and of the bodies that splice into it.
    let hb = root;
    let frame = matches!(t, TermKind::Call { .. }).then(|| transfer::run_inst(body, block));
    let roots = &*em.roots;
    let facts = &*em.facts;
    let copied = |q: PlaceId| match roots.role(facts.place(q).root) {
        Some(Role::Local(k) | Role::Cell(k)) => {
            inside(p, k.0, hb) && !in_clause_or_closure(p, k.0, hb)
        }
        Some(Role::Frame(i)) => Some(i) == frame,
        _ => false,
    };
    // The locals whose value at the node points outside the copied frames
    // (or holds a task, which a copy cannot hold), and the locals that hold
    // a linear value. A closure value points into the places of its
    // captures.
    let mut outside: HashSet<(BodyId, weft_ir::LocalId)> = HashSet::new();
    let mut held_linear: HashSet<(BodyId, weft_ir::LocalId)> = HashSet::new();
    for (k, tree) in st.trees() {
        if !inside(p, k.0, hb) || in_clause_or_closure(p, k.0, hb) {
            continue;
        }
        let v = tree.flat();
        if !(v.tasks.is_empty()
            && v.refs.iter().all(|&q| copied(q))
            && v.caps.iter().all(|&q| copied(q)))
        {
            outside.insert(*k);
        }
        if v.linear {
            held_linear.insert(*k);
        }
    }
    // The locals that the node moves at `Main` (its callee value, and its
    // arguments but the ones that a callee holds to `Ret`): the frames are
    // copied while the node waits, after these moves, so the copies do not
    // hold them.
    let moved = moved_at_main(em, t);
    let fresh = |k: &(BodyId, weft_ir::LocalId)| {
        inside(p, k.0, hb)
            && !in_clause_or_closure(p, k.0, hb)
            && !outside.contains(k)
            && !moved.contains(k)
    };
    let mut vars: Vec<VarId> = Vec::new();
    let mut linear: HashSet<VarId> = HashSet::new();
    for key in em.vars.keys() {
        let local = match key {
            VarKey::S(b, l) | VarKey::C(b, l) => Some((*b, *l)),
            VarKey::H(b, q) | VarKey::U(b, q) | VarKey::W(b, q, _) => Some((*b, q.local)),
            _ => None,
        };
        let Some((b, l)) = local else {
            continue;
        };
        let Ok(k) = super::alpha::owner_local(p, b, l) else {
            continue;
        };
        if fresh(&k) {
            if let Some(v) = em.vars.get(key) {
                vars.push(v);
                if held_linear.contains(&k) {
                    linear.insert(v);
                }
            }
        }
    }
    // The callee frame of a call: the frame root of the call.
    // The value of the `handle` of a local handler: the value of the first
    // run went to the `resume` of the clause, not to the destination of the
    // `handle`, so a linear value there ends before the next run binds it.
    if let Some(BodyKind::Handled(h)) = p.body(hb).map(|b| b.kind) {
        if let Some(v) = handle_dest_var(em, h) {
            if em.facts.var(v).linear {
                em.facts.moved_at.push((v, c));
            }
        }
    }
    if let Some(i) = frame {
        for &(q, v) in &em.facts.owner {
            if matches!(roots.role(em.facts.place(q).root), Some(Role::Frame(j)) if j == i) {
                vars.push(v);
            }
        }
        // The callee runs its code after the perform again.
        let again: Vec<(NodeId, PlaceId)> = em
            .facts
            .mutates_at
            .iter()
            .filter(|(n, _)| *n == main)
            .map(|&(_, q)| (c, q))
            .collect();
        let lends: Vec<(NodeId, PlaceId)> = em
            .facts
            .lends_mut
            .iter()
            .filter(|(n, _)| *n == main)
            .map(|&(_, q)| (c, q))
            .collect();
        let frees: Vec<(NodeId, PlaceId)> = em
            .facts
            .releases_at
            .iter()
            .filter(|(n, _)| *n == main)
            .map(|&(_, q)| (c, q))
            .collect();
        em.facts.lends_mut.extend(again);
        em.facts.lends_mut.extend(lends);
        em.facts.releases_at.extend(frees);
    }
    vars.sort();
    vars.dedup();
    for v in vars {
        em.facts.rebound_at.push((v, c));
        if !linear.contains(&v) {
            em.facts.empty_at.push((v, c));
        }
    }
}

/// The whole locals that terminator `t` of the body of `em` moves at its
/// `Main` node: a moved callee value, and each moved argument but those of a
/// type parameter that the callee holds (they move at `Ret`).
fn moved_at_main(em: &Em<'_>, t: &TermKind) -> HashSet<(BodyId, weft_ir::LocalId)> {
    let p = em.p;
    let body = em.body;
    let mut ops: Vec<&weft_ir::Operand> = Vec::new();
    match t {
        TermKind::Call { callee, args, .. } => {
            let held: Vec<bool> = match callee {
                weft_ir::Callee::Fn(f, _) => {
                    let sum = em.sums.get(*f).ok();
                    let decl = p.fns.get(f.index());
                    (0..args.len())
                        .map(|i| match (sum, decl) {
                            (Some(s), Some(d)) => d.params.get(i).is_some_and(|&ty| {
                                s.holds
                                    .iter()
                                    .any(|&j| super::templates::mentions_index(em.tys, ty, j, 0))
                            }),
                            _ => false,
                        })
                        .collect()
                }
                weft_ir::Callee::Value(f) => {
                    ops.push(f);
                    vec![false; args.len()]
                }
            };
            ops.extend(
                args.iter()
                    .enumerate()
                    .filter(|(i, _)| !held.get(*i).copied().unwrap_or(false))
                    .map(|(_, a)| a),
            );
        }
        TermKind::Perform { args, .. } => ops.extend(args.iter()),
        _ => {}
    }
    ops.into_iter()
        .filter_map(|o| match o {
            weft_ir::Operand::Move(q) if q.proj.is_empty() => {
                super::alpha::owner_local(p, body, q.local).ok()
            }
            _ => None,
        })
        .collect()
}

/// The `S` variable of the destination of the `handle` of handler `h`, if
/// it is a whole local.
fn handle_dest_var(em: &Em<'_>, h: HandlerId) -> Option<VarId> {
    let site = em.p.handlers.get(h.index())?.site;
    let dest =
        em.p.body(site)?
            .blocks
            .iter()
            .find_map(|blk| match &blk.term.kind {
                TermKind::Handle { handler, dest, .. } if *handler == h && !blk.cleanup => {
                    Some(dest.clone())
                }
                _ => None,
            })?;
    if !dest.proj.is_empty() {
        return None;
    }
    let k = super::alpha::owner_local(em.p, site, dest.local).ok()?;
    em.vars.get(&VarKey::S(k.0, k.1))
}

/// True if body `b` (inside handled body `hb`) is in a clause body or a
/// closure body inside `hb`: its frames are not frames of the handled body.
fn in_clause_or_closure(p: &Program, b: BodyId, hb: BodyId) -> bool {
    let mut at = Some(b);
    for _ in 0..=p.bodies.len() {
        let Some(x) = at else {
            return false;
        };
        if x == hb {
            return false;
        }
        let Some(d) = p.body(x) else {
            return false;
        };
        if matches!(d.kind, BodyKind::Clause(..) | BodyKind::Closure(_)) {
            return true;
        }
        at = d.parent;
    }
    false
}

/// The entry node `n` of a clause body: its parameters bind as the
/// parameters of a function (`super::templates::entry`), and its
/// continuation binds.
///
/// # Errors
///
/// The errors of `super::templates::entry`.
pub fn clause_entry(em: &mut Em<'_>, n: NodeId, params: &[(weft_ir::LocalId, Tree)]) -> R {
    super::templates::entry(em, n, params)?;
    // A parameter that holds a linear closure of a perform (O3-7, plan stage
    // F16): the clause must run it or give it on (W0601 at its end).
    for (l, v) in params {
        let k = em.key(*l)?;
        super::templates::mark_fn_linear(em, k, &v.flat());
    }
    let kont = em.p.body(em.body).and_then(|b| b.kont).map(|(k, _)| k);
    if let Some(k) = kont {
        let key = em.key(k)?;
        if let Some(s) = em.s_var(key) {
            em.facts.rebound_at.push((s, n));
            em.facts.empty_at.push((s, n));
        }
    }
    Ok(())
}

/// The blocks of clause body `c` in the `pre` part (from the entry, up to
/// and with the resume points) and in the `post` part (from the block after
/// each resume point), by the normal edges.
fn regions(b: &weft_ir::Body) -> (BTreeSet<BlockId>, BTreeSet<BlockId>) {
    let walk = |starts: Vec<BlockId>, stop: bool| {
        let mut seen: BTreeSet<BlockId> = BTreeSet::new();
        let mut work = starts;
        while let Some(x) = work.pop() {
            if !seen.insert(x) {
                continue;
            }
            let Some(blk) = b.blocks.get(x.index()) else {
                continue;
            };
            if stop && matches!(blk.term.kind, TermKind::Resume { .. }) {
                continue;
            }
            work.extend(blk.term.kind.normal_successors());
        }
        seen
    };
    let pre = walk(vec![b.entry], true);
    let nexts: Vec<BlockId> = b
        .blocks
        .iter()
        .filter_map(|blk| match blk.term.kind {
            TermKind::Resume { next, .. } => Some(next),
            _ => None,
        })
        .collect();
    let post = walk(nexts, false);
    (pre, post)
}

/// The nodes of the `pre` part and of the `post` part of clause body `c`,
/// with the nodes of the handled bodies that splice into it (the region of
/// the block of their `handle`).
fn clause_nodes(p: &Program, ix: &Index, c: BodyId) -> (HashSet<NodeId>, HashSet<NodeId>) {
    let mut pre = HashSet::new();
    let mut post = HashSet::new();
    let Some(b) = p.body(c) else {
        return (pre, post);
    };
    let (pre_blocks, post_blocks) = regions(b);
    // The block of the clause where each spliced body runs.
    let place_of = |key: &NodeKey| -> Option<(BlockId, u32, Phase)> {
        if key.body == c {
            return Some((key.block, key.at, key.phase));
        }
        let mut at = key.body;
        for _ in 0..=p.bodies.len() {
            let x = p.bodies.get(at.index())?;
            let BodyKind::Handled(h) = x.kind else {
                return None;
            };
            let site = x.parent?;
            if site == c {
                let s = p.body(c)?;
                let blk = s.blocks.iter().position(
                    |blk| matches!(blk.term.kind, TermKind::Handle { handler, .. } if handler == h),
                )?;
                return Some((BlockId(u32::try_from(blk).ok()?), TERM, Phase::Main));
            }
            at = site;
        }
        None
    };
    // The clause and the handled bodies that splice into it.
    let mut bodies = vec![c];
    let mut i = 0;
    while let Some(&x) = bodies.get(i) {
        i += 1;
        bodies.extend(ix.kids.get(&x).into_iter().flatten().copied().filter(|&k| {
            p.body(k)
                .is_some_and(|d| matches!(d.kind, BodyKind::Handled(_)))
        }));
    }
    for (key, n) in ix.nodes(&bodies) {
        let n = *n;
        if key.dest != NORMAL {
            continue;
        }
        let Some((block, at, phase)) = place_of(key) else {
            continue;
        };
        let resume_block = b
            .blocks
            .get(block.index())
            .is_some_and(|blk| matches!(blk.term.kind, TermKind::Resume { .. }));
        let after_resume = resume_block && at == TERM && phase != Phase::Main;
        if pre_blocks.contains(&block) && !after_resume {
            pre.insert(n);
        }
        if post_blocks.contains(&block) || after_resume {
            post.insert(n);
        }
    }
    (pre, post)
}

/// The variables of the locals of body `c` and of the bodies inside it.
fn own_vars(ix: &Index, by_body: &HashMap<BodyId, Vec<VarId>>, c: BodyId) -> HashSet<VarId> {
    ix.subtree(c)
        .iter()
        .flat_map(|b| by_body.get(b).into_iter().flatten().copied())
        .collect()
}

/// The variables of the component by the body of their local.
fn vars_by_body(vars: &Vars) -> HashMap<BodyId, Vec<VarId>> {
    let mut out: HashMap<BodyId, Vec<VarId>> = HashMap::new();
    for k in vars.keys() {
        if let Some(v) = vars.get(k) {
            out.entry(key_body(k)).or_default().push(v);
        }
    }
    out
}

/// The text of the last step of place `q` (the display of `q` after the
/// display of its parent).
fn step_text(facts: &FnFacts, q: PlaceId) -> String {
    let info = facts.place(q);
    let Some(parent) = info.parent else {
        return String::new();
    };
    let pd = &facts.place(parent).display;
    info.display
        .strip_prefix(pd.as_str())
        .map_or_else(|| ".?".to_string(), str::to_string)
}

/// Place `q` with its root replaced by place `base`: the steps of `q` below
/// its root, on `base`.
fn reroot(facts: &mut FnFacts, q: PlaceId, base: PlaceId) -> PlaceId {
    let mut chain: Vec<PlaceId> = Vec::new();
    let mut at = Some(q);
    while let Some(x) = at {
        chain.push(x);
        at = facts.place(x).parent;
    }
    chain.pop();
    let mut out = base;
    for &x in chain.iter().rev() {
        let Some(step) = facts.place(x).steps.last().copied() else {
            continue;
        };
        let text = step_text(facts, x);
        out = facts.child(out, step, &text);
    }
    out
}

/// σ of one run of a clause: the places of each parameter and what the
/// references behind it point into.
#[derive(Clone, Debug, Default)]
struct Sigma {
    /// σ(`Param(i)`).
    args: Vec<Vec<PlaceId>>,
    /// σ(`Held(i)`).
    helds: Vec<Vec<PlaceId>>,
    /// The handle places that the places of each argument depend on.
    deps: Vec<Vec<PlaceId>>,
}

impl Sigma {
    /// Adds the places of `o`.
    fn join(&mut self, o: &Self) {
        for (i, ps) in o.args.iter().enumerate() {
            if self.args.len() <= i {
                self.args.resize(i + 1, Vec::new());
            }
            if let Some(mine) = self.args.get_mut(i) {
                mine.extend(ps.iter().copied());
                mine.sort();
                mine.dedup();
            }
        }
        for (i, ps) in o.helds.iter().enumerate() {
            if self.helds.len() <= i {
                self.helds.resize(i + 1, Vec::new());
            }
            if let Some(mine) = self.helds.get_mut(i) {
                mine.extend(ps.iter().copied());
                mine.sort();
                mine.dedup();
            }
        }
        for (i, ps) in o.deps.iter().enumerate() {
            if self.deps.len() <= i {
                self.deps.resize(i + 1, Vec::new());
            }
            if let Some(mine) = self.deps.get_mut(i) {
                mine.extend(ps.iter().copied());
                mine.sort();
                mine.dedup();
            }
        }
    }
}

/// How a place of a clause maps at a run node.
enum Mapped {
    /// A place of the parameter `i` of the clause, on these places.
    Param(u32, Vec<PlaceId>),
    /// A place outside the clause: the same place.
    Same(PlaceId),
    /// A place of a local of the clause: not seen outside it.
    Own,
}

/// What a place of a clause maps to at a run node.
struct Mapper<'a> {
    /// The program.
    p: &'a Program,
    /// The `S` variables of the locals of the component (a new value of one
    /// in a clause is an `overwrites` at the run node).
    locals: &'a HashSet<VarId>,
    /// The roots of the component.
    roots: &'a Roots,
    /// The clause body.
    clause: BodyId,
    /// The nodes of the clause that run a function value of a parameter of
    /// the clause, with the index of the parameter (O3-7, plan stage F16):
    /// a change there is a change of the run of that argument of the
    /// perform, with its root.
    param_runs: &'a HashMap<NodeId, u32>,
}

impl Mapper<'_> {
    /// Place `q` of the clause at a run node with σ `s`.
    fn map(&self, facts: &mut FnFacts, s: &Sigma, q: PlaceId) -> Mapped {
        let root = facts.place(q).root;
        match self.roots.role(root) {
            Some(Role::Param(b, i)) if b == self.clause => {
                let bases = s.args.get(i as usize).cloned().unwrap_or_default();
                Mapped::Param(i, bases.into_iter().map(|b| reroot(facts, q, b)).collect())
            }
            Some(Role::Held(b, i)) if b == self.clause => {
                let bases = s.helds.get(i as usize).cloned().unwrap_or_default();
                Mapped::Param(i, bases.into_iter().map(|b| reroot(facts, q, b)).collect())
            }
            Some(Role::Local(k) | Role::Cell(k)) if inside(self.p, k.0, self.clause) => Mapped::Own,
            _ => Mapped::Same(q),
        }
    }

    /// The parameter of the clause that place `q` is below, if any.
    fn param_of(&self, facts: &FnFacts, q: PlaceId) -> Option<u32> {
        match self.roots.role(facts.place(q).root) {
            Some(Role::Param(b, i) | Role::Held(b, i)) if b == self.clause => Some(i),
            _ => None,
        }
    }

    /// The places of place `q` at a run node with σ `s`.
    fn places(&self, facts: &mut FnFacts, s: &Sigma, q: PlaceId) -> Vec<PlaceId> {
        match self.map(facts, s, q) {
            Mapped::Param(_, ps) => ps,
            Mapped::Same(q) => vec![q],
            Mapped::Own => Vec::new(),
        }
    }
}

/// The tables that [`project`] reads.
pub struct Tables<'a> {
    /// The program.
    pub p: &'a Program,
    /// The types.
    pub tys: &'a TyTable,
    /// The roots of the component.
    pub roots: &'a Roots,
    /// The variables of the component.
    pub vars: &'a Vars,
    /// The nodes of the component.
    pub table: &'a NodeTable,
}

/// `spared_at(V, n)` of each variable `V` of a local outside the handled
/// bodies `hs` (ADR 0005, `docs/ir.md` 6.5): each abort of node `n` goes to
/// a local handler whose handled body is in `hs`, and the unwinding of the
/// handled body does not reach the variable. If a node of the clause part
/// `nodes` can abort (other than a `resume`, whose aborts are of the
/// handled body), the abort can go further: no variable is spared.
fn spare(
    p: &Program,
    facts: &mut FnFacts,
    cands: &[(BodyId, VarId)],
    (n, hs): (NodeId, &[BodyId]),
) {
    facts.spared_at.extend(
        cands
            .iter()
            .filter(|(b, _)| !hs.iter().any(|&hb| inside(p, *b, hb)))
            .map(|&(_, v)| (v, n)),
    );
}

/// The body of the local of variable key `k`.
const fn key_body(k: &VarKey) -> BodyId {
    match k {
        VarKey::S(b, _)
        | VarKey::H(b, _)
        | VarKey::U(b, _)
        | VarKey::C(b, _)
        | VarKey::E(b, _)
        | VarKey::D(b, _, _)
        | VarKey::W(b, _, _)
        | VarKey::N(b, _, _, _) => *b,
    }
}

/// The number of clause bodies on the parent chain of body `b` (with `b`).
fn clause_depth(p: &Program, b: BodyId) -> usize {
    let mut n = 0;
    let mut at = Some(b);
    for _ in 0..=p.bodies.len() {
        let Some(x) = at.and_then(|x| p.bodies.get(x.index())) else {
            break;
        };
        if matches!(x.kind, BodyKind::Clause(..)) {
            n += 1;
        }
        at = x.parent;
    }
    n
}

/// The facts of the clauses at the nodes that run them (see the module
/// text): the `pre` part at each perform, the `post` part at `Post`, then
/// the rest of the handled body at each `Resume`.
pub fn project(t: &Tables<'_>, facts: &mut FnFacts, hx: &Handlers) {
    let p = t.p;
    let _ = t.tys;
    let ix = Index::new(p, t.table);
    // The join of σ over the runs of a clause (for `Post`).
    let joined = joined_sigma(hx);
    let locals: HashSet<VarId> = t
        .vars
        .keys()
        .filter(|k| matches!(k, VarKey::S(..)))
        .filter_map(|k| t.vars.get(k))
        .collect();
    let by_body = vars_by_body(t.vars);
    let mut regions: HashMap<BodyId, (HashSet<NodeId>, HashSet<NodeId>)> = HashMap::new();
    for r in &hx.runs {
        regions
            .entry(r.clause)
            .or_insert_with(|| clause_nodes(p, &ix, r.clause));
    }
    let param_runs = param_run_nodes(p, t.table, regions.keys().copied());
    let mut owned: HashMap<BodyId, HashSet<VarId>> = HashMap::new();
    // The rows of the facts at the nodes of each clause: each run of the
    // clause reads these, and a run node in a clause adds its rows to the
    // rows of that clause.
    let mut clause_of: HashMap<NodeId, BodyId> = HashMap::new();
    for (&c, (pre, post)) in &regions {
        for &x in pre.iter().chain(post) {
            clause_of.insert(x, c);
        }
    }
    let mut parts: HashMap<BodyId, FnFacts> = clause_rows(facts, &clause_of);
    // The `Main` nodes of the `Resume`s (their aborts are of the handled
    // body), and the variables that `spared_at` can matter for: a linear
    // or `!Move` value (W0602, W0503).
    let resumes: HashSet<NodeId> = t
        .table
        .iter()
        .filter(|(k, _)| {
            k.at == TERM
                && k.phase == Phase::Main
                && p.body(k.body)
                    .and_then(|b| b.blocks.get(k.block.index()))
                    .is_some_and(|b| matches!(b.term.kind, TermKind::Resume { .. }))
        })
        .map(|(_, &x)| x)
        .collect();
    let cands: Vec<(BodyId, VarId)> = t
        .vars
        .keys()
        .filter_map(|k| t.vars.get(k).map(|v| (key_body(k), v)))
        .filter(|&(_, v)| {
            let info = facts.var(v);
            info.linear || info.immovable
        })
        .collect();
    // A run node in a clause gets the facts of the clauses that it runs
    // before that clause goes to its own run nodes: the runs of the deepest
    // clauses first.
    let mut order: Vec<&ClauseRun> = hx.runs.iter().collect();
    order.sort_by_key(|r| std::cmp::Reverse(clause_depth(p, r.at)));
    for r in order {
        let Some((pre, post)) = regions.get(&r.clause) else {
            continue;
        };
        let nodes = if r.post { post } else { pre };
        let own = owned
            .entry(r.clause)
            .or_insert_with(|| own_vars(&ix, &by_body, r.clause));
        let s = if r.post {
            joined.get(&r.clause).cloned().unwrap_or_default()
        } else {
            Sigma {
                args: r.args.clone(),
                helds: r.helds.clone(),
                deps: r.deps.clone(),
            }
        };
        let cap = hx.ids.get(&r.handler).map(|x| x.1);
        let m = Mapper {
            p,
            locals: &locals,
            roots: t.roots,
            clause: r.clause,
            param_runs: &param_runs,
        };
        let empty = FnFacts::default();
        let part = parts.get(&r.clause).unwrap_or(&empty);
        let new = copy_part(
            facts,
            part,
            &m,
            (nodes, own),
            (&s, &r.ins, r.given.as_deref()),
            (r.node, cap),
        );
        let abort = part
            .may_abort
            .iter()
            .any(|x| nodes.contains(x) && !resumes.contains(x));
        add_rows(facts, &new);
        if let Some(c) = clause_of.get(&r.node) {
            add_rows(parts.entry(*c).or_default(), &new);
        }
        if let (Some(hs), false) = (&r.spares, abort) {
            spare(p, facts, &cands, (r.node, hs));
        }
    }
    // A clause that puts a reference of its parameter into a place outside
    // it (`keep = x`): the variable points into the places of the
    // arguments. Only a row whose place is below a parameter of a clause
    // can map.
    let mut rows_of: HashMap<BodyId, Vec<(VarId, PlaceId)>> = HashMap::new();
    for &(v, q) in &facts.points_into {
        if let Some(Role::Param(b, _) | Role::Held(b, _)) = t.roots.role(facts.place(q).root) {
            if joined.contains_key(&b) {
                rows_of.entry(b).or_default().push((v, q));
            }
        }
    }
    for (&c, s) in &joined {
        let own = owned.entry(c).or_insert_with(|| own_vars(&ix, &by_body, c));
        let m = Mapper {
            p,
            locals: &locals,
            roots: t.roots,
            clause: c,
            param_runs: &param_runs,
        };
        let rows: Vec<(VarId, PlaceId)> = rows_of
            .get(&c)
            .into_iter()
            .flatten()
            .filter(|(v, _)| !own.contains(v))
            .copied()
            .collect();
        for (v, q) in rows {
            if let Mapped::Param(_, ps) = m.map(facts, s, q) {
                facts.points_into.extend(ps.into_iter().map(|x| (v, x)));
            }
        }
    }
    for (c, (pre, post)) in &regions {
        let Some(h) = hx.runs.iter().find(|r| r.clause == *c).map(|r| r.handler) else {
            continue;
        };
        let Some(&(hid, _)) = hx.ids.get(&h) else {
            continue;
        };
        let escapes: BTreeSet<String> = parts
            .get(c)
            .into_iter()
            .flat_map(|x| x.escapes_at.iter())
            .filter(|(n, _)| pre.contains(n) || post.contains(n))
            .map(|(_, e)| e.clone())
            .collect();
        facts
            .clause_performs
            .extend(escapes.into_iter().map(|e| (hid, e)));
    }
}

/// The nodes of the clauses `clauses` that call a function value of a
/// parameter of the clause, with the index of the parameter (O3-7).
fn param_run_nodes(
    p: &Program,
    table: &NodeTable,
    clauses: impl Iterator<Item = BodyId>,
) -> HashMap<NodeId, u32> {
    let mut out = HashMap::new();
    for c in clauses {
        let Some(b) = p.body(c) else {
            continue;
        };
        for (bi, blk) in b.blocks.iter().enumerate() {
            let TermKind::Call {
                callee:
                    weft_ir::Callee::Value(weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q)),
                ..
            } = &blk.term.kind
            else {
                continue;
            };
            let Some(i) = b.params.iter().position(|&l| l == q.local) else {
                continue;
            };
            if !q.proj.is_empty() {
                continue;
            }
            let block = BlockId(u32::try_from(bi).unwrap_or(u32::MAX));
            for phase in [Phase::Main, Phase::Ret] {
                let key = NodeKey {
                    body: c,
                    block,
                    at: TERM,
                    phase,
                    dest: NORMAL,
                };
                if let Some(n) = table.get(key) {
                    out.insert(n, u32::try_from(i).unwrap_or(u32::MAX));
                }
            }
        }
    }
    out
}

/// The rows of `facts` at the nodes of each clause (`clause_of`), of the
/// relations that [`copy_part`] reads.
fn clause_rows(facts: &FnFacts, clause_of: &HashMap<NodeId, BodyId>) -> HashMap<BodyId, FnFacts> {
    let mut out: HashMap<BodyId, FnFacts> = HashMap::new();
    let at = |x: &NodeId| clause_of.get(x).copied();
    macro_rules! rows {
        ($rel:ident, $node:expr) => {
            for row in &facts.$rel {
                if let Some(c) = at(&$node(row)) {
                    out.entry(c).or_default().$rel.push(row.clone());
                }
            }
        };
    }
    rows!(uses, |r: &(VarId, NodeId)| r.1);
    rows!(moved_at, |r: &(VarId, NodeId)| r.1);
    rows!(rest_linear, |r: &(VarId, NodeId)| r.1);
    rows!(overwrites, |r: &(VarId, NodeId)| r.1);
    rows!(rebound_at, |r: &(VarId, NodeId)| r.1);
    rows!(unset_at, |r: &(VarId, NodeId)| r.1);
    rows!(mutates_at, |r: &(NodeId, PlaceId)| r.0);
    rows!(lends_mut, |r: &(NodeId, PlaceId)| r.0);
    rows!(reads_at, |r: &(NodeId, PlaceId)| r.0);
    rows!(releases_at, |r: &(NodeId, PlaceId)| r.0);
    rows!(moved_part, |r: &(PlaceId, NodeId)| r.1);
    rows!(performs_at, |r: &(NodeId, CapId)| r.0);
    rows!(escapes_at, |r: &(NodeId, String)| r.0);
    rows!(may_abort, |r: &NodeId| *r);
    rows!(multi_at, |r: &NodeId| *r);
    out
}

/// Adds the rows of the relations of [`copy_part`] of `src` to `dst`.
fn add_rows(dst: &mut FnFacts, src: &FnFacts) {
    dst.uses.extend(src.uses.iter().copied());
    dst.moved_at.extend(src.moved_at.iter().copied());
    dst.rest_linear.extend(src.rest_linear.iter().copied());
    dst.overwrites.extend(src.overwrites.iter().copied());
    dst.unset_at.extend(src.unset_at.iter().copied());
    dst.mutates_at.extend(src.mutates_at.iter().copied());
    dst.lends_mut.extend(src.lends_mut.iter().copied());
    dst.call_mut.extend(src.call_mut.iter().copied());
    dst.reads_at.extend(src.reads_at.iter().copied());
    dst.releases_at.extend(src.releases_at.iter().copied());
    dst.moved_part.extend(src.moved_part.iter().copied());
    dst.performs_at.extend(src.performs_at.iter().copied());
    dst.escapes_at.extend(src.escapes_at.iter().cloned());
    dst.may_abort.extend(src.may_abort.iter().copied());
    dst.multi_at.extend(src.multi_at.iter().copied());
}

/// σ of each clause: the join of σ of its performs.
fn joined_sigma(hx: &Handlers) -> BTreeMap<BodyId, Sigma> {
    let mut joined: BTreeMap<BodyId, Sigma> = BTreeMap::new();
    for r in hx.runs.iter().filter(|r| !r.post) {
        let s = Sigma {
            args: r.args.clone(),
            helds: r.helds.clone(),
            deps: r.deps.clone(),
        };
        joined.entry(r.clause).or_default().join(&s);
    }
    joined
}

/// Copies the facts of the nodes `nodes` of a clause to the node `n` that
/// runs it, with σ `s`: the variables that are not in `own` and the places
/// that the clause can see. A change of a place gets a `call_mut` with the
/// root of the parameter, or the root of the clauses of the capability
/// `cap` for a place of the site. With `given` (a call that runs the
/// clause), a change through a parameter has the callee root of the
/// argument whose given place it is below (none for a place of the callee
/// frame or of an `rc` group).
fn copy_part(
    facts: &mut FnFacts,
    part: &FnFacts,
    m: &Mapper<'_>,
    (nodes, own): (&HashSet<NodeId>, &HashSet<VarId>),
    (s, ins, given): (&Sigma, &[usize], Option<&GivenRoots>),
    (n, cap): (NodeId, Option<CapId>),
) -> FnFacts {
    let mut new = FnFacts::default();
    let at = |x: &NodeId| nodes.contains(x);
    let vars = |rows: &[(VarId, NodeId)]| -> Vec<VarId> {
        rows.iter()
            .filter(|(v, x)| at(x) && !own.contains(v))
            .map(|(v, _)| *v)
            .collect()
    };
    new.uses = vars(&part.uses).into_iter().map(|v| (v, n)).collect();
    new.moved_at = vars(&part.moved_at).into_iter().map(|v| (v, n)).collect();
    new.rest_linear = vars(&part.rest_linear)
        .into_iter()
        .map(|v| (v, n))
        .collect();
    let mut over = vars(&part.overwrites);
    // A new value of a variable outside the clause is a new value at the
    // run node on some paths: the old value can be overwritten, and the
    // variable can hold the new value after (no `rebound_at`: the clause
    // need not give it on each path).
    over.extend(
        vars(&part.rebound_at)
            .into_iter()
            .filter(|v| m.locals.contains(v)),
    );
    new.overwrites = over.into_iter().map(|v| (v, n)).collect();
    new.unset_at = vars(&part.unset_at).into_iter().map(|v| (v, n)).collect();
    let places = |rows: &[(NodeId, PlaceId)]| -> Vec<PlaceId> {
        rows.iter()
            .filter(|(x, _)| at(x))
            .map(|(_, q)| *q)
            .collect()
    };
    let clause_root = cap.map_or(crate::body::roots::STORED, crate::body::roots::clause);
    // A parameter of the clause points into its own root and into the places
    // of the arguments (plan stage F15): a change through it has a row for
    // each. The row of the place of an argument at a node that has a row
    // below the root of that parameter is the same change: the row of the
    // parameter maps it.
    let rows: Vec<(NodeId, PlaceId, bool)> = part
        .mutates_at
        .iter()
        .map(|&(x, q)| (x, q, false))
        .chain(part.lends_mut.iter().map(|&(x, q)| (x, q, true)))
        .filter(|(x, _, _)| at(x))
        .collect();
    let mut through: HashSet<(NodeId, u32)> = HashSet::new();
    for &(x, q, _) in &rows {
        if let Some(i) = m.param_of(facts, q) {
            through.insert((x, i));
        }
    }
    for (x, q, lends) in rows {
        let same = through.iter().any(|&(y, i)| {
            y == x && {
                let i = i as usize;
                s.args
                    .get(i)
                    .into_iter()
                    .chain(s.helds.get(i))
                    .flatten()
                    .any(|&b| at_or_below(facts, q, b))
            }
        });
        if same && m.param_of(facts, q).is_none() {
            continue;
        }
        let (root, ps) = match m.map(facts, s, q) {
            Mapped::Param(_, ps) if given.is_some() => (None, ps),
            Mapped::Param(i, ps) => {
                let i = i as usize;
                (
                    Some(crate::body::roots::param(ins.get(i).copied().unwrap_or(i))),
                    ps,
                )
            }
            Mapped::Same(q) => {
                let root = m
                    .param_runs
                    .get(&x)
                    .map_or(clause_root, |&i| crate::body::roots::fn_arg(i as usize));
                (Some(root), vec![q])
            }
            Mapped::Own => continue,
        };
        for x in ps {
            if lends {
                new.lends_mut.push((n, x));
            } else {
                new.mutates_at.push((n, x));
            }
            match (root, given) {
                (Some(root), _) => new.call_mut.push((n, x, root)),
                (None, Some(g)) => {
                    for r in given_roots(facts, g, x) {
                        new.call_mut.push((n, x, r));
                    }
                }
                (None, None) => {}
            }
        }
    }
    for q in places(&part.reads_at) {
        let ps = m.places(facts, s, q);
        new.reads_at.extend(ps.into_iter().map(|x| (n, x)));
    }
    for q in places(&part.releases_at) {
        let ps = m.places(facts, s, q);
        new.releases_at.extend(ps.into_iter().map(|x| (n, x)));
    }
    let parts: Vec<PlaceId> = part
        .moved_part
        .iter()
        .filter(|(_, x)| at(x))
        .map(|(q, _)| *q)
        .collect();
    for q in parts {
        let ps = m.places(facts, s, q);
        new.moved_part.extend(ps.into_iter().map(|x| (x, n)));
    }
    new.performs_at = part
        .performs_at
        .iter()
        .filter(|(x, _)| at(x))
        .map(|(_, c)| (n, *c))
        .collect();
    new.escapes_at = part
        .escapes_at
        .iter()
        .filter(|(x, _)| at(x))
        .map(|(_, e)| (n, e.clone()))
        .collect();
    // A node that runs a clause is a suspension point: it can abort if a
    // node of the clause can, a `resume` too (ADR 0005: each named effect
    // can abort, W0602), also when the clause resumes on each path and the
    // node has no abort edge to the handler (plan stage F15).
    if part.may_abort.iter().any(at) {
        new.may_abort.push(n);
    }
    if part.multi_at.iter().any(at) {
        new.multi_at.push(n);
    }
    new
}

/// True if place `q` is place `b` or a place below it; a wildcard place `b`
/// stands for each place below its base.
fn at_or_below(facts: &FnFacts, q: PlaceId, b: PlaceId) -> bool {
    let b = facts.wild_base(b).unwrap_or(b);
    let mut at = Some(q);
    while let Some(x) = at {
        if x == b {
            return true;
        }
        at = facts.place(x).parent;
    }
    false
}

/// The given places of the arguments of a call that runs a clause, each
/// with the callee root of its parameter (`ClauseRun::given`).
type GivenRoots = [(PlaceId, u32)];

/// The callee roots of the given places `given` at or above place `x`.
fn given_roots(facts: &FnFacts, given: &[(PlaceId, u32)], x: PlaceId) -> Vec<u32> {
    let mut out = Vec::new();
    let mut at = Some(x);
    while let Some(q) = at {
        out.extend(given.iter().filter(|(b, _)| *b == q).map(|(_, r)| *r));
        at = facts.place(q).parent;
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// The references that the clauses put behind a reference parameter of the
/// function or into an `rc` object (the W0204 store check).
///
/// The places of the parameters of each clause map onto the places of the
/// arguments of its performs.
pub fn map_stored(
    t: &Tables<'_>,
    facts: &mut FnFacts,
    (hx, holders): (&Handlers, &mut super::holders::Holders),
    stored: Vec<(BodyId, Stored)>,
) -> Vec<Stored> {
    let joined = joined_sigma(hx);
    let mut out = Vec::new();
    for (c, mut st) in stored {
        let s = joined.get(&c).cloned().unwrap_or_default();
        let m = Mapper {
            p: t.p,
            locals: &HashSet::new(),
            roots: t.roots,
            clause: c,
            param_runs: &HashMap::new(),
        };
        let mut refs = Vec::new();
        for &r in &st.refs {
            refs.extend(m.places(facts, &s, r));
        }
        refs.sort();
        refs.dedup();
        st.refs = refs;
        let into = m.places(facts, &s, st.into);
        // The nodes where the clause runs: a store there is a weak new value
        // of the place.
        let nodes: Vec<NodeId> = hx
            .runs
            .iter()
            .filter(|r| r.clause == c)
            .map(|r| r.node)
            .collect();
        for i in into {
            // A place of a local of the site: its holder variable points into
            // the stored places, as at the `Ret` of a call (part `stores`).
            if let Some((k, path)) = t.roots.path_of(facts, i) {
                let holder = t
                    .vars
                    .parts_of(k.0, k.1)
                    .iter()
                    .filter(|(kind, _, _)| *kind == super::vars::PartKind::H)
                    .filter_map(|(_, proj, v)| super::templates::steps(proj).map(|p| (p, *v)))
                    .filter(|(p, _)| path.starts_with(p))
                    .max_by_key(|(p, _)| p.len())
                    .map(|(_, v)| v)
                    .or_else(|| t.vars.get(&VarKey::S(k.0, k.1)));
                if let Some(h) = holder {
                    let mut part = false;
                    for &n in &nodes {
                        part |= holders.add(n, h, &st.refs);
                    }
                    if !part {
                        facts.points_into.extend(st.refs.iter().map(|&r| (h, r)));
                    }
                }
                continue;
            }
            let mut x = st.clone();
            x.into = i;
            x.clause = true;
            out.push(x);
        }
    }
    out
}

/// The rest of the handled body at each `Resume` of a clause (see the
/// module text).
///
/// The rest is the nodes of the handled body that a perform of the clause
/// reaches, and the `Exit` and `Post` nodes of the `handle`. The `Resume`
/// lends each place that they change and frees each place that they free.
/// A change or a free of a place that a parameter of the clause points into
/// (σ of a perform) is a change or a free of the place of the parameter.
///
/// # Errors
///
/// Returns [`AlphaError::Later`] for a clause whose run nodes the region
/// does not find in the handled body.
pub fn continuations(t: &Tables<'_>, facts: &mut FnFacts, hx: &Handlers) -> R {
    let p = t.p;
    let joined = &joined_sigma(hx);
    // The frames of the clauses end at `Post`: a reference into a local of a
    // clause that a variable outside the clause holds is invalid there.
    let ends: Vec<(HandlerId, NodeId)> = hx
        .ends
        .iter()
        .map(|&(h, _, post)| (h, post))
        .chain(hx.landings.iter().copied())
        .collect();
    let ix = Index::new(p, t.table);
    let mut roots_of: HashMap<BodyId, Vec<PlaceId>> = HashMap::new();
    for (k, r) in t.roots.local_roots().chain(t.roots.cell_roots()) {
        roots_of.entry(k.0).or_default().push(r);
    }
    for &(h, post) in &ends {
        let clauses: Vec<BodyId> = p
            .handlers
            .get(h.index())
            .map(|d| d.clauses.iter().map(|(_, c)| *c).collect())
            .unwrap_or_default();
        let mut rs: Vec<PlaceId> = Vec::new();
        for &c in &clauses {
            for b in ix.subtree(c) {
                rs.extend(roots_of.get(&b).into_iter().flatten().copied());
            }
        }
        rs.sort();
        rs.dedup();
        facts.releases_at.extend(rs.into_iter().map(|r| (post, r)));
    }
    // The `multi` points: `multi_at`, and each node that runs a clause that
    // can resume more than once (`performs_at` of a `clause_multi`
    // capability, plan stage F16).
    let multi_caps: HashSet<CapId> = facts.clause_multi.iter().copied().collect();
    let multi: HashSet<NodeId> = facts
        .multi_at
        .iter()
        .copied()
        .chain(
            facts
                .performs_at
                .iter()
                .filter(|(_, c)| multi_caps.contains(c))
                .map(|(n, _)| *n),
        )
        .collect();
    // `body_multi`: a node of the handled body can resume more than once,
    // so a `resume` of a clause is a `multi` point (`multi_at` by the rule of
    // the spec, W0503).
    for (&h, &(_, cap)) in &hx.ids {
        let Some(hb) = p.handlers.get(h.index()).map(|d| d.handled) else {
            continue;
        };
        let nodes = ix.spliced_nodes(p, hb, false);
        if multi.iter().any(|n| nodes.contains(n)) {
            facts.body_multi.push(cap);
        }
    }
    if hx.resumes.is_empty() {
        return Ok(());
    }
    let mut succ: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
    for &(a, b) in &facts.cfg_edge {
        succ.entry(a).or_default().push(b);
    }
    // The rows of the relations that a continuation reads, by node. A
    // `Resume` adds its rows to them (a resume node of an inner clause can
    // be in the region of an outer continuation).
    let mut changes: HashMap<NodeId, Vec<PlaceId>> = HashMap::new();
    for &(x, q) in facts.mutates_at.iter().chain(&facts.lends_mut) {
        changes.entry(x).or_default().push(q);
    }
    let mut ends_of: HashMap<NodeId, Vec<VarId>> = HashMap::new();
    for &(v, x) in facts
        .moved_at
        .iter()
        .chain(&facts.scope_end)
        .chain(&facts.unwound_at)
    {
        ends_of.entry(x).or_default().push(v);
    }
    let mut frees_of: HashMap<NodeId, Vec<PlaceId>> = HashMap::new();
    for &(q, x) in &facts.moved_part {
        frees_of.entry(x).or_default().push(q);
    }
    for &(x, q) in &facts.releases_at {
        frees_of.entry(x).or_default().push(q);
    }
    let owners: HashMap<VarId, Vec<PlaceId>> = {
        let mut m: HashMap<VarId, Vec<PlaceId>> = HashMap::new();
        for &(q, v) in &facts.owner {
            m.entry(v).or_default().push(q);
        }
        m
    };
    let rg = Region {
        p,
        ix: &ix,
        hx,
        succ: &succ,
        multi: multi_handlers(facts, hx, &multi),
    };
    for &(r, h, c) in &hx.resumes {
        let Some(seen) = rg.of(h, c)? else {
            continue;
        };
        // The frame of the clause waits at its `resume`: the rest of the
        // handled body does not free a local of the clause (the release at
        // `Post` and `Landing` is for the frames of the clauses of the
        // handlers inside the handled body).
        let own: HashSet<weft_facts::RootId> = ix
            .subtree(c)
            .iter()
            .flat_map(|b| roots_of.get(b).into_iter().flatten())
            .map(|&q| facts.place(q).root)
            .collect();
        let mut changed: BTreeSet<PlaceId> = BTreeSet::new();
        let mut freed: BTreeSet<PlaceId> = BTreeSet::new();
        for x in &seen {
            changed.extend(changes.get(x).into_iter().flatten().copied());
            for v in ends_of.get(x).into_iter().flatten() {
                freed.extend(owners.get(v).into_iter().flatten().copied());
            }
            freed.extend(frees_of.get(x).into_iter().flatten().copied());
        }
        freed.retain(|&q| !own.contains(&facts.place(q).root));
        // The places of the parameters of the clause.
        let mut params: Vec<(PlaceId, PlaceId)> = Vec::new();
        if let Some(s) = joined.get(&c) {
            let names: Vec<(usize, String)> = p
                .body(c)
                .map(|b| {
                    b.params
                        .iter()
                        .enumerate()
                        .map(|(i, &l)| {
                            (
                                i,
                                b.local(l)
                                    .and_then(|d| d.name.clone())
                                    .unwrap_or_else(|| format!("parameter {i}")),
                            )
                        })
                        .collect()
                })
                .unwrap_or_default();
            for (i, _) in names {
                let i32 = u32::try_from(i).unwrap_or(u32::MAX);
                let Some(pr) = t.roots.param_of(c, i32) else {
                    continue;
                };
                for &a in s
                    .args
                    .get(i)
                    .into_iter()
                    .flatten()
                    .chain(s.deps.get(i).into_iter().flatten())
                {
                    params.push((pr, a));
                }
                if let Some(hr) = t.roots.held_of(c, i32) {
                    for &a in s.helds.get(i).into_iter().flatten() {
                        params.push((hr, a));
                    }
                }
            }
        }
        let mut lends: BTreeSet<PlaceId> = changed.clone();
        let mut frees: BTreeSet<PlaceId> = freed.clone();
        for &(pr, a) in &params {
            for &q in &changed {
                match through_param(facts, pr, a, q, false) {
                    Through::Lend(x) => {
                        lends.insert(x);
                    }
                    Through::Free(x) => {
                        frees.insert(x);
                    }
                    Through::None => {}
                }
            }
            for &q in &freed {
                if let Through::Free(x) | Through::Lend(x) = through_param(facts, pr, a, q, true) {
                    frees.insert(x);
                }
            }
        }
        changes.entry(r).or_default().extend(lends.iter().copied());
        frees_of.entry(r).or_default().extend(frees.iter().copied());
        facts.lends_mut.extend(lends.into_iter().map(|q| (r, q)));
        facts.releases_at.extend(frees.into_iter().map(|q| (r, q)));
    }
    Ok(())
}

/// The handler of each node that runs a clause that can resume more than
/// once: the handler of the clause, or `None` for a `multi` operation of a
/// handler of a caller (`multi_at`).
fn multi_handlers(
    facts: &FnFacts,
    hx: &Handlers,
    multi: &HashSet<NodeId>,
) -> HashMap<NodeId, Option<HandlerId>> {
    let by_cap: HashMap<CapId, HandlerId> = hx.ids.iter().map(|(&h, &(_, c))| (c, h)).collect();
    let caps: HashSet<CapId> = facts.clause_multi.iter().copied().collect();
    let mut out: HashMap<NodeId, Option<HandlerId>> = HashMap::new();
    for &n in &facts.multi_at {
        out.insert(n, None);
    }
    for &(n, c) in &facts.performs_at {
        if multi.contains(&n) && caps.contains(&c) {
            if let Some(&h) = by_cap.get(&c) {
                out.insert(n, Some(h));
            }
        }
    }
    out
}

/// The region of the continuation of a `resume` (`docs/ir.md` 6.7, plan
/// stage F17): the nodes that can run while a clause waits at its `resume`.
struct Region<'a> {
    p: &'a Program,
    ix: &'a Index,
    hx: &'a Handlers,
    succ: &'a HashMap<NodeId, Vec<NodeId>>,
    /// The nodes that run a clause that can resume more than once, with its
    /// handler ([`multi_handlers`]).
    multi: HashMap<NodeId, Option<HandlerId>>,
}

impl Region<'_> {
    /// The handled body of handler `h`.
    fn handled(&self, h: HandlerId) -> Option<BodyId> {
        self.p.handlers.get(h.index()).map(|d| d.handled)
    }

    /// The `Exit` and `Post` nodes of handler `h`.
    fn ends(&self, h: HandlerId) -> Vec<NodeId> {
        self.hx
            .ends
            .iter()
            .filter(|(x, _, _)| *x == h)
            .flat_map(|(_, e, po)| [*e, *po])
            .collect()
    }

    /// The nodes of handled body `hb` and of the bodies that splice into it,
    /// on the normal path or on a cleanup path whose abort lands in a
    /// handler inside `hb` (D-CONT-UNWIND of the review of group D).
    fn body_nodes(&self, hb: BodyId) -> HashSet<NodeId> {
        let bodies: Vec<BodyId> = self
            .ix
            .subtree(hb)
            .into_iter()
            .filter(|&b| splice_root(self.p, b) != b)
            .collect();
        let dests: HashSet<u32> = self
            .p
            .handlers
            .iter()
            .enumerate()
            .filter(|(_, d)| bodies.contains(&d.handled))
            .map(|(i, _)| {
                super::frames::FIRST_HANDLER.saturating_add(u32::try_from(i).unwrap_or(u32::MAX))
            })
            .collect();
        self.ix
            .nodes(&bodies)
            .filter(|(k, _)| k.dest == NORMAL || dests.contains(&k.dest))
            .map(|(_, n)| *n)
            .collect()
    }

    /// The nodes of the component of body `root` (the body and the bodies
    /// that splice into it) on the normal path.
    fn component_nodes(&self, root: BodyId) -> HashSet<NodeId> {
        let bodies: Vec<BodyId> = self
            .ix
            .subtree(root)
            .into_iter()
            .filter(|&b| splice_root(self.p, b) == root)
            .collect();
        self.ix
            .nodes(&bodies)
            .filter(|(k, _)| k.dest == NORMAL)
            .map(|(_, n)| *n)
            .collect()
    }

    /// The start points of the region of clause `c` in the nodes `body` of
    /// its handled body: each node that runs the clause, and if the node
    /// itself runs code after the perform (a call, the run of a function
    /// value, or the run of an inner clause), the node too (D-CONT-RUN). A
    /// perform in a clause of an inner handler maps to the nodes that run
    /// that clause (D-CONT-NEST).
    ///
    /// Returns `None` if a run of the clause maps to no node of `body`.
    fn starts(&self, c: BodyId, body: &HashSet<NodeId>) -> Option<Vec<(NodeId, bool)>> {
        let mut out: Vec<(NodeId, bool)> = Vec::new();
        let mut todo: Vec<(&ClauseRun, bool)> = self
            .hx
            .runs
            .iter()
            .filter(|x| !x.post && x.clause == c)
            .map(|x| (x, false))
            .collect();
        let mut done: HashSet<BodyId> = HashSet::new();
        while let Some((x, mapped)) = todo.pop() {
            if body.contains(&x.node) {
                out.push((x.node, mapped || x.given.is_some()));
                continue;
            }
            match clause::enclosing_clause(self.p, x.at) {
                // A perform in a closure body that a node of the handled
                // body runs: that node is a run of the clause too (a call
                // that runs a clause, plan stage F16). A closure that no
                // node runs (dead code) runs no clause.
                None if !mapped => {
                    let mut runs = self
                        .hx
                        .runs
                        .iter()
                        .filter(|y| y.clause == c && y.given.is_some())
                        .peekable();
                    if runs.peek().is_some() && !runs.any(|y| body.contains(&y.node)) {
                        return None;
                    }
                }
                Some(c1) if c1 != c => {
                    if done.insert(c1) {
                        todo.extend(
                            self.hx
                                .runs
                                .iter()
                                .filter(|y| y.clause == c1)
                                .map(|y| (y, true)),
                        );
                    }
                }
                _ => return None,
            }
        }
        Some(out)
    }

    /// The nodes from the nodes `starts` (each with the node itself or only
    /// the nodes after it) on, inside the nodes `body`.
    fn walk(&self, starts: &[(NodeId, bool)], body: &HashSet<NodeId>, seen: &mut HashSet<NodeId>) {
        let mut work: Vec<NodeId> = Vec::new();
        for &(n, with) in starts {
            if with && body.contains(&n) {
                seen.insert(n);
            }
            work.extend(self.succ.get(&n).into_iter().flatten().copied());
        }
        while let Some(x) = work.pop() {
            if !body.contains(&x) || !seen.insert(x) {
                continue;
            }
            work.extend(self.succ.get(&x).into_iter().flatten().copied());
        }
    }

    /// The region of the continuation of each `resume` of clause `c` of
    /// handler `h`: the nodes of the handled body after each node that runs
    /// the clause, and `Exit` and `Post` of the `handle`. If a node of the
    /// region runs a clause of an outer `multi` handler, a copy of the frame
    /// of the clause waits while the rest of that handled body runs, and
    /// runs again from the node (D-COPY-WAIT): the region has those nodes
    /// too.
    ///
    /// # Errors
    ///
    /// Returns [`AlphaError::Later`] if a run of the clause maps to no node
    /// of the handled body.
    fn of(&self, h: HandlerId, c: BodyId) -> Result<Option<HashSet<NodeId>>, AlphaError> {
        let Some(hb) = self.handled(h) else {
            return Ok(None);
        };
        let body = self.body_nodes(hb);
        let Some(starts) = self.starts(c, &body) else {
            return Err(AlphaError::Later(
                "a perform whose rest of the handled body the facts do not find (stage F17)",
            ));
        };
        let mut seen: HashSet<NodeId> = HashSet::new();
        self.walk(&starts, &body, &mut seen);
        let ends = self.ends(h);
        seen.extend(ends.iter().copied());
        // The outer `multi` handlers whose clauses a node of the region runs.
        let mut done: HashSet<Option<HandlerId>> = HashSet::new();
        loop {
            let found: Vec<Option<HandlerId>> = seen
                .iter()
                .filter_map(|n| self.multi.get(n).copied())
                .filter(|m| !done.contains(m))
                .collect();
            let Some(m) = found.first().copied() else {
                break;
            };
            done.insert(m);
            let outer = match m {
                Some(hm) if hm == h => continue,
                Some(hm) => match self.handled(hm) {
                    Some(hbm) if inside(self.p, hb, hbm) => {
                        let mut b = self.body_nodes(hbm);
                        b.extend(self.ends(hm));
                        b
                    }
                    _ => continue,
                },
                None => self.component_nodes(splice_root(self.p, hb)),
            };
            let from: Vec<(NodeId, bool)> = ends.iter().map(|&n| (n, false)).collect();
            self.walk(&from, &outer, &mut seen);
            if let Some(hm) = m {
                seen.extend(self.ends(hm));
            }
        }
        Ok(Some(seen))
    }
}

/// What a change or a free of a place is for a parameter of a clause
/// ([`through_param`]).
enum Through {
    /// A change of this place of the parameter.
    Lend(PlaceId),
    /// A free of this place of the parameter.
    Free(PlaceId),
    /// The places do not overlap.
    None,
}

/// What a change (or with `free`, a free) of place `q` is for the
/// parameter root `pr` whose argument is place `a`.
///
/// - `q` is `a`: a change (a free) of the root of the parameter.
/// - `q` is above `a`: a free of the root of the parameter if `free`, or if
///   the steps from `q` to `a` cross an unstable step (the change can end
///   the place of the argument); else nothing (a change of a place above
///   through stable steps keeps the place).
/// - `q` is below `a`: a change (a free) of the place below the root of the
///   parameter with the steps of `q` after `a`.
fn through_param(facts: &mut FnFacts, pr: PlaceId, a: PlaceId, q: PlaceId, free: bool) -> Through {
    // A wildcard argument place (the places that a call gives, plan stage
    // F15) stands for each place at or below its base: the argument can be
    // below a changed place there, also through an unstable step, so a
    // change at or below the base frees the root of the parameter; a change
    // above the base is a change above the parameter.
    if let Some(b) = facts.wild_base(a).filter(|&b| b != a) {
        if at_or_below(facts, q, b) {
            return Through::Free(pr);
        }
        return match through_param(facts, pr, b, q, free) {
            Through::Free(_) => Through::Free(pr),
            _ => Through::None,
        };
    }
    let pa = facts.place(a).clone();
    let pq = facts.place(q).clone();
    if pa.root != pq.root {
        return Through::None;
    }
    let n = pa.steps.len().min(pq.steps.len());
    if pa.steps.get(..n) != pq.steps.get(..n) {
        return Through::None;
    }
    let kind = |x| {
        if free {
            Through::Free(x)
        } else {
            Through::Lend(x)
        }
    };
    if pq.steps.len() == pa.steps.len() {
        return kind(pr);
    }
    if pq.steps.len() < pa.steps.len() {
        let unstable = pa
            .steps
            .get(pq.steps.len()..)
            .is_some_and(|st| st.iter().any(|x| x.unstable));
        return if free || unstable {
            Through::Free(pr)
        } else {
            Through::None
        };
    }
    // `q` is below `a`: the steps of `q` after `a`, on the parameter root.
    let mut chain: Vec<PlaceId> = Vec::new();
    let mut at = Some(q);
    while let Some(x) = at {
        if x == a {
            break;
        }
        chain.push(x);
        at = facts.place(x).parent;
    }
    if at != Some(a) {
        return kind(facts.wildcard(pr));
    }
    let mut out = pr;
    for &x in chain.iter().rev() {
        let Some(step) = facts.place(x).steps.last().copied() else {
            continue;
        };
        let text = step_text(facts, x);
        out = facts.child(out, step, &text);
    }
    kind(out)
}
