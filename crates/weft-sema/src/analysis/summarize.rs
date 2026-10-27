//! `summarize`: the summary of a body from its facts (`docs/ir.md` 6.7).
//!
//! The fact generator writes the facts of the component of a function body
//! with the summaries of its callees. [`summarize`] projects these facts onto
//! the interface of the function, by the part of each relation in `RELS`
//! (`crate::factgen::rels`):
//!
//! - `mutates_at` (part `muts`): each changed place whose root is a place
//!   of the interface (the pointee of a parameter, what the references
//!   behind a parameter point into, an `rc` group), and each changed place
//!   of a by-value parameter with no reference in its type. The old
//!   inference names such a change in the row, so W0701 asks for it. At a
//!   call, σ gives such a parameter no place, so the caller applies nothing
//!   (`super::apply::Sigma::args`). A change below a wildcard place is a
//!   change of its base, as the old inference says (`mut(p..)` is
//!   `mut(p)`). A place that another changed place covers adds nothing.
//! - `escapes_at` (part `performs`): each effect that a node performs
//!   through the capability of a caller.
//! - `may_abort` (part `aborts`): a failure of the runtime (`raises`) of a
//!   callee, and an `assert` of the body or of a callee (stage F7). An abort
//!   of an effect comes with its perform.
//! - `multi_at` (part `multi`): a callee that can resume more than once with
//!   no effect of its row that says so.
//!
//! The other parts of the summary of a function with no stated row come from
//! its signature: the parameters, the reads, the result, the stores, the
//! `@ uniq` parameters (`super::sig::build`). A body that the fact generator
//! supports has no type parameter (stage F20), so its parts `drops` and
//! `holds` are empty.

use std::collections::BTreeMap;

use weft_facts::{FnFacts, PlaceId, Step, StepKind};
use weft_ir::{BodyId, Callee, LocalId, TermKind, TyTable};

use super::sig::{holds_refs, is_ref, Inferred};
use super::summary::{Abort, IPlace, IRoot, IStep, Summaries};
use crate::factgen::alpha::{Role, Roots};
use crate::program::FnSig;

/// The by-value parameters of body `entry` whose type holds no reference,
/// by local: the old inference names a change of such a parameter in the
/// row (`mut(v)` for `v: Vec<u64>`).
pub fn owned_params(ir: &weft_ir::Program, tys: &TyTable, entry: BodyId) -> BTreeMap<LocalId, u32> {
    let mut out = BTreeMap::new();
    let Some(b) = ir.bodies.get(entry.index()) else {
        return out;
    };
    for (i, &l) in b.params.iter().enumerate() {
        let Some(d) = b.locals.get(l.index()) else {
            continue;
        };
        if matches!(d.kind, weft_ir::LocalKind::Param(_))
            && !is_ref(tys, d.ty)
            && !holds_refs(tys, d.ty)
        {
            out.insert(l, u32::try_from(i).unwrap_or(u32::MAX));
        }
    }
    out
}

/// The interface place of fact place `p`, with its callee root index.
///
/// `p` is a place of the component of function body `entry`. The result is
/// `None` if the root of `p` is not a root of the interface. `owned` are the
/// by-value parameters with no reference ([`owned_params`]): a place of such
/// a parameter is a place of its `Param` root, as the old inference says.
pub fn interface_place(
    facts: &FnFacts,
    roots: &Roots,
    entry: BodyId,
    sig: &FnSig,
    owned: &BTreeMap<LocalId, u32>,
    p: PlaceId,
) -> Option<(IPlace, u32)> {
    let info = facts.places.get(p.index())?;
    let (root, idx) = match roots.role(info.root)? {
        Role::Local((b, l)) if b == entry && owned.contains_key(&l) => {
            let i = owned.get(&l).copied()?;
            (IRoot::Param(i), super::sig::sig_root(sig, i as usize))
        }
        Role::Param(b, i) if b == entry => (IRoot::Param(i), super::sig::sig_root(sig, i as usize)),
        Role::Held(b, i) if b == entry => (IRoot::Held(i), super::sig::sig_root(sig, i as usize)),
        Role::Group => {
            let a = roots.group_adt(info.root)?;
            (
                IRoot::Group(a),
                crate::body::roots::group(crate::AdtId(a.index())),
            )
        }
        _ => return None,
    };
    Some((IPlace::cut(root, steps_of(facts, p)), idx))
}

/// The steps of fact place `p` from its root, each with its text: a
/// wildcard step (also of a one-place instance) is the wildcard step, and a
/// side of a split is an element step (a caller makes its own splits).
fn steps_of(facts: &FnFacts, p: PlaceId) -> Vec<IStep> {
    let mut out = Vec::new();
    let mut at = p;
    while let Some(parent) = facts.places.get(at.index()).and_then(|i| i.parent) {
        let Some(info) = facts.places.get(at.index()) else {
            break;
        };
        if let Some(&s) = info.steps.last() {
            let step = if weft_facts::is_wild_step(&s) {
                IStep::Wild
            } else if let StepKind::Seg { .. } = s.kind {
                let elem = Step {
                    kind: StepKind::Elem,
                    unstable: s.unstable,
                };
                IStep::Step(elem, "[]".to_string())
            } else {
                let before = facts
                    .places
                    .get(parent.index())
                    .map_or(0, |i| i.display.len());
                let text = info.display.get(before..).unwrap_or("");
                IStep::Step(s, text.to_string())
            };
            out.push(step);
        }
        at = parent;
    }
    out.reverse();
    out
}

/// The parts of effect inference of the function body `entry`.
///
/// They come from the facts `facts` of its component `comp` and the roots
/// `roots` of its fact generation; `sig` is its signature. `ir` is the IR,
/// and `sums` the summaries that the fact generation applied at the calls.
///
/// Only the first `nodes` nodes of `facts` are nodes of the body: the nodes
/// of its closure bodies come after them (stage F11). A closure acts on the
/// interface where it runs, at a call of the body: `applied` are the aborts
/// (a failure, an `assert`) of the summaries that the body applies at its
/// calls of function values.
#[allow(clippy::too_many_arguments)]
pub fn summarize(
    ir: &weft_ir::Program,
    tys: &TyTable,
    sums: &Summaries,
    facts: &FnFacts,
    roots: &Roots,
    comp: &[BodyId],
    entry: BodyId,
    sig: &FnSig,
    nodes: usize,
    applied: &std::collections::BTreeSet<Abort>,
    fv: &FnParts<'_>,
) -> Inferred {
    let mut out = Inferred::default();
    let mut changed = Inferred::default();
    let owned = owned_params(ir, tys, entry);
    // The function values (stage F12): the runs, and the values of the
    // result with the places of their environments.
    let place = |p: PlaceId| -> Option<IPlace> {
        if let Some((ip, _)) = interface_place(facts, roots, entry, sig, &owned, p) {
            return Some(ip);
        }
        let info = facts.places.get(p.index())?;
        matches!(roots.role(info.root), Some(Role::Caller))
            .then(|| IPlace::cut(IRoot::Caller, steps_of(facts, p)))
    };
    // A run gets a reference into a local of the body (`f(&x)`): the frame
    // of the run node, which ends at its `FrameEnd` (F3-2).
    let run_place = |p: PlaceId| -> Option<IPlace> {
        place(p).or_else(|| {
            let info = facts.places.get(p.index())?;
            match roots.role(info.root) {
                Some(Role::Local(_) | Role::Frame(_) | Role::Cell(_)) => {
                    Some(IPlace::wild(IRoot::Frame))
                }
                _ => None,
            }
        })
    };
    let runs = runs_of(fv.runs, false, &run_place, ir.body(entry));
    changed.multi |= fv.code_multi;
    for r in &runs {
        super::sig::join_run(&mut changed.runs, r);
    }
    let ret_ty = ir
        .bodies
        .get(entry.index())
        .and_then(|b| b.local(b.ret))
        .map(|d| d.ty);
    if ret_ty.is_some_and(|t| crate::props::ir_has_fns(tys, t)) {
        let (fns, places, caps) = ret_fns_of(ir, fv.returns, fv.made, entry, &place);
        made_effects(sums, sig, (&fns, &caps), &mut changed);
        changed.ret_fns = fns;
        changed.ret_places = places;
        changed.ret_linear = ret_linear(ir, tys, fv.returns, entry);
    }
    // The values that the body puts into the heap slots of interface places
    // (stage F13): the closures there have their effects in the row too.
    for (into, (fns, places, caps)) in
        stored_parts_of(ir, facts, roots, fv.returns, fv.made, entry, &place, false)
    {
        made_effects(sums, sig, (&fns, &caps), &mut changed);
        if !places.is_empty() {
            changed.puts.entry(into.clone()).or_default().extend(places);
        }
        if !fns.is_empty() {
            changed.put_fns.entry(into).or_default().extend(fns);
        }
    }
    for &(n, m) in &facts.mutates_at {
        if n.index() >= nodes {
            continue;
        }
        let base = facts.wild_base(m).unwrap_or(m);
        if let Some(mp) = interface_place(facts, roots, entry, sig, &owned, base) {
            changed.muts.push(mp);
        }
    }
    changed.muts.sort();
    changed.muts.dedup();
    // The code that the body runs and that a caller does not run again (code
    // of a caller of a value that the body does not know, the captures of a
    // closure that a callee made): a change through the places of the
    // interface that it gets is a lend of the body (follow-up F13.2).
    for &(n, l) in fv.lends {
        if n.index() >= nodes {
            continue;
        }
        let base = facts.wild_base(l).unwrap_or(l);
        if let Some(ip) = place(base) {
            changed.lends.insert(ip);
        }
    }
    // The reads of a place of an `rc` object: the signature gives the reads
    // of the parameters (stage F13, the summary oracle).
    for &(n, r) in &facts.reads_at {
        if n.index() >= nodes {
            continue;
        }
        let base = facts.wild_base(r).unwrap_or(r);
        if let Some((ip, _)) = interface_place(facts, roots, entry, sig, &owned, base) {
            if matches!(ip.root, IRoot::Group(_)) {
                changed.reads.insert(ip);
            }
        }
    }
    let made_named = changed.named.clone();
    out.join(&changed);
    out.named = facts
        .escapes_at
        .iter()
        .filter(|(n, _)| n.index() < nodes)
        .map(|(_, e)| e.clone())
        .collect();
    out.named.extend(made_named);
    out.raises |= applied.contains(&Abort::Raises);
    out.assert |= applied.contains(&Abort::Assert);
    out.gives_frame |= gives_frame(ir, tys, sums, (facts, roots), comp, nodes);
    for &b in comp.iter().filter(|&&b| ir.closure_of(b).is_none()) {
        let Some(body) = ir.bodies.get(b.index()) else {
            continue;
        };
        for blk in &body.blocks {
            if let TermKind::Assert { .. } = blk.term.kind {
                out.assert = true;
            }
            let TermKind::Call {
                callee: Callee::Fn(f, _),
                ..
            } = &blk.term.kind
            else {
                continue;
            };
            let Ok(s) = sums.get(*f) else {
                continue;
            };
            if s.aborts.contains(&Abort::Raises) {
                out.raises = true;
            }
            if s.aborts.contains(&Abort::Assert) {
                out.assert = true;
            }
            if s.unknown_multi {
                out.multi = true;
            }
        }
    }
    out
}

/// True if a body can give a place of its own frame to an operation of a
/// caller (`Summary::gives_frame`, plan stage F15).
///
/// An effect leaves the body (`escapes_at` at a node of the function
/// component, the first `nodes` nodes), and a node that lets an effect
/// leave (also in a clause) gives the code there a place of a local (`call_arg`: an argument of a perform through the capability
/// of a caller, or of a call); or a call in the body runs a callee that
/// gives its frame and performs an effect that leaves the body (no local
/// handler of the body handles it), or runs a function value.
fn gives_frame(
    ir: &weft_ir::Program,
    tys: &TyTable,
    sums: &Summaries,
    (facts, roots): (&FnFacts, &Roots),
    comp: &[BodyId],
    nodes: usize,
) -> bool {
    // The effects that leave the body: at the nodes of the function
    // component (the code of the clauses there too, `handlers::project`).
    if !facts.escapes_at.iter().any(|(n, _)| n.index() < nodes) {
        return false;
    }
    // The nodes where code gets places: also the nodes of the clauses of the
    // body, whose performs through the capability of a caller give the
    // places of their parameters (a local of a callee, `clause::given`).
    let escapes: std::collections::HashSet<weft_facts::NodeId> =
        facts.escapes_at.iter().map(|(n, _)| *n).collect();
    let local = |q: PlaceId| {
        let root = facts.place(q).root;
        matches!(
            roots.role(root),
            Some(Role::Local(_) | Role::Frame(_) | Role::Cell(_))
        )
    };
    if facts
        .call_arg
        .iter()
        .any(|&(n, q, _)| escapes.contains(&n) && local(q))
    {
        return true;
    }
    comp.iter()
        .filter(|&&b| ir.closure_of(b).is_none())
        .filter_map(|&b| ir.body(b))
        .flat_map(|b| &b.blocks)
        .any(|blk| match &blk.term.kind {
            TermKind::Call {
                callee: Callee::Fn(f, _),
                caps,
                ..
            } => sums.get(*f).is_ok_and(|s| {
                s.gives_frame
                    && s.performs.iter().any(|pf| match (&pf.cap, caps) {
                        (super::summary::CapIface::Row, weft_ir::CapArgs::Lexical(env)) => {
                            crate::factgen::frames::resolve(ir, tys, *env, &pf.effect, true)
                                == crate::factgen::frames::Dest::Past
                        }
                        _ => true,
                    })
            }),
            TermKind::Call {
                callee: Callee::Value(_),
                ..
            } => true,
            _ => false,
        })
}

/// What the fact generation of a body gives for its function values (stage
/// F12): the runs at its run nodes (each with `many`), and the states at its
/// `Return` nodes.
#[derive(Clone, Copy, Debug)]
pub struct FnParts<'a> {
    /// The runs of the function values of the interface.
    pub runs: &'a [(crate::analysis::transfer::RunOf, bool)],
    /// The state at each `Return`.
    pub returns: &'a [super::State],
    /// A run node runs code of a caller that can resume more than once.
    pub code_multi: bool,
    /// The join of the states where the body makes its closures (before
    /// each closure literal and each terminator): a `Kept` capture keeps
    /// the value that its variable has there, also after the variable ends.
    pub made: Option<&'a super::State>,
    /// The run nodes of code of a caller for a value of the interface
    /// (`Em::run_nodes`): the `lends` of these nodes are no `lends` of a
    /// closure summary, because a caller applies the value that it gives
    /// there.
    pub run_nodes: &'a [weft_facts::NodeId],
    /// In a closure body: each node where the body gives a capture a whole
    /// new value (`whole_capture`), with the index of the capture. The
    /// changes at the nodes after them are the part `late_muts`.
    pub rebind_nodes: &'a [(u32, weft_facts::NodeId)],
    /// The `lends_mut` of the summaries that the body applies and that no
    /// entry of `runs` gives again to a caller (`templates::Em::own_lends`).
    /// In a function body their interface places are the part `lends`; in a
    /// closure body they stay `lends` at a run node of `run_nodes`
    /// (follow-up F13.2).
    pub lends: &'a [(weft_facts::NodeId, PlaceId)],
}

/// The part `runs` of a body from the runs at its run nodes (`runs`): one
/// entry for each parameter (`capture` false) or capture (`capture` true),
/// `many` if a run node runs it more than once or two run nodes run it,
/// with the interface places (`place`) that the run nodes give. With
/// `closure`, the body is a closure body (its captures count).
fn runs_of(
    runs: &[(crate::analysis::transfer::RunOf, bool)],
    closure: bool,
    place: &dyn Fn(PlaceId) -> Option<IPlace>,
    body: Option<&weft_ir::Body>,
) -> Vec<super::summary::Run> {
    let mut out: Vec<super::summary::Run> = Vec::new();
    for (r, many) in runs {
        // The blocks that run the value on each path through them: a run
        // that a callee does on some paths only does not count (H5b).
        let blocks: std::collections::BTreeSet<weft_ir::BlockId> = runs
            .iter()
            .filter(|(x, _)| {
                x.param == r.param && x.capture == r.capture && x.result == r.result && !x.maybe
            })
            .map(|(x, _)| x.block)
            .collect();
        // A function body has no capture.
        if r.capture && !closure {
            continue;
        }
        let mut args: Vec<IPlace> = r.places.iter().filter_map(|&q| place(q)).collect();
        args.sort();
        args.dedup();
        let run = super::summary::Run {
            param: r.param,
            capture: r.capture,
            result: r.result,
            many: *many,
            task: r.task,
            args,
            multi: r.multi,
            maybe: body.is_none_or(|b| returns_without(b, &blocks)),
        };
        // A second run node of the value runs it again.
        if let Some(x) = out
            .iter_mut()
            .find(|x| x.param == run.param && x.capture == run.capture && x.result == run.result)
        {
            x.many = true;
        }
        super::sig::join_run(&mut out, &run);
    }
    out
}

/// True if a normal path of body `b` from its entry reaches a `Return`
/// with no block of `blocks` on it (a block of `blocks` runs a value at its
/// terminator).
fn returns_without(
    b: &weft_ir::Body,
    blocks: &std::collections::BTreeSet<weft_ir::BlockId>,
) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut work = vec![b.entry];
    while let Some(id) = work.pop() {
        if !seen.insert(id) || blocks.contains(&id) {
            continue;
        }
        let Some(blk) = b.blocks.get(id.index()) else {
            continue;
        };
        if blk.cleanup {
            continue;
        }
        if matches!(blk.term.kind, TermKind::Return) {
            return true;
        }
        work.extend(blk.term.kind.normal_successors());
    }
    false
}

/// The function values of `_0` of body `body` at its `Return` states
/// `returns` (part `ret`, stage F12), and the interface places (`place`)
/// that the result and the environments of its closures point into. A
/// closure of the body goes out as a closure that a callee made: its `Kept`
/// captures hold the values of the variables of the maker at the
/// `Return` and where the body makes the closure (`made`).
fn ret_fns_of(
    ir: &weft_ir::Program,
    returns: &[super::State],
    made: Option<&super::State>,
    body: BodyId,
    place: &dyn Fn(PlaceId) -> Option<IPlace>,
) -> RetParts {
    let Some(b) = ir.body(body) else {
        return RetParts::default();
    };
    let values: Vec<(&super::State, super::AbsVal)> = returns
        .iter()
        .map(|st| (st, st.value((body, b.ret), &[]).flat()))
        .collect();
    fn_parts_of(ir, &values, made, body, place)
}

/// The move path of the leading field and variant projections of `proj`.
fn field_path(proj: &[weft_ir::Proj]) -> Vec<super::PathStep> {
    proj.iter()
        .map_while(|p| match p {
            weft_ir::Proj::Field(f) => Some(super::PathStep::Field(f.0)),
            weft_ir::Proj::Variant(v) => Some(super::PathStep::Variant(v.0)),
            _ => None,
        })
        .collect()
}

/// The function values `v` of each pair (`st`, `v`) of `values` in the
/// terms of the interface (`place`), with the places that the values and
/// the environments of their closures point into, and the places of each
/// capture ([`ret_fns_of`]; stage F13 for the values that a body stores).
fn fn_parts_of(
    ir: &weft_ir::Program,
    values: &[(&super::State, super::AbsVal)],
    made: Option<&super::State>,
    body: BodyId,
    place: &dyn Fn(PlaceId) -> Option<IPlace>,
) -> RetParts {
    use super::summary::RetFn;
    use super::FnVal;
    let mut fns = std::collections::BTreeSet::new();
    let mut places = std::collections::BTreeSet::new();
    let mut caps: CapPlaces = BTreeMap::new();
    let one = |f: &FnVal| match f {
        FnVal::Item(g, t) => RetFn::Item(*g, t.clone()),
        FnVal::Closure(c) | FnVal::Made(c) => RetFn::Made(*c),
        // For a result of a run of a parameter, the caller gives back the
        // values of the argument and what their runs give back
        // (`transfer::with_results`).
        FnVal::Param(i) | FnVal::ParamResult(i) => RetFn::Param(*i),
        FnVal::Capture(k) => RetFn::Capture(*k),
        FnVal::Unknown => RetFn::Unknown,
    };
    for (st, v) in values {
        places.extend(v.refs.iter().filter_map(|&q| place(q)));
        // The closures of the value, and the closures that their `Kept`
        // captures hold (a closure that runs a captured closure), each one
        // time.
        let mut work: Vec<FnVal> = v.fns.iter().cloned().collect();
        let mut seen = std::collections::BTreeSet::new();
        while let Some(f) = work.pop() {
            if !seen.insert(f.clone()) {
                continue;
            }
            fns.insert(one(&f));
            // A closure of the body, or a closure that a closure of the body
            // made (`let m = || || print(r.hp); m()`): a `Kept` capture
            // shares a variable of the body through the captures of the
            // makers, so it holds the value of the variable at the `Return`
            // (class K3-Made of the review of stage F13).
            let (FnVal::Closure(c) | FnVal::Made(c)) = f else {
                continue;
            };
            let Some(decl) = ir.closures.get(c.index()) else {
                continue;
            };
            for (ki, cap) in decl.captures.iter().enumerate() {
                if !matches!(
                    cap.mode,
                    weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByMove
                ) {
                    continue;
                }
                let shared = (cap.mode == weft_ir::CaptureMode::Kept)
                    .then(|| super::apply::made_capture_source(ir, c, ki, body))
                    .flatten();
                let (k, path) = match shared {
                    Some(src) => {
                        let Ok(k) = crate::factgen::alpha::owner_local(ir, body, src.local) else {
                            fns.insert(RetFn::Unknown);
                            continue;
                        };
                        (k, field_path(&src.proj))
                    }
                    // A made closure of another maker holds its environment
                    // in its value.
                    None if decl.maker != body && matches!(f, FnVal::Made(_)) => continue,
                    // A `ByMove` capture: the value where the closure is made.
                    None => {
                        let Ok(k) =
                            crate::factgen::alpha::owner_local(ir, decl.maker, cap.source.local)
                        else {
                            fns.insert(RetFn::Unknown);
                            continue;
                        };
                        (k, Vec::new())
                    }
                };
                let mut src = st.value(k, &path).flat();
                if let Some(m) = made {
                    src.join(&m.value(k, &path).flat());
                }
                let ps: Vec<IPlace> = src.refs.iter().filter_map(|&q| place(q)).collect();
                caps.entry((c, u32::try_from(ki).unwrap_or(u32::MAX)))
                    .or_default()
                    .extend(ps.iter().cloned());
                if cap.mode == weft_ir::CaptureMode::Kept {
                    places.extend(ps);
                    work.extend(src.fns.iter().cloned());
                }
            }
        }
    }
    (fns, places, caps)
}

/// The values that body `body` puts into the heap slots of interface places
/// at its `Return` states `returns` (parts `puts` and `put_fns`, stage F13):
/// for each slot place that `place` names, the places that the stored
/// references point into, and the function values with the places of their
/// environments ([`fn_parts_of`]). With `all`, each slot with references
/// counts; else only a slot of an `rc` object and a slot with function
/// values (a function has the part `stores` from its signature for the
/// other references).
#[allow(clippy::too_many_arguments)]
fn stored_parts_of(
    ir: &weft_ir::Program,
    facts: &FnFacts,
    roots: &Roots,
    returns: &[super::State],
    made: Option<&super::State>,
    body: BodyId,
    place: &dyn Fn(PlaceId) -> Option<IPlace>,
    all: bool,
) -> Vec<(IPlace, RetParts)> {
    let mut keys: std::collections::BTreeSet<PlaceId> = std::collections::BTreeSet::new();
    for st in returns {
        keys.extend(st.behind_fns().keys().copied());
        for (q, refs) in st.behind() {
            let group = facts
                .places
                .get(q.index())
                .is_some_and(|i| matches!(roots.role(i.root), Some(Role::Group)));
            if !refs.is_empty() && (all || group) {
                keys.insert(*q);
            }
        }
    }
    let mut out: Vec<(IPlace, RetParts)> = Vec::new();
    for q in keys {
        let Some(into) = place(q) else {
            continue;
        };
        let values: Vec<(&super::State, super::AbsVal)> = returns
            .iter()
            .map(|st| {
                let mut v = super::AbsVal::none();
                v.fns = st.behind_fns().get(&q).cloned().unwrap_or_default();
                v.refs = st.behind().get(&q).cloned().unwrap_or_default();
                (st, v)
            })
            .collect();
        let parts = fn_parts_of(ir, &values, made, body, place);
        match out.iter_mut().find(|(k, _)| *k == into) {
            Some((_, have)) => {
                have.0.extend(parts.0);
                have.1.extend(parts.1);
                for (k, v) in parts.2 {
                    have.2.entry(k).or_default().extend(v);
                }
            }
            None => out.push((into, parts)),
        }
    }
    out
}

/// The changes and the effects of the closures `fns` that a body gives to
/// its callers (a result, or a value that it stores, stage F12 and F13): the
/// effects of each closure, of the closures that they give back, and the
/// changes through the references of their captures (`caps`), in the terms
/// of the interface of the function with signature `sig`. The old inference
/// puts them in the row (W0701, W0702 at a caller).
fn made_effects(
    sums: &Summaries,
    sig: &FnSig,
    (fns, caps): (
        &std::collections::BTreeSet<super::summary::RetFn>,
        &CapPlaces,
    ),
    changed: &mut Inferred,
) {
    let mut work: Vec<weft_ir::ClosureId> = fns
        .iter()
        .filter_map(|f| match f {
            super::summary::RetFn::Made(c) => Some(*c),
            _ => None,
        })
        .collect();
    let mut seen = std::collections::BTreeSet::new();
    while let Some(c) = work.pop() {
        if !seen.insert(c) {
            continue;
        }
        if let Ok(cs) = sums.closure(c) {
            changed
                .named
                .extend(cs.performs.iter().map(|pf| pf.effect.clone()));
            work.extend(cs.ret.fns.iter().filter_map(|f| match f {
                super::summary::RetFn::Made(x) => Some(*x),
                _ => None,
            }));
        }
    }
    for f in fns {
        if let super::summary::RetFn::Made(c) = f {
            if let Ok(cs) = sums.closure(*c) {
                for (m, _) in &cs.muts {
                    let (k, wild) = match m.root {
                        IRoot::CaptureHeld(k) => (k, false),
                        IRoot::CaptureDeep(k) => (k, true),
                        _ => continue,
                    };
                    for base in caps.get(&(*c, k)).into_iter().flatten() {
                        let mut steps = base.steps.clone();
                        if wild {
                            steps.push(IStep::Wild);
                        } else {
                            steps.extend(m.steps.iter().cloned());
                        }
                        let ip = IPlace::cut(base.root.clone(), steps);
                        let idx = match base.root {
                            IRoot::Param(i) | IRoot::Held(i) => {
                                super::sig::sig_root(sig, i as usize)
                            }
                            _ => continue,
                        };
                        changed.muts.push((ip, idx));
                    }
                }
            }
        }
    }
}

/// True if `_0` of body `body` can hold a linear closure (`Ret::linear`).
///
/// The value of `_0` at a `Return` state of `returns` is linear, and its
/// type has a function part. A type that can be linear (a linear type, a
/// type parameter) says so by itself.
pub fn ret_linear(
    ir: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    returns: &[super::State],
    body: BodyId,
) -> bool {
    let Some(b) = ir.body(body) else {
        return false;
    };
    let fn_part = b.local(b.ret).is_some_and(|d| {
        crate::props::ir_has_fns(tys, d.ty)
            && !crate::props::ir_maybe_linear(tys, d.ty)
            && !tys.mentions_param(d.ty)
    });
    fn_part
        && returns
            .iter()
            .any(|st| st.value((body, b.ret), &[]).flat().linear)
}

/// The interface places that the references of each capture of each closure
/// of a result point into ([`ret_fns_of`]).
type CapPlaces = BTreeMap<(weft_ir::ClosureId, u32), std::collections::BTreeSet<IPlace>>;

/// The function values of a result, the places of their environments, and
/// the places of each capture ([`ret_fns_of`]).
type RetParts = (
    std::collections::BTreeSet<super::summary::RetFn>,
    std::collections::BTreeSet<IPlace>,
    CapPlaces,
);

/// The interface place of fact place `p` of the facts of closure body
/// `body` in the terms of its interface (`docs/ir.md` 6.7), with its callee
/// root index: a place of a capture (`Capture`, `CaptureHeld`, and a place of
/// the value of a `ByMove` capture in the environment), of a parameter after
/// the environment (`Param`, `Held`, by the index of the argument), of an
/// `rc` group, or of a caller. With `frame`, a place of a local of the body
/// (or of a callee frame) is the wildcard place of the `Frame` root: a value
/// that leaves the body with a reference into its frame.
fn closure_place(
    ir: &weft_ir::Program,
    facts: &FnFacts,
    roots: &Roots,
    body: BodyId,
    p: PlaceId,
    frame: bool,
) -> Option<(IPlace, u32)> {
    let info = facts.places.get(p.index())?;
    let steps = steps_of(facts, p);
    let stored = crate::body::roots::STORED;
    let (root, idx, steps) = match roots.role(info.root)? {
        Role::Capture(b, k) if b == body => (IRoot::Capture(k), stored, steps),
        Role::CaptureHeld(b, k) if b == body => (IRoot::CaptureHeld(k), stored, steps),
        Role::CaptureDeep(b, k) if b == body => (IRoot::CaptureDeep(k), stored, steps),
        Role::Param(b, i) if b == body && i > 0 => (
            IRoot::Param(i - 1),
            crate::body::roots::param(i as usize - 1),
            steps,
        ),
        Role::Held(b, i) if b == body && i > 0 => (
            IRoot::Held(i - 1),
            crate::body::roots::param(i as usize - 1),
            steps,
        ),
        Role::Group => {
            let a = roots.group_adt(info.root)?;
            (
                IRoot::Group(a),
                crate::body::roots::group(crate::AdtId(a.index())),
                steps,
            )
        }
        Role::Caller => (IRoot::Caller, 0, steps),
        // The value of a `ByMove` capture is a part of the environment.
        Role::Local((b, l))
            if b == body && ir.body(b).and_then(|x| x.params.first()) == Some(&l) =>
        {
            let Some(IStep::Step(s, _)) = steps.first() else {
                return frame.then(|| (IPlace::wild(IRoot::Frame), 0));
            };
            let StepKind::Field { id } = s.kind else {
                return None;
            };
            // The reference of a `ByRef` capture is a part of the closure
            // value: its pointee is the `Capture` root.
            let by_move = ir
                .closure_of(body)
                .and_then(|(_, d)| d.captures.get(id as usize))
                .is_some_and(|c| c.mode == weft_ir::CaptureMode::ByMove);
            if !by_move {
                return None;
            }
            (
                IRoot::Capture(id),
                stored,
                steps.get(1..).unwrap_or(&[]).to_vec(),
            )
        }
        Role::Local((b, _)) if frame && b == body => return Some((IPlace::wild(IRoot::Frame), 0)),
        Role::Frame(_) if frame => return Some((IPlace::wild(IRoot::Frame), 0)),
        _ => return None,
    };
    Some((IPlace::cut(root, steps), idx))
}

/// The operands of terminator `t`.
fn term_operands(t: &TermKind) -> Vec<&weft_ir::Operand> {
    match t {
        TermKind::Call { callee, args, .. } => {
            let mut v: Vec<&weft_ir::Operand> = args.iter().collect();
            if let Callee::Value(op) = callee {
                v.push(op);
            }
            v
        }
        TermKind::Perform { args, .. } => args.iter().collect(),
        TermKind::Switch { on, .. } => vec![on],
        TermKind::Assert { cond, .. } => vec![cond],
        TermKind::Resume { arg, .. } => vec![arg],
        TermKind::Spawn { scope, task, .. } => vec![scope, task],
        TermKind::Join { task, .. } | TermKind::Detach { task, .. } => vec![task],
        TermKind::Fork { branches, .. } => branches.iter().collect(),
        _ => Vec::new(),
    }
}

/// The captures of closure `decl` that a statement or a terminator of
/// `body` moves: a `move` operand or a `Consume` at or below a `ByMove`
/// capture `env.k`.
fn moved_captures(
    b: &weft_ir::Body,
    decl: &weft_ir::ClosureDecl,
) -> std::collections::BTreeSet<u32> {
    use weft_ir::{CaptureMode, Operand, Proj, StmtKind};
    let env = b.params.first().copied();
    let mut out = std::collections::BTreeSet::new();
    let mut note = |q: &weft_ir::Place| {
        if Some(q.local) != env {
            return;
        }
        if let Some(Proj::Field(f)) = q.proj.first() {
            if decl
                .captures
                .get(f.index())
                .is_some_and(|c| c.mode == CaptureMode::ByMove)
            {
                out.insert(f.0);
            }
        }
    };
    for blk in &b.blocks {
        for s in &blk.stmts {
            match &s.kind {
                StmtKind::Consume(q) => note(q),
                StmtKind::Assign(_, rv) => {
                    for op in super::transfer::rvalue_operands(rv) {
                        if let Operand::Move(q) = op {
                            note(q);
                        }
                    }
                }
                StmtKind::Print(ops) => {
                    for op in ops {
                        if let Operand::Move(q) = op {
                            note(q);
                        }
                    }
                }
                _ => {}
            }
        }
        for op in term_operands(&blk.term.kind) {
            if let Operand::Move(q) = op {
                note(q);
            }
        }
    }
    out
}

/// The capture of closure `decl` that an assignment to place `q` of body `b`
/// gives a whole new value: `env.k` of a `Kept` capture, or `(*env.k)` of a
/// `ByRef` capture.
pub fn whole_capture(
    b: &weft_ir::Body,
    decl: &weft_ir::ClosureDecl,
    q: &weft_ir::Place,
) -> Option<u32> {
    use weft_ir::{CaptureMode, DerefKind, Proj};
    if Some(q.local) != b.params.first().copied() {
        return None;
    }
    let Some(Proj::Field(f)) = q.proj.first() else {
        return None;
    };
    let mode = decl.captures.get(f.index())?.mode;
    let whole = match mode {
        CaptureMode::Kept => q.proj.len() == 1,
        CaptureMode::ByRef => {
            q.proj.len() == 2 && q.proj.get(1) == Some(&Proj::Deref(DerefKind::Ref))
        }
        _ => false,
    };
    whole.then_some(f.0)
}

/// The captures of closure `decl` that body `b` gives a whole new value on
/// each normal path from its entry to a `Return` (part `rebinds`, a must
/// part): an assignment to `env.k` of a `Kept` capture or to `(*env.k)` of a
/// `ByRef` capture. A path that aborts has no `Ret` node at the call.
fn rebound_captures(
    b: &weft_ir::Body,
    decl: &weft_ir::ClosureDecl,
) -> std::collections::BTreeSet<u32> {
    use std::collections::BTreeSet;
    use weft_ir::{StmtKind, TermKind};
    let all: BTreeSet<u32> = (0..decl.captures.len())
        .filter_map(|k| u32::try_from(k).ok())
        .collect();
    let gives = |q: &weft_ir::Place| whole_capture(b, decl, q);
    let order = weft_ir::order::reverse_post_order(b);
    // The set at the entry of each block: `None` until a path reaches it.
    let mut at: Vec<Option<BTreeSet<u32>>> = vec![None; b.blocks.len()];
    if let Some(e) = at.get_mut(b.entry.index()) {
        *e = Some(BTreeSet::new());
    }
    let mut out: Option<BTreeSet<u32>> = None;
    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds <= b.blocks.len() + 1 {
        changed = false;
        rounds += 1;
        for &bid in &order {
            let (Some(blk), Some(Some(start))) = (b.blocks.get(bid.index()), at.get(bid.index()))
            else {
                continue;
            };
            if blk.cleanup {
                continue;
            }
            let mut set = start.clone();
            for s in &blk.stmts {
                if let StmtKind::Assign(q, _) = &s.kind {
                    set.extend(gives(q));
                }
            }
            if let TermKind::Call { dest, .. } = &blk.term.kind {
                set.extend(gives(dest));
            }
            if matches!(blk.term.kind, TermKind::Return) {
                out = Some(match out {
                    Some(o) => o.intersection(&set).copied().collect(),
                    None => set.clone(),
                });
            }
            for to in blk.term.kind.normal_successors() {
                let Some(slot) = at.get_mut(to.index()) else {
                    continue;
                };
                let next = match slot {
                    Some(old) => old.intersection(&set).copied().collect(),
                    None => set.clone(),
                };
                if slot.as_ref() != Some(&next) {
                    *slot = Some(next);
                    changed = true;
                }
            }
        }
    }
    out.unwrap_or_default()
        .intersection(&all)
        .copied()
        .collect()
}

/// The part `late_muts` of a closure summary: the interface places that the
/// facts `facts` change or lend at the nodes that come after a node of
/// `rebind_nodes` of a capture in `rebinds` (on some path). A call gives the
/// captures their new values at `Ret`, so these changes come at `Ret` too
/// (hole H1 of the review of the ABC preview: `|| { r = &v[0]; v.push(3) }`).
/// `place` gives the interface place of a fact place.
fn late_muts(
    facts: &FnFacts,
    rebinds: &std::collections::BTreeSet<u32>,
    rebind_nodes: &[(u32, weft_facts::NodeId)],
    place: &dyn Fn(PlaceId) -> Option<(IPlace, u32)>,
) -> Vec<(IPlace, u32)> {
    use std::collections::BTreeSet;
    let mut next: BTreeMap<weft_facts::NodeId, Vec<weft_facts::NodeId>> = BTreeMap::new();
    for &(a, b) in &facts.cfg_edge {
        next.entry(a).or_default().push(b);
    }
    let mut seen: BTreeSet<weft_facts::NodeId> = BTreeSet::new();
    let mut work: Vec<weft_facts::NodeId> = rebind_nodes
        .iter()
        .filter(|(k, _)| rebinds.contains(k))
        .flat_map(|(_, n)| next.get(n).cloned().unwrap_or_default())
        .collect();
    while let Some(n) = work.pop() {
        if seen.insert(n) {
            work.extend(next.get(&n).cloned().unwrap_or_default());
        }
    }
    let mut out: Vec<(IPlace, u32)> = facts
        .mutates_at
        .iter()
        .chain(facts.lends_mut.iter())
        .filter(|(n, _)| seen.contains(n))
        .filter_map(|&(_, m)| place(m))
        .collect();
    out.sort();
    out.dedup();
    out
}

/// The summary of closure body `body` from the facts `facts` of its
/// component in the terms of its interface (`docs/ir.md` 6.7, stage F11).
///
/// `returns` are the states before each `Return` of the body, `aborts` the
/// aborts of the summaries that the body applies at its calls of function
/// values, and `sums` the summaries that the fact generation applied.
///
/// - `muts`, `reads`, `lends`: the places of `mutates_at`, `reads_at` and
///   `lends_mut` whose root is a root of the interface (`closure_place`).
/// - `performs` and `aborts`: each effect of `escapes_at` (an operation of
///   it can abort), a failure or an `assert` of a callee or of the body.
/// - `uses`: each `Kept` and `ByRef` capture (the body names each capture).
/// - `moves`: each `ByMove` capture that the body moves.
/// - `rebinds`: each `Kept` or `ByRef` capture that each path to a `Return`
///   gives a whole new value.
/// - `puts`: the references of each heap slot of an interface place at a
///   `Return` (a store into a capture, a part of it or a place behind a
///   reference), and the new references of each `ByMove` capture; a
///   reference into a local of the body is the `Frame` root.
/// - `ret`: the places of `_0` at each `Return` that are in the interface (a
///   reference into a local is W0204 in the body).
/// - `runs`: each capture that the body calls (a function value of the
///   maker), `Many` if two calls or a call in a cycle run it.
#[allow(clippy::too_many_arguments)]
pub fn closure(
    ir: &weft_ir::Program,
    sums: &Summaries,
    facts: &FnFacts,
    roots: &Roots,
    body: BodyId,
    aborts: &std::collections::BTreeSet<Abort>,
    fv: &FnParts<'_>,
) -> super::summary::Summary {
    use super::summary::{CapIface, ParamIface, Perform, Summary};
    use std::collections::BTreeSet;
    let (returns, runs) = (fv.returns, fv.runs);
    let mut out = Summary::default();
    let Some((_, decl)) = ir.closure_of(body) else {
        return out;
    };
    let Some(b) = ir.body(body) else {
        return out;
    };
    for (j, &l) in b.params.iter().enumerate().skip(1) {
        let name = b
            .locals
            .get(l.index())
            .and_then(|d| d.name.clone())
            .unwrap_or_else(|| format!("parameter {j}"));
        out.params.push(ParamIface {
            name,
            root: crate::body::roots::param(j - 1),
            in_place: None,
        });
    }
    let place = |p: PlaceId| {
        let base = facts.wild_base(p).unwrap_or(p);
        closure_place(ir, facts, roots, body, base, false)
    };
    for &(_, m) in &facts.mutates_at {
        out.muts.extend(place(m));
    }
    out.muts.sort();
    out.muts.dedup();
    let mut reads: Vec<IPlace> = facts
        .reads_at
        .iter()
        .filter_map(|&(_, r)| place(r).map(|x| x.0))
        .collect();
    reads.sort();
    reads.dedup();
    out.reads = reads;
    // The lends of code of a caller at the runs of the values of the
    // interface are not lends of the closure: a caller applies the values
    // that it gives there (part `runs`; follow-up F13.2 for a closure that a
    // callee made, which runs the values that it holds). The lends of
    // another summary at such a node stay (`Em::own_lends`).
    let mut lends: Vec<IPlace> = facts
        .lends_mut
        .iter()
        .filter(|x| !fv.run_nodes.contains(&x.0) || fv.lends.contains(x))
        .filter_map(|&(_, r)| place(r).map(|x| x.0))
        .collect();
    lends.sort();
    lends.dedup();
    out.lends = lends;
    for (_, e) in &facts.escapes_at {
        let pf = Perform {
            effect: e.clone(),
            cap: CapIface::Row,
        };
        out.aborts.insert(Abort::Perform(pf.clone()));
        out.performs.insert(pf);
    }
    out.aborts.extend(aborts.iter().cloned());
    // A closure that performs through the capability of a caller can give
    // a place of its frame to an operation (plan stage F15).
    out.gives_frame = !facts.escapes_at.is_empty();
    // A node of the body that can resume more than once (a `multi`
    // operation, a callee that can): a run of the closure can.
    out.multi = !facts.multi_at.is_empty();
    for blk in &b.blocks {
        match &blk.term.kind {
            TermKind::Assert { .. } => {
                out.aborts.insert(Abort::Assert);
            }
            TermKind::Call {
                callee: Callee::Fn(f, _),
                ..
            } => {
                if let Ok(s) = sums.get(*f) {
                    for a in &s.aborts {
                        if matches!(a, Abort::Raises | Abort::Assert) {
                            out.aborts.insert(a.clone());
                        }
                    }
                    out.unknown_multi |= s.unknown_multi;
                }
            }
            _ => {}
        }
    }
    // The function values of the interface that the body runs: its captures
    // and its parameters (stage F12).
    out.runs = runs_of(
        runs,
        true,
        &|q| closure_place(ir, facts, roots, body, q, true).map(|x| x.0),
        Some(b),
    );
    out.uses = decl
        .captures
        .iter()
        .enumerate()
        .filter(|(_, c)| {
            matches!(
                c.mode,
                weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef
            )
        })
        .filter_map(|(k, _)| u32::try_from(k).ok())
        .collect();
    out.moves = moved_captures(b, decl);
    out.rebinds = rebound_captures(b, decl);
    out.late_muts = late_muts(facts, &out.rebinds, fv.rebind_nodes, &place);
    // The values that the body puts into interface places, and the result.
    let refs_of = |ps: &mut dyn Iterator<Item = PlaceId>| -> Vec<IPlace> {
        let mut v: Vec<IPlace> = ps
            .filter_map(|r| closure_place(ir, facts, roots, body, r, true).map(|x| x.0))
            .collect();
        v.sort();
        v.dedup();
        v
    };
    let mut puts: BTreeMap<IPlace, BTreeSet<IPlace>> = BTreeMap::new();
    let mut ret: BTreeSet<IPlace> = BTreeSet::new();
    let env = b.params.first().copied();
    for st in returns {
        for (q, refs) in st.behind() {
            let Some((into, _)) = closure_place(ir, facts, roots, body, *q, false) else {
                continue;
            };
            let rs = refs_of(&mut refs.iter().copied());
            if !rs.is_empty() {
                puts.entry(into).or_default().extend(rs);
            }
        }
        if let Some(env) = env {
            for (k, cap) in decl.captures.iter().enumerate() {
                if cap.mode != weft_ir::CaptureMode::ByMove {
                    continue;
                }
                let k32 = u32::try_from(k).unwrap_or(u32::MAX);
                let v = st.value((body, env), &[super::PathStep::Field(k32)]).flat();
                let rs = refs_of(&mut v.refs.iter().copied());
                if !rs.is_empty() {
                    puts.entry(IPlace::root(IRoot::Capture(k32)))
                        .or_default()
                        .extend(rs);
                }
            }
        }
        let r = st.value((body, b.ret), &[]).flat();
        for x in r.refs {
            if let Some((ip, _)) = closure_place(ir, facts, roots, body, x, false) {
                ret.insert(ip);
            }
        }
    }
    let iface = |q: PlaceId| closure_place(ir, facts, roots, body, q, false).map(|x| x.0);
    let (fns, places, _) = ret_fns_of(ir, returns, fv.made, body, &iface);
    out.ret.fns = fns.into_iter().collect();
    // The function values that the body puts into the heap slots of
    // interface places, with the places of their environments (stage F13).
    for (into, (fs, ps, _)) in
        stored_parts_of(ir, facts, roots, returns, fv.made, body, &iface, true)
    {
        if !ps.is_empty() {
            puts.entry(into.clone()).or_default().extend(ps);
        }
        if !fs.is_empty() {
            out.put_fns.push((into, fs.into_iter().collect()));
        }
    }
    ret.extend(places);
    out.puts = puts
        .into_iter()
        .map(|(k, v)| (k, v.into_iter().collect()))
        .collect();
    out.ret.places = ret.into_iter().collect();
    out
}
