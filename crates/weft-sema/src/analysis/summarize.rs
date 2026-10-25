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
    let runs = runs_of(fv.runs, false, &run_place);
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
        // The effects of a closure that the function gives back are in its
        // row, as the old inference says (W0701, W0702 at a caller): its
        // effects, and its changes through the references of its captures.
        // The effects of the closures that those closures give back too.
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
        for f in &fns {
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
        changed.ret_fns = fns;
        changed.ret_places = places;
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
) -> Vec<super::summary::Run> {
    let mut out: Vec<super::summary::Run> = Vec::new();
    for (r, many) in runs {
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
            many: *many,
            task: r.task,
            args,
            multi: r.multi,
        };
        // A second run node of the value runs it again.
        if let Some(x) = out
            .iter_mut()
            .find(|x| x.param == run.param && x.capture == run.capture)
        {
            x.many = true;
        }
        super::sig::join_run(&mut out, &run);
    }
    out
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
    use super::summary::RetFn;
    use super::FnVal;
    let mut fns = std::collections::BTreeSet::new();
    let mut places = std::collections::BTreeSet::new();
    let mut caps: CapPlaces = BTreeMap::new();
    let Some(b) = ir.body(body) else {
        return (fns, places, caps);
    };
    let one = |f: &FnVal| match f {
        FnVal::Item(g, t) => RetFn::Item(*g, t.clone()),
        FnVal::Closure(c) | FnVal::Made(c) => RetFn::Made(*c),
        FnVal::Param(i) => RetFn::Param(*i),
        FnVal::Capture(k) => RetFn::Capture(*k),
        FnVal::Unknown => RetFn::Unknown,
    };
    for st in returns {
        let v = st.value((body, b.ret), &[]).flat();
        places.extend(v.refs.iter().filter_map(|&q| place(q)));
        // The closures of the result, and the closures that their `Kept`
        // captures hold (a closure that runs a captured closure), each one
        // time.
        let mut work: Vec<FnVal> = v.fns.iter().cloned().collect();
        let mut seen = std::collections::BTreeSet::new();
        while let Some(f) = work.pop() {
            if !seen.insert(f.clone()) {
                continue;
            }
            fns.insert(one(&f));
            let FnVal::Closure(c) = f else {
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
                let Ok(k) = crate::factgen::alpha::owner_local(ir, decl.maker, cap.source.local)
                else {
                    fns.insert(RetFn::Unknown);
                    continue;
                };
                let mut src = st.value(k, &[]).flat();
                if let Some(m) = made {
                    src.join(&m.value(k, &[]).flat());
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

/// The captures of closure `decl` that body `b` gives a whole new value on
/// each normal path from its entry to a `Return` (part `rebinds`, a must
/// part): an assignment to `env.k` of a `Kept` capture or to `(*env.k)` of a
/// `ByRef` capture. A path that aborts has no `Ret` node at the call.
fn rebound_captures(
    b: &weft_ir::Body,
    decl: &weft_ir::ClosureDecl,
) -> std::collections::BTreeSet<u32> {
    use std::collections::BTreeSet;
    use weft_ir::{CaptureMode, DerefKind, Proj, StmtKind, TermKind};
    let env = b.params.first().copied();
    let all: BTreeSet<u32> = (0..decl.captures.len())
        .filter_map(|k| u32::try_from(k).ok())
        .collect();
    let gives = |q: &weft_ir::Place| -> Option<u32> {
        if Some(q.local) != env {
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
    };
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
    let mut lends: Vec<IPlace> = facts
        .lends_mut
        .iter()
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
    out.runs = runs_of(runs, true, &|q| {
        closure_place(ir, facts, roots, body, q, true).map(|x| x.0)
    });
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
    let (fns, places, _) = ret_fns_of(ir, returns, fv.made, body, &|q| {
        closure_place(ir, facts, roots, body, q, false).map(|x| x.0)
    });
    out.ret.fns = fns.into_iter().collect();
    ret.extend(places);
    out.puts = puts
        .into_iter()
        .map(|(k, v)| (k, v.into_iter().collect()))
        .collect();
    out.ret.places = ret.into_iter().collect();
    out
}
