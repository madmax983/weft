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
) -> Inferred {
    let mut out = Inferred::default();
    let mut changed = Inferred::default();
    let owned = owned_params(ir, tys, entry);
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
    out.join(&changed);
    out.named = facts
        .escapes_at
        .iter()
        .filter(|(n, _)| n.index() < nodes)
        .map(|(_, e)| e.clone())
        .collect();
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
    returns: &[super::State],
    aborts: &std::collections::BTreeSet<Abort>,
) -> super::summary::Summary {
    use super::summary::{CapIface, ParamIface, Perform, Run, Summary};
    use std::collections::BTreeSet;
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
    let cycles = super::widen::Cycles::of(ir, &[body]);
    let mut run_sites: BTreeMap<u32, (usize, bool)> = BTreeMap::new();
    for (bi, blk) in b.blocks.iter().enumerate() {
        let block = weft_ir::BlockId(u32::try_from(bi).unwrap_or(u32::MAX));
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
            TermKind::Call {
                callee: Callee::Value(weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q)),
                ..
            } if Some(&q.local) == b.params.first() && q.proj.len() == 1 => {
                if let Some(weft_ir::Proj::Field(f)) = q.proj.first() {
                    let e = run_sites.entry(f.0).or_insert((0, false));
                    e.0 += 1;
                    e.1 |= cycles.has(body, block);
                }
            }
            _ => {}
        }
    }
    out.runs = run_sites
        .into_iter()
        .map(|(k, (n, cyc))| Run {
            param: k,
            capture: true,
            many: n > 1 || cyc,
            task: false,
        })
        .collect();
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
    out.puts = puts
        .into_iter()
        .map(|(k, v)| (k, v.into_iter().collect()))
        .collect();
    out.ret.places = ret.into_iter().collect();
    out
}
