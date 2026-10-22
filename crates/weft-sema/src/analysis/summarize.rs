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
//!   callee. An abort of an effect comes with its perform. Stage F7 adds
//!   `assert` and the aborts past the function.
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
) -> Inferred {
    let mut out = Inferred::default();
    let mut changed = Inferred::default();
    let owned = owned_params(ir, tys, entry);
    for &(_, m) in &facts.mutates_at {
        let base = facts.wild_base(m).unwrap_or(m);
        if let Some(mp) = interface_place(facts, roots, entry, sig, &owned, base) {
            changed.muts.push(mp);
        }
    }
    changed.muts.sort();
    changed.muts.dedup();
    out.join(&changed);
    out.named = facts.escapes_at.iter().map(|(_, e)| e.clone()).collect();
    for &b in comp {
        let Some(body) = ir.bodies.get(b.index()) else {
            continue;
        };
        for blk in &body.blocks {
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
            if s.unknown_multi {
                out.multi = true;
            }
        }
    }
    out
}
