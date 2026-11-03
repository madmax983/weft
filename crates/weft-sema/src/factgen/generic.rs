//! The parts `drops` and `holds` of the summary of a generic body
//! (`docs/ir.md` 5.20, 6.7; plan stage F20).
//!
//! A generic body does not know if a value of a type parameter is linear: a
//! caller can give a linear type there. The fact generator writes the facts
//! of the component of such a body with each type parameter linear
//! (`crate::props::GenericBody`). A variable that is linear only through a
//! type parameter has these type parameters in `VarInfo::generic`.
//! [`finish`] then asks two queries over the facts, with the rules of the
//! spec for a linear value (`spec/weft.dl`, W0601 and W0602):
//!
//! - `drops`: the value is live where its variable goes out of scope or gets
//!   a new value (`unconsumed`, `overwritten`): the body drops it, or a `Dead`
//!   or an overwrite ends a value that can still be there.
//! - `holds`: the value is live at a node that can abort, or that can resume
//!   a `multi` continuation more than once (`abort_unhandled`, W0503), or it
//!   moves into a task that a scope can cancel before it runs.
//!
//! - `forks`: a `fork` branch captures a value that a type argument can make
//!   nonportable (OL-NR-ptrfork).
//!
//! A linear value whose `on abort` comes from a type argument (a `Task<T>`
//! handle) that is live at a node that can abort gives `holds` too (OL-3a).
//!
//! The type parameters of each such variable go to the part. Then the
//! variable loses the flag `linear`: the body itself has no error for a
//! value that is linear only if a caller makes it so. A caller checks the
//! parts with the type arguments of its call (`crate::factgen::templates`):
//! a variable of the type argument in a part of the graph of its own
//! ([`held_across`]), a dropped value, a `fork` branch.
//!
//! [`item_values`] gives the same checks to a generic function item as a
//! value (RR9, V081).

use std::collections::{BTreeSet, HashSet};

use weft_facts::{FnFacts, NodeId, VarId};

/// The type parameters that a generic body drops and holds.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Found {
    /// The type parameters of the values that the body drops (part `drops`).
    pub drops: BTreeSet<u32>,
    /// The type parameters of the values that the body holds across a node
    /// that can abort or resume more than once (part `holds`).
    pub holds: BTreeSet<u32>,
    /// The type parameters of the values that a `fork` branch captures
    /// (part `forks`, OL-NR-ptrfork): a nonportable type argument is W0401
    /// at a call.
    pub forks: BTreeSet<u32>,
}

/// True if a body of component `comp` has a local whose type names a type
/// parameter: the component of a generic body.
pub fn is_generic(p: &weft_ir::Program, tys: &weft_ir::TyTable, comp: &[weft_ir::BodyId]) -> bool {
    comp.iter().any(|&b| {
        p.bodies
            .get(b.index())
            .is_some_and(|x| x.locals.iter().any(|d| tys.mentions_param(d.ty)))
    })
}

/// The parts `drops`, `holds` and `forks` of the facts `facts` of a generic body (see the
/// module comment).
///
/// Each variable that is linear only through a type parameter then loses the flags `linear`
/// and `has_on_abort`.
pub fn finish(facts: &mut FnFacts) -> Found {
    let mut out = Found::default();
    // A `fork` branch that captures a value that a type argument can make
    // nonportable.
    let forks: HashSet<_> = facts
        .tasks
        .iter()
        .enumerate()
        .filter(|(_, t)| t.kind == weft_facts::TaskKind::Fork)
        .map(|(i, _)| i)
        .collect();
    for &(t, v) in &facts.captures {
        if forks.contains(&t.index()) {
            if let Some(info) = facts.vars.get(v.index()) {
                out.forks.extend(info.generic.nonportable.iter().copied());
            }
        }
    }
    let wanted: Vec<VarId> = facts
        .vars
        .iter()
        .enumerate()
        .filter(|(_, v)| {
            v.linear
                && (!v.generic.linear.is_empty()
                    || (v.has_on_abort && !v.generic.on_abort.is_empty()))
        })
        .map(|(i, _)| VarId(u32::try_from(i).unwrap_or(u32::MAX)))
        .collect();
    if wanted.is_empty() {
        return out;
    }
    let n = facts.nodes.len();
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &(a, b) in &facts.cfg_edge {
        if let Some(s) = succ.get_mut(a.index()) {
            s.push(b.index());
        }
    }
    let node_set = |rel: &[NodeId]| -> HashSet<usize> { rel.iter().map(|x| x.index()).collect() };
    let may_abort = node_set(&facts.may_abort);
    // A node that can resume more than once: `multi_at`, and the rules of
    // the spec over the clauses and the resumes.
    let mut multi = node_set(&facts.multi_at);
    let clause_multi: HashSet<_> = facts.clause_multi.iter().copied().collect();
    let body_multi: HashSet<_> = facts.body_multi.iter().copied().collect();
    for &(p, c) in &facts.performs_at {
        if clause_multi.contains(&c) {
            multi.insert(p.index());
        }
    }
    for &(p, c) in &facts.resumes_at {
        if clause_multi.contains(&c) || body_multi.contains(&c) {
            multi.insert(p.index());
        }
    }
    let spawns: HashSet<usize> = facts.spawned_at.iter().map(|(_, p)| p.index()).collect();
    for v in wanted {
        let pairs = |rel: &[(VarId, NodeId)]| -> HashSet<usize> {
            rel.iter()
                .filter(|(x, _)| *x == v)
                .map(|(_, p)| p.index())
                .collect()
        };
        let rebound = pairs(&facts.rebound_at);
        let empty = pairs(&facts.empty_at);
        let over = pairs(&facts.overwrites);
        let moved = pairs(&facts.moved_at);
        let rest = pairs(&facts.rest_linear);
        let ends_at = pairs(&facts.scope_end);
        let unwound = pairs(&facts.unwound_at);
        let spared = pairs(&facts.spared_at);
        let ends_linear = |p: usize| moved.contains(&p) && !rest.contains(&p);
        // `live_linear` of the spec: the nodes where the value is live.
        let mut live = vec![false; n];
        let mut work: Vec<usize> = Vec::new();
        for &p in rebound.iter().filter(|p| !empty.contains(p)).chain(&over) {
            work.extend(succ.get(p).into_iter().flatten().copied());
        }
        let (mut dropped, mut held, mut held_abort) = (false, false, false);
        while let Some(p) = work.pop() {
            if p >= n || std::mem::replace(&mut live[p], true) {
                continue;
            }
            if ends_at.contains(&p) || rebound.contains(&p) || over.contains(&p) {
                dropped = true;
            }
            if (may_abort.contains(&p) || multi.contains(&p))
                && !ends_linear(p)
                && !spared.contains(&p)
            {
                held = true;
                held_abort |= may_abort.contains(&p);
            }
            if !ends_linear(p) && !unwound.contains(&p) {
                work.extend(succ.get(p).into_iter().flatten().copied());
            }
        }
        // A value that moves into a task: a scope can cancel the task before
        // it runs, and the closure of the task goes away with the value.
        if moved.iter().any(|p| spawns.contains(p)) {
            held = true;
        }
        let Some(info) = facts.vars.get_mut(v.index()) else {
            continue;
        };
        // A value that is linear with no type parameter: its `on abort`
        // comes from the type arguments of a caller (part `holds`), and
        // the body checks the rest itself.
        if info.generic.linear.is_empty() {
            if held_abort {
                out.holds.extend(info.generic.on_abort.iter().copied());
            }
            continue;
        }
        if dropped {
            out.drops.extend(info.generic.linear.iter().copied());
        }
        if held {
            out.holds.extend(info.generic.linear.iter().copied());
        }
        info.linear = false;
        info.has_on_abort = false;
    }
    out
}

/// The checks of each generic function item as a value in the bodies
/// `comp` (`docs/ir.md` 5.20, 5.35; RR9, V081; `check_item_value` of the
/// old lowering).
///
/// Code that the body does not follow can run the value, so the checks of
/// a call of the item with the type arguments of the value apply at the
/// value, in a part of the graph of its own (no other value is live there):
/// a type argument in the part `holds` of the summary of the item gets a
/// variable that is live across a node that can abort or resume more than
/// once, as the item can (W0602, W0503); a type argument in the part
/// `drops` gets a value that goes away (W0601). In a generic body these
/// variables are linear through a type parameter too, so [`finish`] finds
/// them. `names` gives the name of a type parameter of an item.
pub fn item_values(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    sums: &crate::analysis::Summaries,
    comp: &[weft_ir::BodyId],
    names: &dyn Fn(weft_ir::FnId, u32) -> String,
    facts: &mut FnFacts,
) {
    use weft_ir::{Operand, StmtKind, TermKind};
    let mut found: Vec<(weft_ir::FnId, Vec<weft_ir::TyId>, weft_ir::Span)> = Vec::new();
    let mut add = |op: &Operand, at: weft_ir::Span| {
        if let Operand::Const(weft_ir::Const::Fn(f, targs)) = op {
            if !targs.is_empty() {
                found.push((*f, targs.clone(), at));
            }
        }
    };
    for &b in comp {
        let Some(body) = p.bodies.get(b.index()) else {
            continue;
        };
        for blk in &body.blocks {
            for s in &blk.stmts {
                if let StmtKind::Assign(_, rv) = &s.kind {
                    for op in crate::analysis::transfer::rvalue_operands(rv) {
                        add(op, s.origin.span);
                    }
                }
            }
            match &blk.term.kind {
                TermKind::Call { args, .. } | TermKind::Perform { args, .. } => {
                    for op in args {
                        add(op, blk.term.origin.span);
                    }
                }
                _ => {}
            }
        }
    }
    for (f, targs, at) in found {
        let (Ok(sum), Some(decl)) = (sums.get(f), p.fns.get(f.index())) else {
            continue;
        };
        if sum.holds.is_empty() && sum.drops.is_empty() {
            continue;
        }
        let item = decl
            .name
            .rsplit('.')
            .next()
            .unwrap_or(decl.name.as_str())
            .to_string();
        let span = weft_facts::Span {
            lo: at.lo,
            hi: at.hi,
        };
        let abort = sum.can_abort() || !sum.performs.is_empty();
        let multi = sum.multi || sum.unknown_multi;
        for &j in &sum.holds {
            let Some(&t) = targs.get(j as usize) else {
                continue;
            };
            if abort || multi {
                held_across(facts, tys, span, (names(f, j), &item), t, (abort, multi));
            }
        }
        for &j in &sum.drops {
            let Some(&t) = targs.get(j as usize) else {
                continue;
            };
            dropped_value(facts, tys, span, &item, t);
        }
    }
}

/// A variable of a value of type `t`, if the value can be linear (also
/// through a type parameter of a generic body).
fn linear_var(
    facts: &mut FnFacts,
    tys: &weft_ir::TyTable,
    span: weft_facts::Span,
    name: String,
    kind: weft_facts::VarKind,
    t: weft_ir::TyId,
) -> Option<VarId> {
    let props = crate::props::ir_props(tys, t);
    let (linear, generic) =
        super::vars::generic_linear(tys, t, crate::props::ir_strict_linear(tys, t));
    if !linear {
        return None;
    }
    let mut info = weft_facts::VarInfo::plain(name, kind, span, tys.show(t));
    info.linear = true;
    info.has_on_abort = props.on_abort;
    info.once = props.once;
    info.nonportable = props.nonportable;
    if props.on_abort && generic.is_empty() {
        info.generic.on_abort = super::vars::generic_abort(tys, t);
    }
    info.generic.nonportable = super::vars::generic_nonportable(tys, t);
    info.generic.linear = generic;
    Some(facts.add_var(info))
}

/// A value of type `t` that a callee holds across a node of its own.
///
/// The node can abort (`abort`) or resume more than once (`multi`), and it is in a
/// part of the graph of its own: a variable named `name.0` binds, the node of the
/// callee `name.1` comes, and the callee gives the value back (W0602, W0503 of the
/// variable; `hold_generic` of the old lowering).
pub fn held_across(
    facts: &mut FnFacts,
    tys: &weft_ir::TyTable,
    span: weft_facts::Span,
    name: (String, &str),
    t: weft_ir::TyId,
    (abort, multi): (bool, bool),
) {
    let Some(v) = linear_var(facts, tys, span, name.0, weft_facts::VarKind::Temp, t) else {
        return;
    };
    let b = facts.add_ir_node(span, "held by the callee", "held", "");
    let a = facts.add_ir_node(span, name.1, "held", "");
    let r = facts.add_ir_node(span, "given back by the callee", "held", "");
    facts.cfg_edge.push((b, a));
    facts.cfg_edge.push((a, r));
    facts.rebound_at.push((v, b));
    if abort {
        facts.may_abort.push(a);
    }
    if multi {
        facts.multi_at.push(a);
    }
    facts.uses.push((v, r));
    facts.moved_at.push((v, r));
}

/// A value of type `t` that the function item `item` drops, in a part of
/// the graph of its own (W0601 of the variable).
fn dropped_value(
    facts: &mut FnFacts,
    tys: &weft_ir::TyTable,
    span: weft_facts::Span,
    item: &str,
    t: weft_ir::TyId,
) {
    let Some(v) = linear_var(
        facts,
        tys,
        span,
        item.to_string(),
        weft_facts::VarKind::Dropped,
        t,
    ) else {
        return;
    };
    let b = facts.add_ir_node(span, item, "dropped", "");
    let d = facts.add_ir_node(span, "drop", "dropped", "");
    facts.cfg_edge.push((b, d));
    facts.rebound_at.push((v, b));
    facts.scope_end.push((v, d));
}
