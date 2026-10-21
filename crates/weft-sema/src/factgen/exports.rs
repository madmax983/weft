//! The exports of the `ir` pipeline for the AST compiler of the interpreter:
//! `FnFacts::by_value`, `FnFacts::arg_order` and `FnFacts::int_ops`.
//!
//! These fields are not relations of the spec. The AST compiler reads them by
//! the span of the expression, so `--engine=ast` can run a program that the
//! `ir` pipeline checked. The `ir` pipeline gives the decisions of the IR:
//!
//! - `by_value`: the captures that a closure aggregate of the IR moves (rule
//!   CAPTURE, `docs/ir.md` 5.1.7): each `ByMove` capture, and each `Kont`
//!   capture of a `once` continuation (its operand is a `move`). The key is
//!   the origin of the aggregate: the closure literal.
//! - `arg_order`: the argument of each parameter, as the IR evaluates the
//!   arguments (THIR `CallInfo::args`, `docs/ir.md` 5.18 and 5.21), for the
//!   calls whose callee the AST compiler does not know: a method of a value
//!   receiver and a call of a local, with named arguments.
//! - `int_ops`: the integer type of each operator of the IR (THIR `int_ty`;
//!   a compound assignment has its entry at its value).
//!
//! A body with no IR keeps the exports of the old lowering: the IR has no
//! decision for it.

use std::collections::BTreeMap;

use weft_facts::{FnFacts, VarId, VarInfo, VarKind};
use weft_ir::{
    AggKind, BodyId, CaptureMode, LocalDecl, LocalKind, Operand, Place, Program, Proj, Rvalue,
    StmtKind,
};
use weft_syntax::ast::{self, ExprKind, Span};

use crate::irbuild::scope::body_entries;
use crate::irbuild::{walk_block, Built, Outcome};
use crate::thir::{Callee, Tables};
use crate::Analysis;

/// Fills the exports of `facts` (one for each body of `a`) from the IR of
/// `built`, or from the old facts for a body with no IR.
pub(super) fn fill(a: &Analysis, built: &Built, facts: &mut [FnFacts]) {
    let funcs = a.bodies.iter().filter(|b| b.func.is_some()).count();
    for (i, e) in built.entries.iter().enumerate() {
        let (Some(old), Some(f)) = (a.bodies.get(i), facts.get_mut(i)) else {
            continue;
        };
        if !matches!(e.outcome, Outcome::Built(_)) {
            copy_old(&old.facts, f);
            continue;
        }
        let block = match old.func {
            Some(id) => a
                .program
                .fns
                .get(id.index())
                .and_then(|d| d.decl.body.as_ref()),
            None => i
                .checked_sub(funcs)
                .and_then(|j| a.program.tests.get(j))
                .map(|t| &t.body),
        };
        if let (Some(block), Some(t)) = (block, a.thir.get(i)) {
            from_thir(t, block, f);
        }
    }
    captures(built, facts);
}

/// Copies the exports of the old lowering.
fn copy_old(old: &FnFacts, f: &mut FnFacts) {
    for &(span, v) in &old.by_value {
        let name = old.var(v).name.clone();
        let v = var_named(f, &name);
        f.by_value.push((span, v));
    }
    f.arg_order.clone_from(&old.arg_order);
    f.int_ops.clone_from(&old.int_ops);
}

/// The variable of `f` with the name `name`: an existing one, or a new one
/// with no facts. The interpreter reads only the name of a variable of
/// `by_value`.
fn var_named(f: &mut FnFacts, name: &str) -> VarId {
    if let Some(i) = f.vars.iter().position(|v| v.name == name) {
        return VarId(u32::try_from(i).unwrap_or(u32::MAX));
    }
    f.add_var(VarInfo {
        name: name.to_string(),
        kind: VarKind::Local,
        span: Span::default(),
        ty: String::new(),
        linear: false,
        has_on_abort: false,
        once: false,
        immovable: false,
        uniq: false,
        nonportable: false,
        callable: false,
    })
}

/// The argument orders and the integer types of the expressions of `block`.
fn from_thir(t: &Tables, block: &ast::Block, f: &mut FnFacts) {
    walk_block(block, &mut |x| {
        if let Some(it) = t.int_ty.get(&x.id) {
            f.int_ops.push((x.span, it.name().to_string()));
        }
        let (args, call) = match &x.kind {
            ExprKind::Call { args, .. } | ExprKind::MethodCall { args, .. } => {
                (args, t.call.get(&x.id))
            }
            _ => return,
        };
        let Some(call) = call else {
            return;
        };
        let unknown = call.recv.is_some() || matches!(call.callee, Callee::Value(_));
        if unknown && args.iter().any(|a| a.name.is_some()) {
            f.arg_order.push((x.span, call.args.clone()));
        }
    });
}

/// The captures that the closure aggregates of the IR move, into the facts of
/// the body of each aggregate.
fn captures(built: &Built, facts: &mut [FnFacts]) {
    let p = &built.program;
    // The moved names of each aggregate, by the entry and the span, in order.
    let mut moved: BTreeMap<(usize, Span), Vec<String>> = BTreeMap::new();
    for (b, entry) in p.bodies.iter().zip(body_entries(built)) {
        let Some(entry) = entry else {
            continue;
        };
        for blk in &b.blocks {
            for s in &blk.stmts {
                let StmtKind::Assign(_, Rvalue::Aggregate(AggKind::Closure(c), ops)) = &s.kind
                else {
                    continue;
                };
                let Some(decl) = p.closures.get(c.index()) else {
                    continue;
                };
                let o = s.origin.span;
                let key = (entry, Span { lo: o.lo, hi: o.hi });
                let names = moved.entry(key).or_default();
                for (k, cap) in decl.captures.iter().enumerate() {
                    let moves_kont = cap.mode == CaptureMode::Kont
                        && matches!(ops.get(k), Some(Operand::Move(_)));
                    if cap.mode != CaptureMode::ByMove && !moves_kont {
                        continue;
                    }
                    if let Some(name) =
                        var_decl(p, decl.maker, &cap.source).and_then(|d| d.name.clone())
                    {
                        names.push(name);
                    }
                }
            }
        }
    }
    for ((entry, span), names) in moved {
        let Some(f) = facts.get_mut(entry) else {
            continue;
        };
        for name in names {
            let v = var_named(f, &name);
            f.by_value.push((span, v));
        }
    }
}

/// The declaration of the variable that `place` of body `body` names: a user
/// local or a parameter, through upvar locals and the captures of closure
/// bodies.
fn var_decl<'p>(p: &'p Program, body: BodyId, place: &Place) -> Option<&'p LocalDecl> {
    let mut body = body;
    let mut place = place.clone();
    // Each step goes to a parent body, which has a lower id, so the walk ends.
    for _ in 0..=p.bodies.len() {
        let b = p.bodies.get(body.index())?;
        let decl = b.locals.get(place.local.index())?;
        match decl.kind {
            LocalKind::Upvar(l) => {
                body = b.parent?;
                place = Place {
                    local: l,
                    proj: place.proj,
                };
            }
            LocalKind::Env => {
                let Some(Proj::Field(k)) = place.proj.first() else {
                    return None;
                };
                let c = p.closures.iter().find(|c| c.body == body)?;
                let cap = c.captures.get(k.index())?;
                body = c.maker;
                place = cap.source.clone();
            }
            _ => return Some(decl),
        }
    }
    None
}
