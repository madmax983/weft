//! Checks in Rust over the summaries (`docs/ir.md` 6.9).
//!
//! W0118 is a query over the summary of each `on abort` function
//! ([`on_abort_rows`]): its changes are below its parameter value (F3-1),
//! its row holds only effects that the root handlers serve, its `raises`
//! part is empty, and its `drops` and `holds` parts hold no type parameter
//! of its parameter type (F3-3, F3-4). The texts are those of the old
//! pipeline (`crate::program::on_abort_row`).
//!
//! The check of a function item as a value with type arguments
//! (`docs/ir.md` 5.35, `check_item_value` of the old lowering) is
//! `super::generic::item_values` (plan stage F20).
//!
//! [`cap_escapes`] is W0313 for a capability (`docs/ir.md` 6.9, plan stage
//! F17): a closure that captures the capability of a handler leaves the
//! `handle` (the analysis finds it at the end of the handled body,
//! `crate::analysis::clause::Escape`).

use weft_syntax::diag::Diagnostic;

use crate::analysis::sig::to_effect_sig;
use crate::analysis::Summaries;
use crate::irbuild::Built;
use crate::program::{on_abort_fns, on_abort_row};
use crate::Analysis;

/// W0118 for each `on abort` function of the analysis `a`, from its
/// summary in `sums` (`docs/ir.md` 6.9).
///
/// The summary gives the row: the
/// changed places (`muts`), the effects through the capability of a caller
/// (`performs`), `raises`, `drops` and `holds`
/// (`crate::analysis::sig::to_effect_sig`), and `reaches` (`checks::reaches`). A
/// function with no summary (an extern function that no body calls) keeps
/// its declaration. No row comes from the old inference (plan stage R0i).
/// `no_runtime`: no root handler serves an effect.
pub fn on_abort_rows(
    a: &Analysis,
    built: &Built,
    sums: &Summaries,
    no_runtime: bool,
) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for f in on_abort_fns(&a.program) {
        let Some(sig) = a.program.fns.get(f.index()).map(|def| &def.sig) else {
            continue;
        };
        let row = built
            .fns
            .get(&f)
            .and_then(|g| sums.get(*g).ok())
            .map_or_else(
                || sig.effects.clone(),
                |s| {
                    let mut row = to_effect_sig(&a.program, s);
                    // The worst case of a body with no IR runs each value
                    // of its parameter; the program has an error for the
                    // body, and the other parts of the worst case give
                    // W0118 already.
                    let decl = built
                        .fns
                        .get(&f)
                        .and_then(|g| built.program.fns.get(g.index()))
                        .filter(|d| d.body.is_some());
                    row.reaches = decl.is_some_and(|d| reaches(&built.tys, d, s));
                    row
                },
            );
        out.extend(on_abort_row(&a.program, f, sig, &row, no_runtime));
    }
    out
}

/// True if a function with declaration `d` and summary `s` can run a
/// function value that it does not know (`reaches` of W0118, class D-W0118
/// of stage F17). Such a value can do what its maker can, so an `on abort`
/// function cannot run it (plan stage R0i: the old inference gave this
/// part). It is one of:
///
/// - a run of the part `runs` of a capture, or of a value of a parameter
///   whose type has a function part: a call or a task, also through a
///   callee. A task counts: a local `Fail` handler around its scope can
///   catch the failure of the scope, so no other W0118 names it (R0i fix,
///   `fixes/r0i/r31_*`). A parameter with no function part in its type
///   (a value of a type parameter, `s.spawn(|| x)`) runs no code that a
///   caller made;
/// - a run of a value that no part of the interface names (the part
///   `unknown_runs`: a value from an `rc` object, the result of an extern
///   function), also through a callee, and also in a program with no
///   `multi` operation. The part `unknown_multi` does not count: the worst
///   case of a callee with no IR has it (it can resume more than once) and
///   runs no value (`fixes/r0i/r28_*`).
fn reaches(tys: &weft_ir::TyTable, d: &weft_ir::FnDecl, s: &crate::analysis::Summary) -> bool {
    let fn_part = |j: u32| {
        d.params
            .get(j as usize)
            .is_some_and(|&t| crate::props::ir_has_fns(tys, t))
    };
    s.unknown_runs || s.runs.iter().any(|r| r.capture || fn_part(r.param))
}

/// The span of the `handle` of handler `h`: the `handle` terminator of its
/// site, else the handled body. W0313 of the handler has this span.
pub fn handle_span(p: &weft_ir::Program, h: weft_ir::HandlerId) -> Option<weft_ir::Span> {
    let d = p.handlers.get(h.index())?;
    let origin = p.body(d.site).and_then(|b| {
        b.blocks
            .iter()
            .find(|x| matches!(x.term.kind, weft_ir::TermKind::Handle { handler, .. } if handler == h))
            .map(|x| x.term.origin.span)
    });
    origin.or_else(|| p.body(d.handled).map(|b| b.origin.span))
}

/// W0313 for each handler of `escapes` (`docs/ir.md` 6.9).
///
/// A closure that captures the capability of the handler leaves the
/// `handle`: in the value of the `handle`, in a local of the site or in a
/// heap slot. The span is the `handle` expression and the texts are those
/// of the old lowering (`check_cap_escape`).
pub fn cap_escapes(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    escapes: &[(weft_ir::HandlerId, crate::analysis::clause::Escape)],
) -> Vec<Diagnostic> {
    use crate::analysis::clause::Escape;
    use weft_syntax::diag::Code;
    let mut out = Vec::new();
    for (h, how) in escapes {
        let Some(d) = p.handlers.get(h.index()) else {
            continue;
        };
        if let Escape::Kont(cb, k) = how {
            out.extend(kont_escape(p, tys, *cb, k));
            continue;
        }
        let effect = tys
            .effects()
            .get(d.effect.index())
            .map_or_else(String::new, |e| e.name.clone());
        let Some(sp) = handle_span(p, *h) else {
            continue;
        };
        let head = format!("a closure that performs `{effect}` escapes its handler");
        let msg = match how {
            Escape::Value => head,
            Escape::Local(name) => format!("{head}: the local `{name}` keeps it"),
            Escape::Stored => format!("{head}: the body stores it"),
            Escape::Given | Escape::Kont(..) => {
                format!("{head}: the body gives it to code that can keep it")
            }
        };
        let span = weft_syntax::ast::Span {
            lo: sp.lo,
            hi: sp.hi,
        };
        let mut diag = Diagnostic::error(Code::W0313, msg, span);
        diag.unit = sp.unit as usize;
        out.push(diag);
    }
    out
}

/// W0313 for a closure that resumes the continuation of clause `cb` and
/// leaves the clause (stage R0g): the span is the clause, and the texts are
/// those of the old lowering (`check_cont_escape`, `cont_to_body`).
fn kont_escape(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    cb: weft_ir::BodyId,
    how: &crate::analysis::clause::KontEscape,
) -> Option<Diagnostic> {
    use crate::analysis::clause::KontEscape;
    use weft_syntax::diag::Code;
    let b = p.body(cb)?;
    let weft_ir::BodyKind::Clause(h, op) = b.kind else {
        return None;
    };
    let e = p.handlers.get(h.index())?.effect;
    let op = tys
        .effects()
        .get(e.index())
        .and_then(|d| d.ops.get(op.index()))
        .map_or_else(String::new, |o| o.name.clone());
    let head = format!("a closure that resumes the continuation of `{op}` escapes its clause");
    let msg = match how {
        KontEscape::Value => format!("{head}: it is the value of the clause"),
        KontEscape::Local(Some(name)) => format!("{head}: the local `{name}` keeps it"),
        KontEscape::Local(None) | KontEscape::Stored => format!("{head}: the clause stores it"),
        KontEscape::Resumed => {
            "a `resume` gives the handled computation a closure that resumes a continuation"
                .to_string()
        }
    };
    let sp = b.origin.span;
    let span = weft_syntax::ast::Span {
        lo: sp.lo,
        hi: sp.hi,
    };
    let mut diag = Diagnostic::error(Code::W0313, msg, span);
    diag.unit = sp.unit as usize;
    Some(diag)
}

/// W0314 (`docs/ir.md` 6.9, plan stage F19): one error for each span and
/// text of `found` (`templates::task_w0314`).
pub fn w0314(found: &[(weft_ir::Span, String)]) -> Vec<Diagnostic> {
    use weft_syntax::diag::Code;
    let mut seen = std::collections::BTreeSet::new();
    let mut out = Vec::new();
    for (sp, msg) in found {
        if !seen.insert((sp.unit, sp.lo, sp.hi, msg.clone())) {
            continue;
        }
        let span = weft_syntax::ast::Span {
            lo: sp.lo,
            hi: sp.hi,
        };
        let mut diag = Diagnostic::error(Code::W0314, msg.clone(), span);
        diag.unit = sp.unit as usize;
        out.push(diag);
    }
    out
}

/// Rule A of plan stage R0z (Z1): true if closure `c` captures a
/// continuation (a `Kont` capture).
///
/// A closure that a body of the closure
/// makes and that captures a continuation makes the closure capture it too.
pub fn closure_konts(p: &weft_ir::Program, c: weft_ir::ClosureId) -> bool {
    p.closures.get(c.index()).is_some_and(|d| {
        d.captures
            .iter()
            .any(|k| k.mode == weft_ir::CaptureMode::Kont)
    })
}

/// The structural check of rule A of plan stage R0z (Z1).
///
/// It runs on the bodies
/// `bodies` (the components of the bodies whose analysis stops with a
/// `Later`): W0314 at each spawn or `fork` branch whose task is a closure on
/// the static way of its body (the one value of a local of the body) that
/// holds a continuation (a `Kont` capture) or the capability of a local
/// handler that is not a `Fail` handler (a `Cap` capture). A closure or an
/// aggregate that a capture holds on the static way of the body of the maker
/// counts too. The texts are those of the old pipeline.
pub fn task_konts(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    bodies: &[weft_ir::BodyId],
) -> Vec<Diagnostic> {
    use weft_ir::TermKind;
    let mut found: Vec<(weft_ir::Span, String)> = Vec::new();
    for &b in bodies {
        let Some(body) = p.body(b) else {
            continue;
        };
        for blk in &body.blocks {
            let tasks: Vec<(&weft_ir::Operand, weft_ir::SpawnId)> = match &blk.term.kind {
                TermKind::Spawn { task, site, .. } => vec![(task, *site)],
                TermKind::Fork {
                    branches, sites, ..
                } => branches.iter().zip(sites.iter().copied()).collect(),
                _ => Vec::new(),
            };
            for (op, site) in tasks {
                let Some(held) = static_held(p, tys, b, op) else {
                    continue;
                };
                let at = p
                    .spawns
                    .get(site.index())
                    .map_or(blk.term.origin.span, |d| d.origin.span);
                let msg = match held {
                    Held::Kont => super::templates::KONT_TASK,
                    Held::Cap => {
                        "a task cannot perform through a handler of this task: the handler runs on another task"
                    }
                };
                found.push((at, msg.to_string()));
            }
        }
    }
    w0314(&found)
}

/// What a task value holds that a task cannot hold ([`task_konts`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Held {
    /// A continuation.
    Kont,
    /// The capability of a local handler.
    Cap,
}

/// What the value of operand `op` of body `b` holds on the static way
/// ([`task_konts`]), if it holds a continuation or the capability of a local
/// handler that is not a `Fail` handler.
fn static_held(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    b: weft_ir::BodyId,
    op: &weft_ir::Operand,
) -> Option<Held> {
    // The work: a body, an operand, and the depth of the closures: 0 for
    // the closure of the task, more for a closure that a capture holds.
    let mut work: Vec<(weft_ir::BodyId, weft_ir::Operand, usize)> = vec![(b, op.clone(), 0)];
    let mut seen_closures = std::collections::BTreeSet::new();
    let mut steps = 0usize;
    let mut cap = false;
    while let Some((b, op, depth)) = work.pop() {
        steps += 1;
        if steps
            > 4 * p
                .bodies
                .len()
                .saturating_add(p.closures.len())
                .saturating_add(8)
        {
            break;
        }
        let (weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q)) = &op else {
            continue;
        };
        if !q.proj.is_empty() {
            continue;
        }
        let Some(rv) = one_def(p, b, q.local) else {
            continue;
        };
        match rv {
            weft_ir::Rvalue::Use(x) => work.push((b, x.clone(), depth)),
            weft_ir::Rvalue::Aggregate(weft_ir::AggKind::Closure(c), ops) => {
                if !seen_closures.insert(*c) {
                    continue;
                }
                let Some(d) = p.closures.get(c.index()) else {
                    continue;
                };
                for (k, x) in d.captures.iter().enumerate() {
                    match x.mode {
                        weft_ir::CaptureMode::Kont => return Some(Held::Kont),
                        weft_ir::CaptureMode::Cap => {
                            // The closure of the task holds the capability
                            // only if its code uses it (as the old pipeline:
                            // the operations of the summary of the task); a
                            // closure that a capture holds holds it.
                            if let Some(h) = cap_capture_handler(p, tys, *c, k) {
                                cap |= depth > 0 || cap_used(p, tys, d.body, h);
                            }
                        }
                        _ => {}
                    }
                }
                work.extend(ops.iter().map(|o| (b, o.clone(), depth + 1)));
            }
            weft_ir::Rvalue::Aggregate(_, ops) => {
                work.extend(ops.iter().map(|o| (b, o.clone(), depth)));
            }
            _ => {}
        }
    }
    cap.then_some(Held::Cap)
}

/// True if the code of closure body `cb` (and of the bodies inside it with
/// no closure body between them) uses the capability of handler `h` on the
/// static way: a perform through it, a call of a function whose stated row
/// has the effect of `h` where `h` serves it, or a closure with a `Cap`
/// capture of `h` (or the result of such a call whose function type has the
/// effect in its row) that the code reads (runs, gives or keeps) or writes
/// into a local outside the closure body ([`static_held`]).
fn cap_used(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    cb: weft_ir::BodyId,
    h: weft_ir::HandlerId,
) -> bool {
    use weft_ir::{Callee, CapArgs, Operand, Rvalue, StmtKind, TermKind};
    let Some(e) = p.handlers.get(h.index()).map(|d| d.effect) else {
        return true;
    };
    let ident = tys.effects().get(e.index()).map(|d| d.identity.clone());
    let bodies: Vec<weft_ir::BodyId> = (0..p.bodies.len())
        .filter_map(|i| u32::try_from(i).ok().map(weft_ir::BodyId))
        .filter(|&y| inside_no_closure(p, y, cb))
        .collect();
    let handler_of = |y: weft_ir::BodyId, place: &weft_ir::Place| {
        crate::analysis::clause::cap_handler(p, y, place).or_else(|| {
            let (c, k, _) = crate::factgen::alpha::env_capture(p, y, place)?;
            crate::analysis::clause::capture_handler(p, c, k)
        })
    };
    // The locals (by their owner) that get a closure with a capture of `h`.
    let mut holders: Vec<(weft_ir::BodyId, weft_ir::LocalId)> = Vec::new();
    for &y in &bodies {
        let Some(body) = p.body(y) else {
            continue;
        };
        for blk in &body.blocks {
            for st in &blk.stmts {
                if let StmtKind::Assign(q, Rvalue::Aggregate(weft_ir::AggKind::Closure(c2), _)) =
                    &st.kind
                {
                    let n = p.closures.get(c2.index()).map_or(0, |d| d.captures.len());
                    if (0..n).any(|k| cap_capture_handler(p, tys, *c2, k) == Some(h)) {
                        let Ok(o) = crate::factgen::alpha::owner_local(p, y, q.local) else {
                            return true;
                        };
                        if !bodies.contains(&o.0) || !q.proj.is_empty() {
                            return true;
                        }
                        holders.push(o);
                    }
                }
            }
            match &blk.term.kind {
                TermKind::Perform {
                    cap: weft_ir::CapOperand::Local(place),
                    ..
                } if handler_of(y, place) == Some(h) => return true,
                TermKind::Call {
                    callee: Callee::Fn(f, _),
                    caps: CapArgs::Lexical(env),
                    ..
                } => {
                    let stated = p
                        .fns
                        .get(f.index())
                        .and_then(|d| d.stated_row.as_ref())
                        .is_some_and(|r| r.contains(&e));
                    // The closure of the task binds the effect to its capture
                    // (`resolve` gives `Past` for a closure environment), or
                    // the handler of the capture serves it.
                    let serves = ident.as_ref().is_some_and(|id| {
                        match super::frames::resolve(p, tys, *env, id, true) {
                            super::frames::Dest::Handler { handler, .. } => handler == h,
                            super::frames::Dest::Past => true,
                        }
                    });
                    if stated && serves {
                        return true;
                    }
                    // A result whose function type has the effect in its row
                    // holds the capability of the call: as a closure with the
                    // capture.
                    let holds = |q: &weft_ir::Place| {
                        body.local(q.local).is_some_and(|d| {
                            matches!(tys.try_get(d.ty), Some(weft_ir::Ty::Fn(ft))
                                if ft.row.as_ref().is_some_and(|r| r.contains(&e)))
                        })
                    };
                    if let TermKind::Call { dest, .. } = &blk.term.kind {
                        if serves && holds(dest) {
                            let Ok(o) = crate::factgen::alpha::owner_local(p, y, dest.local) else {
                                return true;
                            };
                            if !bodies.contains(&o.0) || !dest.proj.is_empty() {
                                return true;
                            }
                            holders.push(o);
                        }
                    }
                }
                _ => {}
            }
        }
    }
    if holders.is_empty() {
        return false;
    }
    // A read of a holder: an operand of a statement or of a terminator.
    for &y in &bodies {
        let Some(body) = p.body(y) else {
            continue;
        };
        let reads = |op: &Operand| match op {
            Operand::Copy(q) | Operand::Move(q) => {
                crate::factgen::alpha::owner_local(p, y, q.local)
                    .is_ok_and(|o| holders.contains(&o))
            }
            Operand::Const(_) => false,
        };
        let place_reads = |q: &weft_ir::Place| {
            crate::factgen::alpha::owner_local(p, y, q.local).is_ok_and(|o| holders.contains(&o))
        };
        for blk in &body.blocks {
            for st in &blk.stmts {
                if let StmtKind::Assign(_, rv) = &st.kind {
                    if crate::analysis::transfer::rvalue_operands(rv)
                        .into_iter()
                        .any(&reads)
                    {
                        return true;
                    }
                    if let Rvalue::Ref(q) | Rvalue::Len(q) | Rvalue::Discriminant(q) = rv {
                        if place_reads(q) {
                            return true;
                        }
                    }
                }
            }
            let mut ops: Vec<&Operand> = Vec::new();
            match &blk.term.kind {
                TermKind::Call { callee, args, .. } => {
                    if let Callee::Value(v) = callee {
                        ops.push(v);
                    }
                    ops.extend(args.iter());
                }
                TermKind::Switch { on, .. } => ops.push(on),
                t => ops.extend(crate::factgen::term_operands(t)),
            }
            if ops.into_iter().any(&reads) {
                return true;
            }
        }
    }
    false
}

/// The rvalue of the one assignment of the whole local `l` of body `b`, if
/// the body assigns it once and no statement of the body assigns a part of
/// it.
fn one_def(
    p: &weft_ir::Program,
    b: weft_ir::BodyId,
    l: weft_ir::LocalId,
) -> Option<&weft_ir::Rvalue> {
    let body = p.body(b)?;
    let mut out = None;
    for blk in &body.blocks {
        for s in &blk.stmts {
            if let weft_ir::StmtKind::Assign(q, rv) = &s.kind {
                if q.local != l {
                    continue;
                }
                if out.is_some() || !q.proj.is_empty() {
                    return None;
                }
                out = Some(rv);
            }
        }
    }
    out
}

/// An error with code `code`, text `msg`, at span `sp` of the IR.
pub fn error_at(
    code: weft_syntax::diag::Code,
    sp: weft_ir::Span,
    msg: impl Into<String>,
) -> Diagnostic {
    let span = weft_syntax::ast::Span {
        lo: sp.lo,
        hi: sp.hi,
    };
    let mut d = Diagnostic::error(code, msg.into(), span);
    d.unit = sp.unit as usize;
    d
}

/// The local handler that the `Cap` capture `k` of closure `c` names, if its
/// effect is not `Fail`.
pub fn cap_capture_handler(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    c: weft_ir::ClosureId,
    k: usize,
) -> Option<weft_ir::HandlerId> {
    let k = u32::try_from(k).ok()?;
    let h = crate::analysis::clause::capture_handler(p, c, k)?;
    let d = p.handlers.get(h.index())?;
    let e = tys.effects().get(d.effect.index())?;
    (e.identity != super::frames::FAIL).then_some(h)
}

/// Rule D of plan stage R0z (Z1), the structural form for an operation of
/// the handler itself.
///
/// It runs on the bodies
/// `bodies` (the components of the bodies whose analysis stops with a
/// `Later`, and of the bodies that reach them): W0313 for a closure that
/// performs through the capability of a local handler H and that a perform
/// of an operation of H itself gets as an argument (the closure on the
/// static way of the body). The clause runs outside H, and it can keep its
/// parameter. The span is the `handle` of H, and the text is that of the old
/// pipeline.
pub fn own_op_escapes(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    bodies: &[weft_ir::BodyId],
) -> Vec<Diagnostic> {
    use weft_ir::TermKind;
    let mut out = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for &b in bodies {
        let Some(body) = p.body(b) else {
            continue;
        };
        for blk in &body.blocks {
            let TermKind::Perform {
                cap: weft_ir::CapOperand::Local(cap),
                args,
                ..
            } = &blk.term.kind
            else {
                continue;
            };
            let h = crate::analysis::clause::cap_handler(p, b, cap).or_else(|| {
                let (c, k, _) = crate::factgen::alpha::env_capture(p, b, cap)?;
                crate::analysis::clause::capture_handler(p, c, k)
            });
            let Some(h) = h else {
                continue;
            };
            let gives = args.iter().any(|a| {
                static_closures(p, b, a).into_iter().any(|c| {
                    p.closures.get(c.index()).is_some_and(|d| {
                        (0..d.captures.len()).any(|k| cap_capture_handler(p, tys, c, k) == Some(h))
                    })
                })
            });
            if !gives || !seen.insert(h) {
                continue;
            }
            let (Some(sp), Some(d)) = (handle_span(p, h), p.handlers.get(h.index())) else {
                continue;
            };
            let effect = tys
                .effects()
                .get(d.effect.index())
                .map_or_else(String::new, |e| e.name.clone());
            out.push(error_at(
                weft_syntax::diag::Code::W0313,
                sp,
                format!(
                    "a closure that performs `{effect}` escapes its handler: the body gives it to code that can keep it"
                ),
            ));
        }
    }
    out
}

/// The closures that operand `op` of body `b` holds on the static way: the
/// one value of a local (through copies and moves), also in an aggregate.
fn static_closures(
    p: &weft_ir::Program,
    b: weft_ir::BodyId,
    op: &weft_ir::Operand,
) -> Vec<weft_ir::ClosureId> {
    let mut out = Vec::new();
    let mut work = vec![op.clone()];
    let mut steps = 0usize;
    while let Some(op) = work.pop() {
        steps += 1;
        if steps > 64 {
            break;
        }
        let (weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q)) = &op else {
            continue;
        };
        if !q.proj.is_empty() {
            continue;
        }
        match one_def(p, b, q.local) {
            Some(weft_ir::Rvalue::Use(x)) => work.push(x.clone()),
            Some(weft_ir::Rvalue::Aggregate(weft_ir::AggKind::Closure(c), _)) => out.push(*c),
            Some(weft_ir::Rvalue::Aggregate(_, ops)) => work.extend(ops.iter().cloned()),
            _ => {}
        }
    }
    out
}

/// Rule B of plan stage R0z (Z1): true if operand `op` of body `b` is the
/// result of an operation of a user effect.
///
/// The operand is, on
/// the static way, the result of a perform of an operation of a user
/// effect through the row: a value of code of a caller (a clause of a
/// handler on the stack of this task).
pub fn op_result(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    b: weft_ir::BodyId,
    op: &weft_ir::Operand,
) -> bool {
    let mut op = op.clone();
    let mut b = b;
    for _ in 0..64 {
        let (weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q)) = &op else {
            return false;
        };
        if !q.proj.is_empty() {
            return false;
        }
        // The local of the body that owns the cell (an upvar names the
        // local of a parent).
        let Ok((ob, l)) = crate::factgen::alpha::owner_local(p, b, q.local) else {
            return false;
        };
        b = ob;
        // Each write of the local, in each body.
        let mut stmts: Vec<&weft_ir::Rvalue> = Vec::new();
        let mut dests: Vec<(&weft_ir::CapOperand, &weft_ir::Place)> = Vec::new();
        let mut other = false;
        for (i, y) in p.bodies.iter().enumerate() {
            let yb = weft_ir::BodyId(u32::try_from(i).unwrap_or(u32::MAX));
            let owns = |x: weft_ir::LocalId| {
                crate::factgen::alpha::owner_local(p, yb, x).ok() == Some((ob, l))
            };
            for blk in &y.blocks {
                for st in &blk.stmts {
                    if let weft_ir::StmtKind::Assign(x, rv) = &st.kind {
                        if owns(x.local) {
                            if yb == ob && x.proj.is_empty() {
                                stmts.push(rv);
                            } else {
                                other = true;
                            }
                        }
                    }
                }
                match &blk.term.kind {
                    weft_ir::TermKind::Perform { cap, dest, .. } if owns(dest.local) => {
                        if yb == ob && dest.proj.is_empty() {
                            dests.push((cap, dest));
                        } else {
                            other = true;
                        }
                    }
                    weft_ir::TermKind::Call { dest, .. }
                    | weft_ir::TermKind::Resume { dest, .. }
                        if owns(dest.local) =>
                    {
                        other = true;
                    }
                    _ => {}
                }
            }
        }
        if other {
            return false;
        }
        match (stmts.as_slice(), dests.as_slice()) {
            ([], [(weft_ir::CapOperand::Row(e), _)]) => {
                return tys
                    .effects()
                    .get(e.index())
                    .is_some_and(|d| !crate::effects::is_std(&d.identity));
            }
            ([weft_ir::Rvalue::Use(x)], []) => op = x.clone(),
            _ => return false,
        }
    }
    false
}

/// Rule F of plan stage R0z (Z1): W0501 for a second `resume` of a `once`
/// continuation.
///
/// The two resumes are on a path of a body that is not the clause body itself (a
/// scope body or a handled body inside the clause, or a closure that
/// captures the continuation). The facts of the clause give W0501 for a
/// `resume` in the clause body. The span is the second `resume`, and the
/// texts are those of the old pipeline.
pub fn twice_resumed(p: &weft_ir::Program) -> Vec<Diagnostic> {
    use weft_ir::TermKind;
    let mut out = Vec::new();
    for (i, body) in p.bodies.iter().enumerate() {
        let b = weft_ir::BodyId(u32::try_from(i).unwrap_or(u32::MAX));
        // The `once` continuation of each resume of the body.
        let konts: Vec<(usize, weft_ir::BodyId)> = body
            .blocks
            .iter()
            .enumerate()
            .filter_map(|(j, blk)| match &blk.term.kind {
                TermKind::Resume { kont, .. } => match kont_of(p, b, kont) {
                    Some((cb, false)) if cb != b => Some((j, cb)),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        for &(j, cb) in &konts {
            // The blocks after the resume of block `j`, on the normal edges.
            let mut seen = std::collections::BTreeSet::new();
            let mut work: Vec<weft_ir::BlockId> = Vec::new();
            if let Some(blk) = body.blocks.get(j) {
                if let TermKind::Resume { next, .. } = &blk.term.kind {
                    work.push(*next);
                }
            }
            while let Some(x) = work.pop() {
                if !seen.insert(x) {
                    continue;
                }
                let Some(blk) = body.blocks.get(x.index()) else {
                    continue;
                };
                if blk.cleanup {
                    continue;
                }
                if konts.contains(&(x.index(), cb)) {
                    let mut d = error_at(
                        weft_syntax::diag::Code::W0501,
                        blk.term.origin.span,
                        "a `once` continuation is resumed twice",
                    );
                    d = d.note("an operation that is not `multi` resumes at most once");
                    out.push(d);
                    continue;
                }
                work.extend(blk.term.kind.normal_successors());
            }
        }
    }
    out.sort_by_key(|d| (d.unit, d.span.lo));
    out.dedup();
    out
}

/// The clause body and the mode (`multi`) of the continuation `kont` of
/// body `b`: a continuation local of a clause, an upvar local of one, or a
/// `Kont` capture of a closure (through the makers).
fn kont_of(
    p: &weft_ir::Program,
    b: weft_ir::BodyId,
    kont: &weft_ir::Place,
) -> Option<(weft_ir::BodyId, bool)> {
    let (mut b, mut kont) = (b, kont.clone());
    for _ in 0..=p.closures.len() {
        if let Some((_, cb, multi)) = crate::analysis::clause::kont_handler(p, b, &kont) {
            return Some((cb, multi));
        }
        let (c, k, mode) = crate::factgen::alpha::env_capture(p, b, &kont)?;
        if mode != weft_ir::CaptureMode::Kont {
            return None;
        }
        let d = p.closures.get(c.index())?;
        kont = d.captures.get(k as usize)?.source.clone();
        b = d.maker;
    }
    None
}

/// Rule D of plan stage R0z (Z1), the structural form of "not through a
/// local outside it".
///
/// It runs on the bodies `bodies` (the components of the bodies
/// whose analysis stops with a `Later`, and of the bodies that reach them):
/// W0313 at the `handle` of a local handler H if a body inside the handled
/// body of H (with no closure body between them) writes a local L of a body
/// outside it, and L gets no other write inside the handled body. The value
/// that it writes, on the static way of the body, is one of these:
///
/// - a closure with a `Cap` capture of H;
/// - the result of a call of a function whose result, on the static way of
///   its body, is a closure that performs an operation of the effect of H
///   through the row, and H serves the effect at the call;
/// - the parameter of the clause of an operation of another handler, when a
///   perform in a body of `bodies` gives the operation a closure with a
///   `Cap` capture of H.
///
/// At the end of the handled body, L holds a closure that performs through
/// H. The text is that of the old pipeline.
pub fn local_escapes(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    bodies: &[weft_ir::BodyId],
) -> Vec<Diagnostic> {
    use weft_ir::{Callee, Rvalue, StmtKind, TermKind};
    let mut found: Vec<(weft_ir::HandlerId, weft_ir::BodyId, weft_ir::LocalId)> = Vec::new();
    let caps_of = |c: weft_ir::ClosureId| -> Vec<weft_ir::HandlerId> {
        let n = p.closures.get(c.index()).map_or(0, |d| d.captures.len());
        (0..n)
            .filter_map(|k| cap_capture_handler(p, tys, c, k))
            .collect()
    };
    for &b in bodies {
        let Some(body) = p.body(b) else {
            continue;
        };
        // The locals of the body that hold the result of a call, with the
        // handlers whose effect the closure of the result performs.
        let mut call_hs: Vec<(weft_ir::LocalId, weft_ir::HandlerId)> = Vec::new();
        for blk in &body.blocks {
            if let TermKind::Call {
                callee: Callee::Fn(f, _),
                dest,
                ..
            } = &blk.term.kind
            {
                if dest.proj.is_empty() {
                    for h in result_handlers(p, tys, body.cap_env, *f) {
                        call_hs.push((dest.local, h));
                    }
                }
            }
        }
        for blk in &body.blocks {
            for st in &blk.stmts {
                let StmtKind::Assign(q, rv) = &st.kind else {
                    continue;
                };
                let ops: Vec<&weft_ir::Operand> = match rv {
                    Rvalue::Use(x) => vec![x],
                    Rvalue::Aggregate(weft_ir::AggKind::Closure(_), _) => Vec::new(),
                    Rvalue::Aggregate(_, ops) => ops.iter().collect(),
                    _ => Vec::new(),
                };
                let mut hs: Vec<weft_ir::HandlerId> = Vec::new();
                if let Rvalue::Aggregate(weft_ir::AggKind::Closure(c), _) = rv {
                    hs.extend(caps_of(*c));
                }
                for op in ops {
                    for c in static_closures(p, b, op) {
                        hs.extend(caps_of(c));
                    }
                    for l in static_locals(p, b, op) {
                        hs.extend(call_hs.iter().filter(|(x, _)| *x == l).map(|(_, h)| *h));
                    }
                }
                for h in hs {
                    found.extend(keeps(p, b, q.local, h));
                }
            }
            // A perform that gives a closure with a capability of H to the
            // clause of another handler, which writes its parameter into a
            // local outside H.
            let TermKind::Perform {
                cap: weft_ir::CapOperand::Local(cap),
                op,
                args,
                ..
            } = &blk.term.kind
            else {
                continue;
            };
            let r = crate::analysis::clause::cap_handler(p, b, cap).or_else(|| {
                let (c, k, _) = crate::factgen::alpha::env_capture(p, b, cap)?;
                crate::analysis::clause::capture_handler(p, c, k)
            });
            let Some(cb) = r
                .and_then(|r| crate::analysis::clause::serving(p, r, *op))
                .and_then(|r| crate::analysis::clause::clause_of(p, r, *op))
            else {
                continue;
            };
            for (i, a) in args.iter().enumerate() {
                let hs: Vec<weft_ir::HandlerId> = static_closures(p, b, a)
                    .into_iter()
                    .flat_map(caps_of)
                    .collect();
                if hs.is_empty() {
                    continue;
                }
                for l in param_writes(p, cb, i) {
                    for &h in &hs {
                        found.extend(keeps(p, cb, l, h));
                    }
                }
            }
        }
    }
    found.sort();
    found.dedup();
    let mut out = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for (h, ob, ol) in found {
        if !seen.insert(h) {
            continue;
        }
        let (Some(sp), Some(d)) = (handle_span(p, h), p.handlers.get(h.index())) else {
            continue;
        };
        let effect = tys
            .effects()
            .get(d.effect.index())
            .map_or_else(String::new, |e| e.name.clone());
        let name = p
            .body(ob)
            .and_then(|x| x.local(ol))
            .and_then(|x| x.name.clone())
            .unwrap_or_default();
        out.push(error_at(
            weft_syntax::diag::Code::W0313,
            sp,
            format!("a closure that performs `{effect}` escapes its handler: the local `{name}` keeps it"),
        ));
    }
    out
}

/// The local of a body outside the handled body of handler `h` that a write
/// of local `l` of body `b` writes, if `b` is inside that handled body with
/// no closure body between them, and the local gets no other write inside
/// the handled body ([`local_escapes`]).
fn keeps(
    p: &weft_ir::Program,
    b: weft_ir::BodyId,
    l: weft_ir::LocalId,
    h: weft_ir::HandlerId,
) -> Option<(weft_ir::HandlerId, weft_ir::BodyId, weft_ir::LocalId)> {
    let hd = p.handlers.get(h.index())?.handled;
    if !inside_no_closure(p, b, hd) {
        return None;
    }
    let (ob, ol) = crate::factgen::alpha::owner_local(p, b, l).ok()?;
    if inside(p, ob, hd) {
        return None;
    }
    // The writes of the local inside the handled body.
    let mut writes = 0usize;
    for (i, y) in p.bodies.iter().enumerate() {
        let yb = weft_ir::BodyId(u32::try_from(i).unwrap_or(u32::MAX));
        if !inside(p, yb, hd) {
            continue;
        }
        for blk in &y.blocks {
            for st in &blk.stmts {
                if let weft_ir::StmtKind::Assign(q, _) = &st.kind {
                    if crate::factgen::alpha::owner_local(p, yb, q.local).ok() == Some((ob, ol)) {
                        writes += 1;
                    }
                }
            }
            let dest = match &blk.term.kind {
                weft_ir::TermKind::Call { dest, .. }
                | weft_ir::TermKind::Perform { dest, .. }
                | weft_ir::TermKind::Resume { dest, .. } => Some(dest),
                _ => None,
            };
            if let Some(q) = dest {
                if crate::factgen::alpha::owner_local(p, yb, q.local).ok() == Some((ob, ol)) {
                    writes += 1;
                }
            }
        }
    }
    (writes == 1).then_some((h, ob, ol))
}

/// True if body `b` is body `a` or a body inside it (its lexical parents).
fn inside(p: &weft_ir::Program, b: weft_ir::BodyId, a: weft_ir::BodyId) -> bool {
    let mut at = Some(b);
    for _ in 0..=p.bodies.len() {
        let Some(x) = at else {
            return false;
        };
        if x == a {
            return true;
        }
        at = p.body(x).and_then(|y| y.parent);
    }
    false
}

/// True if body `b` is body `a` or a body inside it, with no closure body
/// on the way from `b` up to `a`.
fn inside_no_closure(p: &weft_ir::Program, b: weft_ir::BodyId, a: weft_ir::BodyId) -> bool {
    let mut at = Some(b);
    for _ in 0..=p.bodies.len() {
        let Some(x) = at else {
            return false;
        };
        if x == a {
            return true;
        }
        let Some(y) = p.body(x) else {
            return false;
        };
        if matches!(y.kind, weft_ir::BodyKind::Closure(_)) {
            return false;
        }
        at = y.parent;
    }
    false
}

/// The locals that operand `op` of body `b` copies on the static way
/// (through copies and moves, also in an aggregate), with the local of the
/// operand.
fn static_locals(
    p: &weft_ir::Program,
    b: weft_ir::BodyId,
    op: &weft_ir::Operand,
) -> Vec<weft_ir::LocalId> {
    let mut out = Vec::new();
    let mut work = vec![op.clone()];
    while let Some(op) = work.pop() {
        if out.len() > 64 {
            break;
        }
        let (weft_ir::Operand::Copy(q) | weft_ir::Operand::Move(q)) = &op else {
            continue;
        };
        if !q.proj.is_empty() || out.contains(&q.local) {
            continue;
        }
        out.push(q.local);
        match one_def(p, b, q.local) {
            Some(weft_ir::Rvalue::Use(x)) => work.push(x.clone()),
            Some(weft_ir::Rvalue::Aggregate(_, ops)) => work.extend(ops.iter().cloned()),
            _ => {}
        }
    }
    out
}

/// The handlers that serve, at a call in capability environment `env`, an
/// effect that the closure of the result of function `f` performs through
/// the row: the result of the body of `f` on the static way is a closure,
/// and its body performs an operation of the effect through the row.
fn result_handlers(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    env: weft_ir::CapEnvId,
    f: weft_ir::FnId,
) -> Vec<weft_ir::HandlerId> {
    let Some(fb) = p
        .bodies
        .iter()
        .position(|b| b.kind == weft_ir::BodyKind::Fn(f))
        .and_then(|i| u32::try_from(i).ok())
        .map(weft_ir::BodyId)
    else {
        return Vec::new();
    };
    let ret = weft_ir::Operand::Copy(weft_ir::Place::local(weft_ir::LocalId(0)));
    let mut out = Vec::new();
    for c in static_closures(p, fb, &ret) {
        let Some(cb) = p.closures.get(c.index()).map(|d| d.body) else {
            continue;
        };
        let Some(body) = p.body(cb) else {
            continue;
        };
        for blk in &body.blocks {
            if let weft_ir::TermKind::Perform {
                cap: weft_ir::CapOperand::Row(e),
                ..
            } = &blk.term.kind
            {
                let Some(id) = tys.effects().get(e.index()).map(|d| d.identity.clone()) else {
                    continue;
                };
                if id == super::frames::FAIL {
                    continue;
                }
                if let super::frames::Dest::Handler { handler, .. } =
                    super::frames::resolve(p, tys, env, &id, true)
                {
                    out.push(handler);
                }
            }
        }
    }
    out
}

/// The locals that the clause body `cb` writes with the value of its
/// parameter `i` on the static way (through copies and moves of whole
/// locals of the clause), with the local of the parameter.
fn param_writes(p: &weft_ir::Program, cb: weft_ir::BodyId, i: usize) -> Vec<weft_ir::LocalId> {
    let Some(body) = p.body(cb) else {
        return Vec::new();
    };
    let Some(param) = body
        .locals
        .iter()
        .position(|d| d.kind == weft_ir::LocalKind::Param(u32::try_from(i).unwrap_or(u32::MAX)))
        .and_then(|j| u32::try_from(j).ok())
        .map(weft_ir::LocalId)
    else {
        return Vec::new();
    };
    let mut held = vec![param];
    let mut out = Vec::new();
    for _ in 0..4 {
        for blk in &body.blocks {
            for st in &blk.stmts {
                let weft_ir::StmtKind::Assign(
                    q,
                    weft_ir::Rvalue::Use(weft_ir::Operand::Copy(x) | weft_ir::Operand::Move(x)),
                ) = &st.kind
                else {
                    continue;
                };
                if !x.proj.is_empty() || !held.contains(&x.local) {
                    continue;
                }
                let own = crate::factgen::alpha::owner_local(p, cb, q.local)
                    .is_ok_and(|(ob, _)| ob == cb);
                if own && q.proj.is_empty() {
                    if !held.contains(&q.local) {
                        held.push(q.local);
                    }
                } else if !out.contains(&q.local) {
                    out.push(q.local);
                }
            }
        }
    }
    out
}
