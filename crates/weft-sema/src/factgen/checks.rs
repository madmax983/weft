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
/// (`crate::analysis::sig::to_effect_sig`). A function with no summary
/// keeps the row of the old inference. `no_runtime`: no root handler serves
/// an effect.
pub fn on_abort_rows(
    a: &Analysis,
    built: &Built,
    sums: &Summaries,
    no_runtime: bool,
) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for f in on_abort_fns(&a.program) {
        let Some(sig) = a.sigs.get(f.index()) else {
            continue;
        };
        let row = built
            .fns
            .get(&f)
            .and_then(|g| sums.get(*g).ok())
            .map_or_else(
                || sig.effects.clone(),
                |s| {
                    // A call of a function value that the function does not
                    // know is an item check of the old inference (`reaches`,
                    // class D-W0118 of stage F17): the summary keeps it.
                    let mut row = to_effect_sig(&a.program, s);
                    row.reaches |= sig.effects.reaches;
                    row
                },
            );
        out.extend(on_abort_row(&a.program, f, sig, &row, no_runtime));
    }
    out
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
