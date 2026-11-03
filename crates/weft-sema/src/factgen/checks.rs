//! Checks in Rust over the summaries (`docs/ir.md` 6.9).
//!
//! W0118 is a query over the summary of each `on abort` function
//! ([`on_abort_rows`]): its changes are below its parameter value (F3-1),
//! its row holds only effects that the root handlers serve, its `raises`
//! part is empty, and its `drops` and `holds` parts hold no type parameter
//! of its parameter type (F3-3, F3-4). The texts are those of the old
//! pipeline (`crate::program::on_abort_row`).
//!
//! [`item_value`] is the check of a function item as a value with type
//! arguments (`docs/ir.md` 5.35, `check_item_value` of the old lowering).
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

/// The check of the function item `f` as a value with the type arguments
/// `targs` (`docs/ir.md` 5.35).
///
/// A caller can run the value, so a type argument that the summary of `f`
/// drops or holds must not be linear (W0601, W0602 at the value in the old
/// lowering).
///
/// Returns a reason if the check finds such a type argument: the facts have
/// no node for it yet, so the program stays with the old pipeline (its
/// lowering gives the diagnostic). `None` if the value passes.
pub fn item_value(
    sums: &Summaries,
    tys: &weft_ir::TyTable,
    f: weft_ir::FnId,
    targs: &[weft_ir::TyId],
) -> Option<&'static str> {
    let sum = sums.get(f).ok()?;
    let linear = |j: &u32| {
        targs
            .get(*j as usize)
            .is_some_and(|&t| crate::props::ir_maybe_linear(tys, t))
    };
    (sum.drops.iter().any(linear) || sum.holds.iter().any(linear)).then_some(
        "a function item as a value that drops or holds a linear type argument (stage F20)",
    )
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
        let effect = tys
            .effects()
            .get(d.effect.index())
            .map_or_else(String::new, |e| e.name.clone());
        // The `handle` terminator of the site.
        let origin = p.body(d.site).and_then(|b| {
            b.blocks
                .iter()
                .find(|x| {
                    matches!(x.term.kind, weft_ir::TermKind::Handle { handler, .. } if handler == *h)
                })
                .map(|x| x.term.origin.span)
        });
        let Some(sp) = origin.or_else(|| p.body(d.handled).map(|b| b.origin.span)) else {
            continue;
        };
        let head = format!("a closure that performs `{effect}` escapes its handler");
        let msg = match how {
            Escape::Value => head,
            Escape::Local(name) => format!("{head}: the local `{name}` keeps it"),
            Escape::Stored => format!("{head}: the body stores it"),
            Escape::Given => format!("{head}: the body gives it to code that can keep it"),
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
