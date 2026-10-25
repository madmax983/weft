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
            .map_or_else(|| sig.effects.clone(), |s| to_effect_sig(&a.program, s));
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
