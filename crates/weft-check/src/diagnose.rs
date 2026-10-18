//! Diagnostics from checker results. Each diagnostic shows its derivation.

use std::collections::BTreeMap;

use weft_facts::{FnFacts, NodeId, VarId, VarKind};
use weft_sema::effects;
use weft_syntax::diag::Diagnostic;

use crate::rules::Report;

/// The most other sites that a W0602 note lists by line.
const LISTED_SITES: usize = 5;

fn node_span(f: &FnFacts, n: NodeId) -> weft_facts::Span {
    f.node(n).span
}

fn once_closure(f: &FnFacts, n: NodeId) -> Diagnostic {
    Diagnostic::error("W0502", "a `once` closure is called twice", node_span(f, n))
        .note("the closure moves a captured value, so it can run only once")
}

/// Turns a checker report into diagnostics, in source order.
pub fn diagnose(f: &FnFacts, r: &Report) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let v = &r.violations;

    // W0301: the derivation of the design doc.
    for inv in &r.invalidations {
        let var = f.var(inv.var);
        let path = &f.place(inv.path).display;
        let mutated = &f.place(inv.mutated).display;
        let at = f.node(inv.at);
        let mut_text = if at.detail.is_empty() {
            format!("mut({mutated})")
        } else {
            at.detail.clone()
        };
        let name = if var.kind == VarKind::Iterator {
            "the loop iterator".to_string()
        } else {
            format!("`{}`", var.name)
        };
        let d = Diagnostic::error("W0301", format!("{name} used after it was invalidated"), node_span(f, inv.used_at))
            .note_at(format!("{} : &{} in {path}", var.name, var.ty.trim_start_matches('&')), var.span)
            .note_at(format!("{} : {mut_text}", at.label), at.span)
            .note(format!(
                "{mutated} is a strict prefix of {path}, through an unstable step  →  invalidated at line {{line:{}}}",
                at.span.lo
            ))
            .note(format!("used at line {{line:{}}}", node_span(f, inv.used_at).lo));
        out.push(d);
    }

    for &(var, n) in &v.use_after_move {
        let info = f.var(var);
        let d = match info.kind {
            VarKind::Continuation => Diagnostic::error(
                "W0501",
                "a `once` continuation is resumed twice",
                node_span(f, n),
            )
            .note("an operation that is not `multi` resumes at most once"),
            _ if info.callable => once_closure(f, n),
            _ => Diagnostic::error(
                "W0302",
                format!("`{}` used after it was moved", info.name),
                node_span(f, n),
            )
            .note_at(format!("{} : {}", info.name, info.ty), info.span),
        };
        out.push(d);
    }
    for &(var, n) in &v.moved_immovable {
        let info = f.var(var);
        out.push(
            Diagnostic::error(
                "W0604",
                format!("`{}` has a `!Move` type and cannot move", info.name),
                node_span(f, n),
            )
            .note("construct it in place and use it through references"),
        );
    }
    for &(var, n) in &v.unconsumed {
        let info = f.var(var);
        let d = if info.kind == VarKind::Task {
            Diagnostic::error(
                "W0601",
                format!("task handle `{}` is not joined or detached", info.name),
                node_span(f, n),
            )
        } else {
            Diagnostic::error(
                "W0601",
                format!(
                    "linear value `{}` is dropped without being consumed",
                    info.name
                ),
                node_span(f, n),
            )
            .note_at(format!("{} : {} (linear)", info.name, info.ty), info.span)
            .note("move it into a call that consumes it on every normal path")
        };
        out.push(d);
    }
    for &(var, n) in &v.overwritten {
        let info = f.var(var);
        out.push(Diagnostic::error(
            "W0601",
            format!(
                "linear value `{}` is overwritten before it is consumed",
                info.name
            ),
            node_span(f, n),
        ));
    }
    // W0602: one error for each value, at the first site that can abort.
    let mut aborts: BTreeMap<VarId, Vec<NodeId>> = BTreeMap::new();
    for &(var, n) in &v.abort_unhandled {
        aborts.entry(var).or_default().push(n);
    }
    for (var, mut sites) in aborts {
        sites.sort_by_key(|&n| node_span(f, n).lo);
        let Some((&first, rest)) = sites.split_first() else {
            continue;
        };
        let info = f.var(var);
        let at = f.node(first);
        let mut d = Diagnostic::error(
            "W0602",
            format!(
                "linear value `{}` is live across `{}`, which can abort",
                info.name, at.label
            ),
            at.span,
        )
        .note_at(
            format!("{} : {} (linear, no `on abort`)", info.name, info.ty),
            info.span,
        )
        .note("declare `on abort = f` on the type, or consume the value before this call");
        if !rest.is_empty() {
            let lines: Vec<String> = rest
                .iter()
                .take(LISTED_SITES)
                .map(|&n| format!("{{line:{}}}", node_span(f, n).lo))
                .collect();
            let more = if rest.len() > LISTED_SITES {
                ", ..."
            } else {
                ""
            };
            d = d.note(format!(
                "and {} more sites that can abort, at lines {}{more}",
                rest.len(),
                lines.join(", ")
            ));
        }
        out.push(d);
    }
    for &(var, n) in &v.live_across_multi {
        let info = f.var(var);
        let at = f.node(n);
        out.push(
            Diagnostic::error(
                "W0503",
                format!("`{}` is not `many`, but it is live across `{}`, which can resume more than once", info.name, at.label),
                at.span,
            )
            .note_at(format!("{} : {}", info.name, info.ty), info.span),
        );
    }
    for &(n, p) in &v.unauthorized_mut {
        let at = f.node(n);
        out.push(
            Diagnostic::error(
                "W0703",
                format!(
                    "`{}` mutates `{}`, which the signature does not allow",
                    at.label,
                    f.place(p).display
                ),
                at.span,
            )
            .note(format!(
                "add `mut({})` to the effects after `/`",
                f.place(p).display
            )),
        );
    }
    for (n, e) in &v.unauthorized_effect {
        let at = f.node(*n);
        out.push(
            Diagnostic::error(
                "W0702",
                format!(
                    "`{}` performs `{e}`, which the signature does not allow",
                    at.label
                ),
                at.span,
            )
            .note(format!(
                "add `{}` to the effects after `/`, or handle it here",
                effects::written_name(e)
            )),
        );
    }
    for &(n, p) in &v.shared_mutation {
        let at = f.node(n);
        out.push(Diagnostic::error(
            "W0402",
            format!(
                "`{}` mutates `{}` through a `@ shared` reference",
                at.label,
                f.place(p).display
            ),
            at.span,
        ));
    }
    for &(n, m, a) in &v.alias_conflict {
        let at = f.node(n);
        out.push(
            Diagnostic::error(
                "W0312",
                format!(
                    "`{}` mutates `{}` while another argument points into `{}`",
                    at.label,
                    f.place(m).display,
                    f.place(a).display
                ),
                at.span,
            )
            .note("the callee sees them as separate places, so it cannot protect the references"),
        );
    }
    for c in &r.conflicts {
        let at = f.node(c.at);
        let task = &f.tasks[c.task.index()];
        let (verb, other) = if c.task_writes {
            ("mutates", "accesses")
        } else {
            ("reads", "mutates")
        };
        out.push(
            Diagnostic::error(
                "W0405",
                format!(
                    "this code {other} `{}` while a task {verb} `{}`",
                    f.place(c.node_place).display,
                    f.place(c.task_place).display
                ),
                at.span,
            )
            .note_at(
                format!("task : {verb} {}", f.place(c.task_place).display),
                task.span,
            )
            .note("tasks that can run at the same time need separate footprints"),
        );
    }
    for &(t, var) in &v.nonportable_capture {
        let info = f.var(var);
        out.push(Diagnostic::error(
            "W0401",
            format!(
                "a `fork` branch captures `{}`, which is nonportable",
                info.name
            ),
            f.tasks[t.index()].span,
        ));
    }
    for &(t, var) in &v.shared_mut_capture {
        let info = f.var(var);
        out.push(
            Diagnostic::error(
                "W0403",
                format!(
                    "a `fork` branch mutates through `{}`, a shared-mutable reference",
                    info.name
                ),
                f.tasks[t.index()].span,
            )
            .note("a shared-mutable reference is nonportable; split it into `@ uniq` parts first"),
        );
    }
    for &h in &v.root_handler_in_lib {
        let info = &f.handlers[h.index()];
        out.push(Diagnostic::error(
            "W0801",
            format!(
                "a library installs a root handler for `{}`; only binaries and tests can",
                info.effect
            ),
            info.span,
        ));
    }
    out.sort_by(|a, b| (a.span.lo, &a.code).cmp(&(b.span.lo, &b.code)));
    out
}

/// Replaces `{line:N}` markers (byte offsets) with line numbers.
pub fn resolve_lines(d: &mut Diagnostic, file: &weft_syntax::SourceFile) {
    for n in &mut d.notes {
        while let Some(start) = n.text.find("{line:") {
            let Some(end) = n.text[start..].find('}') else {
                break;
            };
            let num: u32 = n.text[start + 6..start + end].parse().unwrap_or(0);
            let line = file.line_col(num).0;
            n.text
                .replace_range(start..=(start + end), &line.to_string());
        }
    }
}
