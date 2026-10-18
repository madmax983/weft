//! Diagnostics from checker results. Each diagnostic shows its derivation.

use weft_facts::{FnFacts, NodeId, VarKind};
use weft_syntax::diag::Diagnostic;

use crate::rules::{Cause, Conflict, Report};

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
        let at = f.node(inv.at);
        let line = at.span.lo;
        let name = match var.kind {
            VarKind::Iterator => "the loop iterator".to_string(),
            VarKind::Temp | VarKind::BlockValue => format!("the {}", var.name),
            _ => format!("`{}`", var.name),
        };
        // What the node does, and why that invalidates the reference.
        // The place behind an `Rc` handle `a` shows as `a.*`.
        let handle = path.strip_suffix(".*");
        let inside = |owner: &str, verb: &str| {
            let head = if path == owner {
                format!("{owner} {verb}")
            } else if handle == Some(owner) {
                format!("{owner} is an `Rc` handle on the way to the place, and it {verb}")
            } else {
                format!("{path} is inside {owner}, which {verb}")
            };
            format!("{head} at line {{line:{line}}}  →  invalidated at line {{line:{line}}}")
        };
        let (what, why) = match inv.cause {
            Cause::Mutation(m) | Cause::Lend(m) => {
                let mutated = &f.place(m).display;
                let what = match (at.detail.is_empty(), at.label.strip_suffix(" =")) {
                    _ if matches!(inv.cause, Cause::Lend(_)) => format!(
                        "{} : gets {mutated}, and it can mutate through it",
                        at.label
                    ),
                    (true, Some(target)) => format!("{target} : new value"),
                    (true, None) => format!("{} : mut({mutated})", at.label),
                    (false, _) => format!("{} : {}", at.label, at.detail),
                };
                let why = match (f.wild_base(inv.path), f.wild_base(m)) {
                    (Some(b), _) => format!(
                        "{path} can be any place inside {}, and {mutated} overlaps it  →  invalidated at line {{line:{line}}}",
                        f.place(b).display
                    ),
                    (None, Some(b)) => format!(
                        "{mutated} can be any place inside {}, which holds {path}  →  invalidated at line {{line:{line}}}",
                        f.place(b).display
                    ),
                    (None, None) if handle == Some(mutated.as_str()) => format!(
                        "{mutated} is an `Rc` handle on the way to the place, and a new value of it can free the object  →  invalidated at line {{line:{line}}}"
                    ),
                    (None, None) => format!(
                        "{mutated} is a strict prefix of {path}, through an unstable step  →  invalidated at line {{line:{line}}}"
                    ),
                };
                (what, why)
            }
            Cause::Move(o) => {
                let owner = &f.var(o).name;
                (format!("{owner} : moved"), inside(owner, "is moved"))
            }
            Cause::ScopeEnd(o) if f.var(o).kind == VarKind::Temp => (
                "temporary : goes out of scope at the end of the statement".to_string(),
                format!("{path} is inside a temporary value, which goes out of scope at line {{line:{line}}}  →  invalidated at line {{line:{line}}}"),
            ),
            Cause::ScopeEnd(o) => {
                let owner = &f.var(o).name;
                // A local of a closure or a handler clause goes out of scope
                // when the body returns at a call or an operation.
                let when = match at.label.as_str() {
                    "end of block" | "end of statement" | "exit" | "return" | "jump"
                    | "drop" => "goes out of scope".to_string(),
                    callee => format!("goes out of scope when `{callee}` returns"),
                };
                (format!("{owner} : {when}"), inside(owner, &when))
            }
            Cause::MovePart(m) => {
                let moved = &f.place(m).display;
                (format!("{moved} : moved"), inside(moved, "is moved"))
            }
        };
        let holder = if var.kind == VarKind::Closure || var.ty.starts_with("fn(") {
            format!("{} : {}, captures {path}", var.name, var.ty)
        } else if let Some(h) = handle {
            format!(
                "{} : &{} through the `Rc` handle {h}",
                var.name,
                var.ty.trim_start_matches('&')
            )
        } else {
            format!(
                "{} : &{} in {path}",
                var.name,
                var.ty.trim_start_matches('&')
            )
        };
        let used = node_span(f, inv.used_at);
        // A block value is held only across the end of its block.
        let block_value = var.kind == VarKind::BlockValue;
        let d = if let (true, Cause::ScopeEnd(o)) = (block_value, inv.cause) {
            let head = match (var.ty.starts_with("fn("), handle) {
                (true, _) => format!("the closure that this block returns captures `{path}`"),
                (false, Some(h)) => {
                    format!("the value of this block points into the object behind `{h}`")
                }
                (false, None) => format!("the value of this block points into `{path}`"),
            };
            Diagnostic::error(
                "W0301",
                format!(
                    "{head}, but `{}` goes out of scope at the end of the block",
                    f.var(o).name
                ),
                used,
            )
            .note_at(holder, var.span)
            .note_at(what, at.span)
        } else {
            Diagnostic::error(
                "W0301",
                format!("{name} used after it was invalidated"),
                used,
            )
            .note_at(holder, var.span)
            .note_at(what, at.span)
            .note(why)
            .note(format!("used at line {{line:{}}}", used.lo))
        };
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
            VarKind::Closure => once_closure(f, n),
            _ if info.ty.starts_with("fn(") => once_closure(f, n),
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
    for &(var, n) in &v.abort_unhandled {
        let info = f.var(var);
        let at = f.node(n);
        out.push(
            Diagnostic::error(
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
            .note("declare `on abort = f` on the type, or consume the value before this call"),
        );
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
                e.to_lowercase()
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
    // Several nodes of one expression can conflict with the same task: show the
    // conflict with the most specific places once.
    let mut conflicts: Vec<&Conflict> = r.conflicts.iter().collect();
    let depth = |c: &Conflict| {
        (
            f.place(c.node_place).steps.len(),
            f.place(c.task_place).steps.len(),
        )
    };
    conflicts.sort_by_key(|c| {
        let s = f.node(c.at).span;
        (c.task, s.lo, s.hi, std::cmp::Reverse(depth(c)))
    });
    conflicts.dedup_by_key(|c| {
        let s = f.node(c.at).span;
        (c.task, s.lo, s.hi)
    });
    for c in conflicts {
        let at = f.node(c.at);
        let task = &f.tasks[c.task.index()];
        let verb = if c.task_writes { "mutates" } else { "reads" };
        let other = match (c.task_writes, c.free, c.lends) {
            (_, _, true) => "gives a function value that can mutate",
            (true, None, false) => "accesses",
            (false, None, false) => "mutates",
            (_, Some(_), false) => "frees",
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
    out.sort_by_key(|d| (d.span.lo, d.code.clone()));
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
