//! Diagnostics from checker results. Each diagnostic shows its derivation.

use std::collections::BTreeMap;

use weft_facts::{FnFacts, NodeId, PlaceId, VarId, VarKind};
use weft_sema::effects;
use weft_syntax::diag::Diagnostic;

use crate::rules::{Cause, Conflict, Invalidation, Report};

/// The most lines that a note about other sites lists.
const LISTED_SITES: usize = 5;

fn node_span(f: &FnFacts, n: NodeId) -> weft_facts::Span {
    f.node(n).span
}

/// Returns the place to state for a mutation of `p`. What the references behind a
/// parameter `x` point into (`*x` in the facts) is part of `x..`.
fn mut_hint(f: &FnFacts, p: PlaceId) -> String {
    let root = &f.roots[f.place(p).root.index()].name;
    match root.strip_prefix('*') {
        Some(param) => format!("{param}.."),
        None => f.place(p).display.clone(),
    }
}

/// Returns the first node that uses `var` in a handler clause that node `n` runs:
/// `n` performs through a local handler, and the use is in a part of the graph
/// that the entry of the function does not reach.
fn clause_read(f: &FnFacts, var: VarId, n: NodeId) -> Option<NodeId> {
    if !f.performs_at.iter().any(|&(p, _)| p == n) || f.nodes.is_empty() {
        return None;
    }
    let mut succ: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for &(a, b) in &f.cfg_edge {
        succ.entry(a).or_default().push(b);
    }
    let mut seen = vec![false; f.nodes.len()];
    let mut work = vec![NodeId(0)];
    while let Some(a) = work.pop() {
        if std::mem::replace(&mut seen[a.index()], true) {
            continue;
        }
        work.extend(succ.get(&a).into_iter().flatten().copied());
    }
    f.uses
        .iter()
        .filter(|&&(v, q)| v == var && !seen[q.index()])
        .map(|&(_, q)| q)
        .min()
}

fn once_closure(f: &FnFacts, n: NodeId) -> Diagnostic {
    Diagnostic::error("W0502", "a `once` closure is called twice", node_span(f, n))
        .note("the closure moves a captured value, so it can run only once")
}

/// Groups `(variable, node)` pairs by variable. The nodes of each variable
/// are in source order.
fn by_var<'a>(
    f: &FnFacts,
    pairs: impl IntoIterator<Item = &'a (VarId, NodeId)>,
) -> BTreeMap<VarId, Vec<NodeId>> {
    let mut map: BTreeMap<VarId, Vec<NodeId>> = BTreeMap::new();
    for &(var, n) in pairs {
        map.entry(var).or_default().push(n);
    }
    for sites in map.values_mut() {
        sites.sort_by_key(|&n| node_span(f, n).lo);
    }
    map
}

/// Adds a note for the other sites of an error that a variable has at more
/// than one node, for example `and 2 more sites that can abort, at lines 8,
/// 9`. `noun` is the singular and the plural of the word after the count.
/// [`resolve_lines`] changes the `{lines:...}` marker into line numbers.
fn note_more(d: Diagnostic, f: &FnFacts, rest: &[NodeId], noun: (&str, &str)) -> Diagnostic {
    if rest.is_empty() {
        return d;
    }
    let offsets: Vec<String> = rest
        .iter()
        .map(|&n| node_span(f, n).lo.to_string())
        .collect();
    let noun = if rest.len() == 1 { noun.0 } else { noun.1 };
    d.note(format!(
        "and {} more {noun}, at {{lines:{}}}",
        rest.len(),
        offsets.join(" ")
    ))
}

/// Turns a checker report into diagnostics, in source order.
///
/// A rule that fails at many nodes for one variable gives one error, at the
/// first node. A note lists the other nodes.
pub fn diagnose(f: &FnFacts, r: &Report) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let v = &r.violations;

    // W0301: the derivation of the design doc. One error for each reference
    // and invalidating node, at the first use. The node can be a mutation, a
    // lend, a move, a part move or a scope end (`Cause`).
    let mut invalidations: BTreeMap<(VarId, NodeId), Vec<&Invalidation>> = BTreeMap::new();
    for inv in &r.invalidations {
        invalidations
            .entry((inv.var, inv.at))
            .or_default()
            .push(inv);
    }
    for mut uses in invalidations.into_values() {
        uses.sort_by_key(|inv| node_span(f, inv.used_at).lo);
        let Some((&inv, rest)) = uses.split_first() else {
            continue;
        };
        let rest: Vec<NodeId> = rest.iter().map(|i| i.used_at).collect();
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
        let holder = if var.callable {
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
            let head = match (var.callable, handle) {
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
        out.push(note_more(d, f, &rest, ("use", "uses")));
    }

    for (var, sites) in by_var(f, &v.use_after_move) {
        let Some((&n, rest)) = sites.split_first() else {
            continue;
        };
        let info = f.var(var);
        let (d, noun) = match info.kind {
            VarKind::Continuation => (
                Diagnostic::error(
                    "W0501",
                    "a `once` continuation is resumed twice",
                    node_span(f, n),
                )
                .note("an operation that is not `multi` resumes at most once"),
                ("resume", "resumes"),
            ),
            _ if info.callable => (once_closure(f, n), ("call", "calls")),
            _ => (
                Diagnostic::error(
                    "W0302",
                    format!("`{}` used after it was moved", info.name),
                    node_span(f, n),
                )
                .note_at(format!("{} : {}", info.name, info.ty), info.span),
                ("use after a move", "uses after a move"),
            ),
        };
        out.push(note_more(d, f, rest, noun));
    }
    for &(var, n) in &v.use_before_set {
        let info = f.var(var);
        // A handler clause uses its captures at each node that runs it. The
        // diagnostic shows the read in the clause, and the node as a note.
        let read = clause_read(f, var, n);
        let mut d = Diagnostic::error(
            "W0304",
            format!("`{}` is used before it has a value", info.name),
            node_span(f, read.unwrap_or(n)),
        )
        .note_at(format!("{} : {}", info.name, info.ty), info.span);
        if read.is_some() {
            d = d.note_at(
                "a handler clause reads it when it runs here",
                node_span(f, n),
            );
        }
        out.push(d.note("give it a value on every path before this use"));
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
        } else if info.callable {
            let who = if matches!(info.kind, VarKind::Closure | VarKind::Temp) {
                "a closure".to_string()
            } else {
                format!("closure `{}`", info.name)
            };
            Diagnostic::error(
                "W0601",
                format!("{who} moves a linear value, but it can go out of scope without a call"),
                node_span(f, n),
            )
            .note("call the closure once on every normal path; a callee that gets it can drop it")
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
    for (var, sites) in by_var(f, &v.abort_unhandled) {
        let Some((&first, rest)) = sites.split_first() else {
            continue;
        };
        let info = f.var(var);
        let at = f.node(first);
        let d = Diagnostic::error(
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
        out.push(note_more(
            d,
            f,
            rest,
            ("site that can abort", "sites that can abort"),
        ));
    }
    // W0503: one error for each value, at the first `multi` operation.
    for (var, sites) in by_var(f, &v.live_across_multi) {
        let Some((&first, rest)) = sites.split_first() else {
            continue;
        };
        let info = f.var(var);
        let at = f.node(first);
        let name = if info.kind == VarKind::Iterator {
            "the loop iterator".to_string()
        } else {
            format!("`{}`", info.name)
        };
        let d = Diagnostic::error(
            "W0503",
            format!(
                "{name} is not `many`, but it is live across `{}`, which can resume more than once",
                at.label
            ),
            at.span,
        )
        .note_at(format!("{} : {}", info.name, info.ty), info.span);
        out.push(note_more(
            d,
            f,
            rest,
            (
                "operation that can resume more than once",
                "operations that can resume more than once",
            ),
        ));
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
                mut_hint(f, p)
            )),
        );
    }
    for (n, e) in &v.unauthorized_effect {
        let at = f.node(*n);
        out.push(
            Diagnostic::error(
                "W0702",
                format!(
                    "`{}` performs {}, which the signature does not allow",
                    at.label,
                    effect_text(e, &f.declared_effect)
                ),
                at.span,
            )
            .note(format!(
                "add `{}` to the effects after `/`, or handle it here",
                effects::in_signature(e)
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
    // One W0312 for each call: the pair with the outermost mutated place. Two
    // overlapping places that both change give the pair in both directions.
    let mut pairs: Vec<(NodeId, PlaceId, PlaceId)> = v.alias_conflict.iter().copied().collect();
    pairs.sort_by_key(|&(n, m, a)| {
        (
            n,
            f.place(m).steps.len(),
            std::cmp::Reverse(f.place(a).steps.len()),
            m,
            a,
        )
    });
    pairs.dedup_by_key(|p| p.0);
    for (n, m, a) in pairs {
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
        let node_place = &f.place(c.node_place).display;
        let what = match (c.task_writes, c.free, c.lends) {
            (_, _, true) => {
                format!("gives `{node_place}` to a function value that can mutate it")
            }
            (true, None, false) => format!("accesses `{node_place}`"),
            (false, None, false) => format!("mutates `{node_place}`"),
            (_, Some(_), false) => format!("frees `{node_place}`"),
        };
        out.push(
            Diagnostic::error(
                "W0405",
                format!(
                    "this code {what} while a task {verb} `{}`",
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

/// W0805 and W0803: the effects that leave `main` or a test.
///
/// The runtime starts these bodies. `who` names the body. `has_root_handler`
/// is true for an effect that the runtime handles. With `no_runtime`, the
/// runtime handles no effect (W0803). Each effect gets one error.
pub fn root_effects(
    f: &FnFacts,
    who: &str,
    no_runtime: bool,
    has_root_handler: &dyn Fn(&str) -> bool,
) -> Vec<Diagnostic> {
    let mut by_effect: BTreeMap<&str, Vec<NodeId>> = BTreeMap::new();
    for (n, e) in &f.escapes_at {
        by_effect.entry(e).or_default().push(*n);
    }
    let escaping: Vec<&str> = by_effect.keys().copied().collect();
    let mut out = Vec::new();
    for (e, mut sites) in by_effect {
        sites.sort_by_key(|&n| node_span(f, n).lo);
        let Some((&first, rest)) = sites.split_first() else {
            continue;
        };
        let span = node_span(f, first);
        let name = root_effect_text(e, &escaping);
        let d = if !has_root_handler(e) {
            Diagnostic::error(
                "W0805",
                format!("{who} performs `{name}`, and no handler handles it"),
                span,
            )
            .note(format!(
                "the runtime handles only the standard effects; handle `{name}` in {who}"
            ))
        } else if no_runtime {
            Diagnostic::error(
                "W0803",
                format!("with no runtime, {who} must handle `{name}` itself"),
                span,
            )
        } else {
            continue;
        };
        out.push(note_more(d, f, rest, ("site", "sites")));
    }
    out
}

/// Returns effect identity `e` as W0805 and W0803 show it.
///
/// The facts name a user effect by its identity, such as `main.Note`. The text
/// shows the written name (`Note`). The text shows the identity when the written
/// name can also name another effect: a standard effect (`Log` alone names the
/// standard one), or another effect in `escaping` (`main.Note` and `main.a.Note`).
fn root_effect_text<'a>(e: &'a str, escaping: &[&str]) -> &'a str {
    let shown = effects::shown(e);
    let std_name = effects::is_std(shown) && !effects::is_std(e);
    let clash = escaping
        .iter()
        .any(|&d| d != e && effects::shown(d) == shown);
    if std_name || clash {
        e
    } else {
        shown
    }
}

/// Replaces `{line:N}` markers (byte offsets) with line numbers. A
/// `{lines:N M ...}` marker becomes `line L` or `lines L1, L2`: each line one
/// time, at most `LISTED_SITES` lines.
pub fn resolve_lines(d: &mut Diagnostic, file: &weft_syntax::SourceFile) {
    for n in &mut d.notes {
        while let Some(start) = n.text.find("{lines:") {
            let Some(end) = n.text[start..].find('}') else {
                break;
            };
            let mut lines: Vec<usize> = n.text[start + 7..start + end]
                .split(' ')
                .filter_map(|o| o.parse().ok())
                .map(|o| file.line_col(o).0)
                .collect();
            lines.sort_unstable();
            lines.dedup();
            let word = if lines.len() == 1 { "line" } else { "lines" };
            let shown: Vec<String> = lines
                .iter()
                .take(LISTED_SITES)
                .map(ToString::to_string)
                .collect();
            let more = if lines.len() > LISTED_SITES {
                ", ..."
            } else {
                ""
            };
            let text = format!("{word} {}{more}", shown.join(", "));
            n.text.replace_range(start..=(start + end), &text);
        }
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

/// Returns effect identity `e` as a diagnostic shows it. When a stated effect of
/// the function has the same written name, the text names the effect that `e` is.
fn effect_text(e: &str, stated: &[String]) -> String {
    let shown = effects::shown(e);
    let clash = stated.iter().any(|d| d != e && effects::shown(d) == shown);
    match (clash, effects::is_std(e)) {
        (false, _) => format!("`{shown}`"),
        (true, true) => format!("the standard effect `{shown}`"),
        (true, false) => format!("`{e}`"),
    }
}
