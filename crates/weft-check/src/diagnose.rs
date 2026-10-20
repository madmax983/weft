//! Diagnostics from checker results. Each diagnostic shows its derivation.

use std::collections::BTreeMap;

use weft_facts::{FnFacts, NodeId, PlaceId, VarId, VarKind, Violations, ARG_TASK, TASK_END};
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

/// Returns the first node that uses `var` in a handler clause that node `n` runs.
/// Node `n` performs through a local handler. The entry node of a clause names
/// the capability of its handler in its detail (`c3`). The search covers the
/// part of the graph that starts at such an entry.
fn clause_read(f: &FnFacts, var: VarId, n: NodeId) -> Option<NodeId> {
    let caps: Vec<String> = f
        .performs_at
        .iter()
        .filter(|&&(p, _)| p == n)
        .map(|&(_, c)| format!("c{}", c.0))
        .collect();
    if caps.is_empty() {
        return None;
    }
    let mut succ: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for &(a, b) in &f.cfg_edge {
        succ.entry(a).or_default().push(b);
    }
    let mut seen = vec![false; f.nodes.len()];
    let mut work: Vec<NodeId> = (0..f.nodes.len())
        .filter(|&i| f.nodes[i].label == "handler clause" && caps.contains(&f.nodes[i].detail))
        .map(|i| NodeId(u32::try_from(i).unwrap_or(u32::MAX)))
        .collect();
    while let Some(a) = work.pop() {
        if std::mem::replace(&mut seen[a.index()], true) {
            continue;
        }
        work.extend(succ.get(&a).into_iter().flatten().copied());
    }
    f.uses
        .iter()
        .filter(|&&(v, q)| v == var && seen[q.index()])
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
/// [`resolve_lines`] changes the marker of the offsets into line numbers.
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
        "and {} more {noun}, at \u{1}lines:{}\u{1}",
        rest.len(),
        offsets.join(" ")
    ))
}

/// Returns true if variable `var` is a hidden variable of the lowering, not a
/// variable of the program: a temporary, the holder of a part, a closure with
/// no name, the hidden iterator of a loop or a value that a generic item drops.
fn is_hidden(var: &weft_facts::VarInfo) -> bool {
    matches!(
        var.kind,
        VarKind::Temp
            | VarKind::BlockValue
            | VarKind::Iterator
            | VarKind::Closure
            | VarKind::Dropped
    ) || var.name.starts_with('{')
}

/// Returns true if the lowering gives variable `var` a name of its own, such
/// as `{closure}`, not a name of the program.
fn described(var: &weft_facts::VarInfo) -> bool {
    var.kind == VarKind::Iterator || var.name.starts_with('{')
}

/// Returns the name of variable `var` as a diagnostic shows it. A variable
/// with a name of the lowering gets a description, with no braces.
fn shown_name(var: &weft_facts::VarInfo) -> String {
    if var.kind == VarKind::Iterator {
        "the loop iterator".to_string()
    } else if var.name.starts_with('{') {
        format!("the {}", var.name.trim_matches(|c| c == '{' || c == '}'))
    } else {
        format!("`{}`", var.name)
    }
}

/// Returns the note that shows variable `var` and its type.
fn decl_note(var: &weft_facts::VarInfo) -> String {
    let name = if described(var) {
        shown_name(var)
    } else {
        var.name.clone()
    };
    format!("{name} : {}", var.ty)
}

/// Returns the text of the note about the variable of `inv` and what it holds.
/// With `also`, the note is about another holder of the same places.
fn holder_text(f: &FnFacts, inv: &Invalidation, also: bool) -> String {
    let var = f.var(inv.var);
    let path = &f.place(inv.path).display;
    let name = if described(var) {
        shown_name(var)
    } else if also && matches!(var.kind, VarKind::Temp | VarKind::BlockValue) {
        format!("the {}", var.name)
    } else {
        var.name.clone()
    };
    if var.callable {
        format!("{name} : {}, captures {path}", var.ty)
    } else if let Some(h) = path.strip_suffix(".*") {
        format!(
            "{name} : &{} through the `Rc` handle {h}",
            var.ty.trim_start_matches('&')
        )
    } else {
        format!("{name} : &{} in {path}", var.ty.trim_start_matches('&'))
    }
}

/// Groups the W0301 entries (a reference, its first use, and its other uses)
/// that have one invalidating node and one use. One use is one use node. A
/// hidden variable and a variable of the program have one use also if the span
/// of one use is inside the span of the other. Two variables of one kind with
/// different use nodes stay apart: a loop node has the span of the whole loop. The first entry of each group names a variable
/// of the program, if one is in the group, with the earliest use.
fn group_uses<'a>(
    f: &FnFacts,
    entries: Vec<(&'a Invalidation, Vec<NodeId>)>,
) -> Vec<Vec<(&'a Invalidation, Vec<NodeId>)>> {
    let one_use = |a: &Invalidation, b: &Invalidation| {
        if a.used_at == b.used_at {
            return true;
        }
        if is_hidden(f.var(a.var)) == is_hidden(f.var(b.var)) {
            return false;
        }
        let (x, y) = (node_span(f, a.used_at), node_span(f, b.used_at));
        (x.lo >= y.lo && x.hi <= y.hi) || (y.lo >= x.lo && y.hi <= x.hi)
    };
    let mut groups: Vec<Vec<(&Invalidation, Vec<NodeId>)>> = Vec::new();
    for e in entries {
        let found = groups
            .iter_mut()
            .find(|g| g.iter().any(|(o, _)| o.at == e.0.at && one_use(o, e.0)));
        match found {
            Some(g) => g.push(e),
            None => groups.push(vec![e]),
        }
    }
    for g in &mut groups {
        g.sort_by_key(|(inv, _)| {
            (
                is_hidden(f.var(inv.var)),
                node_span(f, inv.used_at).lo,
                inv.var,
            )
        });
    }
    groups
}

/// The character around a marker of node offsets in the text of a note
/// (`line:N`, `lines:N M`). No source text has it, so no other text can look
/// like a marker. [`resolve_lines`] changes each marker into line numbers.
const MARK: char = '\u{1}';

/// Turns a checker report into diagnostics, in source order. `file` is the
/// source of the body: the notes give line numbers in it.
///
/// A rule that fails at many nodes for one variable gives one error, at the
/// first node. A note lists the other nodes.
pub fn diagnose(f: &FnFacts, r: &Report, file: &weft_syntax::SourceFile) -> Vec<Diagnostic> {
    let mut out = diagnose_marked(f, r);
    for d in &mut out {
        resolve_lines(d, file);
    }
    out
}

/// Turns a checker report into diagnostics whose notes can hold markers of
/// node offsets (`MARK`). Each rule has a function of its own.
pub(crate) fn diagnose_marked(f: &FnFacts, r: &Report) -> Vec<Diagnostic> {
    let v = &r.violations;
    let mut out = Vec::new();
    w0301(f, r, &mut out);
    use_after_move(f, v, &mut out);
    use_before_set(f, v, &mut out);
    moved_immovable(f, v, &mut out);
    unconsumed(f, v, &mut out);
    overwritten(f, v, &mut out);
    abort_unhandled(f, v, &mut out);
    live_across_multi(f, v, &mut out);
    unauthorized_mut(f, v, &mut out);
    unauthorized_effect(f, v, &mut out);
    shared_mutation(f, v, &mut out);
    alias_conflict(f, v, &mut out);
    task_conflict(f, r, &mut out);
    nonportable_capture(f, v, &mut out);
    shared_mut_capture(f, v, &mut out);
    root_handler_in_lib(f, v, &mut out);
    // A stable sort: the errors at one place keep the order of the rules above.
    out.sort_by(|a, b| (a.span.lo, &a.code).cmp(&(b.span.lo, &b.code)));
    out
}

/// W0301: the derivation of the design doc (`error`).
fn w0301(f: &FnFacts, r: &Report, out: &mut Vec<Diagnostic>) {
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
    // One entry for each reference and invalidating node, at its first use.
    let mut entries: Vec<(&Invalidation, Vec<NodeId>)> = Vec::new();
    for mut uses in invalidations.into_values() {
        uses.sort_by_key(|inv| node_span(f, inv.used_at).lo);
        let Some((&inv, rest)) = uses.split_first() else {
            continue;
        };
        entries.push((inv, rest.iter().map(|i| i.used_at).collect()));
    }
    // Entries with one invalidating node and uses in one expression are one
    // error: it names a variable of the program, and a note names each other
    // holder, such as the hidden variable of a part or of a stored closure.
    for group in group_uses(f, entries) {
        let Some(((inv, rest), others)) = group.split_first() else {
            continue;
        };
        let inv = *inv;
        let var = f.var(inv.var);
        let path = &f.place(inv.path).display;
        let at = f.node(inv.at);
        let name = match var.kind {
            VarKind::Temp | VarKind::BlockValue => format!("the {}", var.name),
            _ => shown_name(var),
        };
        let handle = path.strip_suffix(".*");
        let (what, why) = w0301_cause(f, inv);
        let holder = holder_text(f, inv, false);
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
            .note(format!("used at line \u{1}line:{}\u{1}", used.lo))
        };
        let mut d = note_more(d, f, rest, ("use", "uses"));
        for (other, _) in others {
            let text = format!("also {}", holder_text(f, other, true));
            d = d.note_at(text, f.var(other.var).span);
        }
        out.push(d);
    }
}

/// W0302, W0501 and W0502: a value, a continuation or a closure that is used
/// after a move (`use_after_move`). One error for each variable.
/// Returns the notes of W0301 about the node that invalidates the reference of
/// `inv`: what the node does, and why that invalidates the reference.
fn w0301_cause(f: &FnFacts, inv: &Invalidation) -> (String, String) {
    let path = &f.place(inv.path).display;
    let at = f.node(inv.at);
    let line = at.span.lo;
    let handle = path.strip_suffix(".*");
    let inside = |owner: &str, verb: &str| {
        let head = if path == owner {
            format!("{owner} {verb}")
        } else if handle == Some(owner) {
            format!("{owner} is an `Rc` handle on the way to the place, and it {verb}")
        } else {
            format!("{path} is inside {owner}, which {verb}")
        };
        format!(
            "{head} at line \u{1}line:{line}\u{1}  →  invalidated at line \u{1}line:{line}\u{1}"
        )
    };
    match inv.cause {
        Cause::Mutation(m) | Cause::Lend(m) => {
            let mutated = &f.place(m).display;
            let what = match (at.detail.is_empty(), at.label.strip_suffix(" =")) {
                // A task that ends here can have changed the place while it ran.
                _ if matches!(inv.cause, Cause::Lend(_)) && at.label == TASK_END => {
                    format!("{TASK_END} : the task could change {mutated} while it ran")
                }
                _ if matches!(inv.cause, Cause::Lend(_)) => format!(
                    "{} : gets {mutated}, and it can mutate through it",
                    at.label
                ),
                (true, Some(target)) => format!("{target} : new value"),
                (true, None) => format!("{} : mut({mutated})", at.label),
                (false, _) => format!("{} : {}", at.label, at.detail),
            };
            // Inside one one-place wildcard place, rule 3 compares the steps.
            let one = f.one_place_of(m);
            let same = one.is_some() && one == f.one_place_of(inv.path);
            let why = match (f.wild_base(inv.path), f.wild_base(m)) {
                _ if same => format!(
                    "{mutated} is a strict prefix of {path}, through an unstable step  →  invalidated at line \u{1}line:{line}\u{1}"
                ),
                (Some(b), _) => format!(
                    "{path} can be any place inside {}, and {mutated} overlaps it  →  invalidated at line \u{1}line:{line}\u{1}",
                    f.place(b).display
                ),
                (None, Some(b)) => format!(
                    "{mutated} can be any place inside {}, which holds {path}  →  invalidated at line \u{1}line:{line}\u{1}",
                    f.place(b).display
                ),
                (None, None) if handle == Some(mutated.as_str()) => format!(
                    "{mutated} is an `Rc` handle on the way to the place, and a new value of it can free the object  →  invalidated at line \u{1}line:{line}\u{1}"
                ),
                (None, None) => format!(
                    "{mutated} is a strict prefix of {path}, through an unstable step  →  invalidated at line \u{1}line:{line}\u{1}"
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
            format!("{path} is inside a temporary value, which goes out of scope at line \u{1}line:{line}\u{1}  →  invalidated at line \u{1}line:{line}\u{1}"),
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
        Cause::Unwound(o) => {
            let owner = &f.var(o).name;
            let when = "goes out of scope on an abort path";
            (format!("{owner} : {when}"), inside(owner, when))
        }
        Cause::MovePart(m) => {
            let moved = &f.place(m).display;
            (format!("{moved} : moved"), inside(moved, "is moved"))
        }
        Cause::Release(m) => {
            let freed = &f.place(m).display;
            (
                format!(
                    "{} : the handled body changed a place above what {freed} points to",
                    at.label
                ),
                inside(freed, "can be freed"),
            )
        }
    }
}

fn use_after_move(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
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
                    format!("{} used after it was moved", shown_name(info)),
                    node_span(f, n),
                )
                .note_at(decl_note(info), info.span),
                ("use after a move", "uses after a move"),
            ),
        };
        out.push(note_more(d, f, rest, noun));
    }
}

/// W0304: a use before a value (`use_before_set`).
fn use_before_set(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(var, n) in &v.use_before_set {
        let info = f.var(var);
        // A handler clause uses its captures at each node that runs it. The
        // diagnostic shows the read in the clause, and the node as a note.
        let read = clause_read(f, var, n);
        let mut d = Diagnostic::error(
            "W0304",
            format!("{} is used before it has a value", shown_name(info)),
            node_span(f, read.unwrap_or(n)),
        )
        .note_at(decl_note(info), info.span);
        if read.is_some() {
            d = d.note_at(
                "a handler clause reads it when it runs here",
                node_span(f, n),
            );
        }
        out.push(d.note("give it a value on every path before this use"));
    }
}

/// W0604: a move of a `!Move` value (`moved_immovable`).
fn moved_immovable(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(var, n) in &v.moved_immovable {
        let info = f.var(var);
        out.push(
            Diagnostic::error(
                "W0604",
                format!("{} has a `!Move` type and cannot move", shown_name(info)),
                node_span(f, n),
            )
            .note("construct it in place and use it through references"),
        );
    }
}

/// W0601: a linear value that goes away with no consume (`unconsumed`).
fn unconsumed(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(var, n) in &v.unconsumed {
        let info = f.var(var);
        let d = if info.kind == VarKind::Task {
            Diagnostic::error(
                "W0601",
                format!("task handle `{}` is not joined or detached", info.name),
                node_span(f, n),
            )
        } else if info.kind == VarKind::Dropped && !info.callable {
            Diagnostic::error(
                "W0601",
                format!(
                    "`{}` drops a value of the linear type `{}`",
                    info.name, info.ty
                ),
                node_span(f, n),
            )
            .note(format!(
                "`{}` can drop a value of its type parameter here; a linear value must be consumed on every normal path",
                info.name
            ))
        } else if info.callable {
            let who = if matches!(
                info.kind,
                VarKind::Closure | VarKind::Temp | VarKind::Dropped
            ) {
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
                    "linear value {} is dropped without being consumed",
                    shown_name(info)
                ),
                node_span(f, n),
            )
            .note_at(format!("{} (linear)", decl_note(info)), info.span)
            .note("move it into a call that consumes it on every normal path")
        };
        out.push(d);
    }
}

/// W0601: a linear value that gets a new value before a consume (`overwritten`).
fn overwritten(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(var, n) in &v.overwritten {
        let info = f.var(var);
        out.push(Diagnostic::error(
            "W0601",
            format!(
                "linear value {} is overwritten before it is consumed",
                shown_name(info)
            ),
            node_span(f, n),
        ));
    }
}

/// W0602: a linear value with no `on abort` that is live where code can abort
/// (`abort_unhandled`).
fn abort_unhandled(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
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
                "linear value {} is live across `{}`, which can abort",
                shown_name(info),
                at.label
            ),
            at.span,
        )
        .note_at(
            format!("{} (linear, no `on abort`)", decl_note(info)),
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
}

/// W0503: a value that is not `many` and is live across a `multi` operation
/// (`live_across_multi`).
fn live_across_multi(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    // W0503: one error for each value, at the first `multi` operation.
    for (var, sites) in by_var(f, &v.live_across_multi) {
        let Some((&first, rest)) = sites.split_first() else {
            continue;
        };
        let info = f.var(var);
        let at = f.node(first);
        let name = shown_name(info);
        let mut d = Diagnostic::error(
            "W0503",
            format!(
                "{name} is not `many`, but it is live across `{}`, which can resume more than once",
                at.label
            ),
            at.span,
        )
        .note_at(decl_note(info), info.span);
        if info.immovable {
            d = d.note(
                "a `!Move` value keeps its address, and each resume runs with a copy of the value",
            );
        }
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
}

/// W0703: a mutation that the signature does not state (`unauthorized_mut`).
fn unauthorized_mut(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
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
}

/// W0702: an effect that the signature does not state (`unauthorized_effect`).
fn unauthorized_effect(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for (n, e) in &v.unauthorized_effect {
        let at = f.node(*n);
        let note = match written(f, e) {
            Some(w) => format!("add `{w}` to the effects after `/`, or handle it here"),
            None => private_note(e),
        };
        out.push(
            Diagnostic::error(
                "W0702",
                format!(
                    "`{}` performs {}, which the signature does not allow",
                    at.label,
                    effect_text(f, e)
                ),
                at.span,
            )
            .note(note),
        );
    }
}

/// W0402: a mutation through a `@ shared` reference (`shared_mutation`).
fn shared_mutation(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
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
}

/// W0312: a mutated argument that another argument points into
/// (`alias_conflict`).
fn alias_conflict(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
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
}

/// W0405: an access that overlaps the footprint of a task that can run at the
/// same time (`task_conflict`).
fn task_conflict(f: &FnFacts, r: &Report, out: &mut Vec<Diagnostic>) {
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
            (_, _, true) if at.label == TASK_END => {
                format!("waits for a task that can change `{node_place}`")
            }
            (_, _, true) if at.label == ARG_TASK => {
                format!("calls a callee that can change `{node_place}`")
            }
            (true, None, false) if at.label == ARG_TASK => {
                format!("calls a callee that can access `{node_place}`")
            }
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
}

/// W0401: a `fork` branch that captures a nonportable value
/// (`nonportable_capture`).
fn nonportable_capture(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(t, var) in &v.nonportable_capture {
        let info = f.var(var);
        out.push(Diagnostic::error(
            "W0401",
            format!(
                "a `fork` branch captures {}, which is nonportable",
                shown_name(info)
            ),
            f.tasks[t.index()].span,
        ));
    }
}

/// W0403: a `fork` branch that mutates through a shared-mutable reference
/// (`shared_mut_capture`).
fn shared_mut_capture(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(t, var) in &v.shared_mut_capture {
        let info = f.var(var);
        out.push(
            Diagnostic::error(
                "W0403",
                format!(
                    "a `fork` branch mutates through {}, a shared-mutable reference",
                    shown_name(info)
                ),
                f.tasks[t.index()].span,
            )
            .note("a shared-mutable reference is nonportable; split it into `@ uniq` parts first"),
        );
    }
}

/// W0801: a library that installs a root handler (`root_handler_in_lib`).
fn root_handler_in_lib(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
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
        let name = root_effect_text(f, e, &escaping);
        let d = if !has_root_handler(e) {
            let note = match written(f, e) {
                Some(w) => {
                    format!("the runtime handles only the standard effects; handle `{w}` in {who}")
                }
                None => private_note(e),
            };
            Diagnostic::error(
                "W0805",
                format!("{who} performs `{name}`, and no handler handles it"),
                span,
            )
            .note(note)
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
/// The facts name a user effect by its identity, such as `main.a.Note`. The
/// text shows the name that body `f` can write (`a.Note`). The text shows the
/// identity when that name is also the name of a standard effect (`Log`), or the
/// text of another effect in `escaping`.
fn root_effect_text<'a>(f: &'a FnFacts, e: &'a str, escaping: &[&str]) -> &'a str {
    let shown = effect_shown(f, e);
    let std_name = effects::is_std(shown) && !effects::is_std(e);
    let clash = escaping
        .iter()
        .any(|&d| d != e && effect_shown(f, d) == shown);
    if std_name || clash {
        e
    } else {
        shown
    }
}

/// Returns effect identity `e` as a message of body `f` shows it: a standard
/// effect has its name (`Log`), and a user effect has the name that the body
/// can write (`Note`, `a.Note`, `util.Note`). A user effect that the body cannot
/// name has its identity.
fn effect_shown<'a>(f: &'a FnFacts, e: &'a str) -> &'a str {
    if effects::is_std(e) {
        e
    } else {
        f.effect_name(e).unwrap_or(e)
    }
}

/// Returns effect identity `e` as body `f` can write it in a row or in a
/// `handle`: the alias of a standard effect (`log`), or the name or path of a
/// user effect (`a.Note`). Returns `None` if the body cannot name it.
fn written(f: &FnFacts, e: &str) -> Option<String> {
    if effects::is_std(e) {
        Some(effects::in_signature(e))
    } else {
        f.effect_name(e).map(str::to_string)
    }
}

/// Returns the note for a user effect that the body cannot name: a private
/// effect of another package.
fn private_note(e: &str) -> String {
    format!("`{e}` is private in its package: code outside the package cannot state or handle it; the package must make it `pub`")
}

/// Changes the markers of node offsets in the notes of `d` into line numbers
/// of `file`: `line:N` gives one line, and `lines:N M` gives a list with at
/// most [`LISTED_SITES`] lines.
pub(crate) fn resolve_lines(d: &mut Diagnostic, file: &weft_syntax::SourceFile) {
    for n in &mut d.notes {
        let mut text = String::new();
        let mut parts = n.text.split(MARK);
        if let Some(first) = parts.next() {
            text.push_str(first);
        }
        // The parts alternate: a marker, then plain text.
        let mut marker = true;
        for part in parts {
            if !marker {
                text.push_str(part);
                marker = true;
                continue;
            }
            marker = false;
            if let Some(list) = part.strip_prefix("lines:") {
                let mut lines: Vec<usize> = list
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
                text.push_str(word);
                text.push(' ');
                text.push_str(&shown.join(", "));
                text.push_str(more);
            } else if let Some(num) = part.strip_prefix("line:") {
                let offset: u32 = num.parse().unwrap_or(0);
                text.push_str(&file.line_col(offset).0.to_string());
            } else {
                text.push_str(part);
            }
        }
        n.text = text;
    }
}

/// Returns effect identity `e` as a diagnostic of body `f` shows it (see
/// [`effect_shown`]). When a stated effect of the function shows the same text,
/// the text names the effect that `e` is.
fn effect_text(f: &FnFacts, e: &str) -> String {
    let shown = effect_shown(f, e);
    let clash = f
        .declared_effect
        .iter()
        .any(|d| d != e && effect_shown(f, d) == shown);
    match (clash, effects::is_std(e)) {
        (false, _) => format!("`{shown}`"),
        (true, true) => format!("the standard effect `{shown}`"),
        (true, false) => format!("`{e}`"),
    }
}
