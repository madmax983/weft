//! Diagnostics from checker results. Each diagnostic shows its derivation.

use std::collections::{BTreeMap, BTreeSet};
use weft_syntax::diag::Code;

use weft_facts::{
    ArgSite, FnFacts, NodeId, PlaceId, RefKind, RefSite, VarId, VarKind, Violations, ARG_TASK,
    TASK_END,
};
use weft_sema::effects;
use weft_syntax::diag::Diagnostic;
use weft_verified::places;

use crate::bridge::fact_key;
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

/// Returns the keys of the facts `relation(var, n)`, one for each node `n` of
/// `nodes` ([`fact_key`]).
fn var_keys(relation: &str, var: VarId, nodes: &[NodeId]) -> Vec<String> {
    nodes
        .iter()
        .map(|n| fact_key(relation, &[&var, n]))
        .collect()
}

fn once_closure(f: &FnFacts, n: NodeId) -> Diagnostic {
    Diagnostic::error(
        Code::W0502,
        "a `once` closure is called twice",
        node_span(f, n),
    )
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
            | VarKind::Result
    ) || var.name.starts_with('{')
}

/// Returns true if the lowering gives variable `var` a name of its own, such
/// as `{closure}`, not a name of the program.
fn described(var: &weft_facts::VarInfo) -> bool {
    var.kind == VarKind::Iterator || var.name.starts_with('{')
}

/// Returns the name of variable `var` as a diagnostic shows it. A variable
/// with a name of the lowering gets a description, with no braces. The holder
/// of the value of a frame, such as `scope body value`, gets `the`.
fn shown_name(var: &weft_facts::VarInfo) -> String {
    if var.kind == VarKind::Iterator {
        "the loop iterator".to_string()
    } else if var.kind == VarKind::BlockValue {
        format!("the {}", var.name)
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
/// different use nodes stay apart: a loop node has the span of the whole loop.
/// The first entry of each group names a variable of the program, if one is
/// in the group, with the earliest use.
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
    arg_outside(f, v, &mut out);
    ref_outside(f, v, &mut out);
    not_uniq(f, v, &mut out);
    arg_effect_outside(f, v, &mut out);
    sim_in_lib(f, v, &mut out);
    root_effects(f, v, &mut out);
    // A stable sort: the errors at one place keep the order of the rules above.
    out.sort_by(|a, b| (a.span.lo, &a.code).cmp(&(b.span.lo, &b.code)));
    out
}

/// W0301: the derivation of the design doc (`error`).
///
/// The evidence (`Report::invalidations`) has one entry for each use. First
/// the entries of one reference and one invalidating node become one entry,
/// at the first use: the other uses go to a note. Then [`group_uses`] joins
/// the entries of different holders with one invalidating node and one use
/// into one error. The node can be a mutation, a lend, a move, a part move, a
/// release or the end of a scope (`Cause`).
fn w0301(f: &FnFacts, r: &Report, out: &mut Vec<Diagnostic>) {
    // The key is the reference and the invalidating node.
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
        // The value that a body gives back, at its `return`.
        if let (VarKind::Result, Cause::ScopeEnd(o)) = (var.kind, inv.cause) {
            if f.node(inv.used_at).label == "return" {
                let keys = group.iter().flat_map(|(e, rest)| {
                    let uses: Vec<NodeId> = std::iter::once(e.used_at)
                        .chain(rest.iter().copied())
                        .collect();
                    var_keys("error", e.var, &uses)
                });
                out.extend(returned(f, inv, o).map(|d| d.with_facts(keys)));
                continue;
            }
        }
        let name = match var.kind {
            VarKind::Temp | VarKind::BlockValue => format!("the {}", var.name),
            VarKind::Result => var.name.clone(),
            _ => shown_name(var),
        };
        let handle = path.strip_suffix(".*");
        let (what, why) = w0301_cause(f, inv);
        let holder = holder_text(f, inv, false);
        let used = node_span(f, inv.used_at);
        // The value of a frame is held only across the end of its frame: a
        // block, a scope body, a handled body or a clause. The name of the
        // hidden variable names the frame.
        let block_value = var.kind == VarKind::BlockValue;
        let d = if let (true, Cause::ScopeEnd(o)) = (block_value, inv.cause) {
            let frame = var.name.strip_suffix(" value").unwrap_or("block");
            let head = match (var.callable, handle) {
                (true, _) => format!("the closure that this {frame} returns captures `{path}`"),
                (false, Some(h)) => {
                    format!("the value of this {frame} points into the object behind `{h}`")
                }
                (false, None) => format!("the value of this {frame} points into `{path}`"),
            };
            Diagnostic::error(
                Code::W0301,
                format!(
                    "{head}, but `{}` goes out of scope at the end of the {frame}",
                    f.var(o).name
                ),
                used,
            )
            .note_at(holder, var.span)
            .note_at(what, at.span)
        } else if let (VarKind::Closure, Cause::ScopeEnd(o)) = (var.kind, inv.cause) {
            // A closure with no name that captures a local of a frame, such as
            // the value of a scope body.
            Diagnostic::error(
                Code::W0301,
                format!(
                    "the closure captures `{path}`, but `{}` goes out of scope before this use",
                    f.var(o).name
                ),
                used,
            )
            .note_at(holder, var.span)
            .note_at(what, at.span)
        } else {
            Diagnostic::error(
                Code::W0301,
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
        // The facts `error(R, P)` of the group: each holder at each of its uses.
        let keys = group.iter().flat_map(|(e, rest)| {
            let uses: Vec<NodeId> = std::iter::once(e.used_at)
                .chain(rest.iter().copied())
                .collect();
            var_keys("error", e.var, &uses)
        });
        out.push(d.with_facts(keys));
    }
}

/// The error of the value that a body gives back (`_0` of the IR, the
/// variable `var` of `inv`), when the end of local `o` at the frame end
/// makes it invalid before its `return` (`docs/ir.md` 6.9):
///
/// - a function or a closure: W0204 at the span of the `return` (the
///   returned expression), as the old lowering. A by-value parameter that
///   the signature states as a returned place has the W0204 of the
///   signature check: no second error.
/// - a handled body, a scope body or a clause: W0301, the value leaves
///   after its place ends.
fn returned(f: &FnFacts, inv: &Invalidation, o: VarId) -> Option<Diagnostic> {
    let var = f.var(inv.var);
    let mut owner = f.var(o).clone();
    // A closure that captures a local by reference points into the cell of
    // the local (`x (cell)`, `docs/ir.md` 6.3): the text names the local.
    let cell = |t: &str| t.strip_suffix(" (cell)").unwrap_or(t).to_string();
    owner.name = cell(&owner.name);
    let path = &cell(&f.place(inv.path).display);
    let span = node_span(f, inv.used_at);
    let holder = holder_text(f, inv, false);
    let what = w0301_cause(f, inv).0;
    let at = f.node(inv.at).span;
    let closure = var.name == "the closure result";
    if var.name != "the result" && !closure {
        let frame = var.name.strip_suffix(" value").unwrap_or("body");
        let message = format!(
            "the value leaves after its place ends: the value of this {frame} points into `{path}`, but `{}` goes out of scope at the end of the {frame}",
            owner.name
        );
        return Some(
            Diagnostic::error(Code::W0301, message, span)
                .note_at(holder, var.span)
                .note_at(what, at),
        );
    }
    let root = f.place(inv.path).root;
    let stated = f.ref_sites.iter().any(|site| {
        matches!(site.kind, RefKind::Return { .. })
            && f.ref_in
                .iter()
                .any(|&(n, d)| n == site.node && f.place(d).root == root)
    });
    if owner.kind == VarKind::Param && stated {
        return None;
    }
    let message = if closure {
        let whose = match owner.kind {
            VarKind::Param => format!("its parameter `{}`", owner.name),
            VarKind::Temp | VarKind::BlockValue => "its temporary value".to_string(),
            _ => format!("its local `{}`", owner.name),
        };
        let head = if var.callable {
            format!("the closure returns a closure that captures `{path}`")
        } else {
            format!("the closure returns a reference into `{path}`")
        };
        format!("{head}: {whose} goes out of scope at the return")
    } else {
        let whose = match owner.kind {
            VarKind::Param => format!("the by-value parameter `{}`", owner.name),
            VarKind::Temp | VarKind::BlockValue => "a temporary value".to_string(),
            _ => format!("the local `{}`", owner.name),
        };
        let head = if var.callable {
            format!("the returned closure captures `{path}`")
        } else {
            format!("returned reference points into `{path}`")
        };
        format!(
            "{head}: {whose} of `{}` goes out of scope at the return",
            f.name
        )
    };
    Some(
        Diagnostic::error(Code::W0204, message, span)
            .note_at(holder, var.span)
            .note_at(what, at),
    )
}

/// Returns the footprint of the handler that node `n` performs through, as a
/// list of places: the footprint that holds place `m`. Returns `None` if no
/// such handler is there.
fn footprint_text(f: &FnFacts, n: NodeId, m: PlaceId) -> Option<String> {
    let cap = f
        .performs_at
        .iter()
        .filter(|&&(p, _)| p == n)
        .map(|&(_, c)| c)
        .find(|&c| f.footprint.contains(&(c, m)))?;
    let places: Vec<&str> = f
        .footprint
        .iter()
        .filter(|&&(c, _)| c == cap)
        .map(|&(_, q)| f.place(q).display.as_str())
        .collect();
    Some(places.join(", "))
}

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
                // A perform, or a call that performs, reaches a handler: it is a
                // call with the footprint of the handler.
                _ if matches!(inv.cause, Cause::Mutation(_)) && !f.mutates_at.contains(&(inv.at, m)) => {
                    match footprint_text(f, inv.at, m) {
                        Some(fp) => format!(
                            "{} : mut({fp}), the footprint of the handler that it performs through",
                            at.label
                        ),
                        None => format!("{} : mut({mutated})", at.label),
                    }
                }
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
            // A scope body and a clause end their own temporaries.
            match at.label.as_str() {
                l @ ("end of the scope body" | "end of the clause") => {
                    format!("temporary : goes out of scope at the {l}")
                }
                _ => "temporary : goes out of scope at the end of the statement".to_string(),
            },
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
            // A reference to a place above the moved part reads the part too.
            let mut above = f.place(m).parent;
            while let Some(q) = above.filter(|&q| q != inv.path) {
                above = f.place(q).parent;
            }
            let why = if above.is_some() {
                format!(
                    "{moved} is a part of {path}, and it is moved at line \u{1}line:{line}\u{1}  →  invalidated at line \u{1}line:{line}\u{1}"
                )
            } else {
                inside(moved, "is moved")
            };
            (format!("{moved} : moved"), why)
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

/// W0302, W0501 and W0502: a value, a continuation or a closure that is used
/// after a move (`use_after_move`). One error for each variable.
fn use_after_move(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for (var, sites) in by_var(f, &v.use_after_move) {
        let Some((&n, rest)) = sites.split_first() else {
            continue;
        };
        let info = f.var(var);
        let (d, noun) = match info.kind {
            VarKind::Continuation => (
                Diagnostic::error(
                    Code::W0501,
                    "a `once` continuation is resumed twice",
                    node_span(f, n),
                )
                .note("an operation that is not `multi` resumes at most once"),
                ("resume", "resumes"),
            ),
            _ if info.callable => (once_closure(f, n), ("call", "calls")),
            _ => (
                Diagnostic::error(
                    Code::W0302,
                    format!("{} used after it was moved", shown_name(info)),
                    node_span(f, n),
                )
                .note_at(decl_note(info), info.span),
                ("use after a move", "uses after a move"),
            ),
        };
        let d = note_more(d, f, rest, noun).with_facts(var_keys("use_after_move", var, &sites));
        out.push(d);
    }
}

/// W0304: a use before a value (`use_before_set`). One error for each
/// variable, at the first use. A note lists the other uses.
fn use_before_set(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for (var, sites) in by_var(f, &v.use_before_set) {
        let info = f.var(var);
        // A handler clause uses its captures at each node that runs it. The
        // diagnostic shows the read in the clause, and the node as a note. So
        // each site shows its read, in source order.
        let mut shown: Vec<(NodeId, NodeId)> = sites
            .iter()
            .map(|&n| (clause_read(f, var, n).unwrap_or(n), n))
            .collect();
        shown.sort_by_key(|&(read, n)| (node_span(f, read).lo, node_span(f, n).lo));
        shown.dedup_by_key(|&mut (read, _)| read);
        let Some((&(read, n), rest)) = shown.split_first() else {
            continue;
        };
        let mut d = Diagnostic::error(
            Code::W0304,
            format!("{} is used before it has a value", shown_name(info)),
            node_span(f, read),
        )
        .note_at(decl_note(info), info.span);
        if read != n {
            d = d.note_at(
                "a handler clause reads it when it runs here",
                node_span(f, n),
            );
        }
        let d = d.note("give it a value on every path before this use");
        let reads: Vec<NodeId> = rest.iter().map(|&(read, _)| read).collect();
        let mut d = note_more(d, f, &reads, ("use", "uses"));
        // A later read in a clause tells where the clause runs too.
        for &(read, n) in rest.iter().filter(|&&(read, n)| read != n) {
            d = d.note_at(
                format!(
                    "a handler clause reads it at line \u{1}line:{}\u{1} when it runs here",
                    node_span(f, read).lo
                ),
                node_span(f, n),
            );
        }
        let keys = var_keys("use_before_set", var, &sites);
        out.push(d.with_facts(keys));
    }
}

/// W0604: a move of a `!Move` value (`moved_immovable`).
fn moved_immovable(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(var, n) in &v.moved_immovable {
        let info = f.var(var);
        out.push(
            Diagnostic::error(
                Code::W0604,
                format!("{} has a `!Move` type and cannot move", shown_name(info)),
                node_span(f, n),
            )
            .note("construct it in place and use it through references")
            .with_facts(var_keys("moved_immovable", var, &[n])),
        );
    }
}

/// W0601: a linear value that goes away with no consume (`unconsumed`).
fn unconsumed(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(var, n) in &v.unconsumed {
        let info = f.var(var);
        let d = if info.kind == VarKind::Task {
            Diagnostic::error(
                Code::W0601,
                format!("task handle `{}` is not joined or detached", info.name),
                node_span(f, n),
            )
        } else if info.kind == VarKind::Dropped && !info.callable {
            Diagnostic::error(
                Code::W0601,
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
                Code::W0601,
                format!("{who} moves a linear value, but it can go out of scope without a call"),
                node_span(f, n),
            )
            .note("call the closure once on every normal path; a callee that gets it can drop it")
        } else {
            Diagnostic::error(
                Code::W0601,
                format!("{} is dropped without being consumed", linear_subject(info)),
                node_span(f, n),
            )
            .note_at(format!("{} (linear)", decl_note(info)), info.span)
            .note("move it into a call that consumes it on every normal path")
        };
        let d = rest_note(f, var, d);
        out.push(d.with_facts(var_keys("unconsumed", var, &[n])));
    }
}

/// W0601: a linear value that gets a new value before a consume (`overwritten`).
fn overwritten(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(var, n) in &v.overwritten {
        let info = f.var(var);
        out.push(
            Diagnostic::error(
                Code::W0601,
                format!(
                    "{} is overwritten before it is consumed",
                    linear_subject(info)
                ),
                node_span(f, n),
            )
            .with_facts(var_keys("overwritten", var, &[n])),
        );
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
        // A scope can cancel a task before it runs, and the closure of the
        // task then goes away with what it moved. The closure of the task
        // captures a linear variable with no `on abort` (`rules::linear`).
        let starts = f.moved_at.contains(&(var, first))
            && f.spawned_at.iter().any(|&(t, p)| {
                p == first
                    && f.captures
                        .iter()
                        .any(|&(u, x)| u == t && f.var(x).linear && !f.var(x).has_on_abort)
            });
        // The end of a scope aborts if a task of the scope failed.
        let how = if starts {
            "a sibling can fail, or the owner can time out or be cancelled, and the closure then goes away with the values that it took; declare `on abort = f` on the type of each linear value that the closure takes, or make the value inside the task"
        } else if at.label == "scope end" {
            "a task of the scope can fail, and the end of the scope then aborts; declare `on abort = f` on the type, or consume the value before the end of the scope"
        } else {
            "declare `on abort = f` on the type, or consume the value before this call"
        };
        let message = if starts {
            let owner = if at.label == "fork branch" {
                "the `fork`"
            } else {
                "the scope"
            };
            // A call or a block can start the task with the value: a callee
            // that runs a function argument as a task, or a block whose code
            // spawns.
            if matches!(at.label.as_str(), "spawn" | "fork branch") {
                format!(
                    "{} moves into the task at `{}`, and {owner} can cancel the task before it runs",
                    linear_subject(info),
                    at.label
                )
            } else {
                format!(
                    "{} moves at `{}`, and a task that starts there takes its linear value; {owner} can cancel the task before it runs",
                    linear_subject(info),
                    at.label
                )
            }
        } else {
            format!(
                "{} is live across `{}`, which can abort",
                linear_subject(info),
                at.label
            )
        };
        let d = Diagnostic::error(Code::W0602, message, at.span)
            .note_at(
                format!("{} (linear, no `on abort`)", decl_note(info)),
                info.span,
            )
            .note(how);
        let d = note_more(d, f, rest, ("site that can abort", "sites that can abort"));
        let d = rest_note(f, var, d);
        out.push(d.with_facts(var_keys("abort_unhandled", var, &sites)));
    }
}

/// Returns the subject of a diagnostic about linear variable `info`: "linear
/// value `t`", "the linear scope body value" for the value of a frame, or
/// "the linear closure" for a value with a name of the lowering.
fn linear_subject(info: &weft_facts::VarInfo) -> String {
    if info.kind == VarKind::BlockValue {
        format!("the linear {}", info.name)
    } else if info.name.starts_with('{') {
        format!(
            "the linear {}",
            info.name.trim_matches(|c| c == '{' || c == '}')
        )
    } else {
        format!("linear value {}", shown_name(info))
    }
}

/// Adds a note to a diagnostic of W0601 or W0602 about variable `var` if a
/// move of a part of it left the other linear parts (`rest_linear`).
fn rest_note(f: &FnFacts, var: VarId, d: Diagnostic) -> Diagnostic {
    let Some(&(_, n)) = f.rest_linear.iter().find(|&&(v, _)| v == var) else {
        return d;
    };
    let info = f.var(var);
    d.note_at(rest_hint(&info.name, &info.ty), node_span(f, n))
}

/// Returns how the program can consume each part of `name`, a value of the
/// type with text `ty`, after a move of one part.
fn rest_hint(name: &str, ty: &str) -> String {
    let ty = ty.trim();
    if ty.starts_with("Vec<") || ty.starts_with('[') {
        return format!(
            "a move of an element leaves the other elements in `{name}`; nothing consumes a `Vec` or an array of linear values, so keep them in a tuple or a struct"
        );
    }
    let pattern = if let Some(inner) = ty.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
        // The number of parts: the commas at the top level of the tuple.
        let mut depth = 0usize;
        let mut parts = 1;
        for c in inner.chars() {
            match c {
                '(' | '<' | '[' => depth += 1,
                ')' | '>' | ']' => depth = depth.saturating_sub(1),
                ',' if depth == 0 => parts += 1,
                _ => {}
            }
        }
        let names: Vec<String> = (0..parts).map(|i| format!("x{i}")).collect();
        format!("`let ({}) = {name}`", names.join(", "))
    } else {
        let head = ty.split('<').next().unwrap_or(ty);
        format!("`let {head}(x0, x1, ...) = {name}`, with one name for each field")
    };
    format!(
        "a move of a part leaves the other linear parts in `{name}`; destructure the value to consume each part: {pattern}"
    )
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
            Code::W0503,
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
        let d = note_more(
            d,
            f,
            rest,
            (
                "operation that can resume more than once",
                "operations that can resume more than once",
            ),
        );
        out.push(d.with_facts(var_keys("live_across_multi", var, &sites)));
    }
}

/// W0703: a mutation that the signature does not state (`unauthorized_mut`).
fn unauthorized_mut(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(n, p) in &v.unauthorized_mut {
        let at = f.node(n);
        out.push(
            Diagnostic::error(
                Code::W0703,
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
            ))
            .with_facts([fact_key("unauthorized_mut", &[&n, &p])]),
        );
    }
}

/// Returns the effects that body `f` states or performs. W0702 names an effect by
/// its identity when another of these shows the same text.
fn stated_or_performed(f: &FnFacts) -> impl Iterator<Item = &str> {
    f.declared_effect
        .iter()
        .chain(f.escapes_at.iter().map(|(_, e)| e))
        .map(String::as_str)
}

/// W0702: an effect that the signature does not state (`unauthorized_effect`).
fn unauthorized_effect(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for (n, e) in &v.unauthorized_effect {
        let at = f.node(*n);
        let note = match written(f, e) {
            Some(w) => format!("add `{w}` to the effects after `/`, or handle it here"),
            None => unnamed_note(f, e),
        };
        out.push(
            Diagnostic::error(
                Code::W0702,
                format!(
                    "`{}` performs {}, which the signature does not allow",
                    at.label,
                    effect_text(f, e, stated_or_performed(f))
                ),
                at.span,
            )
            .note(note)
            .with_facts([fact_key("unauthorized_effect", &[n, e])]),
        );
    }
}

/// W0402: a mutation through a `@ shared` reference (`shared_mutation`).
fn shared_mutation(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(n, p) in &v.shared_mutation {
        let at = f.node(n);
        out.push(
            Diagnostic::error(
                Code::W0402,
                format!(
                    "`{}` mutates `{}` through a `@ shared` reference",
                    at.label,
                    f.place(p).display
                ),
                at.span,
            )
            .with_facts([fact_key("shared_mutation", &[&n, &p])]),
        );
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
        // The error reports each pair of the call.
        let keys = v
            .alias_conflict
            .iter()
            .filter(|t| t.0 == n)
            .map(|(n, m, a)| fact_key("alias_conflict", &[n, m, a]));
        out.push(
            Diagnostic::error(
                Code::W0312,
                format!(
                    "`{}` mutates `{}` while another argument points into `{}`",
                    at.label,
                    f.place(m).display,
                    f.place(a).display
                ),
                at.span,
            )
            .note("the callee sees them as separate places, so it cannot protect the references")
            .with_facts(keys),
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
    // One error for each task and span. It reports the conflict of each node
    // with that span.
    let mut groups: Vec<(&Conflict, Vec<String>)> = Vec::new();
    for c in conflicts {
        let key = fact_key("task_conflict", &[&c.task, &c.at]);
        let s = f.node(c.at).span;
        match groups.last_mut() {
            Some((g, keys)) if g.task == c.task && f.node(g.at).span == s => keys.push(key),
            _ => groups.push((c, vec![key])),
        }
    }
    for (c, keys) in groups {
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
                Code::W0405,
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
            .note("tasks that can run at the same time need separate footprints")
            .with_facts(keys),
        );
    }
}

/// W0401: a `fork` branch that captures a nonportable value
/// (`nonportable_capture`).
fn nonportable_capture(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(t, var) in &v.nonportable_capture {
        let info = f.var(var);
        out.push(
            Diagnostic::error(
                Code::W0401,
                format!(
                    "a `fork` branch captures {}, which is nonportable",
                    shown_name(info)
                ),
                f.tasks[t.index()].span,
            )
            .with_facts([fact_key("nonportable_capture", &[&t, &var])]),
        );
    }
}

/// W0403: a `fork` branch that mutates through a shared-mutable reference
/// (`shared_mut_capture`).
fn shared_mut_capture(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(t, var) in &v.shared_mut_capture {
        let info = f.var(var);
        out.push(
            Diagnostic::error(
                Code::W0403,
                format!(
                    "a `fork` branch mutates through {}, a shared-mutable reference",
                    shown_name(info)
                ),
                f.tasks[t.index()].span,
            )
            .note("a shared-mutable reference is nonportable; split it into `@ uniq` parts first")
            .with_facts([fact_key("shared_mut_capture", &[&t, &var])]),
        );
    }
}

/// W0801: a library that installs a root handler (`root_handler_in_lib`).
fn root_handler_in_lib(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &h in &v.root_handler_in_lib {
        let info = &f.handlers[h.index()];
        // The rule of ADR 0005: the name that the body writes, and the identity
        // when another effect of the body has the same name.
        out.push(
            Diagnostic::error(
                Code::W0801,
                format!(
                    "a library installs a root handler for {}; only binaries and tests can",
                    effect_text(f, &info.effect, named_effects(f))
                ),
                info.span,
            )
            .with_facts([fact_key("root_handler_in_lib", &[&h])]),
        );
    }
}

/// Returns the name of a body that the runtime starts, for W0805 and W0803:
/// `` `main` ``, or the name of a test (`test "x"`). A test name has a space,
/// and a function name has none.
fn started_name(f: &FnFacts) -> String {
    if f.name.starts_with("test ") {
        f.name.clone()
    } else {
        format!("`{}`", f.name)
    }
}

/// Groups the facts `relation(P, E)` by effect: the sites of each effect, in
/// source order.
fn by_effect<'a>(
    f: &FnFacts,
    pairs: impl IntoIterator<Item = &'a (NodeId, String)>,
) -> BTreeMap<&'a str, Vec<NodeId>> {
    let mut map: BTreeMap<&str, Vec<NodeId>> = BTreeMap::new();
    for (n, e) in pairs {
        map.entry(e.as_str()).or_default().push(*n);
    }
    for sites in map.values_mut() {
        sites.sort_by_key(|&n| node_span(f, n).lo);
    }
    map
}

/// W0805 and W0803: the effects that leave `main` or a test
/// (`unhandled_effect`, `embedded_effect`). The runtime starts these bodies.
/// It handles only the standard effects, and with no runtime none. Each effect
/// gets one error, at its first site.
fn root_effects(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    let who = started_name(f);
    let escaping: BTreeSet<&str> = f.escapes_at.iter().map(|(_, e)| e.as_str()).collect();
    let escaping: Vec<&str> = escaping.into_iter().collect();
    for (relation, pairs) in [
        ("unhandled_effect", &v.unhandled_effect),
        ("embedded_effect", &v.embedded_effect),
    ] {
        for (e, sites) in by_effect(f, pairs) {
            let Some((&first, rest)) = sites.split_first() else {
                continue;
            };
            let span = node_span(f, first);
            let name = root_effect_text(f, e, &escaping);
            let d = if relation == "unhandled_effect" {
                let note = match written(f, e) {
                    Some(w) => format!(
                        "the runtime handles only the standard effects; handle `{w}` in {who}"
                    ),
                    None => unnamed_note(f, e),
                };
                Diagnostic::error(
                    Code::W0805,
                    format!("{who} performs {name}, and no handler handles it"),
                    span,
                )
                .note(note)
            } else {
                Diagnostic::error(
                    Code::W0803,
                    format!("with no runtime, {who} must handle {name} itself"),
                    span,
                )
            };
            let keys = sites.iter().map(|n| fact_key(relation, &[n, &e]));
            out.push(note_more(d, f, rest, ("site", "sites")).with_facts(keys));
        }
    }
}

/// Returns the argument of parameter `index` of the call at node `n`
/// (`FnFacts::arg_sites`).
fn arg_site(f: &FnFacts, n: NodeId, index: u32) -> Option<&ArgSite> {
    f.arg_sites.iter().find(|a| a.node == n && a.index == index)
}

/// W0203: a reference argument that points outside the place that its
/// parameter states (`arg_outside`).
fn arg_outside(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(n, i, a) in &v.arg_outside {
        let key = fact_key("arg_outside", &[&n, &i, &a]);
        let Some(site) = arg_site(f, n, i) else {
            out.push(no_site(Code::W0203, f, n, key));
            continue;
        };
        let shown = &f.place(a).display;
        // Inside a stated place, but through an unstable step below it.
        let below = f.param_in.iter().any(|&(p, j, d)| {
            p == n
                && j == i
                && !f.place(d).is_wildcard()
                && f.place(d).root == f.place(a).root
                && places::within(&f.place(a).steps, &f.place(d).steps)
        });
        let below = if below {
            format!(", and `{shown}` is below it through an unstable step")
        } else {
            String::new()
        };
        out.push(
            Diagnostic::error(
                Code::W0203,
                format!(
                    "argument `{}` points into `{shown}`, but `{}` needs `{}`{below}",
                    site.param, site.callee, site.needs
                ),
                site.span,
            )
            .with_facts([key]),
        );
    }
}

/// Returns a diagnostic for a violation whose site the facts do not give
/// (`ArgSite`, `RefSite`). Sema gives a site with each fact, so this is a
/// fact of another producer. The violation still is an error.
fn no_site(code: Code, f: &FnFacts, n: NodeId, key: String) -> Diagnostic {
    Diagnostic::error(
        code,
        format!("`{key}` holds here (the facts give no other details)"),
        node_span(f, n),
    )
    .with_facts([key])
}

/// Returns the place that gets a reference at node `n`
/// (`FnFacts::ref_sites`).
fn ref_site(f: &FnFacts, n: NodeId) -> Option<&RefSite> {
    f.ref_sites.iter().find(|s| s.node == n)
}

/// W0204, W0605: a reference that points outside the place that its function
/// or its field states (`ref_outside`). A return gets one error for each
/// place, and a field one error for each value.
fn ref_outside(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    let mut by_node: BTreeMap<NodeId, Vec<PlaceId>> = BTreeMap::new();
    for &(n, a) in &v.ref_outside {
        by_node.entry(n).or_default().push(a);
    }
    for (n, bad) in by_node {
        let keys: Vec<String> = bad
            .iter()
            .map(|a| fact_key("ref_outside", &[&n, a]))
            .collect();
        let Some(site) = ref_site(f, n) else {
            let code = if f.node(n).label == "return" {
                Code::W0204
            } else {
                Code::W0605
            };
            out.extend(keys.into_iter().map(|k| no_site(code, f, n, k)));
            continue;
        };
        let span = node_span(f, n);
        let at = &site.needs;
        match &site.kind {
            RefKind::Return { env } => {
                for (&a, key) in bad.iter().zip(keys) {
                    let shown = &f.place(a).display;
                    // Inside a stated place, but through an unstable step below it.
                    let below = f.ref_in.iter().any(|&(p, d)| {
                        p == n
                            && !f.place(d).is_wildcard()
                            && f.place(d).root == f.place(a).root
                            && places::within(&f.place(a).steps, &f.place(d).steps)
                    });
                    let message = if *env == Some(f.place(a).root) {
                        format!("the returned reference can come from a handler of a caller, which can give a place outside `{at}`")
                    } else if below {
                        format!("returned reference points into `{shown}`, which is below `{at}` through an unstable step: state the place, or `{at}..`")
                    } else {
                        format!("returned reference points into `{shown}`, but the signature says `{at}`")
                    };
                    out.push(Diagnostic::error(Code::W0204, message, span).with_facts([key]));
                }
            }
            RefKind::Field => {
                let shown = bad.first().map_or("", |&a| f.place(a).display.as_str());
                out.push(
                    Diagnostic::error(
                        Code::W0605,
                        format!("this field can point only into `{at}` of its own struct, but the value points into `{shown}`"),
                        span,
                    )
                    .with_facts(keys),
                );
            }
            RefKind::Literal { field } => {
                let shown: Vec<&str> = bad.iter().map(|&a| f.place(a).display.as_str()).collect();
                out.push(
                    Diagnostic::error(
                        Code::W0605,
                        format!(
                            "`{field}` can point only into `{at}` of its own struct, but this value points into `{}`; give the field its value after the struct has a place",
                            shown.join(" | ")
                        ),
                        span,
                    )
                    .with_facts(keys),
                );
            }
        }
    }
}

/// W0406: an argument that can be aliased for a `@ uniq` parameter
/// (`not_uniq`). For a call in a closure, the error is where the closure runs.
fn not_uniq(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &(n, i) in &v.not_uniq {
        let key = fact_key("not_uniq", &[&n, &i]);
        let Some(site) = arg_site(f, n, i) else {
            out.push(no_site(Code::W0406, f, n, key));
            continue;
        };
        let head = format!(
            "`{}` needs a `@ uniq` reference for `{}`",
            site.callee, site.param
        );
        let message = match &site.via {
            Some(local) => {
                format!("{head}: the closure gives it `{local}`, which is not `@ uniq` here")
            }
            None => head,
        };
        out.push(Diagnostic::error(Code::W0406, message, site.span).with_facts([key]));
    }
}

/// W0705: a function argument that performs an effect that its parameter type
/// does not allow (`arg_effect_outside`). One error for each argument.
fn arg_effect_outside(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    let mut by_arg: BTreeMap<(NodeId, u32), Vec<&str>> = BTreeMap::new();
    for (n, i, e) in &v.arg_effect_outside {
        by_arg.entry((*n, *i)).or_default().push(e);
    }
    for ((n, i), extra) in by_arg {
        let keys = extra
            .iter()
            .map(|e| fact_key("arg_effect_outside", &[&n, &i, e]));
        let Some(site) = arg_site(f, n, i) else {
            out.extend(keys.map(|k| no_site(Code::W0705, f, n, k)));
            continue;
        };
        let shown: Vec<&str> = extra.iter().map(|e| effects::shown(e)).collect();
        out.push(
            Diagnostic::error(
                Code::W0705,
                format!(
                    "this function argument performs `{}`, which its parameter type does not allow",
                    shown.join(", ")
                ),
                site.span,
            )
            .with_facts(keys),
        );
    }
}

/// W0802: a library that uses `sim.run` (`sim_in_lib`).
fn sim_in_lib(f: &FnFacts, v: &Violations, out: &mut Vec<Diagnostic>) {
    for &n in &v.sim_in_lib {
        out.push(
            Diagnostic::error(
                Code::W0802,
                "only binaries and tests can install root handlers (`sim.run`)",
                node_span(f, n),
            )
            .with_facts([fact_key("sim_in_lib", &[&n])]),
        );
    }
}

/// Returns effect identity `e` as W0805 and W0803 show it, with its quotes.
///
/// The facts name a user effect by its identity, such as `main.a.Note`. The
/// text shows the name that body `f` can write (`a.Note`). A user effect shows
/// its identity when that name is also the name of a standard effect (`Log`).
/// Else the text follows [`effect_text`]: when another effect in `escaping`
/// shows the same text, a user effect shows its identity and a standard effect
/// is "the standard effect `Log`".
fn root_effect_text(f: &FnFacts, e: &str, escaping: &[&str]) -> String {
    let shown = effect_shown(f, e);
    if effects::is_std(shown) && !effects::is_std(e) {
        return format!("`{e}`");
    }
    effect_text(f, e, escaping.iter().copied())
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

/// Returns the note for a user effect that body `f` cannot name: a private
/// effect of another package, or an effect whose paths a nearer name hides.
fn unnamed_note(f: &FnFacts, e: &str) -> String {
    effects::unnamed_note(e, f.effect_hidden(e))
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
/// [`effect_shown`]). When another effect of `others` shows the same text, the
/// text names the effect that `e` is: the standard effect `Log`, or the
/// identity of a user effect (`main.Log`).
fn effect_text<'a>(f: &FnFacts, e: &str, others: impl IntoIterator<Item = &'a str>) -> String {
    let shown = effect_shown(f, e);
    let clash = others
        .into_iter()
        .any(|d| d != e && effect_shown(f, d) == shown);
    match (clash, effects::is_std(e)) {
        (false, _) => format!("`{shown}`"),
        (true, true) => format!("the standard effect `{shown}`"),
        (true, false) => format!("`{e}`"),
    }
}

/// Returns each effect that the facts of body `f` name: the stated, escaping,
/// handled and clause effects.
fn named_effects(f: &FnFacts) -> impl Iterator<Item = &str> {
    f.declared_effect
        .iter()
        .chain(f.escapes_at.iter().map(|(_, e)| e))
        .chain(f.handlers.iter().map(|h| &h.effect))
        .chain(f.clause_performs.iter().map(|(_, e)| e))
        .map(String::as_str)
}
