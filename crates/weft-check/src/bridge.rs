//! Runs the Datalog specification (`spec/weft.dl`) on the facts.
//!
//! This is the reference semantics. The production checker must give the same
//! [`Violations`].

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::sync::OnceLock;

use weft_datalog::{
    evaluate, parse_program_named, Database, Derivation, EvalOptions, Output, Premise, Program,
    Reason, Value,
};
use weft_facts::{FnFacts, HandlerId, NodeId, PlaceId, Step, TaskId, TaskKind, VarId, Violations};
use weft_verified::places;

/// The source of the specification.
pub const SPEC_SRC: &str = include_str!("../../../spec/weft.dl");

/// Returns the parsed specification. The first call parses it, and later
/// calls use that result.
///
/// # Panics
///
/// Panics if `spec/weft.dl` does not parse. The file is part of this crate
/// (`include_str!`), and a test parses it, so this cannot happen in a build
/// that passed its tests.
pub fn spec() -> &'static Program {
    static SPEC: OnceLock<Program> = OnceLock::new();
    SPEC.get_or_init(|| match parse_program_named("spec/weft.dl", SPEC_SRC) {
        Ok(p) => p,
        Err(e) => panic!("spec/weft.dl does not parse: {e}"),
    })
}

/// Why the spec gives no violations for a body.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SpecError {
    /// The Datalog engine failed.
    #[error("the spec does not evaluate: {0}")]
    Eval(#[from] weft_datalog::Error),
    /// A violation fact has a value that is not an id of the facts.
    #[error("the spec derives `{0}`, and a value in it is not an id of the facts")]
    BadTuple(String),
}

/// One argument of an input fact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Arg {
    /// A symbol, such as `n3` or `Log`.
    Sym(String),
    /// An integer.
    Int(i64),
}

/// A group of places that can have related last steps. The key is the root,
/// the depth and the class of the last step.
type StepGroup = (u32, usize, (u8, u32));

/// Calls `emit` once for each input fact of one function.
pub fn each_fact(f: &FnFacts, emit: &mut dyn FnMut(&str, &[Arg])) {
    let s = |x: &dyn std::fmt::Display| Arg::Sym(x.to_string());
    for (i, p) in f.places.iter().enumerate() {
        let id = PlaceId(u32::try_from(i).unwrap_or(0));
        emit("place", &[s(&id)]);
        if let Some(q) = p.parent {
            emit("parent", &[s(&id), s(&q)]);
        }
        if p.steps.last().is_some_and(|st| st.unstable) {
            emit("unstable", &[s(&id)]);
        }
        if p.is_wildcard() {
            emit("wildcard", &[s(&id)]);
        }
        if f.param_rooted(id) {
            emit("param_rooted", &[s(&id)]);
        }
    }
    // Last-step relations between places of the same root and depth. Two last
    // steps of different classes have no relation (`places::step_class`), so
    // the loop compares the places of one class.
    let mut groups: BTreeMap<StepGroup, Vec<(usize, &Step)>> = BTreeMap::new();
    for (i, p) in f.places.iter().enumerate() {
        if let Some(last) = p.steps.last() {
            groups
                .entry((p.root.0, p.steps.len(), places::step_class(last)))
                .or_default()
                .push((i, last));
        }
    }
    let mut pairs = Vec::new();
    for (&(root, depth, _), group) in &groups {
        for &(i, a) in group {
            for &(j, b) in group {
                let (alias, within) = (places::step_alias(a, b), places::step_within(a, b));
                if alias || within {
                    pairs.push((root, depth, i, j, alias, within));
                }
            }
        }
    }
    // The facts come in the order of root, depth and place, as with no classes.
    pairs.sort_unstable();
    for (_, _, i, j, alias, within) in pairs {
        let pv = s(&PlaceId(u32::try_from(i).unwrap_or(0)));
        let qv = s(&PlaceId(u32::try_from(j).unwrap_or(0)));
        if alias {
            emit("step_alias", &[pv.clone(), qv.clone()]);
        }
        if within {
            emit("step_within", &[pv, qv]);
        }
    }
    for (a, b) in &f.cfg_edge {
        emit("cfg_edge", &[s(a), s(b)]);
    }
    macro_rules! rel2 {
        ($name:literal, $v:expr) => {
            for (a, b) in &$v {
                emit($name, &[s(a), s(b)]);
            }
        };
    }
    rel2!("points_into", f.points_into);
    rel2!("mutates_at", f.mutates_at);
    rel2!("reads_at", f.reads_at);
    rel2!("performs_at", f.performs_at);
    rel2!("footprint", f.footprint);
    rel2!("rebound_at", f.rebound_at);
    rel2!("uses", f.uses);
    rel2!("moved_at", f.moved_at);
    rel2!("scope_end", f.scope_end);
    rel2!("owner", f.owner);
    rel2!("moved_part", f.moved_part);
    rel2!("spawned_at", f.spawned_at);
    rel2!("joined_at", f.joined_at);
    rel2!("task_reads", f.task_reads);
    rel2!("task_writes", f.task_writes);
    rel2!("captures", f.captures);
    rel2!("mut_through", f.mut_through);
    rel2!("lends_mut", f.lends_mut);
    for (p, e) in &f.escapes_at {
        emit("escapes_at", &[s(p), s(e)]);
    }
    for n in &f.may_abort {
        emit("may_abort", &[s(n)]);
    }
    for n in &f.multi_at {
        emit("multi_at", &[s(n)]);
    }
    for d in &f.declared_mut {
        emit("declared_mut", &[s(d)]);
    }
    for e in &f.declared_effect {
        emit("declared_effect", &[s(e)]);
    }
    for sr in &f.shared_root {
        emit("shared_root", &[s(sr)]);
    }
    for (i, v) in f.vars.iter().enumerate() {
        let id = s(&VarId(u32::try_from(i).unwrap_or(0)));
        for (flag, name) in [
            (v.linear, "linear"),
            (v.has_on_abort, "has_on_abort"),
            (v.once, "once_var"),
            (v.immovable, "immovable"),
            (v.nonportable, "nonportable"),
            (v.uniq, "uniq"),
        ] {
            if flag {
                emit(name, std::slice::from_ref(&id));
            }
        }
    }
    for (i, t) in f.tasks.iter().enumerate() {
        let id = s(&TaskId(u32::try_from(i).unwrap_or(0)));
        emit("task", std::slice::from_ref(&id));
        if t.kind == TaskKind::Fork {
            emit("fork_task", &[id]);
        }
    }
    for (p, m, i) in &f.call_mut {
        emit("call_mut", &[s(p), s(m), Arg::Int(i64::from(*i))]);
    }
    for (p, a, i) in &f.call_arg {
        emit("call_arg", &[s(p), s(a), Arg::Int(i64::from(*i))]);
    }
    if f.has_signature {
        emit("has_signature", &[]);
    }
    if f.library {
        emit("library", &[]);
    }
    for (i, h) in f.handlers.iter().enumerate() {
        let id = s(&HandlerId(u32::try_from(i).unwrap_or(0)));
        let e = s(&h.effect);
        emit("handler", &[id.clone(), e.clone()]);
        if h.is_std {
            emit("std_effect", &[e]);
        }
        if h.forwards {
            emit("forwards", &[id]);
        }
    }
}

/// Builds the input database of one function.
pub fn database(f: &FnFacts) -> Database {
    let mut db = Database::new();
    each_fact(f, &mut |rel, args| {
        let vals: Vec<Value> = args
            .iter()
            .map(|a| match a {
                Arg::Sym(t) => db.sym(t),
                Arg::Int(i) => Value::Int(*i),
            })
            .collect();
        db.insert(rel, vals);
    });
    db
}

/// Writes the input facts of one function in Datalog syntax.
pub fn facts_text(f: &FnFacts) -> String {
    let mut out = format!("// facts of `{}`\n", f.name);
    each_fact(f, &mut |rel, args| {
        let a: Vec<String> = args
            .iter()
            .map(|a| match a {
                Arg::Sym(t)
                    if t.chars().next().is_some_and(|c| c.is_ascii_lowercase())
                        && t.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') =>
                {
                    t.clone()
                }
                Arg::Sym(t) => format!("{t:?}"),
                Arg::Int(i) => i.to_string(),
            })
            .collect();
        let _ = writeln!(out, "{rel}({}).", a.join(", "));
    });
    out
}

/// Evaluates the spec on one function.
pub fn evaluate_spec(f: &FnFacts, provenance: bool) -> Result<Output, weft_datalog::Error> {
    evaluate(spec(), database(f), EvalOptions { provenance })
}

/// Returns the text of a symbol, without Datalog quotes.
fn raw(out: &Output, v: Value) -> String {
    let t = out.display_value(v);
    t.strip_prefix('"')
        .and_then(|x| x.strip_suffix('"'))
        .map_or_else(
            || t.clone(),
            |inner| inner.replace("\\\"", "\"").replace("\\\\", "\\"),
        )
}

fn parse_id(out: &Output, v: Value, prefix: char) -> Option<u32> {
    let text = raw(out, v);
    text.strip_prefix(prefix)?.parse().ok()
}

/// Reads one violation relation. Each tuple must parse.
fn read<T: Ord>(
    out: &Output,
    rel: &str,
    parse: impl Fn(&[Value]) -> Option<T>,
) -> Result<BTreeSet<T>, SpecError> {
    out.tuples(rel)
        .iter()
        .map(|t| parse(t).ok_or_else(|| SpecError::BadTuple(out.display_tuple(rel, t))))
        .collect()
}

/// Reads the violation relations from a spec result.
///
/// # Errors
///
/// Returns [`SpecError::BadTuple`] if a violation fact has a value that is not
/// an id of the facts. The result would hide a disagreement.
pub fn violations(out: &Output) -> Result<Violations, SpecError> {
    let n = |x| parse_id(out, x, 'n').map(NodeId);
    let var = |x| parse_id(out, x, 'v').map(VarId);
    let pl = |x| parse_id(out, x, 'p').map(PlaceId);
    let t = |x| parse_id(out, x, 't').map(TaskId);
    let vn = |tu: &[Value]| match *tu {
        [a, b] => Some((var(a)?, n(b)?)),
        _ => None,
    };
    let np = |tu: &[Value]| match *tu {
        [a, b] => Some((n(a)?, pl(b)?)),
        _ => None,
    };
    let tv = |tu: &[Value]| match *tu {
        [a, b] => Some((t(a)?, var(b)?)),
        _ => None,
    };
    Ok(Violations {
        error: read(out, "error", vn)?,
        use_after_move: read(out, "use_after_move", vn)?,
        moved_immovable: read(out, "moved_immovable", vn)?,
        unconsumed: read(out, "unconsumed", vn)?,
        overwritten: read(out, "overwritten", vn)?,
        abort_unhandled: read(out, "abort_unhandled", vn)?,
        live_across_multi: read(out, "live_across_multi", vn)?,
        unauthorized_mut: read(out, "unauthorized_mut", np)?,
        unauthorized_effect: read(out, "unauthorized_effect", |tu| match *tu {
            [a, e] => Some((n(a)?, raw(out, e))),
            _ => None,
        })?,
        shared_mutation: read(out, "shared_mutation", np)?,
        alias_conflict: read(out, "alias_conflict", |tu| match *tu {
            [a, m, p] => Some((n(a)?, pl(m)?, pl(p)?)),
            _ => None,
        })?,
        task_conflict: read(out, "task_conflict", |tu| match *tu {
            [a, b] => Some((t(a)?, n(b)?)),
            _ => None,
        })?,
        nonportable_capture: read(out, "nonportable_capture", tv)?,
        shared_mut_capture: read(out, "shared_mut_capture", tv)?,
        root_handler_in_lib: read(out, "root_handler_in_lib", |tu| match *tu {
            [h] => parse_id(out, h, 'h').map(HandlerId),
            _ => None,
        })?,
        stealable: read(out, "stealable", |tu| match *tu {
            [a] => t(a),
            _ => None,
        })?,
    })
}

/// Runs the spec and returns its violations.
///
/// # Errors
///
/// Returns the error of the Datalog engine, or a violation fact that does not
/// parse.
pub fn check_spec(f: &FnFacts) -> Result<Violations, SpecError> {
    violations(&evaluate_spec(f, false)?)
}

/// Renders a derivation with source names: `v1` becomes `first`, `p3` becomes
/// `world.entities[]`, and `n4` becomes `n4@line`.
pub fn render_derivation(d: &Derivation, f: &FnFacts, line_of: &dyn Fn(u32) -> usize) -> String {
    let mut out = String::new();
    render(d, f, line_of, &mut out);
    out
}

fn rename(text: &str, f: &FnFacts, line_of: &dyn Fn(u32) -> usize) -> String {
    let mut out = String::new();
    let mut word = String::new();
    let flush = |word: &mut String, out: &mut String| {
        let name = rename_word(word, f, line_of);
        out.push_str(&name);
        word.clear();
    };
    for ch in text.chars() {
        if ch.is_alphanumeric() || ch == '_' {
            word.push(ch);
        } else {
            flush(&mut word, &mut out);
            out.push(ch);
        }
    }
    flush(&mut word, &mut out);
    out
}

fn rename_word(w: &str, f: &FnFacts, line_of: &dyn Fn(u32) -> usize) -> String {
    let (head, rest) = w.split_at(w.chars().next().map_or(0, char::len_utf8));
    let Ok(i) = rest.parse::<usize>() else {
        return w.to_string();
    };
    match head {
        "v" if i < f.vars.len() => format!("`{}`", f.vars[i].name),
        "p" if i < f.places.len() => format!("`{}`", f.places[i].display),
        "n" if i < f.nodes.len() => format!(
            "{}@line{}",
            f.nodes[i].label.replace(' ', "_"),
            line_of(f.nodes[i].span.lo)
        ),
        _ => w.to_string(),
    }
}

/// The deepest indent of a rendered derivation, in levels. A deeper line
/// keeps this indent.
pub const MAX_INDENT: usize = 32;

/// The renderer folds a chain that has more steps than this.
pub const CHAIN_FOLD: usize = 8;

/// The steps that the renderer shows at each end of a folded chain.
pub const CHAIN_KEEP: usize = 3;

/// What the renderer does at the next step of a chain.
#[derive(Clone, Copy)]
enum Chain<'a> {
    /// The node starts a chain: measure it first.
    Start,
    /// Show each step: the chain is short, or this is its end.
    Show,
    /// Show `left` more steps, then skip `skipped` steps to `tail`.
    Fold {
        left: usize,
        skipped: usize,
        tail: &'a Derivation,
    },
}

/// One unit of work of the renderer.
enum Item<'a> {
    /// A derivation node at a depth.
    Node(&'a Derivation, usize, Chain<'a>),
    /// A line of text at a depth.
    Line(usize, String),
}

/// Returns the component of each relation of the spec, as an index into
/// [`Program::components`]. Two relations have the same component when each
/// depends on the other, for example `live_in` and `live_out`.
fn spec_components() -> &'static BTreeMap<String, usize> {
    static COMPONENTS: OnceLock<BTreeMap<String, usize>> = OnceLock::new();
    COMPONENTS.get_or_init(|| {
        let comps = spec().components().unwrap_or_default();
        let mut map = BTreeMap::new();
        for (i, comp) in comps.into_iter().enumerate() {
            for relation in comp {
                map.insert(relation, i);
            }
        }
        map
    })
}

/// Returns true if a chain can go from a fact of relation `a` to a premise
/// of relation `b`: the relations are equal, or they depend on each other in
/// the spec.
fn same_chain(a: &str, b: &str) -> bool {
    let comps = spec_components();
    a == b || comps.get(a).is_some_and(|ca| comps.get(b) == Some(ca))
}

/// Returns the next step of the chain of `d`: its first derived premise of
/// the same relation, or of a relation that depends on the relation of `d`.
fn chain_child(d: &Derivation) -> Option<&Derivation> {
    d.premises().iter().find_map(|p| match p {
        Premise::Derived(c) if same_chain(&d.fact.relation, &c.fact.relation) => Some(c),
        _ => None,
    })
}

/// Names the relations of the chain steps from `from` up to `to`, each one
/// time, in the order of the chain. For example: `` `invalid` ``.
fn chain_relations(from: &Derivation, to: &Derivation) -> String {
    let mut names: Vec<&str> = Vec::new();
    let mut cur = Some(from);
    while let Some(d) = cur.filter(|d| !std::ptr::eq(*d, to)) {
        if !names.contains(&d.fact.relation.as_str()) {
            names.push(&d.fact.relation);
        }
        cur = chain_child(d);
    }
    let quoted: Vec<String> = names.iter().map(|n| format!("`{n}`")).collect();
    quoted.join(", ")
}

/// Measures the chain that starts at `d`, and decides if the renderer folds it.
fn measure(d: &Derivation) -> Chain<'_> {
    let mut steps = vec![d];
    let mut cur = d;
    while let Some(c) = chain_child(cur) {
        steps.push(c);
        cur = c;
    }
    let n = steps.len();
    match steps.get(n.saturating_sub(CHAIN_KEEP)) {
        Some(&tail) if n > CHAIN_FOLD => Chain::Fold {
            left: CHAIN_KEEP - 1,
            skipped: n - 2 * CHAIN_KEEP,
            tail,
        },
        _ => Chain::Show,
    }
}

/// Writes the indent of one line.
fn indent(out: &mut String, depth: usize) {
    let _ = write!(out, "{:w$}", "", w = 2 * depth.min(MAX_INDENT));
}

/// Writes the tree with a stack, not with recursion, so a deep derivation does
/// not overflow the stack. Each line is one node. A child is two spaces deeper
/// than its parent, up to [`MAX_INDENT`] levels.
///
/// A chain is a path of derived premises whose relations depend on each
/// other, for example `invalid` after `invalid`, or `live_out` and `live_in`
/// in turn. The renderer folds a chain that has more than [`CHAIN_FOLD`]
/// steps. It shows the first and the last [`CHAIN_KEEP`] steps, and one line
/// for the steps between them.
fn render(d: &Derivation, f: &FnFacts, line_of: &dyn Fn(u32) -> usize, out: &mut String) {
    let mut stack = vec![Item::Node(d, 0, Chain::Start)];
    while let Some(item) = stack.pop() {
        let (d, depth, chain) = match item {
            Item::Line(depth, text) => {
                indent(out, depth);
                out.push_str(&text);
                out.push('\n');
                continue;
            }
            Item::Node(d, depth, chain) => (d, depth, chain),
        };
        indent(out, depth);
        let fact = rename(&d.fact.text, f, line_of);
        let (text, premises) = match &d.reason {
            Reason::Input => {
                let _ = writeln!(out, "{fact}  [fact]");
                continue;
            }
            Reason::Fact { .. } => {
                let _ = writeln!(out, "{fact}  [spec fact]");
                continue;
            }
            Reason::Rule { text, premises, .. } => (text, premises),
        };
        let _ = writeln!(out, "{fact}  by  {text}");
        let chain = match chain {
            Chain::Start => measure(d),
            c => c,
        };
        let next = chain_child(d);
        for p in premises.iter().rev() {
            let item = match p {
                Premise::Derived(c) if next.is_some_and(|n| std::ptr::eq(n, c)) => match chain {
                    Chain::Fold {
                        left: 0,
                        skipped,
                        tail,
                    } => {
                        stack.push(Item::Node(tail, depth + 2, Chain::Show));
                        Item::Line(
                            depth + 1,
                            format!("... {skipped} more {} steps ...", chain_relations(c, tail)),
                        )
                    }
                    Chain::Fold {
                        left,
                        skipped,
                        tail,
                    } => Item::Node(
                        c,
                        depth + 1,
                        Chain::Fold {
                            left: left - 1,
                            skipped,
                            tail,
                        },
                    ),
                    Chain::Start | Chain::Show => Item::Node(c, depth + 1, Chain::Show),
                },
                Premise::Derived(c) => Item::Node(c, depth + 1, Chain::Start),
                Premise::Absent { text, .. } => Item::Line(
                    depth + 1,
                    format!("not {}  [absent]", rename(text, f, line_of)),
                ),
                Premise::Holds { text, .. } => {
                    Item::Line(depth + 1, format!("{}  [holds]", rename(text, f, line_of)))
                }
            };
            stack.push(item);
        }
    }
}

/// The violation relations of the spec, in report order.
pub const VIOLATION_RELATIONS: [&str; 15] = [
    "error",
    "use_after_move",
    "moved_immovable",
    "unconsumed",
    "overwritten",
    "abort_unhandled",
    "live_across_multi",
    "unauthorized_mut",
    "unauthorized_effect",
    "shared_mutation",
    "alias_conflict",
    "task_conflict",
    "nonportable_capture",
    "shared_mut_capture",
    "root_handler_in_lib",
];

/// One explained violation: the fact and its derivation tree.
#[derive(Clone, Debug)]
pub struct Explained {
    /// The violation relation.
    pub relation: String,
    /// The derived fact, with source names.
    pub fact: String,
    /// The derivation tree, with source names.
    pub tree: String,
    /// The derivation as JSON, with raw ids.
    pub json: String,
}

/// Runs the spec with provenance and explains every violation of one function.
pub fn explain(
    f: &FnFacts,
    line_of: &dyn Fn(u32) -> usize,
) -> Result<Vec<Explained>, weft_datalog::Error> {
    let out = evaluate_spec(f, true)?;
    let mut v = Vec::new();
    for rel in VIOLATION_RELATIONS {
        for t in out.tuples(rel) {
            if let Some(d) = out.explain(rel, &t) {
                v.push(Explained {
                    relation: rel.to_string(),
                    fact: rename(&out.display_tuple(rel, &t), f, line_of),
                    tree: render_derivation(&d, f, line_of),
                    json: d.to_json(out.interner()),
                });
            }
        }
    }
    Ok(v)
}
