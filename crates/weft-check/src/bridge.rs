//! Runs the Datalog specification (`spec/weft.dl`) on the facts.
//!
//! This is the reference semantics. The production checker must give the same
//! [`Violations`].

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::sync::OnceLock;

use weft_datalog::{
    evaluate, parse_program_named, Database, Derivation, EvalOptions, Output, Premise, Program,
    Reason, Value,
};
use weft_facts::{FnFacts, HandlerId, NodeId, PlaceId, TaskId, TaskKind, VarId, Violations};
use weft_verified::places;

/// The source of the specification.
pub const SPEC_SRC: &str = include_str!("../../../spec/weft.dl");

/// Returns the parsed specification. It is parsed once.
pub fn spec() -> &'static Program {
    static SPEC: OnceLock<Program> = OnceLock::new();
    SPEC.get_or_init(|| match parse_program_named("spec/weft.dl", SPEC_SRC) {
        Ok(p) => p,
        Err(e) => panic!("spec/weft.dl does not parse: {e}"),
    })
}

/// One argument of an input fact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Arg {
    /// A symbol, such as `n3` or `Log`.
    Sym(String),
    /// An integer.
    Int(i64),
}

/// Calls `emit` once for each input fact of one function.
#[allow(clippy::too_many_lines)]
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
    // Last-step relations between places of the same root and depth.
    let mut groups: std::collections::BTreeMap<(u32, usize), Vec<usize>> =
        std::collections::BTreeMap::new();
    for (i, p) in f.places.iter().enumerate() {
        if !p.steps.is_empty() {
            groups.entry((p.root.0, p.steps.len())).or_default().push(i);
        }
    }
    for group in groups.values() {
        for &i in group {
            let Some(a) = f.places[i].steps.last() else {
                continue;
            };
            for &j in group {
                let Some(b) = f.places[j].steps.last() else {
                    continue;
                };
                let pv = s(&PlaceId(u32::try_from(i).unwrap_or(0)));
                let qv = s(&PlaceId(u32::try_from(j).unwrap_or(0)));
                if places::step_alias(a, b) {
                    emit("step_alias", &[pv.clone(), qv.clone()]);
                }
                if places::step_within(a, b) {
                    emit("step_within", &[pv, qv]);
                }
            }
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
    for c in &f.clause_multi {
        emit("clause_multi", &[s(c)]);
    }
    for c in &f.body_multi {
        emit("body_multi", &[s(c)]);
    }
    rel2!("resumes_at", f.resumes_at);
    for (h, e) in &f.clause_performs {
        emit("clause_performs", &[s(h), s(e)]);
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

/// Reads the violation relations from a spec result.
pub fn violations(out: &Output) -> Violations {
    let mut v = Violations::default();
    let n = |x| parse_id(out, x, 'n').map(NodeId);
    let var = |x| parse_id(out, x, 'v').map(VarId);
    let pl = |x| parse_id(out, x, 'p').map(PlaceId);
    let t = |x| parse_id(out, x, 't').map(TaskId);
    let pairs = |rel: &str,
                 a: &dyn Fn(Value) -> Option<u32>,
                 b: &dyn Fn(Value) -> Option<u32>|
     -> BTreeSet<(u32, u32)> {
        out.tuples(rel)
            .iter()
            .filter_map(|t| Some((a(t[0])?, b(t[1])?)))
            .collect()
    };
    let vn = |rel: &str| -> BTreeSet<(VarId, NodeId)> {
        out.tuples(rel)
            .iter()
            .filter_map(|tu| Some((var(tu[0])?, n(tu[1])?)))
            .collect()
    };
    v.error = vn("error");
    v.use_after_move = vn("use_after_move");
    v.moved_immovable = vn("moved_immovable");
    v.unconsumed = vn("unconsumed");
    v.overwritten = vn("overwritten");
    v.abort_unhandled = vn("abort_unhandled");
    v.live_across_multi = vn("live_across_multi");
    v.unauthorized_mut = out
        .tuples("unauthorized_mut")
        .iter()
        .filter_map(|tu| Some((n(tu[0])?, pl(tu[1])?)))
        .collect();
    v.unauthorized_effect = out
        .tuples("unauthorized_effect")
        .iter()
        .filter_map(|tu| Some((n(tu[0])?, raw(out, tu[1]))))
        .collect();
    v.shared_mutation = out
        .tuples("shared_mutation")
        .iter()
        .filter_map(|tu| Some((n(tu[0])?, pl(tu[1])?)))
        .collect();
    v.alias_conflict = out
        .tuples("alias_conflict")
        .iter()
        .filter_map(|tu| Some((n(tu[0])?, pl(tu[1])?, pl(tu[2])?)))
        .collect();
    v.task_conflict = out
        .tuples("task_conflict")
        .iter()
        .filter_map(|tu| Some((t(tu[0])?, n(tu[1])?)))
        .collect();
    v.nonportable_capture = out
        .tuples("nonportable_capture")
        .iter()
        .filter_map(|tu| Some((t(tu[0])?, var(tu[1])?)))
        .collect();
    v.shared_mut_capture = out
        .tuples("shared_mut_capture")
        .iter()
        .filter_map(|tu| Some((t(tu[0])?, var(tu[1])?)))
        .collect();
    v.root_handler_in_lib = out
        .tuples("root_handler_in_lib")
        .iter()
        .filter_map(|tu| parse_id(out, tu[0], 'h').map(HandlerId))
        .collect();
    v.stealable = out
        .tuples("stealable")
        .iter()
        .filter_map(|tu| t(tu[0]))
        .collect();
    let _ = pairs;
    v
}

/// Runs the spec and returns its violations.
pub fn check_spec(f: &FnFacts) -> Result<Violations, weft_datalog::Error> {
    Ok(violations(&evaluate_spec(f, false)?))
}

/// Renders a derivation with source names: `v1` becomes `first`, `p3` becomes
/// `world.entities[]`, and `n4` becomes `n4@line`.
pub fn render_derivation(d: &Derivation, f: &FnFacts, line_of: &dyn Fn(u32) -> usize) -> String {
    let mut out = String::new();
    render(d, f, line_of, 0, &mut out);
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

fn render(
    d: &Derivation,
    f: &FnFacts,
    line_of: &dyn Fn(u32) -> usize,
    depth: usize,
    out: &mut String,
) {
    let pad = "  ".repeat(depth);
    let fact = rename(&d.fact.text, f, line_of);
    match &d.reason {
        Reason::Input => {
            let _ = writeln!(out, "{pad}{fact}  [fact]");
        }
        Reason::Fact { .. } => {
            let _ = writeln!(out, "{pad}{fact}  [spec fact]");
        }
        Reason::Rule { text, premises, .. } => {
            let _ = writeln!(out, "{pad}{fact}  by  {text}");
            for p in premises {
                match p {
                    Premise::Derived(c) => render(c, f, line_of, depth + 1, out),
                    Premise::Absent { text, .. } => {
                        let _ = writeln!(out, "{pad}  not {}  [absent]", rename(text, f, line_of));
                    }
                    Premise::Holds { text, .. } => {
                        let _ = writeln!(out, "{pad}  {}  [holds]", rename(text, f, line_of));
                    }
                }
            }
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
