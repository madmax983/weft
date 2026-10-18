//! Runs the Datalog specification (`spec/weft.dl`) on the facts.
//!
//! This is the reference semantics. The production checker must give the same
//! [`Violations`].

use std::collections::BTreeSet;
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

/// Builds the input database of one function.
pub fn database(f: &FnFacts) -> Database {
    let mut db = Database::new();
    macro_rules! s {
        ($x:expr) => {
            db.sym(&$x.to_string())
        };
    }
    for (i, p) in f.places.iter().enumerate() {
        let id = PlaceId(u32::try_from(i).unwrap_or(0));
        let v = s!(id);
        db.insert("place", [v]);
        if let Some(q) = p.parent {
            let qv = s!(q);
            db.insert("parent", [v, qv]);
        }
        if p.steps.last().is_some_and(|s| s.unstable) {
            db.insert("unstable", [v]);
        }
        if f.param_rooted(id) {
            db.insert("param_rooted", [v]);
        }
    }
    // Last-step relations between places of the same root and depth.
    for (i, p) in f.places.iter().enumerate() {
        let Some(a) = p.steps.last() else { continue };
        for (j, q) in f.places.iter().enumerate() {
            if p.root != q.root || p.steps.len() != q.steps.len() {
                continue;
            }
            let Some(b) = q.steps.last() else { continue };
            let pv = s!(PlaceId(u32::try_from(i).unwrap_or(0)));
            let qv = s!(PlaceId(u32::try_from(j).unwrap_or(0)));
            if places::step_alias(a, b) {
                db.insert("step_alias", [pv, qv]);
            }
            if places::step_within(a, b) {
                db.insert("step_within", [pv, qv]);
            }
        }
    }
    for (a, b) in &f.cfg_edge {
        let x = [s!(a), s!(b)];
        db.insert("cfg_edge", x);
    }
    macro_rules! rel2 {
        ($name:literal, $v:expr) => {
            for (a, b) in &$v {
                let x = [s!(a), s!(b)];
                db.insert($name, x);
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
    rel2!("spawned_at", f.spawned_at);
    rel2!("joined_at", f.joined_at);
    rel2!("task_reads", f.task_reads);
    rel2!("task_writes", f.task_writes);
    rel2!("captures", f.captures);
    rel2!("mut_through", f.mut_through);
    for (p, e) in &f.escapes_at {
        let x = [s!(p), s!(e)];
        db.insert("escapes_at", x);
    }
    for n in &f.may_abort {
        let x = [s!(n)];
        db.insert("may_abort", x);
    }
    for n in &f.multi_at {
        let x = [s!(n)];
        db.insert("multi_at", x);
    }
    for d in &f.declared_mut {
        let x = [s!(d)];
        db.insert("declared_mut", x);
    }
    for e in &f.declared_effect {
        let x = [s!(e)];
        db.insert("declared_effect", x);
    }
    for sr in &f.shared_root {
        let x = [s!(sr)];
        db.insert("shared_root", x);
    }
    for (i, v) in f.vars.iter().enumerate() {
        let id = s!(VarId(u32::try_from(i).unwrap_or(0)));
        for (flag, name) in [
            (v.linear, "linear"),
            (v.has_on_abort, "has_on_abort"),
            (v.once, "once_var"),
            (v.immovable, "immovable"),
            (v.nonportable, "nonportable"),
            (v.uniq, "uniq"),
        ] {
            if flag {
                db.insert(name, [id]);
            }
        }
    }
    for (i, t) in f.tasks.iter().enumerate() {
        let id = s!(TaskId(u32::try_from(i).unwrap_or(0)));
        db.insert("task", [id]);
        if t.kind == TaskKind::Fork {
            db.insert("fork_task", [id]);
        }
    }
    for (p, m, i) in &f.call_mut {
        let x = [s!(p), s!(m), Value::Int(i64::from(*i))];
        db.insert("call_mut", x);
    }
    for (p, a, i) in &f.call_arg {
        let x = [s!(p), s!(a), Value::Int(i64::from(*i))];
        db.insert("call_arg", x);
    }
    if f.has_signature {
        db.insert("has_signature", [] as [Value; 0]);
    }
    if f.library {
        db.insert("library", [] as [Value; 0]);
    }
    for (i, h) in f.handlers.iter().enumerate() {
        let id = s!(HandlerId(u32::try_from(i).unwrap_or(0)));
        let e = s!(h.effect);
        db.insert("handler", [id, e]);
        if h.is_std {
            db.insert("std_effect", [e]);
        }
        if h.forwards {
            db.insert("forwards", [id]);
        }
    }
    db
}

/// Evaluates the spec on one function.
pub fn evaluate_spec(f: &FnFacts, provenance: bool) -> Result<Output, weft_datalog::Error> {
    evaluate(spec(), database(f), EvalOptions { provenance })
}

/// Returns the text of a symbol, without Datalog quotes.
fn raw(out: &Output, v: Value) -> String {
    let t = out.display_value(v);
    match t.strip_prefix('"').and_then(|x| x.strip_suffix('"')) {
        Some(inner) => inner.replace("\\\"", "\"").replace("\\\\", "\\"),
        None => t,
    }
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
        Reason::Input => out.push_str(&format!("{pad}{fact}  [fact]\n")),
        Reason::Fact { .. } => out.push_str(&format!("{pad}{fact}  [spec fact]\n")),
        Reason::Rule { text, premises, .. } => {
            out.push_str(&format!("{pad}{fact}  by  {text}\n"));
            for p in premises {
                match p {
                    Premise::Derived(c) => render(c, f, line_of, depth + 1, out),
                    Premise::Absent { text, .. } => {
                        out.push_str(&format!(
                            "{pad}  not {}  [absent]\n",
                            rename(text, f, line_of)
                        ));
                    }
                    Premise::Holds { text, .. } => {
                        out.push_str(&format!("{pad}  {}  [holds]\n", rename(text, f, line_of)));
                    }
                }
            }
        }
    }
}
