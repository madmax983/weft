//! Test D1 (`docs/ir.md` 8.5, plan stage I5): the exports of the old lowering
//! against the IR.
//!
//! The AST engine of the interpreter reads three exports of semantic analysis
//! (`FnFacts`): the captures that a closure takes by value (`by_value`), the
//! order of the arguments of some calls with named arguments (`arg_order`) and
//! the integer type of each arithmetic result (`int_ops`). The IR engine reads
//! the same decisions from the IR. For each program of tier 1 (the files of
//! `tests/gate/manifest-tier1.tsv`; the one package of tier 1 is not in this
//! test), the test checks that:
//!
//! - the `ByMove` captures of each closure of the IR are the captures of
//!   `by_value` for the closure. A `Kont` capture of a `once` continuation
//!   (operand `move`) is a move too. Each other capture of the IR is `Kept`,
//!   `ByRef`, `Cap` or `Kont`: the AST engine keeps the cell of the variable,
//!   and rule CAPTURE (`docs/ir.md` 5.1.7) makes a borrowed capture `ByRef`.
//!   That difference is a difference of the engines (`weft-gate engines`,
//!   class `capture`), not of the exports. One more difference is expected
//!   (class `closure-copy`): a capture that holds a function value and that
//!   the closure body copies. The old analysis moves it (a read of a function
//!   value is a move there), the IR copies the function value (B12b: a
//!   function value is plain data in the IR). [`CLOSURE_COPY`] lists the
//!   programs of tier 1 with such a capture;
//! - the arguments of each IR call with an `arg_order` entry are evaluated in
//!   the order of `arg_order`;
//! - the integer type of each `Binary` and `Unary` of the IR is the type of
//!   `int_ops` at its expression, and each `int_ops` entry has an IR operator.
//!
//! Only the bodies that the builder lowers count. One pass analyzes each
//! program; the three tests read its result. A program whose analysis takes
//! more than [`LIMIT`] is skipped (at most 1 %).
//!
//! To look at a failure: `D1_FILES=a.wf,b.wf` runs the test on these files
//! only, and `D1_DUMP=DIR` writes each list of mismatches and the slowest
//! programs to `DIR`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, OnceLock};
use std::time::Duration;

use weft_ir::{
    AggKind, BodyId, Callee, CaptureMode, LocalId, LocalKind, Operand, Place, Program, Proj,
    Rvalue, StmtKind, TermKind, TyTable,
};
use weft_sema::irbuild::{self, Built, Outcome};
use weft_sema::{analyze_source, Analysis, Options};

/// The repository.
fn repo() -> PathBuf {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    std::fs::canonicalize(&dir).unwrap_or(dir)
}

/// The files of tier 1: the rows of the manifest whose mode is `file`.
fn tier1_files() -> Vec<String> {
    if let Some(list) = std::env::var_os("D1_FILES") {
        return list
            .to_string_lossy()
            .split(',')
            .map(ToString::to_string)
            .collect();
    }
    let file = repo().join("tests/gate/manifest-tier1.tsv");
    let text =
        std::fs::read_to_string(&file).unwrap_or_else(|e| panic!("read {}: {e}", file.display()));
    let mut out = Vec::new();
    for line in text.lines().skip(1) {
        let cols: Vec<&str> = line.split('\t').collect();
        if let [_, path, _, "file", ..] = cols.as_slice() {
            out.push((*path).to_string());
        }
    }
    out
}

/// The time limit for the analysis and the check of one program. The old
/// analysis of a few programs of tier 1 (the closure chains of finding Q3)
/// takes minutes in a debug build; the test skips them and lists them.
const LIMIT: Duration = Duration::from_secs(60);

/// A key of an export: the unit and the span of the expression.
type Key = (usize, u32, u32);

/// The mismatches of one program, as lines of text.
#[derive(Default)]
struct Found {
    by_value: Vec<String>,
    /// The `by_value` captures that the IR does not move because the closure
    /// body copies a function value out of them (expected).
    fn_copy: Vec<String>,
    /// The programs whose analysis takes more than [`LIMIT`].
    skipped: Vec<String>,
    /// The time of each program in milliseconds (for `D1_DUMP`).
    times: Vec<(u128, String)>,
    arg_order: Vec<String>,
    int_ops: Vec<String>,
}

/// The unit of each body of the IR: the unit of its top body.
fn body_units(a: &Analysis, b: &Built) -> Vec<Option<(usize, usize)>> {
    let p = &b.program;
    let mut top: BTreeMap<BodyId, usize> = BTreeMap::new();
    for (i, e) in b.entries.iter().enumerate() {
        if let Outcome::Built(id) = e.outcome {
            top.insert(id, i);
        }
    }
    let mut out = vec![None; p.bodies.len()];
    for (i, slot) in out.iter_mut().enumerate() {
        let mut at = BodyId(u32::try_from(i).unwrap_or(u32::MAX));
        loop {
            if let Some(&k) = top.get(&at) {
                let unit = a.bodies.get(k).map_or(0, |x| x.unit);
                *slot = Some((k, unit));
                break;
            }
            match p.bodies.get(at.index()).and_then(|x| x.parent) {
                Some(parent) => at = parent,
                None => break,
            }
        }
    }
    out
}

/// The declaration of the variable that `place` of body `body` names: a user
/// local or a parameter, through upvar locals and the captures of closure
/// bodies.
fn var_decl<'p>(p: &'p Program, body: BodyId, place: &Place) -> Option<&'p weft_ir::LocalDecl> {
    let b = p.bodies.get(body.index())?;
    let decl = b.locals.get(place.local.index())?;
    match decl.kind {
        LocalKind::Upvar(l) => {
            let parent = b.parent?;
            var_decl(
                p,
                parent,
                &Place {
                    local: l,
                    proj: place.proj.clone(),
                },
            )
        }
        LocalKind::Env => {
            let Some(Proj::Field(k)) = place.proj.first() else {
                return None;
            };
            let c = p.closures.iter().find(|c| c.body == body)?;
            let cap = c.captures.get(k.index())?;
            var_decl(p, c.maker, &cap.source)
        }
        _ => Some(decl),
    }
}

/// The name of the variable that `place` of body `body` names.
fn var_name(p: &Program, body: BodyId, place: &Place) -> Option<String> {
    var_decl(p, body, place).and_then(|d| d.name.clone())
}

/// The captures of the closure aggregates of the IR, by the key of the
/// aggregate.
#[derive(Default)]
struct IrCaptures {
    /// The names of the captures that move into the closure: `ByMove`, and a
    /// `Kont` capture of a `once` continuation (its operand is a `move`).
    moved: BTreeMap<Key, Vec<String>>,
    /// The names of the captures that hold a function value and that the
    /// closure body copies (B12b: a function value is plain data in the IR,
    /// so a read of it is a copy, not a move).
    fn_copies: BTreeMap<Key, BTreeSet<String>>,
    /// The mode of each capture that does not move.
    others: Vec<(Key, CaptureMode)>,
}

/// The operands of the statements and of the calls of body `b`.
fn operands(b: &weft_ir::Body) -> Vec<&Operand> {
    let mut out = Vec::new();
    for blk in &b.blocks {
        for s in &blk.stmts {
            match &s.kind {
                StmtKind::Assign(_, rv) => match rv {
                    Rvalue::Use(o) | Rvalue::Unary(_, _, o) => out.push(o),
                    Rvalue::Binary(_, _, x, y) => out.extend([x, y]),
                    Rvalue::Aggregate(_, ops) | Rvalue::Concat(ops) => out.extend(ops),
                    _ => {}
                },
                StmtKind::Print(ops) => out.extend(ops),
                _ => {}
            }
        }
        if let TermKind::Call { callee, args, .. } = &blk.term.kind {
            if let Callee::Value(o) = callee {
                out.push(o);
            }
            out.extend(args);
        }
    }
    out
}

/// The captures (field indexes of the environment) that body `b` of a
/// closure copies: a `copy` of a place at or below `env.k`.
fn copied_captures(b: &weft_ir::Body) -> BTreeSet<usize> {
    let Some(&env) = b.params.first() else {
        return BTreeSet::new();
    };
    operands(b)
        .into_iter()
        .filter_map(|o| match o {
            Operand::Copy(p) if p.local == env => match p.proj.first() {
                Some(Proj::Field(k)) => Some(k.index()),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// The captures of each closure aggregate of the IR.
fn ir_captures(p: &Program, tys: &TyTable, units: &[Option<(usize, usize)>]) -> IrCaptures {
    let mut out = IrCaptures::default();
    for (bi, b) in p.bodies.iter().enumerate() {
        let Some(Some((_, unit))) = units.get(bi) else {
            continue;
        };
        for blk in &b.blocks {
            for s in &blk.stmts {
                let StmtKind::Assign(_, Rvalue::Aggregate(AggKind::Closure(c), ops)) = &s.kind
                else {
                    continue;
                };
                let Some(decl) = p.closures.get(c.index()) else {
                    continue;
                };
                let key = (*unit, s.origin.span.lo, s.origin.span.hi);
                let copies = p
                    .bodies
                    .get(decl.body.index())
                    .map(copied_captures)
                    .unwrap_or_default();
                let mut names = Vec::new();
                for (k, cap) in decl.captures.iter().enumerate() {
                    let name =
                        || var_name(p, decl.maker, &cap.source).unwrap_or_else(|| "?".into());
                    let moves_kont = cap.mode == CaptureMode::Kont
                        && matches!(ops.get(k), Some(Operand::Move(_)));
                    if cap.mode == CaptureMode::ByMove || moves_kont {
                        names.push(name());
                    } else {
                        out.others.push((key, cap.mode));
                    }
                    let holds_fn =
                        var_decl(p, decl.maker, &cap.source).is_some_and(|d| tys.mentions_fn(d.ty));
                    if copies.contains(&k) && holds_fn {
                        out.fn_copies.entry(key).or_default().insert(name());
                    }
                }
                names.sort();
                if !names.is_empty() {
                    out.moved.insert(key, names);
                }
            }
        }
    }
    out
}

/// The first write of a temporary: the block, the statement, and the start
/// of the expression that gives the value.
type Def = (usize, usize, u32);

/// The first write of each whole temporary of body `b`.
fn temp_defs(b: &weft_ir::Body) -> BTreeMap<LocalId, Def> {
    let mut out = BTreeMap::new();
    let mut note = |dest: &Place, at: Def| {
        let temp = b
            .locals
            .get(dest.local.index())
            .is_some_and(|d| matches!(d.kind, LocalKind::Temp(_)));
        if temp && dest.proj.is_empty() {
            out.entry(dest.local).or_insert(at);
        }
    };
    for (bi, blk) in b.blocks.iter().enumerate() {
        for (si, s) in blk.stmts.iter().enumerate() {
            if let StmtKind::Assign(dest, _) = &s.kind {
                note(dest, (bi, si, s.origin.span.lo));
            }
        }
        if let Some(dest) = term_dest(&blk.term.kind) {
            note(dest, (bi, blk.stmts.len(), blk.term.origin.span.lo));
        }
    }
    out
}

/// The first write of the whole temporary that `op` reads, if it reads one.
fn temp_def(defs: &BTreeMap<LocalId, Def>, op: &Operand) -> Option<Def> {
    let place = op.place()?;
    if !place.proj.is_empty() {
        return None;
    }
    defs.get(&place.local).copied()
}

/// The destination of a terminator that writes one.
const fn term_dest(t: &TermKind) -> Option<&Place> {
    match t {
        TermKind::Call { dest, .. }
        | TermKind::Perform { dest, .. }
        | TermKind::Resume { dest, .. }
        | TermKind::Handle { dest, .. }
        | TermKind::Scope { dest, .. }
        | TermKind::Join { dest, .. }
        | TermKind::Fork { dest, .. } => Some(dest),
        _ => None,
    }
}

/// Checks the order of the arguments of each IR call with an `arg_order` entry.
/// Gives the keys of the calls that it found, and the mismatches.
fn check_arg_order(
    p: &Program,
    units: &[Option<(usize, usize)>],
    orders: &BTreeMap<Key, Vec<Option<u32>>>,
    out: &mut Vec<String>,
) -> BTreeSet<Key> {
    let mut seen = BTreeSet::new();
    for (bi, b) in p.bodies.iter().enumerate() {
        let Some(Some((_, unit))) = units.get(bi) else {
            continue;
        };
        let mut defs = None;
        for blk in &b.blocks {
            let TermKind::Call { args, .. } = &blk.term.kind else {
                continue;
            };
            let o = &blk.term.origin.span;
            let key = (*unit, o.lo, o.hi);
            let Some(order) = orders.get(&key) else {
                continue;
            };
            seen.insert(key);
            let defs = defs.get_or_insert_with(|| temp_defs(b));
            let Some(first) = args.len().checked_sub(order.len()) else {
                out.push(format!(
                    "call at {key:?}: {} IR arguments, {} in arg_order",
                    args.len(),
                    order.len()
                ));
                continue;
            };
            // (parameter, written index, first write) of each argument
            // that a temporary holds.
            let held: Vec<(usize, u32, Def)> = order
                .iter()
                .zip(args.iter().skip(first))
                .enumerate()
                .filter_map(|(i, (k, a))| Some((i, (*k)?, temp_def(defs, a)?)))
                .collect();
            for x in &held {
                for y in held.iter().filter(|y| y.0 > x.0) {
                    if (x.2 .0, x.2 .1) > (y.2 .0, y.2 .1) {
                        out.push(format!(
                            "call at {key:?}: parameter {} runs before parameter {}",
                            y.0, x.0
                        ));
                    }
                    if (x.1 < y.1) != (x.2 .2 < y.2 .2) {
                        out.push(format!(
                            "call at {key:?}: parameters {} and {} do not get the arguments {} and {} (arg_order {order:?})",
                            x.0, y.0, x.1, y.1
                        ));
                    }
                }
            }
        }
    }
    seen
}

/// The integer type of each operator of the IR, by the span of its statement.
fn ir_int_ops(p: &Program, units: &[Option<(usize, usize)>]) -> BTreeMap<Key, BTreeSet<String>> {
    let mut out: BTreeMap<Key, BTreeSet<String>> = BTreeMap::new();
    for (bi, b) in p.bodies.iter().enumerate() {
        let Some(Some((_, unit))) = units.get(bi) else {
            continue;
        };
        for blk in &b.blocks {
            for s in &blk.stmts {
                let it = match &s.kind {
                    StmtKind::Assign(
                        _,
                        Rvalue::Binary(_, Some(it), _, _) | Rvalue::Unary(_, Some(it), _),
                    ) => *it,
                    _ => continue,
                };
                let o = &s.origin.span;
                out.entry((*unit, o.lo, o.hi))
                    .or_default()
                    .insert(it.name().to_string());
            }
        }
    }
    out
}

/// Runs D1 on one program.
fn d1(path: &str, a: &Analysis) -> Found {
    let built = irbuild::build(a);
    let p = &built.program;
    let units = body_units(a, &built);
    let lowered: BTreeSet<usize> = units.iter().flatten().map(|(k, _)| *k).collect();
    let mut found = Found::default();

    // by_value against the ByMove captures.
    let mut by_value: BTreeMap<Key, Vec<String>> = BTreeMap::new();
    let mut orders: BTreeMap<Key, Vec<Option<u32>>> = BTreeMap::new();
    let mut int_ops: BTreeMap<Key, String> = BTreeMap::new();
    for (k, b) in a.bodies.iter().enumerate() {
        if !lowered.contains(&k) {
            continue;
        }
        for (span, v) in &b.facts.by_value {
            by_value
                .entry((b.unit, span.lo, span.hi))
                .or_default()
                .push(b.facts.var(*v).name.clone());
        }
        for (span, o) in &b.facts.arg_order {
            orders.insert((b.unit, span.lo, span.hi), o.clone());
        }
        for (span, name) in &b.facts.int_ops {
            int_ops.insert((b.unit, span.lo, span.hi), name.clone());
        }
    }
    for v in by_value.values_mut() {
        v.sort();
    }
    let caps = ir_captures(p, &built.tys, &units);
    let keys: BTreeSet<&Key> = by_value.keys().chain(caps.moved.keys()).collect();
    for key in keys {
        let old = by_value.get(key).cloned().unwrap_or_default();
        let mut ir = caps.moved.get(key).cloned().unwrap_or_default();
        let copies = caps.fn_copies.get(key);
        for name in &old {
            if let Some(i) = ir.iter().position(|n| n == name) {
                ir.remove(i);
            } else if copies.is_some_and(|c| c.contains(name)) {
                found.fn_copy.push(format!(
                    "{path}: closure at {key:?}: `{name}` (it holds a function value, and the body copies it)"
                ));
            } else {
                found.by_value.push(format!(
                    "{path}: closure at {key:?}: `{name}` is in by_value, but it is not ByMove in the IR"
                ));
            }
        }
        for name in ir {
            found.by_value.push(format!(
                "{path}: closure at {key:?}: `{name}` is ByMove in the IR, but it is not in by_value"
            ));
        }
    }
    for (key, mode) in caps.others {
        if !matches!(
            mode,
            CaptureMode::Kept | CaptureMode::ByRef | CaptureMode::Cap | CaptureMode::Kont
        ) {
            found
                .by_value
                .push(format!("{path}: closure at {key:?}: mode {mode:?}"));
        }
    }

    // arg_order against the order of the argument temporaries.
    let mut lines = Vec::new();
    let seen = check_arg_order(p, &units, &orders, &mut lines);
    found
        .arg_order
        .extend(lines.into_iter().map(|l| format!("{path}: {l}")));
    for key in orders.keys().filter(|k| !seen.contains(k)) {
        found
            .arg_order
            .push(format!("{path}: arg_order at {key:?} has no IR call"));
    }

    // int_ops against the operators. The key of the operator of a compound
    // assignment (`x += v`) is the span of the statement; the key of its
    // int_ops entry is the span of `v`, which ends where the statement ends.
    let ir_ops = ir_int_ops(p, &units);
    let mut used = BTreeSet::new();
    for (key, set) in &ir_ops {
        let fits = |k: &Key| set.len() == 1 && int_ops.get(k).is_some_and(|n| set.contains(n));
        let compound = || {
            int_ops
                .keys()
                .filter(|k| k.0 == key.0 && k.2 == key.2 && k.1 > key.1)
                .max_by_key(|k| k.1)
                .copied()
        };
        if fits(key) {
            used.insert(*key);
        } else if let Some(k) = compound().filter(|k| !int_ops.contains_key(key) && fits(k)) {
            used.insert(k);
        } else {
            found.int_ops.push(format!(
                "{path}: operator at {key:?}: IR {set:?}, int_ops {:?}",
                int_ops.get(key)
            ));
        }
    }
    for (key, name) in &int_ops {
        if !used.contains(key) {
            found.int_ops.push(format!(
                "{path}: int_ops {name} at {key:?} has no IR operator"
            ));
        }
    }
    found
}

/// The result of D1 on tier 1: the number of programs and the mismatches.
struct Result1 {
    programs: usize,
    found: Found,
}

/// Runs D1 on each file of tier 1, once for all the tests.
fn tier1() -> &'static Result1 {
    static R: OnceLock<Result1> = OnceLock::new();
    R.get_or_init(|| {
        let files = tier1_files();
        let root = repo();
        let threads = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
        // The largest files first, so that no thread gets a large file last.
        let mut files: Vec<(u64, String)> = files
            .into_iter()
            .map(|f| {
                let len = std::fs::metadata(root.join(&f)).map_or(0, |m| m.len());
                (len, f)
            })
            .collect();
        files.sort_by(|a, b| b.cmp(a));
        let next = AtomicUsize::new(0);
        let parts: Vec<(usize, Found)> = std::thread::scope(|s| {
            let handles: Vec<_> = (0..threads)
                .map(|_| {
                    let (root, files, next) = (&root, &files, &next);
                    s.spawn(move || {
                        let mut n = 0;
                        let mut f = Found::default();
                        while let Some((_, path)) = files.get(next.fetch_add(1, Ordering::Relaxed))
                        {
                            let at = std::time::Instant::now();
                            // A thread for each program: a program that the
                            // old analysis checks too slowly in a debug build
                            // is skipped (its thread runs on and ends with the
                            // test).
                            let (tx, rx) = mpsc::channel();
                            let (p, full) = (path.clone(), root.join(path));
                            std::thread::spawn(move || {
                                let g = std::fs::read_to_string(&full).ok().and_then(|src| {
                                    analyze_source(&src, Options::from_markers(&src))
                                        .ok()
                                        .map(|a| d1(&p, &a))
                                });
                                let _ = tx.send(g);
                            });
                            let g = match rx.recv_timeout(LIMIT) {
                                Ok(Some(g)) => g,
                                Ok(None) => continue,
                                Err(_) => {
                                    f.skipped.push(path.clone());
                                    continue;
                                }
                            };
                            n += 1;
                            f.by_value.extend(g.by_value);
                            f.fn_copy.extend(g.fn_copy);
                            f.arg_order.extend(g.arg_order);
                            f.int_ops.extend(g.int_ops);
                            f.times.push((at.elapsed().as_millis(), path.clone()));
                        }
                        (n, f)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_else(|_| (0, Found::default())))
                .collect()
        });
        let mut r = Result1 {
            programs: 0,
            found: Found::default(),
        };
        for (n, f) in parts {
            r.programs += n;
            r.found.by_value.extend(f.by_value);
            r.found.fn_copy.extend(f.fn_copy);
            r.found.times.extend(f.times);
            r.found.skipped.extend(f.skipped);
            r.found.arg_order.extend(f.arg_order);
            r.found.int_ops.extend(f.int_ops);
        }
        r.found.by_value.sort();
        r.found.fn_copy.sort();
        r.found.arg_order.sort();
        r.found.int_ops.sort();
        if let Some(dir) = std::env::var_os("D1_DUMP") {
            let dir = PathBuf::from(dir);
            r.found.times.sort();
            let slow: Vec<String> = r
                .found
                .times
                .iter()
                .rev()
                .take(40)
                .map(|(ms, p)| format!("{ms} {p}"))
                .collect();
            let _ = std::fs::write(dir.join("times.txt"), slow.join("\n"));
            for (name, lines) in [
                ("by_value", &r.found.by_value),
                ("fn_copy", &r.found.fn_copy),
                ("arg_order", &r.found.arg_order),
                ("int_ops", &r.found.int_ops),
            ] {
                let _ = std::fs::write(dir.join(format!("{name}.txt")), lines.join("\n"));
            }
        }
        r
    })
}

/// The lines of a failure: the count and the first lines.
fn show(lines: &[String]) -> String {
    let first: Vec<&str> = lines.iter().take(40).map(String::as_str).collect();
    format!("{} mismatches:\n{}", lines.len(), first.join("\n"))
}

/// The programs in which a closure body copies a function value out of a
/// capture that `by_value` moves (class `closure-copy`, B12b): the old
/// analysis moves a value that holds a function value when the body reads
/// the function value, and the IR copies the function value. All of them are
/// programs that the checker rejects. A new program in this list needs a
/// review.
const CLOSURE_COPY: [&str; 14] = [
    "tests/gate/probes/fixes/f12/run_results.wf",
    "tests/gate/probes/r2/redteam/p/zz_modes_vec.wf",
    "tests/gate/probes/r3/oracle/probes/s9_steal_stored.wf",
    "tests/gate/probes/r3/oracle/probes/sc4_vec_in_task.wf",
    "tests/gate/probes/r3/oracle/probes/sc5_tuple_in_task.wf",
    "tests/gate/probes/r3/oracle/probes/sc6_opt_in_task.wf",
    "tests/gate/probes/r3/oracle/probes/sd3_generic_struct.wf",
    "tests/gate/probes/r3/oracle/repro/O3-5_task_runs_field_closure.wf",
    "tests/gate/probes/s5/p/hof2.wf",
    "tests/gate/probes/verify/partb/S4/p/c10_tuple_np.wf",
    "tests/gate/probes/verify/partb/S4/p/c5_nonportable.wf",
    "tests/gate/probes/verify/s5/R2c/p/c2.wf",
    "tests/ir_targets/o3_5_field_closure_tasks.wf",
    "tests/programs/143_arg_roots.wf",
];

/// The programs in which a closure gives back a closure that moves a
/// parameter of the outer closure (`|t: Tx| || rollback(t)`): the old
/// lowering puts the move of `t` in `by_value` of the outer closure, and the
/// IR moves `t` into the inner closure (the parameter of the outer closure is
/// not one of its captures). The IR is right: the oracle runs the inner
/// closure with the moved value. Variants of hole H3 of the review of the
/// ABC preview (F12-fix). A new program in this list needs a review.
const NESTED_PARAM_MOVE: [&str; 2] = [
    "tests/gate/probes/fixes/f12/h3/d11_ret_from_closure_maker_drop.wf",
    "tests/gate/probes/fixes/f12/h3/hl_e_localmaker.wf",
];

#[test]
fn the_by_move_captures_of_the_ir_are_the_by_value_captures() {
    let r = tier1();
    for p in &r.found.skipped {
        eprintln!("skipped (the analysis takes more than {LIMIT:?}): {p}");
    }
    assert!(r.programs > 3000, "{} programs", r.programs);
    assert!(
        r.found.skipped.len() * 100 <= r.programs,
        "{} programs are skipped",
        r.found.skipped.len()
    );
    let new: Vec<&String> = r
        .found
        .fn_copy
        .iter()
        .filter(|l| !CLOSURE_COPY.iter().any(|p| l.starts_with(&format!("{p}:"))))
        .collect();
    assert!(new.is_empty(), "new closure-copy cases: {new:?}");
    eprintln!("{} closure-copy cases", r.found.fn_copy.len());
    let by_value: Vec<String> = r
        .found
        .by_value
        .iter()
        .filter(|l| {
            !NESTED_PARAM_MOVE
                .iter()
                .any(|p| l.starts_with(&format!("{p}:")) && l.contains("is in by_value"))
        })
        .cloned()
        .collect();
    assert!(by_value.is_empty(), "{}", show(&by_value));
}

#[test]
fn each_ir_call_evaluates_its_arguments_in_the_arg_order() {
    let r = tier1();
    assert!(r.found.arg_order.is_empty(), "{}", show(&r.found.arg_order));
}

#[test]
fn the_integer_type_of_each_ir_operator_is_the_int_ops_type() {
    let r = tier1();
    assert!(r.found.int_ops.is_empty(), "{}", show(&r.found.int_ops));
}
