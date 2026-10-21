//! The IR engine (`--engine=ir`, plan stages I1 and I2, `docs/ir.md` 8.1).
//!
//! The IR compiler compiles the programs of the construct groups A, B and C
//! (closures and function values). For a program with a construct of a later
//! stage (a handler, a task), the AST compiler runs the program, and the
//! outcome tells why. The tests here check:
//!
//! - each interpreter program that uses only groups A, B and C gives its
//!   `.out` with the IR engine (none of them shows a change of `docs/ir.md`
//!   8.3);
//! - each other interpreter program falls back and says why;
//! - each program of the static corpus with a `main` or tests gives the same
//!   output with the two engines;
//! - the expected changes of `docs/ir.md` 8.3: choice A (5.1.1, probes p1,
//!   p2 and p9) and the end of the tail temporaries of a loop body at each
//!   iteration (5.1.2, probe p24);
//! - each op of the IR compiler carries its IR location;
//! - the captures of a closure follow the modes of the IR (rule CAPTURE,
//!   `docs/ir.md` 5.1.7): a `Kept` capture shares the cell of the variable, a
//!   `ByRef` capture holds a reference to it, a `ByMove` capture takes the
//!   value when the closure is made.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use weft_interp::code::Op;
use weft_interp::compile_ir::compile_ir;
use weft_interp::{run_main, run_tests, Engine, RunOptions, RunOutcome};
use weft_ir::CaptureMode;
use weft_sema::Options;

/// The interpreter programs that use only the construct groups A, B and C.
/// The IR engine runs each one; each other program falls back.
const RUNS_ON_IR: &[&str] = &[
    "blocking",
    "closure_return",
    "control",
    "int_width",
    "named_args",
    "no_runtime_marker",
    "place_statements",
    "places",
    "rc_cycle",
    "root_handlers",
    "values",
];

fn directive<'s>(src: &'s str, key: &str) -> Option<&'s str> {
    src.lines()
        .take_while(|l| l.starts_with("//"))
        .find_map(|l| l.strip_prefix("// ")?.strip_prefix(key))
        .map(str::trim)
}

fn programs(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "wf"))
        .collect();
    v.sort();
    v
}

fn stem(p: &Path) -> String {
    p.file_stem().unwrap().to_string_lossy().into_owned()
}

/// Runs one interpreter program as `tests/programs.rs` does. Returns the
/// output text and the reason of a fallback.
fn run_program(path: &Path, engine: Engine) -> (String, Option<String>) {
    let src = fs::read_to_string(path).unwrap();
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    let options = Options::from_markers(&src);
    let no_runtime = options.no_runtime;
    let checked = weft_check::check_source(&name, &src, options);
    let opts = RunOptions {
        seed: directive(&src, "seed:").map_or(0, |s| s.parse().unwrap()),
        max_steps: Some(5_000_000),
        no_runtime,
        oracle: true,
        engine,
        ..RunOptions::default()
    };
    let mut out = String::new();
    let fallback;
    if checked.analysis.program.tests.is_empty() {
        let outcome = match run_main(&checked, &opts) {
            Ok(o) => o,
            Err(e) => {
                let o = *e.outcome.clone();
                writeln!(out, "error: {e}").unwrap();
                o
            }
        };
        fallback = outcome.fallback.clone();
        out.insert_str(0, &outcome.stdout);
        let _ = writeln!(out, "leaked {}", outcome.leaked_rc);
    } else {
        let ts = run_tests(&checked, &opts);
        fallback = ts.first().and_then(|t| t.outcome.fallback.clone());
        for t in ts {
            out.push_str(&t.outcome.stdout);
            match t.message {
                None => writeln!(out, "test {}: ok", t.name).unwrap(),
                Some(m) => writeln!(out, "test {}: FAILED: {m}", t.name).unwrap(),
            }
        }
    }
    (out, fallback)
}

/// The output of the AST engine: the `.out` file of the program, as
/// `run_program` writes it.
fn expected(path: &Path) -> String {
    run_program(path, Engine::Ast).0
}

#[test]
fn each_program_of_groups_a_to_c_gives_its_output_with_the_ir_engine() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let mut failures = String::new();
    let mut on_ir = BTreeSet::new();
    for path in programs(&dir) {
        let name = stem(&path);
        let (out, fallback) = run_program(&path, Engine::Ir);
        if let Some(why) = fallback {
            if RUNS_ON_IR.contains(&name.as_str()) {
                let _ = writeln!(failures, "{name}: falls back: {why}");
            }
            if !why.contains("stage I") && !why.contains("has no IR") {
                let _ = writeln!(failures, "{name}: the fallback names no stage: {why}");
            }
            continue;
        }
        on_ir.insert(name.clone());
        let want = expected(&path);
        if out != want {
            let _ = write!(
                failures,
                "{name}: output differs\n--- expected\n{want}--- found\n{out}"
            );
        }
    }
    let want: BTreeSet<String> = RUNS_ON_IR.iter().map(|s| (*s).to_string()).collect();
    assert_eq!(on_ir, want, "the programs that the IR engine runs");
    assert!(failures.is_empty(), "{failures}");
}

#[test]
fn each_program_of_the_corpus_gives_the_same_output_with_both_engines() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut failures = String::new();
    let mut ran = 0;
    for path in programs(&dir) {
        let src = fs::read_to_string(&path).unwrap();
        if !src.contains("fn main(") && !src.lines().any(|l| l.starts_with("test ")) {
            continue;
        }
        let name = stem(&path);
        let (out, fallback) = run_program(&path, Engine::Ir);
        if fallback.is_some() {
            continue;
        }
        ran += 1;
        let want = expected(&path);
        if out != want {
            let _ = write!(
                failures,
                "{name}: output differs\n--- ast\n{want}--- ir\n{out}"
            );
        }
    }
    assert!(ran >= 4, "the IR engine runs only {ran} corpus programs");
    assert!(failures.is_empty(), "{failures}");
}

fn checked(src: &str) -> weft_check::Checked {
    let c = weft_check::check_source("t.wf", src, Options::default());
    assert!(c.ok(), "the checker rejects the program: {:?}", c.codes());
    c
}

fn run_with(src: &str, engine: Engine) -> RunOutcome {
    let c = checked(src);
    let opts = RunOptions {
        max_steps: Some(1_000_000),
        oracle: true,
        engine,
        ..RunOptions::default()
    };
    match run_main(&c, &opts) {
        Ok(o) => o,
        Err(e) => panic!("run failed: {e}\n{}", e.outcome.stdout),
    }
}

/// Runs the unchecked program `src` with `engine`: the checker can reject
/// it (the probes of choice A read a place that a later operand changes).
fn run_unchecked(src: &str, engine: Engine) -> RunOutcome {
    let a = weft_sema::analyze_source(src, Options::default()).unwrap();
    let opts = RunOptions {
        max_steps: Some(1_000_000),
        engine,
        ..RunOptions::default()
    };
    match weft_interp::run_analysis_main(&a, &opts) {
        Ok(o) => o,
        Err(e) => panic!("run failed: {e}\n{}", e.outcome.stdout),
    }
}

#[test]
fn an_operand_is_read_where_it_is_written() {
    // Choice A (`docs/ir.md` 5.1.1, probe p1): the IR reads `x` before the
    // block changes it. The AST engine reads it after the block.
    let src = "fn main() {\n let x = 1\n let y = x + { x = 5; 1 }\n print(y)\n}";
    let ir = run_unchecked(src, Engine::Ir);
    assert_eq!(ir.fallback, None);
    assert_eq!(ir.stdout, "2\n");
    assert_eq!(run_unchecked(src, Engine::Ast).stdout, "6\n");
}

/// Runs probe `name` of `tests/gate/probes/ir/probes` with the oracle checks.
/// Returns the output and the error message, if any.
fn probe(name: &str, engine: Engine) -> (String, Option<String>) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/gate/probes/ir/probes")
        .join(format!("{name}.wf"));
    let src = fs::read_to_string(path).unwrap();
    let a = weft_sema::analyze_source(&src, Options::default()).unwrap();
    let opts = RunOptions {
        max_steps: Some(1_000_000),
        oracle: true,
        engine,
        ..RunOptions::default()
    };
    match weft_interp::run_analysis_main(&a, &opts) {
        Ok(o) => {
            assert_eq!(o.fallback, None);
            (o.stdout, None)
        }
        Err(e) => {
            assert_eq!(e.outcome.fallback, None);
            (e.outcome.stdout.clone(), Some(e.message))
        }
    }
}

#[test]
fn a_reference_is_read_before_a_later_operand_changes_its_place() {
    // Choice A (`docs/ir.md` 8.3, probes p2 and p9): the IR reads `r.hp`
    // before the block pushes to `v`, so the read is not through a dangling
    // reference. The AST engine reads it after the push, and the oracle
    // stops it.
    assert_eq!(
        probe("p2_late_operand_ref", Engine::Ir),
        ("2\n".into(), None)
    );
    assert_eq!(probe("p9_print_late", Engine::Ir), ("1 1\n".into(), None));
    for p in ["p2_late_operand_ref", "p9_print_late"] {
        let (_, e) = probe(p, Engine::Ast);
        assert!(e.unwrap().contains("dangling"), "{p}");
    }
}

#[test]
fn a_tail_temporary_of_a_loop_body_ends_at_each_iteration() {
    // `docs/ir.md` 5.1.2 (probe p24): the `Rc` of `&Rc.new(i)` in the tail
    // of the loop body ends at the end of its iteration. The AST engine ends
    // it at the end of the loop.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/gate/probes/ir/probes/p24_loop_tail_temp.wf");
    let src = fs::read_to_string(path).unwrap();
    let ir = run_with(&src, Engine::Ir);
    assert_eq!(ir.fallback, None);
    assert_eq!(
        ir.stdout,
        "iteration 1 previous tail temp alive: false\n\
         iteration 2 previous tail temp alive: false\n\
         after loop: false\n"
    );
    assert_eq!(
        run_with(&src, Engine::Ast).stdout,
        "iteration 1 previous tail temp alive: true\n\
         iteration 2 previous tail temp alive: true\n\
         after loop: false\n"
    );
}

#[test]
fn a_program_with_a_handler_falls_back_and_says_why() {
    let src = "effect Ask { fn ask() -> u64 }\n\
        fn main() {\n let v = handle Ask { fn ask() { resume(4) } } in { ask() + 1 }\n print(v)\n}";
    let o = run_with(src, Engine::Ir);
    assert_eq!(o.stdout, "5\n");
    let why = o.fallback.expect("the IR engine falls back");
    assert!(why.contains("handler") && why.contains("stage I3"), "{why}");
    assert_eq!(run_with(src, Engine::Ast).fallback, None);
}

/// Returns the capture modes of each closure of the IR of `src`.
fn capture_modes(src: &str) -> Vec<Vec<CaptureMode>> {
    let a = weft_sema::analyze_source(src, Options::default()).unwrap();
    let built = weft_sema::irbuild::build(&a);
    built
        .program
        .closures
        .iter()
        .map(|c| c.captures.iter().map(|k| k.mode).collect())
        .collect()
}

#[test]
fn a_closure_runs_on_the_ir_engine() {
    let src = "fn main() {\n let f = |x: u64| x + 1\n print(f(1))\n}";
    let o = run_with(src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "2\n");
}

#[test]
fn a_kept_counter_closure_shares_its_cell_with_the_maker() {
    // `|| count += 1` is `Kept` (`docs/ir.md` 5.1.7): the closure writes the
    // cell of `count`, so the maker reads 2. The closure that `counter`
    // returns keeps the cell of `n` after the end of `n`.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../weft-sema/tests/ir_golden/closure_kept_counter.wf");
    let src = fs::read_to_string(path).unwrap();
    assert_eq!(
        capture_modes(&src),
        vec![vec![CaptureMode::Kept], vec![CaptureMode::Kept]]
    );
    let o = run_with(&src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "2\n1\n");
}

#[test]
fn a_closure_reads_the_closure_value_that_a_kept_capture_has_at_the_call() {
    // Probe `late_once_capture` (plan stage B12): `k` shares the cell of `c`,
    // so `k()` calls the closure that `c` has at the call. Closure values
    // stay shared: a copy of `c` is the same closure.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/gate/probes/fixes/b12/late_once_capture.wf");
    let src = fs::read_to_string(path).unwrap();
    let o = run_with(&src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "7\n");
}

#[test]
fn a_by_ref_capture_reads_the_new_value_of_the_variable() {
    // The body borrows `x`, so the capture is `ByRef`: the closure holds the
    // reference `&x`, and `(*env.0)` reads the value that `x` has at the
    // call. The checker rejects the write of a borrowed `x`.
    let src = "fn get(r: &u64) -> u64 { r + 0 }\n\
        fn main() {\n let x = 1\n let f = || print(get(&x))\n f()\n x = 5\n f()\n}";
    assert_eq!(capture_modes(src), vec![vec![CaptureMode::ByRef]]);
    let o = run_unchecked(src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "1\n5\n");
}

#[test]
fn a_by_move_capture_moves_when_the_closure_is_made() {
    // `take(v)` moves `v`, so the capture is `ByMove`: the closure takes the
    // value of `v` when it is made. The new value of `v` is not the one of
    // the closure.
    let src = "fn take(v: Vec<u64>) -> usize { v.len() }\n\
        fn main() {\n let v = Vec.new()\n v.push(1)\n let f = || print(take(v))\n\
        v = Vec.new()\n v.push(5)\n v.push(6)\n f()\n print(v.len())\n}";
    assert_eq!(capture_modes(src), vec![vec![CaptureMode::ByMove]]);
    let o = run_with(src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "1\n2\n");
    // A read of `v` after the closure is made reads a moved value. The
    // checker rejects it.
    let src = "fn take(v: Vec<u64>) -> usize { v.len() }\n\
        fn main() {\n let v = Vec.new()\n v.push(1)\n let f = || print(take(v))\n\
        print(take(v))\n f()\n}";
    let a = weft_sema::analyze_source(src, Options::default()).unwrap();
    let opts = RunOptions {
        engine: Engine::Ir,
        ..RunOptions::default()
    };
    let e = weft_interp::run_analysis_main(&a, &opts).unwrap_err();
    assert_eq!(e.outcome.fallback, None);
    assert_eq!(e.outcome.stdout, "");
    assert!(e.message.contains("moved"), "{}", e.message);
}

#[test]
fn the_oracle_stops_a_by_ref_capture_after_the_end_of_its_variable() {
    // Probe J5d (`docs/ir.md` 8.3, rule CAPTURE): the closure that `make`
    // returns reads `p` through `&p` after the end of `p`. The IR engine
    // holds the reference `&p` in the environment (`ByRef`); the AST engine
    // shares the cell and borrows it in the body. The oracle stops both.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/gate/probes/ir/judge_sound/j5d_maker_borrow.wf");
    let src = fs::read_to_string(path).unwrap();
    assert_eq!(capture_modes(&src), vec![vec![CaptureMode::ByRef]]);
    let a = weft_sema::analyze_source(&src, Options::default()).unwrap();
    for engine in [Engine::Ast, Engine::Ir] {
        let opts = RunOptions {
            oracle: true,
            engine,
            ..RunOptions::default()
        };
        let e = weft_interp::run_analysis_main(&a, &opts).unwrap_err();
        assert_eq!(e.outcome.fallback, None, "{engine:?}");
        assert!(e.message.contains("dangling"), "{engine:?}: {}", e.message);
    }
}

#[test]
fn the_closures_of_capture_by_value_give_their_output_with_the_ir_engine() {
    // `capture_by_value.wf` has a `scope` (plan stage I4). With the part that
    // spawns a task taken out, the IR engine runs it, and it gives the
    // `.out` lines of the other parts.
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let src = fs::read_to_string(dir.join("capture_by_value.wf")).unwrap();
    let from = src.find("    let w = Vec.new()").unwrap();
    let to = src.find("    let b = Vec.new()").unwrap();
    let cut = format!("{}{}", &src[..from], &src[to..]);
    let mut want = String::new();
    for l in fs::read_to_string(dir.join("capture_by_value.out"))
        .unwrap()
        .lines()
        .filter(|l| !l.starts_with("task") && !l.starts_with("w "))
    {
        writeln!(want, "{l}").unwrap();
    }
    let o = run_with(&cut, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, want);
    assert_eq!(run_with(&cut, Engine::Ast).stdout, want);
}

#[test]
fn a_function_item_is_a_value() {
    // `Const::Fn` and calls of function values (`docs/ir.md` 5.21, 5.23).
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../weft-sema/tests/ir_golden/fn_value_call.wf");
    let src = fs::read_to_string(path).unwrap();
    let o = run_with(&src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, run_with(&src, Engine::Ast).stdout);
    assert_eq!(o.stdout, "7\n11\n");
}

#[test]
fn a_once_closure_runs_once() {
    // Probe `fn_alias_once` of plan stage B12: `g` holds the `once` closure of `f`.
    // The first call takes the captures; the second call reads a moved
    // value. The checker rejects the program (W0502).
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/gate/probes/fixes/b12/fn_alias_once.wf");
    let src = fs::read_to_string(path).unwrap();
    let a = weft_sema::analyze_source(&src, Options::default()).unwrap();
    for engine in [Engine::Ast, Engine::Ir] {
        let opts = RunOptions {
            engine,
            ..RunOptions::default()
        };
        let e = weft_interp::run_analysis_main(&a, &opts).unwrap_err();
        assert_eq!(e.outcome.fallback, None, "{engine:?}");
        assert!(e.message.contains("moved"), "{engine:?}: {}", e.message);
    }
}

#[test]
fn each_op_carries_its_ir_location() {
    let src = "struct P { a: u64, b: u64 }\n\
        fn sum(p: &P) -> u64 { p.a + p.b }\n\
        fn main() {\n let p = P { a: 1, b: 2 }\n let i = 0\n while i < 2 { print(sum(&p)); i += 1 }\n}";
    let c = checked(src);
    let built = weft_sema::irbuild::build(&c.analysis);
    let code = compile_ir(&c.analysis.program, &built).expect("the IR compiler compiles it");
    assert!(!code.codes.is_empty());
    for unit in &code.codes {
        assert_eq!(unit.locs.len(), unit.ops.len(), "{}", unit.name);
        assert_eq!(unit.spans.len(), unit.ops.len(), "{}", unit.name);
        for l in &unit.locs {
            let body = &built.program.bodies[l.body as usize];
            let block = &body.blocks[l.block as usize];
            assert!(l.stmt as usize <= block.stmts.len());
        }
    }
    // The back edge of the loop is a preemption point.
    let main = code.codes.iter().find(|u| u.name == "main").unwrap();
    assert!(main.ops.iter().any(|o| matches!(o, Op::BackEdge)));
    assert_eq!(run_with(src, Engine::Ir).stdout, "3\n3\n");
}

#[test]
fn a_payload_place_of_a_variant_reads_the_payload_or_faults() {
    // `o.Some` (`docs/ir.md` 5.8): the IR tests the variant, then reads the
    // payload. Another variant is a fault. The AST engine finds no field
    // `Some` in an enum value, so it faults on each variant.
    let src = "fn main() {\n let o: Option<u64> = None\n let p = Some(3)\n print(p.Some)\n print(o.Some)\n}";
    let c = checked(src);
    let opts = RunOptions {
        engine: Engine::Ir,
        ..RunOptions::default()
    };
    let e = run_main(&c, &opts).unwrap_err();
    assert_eq!(e.outcome.fallback, None);
    assert_eq!(e.outcome.stdout, "3\n");
    assert!(e.message.contains("another variant"), "{}", e.message);
    let e = run_main(&c, &RunOptions::default()).unwrap_err();
    assert_eq!(e.outcome.stdout, "");
    assert!(e.message.contains("no field `Some`"), "{}", e.message);
}
