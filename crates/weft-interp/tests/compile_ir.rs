//! The IR engine (`--engine=ir`, plan stages I1 to I4, `docs/ir.md` 8.1).
//!
//! The IR compiler compiles each program that has IR. A program with a body
//! that has no IR (a type error, an error in a declaration, W0303) falls
//! back to the AST compiler, and the outcome tells why. The checker rejects
//! these programs. The tests here check:
//!
//! - each interpreter program gives its `.out` with the IR engine, and only
//!   the programs with no IR fall back;
//! - each program of the static corpus with a `main` or tests gives the same
//!   output with the two engines;
//! - the expected changes of `docs/ir.md` 8.3: choice A (5.1.1, probes p1,
//!   p2 and p9) and the end of the tail temporaries of a loop body at each
//!   iteration (5.1.2, probe p24);
//! - each op of the IR compiler carries its IR location;
//! - the captures of a closure follow the modes of the IR (rule CAPTURE,
//!   `docs/ir.md` 5.1.7): a `Kept` capture shares the cell of the variable, a
//!   `ByRef` capture holds a reference to it, a `ByMove` capture takes the
//!   value when the closure is made;
//! - an upvar local of a handled body or a clause is the cell of the site
//!   local (5.1.7), a `multi` resume copies the cells of the handled body and
//!   shares the cells of the site, and a perform through a capability finds
//!   the handler of the capability (5.24 to 5.27);
//! - scopes, tasks, `fork`, `sim.run` and `with_timeout` (5.29 to 5.31) give
//!   the output of the AST engine, and a task has the same `stealable` mark.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use weft_interp::code::{CodeKind, Op, VarRef};
use weft_interp::compile_ir::compile_ir;
use weft_interp::{run_main, run_tests, Engine, RunOptions, RunOutcome, TraceEvent};
use weft_ir::CaptureMode;
use weft_sema::Options;

/// The interpreter programs with a body that has no IR. The AST compiler
/// runs them; each other program runs on the IR engine.
const NO_IR: &[&str] = &["interrupt_nested_unwind"];

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
fn each_interpreter_program_gives_its_output_with_the_ir_engine() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let mut failures = String::new();
    let mut fell_back = BTreeSet::new();
    let mut count = 0;
    for path in programs(&dir) {
        count += 1;
        let name = stem(&path);
        let (out, fallback) = run_program(&path, Engine::Ir);
        if let Some(why) = fallback {
            if !why.contains("has no IR") {
                let _ = writeln!(failures, "{name}: falls back: {why}");
            }
            fell_back.insert(name.clone());
        }
        let want = expected(&path);
        if out != want {
            let _ = write!(
                failures,
                "{name}: output differs\n--- expected\n{want}--- found\n{out}"
            );
        }
    }
    assert_eq!(count, 61, "the number of interpreter programs");
    let want: BTreeSet<String> = NO_IR.iter().map(|s| (*s).to_string()).collect();
    assert_eq!(fell_back, want, "the programs with no IR");
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
        if let Some(why) = fallback {
            // Only a program with no IR falls back. The checker rejects it.
            assert!(why.contains("has no IR"), "{name}: {why}");
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
    assert!(ran >= 20, "the IR engine runs only {ran} corpus programs");
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
fn a_borrow_of_plain_data_runs_clean_under_the_oracle() {
    // `docs/ir.md` 5.10: a borrow of plain data borrows a promoted temporary.
    // `temp_copy` is the function of `tests/programs/32_temporaries.wf`. In a
    // loop each `Live` makes a new cell: the reference of each iteration
    // keeps its own value, as on the AST engine.
    let src = "struct P { x: u64, y: u64 }\n\
        fn mkp() -> P { P { x: 1, y: 2 } }\n\
        fn temp_copy() {\n    let r = &1\n    print(r)\n}\n\
        fn in_branch(c: bool) { let k = 0; let r = &k; if c { r = &5 }; print(r) }\n\
        fn field_path() { let x = &mkp().x; print(x) }\n\
        fn in_loop() {\n\
            let v = Vec.new()\n    let i = 0\n\
            while i < 3 { v.push(&(i + 1)); i += 1 }\n\
            print(v[0])\n    print(v[2])\n}\n\
        fn write_through() {\n    let i = 0\n\
            while i < 2 { let r = &(0, 0); r.0 += 1; print(r.0); i += 1 }\n}\n\
        fn main() { temp_copy(); in_branch(true); field_path(); in_loop(); write_through() }\n";
    let want = "1\n5\n1\n1\n3\n1\n1\n";
    let ir = run_with(src, Engine::Ir);
    assert_eq!(ir.fallback, None);
    assert_eq!(ir.stdout, want);
    assert_eq!(run_with(src, Engine::Ast).stdout, want);
}

#[test]
fn a_handler_runs_on_the_ir_engine() {
    let src = "effect Ask { fn ask() -> u64 }\n\
        fn main() {\n let v = handle Ask { fn ask() { resume(4) } } in { ask() + 1 }\n print(v)\n}";
    let o = run_with(src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "5\n");
}

#[test]
fn a_scope_runs_on_the_ir_engine() {
    let src = "fn main() / async {\n let v = scope { s =>\n let t = s.spawn(|| 4)\n t.join() + 1\n }\n print(v)\n}";
    let o = run_with(src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "5\n");
    // The scope body is a code unit of its own: it waits for its tasks.
    let code = compiled(src);
    let body = code
        .codes
        .iter()
        .find(|u| u.kind == CodeKind::ScopeBody)
        .expect("a scope body");
    assert_eq!(body.n_params, 1, "the scope capability");
    assert!(body.ops.iter().any(|o| matches!(o, Op::ScopeWait(0))));
}

#[test]
fn a_program_with_no_ir_falls_back_and_says_why() {
    // `rollback` has a type error: it has no IR. The checker rejects the
    // program; the AST compiler runs it.
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let (_, why) = run_program(&dir.join("interrupt_nested_unwind.wf"), Engine::Ir);
    let why = why.expect("the IR engine falls back");
    assert!(why.contains("`rollback` has no IR"), "{why}");
}

#[test]
fn each_task_golden_gives_the_output_of_the_ast_engine() {
    // The golden programs of the IR builder for scopes and tasks
    // (`docs/ir.md` 5.29 to 5.31). Each one gets a `main` that calls its
    // functions, if it has none.
    let extra = [
        ("scope_wait", "fn main() / async { print(scoped(3).len()) }"),
        ("join", ""),
        ("spawn_handle", ""),
        ("detach", ""),
        ("fork", ""),
        (
            "with_timeout",
            "fn main() / async, fail { print(timed(4)) }",
        ),
        (
            "scope_value_chain",
            "fn main() / async { print(early(true), early(false), scoped()) }",
        ),
        ("scope_in_closure", ""),
        ("nested_in_closure", ""),
    ];
    for (name, main) in extra {
        let src = format!("{}\n{main}\n", golden(name));
        let ir = run_oracle(&src, Engine::Ir);
        assert_eq!(ir, run_oracle(&src, Engine::Ast), "{name}");
        assert_eq!(ir.1, None, "{name}");
    }
    // A spawn in statement position: the scope keeps the result.
    let src = format!(
        "{}\nfn go() / async {{ main(true); main(false); print(1) }}\n",
        golden("spawn_stmt_result")
    )
    .replace("fn main(c: bool)", "fn run(c: bool)")
    .replace("main(true); main(false)", "run(true); run(false)")
    .replace("fn go()", "fn main()");
    assert_eq!(run_oracle(&src, Engine::Ir), ("1\n".to_string(), None));
}

#[test]
fn sim_run_gives_its_body_the_workers_of_the_call() {
    // `docs/ir.md` 5.30: `workers` is 4 when the call leaves it out.
    let src = golden("sim_run");
    let a = weft_sema::analyze_source(&src, Options::default()).unwrap();
    let opts = |engine| RunOptions {
        oracle: true,
        engine,
        ..RunOptions::default()
    };
    let ir = weft_interp::run_analysis_tests(&a, &opts(Engine::Ir));
    let ast = weft_interp::run_analysis_tests(&a, &opts(Engine::Ast));
    assert_eq!(ir.len(), 2);
    for (i, t) in ir.iter().zip(&ast) {
        assert_eq!(i.outcome.fallback, None);
        assert!(i.passed, "{}: {:?}", i.name, i.message);
        assert_eq!(i, t);
    }
}

#[test]
fn a_with_timeout_block_that_passes_its_deadline_aborts() {
    // `docs/ir.md` 5.31: the call can abort. The handler of `fail` gets the
    // failure of the deadline.
    let src = "fn slow() -> u64 / clock { sleep(5.s); 1 }\n\
        fn main() / io {\n\
        let r = handle Fail { fn fail(msg) { print(\"failed: {msg}\"); 0 } } in {\n\
        with_timeout(1.s) { slow() } + 1\n }\n print(r)\n}";
    let o = run_with(src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, run_with(src, Engine::Ast).stdout);
    assert_eq!(o.stdout, "failed: timeout\n0\n");
}

#[test]
fn a_task_of_the_ir_engine_has_the_stealable_mark_of_the_checker() {
    // The checker names a task by the span of its closure argument; the IR
    // engine finds the span in the spawn site (`docs/ir.md` 5.29). The two
    // engines start the same tasks, with the same `stealable` marks. The
    // preemption points are not the same: the IR engine runs more ops.
    fn spawns(o: &RunOutcome) -> Vec<(usize, usize, bool)> {
        o.trace
            .iter()
            .filter_map(|e| match e {
                TraceEvent::Spawn {
                    task,
                    parent,
                    stealable,
                    ..
                } => Some((*task, *parent, *stealable)),
                _ => None,
            })
            .collect()
    }
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    for name in ["steal", "fork", "scope_join"] {
        let src = fs::read_to_string(dir.join(format!("{name}.wf"))).unwrap();
        let c = checked(&src);
        let opts = |engine| RunOptions {
            workers: 4,
            max_steps: Some(1_000_000),
            oracle: true,
            engine,
            ..RunOptions::default()
        };
        let ir = run_main(&c, &opts(Engine::Ir)).unwrap();
        let ast = run_main(&c, &opts(Engine::Ast)).unwrap();
        assert_eq!(ir.fallback, None, "{name}");
        assert_eq!(ir.stdout, ast.stdout, "{name}");
        assert_eq!(spawns(&ir), spawns(&ast), "{name}");
        if name == "steal" {
            assert!(spawns(&ir).iter().any(|s| s.2), "{name}: a stealable task");
        }
    }
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
fn capture_by_value_gives_its_output_with_the_ir_engine() {
    // `capture_by_value.wf` has closures and a `scope` with a task.
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let src = fs::read_to_string(dir.join("capture_by_value.wf")).unwrap();
    let want = fs::read_to_string(dir.join("capture_by_value.out")).unwrap();
    let o = run_with(&src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, want);
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

/// Runs the unchecked program `src` with the oracle checks and `engine`.
/// Returns the output and the error message, if any. The IR engine must not
/// fall back.
fn run_oracle(src: &str, engine: Engine) -> (String, Option<String>) {
    let a = weft_sema::analyze_source(src, Options::default()).unwrap();
    let opts = RunOptions {
        max_steps: Some(1_000_000),
        oracle: true,
        engine,
        ..RunOptions::default()
    };
    match weft_interp::run_analysis_main(&a, &opts) {
        Ok(o) => {
            assert_eq!(o.fallback, None, "{engine:?}");
            (o.stdout, None)
        }
        Err(e) => {
            assert_eq!(e.outcome.fallback, None, "{engine:?}");
            (e.outcome.stdout.clone(), Some(e.message))
        }
    }
}

/// Returns the source of the golden program `name` of the IR builder.
fn golden(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../weft-sema/tests/ir_golden")
        .join(format!("{name}.wf"));
    fs::read_to_string(path).unwrap()
}

/// Compiles the IR of the checked program `src`.
fn compiled(src: &str) -> weft_interp::compile::Compiled {
    let c = checked(src);
    let built = weft_sema::irbuild::build(&c.analysis);
    compile_ir(&c.analysis.program, &built).expect("the IR compiler compiles it")
}

#[test]
fn an_upvar_local_is_the_captured_cell_of_the_site() {
    // The handled body and the clause write `n` through their upvar locals
    // (`docs/ir.md` 5.1.7): the writes are writes of the cell of `n`.
    let src = "effect Tick { fn tick() }\n\
        fn main() {\n let n = 1\n\
        handle Tick { fn tick() { n += 10; resume(()) } } in {\n n += 1\n tick()\n n += 100\n }\n\
        print(n)\n}";
    let o = run_with(src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "112\n");
    // The `Handle` op gives the handled body and the clause the cell of the
    // slot of `n`; there the upvar local is the captured cell 0.
    let code = compiled(src);
    let main = code.codes.iter().find(|u| u.name == "main").unwrap();
    let spec = main
        .ops
        .iter()
        .find_map(|o| match o {
            Op::Handle(s) => Some(s.clone()),
            _ => None,
        })
        .expect("main has a `Handle` op");
    assert!(matches!(spec.body_caps.as_slice(), [VarRef::Local(_)]));
    assert_eq!(spec.clauses.len(), 1);
    assert_eq!(spec.clauses[0].caps, spec.body_caps);
    for kind in [CodeKind::HandleBody, CodeKind::Clause] {
        let unit = code.codes.iter().find(|u| u.kind == kind).unwrap();
        assert!(
            unit.ops
                .iter()
                .any(|o| matches!(o, Op::Var(VarRef::Cap(0)))),
            "{kind:?}"
        );
    }
}

#[test]
fn a_move_of_an_upvar_local_in_a_handled_body_moves_the_site_local() {
    // `take(v)` in the handled body moves the value of `v` of `main`. The
    // second `take(v)` reads a moved value. The checker rejects it (W0302).
    let src = "fn take(v: Vec<u64>) -> usize { v.len() }\n\
        effect Tick { fn tick() }\n\
        fn main() {\n let v = Vec.new()\n v.push(1)\n\
        let n = handle Tick { fn tick() { resume(()) } } in { tick(); take(v) }\n\
        print(n)\n print(take(v))\n}";
    for engine in [Engine::Ast, Engine::Ir] {
        let (out, e) = run_oracle(src, engine);
        assert_eq!(out, "1\n", "{engine:?}");
        let e = e.expect("the second `take` faults");
        assert!(e.contains("moved"), "{engine:?}: {e}");
    }
}

#[test]
fn a_multi_resume_copies_the_cells_of_the_handled_body_and_shares_the_site_cells() {
    // Each run of the handled body starts from a copy of its frame at the
    // perform: `local` is 0 at the start of each run. `total` is a local of
    // `main`: the runs share its cell.
    let src = "effect Pick { multi fn pick() -> bool }\n\
        fn main() {\n let total = 0\n\
        handle Pick { fn pick() { resume(true); resume(false) } } in {\n\
        let local = 0\n let b = pick()\n local += 1\n total += 1\n print(b, local, total)\n }\n\
        print(total)\n}";
    let o = run_with(src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "true 1 1\nfalse 1 2\n2\n");
    // Judge probe J4: the reference `r` of the handled body is copied, and
    // it points into the shared `o`, which the first run cleared. The
    // oracle stops the read of the second run with both engines.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/gate/probes/ir/judge_sound/j4_multi_outer_ref.wf");
    let src = fs::read_to_string(path).unwrap();
    for engine in [Engine::Ast, Engine::Ir] {
        let (out, e) = run_oracle(&src, engine);
        assert_eq!(out, "2\n", "{engine:?}");
        let e = e.expect("the second run reads a freed cell");
        assert!(e.contains("dangling"), "{engine:?}: {e}");
    }
}

#[test]
fn a_perform_through_a_capability_finds_the_handler_of_the_capability() {
    // `docs/ir.md` 5.1.8, 5.26: the handled body performs through its
    // capability local, the closure through its `Cap` field. The machine
    // finds the handler; a debug assertion checks that it is the handler of
    // the capability.
    let src = golden("cap_field");
    let o = run_with(&src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "one\n2\n");
    let code = compiled(&src);
    let closure = code
        .codes
        .iter()
        .find(|u| u.kind == CodeKind::Closure)
        .unwrap();
    assert!(closure
        .ops
        .iter()
        .any(|o| matches!(o, Op::PerformCap { .. })));
    // The inner clause performs `outer` through the capability of the outer
    // handled body.
    let src = golden("nested_handle");
    let o = run_with(&src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "30\n");
}

#[test]
fn a_closure_resumes_through_its_kont_field() {
    // `docs/ir.md` 5.27: the closure copies the `multi` continuation into a
    // `Kont` field, so it can run twice.
    let src = format!("{}\nfn main() {{ print(count()) }}\n", golden("cont_field"));
    let o = run_with(&src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "3\n");
    // Judge probe J2: the clause resumes through a closure, then clears `v`.
    // The oracle stops the read through `keep` with both engines.
    let src = golden("resume_closure");
    for engine in [Engine::Ast, Engine::Ir] {
        let (_, e) = run_oracle(&src, engine);
        let e = e.expect("the read through `keep` dangles");
        assert!(e.contains("dangling"), "{engine:?}: {e}");
    }
}

#[test]
fn a_handled_body_in_a_closure_names_the_captures_through_a_view() {
    // `docs/ir.md` 5.1.7 (B12): the handled body and the clause name the
    // captures of the closure through an upvar local of the environment.
    // The handled body moves the linear `l`, the clause reads `n`, and the
    // handled body borrows `v`.
    let src = golden("handle_in_closure");
    let o = run_with(&src, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "unlock 1\n10\n");
}

#[test]
fn each_handler_golden_gives_the_output_of_the_ast_engine() {
    // The golden programs of the IR builder for handlers, also the ones
    // that the checker rejects: the two engines give the same output and
    // the same error.
    for name in [
        "handle_value",
        "multi_tail_upvar",
        "cap_field",
        "nested_handle",
        "handle_in_closure",
        "resume_closure",
        "m8_abort_value_into_body",
    ] {
        let src = golden(name);
        assert_eq!(
            run_oracle(&src, Engine::Ir),
            run_oracle(&src, Engine::Ast),
            "{name}"
        );
    }
}

#[test]
fn nested_multi_continuations_run_on_the_ir_engine() {
    // Finding FD2: each copy of a nested `multi` continuation has a record
    // of its own. The IR engine runs the repro with no fault of the oracle.
    // The claim of FD2 reads the IR oracle cache of plan stage I5.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/gate/probes/r2/fidelity/repro/FD2_multi_nested_drop.wf");
    let src = fs::read_to_string(path).unwrap();
    assert_eq!(run_oracle(&src, Engine::Ir), ("2\n".to_string(), None));
}

#[test]
fn a_jump_out_of_a_handled_body_or_a_clause_faults_with_the_w0315_text() {
    // The builder ends the path of a `return` or a `break` that leaves a
    // handled body or a clause with `Unreachable` (W0315). The IR engine
    // faults there with the text of W0315. The checker rejects the program.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/gate/probes/ir/probes/p17_return_in_clause.wf");
    let src = fs::read_to_string(path).unwrap();
    let (out, e) = run_oracle(&src, Engine::Ir);
    assert_eq!(out, "");
    let e = e.expect("the `return` faults");
    assert!(e.contains("`return` cannot leave a handler clause"), "{e}");
}

// ---------------------------------------------------------------------------
// Landing pads and the unwind order (plan stage I6, `docs/ir.md` 8.2)
// ---------------------------------------------------------------------------

#[test]
fn the_unwinder_keeps_the_order_of_the_locals_of_p18() {
    // The cleanup chain of `work` finishes the locals from the highest
    // index: `c`, then `b`, then `a` (`docs/ir.md` 5.1.6). This is the
    // order of the AST engine too.
    let want = "caught boom\nrollback 3\nrollback 2\nrollback 1\n";
    for engine in [Engine::Ast, Engine::Ir] {
        assert_eq!(
            probe("p18_abort_order", engine),
            (want.to_string(), None),
            "{engine:?}"
        );
    }
}

#[test]
fn a_clause_unwinds_its_fresh_continuation_first() {
    // `docs/ir.md` 8.3 (probe p20): the chain of the clause starts with
    // `UnwindKont`, so the frames of the continuation unwind before the
    // locals of the clause, as in the effects model. The AST engine
    // unwinds the clause frame first.
    assert_eq!(
        probe("p20_clause_unwind_order", Engine::Ir),
        ("caught x\nrollback 1\nrollback 2\n".to_string(), None)
    );
    assert_eq!(
        probe("p20_clause_unwind_order", Engine::Ast),
        ("caught x\nrollback 2\nrollback 1\n".to_string(), None)
    );
}

/// A scope body whose value has an `on abort`. A child fails, so the
/// `ScopeWait` of the scope body aborts while the value is in `_0`.
const SCOPE_VALUE: &str = "linear struct Tx { id: u64 }\n    on abort = rollback\n\
    fn rollback(t: Tx) { let Tx(i) = t; print(\"rollback\", i) }\n\
    fn commit(t: Tx) { let Tx(i) = t; print(\"commit\", i) }\n\
    fn main() / async, fail {\n\
    handle Fail { fn fail(m) { print(\"caught\", m) } } in {\n\
    let t = scope { s =>\n s.spawn(|| fail(\"child\"))\n Tx { id: 1 }\n }\n\
    commit(t)\n }\n}";

#[test]
fn the_value_of_a_scope_body_is_finished_when_scope_wait_aborts() {
    // `docs/ir.md` 5.1.6: the chain of `ScopeWait` starts with `_0`.
    let o = run_with(SCOPE_VALUE, Engine::Ir);
    assert_eq!(o.fallback, None);
    assert_eq!(o.stdout, "rollback 1\ncaught child\n");
    assert_eq!(run_with(SCOPE_VALUE, Engine::Ast).stdout, o.stdout);
    // The landing pad of `ScopeWait` starts with the `UnwindValue` of `_0`
    // (slot 1: the scope capability is slot 0).
    let code = compiled(SCOPE_VALUE);
    let unit = code
        .codes
        .iter()
        .find(|c| c.kind == CodeKind::ScopeBody)
        .expect("a scope body");
    let at = unit
        .ops
        .iter()
        .position(|op| matches!(op, Op::ScopeWait(_)))
        .expect("a `ScopeWait`");
    let pad = unit.pad(at).expect("a landing pad");
    assert!(
        matches!(&unit.ops[pad], Op::UnwindValue { var: VarRef::Local(1), path } if path.is_empty()),
        "{:?}",
        &unit.ops[pad..]
    );
}

#[test]
fn each_aborting_op_of_the_ir_has_a_landing_pad_into_its_cleanup_code() {
    // Each call has a landing pad. The code of the pad has only
    // unwind-mode ops, the ends of slots and jumps, and it ends at
    // `UnwindExit`.
    let code = compiled(SCOPE_VALUE);
    let mut pads = 0;
    for unit in &code.codes {
        for (at, op) in unit.ops.iter().enumerate() {
            let Some(mut pc) = unit.pad(at) else {
                assert!(
                    !matches!(op, Op::Call { .. } | Op::ScopeWait(_) | Op::Handle(_)),
                    "{}: op {at} {op:?} has no landing pad",
                    unit.name
                );
                continue;
            };
            pads += 1;
            loop {
                match &unit.ops[pc] {
                    Op::UnwindExit => break,
                    Op::Jump(t) => pc = *t,
                    Op::UnwindValue { .. }
                    | Op::UnwindKont(_)
                    | Op::DropSlots(_)
                    | Op::EndTemp(_) => pc += 1,
                    other => panic!("{}: {other:?} in a cleanup chain", unit.name),
                }
            }
        }
    }
    assert!(pads >= 4, "only {pads} landing pads");
}
