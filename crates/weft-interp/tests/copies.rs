//! The copies of the callees at their calls (plan stage R0k-a,
//! `weft_sema::factgen::instantiate`) do not change what a program does.
//!
//! The fact oracle runs the program with the copies (the program that the
//! `ir` pipeline checks), so a copy that changes the program would make the
//! oracle check the wrong program. This test runs each probe of the stages
//! R0h, R0k and R0k-a2 with `fn main` on the IR engine two times, the program as the
//! builder gives it and the program with the copies, and compares the
//! output and the fault of the two runs. The files in `tests/copies` add
//! the forms that a wrong copy of the parameters shows: two parameters of
//! the same type, named arguments in the other order, `self`, a struct that
//! holds a reference, and an abort path. The copies of a closure that
//! resumes the continuation of its clause (stage R0k-c1, `instantiate_kont`)
//! have a test of their own, with the probes of `fixes/r0kc` and `fixes/r0g`.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use std::fs;
use std::path::{Path, PathBuf};

use weft_check::check_source;
use weft_interp::{run_main, run_main_copied, RunOptions, RuntimeError};
use weft_sema::Options;

/// The probes of the stages that the copies are for, and the files in
/// `tests/copies`.
fn probes() -> Vec<PathBuf> {
    let here = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixes = here.join("../../tests/gate/probes/fixes");
    let mut out = Vec::new();
    for dir in [
        fixes.join("r0h"),
        fixes.join("r0k"),
        fixes.join("r0k2"),
        fixes.join("r0k3"),
        fixes.join("r0kb1"),
        here.join("tests/copies"),
    ] {
        let Ok(rd) = fs::read_dir(&dir) else {
            continue;
        };
        for e in rd.flatten() {
            let p = e.path();
            if p.extension().is_some_and(|x| x == "wf") {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

/// What a run gives: the output, and the kind and the text of its fault.
fn seen(r: Result<weft_interp::RunOutcome, RuntimeError>) -> (String, String, String) {
    match r {
        Ok(o) => (o.stdout, o.stderr, String::new()),
        Err(e) => (
            e.outcome.stdout.clone(),
            e.outcome.stderr.clone(),
            format!("{:?}: {}", e.kind, e.message),
        ),
    }
}

#[test]
fn the_copies_of_the_callees_do_not_change_the_runs() {
    let opts = RunOptions {
        oracle: true,
        workers: 1,
        max_steps: Some(5_000_000),
        ..RunOptions::default()
    };
    let mut copied = 0;
    let mut local = 0;
    // The probes with a copy of a closure body at a run node (stage R0k-a2).
    let mut closures = 0;
    // The probes with a copy region (stage R0k-b1').
    let mut regions = 0;
    for p in probes() {
        let src = fs::read_to_string(&p).unwrap();
        if !src.contains("fn main") {
            continue;
        }
        let name = p.display().to_string();
        let c = check_source(&name, &src, Options::default());
        let built = weft_sema::irbuild::build(&c.analysis);
        let Some(inst) = weft_sema::factgen::instantiate::instantiate(&built) else {
            continue;
        };
        copied += 1;
        if inst.closure_calls > 0 {
            closures += 1;
        }
        if inst.regions > 0 {
            regions += 1;
        }
        if p.parent().is_some_and(|d| d.ends_with("copies")) {
            local += 1;
        }
        let a = seen(run_main(&c, &opts));
        let b = seen(run_main_copied(&c, &opts));
        assert_eq!(a, b, "{name}: the run of the copy differs");
    }
    assert!(copied >= 40, "only {copied} probes have copies");
    assert_eq!(local, 7, "each file in tests/copies must get a copy");
    assert!(closures >= 8, "only {closures} probes have closure copies");
    assert!(regions >= 6, "only {regions} probes have copy regions");
}

/// The copy regions of `fixes/r0k3/h02_made_closure_row` and
/// `fixes/r0kb1/n06_row_value_ok` (plan stage R0k-b1'). In h02 the closure
/// that `mk` makes performs `run` through the row of `mk`, so its operation
/// goes to the handler of the call of `mk` (the handler of `main`), not to
/// the local handler of `outer` where it runs: the program prints 1 with the
/// copy and without it. In n06 the `reg` of the closure goes past `outer` to
/// the handler of `main`: the program prints 2. A copy that ran with the
/// handlers of the run node would print 9 (h02) and 1 (n06): the program with
/// the copies and no copy regions shows it.
#[test]
fn a_copy_region_runs_with_the_handlers_of_the_closure_value() {
    for (dir, file, out, site_out) in [
        ("r0k3", "h02_made_closure_row.wf", "1\n", "9\n"),
        ("r0kb1", "n06_row_value_ok.wf", "2\n", "1\n"),
    ] {
        the_region_runs_with_the_handlers_of_the_value(dir, file, out, site_out);
    }
}

/// [`a_copy_region_runs_with_the_handlers_of_the_closure_value`] for the
/// probe `file` of `fixes/dir`: the output `out` with and without the copy,
/// and `site_out` for the copy with no copy regions.
fn the_region_runs_with_the_handlers_of_the_value(
    dir: &str,
    file: &str,
    out: &str,
    site_out: &str,
) {
    let opts = RunOptions {
        oracle: true,
        workers: 1,
        max_steps: Some(5_000_000),
        ..RunOptions::default()
    };
    let here = Path::new(env!("CARGO_MANIFEST_DIR"));
    let p = here
        .join("../../tests/gate/probes/fixes")
        .join(dir)
        .join(file);
    let src = fs::read_to_string(&p).unwrap();
    let name = p.display().to_string();
    let c = check_source(&name, &src, Options::default());
    let built = weft_sema::irbuild::build(&c.analysis);
    let inst = weft_sema::factgen::instantiate::instantiate(&built).expect("a copy");
    assert!(inst.regions > 0, "{name}: no copy region");
    let a = seen(run_main(&c, &opts));
    let b = seen(run_main_copied(&c, &opts));
    assert_eq!(a.0, out, "{name}");
    assert_eq!(a, b, "{name}: the run of the copy differs");
    // The machine checks that a perform through a capability finds the
    // handler of the capability; the copy with no regions breaks that.
    let opts = RunOptions {
        site_henv_in_copies: true,
        ..opts
    };
    let mut site = inst.built;
    site.program.regions.clear();
    let out = weft_sema::on_large_stack(|| {
        let code = weft_interp::compile_ir::compile_ir(&c.analysis.program, &site)
            .unwrap_or_else(|f| panic!("no code for the copy: {f}"));
        let rt = weft_interp::runtime::Runtime::with_code(
            &c.analysis.program,
            c.analysis.sigs.as_slice(),
            weft_interp::stealable_spans(&c),
            code,
        );
        seen(weft_interp::run_runtime_main(&rt, &opts))
    });
    assert_eq!(
        out.0, site_out,
        "{name}: the copy with the handlers of the run node"
    );
}

/// The copies of stage R0k-c1 (`instantiate_kont`) do not change what a
/// program does: each probe of `fixes/r0kc` and `fixes/r0g` with such a
/// copy runs with and without it with the same output and fault, also when
/// the make of a closure with a `once` continuation goes.
#[test]
fn the_copies_of_continuation_closures_do_not_change_the_runs() {
    let opts = RunOptions {
        oracle: true,
        workers: 1,
        max_steps: Some(5_000_000),
        ..RunOptions::default()
    };
    let here = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixes = here.join("../../tests/gate/probes/fixes");
    let mut files = Vec::new();
    for dir in [fixes.join("r0kc"), fixes.join("r0g")] {
        for e in fs::read_dir(&dir).unwrap().flatten() {
            let p = e.path();
            if p.extension().is_some_and(|x| x == "wf") {
                files.push(p);
            }
        }
    }
    files.sort();
    let (mut copied, mut removed) = (0, 0);
    for p in files {
        let src = fs::read_to_string(&p).unwrap();
        if !src.contains("fn main") {
            continue;
        }
        let name = p.display().to_string();
        let c = check_source(&name, &src, Options::default());
        let built = weft_sema::irbuild::build(&c.analysis);
        let Some(inst) = weft_sema::factgen::instantiate::instantiate_kont(&built) else {
            continue;
        };
        if inst.covered.is_empty() {
            continue;
        }
        copied += 1;
        // A `once` continuation: the make of the closure goes.
        let made = inst.built.program.bodies.iter().any(|b| {
            b.blocks.iter().flat_map(|k| &k.stmts).any(|s| {
                matches!(&s.kind, weft_ir::StmtKind::Assign(_, weft_ir::Rvalue::Aggregate(weft_ir::AggKind::Closure(x), _)) if inst.covered.contains(x))
            })
        });
        if !made {
            removed += 1;
        }
        let a = seen(run_main(&c, &opts));
        let b = seen(run_kont_copied(&c, &inst.built, &opts));
        assert_eq!(a, b, "{name}: the run of the copy differs");
    }
    assert!(
        copied >= 8,
        "only {copied} probes have copies of continuation closures"
    );
    assert!(
        removed >= 4,
        "only {removed} probes lose the make of the closure"
    );
}

/// Runs `fn main` of the program `built` (the program of `checked` with
/// copies) on the IR engine.
fn run_kont_copied(
    checked: &weft_check::Checked,
    built: &weft_sema::irbuild::Built,
    opts: &RunOptions,
) -> Result<weft_interp::RunOutcome, RuntimeError> {
    weft_sema::on_large_stack(|| {
        let analysis = &checked.analysis;
        let code = weft_interp::compile_ir::compile_ir(&analysis.program, built)
            .unwrap_or_else(|f| panic!("no code for the copy: {f}"));
        let rt = weft_interp::runtime::Runtime::with_code(
            &analysis.program,
            analysis.sigs.as_slice(),
            weft_interp::stealable_spans(checked),
            code,
        );
        weft_interp::run_runtime_main(&rt, opts)
    })
}
