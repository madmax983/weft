//! The copies of the callees at their calls (plan stage R0k-a,
//! `weft_sema::factgen::instantiate`) do not change what a program does.
//!
//! The fact oracle runs the program with the copies (the program that the
//! `ir` pipeline checks), so a copy that changes the program would make the
//! oracle check the wrong program. This test runs each probe of the stages
//! R0h and R0k with `fn main` on the IR engine two times, the program as the
//! builder gives it and the program with the copies, and compares the
//! output and the fault of the two runs.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use std::fs;
use std::path::{Path, PathBuf};

use weft_check::check_source;
use weft_interp::{run_main, run_main_copied, RunOptions, RuntimeError};
use weft_sema::Options;

/// The probes of the stages that the copies are for.
fn probes() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/gate/probes/fixes");
    let mut out = Vec::new();
    for dir in ["r0h", "r0k"] {
        let Ok(rd) = fs::read_dir(root.join(dir)) else {
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
    for p in probes() {
        let src = fs::read_to_string(&p).unwrap();
        if !src.contains("fn main") {
            continue;
        }
        let name = p.display().to_string();
        let c = check_source(&name, &src, Options::default());
        let built = weft_sema::irbuild::build(&c.analysis);
        if weft_sema::factgen::instantiate::instantiate(&built).is_none() {
            continue;
        }
        copied += 1;
        let a = seen(run_main(&c, &opts));
        let b = seen(run_main_copied(&c, &opts));
        assert_eq!(a, b, "{name}: the run of the copy differs");
    }
    assert!(copied >= 40, "only {copied} probes have copies");
}
