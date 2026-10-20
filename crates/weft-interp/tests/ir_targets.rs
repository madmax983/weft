//! The acceptance targets of the core IR are real (`tests/ir_targets`).
//!
//! The checker accepts each bad case of a target today, and the core IR must
//! reject it (the test `ir_targets` of `weft-check`). This test shows that each
//! bad case is a real defect, and that each clean case is clean:
//!
//! - Each test block of a file runs a clean case. It must pass with the oracle.
//! - Each function `bad_NAME()` of a file is a bad case. The test adds
//!   `test "bad_NAME" { bad_NAME() }` to the source and runs that test with
//!   the oracle, for the seeds 0 to 20 and for 1, 2 and 4 workers. One of
//!   these runs must fault.
//!
//! A fault is a run-time error of the kind `ErrorKind::Fault` that shows a
//! defect that the checker must reject: an oracle check, a use after a move,
//! or a linear value with no `on abort` that an abort path drops (ADR 0010).
//! `TestOutcome` gives the kind at the start of its message. A failure that
//! no handler catches is not a fault, so a bad case that needs a handler has
//! the handler inside its function.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use std::fs;
use std::path::{Path, PathBuf};

use weft_interp::{run_tests, ErrorKind, RunOptions};
use weft_sema::Options;

/// The texts of the faults that count, after the kind.
const FAULTS: [&str; 3] = [
    "oracle: ",
    "a value is used after it was moved",
    "so the unwinder cannot finish it",
];

/// The seeds of the runs of a bad case.
const SEEDS: std::ops::RangeInclusive<u64> = 0..=20;

/// The worker counts of the runs of a bad case.
const WORKERS: [usize; 3] = [1, 2, 4];

fn targets() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/ir_targets");
    let mut v: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "wf"))
        .collect();
    v.sort();
    v
}

fn options(seed: u64, workers: usize) -> RunOptions {
    RunOptions {
        seed,
        workers,
        oracle: true,
        max_steps: Some(1_000_000),
        capture_output: true,
        ..RunOptions::default()
    }
}

/// True if the message of a failed test shows a fault that counts.
fn is_fault(message: &str) -> bool {
    message
        .strip_prefix(&format!("{}: ", ErrorKind::Fault))
        .is_some_and(|m| FAULTS.iter().any(|f| m.contains(f)))
}

/// Returns the name of each bad case: each top-level `fn bad_NAME()`.
fn bad_cases(src: &str) -> Result<Vec<&str>, String> {
    let mut out = Vec::new();
    for line in src.lines() {
        let Some(rest) = line.strip_prefix("fn bad_") else {
            continue;
        };
        let len = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        let name = &line[3..3 + "bad_".len() + len];
        if !rest[len..].starts_with("()") {
            return Err(format!("`{name}` must take no argument"));
        }
        out.push(name);
    }
    Ok(out)
}

/// Runs the bad case `bad` until a run faults. Returns the seed, the worker
/// count and the message of that run.
fn first_fault(name: &str, src: &str, bad: &str) -> Option<(u64, usize, String)> {
    let src = format!("{src}\ntest \"{bad}\" {{ {bad}() }}\n");
    let checked = weft_check::check_source(name, &src, Options::from_markers(&src));
    for seed in SEEDS {
        for workers in WORKERS {
            let outcome = run_tests(&checked, &options(seed, workers))
                .into_iter()
                .find(|t| t.name == bad)?;
            if let Some(m) = outcome.message.filter(|m| is_fault(m)) {
                return Some((seed, workers, m));
            }
        }
    }
    None
}

/// Checks one target file. Returns the reasons that it fails.
fn check_target(path: &Path) -> Vec<String> {
    let src = fs::read_to_string(path).unwrap();
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    let mut failures = Vec::new();
    let checked = weft_check::check_source(&name, &src, Options::from_markers(&src));
    let tests = run_tests(&checked, &options(0, RunOptions::default().workers));
    if tests.is_empty() {
        failures.push(format!("{name}: no test block runs a clean case"));
    }
    for t in tests.iter().filter(|t| !t.passed) {
        failures.push(format!(
            "{name}: the clean case {} fails: {:?}",
            t.name, t.message
        ));
    }
    let bads = match bad_cases(&src) {
        Ok(b) => b,
        Err(e) => {
            failures.push(format!("{name}: {e}"));
            return failures;
        }
    };
    if bads.is_empty() {
        failures.push(format!("{name}: no function `bad_NAME()`"));
    }
    for bad in bads {
        match first_fault(&name, &src, bad) {
            Some((seed, workers, m)) => {
                eprintln!("{name}: {bad} faults (seed {seed}, {workers} workers): {m}");
            }
            None => failures.push(format!(
                "{name}: {bad} does not fault; the target is not real"
            )),
        }
    }
    failures
}

#[test]
fn faults_are_kind_fault_with_a_known_text() {
    assert!(is_fault(
        "runtime error: oracle: a read of a freed cell (a dangling reference)"
    ));
    assert!(is_fault(
        "runtime error: a value is used after it was moved"
    ));
    assert!(!is_fault("runtime error: division by zero"));
    assert!(!is_fault("failed: oracle: boom"));
    assert!(!is_fault("step limit: oracle: the run is too long"));
}

#[test]
fn bad_cases_are_top_level_functions_with_no_argument() {
    let src = "fn bad_a() { }\nfn bad_b2() / io { }\n  fn bad_c() { }\nfn ok_d() { }\n";
    assert_eq!(bad_cases(src), Ok(vec!["bad_a", "bad_b2"]));
    assert!(bad_cases("fn bad_e(x: u64) { }\n").is_err());
}

#[test]
fn ir_targets_are_real() {
    let paths = targets();
    assert!(!paths.is_empty(), "tests/ir_targets has no .wf file");
    let failures: Vec<String> = paths.iter().flat_map(|p| check_target(p)).collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
