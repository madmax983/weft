//! The acceptance targets of the core IR are real (`tests/ir_targets`).
//!
//! The checker accepts each bad case of a target today, and the core IR must
//! reject it (the test `ir_targets` of `weft-check`). This test shows that each
//! bad case is a real defect, and that each clean case is clean:
//!
//! - Each test block of a file runs a clean case. It must pass with the oracle,
//!   for the seeds 0 to 20 and for 1, 2 and 4 workers.
//! - Each top-level function `bad_NAME()` of a file is a bad case. The test
//!   adds `test "bad_NAME" { bad_NAME() }` to the source and runs that test
//!   with the oracle, for the same seeds and worker counts. One of these runs
//!   must fault. A function `bad_NAME` with parameters, with `pub` or in a
//!   `mod` is an error: the test cannot run it.
//! - Each `//~` marker must be in a top-level function that a bad case reaches.
//!   A function reaches each function whose name is in its text. So a marker
//!   in a helper that no bad case calls is an error: no run shows that it is
//!   real.
//!
//! A fault is a run-time error of the kind `ErrorKind::Fault` that shows a
//! defect that the checker must reject: an oracle check, a use after a move,
//! or a linear value with no `on abort` that an abort path drops (ADR 0010).
//! `TestOutcome` gives the kind at the start of its message. A failure that
//! no handler catches is not a fault, so a bad case that needs a handler has
//! the handler inside its function.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use weft_interp::{run_tests, ErrorKind, RunOptions};
use weft_sema::Options;
use weft_syntax::ast::{Item, ItemKind};
use weft_syntax::{parse_file, SourceFile};

/// The texts of the faults that count, after the kind.
const FAULTS: [&str; 3] = [
    "oracle: ",
    "a value is used after it was moved",
    "so the unwinder cannot finish it",
];

/// The seeds of the runs of a bad case and of the clean cases.
const SEEDS: std::ops::RangeInclusive<u64> = 0..=20;

/// The worker counts of the runs of a bad case and of the clean cases.
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

/// A top-level function of a target.
struct Func {
    name: String,
    /// The first and the last line of the function.
    lines: (usize, usize),
    /// The words of its text: the names that it can call or use.
    words: BTreeSet<String>,
}

/// Returns the words (identifiers) of a text.
fn words(text: &str) -> BTreeSet<String> {
    text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|w| !w.is_empty())
        .map(str::to_string)
        .collect()
}

/// Adds a reason to `errors` for each function `bad_NAME` of an item that
/// cannot run as a bad case: a `pub` function, a function with parameters, or
/// a function in a `mod`.
fn check_bad_item(item: &Item, top: bool, errors: &mut Vec<String>) {
    match &item.kind {
        ItemKind::Fn(f) if f.name.name.starts_with("bad_") => {
            let name = &f.name.name;
            if !top {
                errors.push(format!("`{name}` must be a top-level function"));
            }
            if item.is_pub {
                errors.push(format!("`{name}` must not be `pub`"));
            }
            if !f.params.is_empty() {
                errors.push(format!("`{name}` must take no argument"));
            }
        }
        ItemKind::Mod(m) => {
            for i in &m.items {
                check_bad_item(i, false, errors);
            }
        }
        _ => {}
    }
}

/// Returns the top-level functions of a target, or the reasons that its bad
/// cases cannot run.
fn functions(src: &str) -> Result<Vec<Func>, Vec<String>> {
    let parsed = parse_file(src).map_err(|e| vec![format!("parse error: {e}")])?;
    let file = SourceFile::new("target", src);
    let mut errors = Vec::new();
    let mut out = Vec::new();
    for item in &parsed.items {
        check_bad_item(item, true, &mut errors);
        let ItemKind::Fn(f) = &item.kind else {
            continue;
        };
        let (lo, hi) = (item.span.lo, item.span.hi.max(item.span.lo + 1) - 1);
        let text = src.get(lo as usize..=hi as usize).unwrap_or_default();
        out.push(Func {
            name: f.name.name.clone(),
            lines: (file.line_col(lo).0, file.line_col(hi).0),
            words: words(text),
        });
    }
    if errors.is_empty() {
        Ok(out)
    } else {
        Err(errors)
    }
}

/// Returns the names of the bad cases: the top-level functions `bad_NAME`.
fn bad_cases(funcs: &[Func]) -> Vec<&str> {
    funcs
        .iter()
        .map(|f| f.name.as_str())
        .filter(|n| n.starts_with("bad_"))
        .collect()
}

/// Returns the names of the functions that a bad case reaches.
fn reached(funcs: &[Func]) -> BTreeSet<&str> {
    let mut seen: BTreeSet<&str> = bad_cases(funcs).into_iter().collect();
    let mut work: Vec<&str> = seen.iter().copied().collect();
    while let Some(n) = work.pop() {
        let Some(f) = funcs.iter().find(|f| f.name == n) else {
            continue;
        };
        for g in funcs.iter().filter(|g| f.words.contains(&g.name)) {
            if seen.insert(g.name.as_str()) {
                work.push(g.name.as_str());
            }
        }
    }
    seen
}

/// Returns a reason for each `//~` marker that is not in a function that a bad
/// case reaches.
fn unreached_markers(src: &str, funcs: &[Func]) -> Vec<String> {
    let reach = reached(funcs);
    let mut out = Vec::new();
    for (i, line) in src.lines().enumerate() {
        if !line.contains("//~") {
            continue;
        }
        let n = i + 1;
        match funcs.iter().find(|f| f.lines.0 <= n && n <= f.lines.1) {
            None => out.push(format!("the marker at line {n} is not in a function")),
            Some(f) if !reach.contains(f.name.as_str()) => out.push(format!(
                "the marker at line {n} is in `{}`, which no bad case reaches",
                f.name
            )),
            Some(_) => {}
        }
    }
    out
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

/// Runs each test block of a target for each seed and worker count. Returns a
/// reason for each test that fails, with the first run where it fails.
fn clean_failures(name: &str, src: &str) -> Vec<String> {
    let checked = weft_check::check_source(name, src, Options::from_markers(src));
    let mut failed = BTreeSet::new();
    let mut out = Vec::new();
    for seed in SEEDS {
        for workers in WORKERS {
            let tests = run_tests(&checked, &options(seed, workers));
            if tests.is_empty() {
                return vec![format!("{name}: no test block runs a clean case")];
            }
            for t in tests.iter().filter(|t| !t.passed) {
                if failed.insert(t.name.clone()) {
                    out.push(format!(
                        "{name}: the clean case {} fails (seed {seed}, {workers} workers): {:?}",
                        t.name, t.message
                    ));
                }
            }
        }
    }
    out
}

/// Checks one target file. Returns the reasons that it fails.
fn check_target(path: &Path) -> Vec<String> {
    let src = fs::read_to_string(path).unwrap();
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    let funcs = match functions(&src) {
        Ok(f) => f,
        Err(errors) => return errors.into_iter().map(|e| format!("{name}: {e}")).collect(),
    };
    let mut failures = clean_failures(&name, &src);
    failures.extend(
        unreached_markers(&src, &funcs)
            .into_iter()
            .map(|e| format!("{name}: {e}")),
    );
    let bads = bad_cases(&funcs);
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
    let funcs = functions(src).unwrap();
    assert_eq!(bad_cases(&funcs), vec!["bad_a", "bad_b2", "bad_c"]);
    let errors = |s: &str| functions(s).err().unwrap_or_default();
    assert_eq!(
        errors("fn bad_e(x: u64) { }\n"),
        vec!["`bad_e` must take no argument"]
    );
    assert_eq!(
        errors("pub fn bad_f() { }\n"),
        vec!["`bad_f` must not be `pub`"]
    );
    assert_eq!(
        errors("mod m { fn bad_g() { } }\n"),
        vec!["`bad_g` must be a top-level function"]
    );
}

#[test]
fn markers_must_be_in_a_function_that_a_bad_case_reaches() {
    let src = "\
fn helper() {
    print(1)   //~ W0301
}
fn lost() {
    print(2)   //~ W0301
}
fn bad_a() { helper() }
fn ok_b() { lost() }
test \"ok_b\" { ok_b() }   //~ W0405
";
    let funcs = functions(src).unwrap();
    assert_eq!(
        reached(&funcs),
        ["bad_a", "helper"].into_iter().collect::<BTreeSet<_>>()
    );
    assert_eq!(
        unreached_markers(src, &funcs),
        vec![
            "the marker at line 5 is in `lost`, which no bad case reaches",
            "the marker at line 9 is not in a function",
        ]
    );
}

#[test]
fn ir_targets_are_real() {
    let paths = targets();
    assert!(!paths.is_empty(), "tests/ir_targets has no .wf file");
    let failures: Vec<String> = paths.iter().flat_map(|p| check_target(p)).collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
