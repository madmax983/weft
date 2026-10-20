//! The acceptance targets of the core IR (`tests/ir_targets`).

#![allow(clippy::unwrap_used, clippy::expect_used)]
//!
//! Each file holds programs that the checker accepts today and that fault at
//! run time with the oracle (review round 3). The fix of each one is in fact
//! generation, so the core IR must find them (ADRs 0003, 0005, 0006 and 0007,
//! and `docs/traceability.md`). A line that ends with `//~ CODE ...` expects
//! those error codes on that line, as in `tests/programs`. The markers give the
//! correct result, not the result of the checker today.
//!
//! The test expects each file to fail. For each file, in sorted order:
//!
//! - An error at a line with no such marker fails the test. This is a false
//!   positive, a broken target, or an error at another line. If the new line
//!   is correct, move the marker.
//! - For each body, the production checker must agree with the Datalog spec.
//! - If the checker reports each marker, the test fails: the target is done.
//!   Move the file to `tests/programs` with the next free number, and delete it
//!   from `tests/ir_targets`. The file needs no other change: its test blocks
//!   run the clean cases, and no test block runs a bad case.
//! - Else the file passes. The test prints the markers that the checker does
//!   not report yet. To see them, run
//!   `cargo test -p weft-check --test ir_targets -- --nocapture`.
//!
//! The directory must hold at least one `.wf` file, and no file can have
//! `fn main`. The test `ir_targets` of `weft-interp` shows that each target is
//! real: each bad case faults, and each clean case runs clean.

mod common;

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use common::{actual, expected, write_disagreements, Codes};
use weft_check::check_source;
use weft_sema::Options;
use weft_syntax::SourceFile;

/// Returns the `.wf` files of a directory, in sorted order.
fn wf_paths(dir: &Path) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = fs::read_dir(dir)
        .expect("the directory exists")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    paths.sort();
    paths
}

fn tests_dir(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests")
        .join(name)
}

/// Returns the number of a corpus file name: the digits before the first `_`.
/// `19b_no_runtime_bad.wf` has the number 19.
fn corpus_number(name: &str) -> Option<u64> {
    let head = name.split('_').next()?;
    let digits: String = head.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// Returns the next free number of `tests/programs`.
fn next_corpus_number() -> u64 {
    wf_paths(&tests_dir("programs"))
        .iter()
        .filter_map(|p| {
            p.file_name()
                .and_then(|n| corpus_number(&n.to_string_lossy()))
        })
        .max()
        .map_or(1, |n| n + 1)
}

/// Returns the pairs of `a` that `b` does not have. A pair counts one time
/// for each occurrence, so the result is the difference of two multisets.
fn minus(a: &Codes, b: &Codes) -> Codes {
    let mut rest = b.clone();
    let mut out = Vec::new();
    for pair in a {
        if let Some(i) = rest.iter().position(|q| q == pair) {
            rest.remove(i);
        } else {
            out.push(pair.clone());
        }
    }
    out
}

/// Checks one target. Returns the markers that the checker does not report
/// yet, or the reason that the target fails.
fn run(path: &Path, next: u64) -> Result<Codes, String> {
    let src = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let name = path
        .file_name()
        .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
    if src.contains("fn main(") {
        return Err(format!(
            "{name}: the file has `fn main`. Remove it: each bad case is a function \
             `bad_NAME()`, and a test block runs each clean case."
        ));
    }
    let checked = check_source(&name, &src, Options::from_markers(&src));
    let file = SourceFile::new(&name, src.as_str());
    let found = actual(&checked, &file);
    let (want, _) = expected(&src);
    let extra = minus(&found, &want);
    let missing = minus(&want, &found);
    let mut msg = String::new();
    if !extra.is_empty() {
        let _ = writeln!(
            msg,
            "{name}: errors with no marker: {extra:?}. This is a false positive, a broken \
             target, or the checker reports the error at another line (move the marker if \
             the new line is right)."
        );
        for d in &checked.diags {
            if extra.contains(&(file.line(d.span), d.code.to_string())) {
                msg.push_str(&d.render(&file));
            }
        }
    }
    write_disagreements(&name, &checked, &mut msg);
    if msg.is_empty() && missing.is_empty() {
        let _ = writeln!(
            msg,
            "{name}: the checker now reports every marker. Move it to \
             tests/programs/{next}_{name} and delete it from tests/ir_targets."
        );
    }
    if msg.is_empty() {
        Ok(missing)
    } else {
        Err(msg)
    }
}

#[test]
fn corpus_numbers_of_file_names() {
    assert_eq!(corpus_number("152_part_move_refs.wf"), Some(152));
    assert_eq!(corpus_number("19b_no_runtime_bad.wf"), Some(19));
    assert_eq!(corpus_number("r3rt2_match_through_ref.wf"), None);
    assert!(next_corpus_number() > 1);
}

#[test]
fn minus_counts_each_occurrence() {
    let pair = |l: usize, c: &str| (l, c.to_string());
    let a = vec![pair(1, "W0301"), pair(1, "W0301"), pair(2, "W0405")];
    let b = vec![pair(1, "W0301"), pair(3, "W0601")];
    assert_eq!(minus(&a, &b), vec![pair(1, "W0301"), pair(2, "W0405")]);
    assert_eq!(minus(&b, &a), vec![pair(3, "W0601")]);
}

#[test]
fn ir_targets() {
    let paths = wf_paths(&tests_dir("ir_targets"));
    assert!(!paths.is_empty(), "tests/ir_targets has no .wf file");
    let next = next_corpus_number();
    let mut failures = Vec::new();
    for path in &paths {
        let name = path
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        match run(path, next) {
            Ok(missing) => eprintln!("{name}: the checker does not report {missing:?} yet"),
            Err(e) => failures.push(e),
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} targets failed:\n{}",
        failures.len(),
        paths.len(),
        failures.join("\n")
    );
}
