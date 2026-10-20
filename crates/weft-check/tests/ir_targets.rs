//! The acceptance targets of the core IR (`tests/ir_targets`).

#![allow(clippy::unwrap_used, clippy::expect_used)]
//!
//! Each file holds bad cases that the checker accepts today and that fault at
//! run time with the oracle (review round 3), controls that the checker finds
//! today, and clean cases that its test blocks run. The fix of each bad case is
//! in fact generation, so the core IR must find them (ADRs 0003, 0005, 0006 and
//! 0007, and `docs/traceability.md`). A line that ends with `//~ CODE ...`
//! expects those error codes on that line, as in `tests/programs`. The markers
//! give the correct result, not the result of the checker today.
//!
//! The test expects the checker to miss at least one marker in each file. For
//! each file, in sorted order:
//!
//! - An error at a line with no such marker fails the test. This is a false
//!   positive, a broken target, or an error at another line. If the new line
//!   is correct, move the marker.
//! - For each body, the production checker must agree with the Datalog spec.
//! - If the checker reports each marker, the test fails: the target is done.
//!   Move the file to `tests/programs` with the number that the message gives,
//!   and delete it from `tests/ir_targets`. Two files that are done at the same
//!   time get two numbers. The file needs no other change: its test blocks run
//!   the clean cases, and no test block runs a bad case.
//! - Else the file passes. The test prints the markers that the checker does
//!   not report yet. To see them, run
//!   `cargo test -p weft-check --test ir_targets -- --nocapture`.
//!
//! The directory must hold at least one `.wf` file, and no file can have a
//! function `main` (the test parses the file to find it). The test `ir_targets`
//! of `weft-interp` shows that each target is real: each bad case faults, and
//! each clean case runs clean.

mod common;

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use common::{actual, expected, write_disagreements, Codes};
use weft_check::check_source;
use weft_sema::Options;
use weft_syntax::ast::{Item, ItemKind};
use weft_syntax::{parse_file, SourceFile};

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

/// True if an item is a function `main`, or a module that holds one.
fn has_main(item: &Item) -> bool {
    match &item.kind {
        ItemKind::Fn(f) => f.name.name == "main",
        ItemKind::Mod(m) => m.items.iter().any(has_main),
        _ => false,
    }
}

/// The result of one target.
#[derive(Debug, PartialEq)]
enum Outcome {
    /// The markers that the checker does not report yet.
    Open(Codes),
    /// The checker reports each marker.
    Done,
}

/// Checks the source of one target. Returns its outcome, or the reason that it
/// fails.
fn run(name: &str, src: &str) -> Result<Outcome, String> {
    let parsed = parse_file(src).map_err(|e| format!("{name}: parse error: {e}"))?;
    if parsed.items.iter().any(has_main) {
        return Err(format!(
            "{name}: the file has `fn main`. Remove it: each bad case is a function \
             `bad_NAME()`, and a test block runs each clean case."
        ));
    }
    let checked = check_source(name, src, Options::from_markers(src));
    let file = SourceFile::new(name, src);
    let found = actual(&checked, &file);
    let (want, _) = expected(src);
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
    write_disagreements(name, &checked, &mut msg);
    if !msg.is_empty() {
        Err(msg)
    } else if missing.is_empty() {
        Ok(Outcome::Done)
    } else {
        Ok(Outcome::Open(missing))
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
fn main_is_found_by_the_parser() {
    let has = |src: &str| {
        run("t.wf", src)
            .err()
            .is_some_and(|e| e.contains("has `fn main`"))
    };
    assert!(has("fn main () { }\n"));
    assert!(has("mod m { fn main() { } }\n"));
    assert!(!has(
        "// no fn main() here\nfn bad_a() { print(1) }   //~ W0301\n"
    ));
}

#[test]
fn a_target_is_open_until_each_marker_is_found() {
    let src = "fn bad_a() { print(1) }   //~ W0301\n";
    assert_eq!(
        run("t.wf", src),
        Ok(Outcome::Open(vec![(1, "W0301".into())]))
    );
    assert_eq!(run("t.wf", "fn ok_a() { print(1) }\n"), Ok(Outcome::Done));
}

#[test]
fn ir_targets() {
    let paths = wf_paths(&tests_dir("ir_targets"));
    assert!(!paths.is_empty(), "tests/ir_targets has no .wf file");
    let mut next = next_corpus_number();
    let mut failures = Vec::new();
    for path in &paths {
        let name = path
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        let src = fs::read_to_string(path).map_err(|e| format!("{name}: {e}"));
        match src.and_then(|src| run(&name, &src)) {
            Ok(Outcome::Open(missing)) => {
                eprintln!("{name}: the checker does not report {missing:?} yet");
            }
            Ok(Outcome::Done) => {
                failures.push(format!(
                    "{name}: the checker now reports every marker. Move it to \
                     tests/programs/{next}_{name} and delete it from tests/ir_targets."
                ));
                next += 1;
            }
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
