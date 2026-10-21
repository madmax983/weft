//! Tests of the `ir-build` command (plan `docs/plan/core-ir.md`, stage B12):
//! it builds and verifies the IR of each program, and counts the outcomes.

use std::sync::Arc;
use std::time::Duration;

use weft_gate::ir_build::{self, Outcome, Summary};
use weft_gate::manifest::{Entry, Mode};
use weft_gate::{pool, thir};

fn entry(path: &str) -> Entry {
    Entry {
        hash: format!("hash-of-{path}"),
        path: path.to_string(),
        set: "data".to_string(),
        mode: Mode::File,
        has_main: true,
        has_tests: false,
        others: Vec::new(),
    }
}

/// Writes the programs into a new directory and returns it with their entries.
fn programs(files: &[(&str, &str)]) -> (tempfile::TempDir, Vec<Entry>) {
    let dir = tempfile::tempdir().unwrap_or_else(|e| panic!("temp dir: {e}"));
    for (name, text) in files {
        std::fs::write(dir.path().join(name), text).unwrap_or_else(|e| panic!("write {name}: {e}"));
    }
    let entries = files.iter().map(|(name, _)| entry(name)).collect();
    (dir, entries)
}

const GOOD: &str = "fn f(x: u64) -> u64 { x + 1 }\nfn main() { print(f(1)) }\n";
const TYPE_ERROR: &str = "fn main() { let x: u64 = true }\n";
const NO_PARSE: &str = "fn main( {\n";

#[test]
fn ir_build_counts_the_bodies_of_each_program() {
    let (dir, entries) = programs(&[
        ("good.wf", GOOD),
        ("type_error.wf", TYPE_ERROR),
        ("no_parse.wf", NO_PARSE),
    ]);
    pool::install_panic_hook();
    let sum = ir_build::run(dir.path(), entries, 2, Duration::from_secs(60), |_| {})
        .unwrap_or_else(|e| panic!("ir-build: {e}"));
    assert_eq!(sum.programs, 3, "{sum:?}");
    assert_eq!(sum.loaded, 2, "{sum:?}");
    assert_eq!(sum.load_errors, 1, "{sum:?}");
    assert_eq!(sum.ir.built, 2, "{sum:?}");
    assert_eq!(sum.ir.no_ir, 1, "{sum:?}");
    assert_eq!(
        sum.ir.no_ir_reasons.get("a type error").copied(),
        Some(1),
        "{sum:?}"
    );
    assert!(sum.ir.unsupported.is_empty(), "{sum:?}");
    assert!(
        sum.ir_broken.is_empty() && sum.crashes.is_empty(),
        "{sum:?}"
    );
    assert!(sum.holds(), "{sum:?}");
    let text = sum.to_markdown("test");
    assert!(text.contains("2 bodies built, 1 with no IR"), "{text}");
    assert!(text.contains("| a type error | 1 |"), "{text}");
}

#[test]
fn a_panic_does_not_hide_the_other_programs() {
    let (dir, entries) = programs(&[("a.wf", GOOD), ("panics.wf", GOOD), ("b.wf", GOOD)]);
    pool::install_panic_hook();
    let base = dir.path().to_path_buf();
    let work: pool::Work<Outcome> = Arc::new(move |e: &Entry| {
        assert!(e.path != "panics.wf", "a bug of the builder");
        ir_build::check(&base, e)
    });
    let sum = ir_build::run_work(entries, 1, Duration::from_secs(60), work, |_| {})
        .unwrap_or_else(|e| panic!("ir-build: {e}"));
    assert_eq!(sum.programs, 3, "{sum:?}");
    assert_eq!(sum.ir.built, 4, "{sum:?}");
    assert_eq!(sum.crashes.len(), 1, "{sum:?}");
    assert!(sum.crashes[0].starts_with("panics.wf: "), "{sum:?}");
    assert!(sum.crashes[0].contains("a bug of the builder"), "{sum:?}");
    assert!(!sum.holds());
}

#[test]
fn a_broken_rule_or_an_unsupported_body_fails_and_a_timeout_does_not() {
    let ok = Outcome {
        ir: thir::IrCounts {
            built: 1,
            ..thir::IrCounts::default()
        },
        ..Outcome::default()
    };
    let mut sum = Summary::default();
    sum.add("ok.wf", ok.clone());
    sum.timeouts.push("slow.wf".to_string());
    assert!(sum.holds(), "{sum:?}");
    let mut broken = ok.clone();
    broken.ir.broken = vec!["V6: body b0, bb1, _2: a cell leaks".to_string()];
    let mut with_broken = sum.clone();
    with_broken.add("broken.wf", broken);
    assert!(!with_broken.holds());
    assert_eq!(with_broken.ir_broken.len(), 1);
    assert!(with_broken
        .to_markdown("t")
        .contains("broken: `broken.wf: V6"));
    let mut unsupported = ok;
    unsupported.ir.unsupported.insert("x (B12)".to_string(), 1);
    let mut with_unsupported = sum;
    with_unsupported.add("u.wf", unsupported);
    assert!(!with_unsupported.holds());
}

#[test]
fn the_slowest_programs_are_listed() {
    let mut sum = Summary::default();
    for (i, ms) in [5u64, 50, 1].into_iter().enumerate() {
        sum.add(
            &format!("p{i}.wf"),
            Outcome {
                build_ms: ms,
                analyze_ms: 2 * ms,
                ..Outcome::default()
            },
        );
    }
    assert_eq!(
        sum.slowest
            .iter()
            .map(|s| s.path.as_str())
            .collect::<Vec<_>>(),
        vec!["p1.wf", "p0.wf", "p2.wf"]
    );
    assert_eq!(sum.build_ms, 56);
    assert_eq!(sum.analyze_ms, 112);
}
