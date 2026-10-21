//! Tests of the snapshots (plan `docs/plan/core-ir.md`, stage G3).
//!
//! The programs are in `tests/data`. That directory is not a root of tier 1.

use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use sha2::{Digest as _, Sha256};
use weft_gate::manifest::{Entry, Mode};
use weft_gate::snapshot::{self, Diag, Kind, Outcome, Pipeline, Settings, Violation};

fn data() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data")
}

fn entry(path: &str, mode: Mode) -> Entry {
    Entry {
        hash: format!("hash-of-{path}"),
        path: path.to_string(),
        set: "data".to_string(),
        mode,
        has_main: true,
        has_tests: false,
        others: Vec::new(),
    }
}

fn check(path: &str, mode: Mode) -> Outcome {
    snapshot::check(&data(), &entry(path, mode), Pipeline::Old)
}

fn diag(code: &str, file: &str, line: usize) -> Diag {
    Diag(code.to_string(), file.to_string(), line)
}

fn violation(file: &str, function: &str, relation: &str, args: &[&str]) -> Violation {
    Violation {
        file: file.to_string(),
        function: function.to_string(),
        relation: relation.to_string(),
        args: args.iter().map(ToString::to_string).collect(),
    }
}

/// Counts the facts of `relation` in the output of `weft facts PATH`.
fn facts_count(path: &str, relation: &str) -> usize {
    let full = data().join(path);
    let args = ["facts".to_string(), full.display().to_string()];
    let out = weft_cli::run(&args).expect("weft facts");
    assert_eq!(out.code, 0, "weft facts {path}: {}", out.stderr);
    let head = format!("{relation}(");
    out.text.lines().filter(|l| l.starts_with(&head)).count()
}

/// Checks that the counts of three relations agree with `weft facts`.
fn assert_counts_match_weft_facts(path: &str, o: &Outcome) {
    for rel in ["cfg_edge", "points_into", "scope_end"] {
        let expected = facts_count(path, rel);
        assert!(expected > 0, "{path} has no `{rel}` facts");
        assert_eq!(
            o.record.counts.get(rel).copied().unwrap_or(0),
            expected,
            "the count of `{rel}` in {path}"
        );
    }
}

/// Checks that the digest hash is the SHA-256 of the full digest, and that the
/// full digest has one line for each counted tuple.
fn assert_digest_is_consistent(o: &Outcome) {
    let hex = weft_gate::manifest::hex(&Sha256::digest(o.digest.as_bytes()));
    assert_eq!(o.record.digest, hex);
    let total: usize = o.record.counts.values().sum();
    assert_eq!(o.digest.lines().count(), total);
    let lines: Vec<&str> = o.digest.lines().collect();
    let mut sorted = lines.clone();
    sorted.sort_unstable();
    assert_eq!(lines, sorted, "the full digest is in sorted order");
}

#[test]
fn a_w0301_program_has_its_diagnostic_and_violation() {
    let o = check("w0301.wf", Mode::File);
    let r = &o.record;
    assert_eq!(r.kind, Kind::Ok, "{:?}", r.message);
    assert_eq!(r.path, "w0301.wf");
    assert_eq!(r.hash, "hash-of-w0301.wf");
    assert_eq!(r.pipeline, "old");
    assert_eq!(r.diagnostics, [diag("W0301", "w0301.wf", 8)]);
    assert_eq!(
        r.violations,
        [violation("w0301.wf", "bad", "error", &["first", "@8"])]
    );
    assert_counts_match_weft_facts("w0301.wf", &o);
    assert_digest_is_consistent(&o);
}

#[test]
fn a_w0601_package_has_its_diagnostic_and_violation() {
    let o = check("w0601_pkg", Mode::Package);
    let r = &o.record;
    assert_eq!(r.kind, Kind::Ok, "{:?}", r.message);
    let main = "w0601_pkg/src/main.wf";
    assert_eq!(r.diagnostics, [diag("W0601", main, 4)]);
    assert_eq!(
        r.violations,
        [violation(main, "forgets", "unconsumed", &["tx", "@4"])]
    );
    assert_counts_match_weft_facts("w0601_pkg", &o);
    assert_digest_is_consistent(&o);
}

#[test]
fn a_clean_program_has_no_diagnostics_and_no_violations() {
    let o = check("clean.wf", Mode::File);
    let r = &o.record;
    assert_eq!(r.kind, Kind::Ok, "{:?}", r.message);
    assert!(r.diagnostics.is_empty(), "{:?}", r.diagnostics);
    assert!(r.violations.is_empty(), "{:?}", r.violations);
    assert_counts_match_weft_facts("clean.wf", &o);
    assert_digest_is_consistent(&o);
}

#[test]
fn the_digest_names_nodes_variables_and_places() {
    let o = check("w0301.wf", Mode::File);
    let lines: Vec<&str> = o.digest.lines().collect();
    // `let first = &world.entities[0]` on line 6: `first` points into the
    // elements of `world.entities`.
    assert!(
        lines.contains(&r#"["w0301.wf","bad","points_into","first","world.entities[]"]"#),
        "{lines:#?}"
    );
    // No raw id stays in the digest.
    for l in &lines {
        for word in l.split(|c: char| !c.is_ascii_alphanumeric()) {
            let raw = ["n", "v", "p"].iter().any(|p| {
                word.strip_prefix(p)
                    .is_some_and(|d| !d.is_empty() && d.chars().all(|c| c.is_ascii_digit()))
            });
            assert!(!raw, "a raw id `{word}` in {l}");
        }
    }
    // A node is `@LINE:LABEL`.
    let edges: Vec<Vec<String>> = lines
        .iter()
        .map(|l| serde_json::from_str::<Vec<String>>(l).expect("a JSON array"))
        .filter(|t| t[2] == "cfg_edge")
        .collect();
    assert!(!edges.is_empty());
    for t in &edges {
        for node in &t[3..] {
            let (line, _label) = node
                .strip_prefix('@')
                .and_then(|n| n.split_once(':'))
                .unwrap_or_else(|| panic!("the node `{node}` is not `@LINE:LABEL`"));
            assert!(line.parse::<usize>().is_ok(), "{node}");
        }
    }
}

#[test]
fn the_record_is_the_same_on_each_run() {
    let a = check("w0601_pkg", Mode::Package);
    let b = check("w0601_pkg", Mode::Package);
    let mut ra = a.record.clone();
    let mut rb = b.record.clone();
    ra.ms = 0;
    rb.ms = 0;
    assert_eq!(ra, rb);
    assert_eq!(a.digest, b.digest);
}

#[test]
fn a_record_is_one_json_line_that_reads_back() {
    let o = check("w0301.wf", Mode::File);
    let line = o.record.to_json().expect("serialize");
    assert!(!line.contains('\n'));
    let back: snapshot::Record = serde_json::from_str(&line).expect("parse");
    assert_eq!(back, o.record);
}

#[test]
fn a_file_that_does_not_parse_gives_w0001() {
    let dir = tempfile::tempdir().expect("temporary directory");
    std::fs::write(dir.path().join("bad.wf"), "fn main( {\n").expect("write");
    let o = snapshot::check(dir.path(), &entry("bad.wf", Mode::File), Pipeline::Old);
    assert_eq!(o.record.kind, Kind::Ok, "{:?}", o.record.message);
    assert_eq!(o.record.diagnostics.len(), 1);
    assert_eq!(o.record.diagnostics[0].0, "W0001");
    assert_eq!(o.record.diagnostics[0].1, "bad.wf");
    assert!(o.record.counts.is_empty());
}

#[test]
fn a_file_that_cannot_be_read_gives_an_error_record() {
    let dir = tempfile::tempdir().expect("temporary directory");
    std::fs::write(dir.path().join("latin1.wf"), b"fn main() {} // \xe9\n").expect("write");
    let o = snapshot::check(dir.path(), &entry("latin1.wf", Mode::File), Pipeline::Old);
    assert_eq!(o.record.kind, Kind::Error);
    assert!(o.record.message.is_some());
    assert!(o.record.diagnostics.is_empty());
}

const fn settings(workers: usize, limit: Duration) -> Settings {
    Settings {
        pipeline: Pipeline::Old,
        groups: weft_sema::Groups::NONE,
        workers,
        limit,
    }
}

/// Runs the pool on `entries` and returns the outcomes in the order of the
/// entries.
fn pool(
    entries: Vec<Entry>,
    s: &Settings,
    work: impl Fn(&Entry) -> Outcome + Send + Sync + 'static,
) -> Vec<Outcome> {
    let n = entries.len();
    let mut out: Vec<Option<Outcome>> = (0..n).map(|_| None).collect();
    snapshot::run_pool(entries, s, Arc::new(work), |i, o| {
        assert!(out[i].is_none(), "two outcomes for entry {i}");
        out[i] = Some(o);
    })
    .expect("run the pool");
    out.into_iter()
        .enumerate()
        .map(|(i, o)| o.unwrap_or_else(|| panic!("no outcome for entry {i}")))
        .collect()
}

#[test]
fn a_panic_of_the_pipeline_gives_a_crash_record() {
    let base = data();
    let entries = vec![
        entry("w0301.wf", Mode::File),
        entry("crash.wf", Mode::File),
        entry("clean.wf", Mode::File),
    ];
    let out = pool(entries, &settings(2, Duration::from_secs(60)), move |e| {
        assert!(e.path != "crash.wf", "the pipeline breaks on {}", e.path);
        snapshot::check(&base, e, Pipeline::Old)
    });
    let kinds: Vec<Kind> = out.iter().map(|o| o.record.kind).collect();
    assert_eq!(kinds, [Kind::Ok, Kind::Crash, Kind::Ok]);
    let crash = &out[1].record;
    assert_eq!(crash.path, "crash.wf");
    assert_eq!(crash.hash, "hash-of-crash.wf");
    assert_eq!(crash.pipeline, "old");
    let message = crash.message.clone().unwrap_or_default();
    assert!(
        message.contains("the pipeline breaks on crash.wf"),
        "{message}"
    );
    assert!(crash.diagnostics.is_empty() && crash.counts.is_empty());
    assert_eq!(out[0].record.diagnostics, [diag("W0301", "w0301.wf", 8)]);
}

#[test]
fn a_program_past_the_time_limit_gives_a_timeout_record() {
    let entries = vec![
        entry("a.wf", Mode::File),
        entry("slow.wf", Mode::File),
        entry("b.wf", Mode::File),
        entry("c.wf", Mode::File),
    ];
    let out = pool(entries, &settings(2, Duration::from_millis(300)), |e| {
        if e.path == "slow.wf" {
            std::thread::sleep(Duration::from_secs(30));
        }
        let mut o = snapshot::check(&data(), &entry("clean.wf", Mode::File), Pipeline::Old);
        o.record.path.clone_from(&e.path);
        o
    });
    let kinds: Vec<Kind> = out.iter().map(|o| o.record.kind).collect();
    assert_eq!(kinds, [Kind::Ok, Kind::Timeout, Kind::Ok, Kind::Ok]);
    assert_eq!(out[1].record.path, "slow.wf");
    let paths: Vec<&str> = out.iter().map(|o| o.record.path.as_str()).collect();
    assert_eq!(paths, ["a.wf", "slow.wf", "b.wf", "c.wf"]);
}

#[test]
fn the_pool_runs_on_a_large_stack() {
    let entries = vec![entry("deep.wf", Mode::File)];
    let out = pool(entries, &settings(1, Duration::from_secs(60)), |e| {
        /// Recurses with a frame of about 4 KB, `n` times.
        fn deep(n: u32) -> u32 {
            let pad = std::hint::black_box([0u8; 4096]);
            if n == 0 {
                u32::from(pad[0])
            } else {
                deep(n - 1) + u32::from(pad[n as usize % 4096])
            }
        }
        // About 64 MB of stack: more than the 8 MB of a default thread.
        let depth = deep(16_000);
        let mut o = snapshot::check(&data(), &entry("clean.wf", Mode::File), Pipeline::Old);
        o.record.path = format!("{}:{depth}", e.path);
        o
    });
    assert_eq!(out[0].record.kind, Kind::Ok);
    assert_eq!(out[0].record.path, "deep.wf:0");
}

#[test]
fn the_violation_relations_are_the_sinks_of_the_spec() {
    let mut names = snapshot::violation_relations();
    names.sort_unstable();
    let mut spec: Vec<&str> = weft_check::bridge::VIOLATION_RELATIONS.to_vec();
    spec.sort_unstable();
    assert_eq!(names, spec);
}

/// The record without the fields that differ between the pipelines and the
/// runs: the name of the pipeline and the time.
fn same_result(r: &weft_gate::snapshot::Record) -> weft_gate::snapshot::Record {
    let mut r = r.clone();
    r.pipeline = String::new();
    r.ms = 0;
    r
}

/// The programs of `tests/data` that the tests of the `ir` pipeline check.
fn ir_entries() -> Vec<Entry> {
    vec![
        entry("w0301.wf", Mode::File),
        entry("clean.wf", Mode::File),
        entry("w0601_pkg", Mode::Package),
    ]
}

#[test]
fn with_the_stub_fact_generator_the_ir_record_is_the_old_record() {
    // Stage F1: the fact generator supports no group, so each program is out
    // of scope, also with every group on.
    let all = weft_sema::Groups::ALL;
    for e in ir_entries() {
        let old = snapshot::check(&data(), &e, Pipeline::Old);
        let ir = snapshot::check_with(&data(), &e, Pipeline::Ir, all);
        assert_eq!(ir.record.pipeline, "ir");
        assert_eq!(
            same_result(&ir.record),
            same_result(&old.record),
            "{}",
            e.path
        );
        let both = snapshot::check_both(&data(), &e, all);
        assert!(!both.in_scope, "{}", e.path);
        assert_eq!(both.old.record.pipeline, "old");
        assert_eq!(both.ir.record.pipeline, "ir");
        assert_eq!(same_result(&both.old.record), same_result(&old.record));
        assert_eq!(same_result(&both.ir.record), same_result(&old.record));
    }
    assert_eq!(Pipeline::parse("ir"), Some(Pipeline::Ir));
    assert_eq!(Pipeline::Ir.name(), "ir");
}

#[test]
fn the_gate_reports_no_coverage_with_the_stub_fact_generator() {
    use weft_gate::classify::Class;
    use weft_gate::oracle::{Cache, Row, Verdict};
    use weft_gate::report::{self, RunSettings};
    let interp = "interp-of-the-test";
    let mut cache = Cache::default();
    for e in ir_entries() {
        cache.insert(Row {
            hash: e.hash.clone(),
            engine: report::ORACLE_ENGINE,
            interp: interp.to_string(),
            verdict: Verdict::Clean,
            detail: String::new(),
            path: e.path.clone(),
        });
    }
    let manifest = weft_gate::manifest::Manifest {
        entries: ir_entries(),
        missing: Vec::new(),
    };
    let settings = RunSettings {
        workers: 2,
        baseline: false,
        groups: weft_sema::Groups::ALL,
        ..RunSettings::default()
    };
    let ledger = weft_gate::ledger::Ledger::default();
    let r = report::run(&data(), manifest, &cache, interp, &ledger, &settings, None)
        .unwrap_or_else(|e| panic!("the gate runs: {e}"));
    assert_eq!(r.rows.len(), 3);
    for row in &r.rows {
        assert!(!row.in_scope, "{}", row.path);
        assert_eq!(row.class, Class::Same, "{}", row.path);
    }
    assert_eq!(r.groups_on, "ABCDEF");
    let md = r.to_markdown();
    assert!(md.contains("| data | 0 | 3 | 0.0 % |"), "{md}");
    // The groups that the programs use: `w0301.wf` and `clean.wf` use group
    // A only.
    assert_eq!(r.used.len(), 3);
    assert!(md.contains("## Groups that the programs use"), "{md}");
}
