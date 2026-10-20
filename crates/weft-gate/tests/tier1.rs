//! The diff gate on tier 1 (plan `docs/plan/core-ir.md`, §1 rule 3 and stage G5).
//!
//! The test checks each program of tier 1, reads the oracle verdicts from the
//! committed cache `tests/gate/oracle-ast.tsv`, classifies each program and
//! writes the report to `target/gate/report-tier1.md`. A blocker of §2.5 makes
//! the test fail. The test does not run the interpreter: if the cache has no
//! verdict for the current interpreter sources, the test fails and tells you
//! the command that makes the cache again.
//!
//! Set `WEFT_GATE_SKIP=1` to skip the test in a quick local loop.

use std::path::{Path, PathBuf};
use std::time::Instant;

use weft_gate::classify::Class;
use weft_gate::manifest::{Entry, Mode};
use weft_gate::oracle::{Cache, Engine, Row, Verdict};
use weft_gate::report::{self, RunSettings};
use weft_gate::Error;

fn repo() -> PathBuf {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    std::fs::canonicalize(&dir).unwrap_or(dir)
}

fn skip() -> bool {
    if std::env::var_os("WEFT_GATE_SKIP").is_some_and(|v| v == "1") {
        eprintln!("skipped: WEFT_GATE_SKIP=1");
        return true;
    }
    false
}

#[test]
fn tier1_has_no_blocker() {
    if skip() {
        return;
    }
    let repo = repo();
    let start = Instant::now();
    let r = report::run_tier1(&repo, &RunSettings::default())
        .unwrap_or_else(|e| panic!("the gate cannot run: {e}"));
    let out = repo.join("target/gate/report-tier1.md");
    if let Some(dir) = out.parent() {
        std::fs::create_dir_all(dir).unwrap_or_else(|e| panic!("make {}: {e}", dir.display()));
    }
    std::fs::write(&out, r.to_markdown())
        .unwrap_or_else(|e| panic!("write {}: {e}", out.display()));
    let counts: Vec<String> = r
        .class_counts()
        .iter()
        .map(|(c, n)| format!("{n} {}", c.name()))
        .collect();
    eprintln!(
        "tier 1: {} programs in {:.1} s: {}; report in {}",
        r.rows.len(),
        start.elapsed().as_secs_f64(),
        counts.join(", "),
        out.display()
    );
    assert!(r.rows.len() > 3000, "tier 1 has {} programs", r.rows.len());
    assert!(
        r.passes(),
        "the gate has {} blockers (see {}):\n{}",
        r.blockers.len(),
        out.display(),
        r.blockers.join("\n")
    );
    // Before stage F1 the `ir` side is the old pipeline, so each program is
    // `same` or `open`.
    let other: Vec<String> = r
        .rows
        .iter()
        .filter(|row| !matches!(row.class, Class::Same | Class::Open))
        .map(|row| format!("{} {}", row.class.name(), row.path))
        .collect();
    assert!(other.is_empty(), "{}", other.join("\n"));
}

fn entry(path: &str) -> Entry {
    Entry {
        hash: format!("hash-of-{path}"),
        path: path.to_string(),
        set: "probes".to_string(),
        mode: Mode::File,
        has_main: true,
        has_tests: false,
        others: Vec::new(),
    }
}

#[test]
fn a_stale_cache_key_gives_a_clear_message() {
    let mut cache = Cache::default();
    cache.insert(Row {
        hash: "hash-of-a.wf".to_string(),
        engine: Engine::Ast,
        interp: "old-interpreter".to_string(),
        verdict: Verdict::Clean,
        detail: String::new(),
        path: "a.wf".to_string(),
    });
    let entries = [entry("a.wf"), entry("b.wf")];
    let found = report::verdicts(&entries, &cache, Engine::Ast, "new-interpreter");
    let Err(e @ Error::Stale { .. }) = found else {
        panic!("a stale key is not an error: {found:?}");
    };
    let text = e.to_string();
    for part in [
        "2 programs",
        "a.wf",
        "new-interpreter",
        "weft-gate --release -- oracle",
    ] {
        assert!(text.contains(part), "the message has no `{part}`: {text}");
    }
    let ok = report::verdicts(&entries[..1], &cache, Engine::Ast, "old-interpreter");
    assert_eq!(ok.ok(), Some(vec![Verdict::Clean]));
}
