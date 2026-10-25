//! Tests of the oracle cache (plan `docs/plan/core-ir.md`, stage G4).
//!
//! The programs are in `tests/data`. That directory is not a root of tier 1.

use std::path::{Path, PathBuf};
use std::time::Duration;

use weft_gate::manifest::{Entry, Manifest, Mode};
use weft_gate::oracle::{self, Cache, Engine, Outcome, Row, Settings, Verdict};

fn data() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data")
}

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

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

/// Settings with one worker, on the worker thread.
fn settings(limit: Duration, max_steps: Option<u64>) -> Settings {
    Settings {
        workers: 1,
        limit,
        max_steps,
        ..Settings::default()
    }
}

/// Settings with child processes of the `weft-gate` program of this build.
fn isolated(limit: Duration, max_steps: Option<u64>, max_memory_mb: u64) -> Settings {
    Settings {
        workers: 2,
        limit,
        max_steps,
        max_memory_mb,
        exe: Some(PathBuf::from(env!("CARGO_BIN_EXE_weft-gate"))),
        engine: Engine::Ast,
        fact_oracle: false,
    }
}

/// Runs the entries on the pool and gives the outcomes in the order of the
/// entries.
fn run_all(base: &Path, entries: Vec<Entry>, s: &Settings) -> Vec<Outcome> {
    let n = entries.len();
    let mut out: Vec<Option<Outcome>> = vec![None; n];
    oracle::run_all(base, entries, s, |i, o| {
        assert!(out[i].is_none(), "two outcomes for entry {i}");
        out[i] = Some(o);
    })
    .expect("run the pool");
    out.into_iter()
        .enumerate()
        .map(|(i, o)| o.unwrap_or_else(|| panic!("no outcome for entry {i}")))
        .collect()
}

fn verdict_of(path: &str) -> Outcome {
    oracle::run_entry(
        &data(),
        &entry(path),
        &settings(oracle::LIMIT, Some(1_000_000)),
    )
}

#[test]
fn a_dangling_read_gives_fault() {
    let o = verdict_of("oracle_dangling.wf");
    assert_eq!(o.verdict, Verdict::Fault, "{}", o.detail);
    assert!(o.detail.contains("dangling"), "{}", o.detail);
    assert!(o.detail.contains("seed 1, workers 1"), "{}", o.detail);
}

#[test]
fn an_index_out_of_bounds_gives_benign() {
    let o = verdict_of("oracle_bounds.wf");
    assert_eq!(o.verdict, Verdict::Benign, "{}", o.detail);
    assert!(o.detail.contains("out of bounds"), "{}", o.detail);
}

#[test]
fn a_fail_gives_fail() {
    let o = verdict_of("oracle_fail.wf");
    assert_eq!(o.verdict, Verdict::Fail, "{}", o.detail);
    assert!(o.detail.contains("stop here"), "{}", o.detail);
}

#[test]
fn a_clean_program_gives_clean() {
    let o = verdict_of("clean.wf");
    assert_eq!(o.verdict, Verdict::Clean, "{}", o.detail);
}

#[test]
fn no_main_and_no_test_gives_not_runnable() {
    let o = verdict_of("oracle_no_main.wf");
    assert_eq!(o.verdict, Verdict::NotRunnable, "{}", o.detail);
}

#[test]
fn a_program_with_test_blocks_runs_the_tests() {
    let o = verdict_of("oracle_tests.wf");
    assert_eq!(o.verdict, Verdict::Fail, "{}", o.detail);
    assert!(o.detail.contains("test `stops`"), "{}", o.detail);
    assert!(o.detail.contains("the test stops here"), "{}", o.detail);
}

#[test]
fn a_package_runs() {
    let o = oracle::run_entry(
        &data(),
        &Entry {
            mode: Mode::Package,
            ..entry("w0601_pkg")
        },
        &settings(oracle::LIMIT, Some(1_000_000)),
    );
    assert_ne!(o.verdict, Verdict::NotRunnable, "{}", o.detail);
}

#[test]
fn a_file_that_cannot_be_read_gives_not_runnable() {
    let dir = tempfile::tempdir().expect("temp dir");
    std::fs::write(dir.path().join("latin1.wf"), b"fn main() {} // \xe9\n").expect("write");
    let o = oracle::run_entry(
        dir.path(),
        &entry("latin1.wf"),
        &settings(oracle::LIMIT, None),
    );
    assert_eq!(o.verdict, Verdict::NotRunnable, "{}", o.detail);
    assert!(!o.detail.contains(&dir.path().display().to_string()));
}

#[test]
fn an_endless_loop_gives_timeout_at_the_step_limit() {
    let o = verdict_of("oracle_loop.wf");
    assert_eq!(o.verdict, Verdict::Timeout, "{}", o.detail);
    assert!(o.detail.contains("step limit"), "{}", o.detail);
}

#[test]
fn an_endless_loop_gives_timeout_at_the_time_limit() {
    // No step limit: the parent stops the child after the time limit of each
    // run.
    let s = isolated(Duration::from_millis(300), None, 2048);
    let out = run_all(&data(), vec![entry("oracle_loop.wf")], &s);
    assert_eq!(out[0].verdict, Verdict::Timeout, "{}", out[0].detail);
    assert!(
        out[0]
            .detail
            .contains("seed 1, workers 1: the run takes more than 300 ms"),
        "{}",
        out[0].detail
    );
}

#[test]
fn an_endless_recursion_gives_timeout_at_the_memory_limit() {
    let s = isolated(Duration::from_secs(30), None, 200);
    let out = run_all(&data(), vec![entry("oracle_recursion.wf")], &s);
    assert_eq!(out[0].verdict, Verdict::Timeout, "{}", out[0].detail);
    assert!(
        out[0].detail.contains("more than 200 MB of memory"),
        "{}",
        out[0].detail
    );
}

#[test]
fn a_child_process_gives_the_verdict_of_a_worker_thread() {
    let names = [
        "oracle_dangling.wf",
        "oracle_bounds.wf",
        "oracle_fail.wf",
        "clean.wf",
        "oracle_no_main.wf",
        "oracle_tests.wf",
        "oracle_loop.wf",
        "gone.wf",
    ];
    let entries: Vec<Entry> = names.iter().map(|n| entry(n)).collect();
    let steps = Some(1_000_000);
    let child = run_all(
        &data(),
        entries.clone(),
        &isolated(oracle::LIMIT, steps, 2048),
    );
    let thread = run_all(&data(), entries, &settings(oracle::LIMIT, steps));
    assert_eq!(child, thread);
}

#[test]
fn the_verdict_is_the_first_in_the_order() {
    use Verdict::{Benign, Clean, Fail, Fault, NotRunnable, Timeout};
    assert_eq!(
        Verdict::ALL,
        [Fault, Timeout, Fail, Benign, Clean, NotRunnable]
    );
    assert!(Fault < Timeout && Timeout < Fail && Fail < Benign && Benign < Clean);
    for v in Verdict::ALL {
        assert_eq!(Verdict::parse(v.name()), Some(v));
    }
    assert_eq!(Verdict::NotRunnable.name(), "not-runnable");
}

#[test]
fn the_six_configurations_are_those_of_the_harness() {
    assert_eq!(
        oracle::CONFIGS,
        [(1, 1), (2, 4), (3, 2), (7, 4), (11, 1), (42, 3)]
    );
}

/// The texts of the Python list `NAME = [...]` in `text`.
fn python_list(text: &str, name: &str) -> Vec<String> {
    let start = text
        .find(&format!("\n{name} = ["))
        .unwrap_or_else(|| panic!("no list `{name}`"));
    let rest = &text[start..];
    let end = rest.find(']').expect("the end of the list");
    rest[..end]
        .split('"')
        .skip(1)
        .step_by(2)
        .map(ToString::to_string)
        .collect()
}

#[test]
fn the_benign_texts_are_those_of_the_harness() {
    let file = repo().join("tools/gate/gen/harness.py");
    let text = std::fs::read_to_string(&file).expect("read harness.py");
    let texts = python_list(&text, "BENIGN");
    assert_eq!(texts.len(), 9);
    assert_eq!(oracle::BENIGN.to_vec(), texts);
    assert!(oracle::is_benign(
        "runtime error: index 3 is out of bounds (length 1)"
    ));
    assert!(oracle::is_benign("runtime error: integer overflow"));
    assert!(!oracle::is_benign(
        "runtime error: oracle: a read of a freed cell (a dangling reference)"
    ));
}

#[test]
fn the_engine_names() {
    assert_eq!(Engine::parse("ast"), Some(Engine::Ast));
    assert_eq!(Engine::Ast.name(), "ast");
    assert_eq!(Engine::parse("ir"), Some(Engine::Ir));
    assert_eq!(Engine::parse("mir"), None);
    assert_eq!(oracle::cache_name(Engine::Ast), "oracle-ast.tsv");
}

fn row(hash: &str, interp: &str, verdict: Verdict, path: &str) -> Row {
    Row {
        hash: hash.to_string(),
        engine: Engine::Ast,
        interp: interp.to_string(),
        verdict,
        detail: "seed 1, workers 1: a\ttab and a\nline feed".to_string(),
        path: path.to_string(),
    }
}

#[test]
fn the_cache_reads_back_its_text() {
    let mut cache = Cache::default();
    cache.insert(row("h2", "i1", Verdict::Clean, "b c:d.wf"));
    cache.insert(row("h1", "i1", Verdict::Fault, "a.wf"));
    let text = cache.to_tsv();
    assert!(text.starts_with(oracle::HEADER));
    // The rows are in the order of the paths. A tab or a line feed in a
    // detail becomes a space.
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 3);
    assert!(lines[1].starts_with("h1\tast\ti1\tfault\t"));
    assert!(lines[1].ends_with("\ta.wf"));
    assert_eq!(lines[1].split('\t').count(), 6);
    let back = Cache::from_tsv(&text).expect("read the cache");
    assert_eq!(back.to_tsv(), text);
    assert_eq!(back.len(), 2);
    let r = back.get("h2", Engine::Ast, "i1").expect("a row");
    assert_eq!(r.path, "b c:d.wf");
    assert_eq!(r.detail, "seed 1, workers 1: a tab and a line feed");
}

#[test]
fn a_row_of_another_interpreter_is_a_miss() {
    let mut cache = Cache::default();
    cache.insert(row("h1", "old-interp", Verdict::Fault, "a.wf"));
    assert!(cache.get("h1", Engine::Ast, "old-interp").is_some());
    assert!(cache.get("h1", Engine::Ast, "new-interp").is_none());
    assert!(cache.get("h2", Engine::Ast, "old-interp").is_none());
}

#[test]
fn a_bad_cache_line_is_an_error() {
    let text = format!("{}\nh1\tast\ti1\tmaybe\tx\ta.wf\n", oracle::HEADER);
    assert!(Cache::from_tsv(&text).is_err());
    let text = format!("{}\nh1\tast\ti1\n", oracle::HEADER);
    assert!(Cache::from_tsv(&text).is_err());
}

#[test]
fn a_cache_hit_skips_the_run() {
    // The file does not exist, so a run gives `not-runnable`. The cached row
    // gives `fault`.
    let mut cache = Cache::default();
    cache.insert(row("hash-of-gone.wf", "i1", Verdict::Fault, "gone.wf"));
    let entries = vec![entry("gone.wf"), entry("clean.wf")];
    let s = settings(oracle::LIMIT, Some(1_000_000));
    let mut rows = Vec::new();
    let summary = oracle::oracle(&data(), entries, &cache, Engine::Ast, "i1", &s, |r, hit| {
        rows.push((r, hit));
    })
    .expect("run the oracle");
    assert_eq!((summary.hits, summary.runs), (1, 1));
    rows.sort_by(|a, b| a.0.path.cmp(&b.0.path));
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].0.path, "clean.wf");
    assert_eq!((rows[0].0.verdict, rows[0].1), (Verdict::Clean, false));
    assert_eq!(rows[0].0.interp, "i1");
    assert_eq!(rows[0].0.hash, "hash-of-clean.wf");
    assert_eq!((rows[1].0.verdict, rows[1].1), (Verdict::Fault, true));
    assert_eq!(summary.counts.get(&Verdict::Fault), Some(&1));
    assert_eq!(summary.counts.get(&Verdict::Clean), Some(&1));
}

#[test]
fn the_interpreter_hash_follows_its_sources() {
    let dir = tempfile::tempdir().expect("temp dir");
    let src = dir.path().join(oracle::INTERP_SRC);
    std::fs::create_dir_all(src.join("machine")).expect("make dirs");
    std::fs::write(src.join("lib.rs"), "fn a() {}\n").expect("write");
    std::fs::write(src.join("machine/mod.rs"), "fn b() {}\n").expect("write");
    let h1 = oracle::interp_hash(dir.path()).expect("hash");
    assert_eq!(h1.len(), 64);
    assert_eq!(oracle::interp_hash(dir.path()).expect("hash"), h1);
    std::fs::write(src.join("machine/mod.rs"), "fn c() {}\n").expect("write");
    let h2 = oracle::interp_hash(dir.path()).expect("hash");
    assert_ne!(h1, h2);
    std::fs::write(src.join("machine/new.rs"), "").expect("write");
    assert_ne!(oracle::interp_hash(dir.path()).expect("hash"), h2);
}

/// The committed cache of each engine has a row for each program of tier 1,
/// with the hash of the interpreter sources of today.
#[test]
fn the_committed_caches_cover_tier_1() {
    let repo = repo();
    let manifest = std::fs::read_to_string(repo.join("tests/gate/manifest-tier1.tsv"))
        .expect("read the tier-1 manifest");
    let manifest = Manifest::from_tsv(&manifest).expect("parse the tier-1 manifest");
    let interp = oracle::interp_hash(&repo).expect("hash the interpreter sources");
    for engine in Engine::ALL {
        let name = oracle::cache_name(engine);
        let file = repo.join("tests/gate").join(&name);
        let text = std::fs::read_to_string(&file).unwrap_or_else(|e| panic!("read {name}: {e}"));
        let cache = Cache::from_tsv(&text).unwrap_or_else(|e| panic!("parse {name}: {e}"));
        let missing: Vec<&str> = manifest
            .entries
            .iter()
            .filter(|e| cache.get(&e.hash, engine, &interp).is_none())
            .map(|e| e.path.as_str())
            .collect();
        assert!(
            missing.is_empty(),
            "tests/gate/{name} has no row for {} programs of tier 1 with the \
             interpreter hash {interp} (first: {:?}). The interpreter sources or the \
             manifest changed. Run `cargo run -p weft-gate --release -- oracle --engine {} \
             --tier 1` and commit the file.",
            missing.len(),
            missing.first(),
            engine.name()
        );
        assert_eq!(
            cache.len(),
            manifest.entries.len(),
            "only tier-1 rows in {name}"
        );
    }
}

/// The fact oracle (stage F9, `docs/ir.md` 8.5): a program in scope that the
/// `ir` pipeline accepts runs with it and passes; a program that the `ir`
/// pipeline rejects, and a program out of scope (a loop, group B), do not
/// run. The child processes get `--fact-oracle`.
#[test]
fn the_fact_oracle_runs_the_accepted_programs_of_the_scope() {
    let on_thread = Settings {
        fact_oracle: true,
        ..settings(oracle::LIMIT, Some(1_000_000))
    };
    let child = Settings {
        fact_oracle: true,
        ..isolated(oracle::LIMIT, Some(1_000_000), oracle::MAX_MEMORY_MB)
    };
    for s in [&on_thread, &child] {
        let out = run_all(
            &data(),
            vec![
                entry("clean.wf"),
                entry("w0301.wf"),
                entry("oracle_loop.wf"),
            ],
            s,
        );
        let classes: Vec<oracle::FactClass> = out.iter().map(oracle::fact_class).collect();
        assert_eq!(
            classes,
            vec![
                oracle::FactClass::Pass,
                oracle::FactClass::Rejected,
                oracle::FactClass::OutOfScope
            ],
            "{out:?}"
        );
    }
    // A failure of the fact oracle is a failure class.
    let failed = Outcome {
        verdict: Verdict::Fault,
        detail: "seed 1, workers 1: runtime error: fact oracle (C4): in `main`".to_string(),
    };
    assert!(oracle::fact_class(&failed).is_failure());
}
