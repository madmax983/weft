//! Tests of the engine differential (plan `docs/plan/core-ir.md`, stage I5,
//! `docs/ir.md` 8.5).
//!
//! The programs are in `tests/data`. The full differential on a tier is the
//! command `weft-gate engines --tier 1|2` (a release build); the test
//! `the_engine_differential_of_tier_1_has_no_unledgered_difference` runs it
//! when it is asked for (`--ignored`).

use std::path::{Path, PathBuf};
use std::time::Duration;

use weft_gate::engines::{self, Difference, Kind, Result1, Rules, Runs};
use weft_gate::ledger::{EntryClass, Ledger};
use weft_gate::manifest::{Entry, Mode};
use weft_gate::oracle::{self, Engine, Observation, Settings, Verdict};

fn data() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data")
}

fn repo() -> PathBuf {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    std::fs::canonicalize(&dir).unwrap_or(dir)
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

/// Settings with one worker, on this thread.
fn on_thread() -> Settings {
    Settings {
        workers: 1,
        max_steps: Some(1_000_000),
        ..Settings::default()
    }
}

/// An observation that ends with `status` and `message`, with `output`.
fn obs(config: usize, status: &str, message: &str, output: &str) -> Observation {
    let verdict = match status {
        "ok" => Verdict::Clean,
        "timeout" | "step-limit" => Verdict::Timeout,
        _ => Verdict::Fault,
    };
    let mut o = Observation::bare(config, verdict, status, message);
    // An observation with an output: the hash is of the output.
    let line = o
        .to_line()
        .unwrap_or_default()
        .replace("\"output\":\"\"", &format!("\"output\":{output:?}"));
    o = Observation::parse_line(&line).unwrap_or(o);
    o.output_hash = format!("hash of {output}");
    o
}

const fn diff(ast: Observation, ir: Observation) -> Difference {
    Difference {
        config: ast.config,
        ast: Some(ast),
        ir: Some(ir),
    }
}

/// A ledger from its text.
fn ledger(text: &str) -> Ledger {
    Ledger::from_toml(text).unwrap_or_else(|e| panic!("the ledger does not parse: {e}"))
}

#[test]
fn the_ir_engine_has_a_name_and_a_cache() {
    assert_eq!(Engine::parse("ir"), Some(Engine::Ir));
    assert_eq!(Engine::Ir.name(), "ir");
    assert_eq!(oracle::cache_name(Engine::Ir), "oracle-ir.tsv");
    assert_eq!(Engine::ALL, [Engine::Ast, Engine::Ir]);
}

#[test]
fn the_oracle_of_the_ir_engine_finds_a_dangling_read() {
    let s = Settings {
        engine: Engine::Ir,
        ..on_thread()
    };
    let o = oracle::run_entry(&data(), &entry("oracle_dangling.wf"), &s);
    assert_eq!(o.verdict, Verdict::Fault, "{}", o.detail);
    assert!(o.detail.contains("dangling"), "{}", o.detail);
}

#[test]
fn a_clean_program_runs_the_same_on_both_engines() {
    let runs = engines::run_both(&data(), &entry("clean.wf"), &on_thread());
    assert_eq!(runs.ast.len(), oracle::CONFIGS.len(), "{runs:?}");
    assert_eq!(runs.ir.len(), oracle::CONFIGS.len(), "{runs:?}");
    assert_eq!(runs.ast[0].output, "1\n");
    assert_eq!(runs.ir[0].fallback, None);
    assert_eq!(engines::compare(&runs.ast, &runs.ir), None);
}

#[test]
fn an_operand_read_where_it_is_written_differs_in_the_output() {
    let runs = engines::run_both(&data(), &entry("engines_choice_a.wf"), &on_thread());
    let d = engines::compare(&runs.ast, &runs.ir).expect("the engines differ");
    assert_eq!(d.config, 0);
    let (a, i) = (d.ast.clone().expect("ast"), d.ir.clone().expect("ir"));
    assert_eq!((a.output.as_str(), i.output.as_str()), ("6\n", "2\n"));
    assert!(Kind::ChoiceA.fits(&d));
    assert!(!Kind::Capture.fits(&d));
    assert!(!Kind::Timeout.fits(&d));
}

#[test]
fn a_child_process_gives_an_observation_for_each_run() {
    let exe = PathBuf::from(env!("CARGO_BIN_EXE_weft-gate"));
    let s = Settings {
        workers: 1,
        engine: Engine::Ir,
        ..Settings::default()
    };
    let (outcome, seen) = oracle::run_isolated_observed(&exe, &data(), &entry("clean.wf"), &s);
    assert_eq!(outcome.verdict, Verdict::Clean, "{}", outcome.detail);
    let configs: Vec<usize> = seen.iter().map(|o| o.config).collect();
    assert_eq!(configs, vec![0, 1, 2, 3, 4, 5]);
    assert!(seen.iter().all(|o| o.status == "ok" && o.output == "1\n"));
    // A run that the parent stops at the time limit is a `timeout`.
    let slow = Settings {
        limit: Duration::from_millis(300),
        max_steps: None,
        ..s
    };
    let (outcome, seen) =
        oracle::run_isolated_observed(&exe, &data(), &entry("oracle_loop.wf"), &slow);
    assert_eq!(outcome.verdict, Verdict::Timeout, "{}", outcome.detail);
    assert!(seen.iter().all(Observation::is_timeout), "{seen:?}");
}

#[test]
fn the_output_of_a_run_that_does_not_end_is_not_compared() {
    let a = obs(0, "timeout", "", "a");
    let b = obs(0, "step-limit", "step limit", "b");
    assert!(engines::same(&a, &b));
    assert!(!engines::same(&a, &obs(0, "ok", "", "a")));
    assert!(engines::same(
        &obs(0, "ok", "", "x"),
        &obs(0, "ok", "", "x")
    ));
    assert!(!engines::same(
        &obs(0, "ok", "", "x"),
        &obs(0, "ok", "", "y")
    ));
}

#[test]
fn the_first_configuration_that_differs_is_the_difference() {
    let ast = vec![obs(0, "ok", "", "1"), obs(1, "ok", "", "2")];
    let ir = vec![obs(0, "ok", "", "1"), obs(1, "ok", "", "3")];
    let d = engines::compare(&ast, &ir).expect("a difference");
    assert_eq!(d.config, 1);
    // A run that faults stops the runs of its engine.
    let ir = vec![obs(0, "fault", "a value is used after it was moved", "")];
    let d = engines::compare(&ast, &ir).expect("a difference");
    assert_eq!(d.config, 0);
    assert!(Kind::MovedClosure.fits(&d));
    let ast = vec![obs(0, "fault", "a value is used after it was moved", "")];
    assert_eq!(engines::compare(&ast, &ir), None);
}

#[test]
fn each_class_has_its_shape() {
    let moved = "a value is used after it was moved";
    let dangling = "oracle: a read of a freed cell (a dangling reference)";
    let race = "oracle: data race: task 1 writes a cell at [], and task 2 reads it at [] with no join between";
    let fits = |k: Kind, a: Observation, i: Observation| k.fits(&diff(a, i));
    assert!(fits(
        Kind::W0315,
        obs(0, "ok", "", "x"),
        obs(0, "fault", "`return` cannot leave a scope body", "")
    ));
    assert!(fits(
        Kind::Receiver,
        obs(0, "fault", moved, ""),
        obs(0, "fault", "a `Vec` is needed here", "")
    ));
    assert!(fits(
        Kind::Receiver,
        obs(0, "fault", "`clone` needs an `Rc`", ""),
        obs(0, "fault", moved, "")
    ));
    assert!(fits(
        Kind::Capture,
        obs(0, "ok", "", "1"),
        obs(0, "fault", dangling, "")
    ));
    assert!(!fits(
        Kind::Capture,
        obs(0, "fault", dangling, ""),
        obs(0, "ok", "", "x")
    ));
    assert!(fits(
        Kind::DanglingMoved,
        obs(0, "fault", moved, ""),
        obs(0, "fault", dangling, "")
    ));
    assert!(fits(
        Kind::DanglingMoved,
        obs(0, "ok", "", "<dangling>"),
        obs(0, "fault", "the place does not exist", "")
    ));
    assert!(fits(
        Kind::MovedRead,
        obs(0, "ok", "", "<moved>"),
        obs(0, "fault", moved, "")
    ));
    assert!(fits(
        Kind::Mention,
        obs(0, "fault", moved, ""),
        obs(0, "ok", "", "")
    ));
    let leak =
        "oracle: linear leak: a live linear value goes away with no consume and no `on abort`";
    assert!(fits(
        Kind::Mention,
        obs(0, "fault", leak, ""),
        obs(0, "ok", "", "unlock 2\n")
    ));
    assert!(fits(
        Kind::BranchTemps,
        obs(0, "ok", "", "2\n"),
        obs(0, "fault", dangling, "")
    ));
    let mut a = obs(0, "fault", leak, "");
    a.line = Some(4);
    let mut i = obs(0, "fault", leak, "");
    i.line = Some(5);
    assert!(fits(Kind::LeakAtDead, a.clone(), i));
    let mut d1 = obs(0, "fault", dangling, "1\n");
    d1.line = Some(8);
    let mut d2 = obs(0, "fault", dangling, "");
    d2.line = Some(12);
    assert!(fits(Kind::ReadOrder, d1.clone(), d2.clone()));
    assert!(fits(Kind::Capture, d1, d2));
    assert!(!fits(Kind::LeakAtDead, a, obs(0, "ok", "", "")));
    assert!(fits(
        Kind::ClosureCopy,
        obs(0, "fault", moved, ""),
        obs(0, "ok", "", "")
    ));
    assert!(fits(
        Kind::FaultText,
        obs(0, "fault", "not a tuple of that size", "a"),
        obs(0, "fault", "has no part 0", "a")
    ));
    assert!(!fits(
        Kind::FaultText,
        obs(0, "fault", "x", "a"),
        obs(0, "fault", "y", "b")
    ));
    assert!(fits(
        Kind::Schedule,
        obs(0, "ok", "", "a\nb\n"),
        obs(0, "ok", "", "b\na\n")
    ));
    assert!(!fits(
        Kind::Schedule,
        obs(0, "ok", "", "a\nb\n"),
        obs(0, "ok", "", "a\nc\n")
    ));
    assert!(fits(
        Kind::RaceReadFirst,
        obs(0, "ok", "", ""),
        obs(0, "fault", race, "")
    ));
    assert!(fits(
        Kind::RaceBeforeDangling,
        obs(0, "fault", dangling, ""),
        obs(0, "fault", race, "")
    ));
    assert!(fits(
        Kind::StaticTypeRead,
        obs(0, "ok", "", "1"),
        obs(
            0,
            "fault",
            "oracle: linear leak: a live linear value goes away with no consume and no `on abort`",
            ""
        )
    ));
    assert!(fits(
        Kind::Timeout,
        obs(0, "timeout", "", ""),
        obs(0, "ok", "", "")
    ));
    assert!(fits(
        Kind::LoopTemps,
        obs(0, "ok", "", "true"),
        obs(0, "ok", "", "false")
    ));
    assert!(!fits(
        Kind::LoopTemps,
        obs(0, "ok", "", "true"),
        obs(0, "fault", moved, "")
    ));
    let no_field = "this value has no field `A`";
    assert!(fits(
        Kind::VariantPlace,
        obs(0, "fault", no_field, ""),
        obs(0, "ok", "", "5\n")
    ));
    assert!(fits(
        Kind::VariantPlace,
        obs(0, "fault", no_field, ""),
        obs(
            0,
            "fault",
            "this value is another variant: it has no such field",
            ""
        )
    ));
    assert!(!fits(
        Kind::VariantPlace,
        obs(0, "fault", no_field, ""),
        obs(0, "fault", no_field, "")
    ));
    assert!(!fits(
        Kind::VariantPlace,
        obs(0, "ok", "", "5\n"),
        obs(0, "fault", no_field, "")
    ));
    for k in Kind::ALL {
        assert_eq!(Kind::parse(k.name()), Some(k));
    }
}

#[test]
fn a_rule_accepts_a_difference_only_on_a_program_that_the_checker_rejects() {
    let l = ledger(
        r#"
[[entry]]
class = "engine"
difference = "moved-closure"
checker = "rejects"
files = ["**"]
reason = "a once closure moves into the call in the IR"
stage = "I5"
"#,
    );
    let rules = Rules::from_ledger(&l);
    assert!(rules.problems.is_empty(), "{:?}", rules.problems);
    let runs = Runs {
        ast: vec![obs(0, "ok", "", "1")],
        ir: vec![obs(0, "fault", "a value is used after it was moved", "")],
    };
    let paths = vec!["p/a.wf".to_string()];
    let on_rejected = engines::judge(&runs, &paths, true, &l, &rules);
    assert!(
        matches!(on_rejected, Result1::Differ { entry: Some(0), .. }),
        "{on_rejected:?}"
    );
    let on_accepted = engines::judge(&runs, &paths, false, &l, &rules);
    assert!(
        matches!(on_accepted, Result1::Differ { entry: None, .. }),
        "{on_accepted:?}"
    );
    // The class must fit the difference.
    let other = Runs {
        ast: vec![obs(0, "ok", "", "1")],
        ir: vec![obs(0, "ok", "", "2")],
    };
    let r = engines::judge(&other, &paths, true, &l, &rules);
    assert!(matches!(r, Result1::Differ { entry: None, .. }), "{r:?}");
}

#[test]
fn a_difference_on_an_accepted_program_needs_an_entry_that_names_it() {
    let l = ledger(
        r#"
[[entry]]
class = "engine"
difference = "choice-a"
files = ["tests/gate/probes/ir/probes/p1_late_operand.wf"]
reason = "choice A: the IR reads the operand `x` before the block writes it"
stage = "I5"

[[entry]]
class = "engine"
difference = "choice-a"
files = ["tests/gate/probes/ir/probes/*.wf"]
reason = "a glob with no checker rule"
"#,
    );
    assert_eq!(l.entries[0].class, EntryClass::Engine);
    assert_eq!(l.entries[0].problem(), None);
    let p = l.entries[1].problem().unwrap_or_default();
    assert!(p.contains("no glob"), "{p}");
    let rules = Rules::from_ledger(&l);
    let runs = Runs {
        ast: vec![obs(0, "ok", "", "6\n")],
        ir: vec![obs(0, "ok", "", "2\n")],
    };
    let paths = vec!["tests/gate/probes/ir/probes/p1_late_operand.wf".to_string()];
    let r = engines::judge(&runs, &paths, false, &l, &rules);
    assert!(matches!(r, Result1::Differ { entry: Some(0), .. }), "{r:?}");
    let unknown = ledger("[[entry]]\nclass = \"engine\"\ndifference = \"other\"\nfiles = [\"a.wf\"]\nreason = \"r\"\n");
    assert_eq!(Rules::from_ledger(&unknown).problems.len(), 1);
}

#[test]
fn a_program_that_falls_back_is_not_a_difference() {
    let mut ir = obs(0, "ok", "", "1");
    ir.fallback = Some("the body `f` has no IR: a type error".to_string());
    let runs = Runs {
        ast: vec![obs(0, "ok", "", "1")],
        ir: vec![ir],
    };
    let l = Ledger::default();
    let r = engines::judge(&runs, &[], true, &l, &Rules::from_ledger(&l));
    assert!(matches!(r, Result1::Fallback(_)), "{r:?}");
}

#[test]
fn a_sample_is_fixed_by_its_seed() {
    let hashes: Vec<String> = (0..2000).map(|i| format!("{i:064x}")).collect();
    let pick = |seed| -> Vec<&String> {
        hashes
            .iter()
            .filter(|h| engines::in_sample(h, 10, seed))
            .collect()
    };
    let (a, b, c) = (pick(1), pick(1), pick(2));
    assert_eq!(a, b);
    assert_ne!(a, c);
    assert!((150..250).contains(&a.len()), "{}", a.len());
    assert!(hashes.iter().all(|h| engines::in_sample(h, 100, 7)));
}

#[test]
fn the_committed_ledger_has_no_problem_in_its_engine_entries() {
    let l = Ledger::read(&repo().join("tests/gate/ledger.toml")).expect("read the ledger");
    let rules = Rules::from_ledger(&l);
    assert!(rules.problems.is_empty(), "{:?}", rules.problems);
    assert!(!rules.entries.is_empty(), "the ledger has no engine entry");
    for (k, _) in &rules.entries {
        let e = &l.entries[*k];
        assert_eq!(e.problem(), None, "{}", e.label());
    }
}

/// The full differential on tier 1 (about 15 minutes with a release build):
/// `cargo test --release -p weft-gate --test engines -- --ignored`.
#[test]
#[ignore = "the full differential of tier 1; run `weft-gate engines --tier 1`"]
fn the_engine_differential_of_tier_1_has_no_unledgered_difference() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_weft-gate"))
        .args(["engines", "--tier", "1"])
        .current_dir(repo())
        .output()
        .expect("run weft-gate engines");
    assert!(
        out.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}
