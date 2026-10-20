//! Tests of the classifier, the ledger and the report (plan
//! `docs/plan/core-ir.md`, stage G5, and §2.5).
//!
//! Each test makes a synthetic pair of snapshot records (`old` and `ir`) and an
//! oracle verdict. The tests do not run the checker or the interpreter.

use std::collections::BTreeMap;

use weft_gate::classify::{self, Class};
use weft_gate::ledger::{self, Ledger};
use weft_gate::oracle::Verdict;
use weft_gate::report::{Input, Policy, Report};
use weft_gate::snapshot::{Diag, Kind, Record};

const CORPUS: &str = "corpus";
const PROBES: &str = "probes";

/// A record of kind `ok` with the diagnostics `diags` (code and line).
fn rec(path: &str, set: &str, diags: &[(&str, usize)]) -> Record {
    Record {
        path: path.to_string(),
        hash: format!("hash-of-{path}"),
        set: set.to_string(),
        pipeline: "old".to_string(),
        kind: Kind::Ok,
        message: None,
        diagnostics: diags
            .iter()
            .map(|(c, l)| Diag((*c).to_string(), path.to_string(), *l))
            .collect(),
        violations: Vec::new(),
        counts: BTreeMap::new(),
        digest: String::new(),
        problems: Vec::new(),
        ms: 0,
    }
}

/// A record of the kind `kind` with no result.
fn rec_kind(path: &str, set: &str, kind: Kind) -> Record {
    Record {
        kind,
        message: Some(format!("the record is {}", kind.name())),
        ..rec(path, set, &[])
    }
}

fn input(old: Record, ir: Record, verdict: Verdict) -> Input {
    Input {
        paths: vec![old.path.clone()],
        old,
        ir,
        verdict,
        in_scope: false,
    }
}

/// One program in the set `set`: `old` and `ir` diagnostics and a verdict.
fn pair(
    path: &str,
    set: &str,
    old: &[(&str, usize)],
    ir: &[(&str, usize)],
    verdict: Verdict,
) -> Input {
    input(rec(path, set, old), rec(path, set, ir), verdict)
}

fn ledger(text: &str) -> Ledger {
    Ledger::from_toml(text).unwrap_or_else(|e| panic!("the ledger does not parse: {e}"))
}

fn build(inputs: &[Input], text: &str) -> Report {
    Report::build(inputs, &ledger(text), &Policy::default())
}

/// The report of one program, and its only row.
fn one(input: Input, text: &str) -> Report {
    let r = build(&[input], text);
    assert_eq!(r.rows.len(), 1, "one row for one program");
    r
}

fn class_of(input: &Input) -> Class {
    classify::classify(&input.old, &input.ir, input.verdict)
}

// The classes of §2.5.

#[test]
fn equal_errors_give_same() {
    let i = pair(
        "a.wf",
        CORPUS,
        &[("W0301", 4)],
        &[("W0301", 4)],
        Verdict::Fault,
    );
    assert_eq!(class_of(&i), Class::Same);
    let i = pair("a.wf", CORPUS, &[], &[], Verdict::Clean);
    assert_eq!(class_of(&i), Class::Same);
}

#[test]
fn a_panic_of_the_ir_pipeline_gives_crash() {
    let i = input(
        rec("a.wf", CORPUS, &[]),
        rec_kind("a.wf", CORPUS, Kind::Crash),
        Verdict::Clean,
    );
    assert_eq!(class_of(&i), Class::Crash);
}

#[test]
fn a_problem_of_the_ir_side_gives_crash() {
    for problem in [
        "verifier: rule V3 in `main`",
        "agreement: `error` differs in `f`",
        "lint gen_kill: a result in `g`",
    ] {
        let mut ir = rec("a.wf", CORPUS, &[]);
        ir.problems.push(problem.to_string());
        let i = input(rec("a.wf", CORPUS, &[]), ir, Verdict::Clean);
        assert_eq!(class_of(&i), Class::Crash, "{problem}");
    }
}

#[test]
fn a_timeout_of_the_ir_side_only_gives_crash() {
    let i = input(
        rec("a.wf", CORPUS, &[]),
        rec_kind("a.wf", CORPUS, Kind::Timeout),
        Verdict::Clean,
    );
    assert_eq!(class_of(&i), Class::Crash);
}

#[test]
fn a_timeout_on_both_sides_gives_same() {
    let i = input(
        rec_kind("a.wf", PROBES, Kind::Timeout),
        rec_kind("a.wf", PROBES, Kind::Timeout),
        Verdict::Clean,
    );
    assert_eq!(class_of(&i), Class::Same);
}

#[test]
fn a_file_that_does_not_load_on_both_sides_gives_same() {
    let i = input(
        rec_kind("a.wf", PROBES, Kind::Error),
        rec_kind("a.wf", PROBES, Kind::Error),
        Verdict::NotRunnable,
    );
    assert_eq!(class_of(&i), Class::Same);
}

#[test]
fn ir_accepts_a_fault_gives_open() {
    let i = pair("a.wf", PROBES, &[], &[], Verdict::Fault);
    assert_eq!(class_of(&i), Class::Open);
}

#[test]
fn old_rejects_ir_accepts_a_fault_gives_lost_fault() {
    let i = pair("a.wf", PROBES, &[("W0301", 3)], &[], Verdict::Fault);
    assert_eq!(class_of(&i), Class::LostFault);
}

#[test]
fn old_accepts_ir_rejects_a_fault_gives_fixed() {
    let i = pair("a.wf", PROBES, &[], &[("W0301", 3)], Verdict::Fault);
    assert_eq!(class_of(&i), Class::Fixed);
}

#[test]
fn old_accepts_ir_rejects_no_fault_gives_new_fp() {
    for v in [
        Verdict::Clean,
        Verdict::Benign,
        Verdict::Fail,
        Verdict::NotRunnable,
    ] {
        let i = pair("a.wf", PROBES, &[], &[("W0301", 3)], v);
        assert_eq!(class_of(&i), Class::NewFp, "{}", v.name());
    }
}

#[test]
fn old_rejects_ir_accepts_no_fault_gives_lost_clean() {
    for v in [
        Verdict::Clean,
        Verdict::Benign,
        Verdict::Fail,
        Verdict::NotRunnable,
        Verdict::Timeout,
    ] {
        let i = pair("a.wf", PROBES, &[("W0301", 3)], &[], v);
        assert_eq!(class_of(&i), Class::LostClean, "{}", v.name());
    }
}

#[test]
fn the_same_codes_on_other_lines_give_moved() {
    let i = pair(
        "a.wf",
        PROBES,
        &[("W0301", 3), ("W0302", 9)],
        &[("W0302", 9), ("W0301", 5)],
        Verdict::Fault,
    );
    assert_eq!(class_of(&i), Class::Moved);
}

#[test]
fn other_codes_or_counts_give_changed() {
    let i = pair(
        "a.wf",
        PROBES,
        &[("W0301", 3)],
        &[("W0302", 3)],
        Verdict::Fault,
    );
    assert_eq!(class_of(&i), Class::Changed);
    let i = pair(
        "a.wf",
        PROBES,
        &[("W0301", 3)],
        &[("W0301", 3), ("W0301", 4)],
        Verdict::Clean,
    );
    assert_eq!(class_of(&i), Class::Changed);
}

#[test]
fn a_warning_does_not_reject() {
    // W0804 (an unknown file marker) is a warning: the program is accepted.
    let i = pair("a.wf", PROBES, &[("W0804", 1)], &[], Verdict::Fault);
    assert_eq!(class_of(&i), Class::Open);
    let i = pair("a.wf", PROBES, &[], &[("W0804", 1)], Verdict::Clean);
    assert_eq!(class_of(&i), Class::Same);
}

#[test]
fn the_class_names_read_back() {
    for c in Class::ALL {
        assert_eq!(Class::parse(c.name()), Some(c));
    }
    assert_eq!(Class::NewFp.name(), "new-fp");
    assert_eq!(Class::LostFault.name(), "lost-fault");
    assert_eq!(Class::LostClean.name(), "lost-clean");
}

// The rules of §2.5: what blocks.

#[test]
fn same_and_fixed_do_not_block() {
    let r = build(
        &[
            pair(
                "a.wf",
                CORPUS,
                &[("W0301", 2)],
                &[("W0301", 2)],
                Verdict::Fault,
            ),
            pair("b.wf", CORPUS, &[], &[("W0301", 2)], Verdict::Fault),
        ],
        "",
    );
    assert!(r.passes(), "{:?}", r.blockers);
    assert_eq!(r.class_counts().get(&Class::Fixed), Some(&1));
}

#[test]
fn crash_blocks_even_with_a_ledger_entry() {
    let i = input(
        rec("a.wf", CORPUS, &[]),
        rec_kind("a.wf", CORPUS, Kind::Crash),
        Verdict::Clean,
    );
    let r = one(
        i,
        r#"
[[entry]]
class = "changed"
files = ["a.wf"]
reason = "not a crash"
"#,
    );
    assert!(!r.passes());
    assert!(r.blockers[0].contains("crash"), "{:?}", r.blockers);
}

#[test]
fn lost_fault_blocks_always() {
    let r = one(
        pair("a.wf", PROBES, &[("W0301", 3)], &[], Verdict::Fault),
        r#"
[[entry]]
class = "lost-clean"
files = ["a.wf"]
reason = "an entry of another class"
signed_by = "review agent"
"#,
    );
    assert!(!r.passes());
    assert!(r.blockers[0].contains("lost-fault"), "{:?}", r.blockers);
}

#[test]
fn new_fp_in_the_corpus_blocks_with_or_without_an_entry() {
    let text = r#"
[[entry]]
class = "new-fp"
files = ["a.wf"]
reason_class = "stricter"
reason = "a stricter rule"
"#;
    for t in ["", text] {
        let r = one(
            pair("a.wf", CORPUS, &[], &[("W0301", 3)], Verdict::Clean),
            t,
        );
        assert!(!r.passes(), "ledger {t:?}");
        assert!(r.blockers[0].contains("new-fp"), "{:?}", r.blockers);
    }
}

#[test]
fn new_fp_in_the_other_repository_sets_blocks() {
    for set in ["interp", "examples", "packages"] {
        let r = one(pair("a.wf", set, &[], &[("W0301", 3)], Verdict::Clean), "");
        assert!(!r.passes(), "{set}");
    }
}

/// `n` probes that the old pipeline accepts and that stay `same`.
fn accepted_probes(n: usize) -> Vec<Input> {
    (0..n)
        .map(|k| pair(&format!("ok/{k}.wf"), PROBES, &[], &[], Verdict::Clean))
        .collect()
}

#[test]
fn new_fp_in_the_probes_needs_an_entry_with_a_reason_class() {
    let mut inputs = accepted_probes(2000);
    inputs.push(pair(
        "fp/a.wf",
        PROBES,
        &[],
        &[("W0301", 3)],
        Verdict::Clean,
    ));
    let r = build(&inputs, "");
    assert!(!r.passes(), "no entry");
    let r = build(
        &inputs,
        r#"
[[entry]]
class = "new-fp"
files = ["fp/a.wf"]
reason = "no reason class"
"#,
    );
    assert!(!r.passes(), "no reason class");
    let r = build(
        &inputs,
        r#"
[[entry]]
class = "new-fp"
files = ["fp/a.wf"]
reason_class = "precision"
reason = "a precision loss, but no issue"
"#,
    );
    assert!(!r.passes(), "a precision loss with no issue");
    for text in [
        r#"
[[entry]]
class = "new-fp"
files = ["fp/a.wf"]
reason_class = "stricter"
reason = "ADR 0012: a stricter rule"
"#,
        r#"
[[entry]]
class = "new-fp"
files = ["fp/a.wf"]
reason_class = "precision"
issue = 41
reason = "a precision loss"
"#,
    ] {
        let r = build(&inputs, text);
        assert!(r.passes(), "{text}: {:?}", r.blockers);
    }
}

#[test]
fn new_fp_in_the_probes_is_at_most_one_in_a_thousand() {
    let text = r#"
[[entry]]
class = "new-fp"
files = ["fp/*.wf"]
reason_class = "stricter"
reason = "ADR 0012: a stricter rule"
"#;
    // 2 000 accepted probes and 2 new-fp: 2 of 2 002 is less than 0.1 %.
    let mut inputs = accepted_probes(2000);
    for k in 0..2 {
        inputs.push(pair(
            &format!("fp/{k}.wf"),
            PROBES,
            &[],
            &[("W0301", 3)],
            Verdict::Clean,
        ));
    }
    let r = build(&inputs, text);
    assert!(r.passes(), "{:?}", r.blockers);
    // 3 new-fp of 2 003 is more than 0.1 %.
    inputs.push(pair(
        "fp/2.wf",
        PROBES,
        &[],
        &[("W0301", 3)],
        Verdict::Clean,
    ));
    let r = build(&inputs, text);
    assert!(!r.passes());
    assert!(
        r.blockers.iter().any(|b| b.contains("0.1 %")),
        "{:?}",
        r.blockers
    );
}

#[test]
fn lost_clean_needs_an_entry_that_a_reviewer_signed() {
    let i = || pair("a.wf", PROBES, &[("W0301", 3)], &[], Verdict::Clean);
    assert!(!one(i(), "").passes(), "no entry");
    let r = one(
        i(),
        r#"
[[entry]]
class = "lost-clean"
files = ["a.wf"]
finding = "V069"
reason = "STATE: the holder of the part rebinds at the new value"
stage = "F8"
"#,
    );
    assert!(!r.passes(), "no signed_by");
    assert!(
        r.blockers[0].contains("signed_by"),
        "the message names the missing field: {:?}",
        r.blockers
    );
    let r = one(
        i(),
        r#"
[[entry]]
class = "lost-clean"
files = ["a.wf"]
finding = "V069"
reason = "STATE: the holder of the part rebinds at the new value"
signed_by = "review agent, stage F8"
stage = "F8"
"#,
    );
    assert!(r.passes(), "{:?}", r.blockers);
}

#[test]
fn moved_and_changed_need_an_entry_with_a_reason() {
    let moved = || {
        pair(
            "a.wf",
            PROBES,
            &[("W0301", 3)],
            &[("W0301", 4)],
            Verdict::Fault,
        )
    };
    let changed = || {
        pair(
            "a.wf",
            PROBES,
            &[("W0301", 3)],
            &[("W0302", 3)],
            Verdict::Fault,
        )
    };
    assert!(!one(moved(), "").passes());
    assert!(!one(changed(), "").passes());
    let entry = |class: &str| {
        format!(
            "[[entry]]\nclass = \"{class}\"\nfiles = [\"a.wf\"]\nreason = \"the use is at the read\"\n"
        )
    };
    assert!(one(moved(), &entry("moved")).passes());
    assert!(one(changed(), &entry("changed")).passes());
    // An entry of the other class does not cover the program.
    assert!(!one(moved(), &entry("changed")).passes());
    assert!(!one(changed(), &entry("moved")).passes());
    // An entry with no reason does not cover the program.
    let bare = "[[entry]]\nclass = \"moved\"\nfiles = [\"a.wf\"]\n";
    assert!(!one(moved(), bare).passes());
}

#[test]
fn an_entry_with_codes_covers_only_those_codes() {
    let changed = pair(
        "a.wf",
        PROBES,
        &[("W0301", 3)],
        &[("W0302", 3)],
        Verdict::Fault,
    );
    let text = |codes: &str| {
        format!(
            "[[entry]]\nclass = \"changed\"\nfiles = [\"a.wf\"]\ncodes = [{codes}]\nreason = \"r\"\n"
        )
    };
    assert!(one(changed.clone(), &text("\"W0301\", \"W0302\"")).passes());
    assert!(!one(changed, &text("\"W0301\"")).passes());
}

#[test]
fn open_with_no_entry_is_reported_before_the_baseline() {
    let r = one(pair("a.wf", PROBES, &[], &[], Verdict::Fault), "");
    assert!(r.passes(), "{:?}", r.blockers);
    assert_eq!(r.rows[0].class, Class::Open);
    let strict = Policy {
        open_needs_entry: true,
    };
    let r = Report::build(
        &[pair("a.wf", PROBES, &[], &[], Verdict::Fault)],
        &Ledger::default(),
        &strict,
    );
    assert!(!r.passes(), "from stage G6 on, open needs an entry");
}

#[test]
fn open_entries_need_a_finding_that_stays_or_an_issue() {
    let strict = Policy {
        open_needs_entry: true,
    };
    let check = |text: &str| {
        Report::build(
            &[pair("a.wf", PROBES, &[], &[], Verdict::Fault)],
            &ledger(text),
            &strict,
        )
        .passes()
    };
    assert!(check(
        "[[entry]]\nclass = \"open\"\nfiles = [\"a.wf\"]\nfinding = \"N2\"\nverdict = \"stays\"\nreason = \"r\"\n"
    ));
    assert!(!check(
        "[[entry]]\nclass = \"open\"\nfiles = [\"a.wf\"]\nfinding = \"N2\"\nverdict = \"construction\"\nreason = \"r\"\n"
    ));
    assert!(!check(
        "[[entry]]\nclass = \"open\"\nfiles = [\"a.wf\"]\nverdict = \"stays\"\nreason = \"r\"\n"
    ));
    assert!(check(
        "[[entry]]\nclass = \"edge\"\nfiles = [\"a.wf\"]\nissue = 7\nreason = \"ship rule\"\n"
    ));
    assert!(!check(
        "[[entry]]\nclass = \"edge\"\nfiles = [\"a.wf\"]\nreason = \"no issue\"\n"
    ));
    assert!(check(
        "[[entry]]\nclass = \"open-old\"\nfiles = [\"a.wf\"]\nfinding = \"unclassified\"\nreason = \"the old pipeline accepts it today\"\n"
    ));
}

// The ledger.

#[test]
fn a_glob_entry_covers_a_group() {
    let inputs = [
        pair(
            "tests/gate/probes/r2/fp/a.wf",
            PROBES,
            &[("W0301", 3)],
            &[("W0301", 4)],
            Verdict::Fault,
        ),
        pair(
            "tests/gate/probes/r2/fp/sub/b.wf",
            PROBES,
            &[("W0302", 3)],
            &[("W0302", 8)],
            Verdict::Fault,
        ),
        pair(
            "tests/gate/probes/r3/c.wf",
            PROBES,
            &[("W0302", 3)],
            &[("W0302", 8)],
            Verdict::Fault,
        ),
    ];
    let r = build(
        &inputs,
        r#"
[[entry]]
class = "moved"
files = ["tests/gate/probes/r2/**/*.wf"]
reason = "the use is at the read"
"#,
    );
    assert_eq!(r.blockers.len(), 1, "{:?}", r.blockers);
    assert!(r.blockers[0].contains("r3/c.wf"), "{:?}", r.blockers);
    let r = build(
        &inputs,
        r#"
[[entry]]
class = "moved"
files = ["tests/gate/probes/r2/fp/*.wf", "tests/gate/probes/r?/c.wf"]
reason = "the use is at the read"
"#,
    );
    assert_eq!(r.blockers.len(), 1, "{:?}", r.blockers);
    assert!(r.blockers[0].contains("sub/b.wf"), "{:?}", r.blockers);
}

#[test]
fn the_glob_rules() {
    assert!(ledger::glob_match("a/*.wf", "a/b.wf"));
    assert!(!ledger::glob_match("a/*.wf", "a/b/c.wf"));
    assert!(ledger::glob_match("a/**/*.wf", "a/c.wf"));
    assert!(ledger::glob_match("a/**/*.wf", "a/b/c/d.wf"));
    assert!(ledger::glob_match("a/**", "a/b/c.wf"));
    assert!(ledger::glob_match("a/?.wf", "a/b.wf"));
    assert!(!ledger::glob_match("a/?.wf", "a/bc.wf"));
    assert!(ledger::glob_match("a/b.wf", "a/b.wf"));
    assert!(!ledger::glob_match("a/b.wf", "a/b.wfx"));
    assert!(ledger::glob_match("*", "pkg"));
    assert!(!ledger::glob_match("*", "a/b"));
}

#[test]
fn an_entry_matches_an_other_path_of_the_program() {
    let mut i = pair(
        "a.wf",
        PROBES,
        &[("W0301", 3)],
        &[("W0301", 4)],
        Verdict::Fault,
    );
    i.paths.push("copy/a.wf".to_string());
    let r = one(
        i,
        "[[entry]]\nclass = \"moved\"\nfiles = [\"copy/*.wf\"]\nreason = \"r\"\n",
    );
    assert!(r.passes(), "{:?}", r.blockers);
}

#[test]
fn an_entry_that_matches_no_program_is_a_warning() {
    let r = build(
        &[pair("a.wf", PROBES, &[], &[], Verdict::Clean)],
        "[[entry]]\nclass = \"moved\"\nfiles = [\"gone/*.wf\"]\nreason = \"r\"\n",
    );
    assert!(r.passes(), "a stale entry does not block");
    assert_eq!(r.warnings.len(), 1, "{:?}", r.warnings);
    assert!(r.warnings[0].contains("gone/*.wf"), "{:?}", r.warnings);
    // An entry that matches a program of another class is also stale.
    let r = build(
        &[pair("a.wf", PROBES, &[], &[], Verdict::Clean)],
        "[[entry]]\nclass = \"moved\"\nfiles = [\"a.wf\"]\nreason = \"r\"\n",
    );
    assert!(r.passes());
    assert_eq!(r.warnings.len(), 1, "{:?}", r.warnings);
}

#[test]
fn the_ledger_syntax() {
    let l = ledger(
        r#"
[[entry]]
class = "lost-clean"
files = ["tests/gate/probes/r2/oracle/fp/v069_part.wf"]   # paths or globs
finding = "V069"
reason = "STATE: the holder of the part rebinds at the new value"
signed_by = "review agent, stage F8"
stage = "F8"
"#,
    );
    assert_eq!(l.entries.len(), 1);
    assert_eq!(l.entries[0].finding.as_deref(), Some("V069"));
    assert!(Ledger::from_toml("").is_ok_and(|l| l.entries.is_empty()));
    for bad in [
        "[[entry]]\nclass = \"nice\"\nfiles = [\"a.wf\"]\n",
        "[[entry]]\nclass = \"moved\"\nfiles = []\n",
        "[[entry]]\nclass = \"moved\"\n",
        "[[entry]]\nclass = \"moved\"\nfiles = [\"a.wf\"]\nsigned = \"x\"\n",
        "[[entry]]\nclass = \"new-fp\"\nfiles = [\"a.wf\"]\nreason_class = \"taste\"\n",
        "entry = 3",
    ] {
        assert!(Ledger::from_toml(bad).is_err(), "{bad}");
    }
}

#[test]
fn the_committed_ledger_parses() {
    let file =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/gate/ledger.toml");
    let text =
        std::fs::read_to_string(&file).unwrap_or_else(|e| panic!("read {}: {e}", file.display()));
    assert!(Ledger::from_toml(&text).is_ok());
}

// The report.

#[test]
fn the_report_has_counts_coverage_and_blockers() {
    let inputs = [
        pair("tests/programs/a.wf", CORPUS, &[], &[], Verdict::Clean),
        pair(
            "tests/programs/b.wf",
            CORPUS,
            &[],
            &[("W0301", 2)],
            Verdict::Clean,
        ),
        pair("p/c.wf", PROBES, &[], &[], Verdict::Fault),
    ];
    let r = build(&inputs, "");
    let counts = r.counts();
    assert_eq!(counts.get(&(CORPUS.to_string(), Class::Same)), Some(&1));
    assert_eq!(counts.get(&(CORPUS.to_string(), Class::NewFp)), Some(&1));
    assert_eq!(counts.get(&(PROBES.to_string(), Class::Open)), Some(&1));
    let md = r.to_markdown();
    for text in [
        "# Gate report",
        "## Counts",
        "## Coverage",
        "## Blockers",
        "new-fp",
        "tests/programs/b.wf",
        "p/c.wf",
    ] {
        assert!(md.contains(text), "the report has no `{text}`:\n{md}");
    }
    assert!(!r.passes());
}
