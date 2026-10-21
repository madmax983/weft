//! Tests of the baseline of the old pipeline (plan `docs/plan/core-ir.md`,
//! §1 rule 3 and stage G6).
//!
//! Each test makes synthetic snapshot records. The tests do not run the
//! checker or the interpreter.

use std::collections::BTreeMap;

use weft_gate::baseline::{self, Comparison};
use weft_gate::ledger::Ledger;
use weft_gate::oracle::Verdict;
use weft_gate::report::{Input, Policy, Report};
use weft_gate::snapshot::{Diag, Kind, Record, Violation};

/// A record of kind `ok` with one diagnostic, one violation and a digest.
fn rec(path: &str) -> Record {
    Record {
        path: path.to_string(),
        hash: format!("hash-of-{path}"),
        set: "probes".to_string(),
        pipeline: "old".to_string(),
        kind: Kind::Ok,
        message: None,
        diagnostics: vec![Diag("W0301".to_string(), path.to_string(), 4)],
        violations: vec![Violation {
            file: path.to_string(),
            function: "main".to_string(),
            relation: "error".to_string(),
            args: vec!["r".to_string(), "@4".to_string()],
        }],
        counts: BTreeMap::from([("cfg_edge".to_string(), 7), ("uses".to_string(), 3)]),
        digest: "d1".to_string(),
        problems: Vec::new(),
        ms: 12,
    }
}

/// A record of the kind `kind` with no result, as the snapshot makes it.
fn rec_kind(path: &str, kind: Kind) -> Record {
    Record {
        kind,
        message: Some("the check takes more than 60000 ms".to_string()),
        diagnostics: Vec::new(),
        violations: Vec::new(),
        counts: BTreeMap::new(),
        digest: String::new(),
        ms: 60_000,
        ..rec(path)
    }
}

fn names(c: &Comparison) -> Vec<String> {
    c.differences.iter().map(|d| d.path.clone()).collect()
}

#[test]
fn the_committed_form_has_no_time_and_reads_back() {
    let records = vec![rec("a.wf"), rec_kind("b.wf", Kind::Timeout)];
    let text = baseline::to_jsonl(&records).unwrap_or_else(|e| panic!("write: {e}"));
    assert_eq!(text.lines().count(), 2);
    assert!(
        !text.contains("\"ms\""),
        "the committed form has no time:\n{text}"
    );
    let back = baseline::from_jsonl(&text).unwrap_or_else(|e| panic!("read: {e}"));
    let want: Vec<Record> = records.iter().map(baseline::committed).collect();
    assert_eq!(back, want);
    assert!(back.iter().all(|r| r.ms == 0));
}

#[test]
fn a_bad_line_gives_its_number() {
    let good = baseline::to_jsonl(&[rec("a.wf")]).unwrap_or_else(|e| panic!("write: {e}"));
    let text = format!("{good}{{\"path\": 3}}\n");
    let e = baseline::from_jsonl(&text).err().map(|e| e.to_string());
    assert!(
        e.as_deref().is_some_and(|t| t.contains("line 2")),
        "the error names the line: {e:?}"
    );
}

#[test]
fn equal_records_pass_and_the_time_does_not_count() {
    let base = vec![rec("a.wf"), rec("b.wf")];
    let mut now = base.clone();
    for r in &mut now {
        r.ms += 1000;
    }
    let c = baseline::compare(&base, &now);
    assert!(c.passes(), "{c:?}");
    assert_eq!(c.compared, 2);
    assert!(c.unknown.is_empty());
}

/// A change of a record.
type Change = Box<dyn Fn(&mut Record)>;

fn change(f: impl Fn(&mut Record) + 'static) -> Change {
    Box::new(f)
}

#[test]
fn each_field_of_the_committed_form_counts() {
    let base = vec![rec("a.wf")];
    let changes: Vec<(&str, Change)> = vec![
        ("diagnostics", change(|r| r.diagnostics[0].2 = 5)),
        ("violations", change(|r| r.violations.clear())),
        (
            "counts",
            change(|r| {
                r.counts.insert("uses".to_string(), 4);
            }),
        ),
        ("digest", change(|r| r.digest = "d2".to_string())),
        ("kind", change(|r| r.kind = Kind::Crash)),
        ("hash", change(|r| r.hash = "other".to_string())),
        ("set", change(|r| r.set = "corpus".to_string())),
    ];
    for (field, change) in changes {
        let mut now = base.clone();
        if let Some(r) = now.first_mut() {
            change(r);
        }
        let c = baseline::compare(&base, &now);
        assert!(!c.passes(), "a change of `{field}` is not a difference");
        assert_eq!(names(&c), vec!["a.wf".to_string()]);
        let text = c.differences[0].what.join("; ");
        assert!(
            text.contains(field),
            "the difference does not name `{field}`: {text}"
        );
    }
}

#[test]
fn a_program_that_comes_or_goes_is_a_difference() {
    let base = vec![rec("a.wf"), rec("b.wf")];
    let now = vec![rec("a.wf"), rec("c.wf")];
    let c = baseline::compare(&base, &now);
    assert!(!c.passes());
    assert_eq!(names(&c), vec!["b.wf".to_string(), "c.wf".to_string()]);
    let text: Vec<String> = c.differences.iter().map(|d| d.what.join("; ")).collect();
    assert!(text[0].contains("not in this run"), "{text:?}");
    assert!(text[1].contains("not in the baseline"), "{text:?}");
}

#[test]
fn a_timeout_is_unknown_and_is_listed() {
    // A debug build is slower: a program that finishes in the release
    // baseline can time out. The comparison skips it and lists it.
    let mut base: Vec<Record> = (0..100).map(|i| rec(&format!("p{i}.wf"))).collect();
    let mut now = base.clone();
    base.push(rec("slow.wf"));
    now.push(rec_kind("slow.wf", Kind::Timeout));
    let c = baseline::compare(&base, &now);
    assert!(c.passes(), "{c:?}");
    assert_eq!(c.compared, 100);
    assert_eq!(c.unknown, vec!["slow.wf".to_string()]);
    // The same for a timeout of the baseline.
    let c = baseline::compare(&now, &base);
    assert!(c.passes(), "{c:?}");
    assert_eq!(c.unknown, vec!["slow.wf".to_string()]);
}

#[test]
fn a_timeout_does_not_hide_a_change_of_a_program_that_finishes() {
    // Only a timeout is unknown. A crash, an error or another result of a
    // program that finishes on both sides is a difference.
    let base = vec![rec("a.wf"), rec("b.wf"), rec("c.wf")];
    let mut changed = rec("b.wf");
    changed.diagnostics.clear();
    let now = vec![
        rec_kind("a.wf", Kind::Crash),
        changed,
        rec_kind("c.wf", Kind::Error),
    ];
    let c = baseline::compare(&base, &now);
    assert!(c.unknown.is_empty());
    assert_eq!(
        names(&c),
        vec!["a.wf".to_string(), "b.wf".to_string(), "c.wf".to_string()]
    );
}

#[test]
fn a_timeout_with_another_text_is_still_unknown() {
    // A program whose text changed is a difference, also when it times out.
    let base = vec![rec("a.wf")];
    let mut now = rec_kind("a.wf", Kind::Timeout);
    now.hash = "other".to_string();
    let c = baseline::compare(&base, &[now]);
    assert!(!c.passes());
    assert_eq!(names(&c), vec!["a.wf".to_string()]);
}

#[test]
fn too_many_unknown_programs_fail() {
    // More than 1 % of unknown programs: the build is too slow for the
    // comparison, or a change makes many programs hang.
    let base: Vec<Record> = (0..200).map(|i| rec(&format!("p{i}.wf"))).collect();
    let mut now = base.clone();
    for r in now.iter_mut().take(2) {
        *r = rec_kind(&r.path, Kind::Timeout);
    }
    assert!(baseline::compare(&base, &now).passes());
    for r in now.iter_mut().take(3) {
        *r = rec_kind(&r.path, Kind::Timeout);
    }
    let c = baseline::compare(&base, &now);
    assert!(c.differences.is_empty());
    assert!(!c.passes(), "3 of 200 programs are unknown: {c:?}");
    assert!(c.blockers("b.jsonl").iter().any(|b| b.contains("unknown")));
}

#[test]
fn the_blockers_name_the_programs_and_the_command() {
    let base = vec![rec("a.wf")];
    let mut now = base.clone();
    now[0].digest = "d2".to_string();
    let c = baseline::compare(&base, &now);
    let blockers = c.blockers("tests/gate/baseline-tier1.jsonl");
    let text = blockers.join("\n");
    for part in [
        "a.wf",
        "digest",
        "tests/gate/baseline-tier1.jsonl",
        "--write-baseline",
    ] {
        assert!(
            text.contains(part),
            "the blockers have no `{part}`:\n{text}"
        );
    }
}

fn input(r: Record, verdict: Verdict) -> Input {
    Input {
        paths: vec![r.path.clone()],
        ir: r.clone(),
        old: r,
        verdict,
        in_scope: false,
    }
}

#[test]
fn the_report_compares_with_the_baseline() {
    let records = vec![rec("a.wf"), rec("b.wf")];
    let inputs: Vec<Input> = records
        .iter()
        .cloned()
        .map(|r| input(r, Verdict::Clean))
        .collect();
    let mut r = Report::build(&inputs, &Ledger::default(), &Policy::default());
    assert_eq!(r.records, records, "the report keeps the old records");
    let mut base = records.clone();
    base[1].diagnostics.clear();
    r.compare_baseline(Some(base), "tests/gate/baseline-tier1.jsonl");
    assert!(!r.passes());
    assert!(
        r.blockers.iter().any(|b| b.contains("b.wf")),
        "{:?}",
        r.blockers
    );
    let md = r.to_markdown();
    for part in ["## Baseline", "b.wf", "tests/gate/baseline-tier1.jsonl"] {
        assert!(md.contains(part), "the report has no `{part}`:\n{md}");
    }

    let mut r = Report::build(&inputs, &Ledger::default(), &Policy::default());
    r.compare_baseline(Some(records), "tests/gate/baseline-tier1.jsonl");
    assert!(r.passes(), "{:?}", r.blockers);
    assert_eq!(r.baseline.as_ref().map(|c| c.compared), Some(2));

    let mut r = Report::build(&inputs, &Ledger::default(), &Policy::default());
    r.compare_baseline(None, "tests/gate/baseline-tier1.jsonl");
    assert!(!r.passes(), "a missing baseline blocks");
}

#[test]
fn from_stage_g6_an_open_program_needs_an_entry() {
    let open = input(
        Record {
            diagnostics: Vec::new(),
            ..rec("tests/gate/probes/x/a.wf")
        },
        Verdict::Fault,
    );
    let r = Report::build(
        std::slice::from_ref(&open),
        &Ledger::default(),
        &Policy::default(),
    );
    assert!(!r.passes(), "an open program with no entry blocks");
    let ledger = Ledger::from_toml(
        "[[entry]]\nclass = \"open-old\"\nfiles = [\"tests/gate/probes/x/*.wf\"]\nfinding = \"M1\"\nreason = \"r\"\nstage = \"G6\"\n",
    )
    .unwrap_or_else(|e| panic!("the ledger does not parse: {e}"));
    let r = Report::build(std::slice::from_ref(&open), &ledger, &Policy::default());
    assert!(r.passes(), "{:?}", r.blockers);
    assert_eq!(r.rows[0].entry, Some(0));
    let md = r.to_markdown();
    for part in ["## Ledger", "open-old", "M1"] {
        assert!(md.contains(part), "the report has no `{part}`:\n{md}");
    }
}
