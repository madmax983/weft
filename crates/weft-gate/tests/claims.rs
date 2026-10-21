//! The claims test (plan `docs/plan/core-ir.md`, §2.5 and stage G7).
//!
//! The claims file `tests/gate/claims.toml` holds a claim for each verdict
//! "construction" or "one rule" of `docs/ir.md` §10 that has a repro, and for
//! each row of `docs/ir.md` §10.4. A claim is on when its stage is done and
//! each group of its `group` set is on. Then the `ir` pipeline must reject an
//! `unsound` repro and accept an `fp` or `sound` repro.
//!
//! The synthetic tests use a fake pipeline. The test of the committed file
//! uses [`claims::pipeline`]: before stage F1 there is no `ir` pipeline, no
//! group is on, and each claim is off. The test then checks only that each
//! repro exists. The test does not run the interpreter.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use weft_gate::claims::{
    self, Checked, ClaimsFile, Groups, IrPipeline, NoIrPipeline, Outcome, Stage,
};
use weft_gate::oracle::Verdict;
use weft_gate::snapshot::Diag;

fn repo() -> PathBuf {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    fs::canonicalize(&dir).unwrap_or(dir)
}

/// A pipeline with fixed answers, for the synthetic tests.
#[derive(Default)]
struct Fake {
    on: &'static str,
    errors: BTreeMap<String, Vec<(&'static str, usize)>>,
    groups: BTreeMap<String, &'static str>,
    engine: BTreeMap<String, Verdict>,
    ms: u64,
    broken: BTreeSet<String>,
}

impl IrPipeline for Fake {
    fn groups_on(&self) -> Groups {
        Groups::parse(self.on).unwrap_or(Groups::NONE)
    }

    fn groups_of(&self, _repo: &Path, repro: &str) -> Result<Option<Groups>, String> {
        self.groups.get(repro).map(|g| Groups::parse(g)).transpose()
    }

    fn check(&self, _repo: &Path, repro: &str) -> Result<Checked, String> {
        if self.broken.contains(repro) {
            return Err(format!("the pipeline panicked on {repro}"));
        }
        let errors = self
            .errors
            .get(repro)
            .map(|v| {
                v.iter()
                    .map(|(c, l)| Diag((*c).to_string(), repro.to_string(), *l))
                    .collect()
            })
            .unwrap_or_default();
        Ok(Checked {
            errors,
            ms: self.ms,
        })
    }

    fn engine_verdict(&self, _repo: &Path, repro: &str) -> Result<Verdict, String> {
        self.engine
            .get(repro)
            .copied()
            .ok_or_else(|| format!("no verdict for {repro}"))
    }
}

/// A temporary repository with the files `files` (empty text).
fn tree(files: &[&str]) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("make a temporary directory");
    for f in files {
        let path = dir.path().join(f);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("make the directory");
        }
        fs::write(&path, "fn main() {}\n").expect("write the file");
    }
    dir
}

/// A claims file with `done` and one claim with the fields `fields`.
fn one(done: &str, fields: &str) -> ClaimsFile {
    let text = format!("done = [{done}]\n\n[[claim]]\n{fields}\n");
    ClaimsFile::from_toml(&text).unwrap_or_else(|e| panic!("parse {text}: {e}"))
}

const R: &str = "tests/gate/probes/x/r.wf";

fn claim_fields(kind: &str, group: &str, stage: &str, extra: &str) -> String {
    format!(
        "finding = \"T1\"\nkind = \"{kind}\"\nverdict = \"construction\"\ngroup = \"{group}\"\n\
         stage = \"{stage}\"\nrepro = [\"{R}\"]\n{extra}"
    )
}

fn outcome(file: &ClaimsFile, root: &Path, pipe: &dyn IrPipeline) -> Outcome {
    let claim = file.claims.first().expect("one claim");
    claims::evaluate(file, claim, root, pipe)
}

const fn fails(o: &Outcome) -> bool {
    matches!(o, Outcome::Fails(_))
}

// ---------------------------------------------------------------- the syntax

#[test]
fn groups_parse_and_print() {
    let g = Groups::parse("ACE").expect("parse ACE");
    assert_eq!(g.to_string(), "ACE");
    assert!(g.contains(Groups::parse("AE").expect("parse AE")));
    assert!(!g.contains(Groups::parse("AD").expect("parse AD")));
    assert!(Groups::parse("AX").is_err());
    assert!(Groups::parse("CA").is_err(), "the letters must be in order");
    assert!(Groups::parse("AA").is_err());
    assert!(Groups::parse("").is_err());
    assert_eq!(
        Groups::parse("AC")
            .expect("AC")
            .union(Groups::parse("AE").expect("AE"))
            .to_string(),
        "ACE"
    );
}

#[test]
fn stages_parse() {
    for s in [
        "S00", "G7", "T3", "B12", "I3", "F8", "F20", "F8.1", "C3", "R5", "P1", "P8",
    ] {
        assert!(Stage::parse(s).is_some(), "{s}");
    }
    for s in ["F21", "G0", "S1", "X1", "F", "F8.", "B13", "P9", "f8"] {
        assert!(Stage::parse(s).is_none(), "{s}");
    }
}

#[test]
fn bad_claims_do_not_parse() {
    let bad = [
        claim_fields("unsure", "A", "F8", ""),
        claim_fields("unsound", "AX", "F8", ""),
        claim_fields("unsound", "A", "F99", ""),
        claim_fields("interp", "A", "I3", "line = 3"),
        claim_fields("unsound", "A", "F8", "limit_ms = 10"),
        claim_fields("speed", "A", "F12", ""),
        claim_fields("fp", "A", "F8", "exact = [\"W0301\"]"),
        claim_fields("unsound", "A", "F8", "unknown = 1"),
        "finding = \"T1\"\nkind = \"unsound\"\nverdict = \"construction\"\ngroup = \"A\"\n\
         stage = \"F8\"\nrepro = []"
            .to_string(),
        "finding = \"T1\"\nkind = \"unsound\"\nverdict = \"construction\"\ngroup = \"A\"\n\
         stage = \"F8\"\nrepro = [\"tests/gate/probes/*.wf\"]"
            .to_string(),
    ];
    for fields in &bad {
        let text = format!("done = [\"G7\"]\n\n[[claim]]\n{fields}\n");
        assert!(
            ClaimsFile::from_toml(&text).is_err(),
            "this claim must not parse:\n{fields}"
        );
    }
    assert!(ClaimsFile::from_toml("done = [\"Z9\"]\n").is_err());
}

// ---------------------------------------------------- (a) the repro must exist

#[test]
fn a_claim_whose_repro_does_not_exist_fails() {
    let root = tree(&[]);
    let file = one("\"G7\"", &claim_fields("unsound", "AD", "F15", ""));
    let problems = file.problems(root.path());
    assert!(
        problems.iter().any(|p| p.contains(R)),
        "no problem for the missing repro: {problems:?}"
    );
    let report = claims::check_all(&file, root.path(), &NoIrPipeline);
    assert!(
        report.failures().iter().any(|f| f.contains(R)),
        "the missing repro does not fail the check: {:?}",
        report.failures()
    );
}

// ------------------------------------------------- (b) a claim of an off group

#[test]
fn a_claim_whose_group_is_off_is_skipped() {
    let root = tree(&[R]);
    // The pipeline would accept the unsound repro, so an `on` claim fails.
    let fake = Fake {
        on: "A",
        ..Fake::default()
    };
    let file = one("\"G7\", \"F15\"", &claim_fields("unsound", "AD", "F15", ""));
    assert!(matches!(
        outcome(&file, root.path(), &fake),
        Outcome::Off(_)
    ));
    // The group is on, but the stage is not done.
    let fake = Fake {
        on: "AD",
        ..Fake::default()
    };
    let file = one("\"G7\"", &claim_fields("unsound", "AD", "F15", ""));
    assert!(matches!(
        outcome(&file, root.path(), &fake),
        Outcome::Off(_)
    ));
    // Both: the claim is on, and it fails.
    let file = one("\"G7\", \"F15\"", &claim_fields("unsound", "AD", "F15", ""));
    assert!(fails(&outcome(&file, root.path(), &fake)));
    let report = claims::check_all(&file, root.path(), &fake);
    assert_eq!(report.failures().len(), 1);
}

#[test]
fn with_no_ir_pipeline_each_claim_is_off() {
    let root = tree(&[R]);
    let file = one(
        "\"G7\", \"F8\", \"F15\"",
        &claim_fields("unsound", "A", "F8", ""),
    );
    assert!(matches!(
        outcome(&file, root.path(), &NoIrPipeline),
        Outcome::Off(_)
    ));
    assert!(claims::check_all(&file, root.path(), &NoIrPipeline)
        .failures()
        .is_empty());
}

// ---------------------------------- (c) the ir pipeline must keep the claim

fn on_fake(errors: &[(&'static str, usize)]) -> Fake {
    let mut fake = Fake {
        on: "ABCDEF",
        ..Fake::default()
    };
    fake.errors.insert(R.to_string(), errors.to_vec());
    fake
}

fn eval(kind: &str, extra: &str, errors: &[(&'static str, usize)]) -> Outcome {
    let root = tree(&[R]);
    let file = one("\"G7\", \"F8\"", &claim_fields(kind, "A", "F8", extra));
    outcome(&file, root.path(), &on_fake(errors))
}

#[test]
fn an_unsound_repro_that_ir_accepts_fails() {
    assert!(fails(&eval("unsound", "", &[])));
    assert!(
        fails(&eval("unsound", "", &[("W0804", 3)])),
        "a warning is not an error"
    );
    assert_eq!(eval("unsound", "", &[("W0301", 9)]), Outcome::Holds);
    // The code and the line of the claim.
    assert_eq!(
        eval("unsound", "code = \"W0301\"", &[("W0301", 9)]),
        Outcome::Holds
    );
    assert!(fails(&eval("unsound", "code = \"W0301\"", &[("W0405", 9)])));
    assert_eq!(eval("unsound", "line = 9", &[("W0405", 9)]), Outcome::Holds);
    assert!(fails(&eval("unsound", "line = 9", &[("W0405", 10)])));
    assert!(fails(&eval(
        "unsound",
        "code = \"W0301\"\nline = 9",
        &[("W0301", 10), ("W0405", 9)]
    )));
    // The exact multiset of codes.
    assert_eq!(
        eval("unsound", "exact = [\"W0601\"]", &[("W0601", 6)]),
        Outcome::Holds
    );
    assert!(fails(&eval(
        "unsound",
        "exact = [\"W0601\"]",
        &[("W0601", 6), ("W0602", 4)]
    )));
}

#[test]
fn an_fp_repro_that_ir_rejects_at_the_claimed_line_fails() {
    assert_eq!(eval("fp", "", &[]), Outcome::Holds);
    assert!(fails(&eval("fp", "", &[("W0301", 9)])));
    assert_eq!(
        eval("fp", "", &[("W0804", 9)]),
        Outcome::Holds,
        "a warning is not an error"
    );
    assert!(fails(&eval("fp", "line = 9", &[("W0301", 9)])));
    assert_eq!(eval("fp", "line = 9", &[("W0301", 12)]), Outcome::Holds);
    assert_eq!(
        eval("fp", "line = 9\ncode = \"W0312\"", &[("W0301", 9)]),
        Outcome::Holds
    );
    assert!(fails(&eval(
        "fp",
        "line = 9\ncode = \"W0312\"",
        &[("W0312", 9)]
    )));
    // A correct program has the rules of `fp`.
    assert_eq!(eval("sound", "", &[]), Outcome::Holds);
    assert!(fails(&eval("sound", "", &[("W0601", 2)])));
}

#[test]
fn a_crash_of_the_pipeline_fails_an_on_claim() {
    let root = tree(&[R]);
    let mut fake = on_fake(&[]);
    fake.broken.insert(R.to_string());
    for kind in ["unsound", "fp"] {
        let file = one("\"G7\", \"F8\"", &claim_fields(kind, "A", "F8", ""));
        assert!(fails(&outcome(&file, root.path(), &fake)), "{kind}");
    }
}

#[test]
fn a_speed_claim_has_a_time_limit() {
    let root = tree(&[R]);
    let file = one(
        "\"G7\", \"F12\"",
        &claim_fields("speed", "AC", "F12", "limit_ms = 1000"),
    );
    let mut fake = on_fake(&[("W0301", 3)]);
    assert_eq!(outcome(&file, root.path(), &fake), Outcome::Holds);
    fake.ms = 1_000_000;
    assert!(fails(&outcome(&file, root.path(), &fake)));
    fake.ms = 0;
    fake.broken.insert(R.to_string());
    assert!(fails(&outcome(&file, root.path(), &fake)));
}

#[test]
fn an_interp_claim_reads_the_engine_verdict() {
    let root = tree(&[R]);
    // The groups of the fact pipeline do not apply to the engine.
    let mut fake = Fake::default();
    let file = one("\"G7\", \"I3\"", &claim_fields("interp", "AD", "I3", ""));
    assert!(fails(&outcome(&file, root.path(), &fake)), "no verdict");
    fake.engine.insert(R.to_string(), Verdict::Fault);
    assert!(fails(&outcome(&file, root.path(), &fake)));
    fake.engine.insert(R.to_string(), Verdict::Clean);
    assert_eq!(outcome(&file, root.path(), &fake), Outcome::Holds);
    let file = one("\"G7\"", &claim_fields("interp", "AD", "I3", ""));
    assert!(matches!(
        outcome(&file, root.path(), &fake),
        Outcome::Off(_)
    ));
}

#[test]
fn the_group_set_must_equal_the_scope_of_the_repro() {
    let root = tree(&[R]);
    let file = one("\"G7\"", &claim_fields("unsound", "AD", "F15", ""));
    // Before F1 the pipeline does not compute the scope: no check.
    assert!(claims::check_all(&file, root.path(), &Fake::default())
        .failures()
        .is_empty());
    let mut fake = Fake::default();
    fake.groups.insert(R.to_string(), "AD");
    assert!(claims::check_all(&file, root.path(), &fake)
        .failures()
        .is_empty());
    fake.groups.insert(R.to_string(), "ACD");
    let failures = claims::check_all(&file, root.path(), &fake).failures();
    assert!(
        failures.iter().any(|f| f.contains("ACD")),
        "a wrong group set does not fail: {failures:?}"
    );
}

// ------------------------------------------------------ the committed claims

fn committed() -> ClaimsFile {
    ClaimsFile::read(&repo().join(claims::CLAIMS))
        .unwrap_or_else(|e| panic!("read {}: {e}", claims::CLAIMS))
}

#[test]
fn the_committed_claims_hold() {
    let repo = repo();
    let file = committed();
    let problems = file.problems(&repo);
    assert!(problems.is_empty(), "{}", problems.join("\n"));
    let pipe = claims::pipeline();
    let report = claims::check_all(&file, &repo, pipe.as_ref());
    eprintln!("{}", report.summary());
    let failures = report.failures();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(file.claims.len() > 200, "{} claims", file.claims.len());
}

/// The ids of the rows of `docs/ir.md` §10.4 and the stage of each row.
fn rows_of_ir_10_4() -> Vec<(String, String)> {
    let text = fs::read_to_string(repo().join("docs/ir.md")).expect("read docs/ir.md");
    let start = text.find("### 10.4 ").expect("docs/ir.md has section 10.4");
    let rest = text.get(start..).unwrap_or_default();
    let end = rest.find("\n## ").unwrap_or(rest.len());
    let mut out = Vec::new();
    for line in rest.get(..end).unwrap_or_default().lines() {
        let cells: Vec<&str> = line.split('|').map(str::trim).collect();
        if cells.len() != 9 {
            continue;
        }
        let (Some(id), Some(stage)) = (cells.get(1), cells.get(7)) else {
            continue;
        };
        if *id == "Id" || id.starts_with('-') {
            continue;
        }
        // "FD1 (= QA2)" is FD1; "N1 (issues)" is the finding N1 of `r3/issues.md`.
        let id = if id.starts_with("N1 (issues)") {
            "issues-N1".to_string()
        } else {
            id.split_whitespace().next().unwrap_or_default().to_string()
        };
        out.push((id, (*stage).to_string()));
    }
    out
}

#[test]
fn each_row_of_ir_10_4_has_a_claim_at_its_stage() {
    let file = committed();
    let rows = rows_of_ir_10_4();
    // 26 rows of round 2, 20 of round 3 and 14 items.
    assert_eq!(rows.len(), 60, "{rows:?}");
    let missing: Vec<String> = rows
        .iter()
        .filter(|(id, stage)| {
            !file
                .claims
                .iter()
                .any(|c| &c.finding == id && &c.stage == stage)
        })
        .map(|(id, stage)| format!("{id} ({stage})"))
        .collect();
    assert!(missing.is_empty(), "rows with no claim: {missing:?}");
}

#[test]
fn each_new_finding_of_ir_10_2_has_a_claim() {
    let file = committed();
    let ids = [
        "M1", "M2", "M3", "M4", "J1", "J2", "J3", "J4", "J5", "J5d", "J6", "map-N1", "map-N2",
        "sem-N1", "sem-N2", "sem-N3", "sem-N4",
    ];
    let missing: Vec<&str> = ids
        .iter()
        .copied()
        .filter(|id| !file.claims.iter().any(|c| c.finding == *id))
        .collect();
    assert!(missing.is_empty(), "no claim: {missing:?}");
}

#[test]
fn each_finding_has_a_claim_or_a_comment_line() {
    let repo = repo();
    let file = committed();
    let text = fs::read_to_string(repo.join(claims::CLAIMS)).expect("read the claims file");
    let data = fs::read_to_string(repo.join("docs/plan/core-ir-inputs/findings.py"))
        .expect("read findings.py");
    let mut ids = Vec::new();
    for line in data.lines() {
        let Some(rest) = line.trim_start().strip_prefix("(\"") else {
            continue;
        };
        // The rows of ROWS have six fields; the rows of CLASSES have three.
        if rest.matches("\", \"").count() < 4 {
            continue;
        }
        if let Some((id, _)) = rest.split_once('"') {
            ids.push(id.to_string());
        }
    }
    assert!(ids.len() > 280, "{} findings", ids.len());
    let missing: Vec<&String> = ids
        .iter()
        .filter(|id| {
            !file.claims.iter().any(|c| &&c.finding == id)
                && !text.lines().any(|l| l.starts_with(&format!("# {id}: ")))
        })
        .collect();
    assert!(
        missing.is_empty(),
        "no claim and no comment line: {missing:?}"
    );
}
