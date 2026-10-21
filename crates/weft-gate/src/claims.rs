//! The claims file of the gate: `tests/gate/claims.toml` (plan §2.5, stage G7).
//!
//! A [`Claim`] says what the `ir` pipeline must do with the repro of a finding
//! of `docs/ir.md` §10: reject it ([`Kind::Unsound`]), accept it ([`Kind::Fp`]
//! and [`Kind::Sound`]), run it with no fault in the IR engine
//! ([`Kind::Interp`]), or check it in a time limit ([`Kind::Speed`]).
//!
//! A claim is on when its stage is in the list `done` of the file and each
//! group of its `group` set is on in the `ir` pipeline ([`IrPipeline::groups_on`]).
//! An `interp` claim needs only its stage: the groups are a setting of the fact
//! pipeline, not of the engine. [`check_all`] checks each claim that is on,
//! and it checks that each repro exists. From stage F1 on, it also checks that
//! the `group` set of each claim equals the union of the groups that the
//! pipeline computes for its repros ([`IrPipeline::groups_of`]).
//!
//! The interface [`IrPipeline`] isolates the `ir` pipeline. Before stage F1
//! there is no `ir` pipeline: [`pipeline`] gives [`NoIrPipeline`], which has no
//! group on. Stage F1 changes [`pipeline`] to give the real pipeline.

use std::collections::BTreeMap;
use std::fmt;
use std::path::Path;

use serde::Deserialize;

use crate::classify::WARNING_CODES;
use crate::oracle::Verdict as OracleVerdict;
use crate::snapshot::Diag;
use crate::Error;

/// The claims file, relative to the repository.
pub const CLAIMS: &str = "tests/gate/claims.toml";

/// A debug build gets this many times the time limit of a `speed` claim.
pub const DEBUG_FACTOR: u64 = 20;

/// What the `ir` pipeline must do with the repro of a claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Kind {
    /// The finding is unsound: the `ir` pipeline must reject the repro.
    Unsound,
    /// The finding is a false positive: the `ir` pipeline must accept the
    /// repro (or, with a `line`, give no error at that line).
    Fp,
    /// The repro is a correct program (a control, or a repro that a fix made
    /// correct): the `ir` pipeline must accept it, as for [`Kind::Fp`].
    Sound,
    /// An interpreter defect: the IR engine must run the repro with no fault.
    Interp,
    /// A speed finding: the `ir` pipeline must check the repro in the time
    /// limit `limit_ms`.
    Speed,
}

impl Kind {
    /// The name in the claims file.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Unsound => "unsound",
            Self::Fp => "fp",
            Self::Sound => "sound",
            Self::Interp => "interp",
            Self::Speed => "speed",
        }
    }
}

/// The verdict of the finding in `docs/ir.md` §10.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Verdict {
    /// The IR removes the cause by its construction.
    Construction,
    /// One rule of the analysis or of the summaries removes the cause.
    OneRule,
    /// The cause stays (a spec rule, a type rule): the `ir` pipeline keeps the
    /// result of the old pipeline.
    Stays,
    /// The IR removes a part; the rest waits for track P.
    Partly,
    /// No verdict of the fact generator (an interpreter defect).
    None,
}

impl Verdict {
    /// The name in the claims file.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Construction => "construction",
            Self::OneRule => "one-rule",
            Self::Stays => "stays",
            Self::Partly => "partly",
            Self::None => "none",
        }
    }
}

/// A set of construct groups (plan §2.6): the letters `A` to `F`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Groups(u8);

/// The letters of the construct groups, in order.
const GROUP_LETTERS: [char; 6] = ['A', 'B', 'C', 'D', 'E', 'F'];

impl Groups {
    /// The empty set.
    pub const NONE: Self = Self(0);

    /// Reads a set: one or more letters `A` to `F`, in order, each one time.
    ///
    /// # Errors
    ///
    /// Returns a message for an empty text, a letter that is not a group, a
    /// letter that is not in order, and a letter that occurs two times.
    pub fn parse(text: &str) -> Result<Self, String> {
        if text.is_empty() {
            return Err("the group set is empty".to_string());
        }
        let mut bits = 0u8;
        let mut last = None;
        for c in text.chars() {
            let Some(i) = GROUP_LETTERS.iter().position(|g| *g == c) else {
                return Err(format!("`{c}` is not a construct group (A to F)"));
            };
            if last.is_some_and(|l| l >= i) {
                return Err(format!(
                    "the group set `{text}` must have each letter one time, in order"
                ));
            }
            last = Some(i);
            bits |= 1 << i;
        }
        Ok(Self(bits))
    }

    /// True if each group of `other` is in this set.
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    /// The groups of this set and of `other`.
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

impl fmt::Display for Groups {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, c) in GROUP_LETTERS.iter().enumerate() {
            if self.0 & (1 << i) != 0 {
                write!(f, "{c}")?;
            }
        }
        Ok(())
    }
}

/// A stage id of the plan: a phase letter and a number (`F8`, `S00`), with
/// the numbers of follow-up stages (`F8.1`, rule 5 of the plan).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Stage {
    /// The phase letter.
    pub phase: char,
    /// The number of the stage in its phase.
    pub number: u32,
    /// The numbers of the follow-up stages.
    pub follow_up: Vec<u32>,
}

/// The phases of the plan (§3 and §6) and the last stage number of each.
const PHASES: [(char, u32); 9] = [
    ('S', 0),
    ('G', 7),
    ('T', 3),
    ('B', 12),
    ('I', 6),
    ('F', 20),
    ('C', 3),
    ('R', 5),
    ('P', 8),
];

impl Stage {
    /// Reads a stage id of the plan, or gives `None`. `S00` is the only stage
    /// of phase S.
    pub fn parse(text: &str) -> Option<Self> {
        let mut parts = text.split('.');
        let head = parts.next()?;
        let mut chars = head.chars();
        let phase = chars.next()?;
        let digits = chars.as_str();
        let (_, last) = PHASES.iter().find(|(p, _)| *p == phase)?;
        let number = if phase == 'S' {
            (digits == "00").then_some(0)?
        } else {
            if digits.is_empty() || digits.starts_with('0') {
                return None;
            }
            digits
                .parse::<u32>()
                .ok()
                .filter(|n| (1..=*last).contains(n))?
        };
        let mut follow_up = Vec::new();
        for p in parts {
            if p.is_empty() || p.starts_with('0') {
                return None;
            }
            follow_up.push(p.parse::<u32>().ok()?);
        }
        Some(Self {
            phase,
            number,
            follow_up,
        })
    }
}

/// One claim of the claims file (`[[claim]]`).
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Claim {
    /// The finding id, as the ledger writes it (`M3`, `V069`, `sem-N1`).
    pub finding: String,
    /// What the `ir` pipeline must do with the repro.
    pub kind: Kind,
    /// The verdict of the finding in `docs/ir.md` §10.
    pub verdict: Verdict,
    /// The construct groups that the repros use (plan §2.6), group A included.
    pub group: String,
    /// The stage that turns the claim on (`docs/ir.md` §10.4, or the stage of
    /// the group).
    pub stage: String,
    /// The repro files, relative to the repository. No globs.
    pub repro: Vec<String>,
    /// `unsound`: the rejection must have an error with this code. `fp` and
    /// `sound` with a `line`: no error with this code at that line.
    #[serde(default)]
    pub code: Option<String>,
    /// `unsound`: the rejection must have an error at this line. `fp` and
    /// `sound`: no error at this line (the other lines can have errors).
    #[serde(default)]
    pub line: Option<usize>,
    /// `unsound` only: the codes of the errors must be these codes, with the
    /// same number of each.
    #[serde(default)]
    pub exact: Option<Vec<String>>,
    /// `speed` only: the time limit of the check of each repro, in
    /// milliseconds, for a release build ([`DEBUG_FACTOR`]).
    #[serde(default)]
    pub limit_ms: Option<u64>,
    /// A note for the reader.
    #[serde(default)]
    pub note: Option<String>,
}

impl Claim {
    /// The group set of the claim. [`ClaimsFile::from_toml`] checks it.
    pub fn groups(&self) -> Groups {
        Groups::parse(&self.group).unwrap_or(Groups::NONE)
    }

    /// A short name of the claim for a message.
    pub fn label(&self) -> String {
        let mut out = format!(
            "{} {} [{} {}]",
            self.finding,
            self.kind.name(),
            self.group,
            self.stage
        );
        if let Some(c) = &self.code {
            out.push(' ');
            out.push_str(c);
        }
        if let Some(l) = self.line {
            out.push_str(" line ");
            out.push_str(&l.to_string());
        }
        out
    }

    /// The fields that do not fit the kind of the claim, or `None`.
    fn field_problem(&self) -> Option<String> {
        let unsound = self.kind == Kind::Unsound;
        let accept = matches!(self.kind, Kind::Fp | Kind::Sound);
        if (self.code.is_some() || self.line.is_some()) && !unsound && !accept {
            return Some(format!(
                "a `{}` claim has no `code` and no `line`",
                self.kind.name()
            ));
        }
        if self.exact.is_some() && !unsound {
            return Some("only an `unsound` claim has `exact`".to_string());
        }
        if self.limit_ms.is_some() != (self.kind == Kind::Speed) {
            return Some("a `speed` claim, and only a `speed` claim, has `limit_ms`".to_string());
        }
        None
    }
}

/// The claims file: the stages that are done and the claims.
#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClaimsFile {
    /// The stages that are done. A stage that turns claims on adds its id.
    pub done: Vec<String>,
    /// The claims (`[[claim]]`), in the order of the file.
    #[serde(default, rename = "claim")]
    pub claims: Vec<Claim>,
}

impl ClaimsFile {
    /// Reads the text of a claims file.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Claims`] if the text is not TOML, if a field or a kind
    /// is unknown, if a stage id or a group set is not correct, if a claim has
    /// no repro or a repro with a glob, or if a field does not fit the kind.
    pub fn from_toml(text: &str) -> Result<Self, Error> {
        let file: Self = toml::from_str(text).map_err(|e| Error::Claims(e.to_string()))?;
        for d in &file.done {
            if Stage::parse(d).is_none() {
                return Err(Error::Claims(format!("`done` has an unknown stage `{d}`")));
            }
        }
        for (i, c) in file.claims.iter().enumerate() {
            let at = |m: String| Error::Claims(format!("claim {} ({}): {m}", i + 1, c.finding));
            if c.finding.trim().is_empty() {
                return Err(at("the claim needs a `finding`".to_string()));
            }
            let groups = Groups::parse(&c.group).map_err(at)?;
            if !groups.contains(Groups::parse("A").map_err(at)?) {
                return Err(at(format!("the group set `{}` needs group A", c.group)));
            }
            if Stage::parse(&c.stage).is_none() {
                return Err(at(format!("`{}` is not a stage of the plan", c.stage)));
            }
            if c.repro.is_empty() {
                return Err(at("the claim needs one or more repro files".to_string()));
            }
            if let Some(r) = c
                .repro
                .iter()
                .find(|r| r.trim().is_empty() || r.contains(['*', '?', '[']))
            {
                return Err(at(format!("`{r}` is not a file path (no globs)")));
            }
            if let Some(m) = c.field_problem() {
                return Err(at(m));
            }
        }
        Ok(file)
    }

    /// Reads the claims file `path`.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Io`] if the file cannot be read, and the errors of
    /// [`ClaimsFile::from_toml`].
    pub fn read(path: &Path) -> Result<Self, Error> {
        let text = std::fs::read_to_string(path).map_err(|e| Error::io(path, e))?;
        Self::from_toml(&text).map_err(|e| match e {
            Error::Claims(m) => Error::Claims(format!("{}: {m}", path.display())),
            other => other,
        })
    }

    /// True if the stage `stage` is in the list `done`.
    pub fn is_done(&self, stage: &str) -> bool {
        let Some(s) = Stage::parse(stage) else {
            return false;
        };
        self.done
            .iter()
            .any(|d| Stage::parse(d).as_ref() == Some(&s))
    }

    /// The problems of the file in the repository `repo`: each repro that is
    /// not a file or a directory.
    pub fn problems(&self, repo: &Path) -> Vec<String> {
        let mut out = Vec::new();
        for c in &self.claims {
            for r in &c.repro {
                if !repo.join(r).exists() {
                    out.push(format!("{}: the repro `{r}` does not exist", c.label()));
                }
            }
        }
        out
    }
}

/// The errors of one check of a repro by the `ir` pipeline.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Checked {
    /// The diagnostics `(code, file, line)`. The warnings
    /// ([`WARNING_CODES`]) are not errors; [`evaluate`] ignores them.
    pub errors: Vec<Diag>,
    /// The time of the check, in milliseconds.
    pub ms: u64,
}

/// The `ir` pipeline, as the claims test sees it.
pub trait IrPipeline {
    /// The construct groups that are on (`Options::ir_groups`, plan §2.6).
    fn groups_on(&self) -> Groups;

    /// The construct groups that the program `repro` uses (the scope of
    /// `irbuild/scope.rs`), or `None` before stage F1.
    ///
    /// # Errors
    ///
    /// Returns a message if the program cannot be read or loaded.
    fn groups_of(&self, repo: &Path, repro: &str) -> Result<Option<Groups>, String>;

    /// Checks the program `repro` with the `ir` pipeline.
    ///
    /// # Errors
    ///
    /// Returns a message if the pipeline panics or does not end, or if the
    /// program cannot be read.
    fn check(&self, repo: &Path, repro: &str) -> Result<Checked, String>;

    /// The verdict of the oracle with the IR engine for the program `repro`
    /// (from the cache of plan §2.4; the claims test does not run the
    /// interpreter).
    ///
    /// # Errors
    ///
    /// Returns a message if there is no verdict.
    fn engine_verdict(&self, repo: &Path, repro: &str) -> Result<OracleVerdict, String>;
}

/// The pipeline before stage F1: no group is on, and no claim of a group
/// stage can be on.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoIrPipeline;

/// The message of [`NoIrPipeline`].
pub const NO_IR_PIPELINE: &str = "no ir pipeline before stage F1";

impl IrPipeline for NoIrPipeline {
    fn groups_on(&self) -> Groups {
        Groups::NONE
    }

    fn groups_of(&self, _repo: &Path, _repro: &str) -> Result<Option<Groups>, String> {
        Ok(None)
    }

    fn check(&self, _repo: &Path, _repro: &str) -> Result<Checked, String> {
        Err(NO_IR_PIPELINE.to_string())
    }

    fn engine_verdict(&self, repo: &Path, repro: &str) -> Result<OracleVerdict, String> {
        ir_oracle_verdict(repo, repro)
    }
}

/// The verdict of the oracle of the IR engine for the program `repro` of the
/// repository `repo`.
///
/// The verdict comes from the committed tier-1 cache `tests/gate/oracle-ir.tsv`
/// (stage I5), with the hash of the interpreter sources of today.
///
/// # Errors
///
/// Returns a message if the cache or the program cannot be read, or if the
/// cache has no verdict for the program.
pub fn ir_oracle_verdict(repo: &Path, repro: &str) -> Result<OracleVerdict, String> {
    use sha2::{Digest as _, Sha256};
    let engine = crate::oracle::Engine::Ir;
    let file = repo
        .join("tests/gate")
        .join(crate::oracle::cache_name(engine));
    let text = std::fs::read_to_string(&file).map_err(|e| format!("{}: {e}", file.display()))?;
    let cache = crate::oracle::Cache::from_tsv(&text).map_err(|e| e.to_string())?;
    let interp = crate::oracle::interp_hash(repo).map_err(|e| e.to_string())?;
    let path = repo.join(repro);
    let hash = if path.is_dir() {
        crate::manifest::package_hash(&path).map_err(|e| e.to_string())?
    } else {
        let bytes = std::fs::read(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        crate::manifest::hex(&Sha256::digest(&bytes))
    };
    cache
        .get(&hash, engine, &interp)
        .map(|r| r.verdict)
        .ok_or_else(|| {
            format!(
                "`{}` has no verdict for {repro} with the interpreter hash {interp}: run `cargo run -p weft-gate --release -- oracle --engine ir --tier 1`",
                file.display()
            )
        })
}

/// The `ir` pipeline of the claims test. Before stage F1: [`NoIrPipeline`].
pub fn pipeline() -> Box<dyn IrPipeline> {
    Box::new(NoIrPipeline)
}

/// The result of one claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// The claim is off, with the reason.
    Off(String),
    /// The claim is on and it holds.
    Holds,
    /// The claim is on and it does not hold, with the reason.
    Fails(String),
}

/// The errors of `checked`: the diagnostics that are not warnings.
fn errors(checked: &Checked) -> Vec<&Diag> {
    checked
        .errors
        .iter()
        .filter(|d| !WARNING_CODES.contains(&d.0.as_str()))
        .collect()
}

/// The text of a list of errors for a message.
fn show(errors: &[&Diag]) -> String {
    if errors.is_empty() {
        return "no error".to_string();
    }
    let v: Vec<String> = errors.iter().map(|d| format!("{}@{}", d.0, d.2)).collect();
    v.join(", ")
}

/// The reason that `claim` is off, or `None` if it is on.
fn off_reason(file: &ClaimsFile, claim: &Claim, pipe: &dyn IrPipeline) -> Option<String> {
    if !file.is_done(&claim.stage) {
        return Some(format!("stage {} is not done", claim.stage));
    }
    if claim.kind != Kind::Interp && !pipe.groups_on().contains(claim.groups()) {
        return Some(format!(
            "group set {} is not on (on: `{}`)",
            claim.group,
            pipe.groups_on()
        ));
    }
    None
}

/// Checks one repro of an `unsound` claim. Gives the reason of a failure.
fn reject_problem(claim: &Claim, errors: &[&Diag]) -> Option<String> {
    if let Some(exact) = &claim.exact {
        let mut want: Vec<&str> = exact.iter().map(String::as_str).collect();
        let mut got: Vec<&str> = errors.iter().map(|d| d.0.as_str()).collect();
        want.sort_unstable();
        got.sort_unstable();
        return (want != got).then(|| {
            format!(
                "the errors must have exactly the codes {want:?}, but they are {}",
                show(errors)
            )
        });
    }
    let fits = |d: &&&Diag| {
        claim.code.as_ref().is_none_or(|c| &d.0 == c) && claim.line.is_none_or(|l| d.2 == l)
    };
    if errors.iter().any(|d| fits(&d)) {
        return None;
    }
    let mut want = "an error".to_string();
    if let Some(c) = &claim.code {
        want.push(' ');
        want.push_str(c);
    }
    if let Some(l) = claim.line {
        want.push_str(" at line ");
        want.push_str(&l.to_string());
    }
    Some(format!(
        "the ir pipeline must give {want}, but it gives {}",
        show(errors)
    ))
}

/// Checks one repro of an `fp` or `sound` claim. Gives the reason of a failure.
fn accept_problem(claim: &Claim, errors: &[&Diag]) -> Option<String> {
    let bad: Vec<&Diag> = errors
        .iter()
        .copied()
        .filter(|d| {
            claim.line.is_none_or(|l| d.2 == l) && claim.code.as_ref().is_none_or(|c| &d.0 == c)
        })
        .collect();
    if bad.is_empty() {
        return None;
    }
    let place = claim
        .line
        .map_or_else(String::new, |l| format!(" at line {l}"));
    Some(format!(
        "the ir pipeline must accept the repro{place}, but it gives {}",
        show(&bad)
    ))
}

/// Evaluates one claim of `file` in the repository `repo` with the pipeline
/// `pipe`.
pub fn evaluate(file: &ClaimsFile, claim: &Claim, repo: &Path, pipe: &dyn IrPipeline) -> Outcome {
    if let Some(reason) = off_reason(file, claim, pipe) {
        return Outcome::Off(reason);
    }
    for r in &claim.repro {
        let problem = match claim.kind {
            Kind::Interp => match pipe.engine_verdict(repo, r) {
                Ok(OracleVerdict::Fault) => {
                    Some("the oracle of the IR engine faults on the repro".to_string())
                }
                Ok(_) => None,
                Err(e) => Some(e),
            },
            kind => match pipe.check(repo, r) {
                Err(e) => Some(e),
                Ok(checked) => {
                    let errs = errors(&checked);
                    match kind {
                        Kind::Unsound => reject_problem(claim, &errs),
                        Kind::Fp | Kind::Sound => accept_problem(claim, &errs),
                        _ => {
                            let limit = claim.limit_ms.unwrap_or(0);
                            let limit = if cfg!(debug_assertions) {
                                limit.saturating_mul(DEBUG_FACTOR)
                            } else {
                                limit
                            };
                            (checked.ms > limit).then(|| {
                                format!(
                                    "the check takes {} ms; the limit is {limit} ms",
                                    checked.ms
                                )
                            })
                        }
                    }
                }
            },
        };
        if let Some(p) = problem {
            return Outcome::Fails(format!("{r}: {p}"));
        }
    }
    Outcome::Holds
}

/// The result of [`check_all`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Report {
    /// The outcome of each claim, in the order of the file, with its label.
    pub outcomes: Vec<(String, Outcome)>,
    /// The problems of the file ([`ClaimsFile::problems`]) and the claims
    /// whose group set is not the scope of their repros.
    pub problems: Vec<String>,
}

impl Report {
    /// Each problem and each claim that fails.
    pub fn failures(&self) -> Vec<String> {
        let mut out = self.problems.clone();
        for (label, o) in &self.outcomes {
            if let Outcome::Fails(why) = o {
                out.push(format!("{label}: {why}"));
            }
        }
        out
    }

    /// One line with the number of claims that are off, that hold and that fail.
    pub fn summary(&self) -> String {
        let mut n: BTreeMap<&str, usize> = BTreeMap::new();
        for (_, o) in &self.outcomes {
            let k = match o {
                Outcome::Off(_) => "off",
                Outcome::Holds => "hold",
                Outcome::Fails(_) => "fail",
            };
            *n.entry(k).or_default() += 1;
        }
        format!(
            "{} claims: {} off, {} hold, {} fail; {} problems",
            self.outcomes.len(),
            n.get("off").copied().unwrap_or(0),
            n.get("hold").copied().unwrap_or(0),
            n.get("fail").copied().unwrap_or(0),
            self.problems.len()
        )
    }
}

/// Checks the claims of `file` in the repository `repo` with the pipeline `pipe`.
///
/// The check finds each repro that does not exist, each claim whose group set
/// is not the scope of its repros (when the pipeline computes the scope), and
/// each claim that is on and does not hold.
pub fn check_all(file: &ClaimsFile, repo: &Path, pipe: &dyn IrPipeline) -> Report {
    let mut report = Report {
        problems: file.problems(repo),
        ..Report::default()
    };
    for c in &file.claims {
        let mut scope = Some(Groups::NONE);
        for r in c.repro.iter().filter(|r| repo.join(r).exists()) {
            match pipe.groups_of(repo, r) {
                Ok(Some(g)) => scope = scope.map(|s| s.union(g)),
                Ok(None) => scope = None,
                Err(e) => {
                    report.problems.push(format!("{}: {r}: {e}", c.label()));
                    scope = None;
                }
            }
        }
        if let Some(s) = scope.filter(|s| *s != Groups::NONE && *s != c.groups()) {
            report.problems.push(format!(
                "{}: the group set is {}, but the repros use {s}",
                c.label(),
                c.group
            ));
        }
        let outcome = if c.repro.iter().all(|r| repo.join(r).exists()) {
            evaluate(file, c, repo, pipe)
        } else {
            Outcome::Fails("a repro does not exist".to_string())
        };
        report.outcomes.push((c.label(), outcome));
    }
    report
}
