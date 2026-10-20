//! The classes of plan §2.5: one class for each program, from the records of
//! the two pipelines and the oracle verdict.
//!
//! Let `D_old` and `D_ir` be the errors of the two records ([`errors`]) and `O`
//! the oracle verdict of the engine of the `ir` pipeline. A program "accepts"
//! when it has no error. [`classify`] gives the first class that applies, in
//! this order:
//!
//! 1. [`Class::Crash`]: the `ir` record is a panic, it has a problem
//!    ([`Record::problems`]), or it is a timeout and the `old` record is not.
//! 2. [`Class::LostFault`]: `old` rejects, `ir` accepts, `O` is `fault`.
//! 3. [`Class::Open`]: `ir` accepts and `O` is `fault` (then `old` accepts).
//! 4. [`Class::Same`]: `D_ir == D_old`.
//! 5. [`Class::Fixed`] or [`Class::NewFp`]: `old` accepts and `ir` rejects;
//!    `fixed` if `O` is `fault`.
//! 6. [`Class::LostClean`]: `old` rejects and `ir` accepts (`O` is not `fault`).
//! 7. [`Class::Moved`]: both reject with the same codes and counts.
//! 8. [`Class::Changed`]: both reject with other codes or counts.
//!
//! A record that is not [`Kind::Ok`] has one error whose code is the name of
//! its kind (for example `timeout`). Thus two timeouts are `same`, and a
//! timeout of `old` only is a rejection of `old`.

use std::collections::BTreeMap;

use crate::oracle::Verdict;
use crate::snapshot::{Diag, Kind, Record};

/// The codes of the diagnostics that are warnings, not errors: an unknown
/// file marker (`weft_cli::package`) and a user lint (`weft lint`). A
/// warning does not reject a program.
pub const WARNING_CODES: [&str; 2] = ["W0804", "L0001"];

/// The class of a program (plan §2.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Class {
    /// The `ir` pipeline panics or does not end, or it has a problem.
    Crash,
    /// The errors are the same.
    Same,
    /// The `ir` pipeline accepts a program that the oracle faults on.
    Open,
    /// `old` accepts, `ir` rejects, and the oracle faults.
    Fixed,
    /// `old` accepts, `ir` rejects, and the oracle does not fault.
    NewFp,
    /// `old` rejects, `ir` accepts, and the oracle faults.
    LostFault,
    /// `old` rejects, `ir` accepts, and the oracle does not fault.
    LostClean,
    /// Both reject with the same codes and counts, on other lines.
    Moved,
    /// Both reject with other codes or counts.
    Changed,
}

impl Class {
    /// All the classes, in the order of the report.
    pub const ALL: [Self; 9] = [
        Self::Crash,
        Self::Same,
        Self::Open,
        Self::Fixed,
        Self::NewFp,
        Self::LostFault,
        Self::LostClean,
        Self::Moved,
        Self::Changed,
    ];

    /// The name in the plan and in the report.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Crash => "crash",
            Self::Same => "same",
            Self::Open => "open",
            Self::Fixed => "fixed",
            Self::NewFp => "new-fp",
            Self::LostFault => "lost-fault",
            Self::LostClean => "lost-clean",
            Self::Moved => "moved",
            Self::Changed => "changed",
        }
    }

    /// Returns the class with the name `name`, or `None`.
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|c| c.name() == name)
    }
}

/// The errors of a record, in sorted order (a multiset).
///
/// For a record of kind [`Kind::Ok`], the diagnostics that are not
/// [`WARNING_CODES`]. For another kind, one error whose code is the name of
/// the kind, on line 0 of the path of the record.
pub fn errors(r: &Record) -> Vec<Diag> {
    if r.kind != Kind::Ok {
        return vec![Diag(r.kind.name().to_string(), r.path.clone(), 0)];
    }
    let mut out: Vec<Diag> = r
        .diagnostics
        .iter()
        .filter(|d| !WARNING_CODES.contains(&d.0.as_str()))
        .cloned()
        .collect();
    out.sort();
    out
}

/// The number of errors of each code.
fn code_counts(errors: &[Diag]) -> BTreeMap<&str, usize> {
    let mut out = BTreeMap::new();
    for d in errors {
        *out.entry(d.0.as_str()).or_default() += 1;
    }
    out
}

/// The codes whose count is different in `a` and `b`, in order. For two
/// multisets with the same counts, the codes whose lines are different.
pub fn changed_codes(a: &[Diag], b: &[Diag]) -> Vec<String> {
    let (ca, cb) = (code_counts(a), code_counts(b));
    let mut out: Vec<String> = ca
        .keys()
        .chain(cb.keys())
        .filter(|c| ca.get(*c) != cb.get(*c))
        .map(ToString::to_string)
        .collect();
    if out.is_empty() {
        out = a
            .iter()
            .filter(|d| !b.contains(d))
            .chain(b.iter().filter(|d| !a.contains(d)))
            .map(|d| d.0.clone())
            .collect();
    }
    out.sort();
    out.dedup();
    out
}

/// The class of a program whose records are `old` and `ir` and whose oracle
/// verdict is `verdict` (see the module text for the order of the rules).
pub fn classify(old: &Record, ir: &Record, verdict: Verdict) -> Class {
    let ir_hangs = ir.kind == Kind::Timeout && old.kind != Kind::Timeout;
    if ir.kind == Kind::Crash || !ir.problems.is_empty() || ir_hangs {
        return Class::Crash;
    }
    let (d_old, d_ir) = (errors(old), errors(ir));
    let fault = verdict == Verdict::Fault;
    match (d_old.is_empty(), d_ir.is_empty()) {
        (false, true) if fault => Class::LostFault,
        (_, true) if fault => Class::Open,
        _ if d_old == d_ir => Class::Same,
        (true, _) if fault => Class::Fixed,
        (true, _) => Class::NewFp,
        (false, true) => Class::LostClean,
        (false, false) if code_counts(&d_old) == code_counts(&d_ir) => Class::Moved,
        (false, false) => Class::Changed,
    }
}
