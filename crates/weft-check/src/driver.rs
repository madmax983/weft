//! The check pipeline: parse, analyze, check, diagnose.

use weft_sema::{Analysis, Options};
use weft_syntax::diag::{Diagnostic, Severity};
use weft_syntax::SourceFile;

use weft_facts::{FnFacts, Violations};

use crate::bridge::{self, SpecError};
use crate::diagnose::{diagnose_marked, resolve_lines};
use crate::evidence;
use crate::rules::{check, Report};

/// The result of checking a program.
#[derive(Clone, Debug)]
pub struct Checked {
    /// The analysis, with all facts.
    pub analysis: Analysis,
    /// One checker report per body, in the order of `analysis.bodies`.
    pub reports: Vec<Report>,
    /// All diagnostics, sorted by unit and location.
    pub diags: Vec<Diagnostic>,
}

impl Checked {
    /// Returns true if no error was found.
    pub fn ok(&self) -> bool {
        !self.diags.iter().any(|d| d.severity == Severity::Error)
    }

    /// Returns the codes of all diagnostics, in order.
    pub fn codes(&self) -> Vec<String> {
        self.diags.iter().map(|d| d.code.clone()).collect()
    }
}

/// Runs the production checker on every body of an analysis.
///
/// `files[u]` is the source of unit `u`; it resolves line numbers in notes.
pub fn check_analysis(analysis: Analysis, files: &[SourceFile]) -> Checked {
    let mut diags = analysis.diags.clone();
    let mut reports = Vec::new();
    for b in &analysis.bodies {
        let r = check(&b.facts);
        let mut ds = diagnose_marked(&b.facts, &r);
        for d in &mut ds {
            d.unit = b.unit;
            if let Some(f) = files.get(b.unit) {
                resolve_lines(d, f);
            }
        }
        diags.extend(ds);
        reports.push(r);
    }
    diags.sort_by(|a, b| (a.unit, a.span.lo, &a.code).cmp(&(b.unit, b.span.lo, &b.code)));
    dedup_diags(&mut diags);
    Checked {
        analysis,
        reports,
        diags,
    }
}

/// Removes a diagnostic that is equal to the diagnostic before it.
///
/// Two diagnostics can be equal also when they report other facts of the spec
/// (`Diagnostic::facts`). The one that stays reports the facts of both.
/// `diags` must be sorted.
pub fn dedup_diags(diags: &mut Vec<Diagnostic>) {
    diags.dedup_by(|b, a| {
        let same = (&a.code, a.severity, &a.message, a.span, &a.notes, a.unit)
            == (&b.code, b.severity, &b.message, b.span, &b.notes, b.unit);
        if same {
            a.facts.append(&mut b.facts);
        }
        same
    });
}

/// Parses, analyzes and checks one source text.
pub fn check_source(name: &str, src: &str, opts: Options) -> Checked {
    let files = vec![
        SourceFile::new("prelude.wf", weft_sema::PRELUDE_SRC),
        SourceFile::new(name, src),
    ];
    match weft_sema::analyze_source(src, opts) {
        Ok(a) => check_analysis(a, &files),
        Err(d) => Checked {
            analysis: Analysis {
                program: weft_sema::Program::default(),
                sigs: Vec::new(),
                bodies: Vec::new(),
                diags: Vec::new(),
                lowerings: 0,
                work: weft_sema::Work::default(),
            },
            reports: Vec::new(),
            diags: vec![d],
        },
    }
}

/// A body where the production checker and the spec disagree.
#[derive(Clone, Debug)]
pub struct Disagreement {
    /// The function name.
    pub function: String,
    /// The checker result.
    pub checker: Violations,
    /// The spec result, or the reason that the spec has no result.
    pub spec: Result<Violations, SpecError>,
    /// The differences between the evidence of the checker and the
    /// derivations of the spec ([`evidence::differences`]).
    pub evidence: Vec<String>,
}

/// Runs the Datalog spec on every body and compares it with the checker: the
/// violations, and the evidence of W0301 and W0405 ([`evidence`]).
///
/// Returns the number of bodies that agree, or the disagreements. A body
/// where the spec fails is a disagreement.
pub fn agreement(c: &Checked) -> Result<usize, Vec<Disagreement>> {
    agreement_with(c, |f, r| {
        let out = evidence::evaluate_probes(f)?;
        Ok((bridge::violations(&out)?, evidence::differences(f, r, &out)))
    })
}

/// The violations of the spec for one body, and the differences of the
/// evidence.
type SpecResult = Result<(Violations, Vec<String>), SpecError>;

/// Compares the checker with the violations that `spec` gives for each body,
/// and with the differences of the evidence that it finds.
fn agreement_with(
    c: &Checked,
    spec: impl Fn(&FnFacts, &Report) -> SpecResult,
) -> Result<usize, Vec<Disagreement>> {
    let mut bad = Vec::new();
    for (b, r) in c.analysis.bodies.iter().zip(&c.reports) {
        let (spec, evidence) = match spec(&b.facts, r) {
            Ok((v, e)) => (Ok(v), e),
            Err(e) => (Err(e), Vec::new()),
        };
        if spec.as_ref() != Ok(&r.violations) || !evidence.is_empty() {
            bad.push(Disagreement {
                function: b.facts.name.clone(),
                checker: r.violations.clone(),
                spec,
                evidence,
            });
        }
    }
    if bad.is_empty() {
        Ok(c.analysis.bodies.len())
    } else {
        Err(bad)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_diagnostics_keep_the_facts_of_both() {
        let span = weft_syntax::ast::Span { lo: 1, hi: 2 };
        let a = Diagnostic::error("W0301", "m", span).with_facts(["f: error(v1, n2)".to_string()]);
        let b = Diagnostic::error("W0301", "m", span).with_facts(["g: error(v1, n2)".to_string()]);
        let c = Diagnostic::error("W0301", "other", span);
        let mut diags = vec![a, b, c];
        dedup_diags(&mut diags);
        assert_eq!(diags.len(), 2);
        assert_eq!(diags[0].facts, ["f: error(v1, n2)", "g: error(v1, n2)"]);
        assert!(diags[1].facts.is_empty());
    }

    #[test]
    fn agreement_counts_the_bodies() {
        let c = check_source("a.wf", "fn f() {}\nfn g() {}\n", Options::default());
        assert_eq!(agreement(&c).map_err(|d| d.len()), Ok(2));
    }

    #[test]
    fn a_spec_that_fails_is_a_disagreement() {
        let c = check_source("a.wf", "fn f() {}\n", Options::default());
        let Err(e) = weft_datalog::parse_program_named("bad.dl", "x(") else {
            panic!("`x(` parses");
        };
        let fail = |_: &FnFacts, _: &Report| Err(SpecError::Eval(e.clone()));
        let Err(bad) = agreement_with(&c, fail) else {
            panic!("a failed spec agrees");
        };
        assert_eq!(bad.len(), 1);
        assert_eq!(bad[0].function, "f");
        assert_eq!(bad[0].checker, Violations::default());
        let text = bad[0].spec.as_ref().map_err(ToString::to_string);
        assert_eq!(
            text,
            Err(format!("the spec does not evaluate: {e}")),
            "{:?}",
            bad[0].spec
        );
        // A different result is a disagreement too.
        let mut other = Violations::default();
        other.stealable.insert(weft_facts::TaskId(0));
        let Err(bad) = agreement_with(&c, |_, _| Ok((other.clone(), Vec::new()))) else {
            panic!("different violations agree");
        };
        assert_eq!(bad[0].spec, Ok(other));
        // A difference of the evidence is a disagreement too.
        let same = |_: &FnFacts, r: &Report| Ok((r.violations.clone(), vec!["x".to_string()]));
        let Err(bad) = agreement_with(&c, same) else {
            panic!("a difference of the evidence agrees");
        };
        assert_eq!(bad[0].evidence, ["x"]);
    }
}
