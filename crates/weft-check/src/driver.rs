//! The check pipeline: parse, analyze, check, diagnose.

use weft_sema::program::ItemRef;
use weft_sema::{effects, Analysis, BodyFacts, Options, ROOT_UNIT};
use weft_syntax::diag::{Diagnostic, Severity};
use weft_syntax::SourceFile;

use weft_facts::{FnFacts, Violations};

use crate::bridge::{self, SpecError};
use crate::diagnose::{diagnose, resolve_lines, root_effects};
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
pub fn check_analysis(analysis: Analysis, files: &[SourceFile], opts: Options) -> Checked {
    let mut diags = analysis.diags.clone();
    let mut reports = Vec::new();
    for b in &analysis.bodies {
        let r = check(&b.facts);
        let mut ds = diagnose(&b.facts, &r);
        if let Some(who) = started_body(&analysis, b) {
            let no_runtime = opts.no_runtime && b.func.is_some();
            // The facts name each effect by its identity. A user effect has a
            // module path (`main.Log`), so it never passes `is_std`, also when
            // it has the name of a standard effect.
            ds.extend(root_effects(&b.facts, &who, no_runtime, &effects::is_std));
        }
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
    diags.dedup();
    Checked {
        analysis,
        reports,
        diags,
    }
}

/// Names a body of the root that the runtime starts: `main` or a test.
/// Returns `None` for another body.
fn started_body(a: &Analysis, b: &BodyFacts) -> Option<String> {
    if b.unit != ROOT_UNIT {
        return None;
    }
    match (b.func, a.program.lookup(a.program.root, "main")) {
        (None, _) => Some(b.facts.name.clone()),
        (Some(f), Some(ItemRef::Fn(main))) if f == main => Some("`main`".to_string()),
        _ => None,
    }
}

/// Parses, analyzes and checks one source text.
pub fn check_source(name: &str, src: &str, opts: Options) -> Checked {
    let files = vec![
        SourceFile::new("prelude.wf", weft_sema::PRELUDE_SRC),
        SourceFile::new(name, src),
    ];
    match weft_sema::analyze_source(src, opts) {
        Ok(a) => check_analysis(a, &files, opts),
        Err(d) => Checked {
            analysis: Analysis {
                program: weft_sema::Program::default(),
                sigs: Vec::new(),
                bodies: Vec::new(),
                diags: Vec::new(),
                lowerings: 0,
                loop_passes: 0,
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
}

/// Runs the Datalog spec on every body and compares it with the checker.
///
/// Returns the number of bodies that agree, or the disagreements. A body
/// where the spec fails is a disagreement.
pub fn agreement(c: &Checked) -> Result<usize, Vec<Disagreement>> {
    agreement_with(c, bridge::check_spec)
}

/// Compares the checker with the violations that `spec` gives for each body.
fn agreement_with(
    c: &Checked,
    spec: impl Fn(&FnFacts) -> Result<Violations, SpecError>,
) -> Result<usize, Vec<Disagreement>> {
    let mut bad = Vec::new();
    for (b, r) in c.analysis.bodies.iter().zip(&c.reports) {
        let spec = spec(&b.facts);
        if spec.as_ref() != Ok(&r.violations) {
            bad.push(Disagreement {
                function: b.facts.name.clone(),
                checker: r.violations.clone(),
                spec,
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
        let fail = |_: &FnFacts| Err(SpecError::Eval(e.clone()));
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
        let Err(bad) = agreement_with(&c, |_| Ok(other.clone())) else {
            panic!("different violations agree");
        };
        assert_eq!(bad[0].spec, Ok(other));
    }
}
