//! The check pipeline: parse, analyze, check, diagnose.

use weft_sema::{Analysis, Options};
use weft_syntax::diag::{Diagnostic, Severity};
use weft_syntax::SourceFile;

use crate::bridge;
use crate::diagnose::{diagnose, resolve_lines};
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
        for d in &mut ds {
            d.unit = b.unit;
            if let Some(f) = files.get(b.unit) {
                resolve_lines(d, f);
            }
        }
        diags.extend(ds);
        reports.push(r);
    }
    if opts.no_runtime {
        diags.extend(no_runtime_diags(&analysis));
    }
    diags.sort_by_key(|d| (d.unit, d.span.lo, d.code.clone()));
    diags.dedup();
    Checked {
        analysis,
        reports,
        diags,
    }
}

/// W0803: in the embedded profile, `main` must handle every standard effect.
fn no_runtime_diags(a: &Analysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for b in &a.bodies {
        let Some(f) = b.func else { continue };
        if a.program.fns[f].name != "main" || b.unit != 1 {
            continue;
        }
        for (n, e) in &b.facts.escapes_at {
            if weft_sema::effects::is_std(e) {
                out.push(Diagnostic::error(
                    "W0803",
                    format!("with no runtime, `main` must handle `{e}` itself"),
                    b.facts.node(*n).span,
                ));
            }
        }
    }
    out
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
    pub checker: weft_facts::Violations,
    /// The spec result.
    pub spec: weft_facts::Violations,
}

/// Runs the Datalog spec on every body and compares it with the checker.
///
/// Returns the number of bodies that agree, or the disagreements.
pub fn agreement(c: &Checked) -> Result<usize, Vec<Disagreement>> {
    let mut bad = Vec::new();
    for (b, r) in c.analysis.bodies.iter().zip(&c.reports) {
        let spec = match bridge::check_spec(&b.facts) {
            Ok(v) => v,
            Err(e) => panic!("spec evaluation failed for {}: {e}", b.facts.name),
        };
        if spec != r.violations {
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
