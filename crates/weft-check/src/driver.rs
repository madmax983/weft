//! The check pipeline: parse, analyze, check, diagnose.

use weft_sema::{Analysis, Options};
use weft_syntax::diag::{Code, Diagnostic, Severity};
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
    /// With `--facts=both` and a program in scope (plan §2.6): the check of
    /// the facts of the `ir` pipeline ([`Analysis::ir_facts`]). `None` when
    /// the `ir` pipeline gives the facts of the old lowering.
    pub ir: Option<Box<Self>>,
}

impl Checked {
    /// Returns true if no error was found.
    pub fn ok(&self) -> bool {
        !self.diags.iter().any(|d| d.severity == Severity::Error)
    }

    /// Returns the codes of all diagnostics, in order.
    pub fn codes(&self) -> Vec<Code> {
        self.diags.iter().map(|d| d.code).collect()
    }
}

/// Runs the production checker on every body of an analysis.
///
/// `files[u]` is the source of unit `u`; it resolves line numbers in notes.
/// Each fact that a diagnostic reports gets the index of its body
/// ([`bridge::body_key`]), so two bodies with one name keep apart.
pub fn check_analysis(mut analysis: Analysis, files: &[SourceFile]) -> Checked {
    if let Some(p) = analysis.ir_scope.as_mut().and_then(|s| s.pending.take()) {
        return check_pending(analysis, files, p);
    }
    let ir = analysis.ir_facts.take().map(|facts| {
        let mut view = analysis.clone();
        view.bodies = facts.bodies;
        view.diags = facts.diags;
        Box::new(check_bodies(view, files))
    });
    let mut c = check_bodies(analysis, files);
    c.ir = ir;
    c
}

/// Checks a program with a construct that the facts of the `ir` pipeline
/// do not model (stage R0g, `weft_sema::factgen::Scope::pending`).
///
/// `analysis` has the facts of the old lowering and, in
/// [`Analysis::ir_facts`], those of the `ir` pipeline. If the check of the
/// `ir` facts finds an error, the `ir` pipeline rejects the program and
/// gives the result (alone, or as [`Checked::ir`] next to the check of the
/// old facts). Else the facts can miss an error, so the old pipeline checks
/// the program: the scope gets the reason of the fallback.
fn check_pending(
    mut analysis: Analysis,
    files: &[SourceFile],
    p: weft_sema::factgen::Pending,
) -> Checked {
    if let Some(facts) = analysis.ir_facts.take() {
        let mut view = analysis.clone();
        view.bodies = facts.bodies;
        view.diags = facts.diags;
        view.sigs = facts.sigs;
        let ir = check_bodies(view, files);
        if !ir.ok() {
            if p.ir_view {
                return ir;
            }
            let mut c = check_bodies(analysis, files);
            c.ir = Some(Box::new(ir));
            return c;
        }
    }
    if let Some(s) = analysis.ir_scope.as_mut() {
        s.fallback = Some(p.reason);
    }
    check_bodies(analysis, files)
}

/// Runs the production checker on every body of `analysis`, with no `ir`
/// side.
fn check_bodies(analysis: Analysis, files: &[SourceFile]) -> Checked {
    let mut diags = analysis.diags.clone();
    let mut reports = Vec::new();
    for (i, b) in analysis.bodies.iter().enumerate() {
        let r = check(&b.facts);
        let mut ds = diagnose_marked(&b.facts, &r);
        for d in &mut ds {
            d.unit = b.unit;
            for key in &mut d.facts {
                *key = bridge::body_key(i, key);
            }
            if let Some(f) = files.get(b.unit) {
                resolve_lines(d, f);
            }
        }
        diags.extend(ds);
        reports.push(r);
    }
    diags.sort_by(|a, b| (a.unit, a.span.lo, &a.code).cmp(&(b.unit, b.span.lo, &b.code)));
    fold(&mut diags);
    dedup_diags(&mut diags);
    Checked {
        analysis,
        reports,
        diags,
        ir: None,
    }
}

/// Folds the facts of each diagnostic with a [`crate::diagnose::FOLD`]
/// message into the W0204 of the signature check of the same parameter
/// before it (the nearest one in the same unit), and removes it. With no
/// such diagnostic, it stays as a W0204 at its own span. `diags` must be
/// sorted.
fn fold(diags: &mut Vec<Diagnostic>) {
    use crate::diagnose::FOLD;
    let mut i = 0;
    while i < diags.len() {
        let Some(name) = diags
            .get(i)
            .and_then(|d| d.message.strip_prefix(FOLD))
            .map(str::to_string)
        else {
            i += 1;
            continue;
        };
        let unit = diags.get(i).map_or(0, |d| d.unit);
        let text = format!("by-value parameter `{name}`");
        let host = (0..i).rev().find(|&j| {
            diags.get(j).is_some_and(|d| {
                d.unit == unit
                    && d.code == weft_syntax::diag::Code::W0204
                    && d.message.contains(&text)
                    && d.facts.is_empty()
            })
        });
        if let Some(j) = host {
            let facts = diags
                .get_mut(i)
                .map(|d| std::mem::take(&mut d.facts))
                .unwrap_or_default();
            if let Some(h) = diags.get_mut(j) {
                h.facts.extend(facts);
            }
            diags.remove(i);
        } else {
            if let Some(d) = diags.get_mut(i) {
                d.message = format!(
                    "a returned reference cannot point into the by-value parameter `{name}`: it goes out of scope at the return"
                );
            }
            i += 1;
        }
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

/// Parses, analyzes and checks one source text, on a large stack
/// ([`weft_sema::on_large_stack`]).
pub fn check_source(name: &str, src: &str, opts: Options) -> Checked {
    weft_sema::on_large_stack(|| check_source_here(name, src, opts))
}

/// Parses, analyzes and checks one source text on the current stack.
fn check_source_here(name: &str, src: &str, opts: Options) -> Checked {
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
                decls: Vec::new(),
                diags: Vec::new(),
                lowerings: 0,
                work: weft_sema::Work::default(),
                thir: Vec::new(),
                thir_tys: weft_sema::thir::TyTable::new(),
                thir_decl_error: None,
                ir_scope: None,
                ir_facts: None,
            },
            reports: Vec::new(),
            diags: vec![d],
            ir: None,
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
        let a = Diagnostic::error(Code::W0301, "m", span)
            .with_facts(["body 0: error(v1, n2)".to_string()]);
        let b = Diagnostic::error(Code::W0301, "m", span)
            .with_facts(["body 1: error(v1, n2)".to_string()]);
        let c = Diagnostic::error(Code::W0301, "other", span);
        let mut diags = vec![a, b, c];
        dedup_diags(&mut diags);
        assert_eq!(diags.len(), 2);
        assert_eq!(
            diags[0].facts,
            ["body 0: error(v1, n2)", "body 1: error(v1, n2)"]
        );
        assert!(diags[1].facts.is_empty());
    }

    /// A checked program can come back from the thread of
    /// [`weft_sema::on_large_stack`].
    #[test]
    fn a_checked_program_is_send_and_sync() {
        fn send_sync<T: Send + Sync>() {}
        send_sync::<Checked>();
    }

    /// An `emit` that writes no fact (the test hook of plan stage F1). Its
    /// type is `weft_sema::factgen::Emit`, so it returns a `Result`.
    #[allow(clippy::unnecessary_wraps)]
    const fn empty(
        _: &weft_sema::factgen::Input<'_>,
        _: &mut [FnFacts],
    ) -> Result<(), weft_sema::factgen::Unsupported> {
        Ok(())
    }

    /// The analysis of `src` with the hook [`empty`], every group on, and the
    /// pipeline `facts`.
    fn hooked(src: &str, facts: weft_sema::FactGen) -> Analysis {
        let units = vec![
            weft_sema::prelude_unit().expect("the prelude"),
            weft_sema::Unit {
                name: String::new(),
                file: weft_syntax::parse_file(src).expect("the source"),
                is_std: false,
            },
        ];
        let opts = Options {
            facts,
            ir_groups: weft_sema::Groups::ALL,
            ..Options::default()
        };
        weft_sema::analyze_with_emit(&units, opts, empty)
    }

    const ESCAPE: &str = "effect Log { fn log(msg: String) }
fn as_result() {
    let f = handle Log { fn log(m) { resume(()) } } in || log(\"late\")
}
";

    #[test]
    fn the_both_mode_checks_both_fact_sets() {
        let files = [
            SourceFile::new("prelude.wf", weft_sema::PRELUDE_SRC),
            SourceFile::new("a.wf", ESCAPE),
        ];
        let c = check_analysis(hooked(ESCAPE, weft_sema::FactGen::Both), &files);
        assert!(c.codes().contains(&Code::W0313), "{:?}", c.codes());
        let ir = c.ir.as_ref().expect("the ir side");
        assert!(ir.diags.is_empty(), "{:?}", ir.codes());
        assert!(ir.ir.is_none());
        assert_eq!(ir.reports.len(), 1);
        // The ir side is the result of the ir mode.
        let alone = check_analysis(hooked(ESCAPE, weft_sema::FactGen::Ir), &files);
        assert_eq!(alone.codes(), ir.codes());
        assert!(alone.ir.is_none());
        // Out of scope, the both mode has no ir side.
        let old = check_source(
            "a.wf",
            ESCAPE,
            Options {
                facts: weft_sema::FactGen::Old,
                ..Options::default()
            },
        );
        assert!(old.ir.is_none());
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
