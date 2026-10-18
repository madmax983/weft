//! Semantic analysis for Weft: names, types, places, modes and effects.
//!
//! [`analyze`] collects items, resolves signatures, infers the effects of
//! functions that do not state them, and lowers every body to [`FnFacts`].
//! The checker in `weft-check` runs the rules on these facts.

pub mod body;
pub mod effects;
pub mod fip;
pub mod program;
pub mod types;

use weft_facts::FnFacts;
use weft_syntax::diag::Diagnostic;
use weft_syntax::parse_file;

pub use program::{FnSig, Program, Unit};

/// The source of the standard prelude.
pub const PRELUDE_SRC: &str = include_str!("../../../std/prelude.wf");

/// Analysis options.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Options {
    /// The root unit is a library: it may not install root handlers.
    pub library: bool,
    /// The embedded profile: no `std.rt`, so `main` must handle every standard effect.
    pub no_runtime: bool,
}

impl Options {
    /// Reads the file markers of a source text. A marker is a line comment
    /// `// weft: WORD ...`. The words are `library` and `no-runtime`.
    pub fn from_markers(src: &str) -> Self {
        let mut o = Self::default();
        for line in src.lines() {
            let Some(words) = line.trim_start().strip_prefix("// weft:") else {
                continue;
            };
            for w in words.split([' ', ',']).filter(|w| !w.is_empty()) {
                match w {
                    "library" => o.library = true,
                    "no-runtime" => o.no_runtime = true,
                    _ => {}
                }
            }
        }
        o
    }

    /// Returns the options that are on in `self` or in `other`.
    #[must_use]
    pub const fn or(self, other: Self) -> Self {
        Self {
            library: self.library || other.library,
            no_runtime: self.no_runtime || other.no_runtime,
        }
    }
}

/// The facts of one body.
#[derive(Clone, Debug)]
pub struct BodyFacts {
    /// The function, or `None` for a test.
    pub func: Option<program::FnId>,
    /// The unit index of the body.
    pub unit: usize,
    /// The facts.
    pub facts: FnFacts,
}

/// The result of analysis.
#[derive(Clone, Debug)]
pub struct Analysis {
    /// The program.
    pub program: Program,
    /// The final signatures, with inferred effects.
    pub sigs: Vec<FnSig>,
    /// The facts of every user body.
    pub bodies: Vec<BodyFacts>,
    /// Diagnostics from analysis (not from the checker).
    pub diags: Vec<Diagnostic>,
    /// The number of effect inference rounds.
    pub rounds: usize,
}

/// Parses the prelude.
pub fn prelude_unit() -> Unit {
    let file = parse_file(PRELUDE_SRC).unwrap_or_default();
    Unit {
        name: "prelude".into(),
        file,
        is_std: true,
    }
}

/// Returns the unit index of a module: 0 for the prelude, 1 for the root, then dependencies.
fn unit_of(prog: &Program, m: program::ModId) -> usize {
    prog.mods[m].unit
}

/// Returns the most rounds of effect inference for `n` functions.
///
/// In a round that changes a signature, a function gets a new effect or a
/// longer `mut` place. One round moves an effect one call back along a call
/// chain, and a place in an inferred signature has at most 8 steps. So 10 rounds
/// for each function are more than a monotone inference needs.
pub const fn round_limit(n: usize) -> usize {
    n.saturating_add(2).saturating_mul(10)
}

/// Analyzes the units. Unit 0 must be the prelude and unit 1 the root.
///
/// Effect inference runs at most [`round_limit`] rounds for the number of user
/// functions. If it does not reach a fixpoint, each function whose effects can
/// still change gets W0706.
pub fn analyze(units: &[Unit], opts: Options) -> Analysis {
    analyze_bounded(units, opts, None)
}

/// Analyzes the units with at most `limit` rounds of effect inference.
pub fn analyze_with_limit(units: &[Unit], opts: Options, limit: usize) -> Analysis {
    analyze_bounded(units, opts, Some(limit))
}

fn analyze_bounded(units: &[Unit], opts: Options, limit: Option<usize>) -> Analysis {
    let (prog, mut diags) = program::Collector::collect(units);
    let mut sigs: Vec<FnSig> = prog.fns.iter().map(|f| f.sig.clone()).collect();
    let user_fns: Vec<usize> = (0..prog.fns.len())
        .filter(|&i| !prog.fns[i].is_std && prog.fns[i].decl.body.is_some())
        .collect();
    let limit = limit.unwrap_or_else(|| round_limit(user_fns.len()));
    let library_of =
        |prog: &Program, f: usize| opts.library || unit_of(prog, prog.fns[f].module) > 1;
    let infer = |sigs: &[FnSig], f: usize| {
        let lib = library_of(&prog, f);
        body::Lower::new(&prog, sigs, prog.fns[f].module, &prog.fns[f].path, lib)
            .lower_fn(f)
            .effects
    };
    // Effect inference: iterate to a fixpoint over the call graph.
    let mut rounds = 0;
    let mut converged = false;
    while rounds < limit {
        rounds += 1;
        let mut changed = false;
        for &f in &user_fns {
            if sigs[f].declared {
                continue;
            }
            let effects = infer(&sigs, f);
            if effects != sigs[f].effects {
                sigs[f].effects = effects;
                changed = true;
            }
        }
        if !changed {
            converged = true;
            break;
        }
    }
    if !converged {
        // The signatures are not a fixpoint. Find the functions that would change.
        for &f in &user_fns {
            if sigs[f].declared || infer(&sigs, f) == sigs[f].effects {
                continue;
            }
            let mut d = Diagnostic::error(
                "W0706",
                format!(
                    "effect inference did not reach a fixpoint in {rounds} rounds; the effects of `{}` can be incomplete",
                    prog.fns[f].path
                ),
                prog.fns[f].decl.name.span,
            )
            .note("state the effects of this function, or report the program as a checker bug");
            d.unit = unit_of(&prog, prog.fns[f].module);
            diags.push(d);
        }
    }
    let mut bodies = Vec::new();
    for &f in &user_fns {
        let lib = library_of(&prog, f);
        let l =
            body::Lower::new(&prog, &sigs, prog.fns[f].module, &prog.fns[f].path, lib).lower_fn(f);
        diags.extend(l.diags);
        bodies.push(BodyFacts {
            func: Some(f),
            unit: unit_of(&prog, prog.fns[f].module),
            facts: l.facts,
        });
    }
    for t in &prog.tests {
        let name = format!("test \"{}\"", t.name);
        let lib = opts.library || unit_of(&prog, t.module) > 1;
        let l = body::Lower::new(&prog, &sigs, t.module, &name, lib).lower_test(&t.body, t.span);
        diags.extend(l.diags);
        bodies.push(BodyFacts {
            func: None,
            unit: unit_of(&prog, t.module),
            facts: l.facts,
        });
    }
    for &f in &user_fns {
        if prog.fns[f].decl.is_fip {
            let unit = unit_of(&prog, prog.fns[f].module);
            diags.extend(fip::check(&prog, &sigs, f).into_iter().map(|mut d| {
                d.unit = unit;
                d
            }));
        }
    }
    Analysis {
        program: prog,
        sigs,
        bodies,
        diags,
        rounds,
    }
}

/// Parses and analyzes one source text as the root unit.
pub fn analyze_source(src: &str, opts: Options) -> Result<Analysis, Diagnostic> {
    let file = parse_file(src).map_err(|e| Diagnostic::error("W0001", e.message, e.span))?;
    let units = vec![
        prelude_unit(),
        Unit {
            name: String::new(),
            file,
            is_std: false,
        },
    ];
    Ok(analyze(&units, opts))
}

#[cfg(test)]
mod tests;
