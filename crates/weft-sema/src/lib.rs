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
#[derive(Clone, Copy, Debug, Default)]
pub struct Options {
    /// The root unit is a library: it may not install root handlers.
    pub library: bool,
    /// The embedded profile: no `std.rt`, so `main` must handle every standard effect.
    pub no_runtime: bool,
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
    /// The effects that the body infers, also for a function that states its
    /// effects. They include the closures that the body makes.
    pub effects: program::EffectSig,
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

/// Analyzes the units. Unit 0 must be the prelude and unit 1 the root.
pub fn analyze(units: &[Unit], opts: Options) -> Analysis {
    let (prog, mut diags) = program::Collector::collect(units);
    let mut sigs: Vec<FnSig> = prog.fns.iter().map(|f| f.sig.clone()).collect();
    let user_fns: Vec<usize> = (0..prog.fns.len())
        .filter(|&i| !prog.fns[i].is_std && prog.fns[i].decl.body.is_some())
        .collect();
    let library_of =
        |prog: &Program, f: usize| opts.library || unit_of(prog, prog.fns[f].module) > 1;
    // Effect inference: iterate to a fixpoint over the call graph. A function that
    // states its effects still infers what it lends to its function parameters, what
    // its returned function value does, which function parameters it stores,
    // whether it can run a stored function value, and whether an unknown function
    // value that it calls can resume more than once.
    let mut rounds = 0;
    loop {
        rounds += 1;
        let mut changed = false;
        for &f in &user_fns {
            let lib = library_of(&prog, f);
            let l = body::Lower::new(&prog, &sigs, prog.fns[f].module, &prog.fns[f].path, lib)
                .lower_fn(f);
            let next = if sigs[f].declared {
                program::EffectSig {
                    lent: l.effects.lent,
                    ret: l.effects.ret,
                    stores: l.effects.stores,
                    reaches: l.effects.reaches,
                    reach_given: l.effects.reach_given,
                    multi: l.effects.multi,
                    ..sigs[f].effects.clone()
                }
            } else {
                l.effects
            };
            if next != sigs[f].effects {
                sigs[f].effects = next;
                changed = true;
            }
        }
        if !changed || rounds >= 32 {
            break;
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
            effects: l.effects,
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
            effects: l.effects,
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
