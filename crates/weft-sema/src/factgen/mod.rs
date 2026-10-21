//! The fact generator of the `ir` pipeline (`docs/ir.md` section 6).
//!
//! The fact generator reads the IR of a program and writes one [`FnFacts`]
//! for each function and each test, with the schema of `weft-facts`. During
//! the migration it runs next to the old lowering (plan §2.6, stage F1):
//!
//! - `run` builds the IR of the analysis, finds the construct groups of each
//!   body (`crate::irbuild::scope`) and decides the scope of the program. A
//!   program is in scope when each group that it uses is on
//!   ([`crate::Options::ir_groups`]) and the fact generator supports each one.
//!   Else the old pipeline checks the whole program, and [`Scope::fallback`]
//!   says why.
//! - For a program in scope, [`emit`] writes the facts. It starts from the
//!   facts of the declarations of each body (the name, the effect names, the
//!   flags of the driver). The `ir` pipeline then fills the exports of the
//!   interpreter from the IR (module `exports`), and keeps the diagnostics of
//!   `typeck` (`docs/ir.md` 2.4) and of the builder.
//!
//! Stage F1 has a stub [`emit`]: it supports no group, so each program is out
//! of scope. A test can give another emit ([`crate::analyze_with_emit`]).

pub mod alpha;
mod exports;
pub mod nodes;
pub mod rels;
pub mod vars;

use std::fmt;

use weft_facts::FnFacts;
use weft_syntax::diag::Diagnostic;

use crate::irbuild::scope::{self, Group, Groups};
use crate::irbuild::{self, Built, Outcome};
use crate::{Analysis, BodyFacts};

/// The fact generator does not support a group that the program uses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unsupported {
    /// The group.
    pub group: Group,
    /// Why, for the note of the fallback.
    pub reason: String,
}

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "the fact generator does not support group {}: {}",
            self.group, self.reason
        )
    }
}

/// What [`emit`] reads.
#[derive(Clone, Copy, Debug)]
pub struct Input<'a> {
    /// The analysis of the old lowering: the program, the signatures and
    /// the THIR tables.
    pub analysis: &'a Analysis,
    /// The IR.
    pub built: &'a Built,
    /// The scope of the program.
    pub scope: &'a Scope,
}

/// A fact generator.
///
/// It writes the facts of each body of the analysis into `facts`, one
/// [`FnFacts`] for each body, in the order of [`Analysis::bodies`]. Each one
/// has the facts of the declarations already.
pub type Emit = fn(&Input<'_>, &mut [FnFacts]) -> Result<(), Unsupported>;

/// The fact generator of the `ir` pipeline.
///
/// # Errors
///
/// Stage F1: it supports no group yet. It returns [`Unsupported`] for the
/// first group that the program uses.
pub fn emit(input: &Input<'_>, _facts: &mut [FnFacts]) -> Result<(), Unsupported> {
    Err(Unsupported {
        group: input.scope.used.first().unwrap_or(Group::A),
        reason: "no group is supported before stage F8".to_string(),
    })
}

/// The scope of a program (plan §2.6).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Scope {
    /// The groups of each body, in the order of [`Analysis::bodies`]. A body
    /// with no IR uses no group.
    pub bodies: Vec<Groups>,
    /// The groups that the program uses: the union of [`Scope::bodies`].
    pub used: Groups,
    /// Why the old pipeline checks the program, or `None` if the program is
    /// in scope.
    pub fallback: Option<String>,
}

impl Scope {
    /// True if the `ir` pipeline checks the program.
    pub const fn in_scope(&self) -> bool {
        self.fallback.is_none()
    }
}

/// The result of the `ir` pipeline for a program in scope.
#[derive(Clone, Debug)]
pub struct IrFacts {
    /// The facts of each body, in the order of [`Analysis::bodies`].
    pub bodies: Vec<BodyFacts>,
    /// The diagnostics: those of `typeck` and of the item checks, and those
    /// of the builder (W0315).
    pub diags: Vec<Diagnostic>,
}

/// The text of a list of groups that are off: `group A`, or
/// `group A, group C and group D`.
fn off_text(off: Groups) -> String {
    let names: Vec<String> = off.iter().map(|g| format!("group {g}")).collect();
    match names.as_slice() {
        [] => String::new(),
        [one] => format!("the program uses {one}, which is off"),
        [rest @ .., last] => format!(
            "the program uses {} and {last}, which are off",
            rest.join(", ")
        ),
    }
}

/// Runs the `ir` pipeline on the analysis `a` of the old lowering, with the
/// groups `on` and the fact generator `emit`. `kept` holds the diagnostics of
/// the analysis that the `ir` pipeline keeps (`docs/ir.md` 2.4).
///
/// Returns the scope of the program and, if it is in scope, its facts and
/// diagnostics.
pub(crate) fn run(
    a: &Analysis,
    on: Groups,
    emit: Emit,
    kept: Vec<Diagnostic>,
) -> (Scope, Option<IrFacts>) {
    let built = irbuild::build(a);
    let bodies = scope::groups(&built);
    let used = bodies.iter().fold(Groups::NONE, |g, b| g.union(*b));
    let mut s = Scope {
        bodies,
        used,
        fallback: None,
    };
    if let Some(e) = built.entries.iter().find_map(|e| match &e.outcome {
        Outcome::Unsupported(u) => Some((e, *u)),
        _ => None,
    }) {
        s.fallback = Some(format!(
            "the builder does not lower `{}`: {}",
            e.0.name,
            e.1.construct.name()
        ));
        return (s, None);
    }
    let off = used.minus(on);
    if !off.is_empty() {
        s.fallback = Some(off_text(off));
        return (s, None);
    }
    let mut facts: Vec<FnFacts> = a.bodies.iter().map(|b| seed(&b.facts)).collect();
    let input = Input {
        analysis: a,
        built: &built,
        scope: &s,
    };
    if let Err(u) = emit(&input, &mut facts) {
        s.fallback = Some(u.to_string());
        return (s, None);
    }
    exports::fill(a, &built, &mut facts);
    let bodies = a
        .bodies
        .iter()
        .zip(facts)
        .map(|(b, facts)| BodyFacts {
            func: b.func,
            unit: b.unit,
            facts,
            effects: b.effects.clone(),
        })
        .collect();
    let mut diags = kept;
    diags.extend(built.diags.iter().cloned());
    (s, Some(IrFacts { bodies, diags }))
}

/// The bodies of the component of the function or test body `entry`.
///
/// They are in the order of their ids (`docs/ir.md` 6.1): the body and each
/// body inside it (closures, clauses, handled bodies, scope bodies). They share
/// the tables of one `FnFacts`.
pub fn component(built: &Built, entry: weft_ir::BodyId) -> Vec<weft_ir::BodyId> {
    let Some(e) = built
        .entries
        .iter()
        .position(|x| x.outcome == Outcome::Built(entry))
    else {
        return Vec::new();
    };
    scope::body_entries(built)
        .into_iter()
        .enumerate()
        .filter(|(_, x)| *x == Some(e))
        .map(|(i, _)| weft_ir::BodyId(u32::try_from(i).unwrap_or(u32::MAX)))
        .collect()
}

/// The facts of the declarations of a body, from the facts of the old
/// lowering: the name, the names of the effects, and the flags of the driver
/// (`library()`, `started()`, `no_runtime()`). They do not depend on the code
/// of the body.
fn seed(old: &FnFacts) -> FnFacts {
    FnFacts {
        name: old.name.clone(),
        effect_names: old.effect_names.clone(),
        hidden_effects: old.hidden_effects.clone(),
        library: old.library,
        started: old.started,
        no_runtime: old.no_runtime,
        ..FnFacts::default()
    }
}
