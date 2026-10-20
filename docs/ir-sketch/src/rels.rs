//! The relation table (`RELS`): one row for each input relation of the spec.
//!
//! The row says where the fact generator emits the relation and how a summary carries
//! it across a body boundary. The summary procedure and the apply procedure read this
//! table, so a new input relation of the spec gets a summary part (or a stated reason
//! why it stays inside its body) before any code can emit it. In the real crate a test
//! also destructures `weft_facts::FnFacts` field by field, as `FnFacts::mark` does,
//! so a new field of `FnFacts` cannot miss a row either.

use crate::facts::Rel;
use std::collections::BTreeSet;

/// Where the fact generator emits a relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Source {
    /// The place interner: one fact for each place or pair of steps.
    Places,
    /// The declarations: locals, signatures, handlers, spawn sites and the driver.
    Decls,
    /// The template of a statement or of a terminator phase (`facts.rs`).
    Template,
}

/// How a relation acts in the spec, which decides how a summary projects it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    /// It holds for the whole component (no node, or a node with no edges).
    Static,
    /// The CFG.
    Edge,
    /// It only adds to a derived relation. A summary projects it as it is.
    Gen,
    /// It stops a derived relation (`invalid`, `moved`, `live_linear`, `active`). A
    /// summary projects it for an outer variable only if each path of the body has it.
    Kill,
    /// Both: `moved_at` adds to `moved` and stops `live_linear`.
    Both,
}

/// The part of a summary that carries a relation to a run node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Part {
    /// Places that the body changes.
    Muts,
    /// Places that the body reads.
    Reads,
    /// Places that the body frees.
    Frees,
    /// Places that the body gives to code that it does not know.
    Lends,
    /// Operations and their capability interface.
    Performs,
    /// Abort destinations.
    Aborts,
    /// Capability interfaces through which the body can resume more than once.
    Multi,
    /// Function values of the interface that the body runs.
    Runs,
    /// Tasks that the body starts in a scope that it does not own.
    Tasks,
    /// The abstract value of `_0`.
    Ret,
    /// Values that the body writes behind a reference or into an `rc` object.
    Stores,
    /// Interface variables that the body uses or moves.
    UsesMoves,
    /// Interface places that the body gives to a `@ uniq` parameter.
    UniqNeeds,
    /// Each change of the body is below its receiver (`writes_via` at a method call).
    OnlySelf,
}

/// One row of the table.
#[derive(Clone, Copy, Debug)]
pub struct Row {
    /// Where the relation comes from.
    pub source: Source,
    /// How it acts.
    pub role: Role,
    /// The summary part that carries it, or `None` with the reason why it stays in its
    /// body.
    pub part: Result<Part, &'static str>,
}

const fn row(source: Source, role: Role, part: Result<Part, &'static str>) -> Row {
    Row { source, role, part }
}

const STATIC: Result<Part, &str> = Err("static: no node");
const LOCAL: Result<Part, &str> = Err("about a variable or a node of this body only");

/// Returns the row of a relation. The match is exhaustive, so a new [`Rel`] needs a
/// row.
pub const fn row_of(r: Rel) -> Row {
    use Part as P;
    use Role::{Both, Edge, Gen, Kill, Static};
    use Source::{Decls, Places, Template};
    match r {
        Rel::Place
        | Rel::Parent
        | Rel::Unstable
        | Rel::Wildcard
        | Rel::OnePlace
        | Rel::StepAlias
        | Rel::StepWithin
        | Rel::ParamRooted => row(Places, Static, STATIC),
        Rel::Owner
        | Rel::Linear
        | Rel::HasOnAbort
        | Rel::OnceVar
        | Rel::Immovable
        | Rel::Nonportable
        | Rel::Uniq
        | Rel::HasSignature
        | Rel::DeclaredMut
        | Rel::DeclaredEffect
        | Rel::SharedRoot
        | Rel::Task
        | Rel::ForkTask
        | Rel::Library
        | Rel::StdEffect
        | Rel::Started
        | Rel::NoRuntime => row(Decls, Static, STATIC),
        Rel::Handler | Rel::Footprint | Rel::ClauseMulti | Rel::BodyMulti | Rel::ClausePerforms | Rel::SimRoot => {
            row(Template, Static, Err("a fact of a handler of this component"))
        }
        Rel::CfgEdge => row(Template, Edge, Err("the CFG of this component")),
        Rel::PointsInto => row(Template, Gen, Ok(P::Ret)),
        Rel::MutatesAt | Rel::CallMut => row(Template, Gen, Ok(P::Muts)),
        Rel::ReadsAt | Rel::CallArg => row(Template, Gen, Ok(P::Reads)),
        Rel::PerformsAt | Rel::EscapesAt | Rel::ResumesAt => row(Template, Gen, Ok(P::Performs)),
        Rel::Uses => row(Template, Gen, Ok(P::UsesMoves)),
        Rel::MovedPart | Rel::ReleasesAt => row(Template, Gen, Ok(P::Frees)),
        Rel::MayAbort => row(Template, Gen, Ok(P::Aborts)),
        Rel::MultiAt => row(Template, Gen, Ok(P::Multi)),
        Rel::SpawnedAt
        | Rel::TaskReads
        | Rel::TaskWrites
        | Rel::Captures
        | Rel::MutThrough
        | Rel::Kept
        | Rel::SpawnsIn
        | Rel::Opaque => row(Template, Gen, Ok(P::Tasks)),
        Rel::LendsMut => row(Template, Gen, Ok(P::Lends)),
        Rel::SimRunAt => row(Template, Gen, Ok(P::Runs)),
        Rel::UniqParam | Rel::ArgAliased => row(Template, Gen, Ok(P::UniqNeeds)),
        Rel::ArgAt | Rel::ParamIn | Rel::FnArgEffect | Rel::ParamEffect => {
            row(Template, Gen, Err("a check of one call node against its callee"))
        }
        Rel::RefAt | Rel::RefIn => row(Template, Gen, Err("a check of one stated place")),
        Rel::Overwrites | Rel::UnsetAt | Rel::ScopeEnd | Rel::RestLinear => row(Template, Gen, LOCAL),
        Rel::MovedAt => row(Template, Both, Ok(P::UsesMoves)),
        Rel::WritesVia => row(Template, Kill, Ok(P::OnlySelf)),
        Rel::JoinedAt => row(Template, Kill, Ok(P::Tasks)),
        Rel::ReboundAt | Rel::EmptyAt | Rel::UnwoundAt => row(Template, Kill, LOCAL),
        Rel::SparedAt => row(Template, Kill, Err("computed at each node from its abort destinations")),
    }
}

/// All relations, in the order of the enum.
pub const ALL: &[Rel] = &[
    Rel::Place,
    Rel::Parent,
    Rel::Unstable,
    Rel::Wildcard,
    Rel::OnePlace,
    Rel::StepAlias,
    Rel::StepWithin,
    Rel::ParamRooted,
    Rel::CfgEdge,
    Rel::PointsInto,
    Rel::MutatesAt,
    Rel::ReadsAt,
    Rel::PerformsAt,
    Rel::Footprint,
    Rel::ReboundAt,
    Rel::Uses,
    Rel::MovedAt,
    Rel::ScopeEnd,
    Rel::Overwrites,
    Rel::UnsetAt,
    Rel::EmptyAt,
    Rel::UnwoundAt,
    Rel::Owner,
    Rel::MovedPart,
    Rel::RestLinear,
    Rel::ReleasesAt,
    Rel::Linear,
    Rel::HasOnAbort,
    Rel::OnceVar,
    Rel::Immovable,
    Rel::MayAbort,
    Rel::MultiAt,
    Rel::SparedAt,
    Rel::ClauseMulti,
    Rel::BodyMulti,
    Rel::ResumesAt,
    Rel::HasSignature,
    Rel::DeclaredMut,
    Rel::DeclaredEffect,
    Rel::EscapesAt,
    Rel::SharedRoot,
    Rel::Task,
    Rel::ForkTask,
    Rel::SpawnedAt,
    Rel::JoinedAt,
    Rel::TaskReads,
    Rel::TaskWrites,
    Rel::Captures,
    Rel::MutThrough,
    Rel::Kept,
    Rel::SpawnsIn,
    Rel::Opaque,
    Rel::Nonportable,
    Rel::Uniq,
    Rel::CallMut,
    Rel::CallArg,
    Rel::LendsMut,
    Rel::WritesVia,
    Rel::Library,
    Rel::Handler,
    Rel::StdEffect,
    Rel::ClausePerforms,
    Rel::SimRoot,
    Rel::SimRunAt,
    Rel::Started,
    Rel::NoRuntime,
    Rel::ArgAt,
    Rel::ParamIn,
    Rel::UniqParam,
    Rel::ArgAliased,
    Rel::FnArgEffect,
    Rel::ParamEffect,
    Rel::RefAt,
    Rel::RefIn,
];

/// The path of the spec. The real crate uses `include_str!("../../../spec/weft.dl")`.
pub const SPEC_PATH: &str = "/home/user/weft/spec/weft.dl";

/// Returns the input relations that the header of the spec lists: each line
/// `//   name(..)` of the block that starts with `// Input facts`. Three of them
/// (`mutates_at`, `multi_at`, `once_var`) are also heads of rules: the spec extends
/// them, so a test of "body minus heads" alone would miss them.
pub fn header_inputs(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut inside = false;
    for line in text.lines() {
        if line.starts_with("// Input facts") {
            inside = true;
            continue;
        }
        if !inside {
            continue;
        }
        let Some(rest) = line.strip_prefix("//   ") else {
            if line.starts_with("//") {
                continue;
            }
            break;
        };
        if let Some(name) = rel_names(rest).into_iter().next() {
            if rest.starts_with(&name) {
                out.insert(name);
            }
        }
    }
    out
}

/// Returns the relations that a rule body names and no rule head defines.
pub fn inputs_of(text: &str) -> BTreeSet<String> {
    let (heads, used) = heads_and_uses(text);
    used.difference(&heads).cloned().collect()
}

/// Returns the relations of the rule heads and of the rule bodies.
fn heads_and_uses(text: &str) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut code = String::new();
    for line in text.lines() {
        let l = line.split("//").next().unwrap_or_default();
        code.push_str(l);
        code.push('\n');
    }
    let mut heads = BTreeSet::new();
    let mut used = BTreeSet::new();
    for rule in code.split('.').map(str::trim).filter(|r| !r.is_empty()) {
        let (head, body) = match rule.split_once(":-") {
            Some((h, b)) => (h, b),
            None => (rule, ""),
        };
        if let Some(name) = rel_names(head).into_iter().next() {
            heads.insert(name);
        }
        for name in rel_names(body) {
            used.insert(name);
        }
    }
    (heads, used)
}

/// Returns the identifiers that are followed by `(`.
fn rel_names(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i].is_ascii_lowercase() || b[i] == b'_' {
            let start = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            if b.get(i) == Some(&b'(') {
                out.push(s[start..i].to_string());
            }
        } else {
            i += 1;
        }
    }
    out
}

/// The input relations of `spec/weft.dl`.
///
/// # Panics
///
/// If the spec file cannot be read (a test helper).
pub fn spec_inputs() -> BTreeSet<String> {
    let text = std::fs::read_to_string(SPEC_PATH).unwrap_or_default();
    assert!(!text.is_empty(), "cannot read {SPEC_PATH}");
    let header = header_inputs(&text);
    let (_, used) = heads_and_uses(&text);
    let pure = inputs_of(&text);
    assert!(pure.is_subset(&header), "a rule names an input that the header does not list");
    assert!(header.is_subset(&used), "the header lists a relation that no rule reads");
    header
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each input relation of the spec has a row, and each row names an input
    /// relation of the spec.
    #[test]
    fn rows_match_the_spec() {
        let spec = spec_inputs();
        let rows: BTreeSet<String> = ALL.iter().map(|r| r.name()).collect();
        let no_row: Vec<&String> = spec.difference(&rows).collect();
        let no_rel: Vec<&String> = rows.difference(&spec).collect();
        assert!(no_row.is_empty(), "spec relations with no row: {no_row:?}");
        assert!(no_rel.is_empty(), "rows that the spec does not have: {no_rel:?}");
    }

    /// Each node relation that can name an interface place or variable has a summary
    /// part, or a stated reason. A relation from a template always has a reason.
    #[test]
    fn each_node_relation_has_a_part_or_a_reason() {
        for r in ALL {
            let row = row_of(*r);
            if let Err(why) = row.part {
                assert!(!why.is_empty(), "{} has no part and no reason", r.name());
            }
            if row.source == Source::Template && matches!(row.role, Role::Gen | Role::Both) {
                // a Gen relation that names a place of the caller must reach the caller
                let names_places = matches!(
                    r,
                    Rel::MutatesAt | Rel::ReadsAt | Rel::LendsMut | Rel::ReleasesAt | Rel::MovedPart | Rel::CallMut | Rel::CallArg
                );
                if names_places {
                    assert!(row.part.is_ok(), "{} names caller places and needs a part", r.name());
                }
            }
        }
    }

    /// The parser finds the input relations of a small program.
    #[test]
    fn inputs_of_a_small_program() {
        let p = "a(X) :- b(X), !c(X).\nd(X) :- a(X), e(X). // f(X)\n";
        let got: Vec<String> = inputs_of(p).into_iter().collect();
        assert_eq!(got, vec!["b", "c", "e"]);
    }
}
