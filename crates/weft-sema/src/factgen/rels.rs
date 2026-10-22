//! The relation table `RELS` (`docs/ir.md` 6.7): one row for each input
//! relation of the spec.
//!
//! The row says where the fact generator emits the relation and how a summary
//! carries it across a body boundary. The summary procedure and the apply
//! procedure read this table, so a new input relation of the spec gets a
//! summary part (or a stated reason why it stays inside its body) before any
//! code can emit it. The tests of `crates/weft-sema/tests/factgen_units.rs`
//! read the input list from the spec ([`spec_inputs`]) and destructure
//! `weft_facts::FnFacts` field by field, so neither a new relation of the spec
//! nor a new field of the facts can miss a row.

use std::collections::BTreeSet;

/// The text of the spec.
pub const SPEC: &str = include_str!("../../../../spec/weft.dl");

/// One input relation of `spec/weft.dl`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[allow(missing_docs)]
pub enum Rel {
    Place,
    Parent,
    Unstable,
    Wildcard,
    OnePlace,
    StepAlias,
    StepWithin,
    ParamRooted,
    CfgEdge,
    PointsInto,
    MutatesAt,
    ReadsAt,
    PerformsAt,
    Footprint,
    ReboundAt,
    Uses,
    MovedAt,
    ScopeEnd,
    Overwrites,
    UnsetAt,
    EmptyAt,
    UnwoundAt,
    Owner,
    MovedPart,
    RestLinear,
    ReleasesAt,
    Linear,
    HasOnAbort,
    OnceVar,
    Immovable,
    MayAbort,
    MultiAt,
    SparedAt,
    ClauseMulti,
    BodyMulti,
    ResumesAt,
    HasSignature,
    DeclaredMut,
    DeclaredEffect,
    EscapesAt,
    SharedRoot,
    Task,
    ForkTask,
    SpawnedAt,
    JoinedAt,
    TaskReads,
    TaskWrites,
    Captures,
    MutThrough,
    Kept,
    SpawnsIn,
    Opaque,
    Nonportable,
    Uniq,
    CallMut,
    CallArg,
    LendsMut,
    WritesVia,
    Library,
    Handler,
    StdEffect,
    ClausePerforms,
    SimRoot,
    SimRunAt,
    Started,
    NoRuntime,
    ArgAt,
    ParamIn,
    UniqParam,
    ArgAliased,
    FnArgEffect,
    ParamEffect,
    RefAt,
    RefIn,
}

impl Rel {
    /// The name of the relation in `spec/weft.dl`: the name of the variant in
    /// snake case.
    pub fn name(self) -> String {
        let s = format!("{self:?}");
        let mut out = String::new();
        for (i, c) in s.chars().enumerate() {
            if c.is_ascii_uppercase() {
                if i > 0 {
                    out.push('_');
                }
                out.push(c.to_ascii_lowercase());
            } else {
                out.push(c);
            }
        }
        out
    }
}

/// Where the fact generator emits a relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Source {
    /// The place interner: one fact for each place or pair of steps.
    Places,
    /// The declarations: locals, signatures, handlers, spawn sites and the driver.
    Decls,
    /// The template of a statement or of a terminator phase.
    Template,
}

/// How a relation acts in the spec, which decides how a summary projects it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    /// It holds for the whole component (no node, or a node with no edges).
    Static,
    /// The control-flow graph.
    Edge,
    /// It only adds to a derived relation. A summary projects it as it is.
    Gen,
    /// It stops a derived relation (`invalid`, `moved`, `live_linear`,
    /// `active`). A summary projects it for an outer variable only if each
    /// path of the body has it (a must part).
    Kill,
    /// Both: `moved_at` adds to `moved` and stops `live_linear`.
    Both,
}

/// The part of a summary (`docs/ir.md` 6.7) that carries a relation to a run
/// node.
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
    /// Tasks that the body starts in a scope that it does not own, and the
    /// task handles of the interface that it joins.
    Tasks,
    /// The abstract value of `_0`.
    Ret,
    /// Values that the body writes behind a reference or into an `rc` object.
    Stores,
    /// The type parameters of the values that the body drops.
    Drops,
    /// The parameters that the body holds across a node that can abort or
    /// resume more than once.
    Holds,
    /// Interface variables that the body uses or moves.
    UsesMoves,
    /// The captures and upvars that the body gives a whole new value on each
    /// path to its `Return` (a must part).
    Rebinds,
    /// Interface places that the body gives to a `@ uniq` parameter.
    UniqNeeds,
    /// Each change of the body is below its receiver (`writes_via` at a
    /// method call).
    OnlySelf,
}

/// One row of the table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Row {
    /// Where the relation comes from.
    pub source: Source,
    /// How it acts.
    pub role: Role,
    /// The summary part that carries it, or the reason why it stays in its
    /// body.
    pub part: Result<Part, &'static str>,
}

const fn row(source: Source, role: Role, part: Result<Part, &'static str>) -> Row {
    Row { source, role, part }
}

/// The reason of a relation with no node.
const STATIC: Result<Part, &str> = Err("static: no node");
/// The reason of a relation about one variable or node of the body.
const LOCAL: Result<Part, &str> = Err("about a variable or a node of this body only");

/// Returns the row of a relation. The match is exhaustive, so a new [`Rel`]
/// needs a row.
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
        Rel::Handler
        | Rel::Footprint
        | Rel::ClauseMulti
        | Rel::BodyMulti
        | Rel::ClausePerforms
        | Rel::SimRoot => row(
            Template,
            Static,
            Err("a fact of a handler of this component"),
        ),
        Rel::CfgEdge => row(
            Template,
            Edge,
            Err("the control-flow graph of this component"),
        ),
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
        Rel::ArgAt | Rel::ParamIn | Rel::FnArgEffect | Rel::ParamEffect => row(
            Template,
            Gen,
            Err("a check of one call node against its callee"),
        ),
        Rel::RefAt | Rel::RefIn => row(Template, Gen, Err("a check of one stated place")),
        Rel::Overwrites | Rel::UnsetAt | Rel::ScopeEnd | Rel::RestLinear => {
            row(Template, Gen, LOCAL)
        }
        Rel::MovedAt => row(Template, Both, Ok(P::UsesMoves)),
        Rel::WritesVia => row(Template, Kill, Ok(P::OnlySelf)),
        // `docs/ir.md` 6.7: the must half of the part `tasks`.
        Rel::JoinedAt => row(Template, Kill, Ok(P::Tasks)),
        // `docs/ir.md` 6.7: a projection only of a capture or an upvar that each
        // path to `Return` gives a whole new value (F3-11).
        Rel::ReboundAt => row(Template, Kill, Ok(P::Rebinds)),
        Rel::EmptyAt | Rel::UnwoundAt => row(Template, Kill, LOCAL),
        Rel::SparedAt => row(
            Template,
            Kill,
            Err("computed at each node from its abort destinations"),
        ),
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

/// Returns the input relations that the header of the spec `text` lists.
///
/// They are the lines `//   name(..)` of the block that starts with
/// `// Input facts`. Three
/// of them (`mutates_at`, `multi_at`, `once_var`) are also heads of rules: the
/// spec extends them, so a test of "body minus heads" alone would miss them.
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

/// Returns the relations that a rule body of `text` names and no rule head
/// defines.
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
        let (head, body) = rule.split_once(":-").unwrap_or((rule, ""));
        if let Some(name) = rel_names(head).into_iter().next() {
            heads.insert(name);
        }
        used.extend(rel_names(body));
    }
    (heads, used)
}

/// Returns the identifiers of `s` that are followed by `(`.
fn rel_names(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b.get(i)
            .is_some_and(|c| c.is_ascii_lowercase() || *c == b'_')
        {
            let start = i;
            while b
                .get(i)
                .is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_')
            {
                i += 1;
            }
            if b.get(i) == Some(&b'(') {
                if let Some(name) = s.get(start..i) {
                    out.push(name.to_string());
                }
            }
        } else {
            i += 1;
        }
    }
    out
}

/// The input relations of `spec/weft.dl`: the relations of its header.
///
/// # Errors
///
/// Returns a message if a rule names an input that the header does not list,
/// or if the header lists a relation that no rule reads.
pub fn spec_inputs() -> Result<BTreeSet<String>, String> {
    let header = header_inputs(SPEC);
    let (_, used) = heads_and_uses(SPEC);
    let pure = inputs_of(SPEC);
    if let Some(r) = pure.difference(&header).next() {
        return Err(format!(
            "a rule names the input `{r}` that the header does not list"
        ));
    }
    if let Some(r) = header.difference(&used).next() {
        return Err(format!("the header lists `{r}`, and no rule reads it"));
    }
    Ok(header)
}
