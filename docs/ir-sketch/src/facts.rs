//! The fact templates of the instructions (design sketch).
//!
//! Each statement is one node. Each terminator is one node, and some terminators have
//! more nodes in a fixed order ([`Phase`]). A template lists the input relations of
//! `spec/weft.dl` that one instruction can emit at its nodes. The fact generator has
//! one function for each template, and no other code emits node facts.
//!
//! The test `each_relation_has_a_source` checks that each input relation of the spec
//! has a source: the place interner, the declarations, or a template.

use crate::{BlockId, BodyId, StmtKind, TermKind};

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
    /// The name of the relation in `spec/weft.dl`.
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

/// The relations that the place interner gives (the bridge derives them).
pub const FROM_PLACES: &[Rel] = &[
    Rel::Place,
    Rel::Parent,
    Rel::Unstable,
    Rel::Wildcard,
    Rel::OnePlace,
    Rel::StepAlias,
    Rel::StepWithin,
    Rel::ParamRooted,
];

/// The relations that the declarations give: locals, signatures, handlers, spawn
/// sites and the driver.
pub const FROM_DECLS: &[Rel] = &[
    Rel::Owner,
    Rel::Linear,
    Rel::HasOnAbort,
    Rel::OnceVar,
    Rel::Immovable,
    Rel::Nonportable,
    Rel::Uniq,
    Rel::HasSignature,
    Rel::DeclaredMut,
    Rel::DeclaredEffect,
    Rel::SharedRoot,
    Rel::Task,
    Rel::ForkTask,
    Rel::Library,
    Rel::StdEffect,
    Rel::Started,
    Rel::NoRuntime,
];

/// The nodes of one instruction, in the order of the CFG edges between them.
///
/// A node never both binds a variable and invalidates it (`no_gen_kill`, B6). A value
/// binds where it exists, before the frees that come after it in the machine: the
/// result of a call binds at `Ret`, and the frame of the callee ends at `FrameEnd`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Phase {
    /// The instruction itself: its operands, its effects, its suspension.
    Main,
    /// A call returns: the result binds, and held arguments move.
    Ret,
    /// The frame that gave the result ends: the callee frame of a call, or the frames of
    /// the continuation for a `resume`.
    FrameEnd,
    /// A clause ended with no `resume` and aborts the frames up to its handler: the
    /// value of the clause binds to the destination of the `handle` before the frames
    /// unwind. One node for each suspending node and each local handler it can abort to.
    AbortValue,
    /// The handled body or the scope body returned: its `_0` is used, and the value binds.
    Exit,
    /// After `Exit` of a `handle`: the code of each clause after its `resume` runs; then
    /// the capability and the frames of the clauses end.
    Post,
    /// The unwinding of a handled body ended at its `handle`: the capability and the
    /// frames of the clauses end.
    Landing,
    /// A `multi` resume runs the code after a suspension point again: the locals of
    /// the copied frames get their copies.
    Copy,
}

/// A node of the facts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeKey {
    /// The body.
    pub body: BodyId,
    /// The block.
    pub block: BlockId,
    /// The statement index, or `u32::MAX` for the terminator.
    pub at: u32,
    /// The phase.
    pub phase: Phase,
    /// For a cleanup block: the abort destination that this copy of the block serves.
    /// The fact generator makes one copy of a cleanup chain for each destination.
    pub dest: u32,
}

/// The relations of the operands of an instruction: each read of a place.
pub const OPERANDS: &[Rel] = &[Rel::Uses, Rel::ReadsAt, Rel::MovedAt, Rel::MovedPart, Rel::RestLinear];

/// The relations that a summary can put at a node that runs another body.
pub const SUMMARY: &[Rel] = &[
    Rel::MutatesAt,
    Rel::ReadsAt,
    Rel::CallMut,
    Rel::CallArg,
    Rel::LendsMut,
    Rel::ReleasesAt,
    Rel::PerformsAt,
    Rel::EscapesAt,
    Rel::MayAbort,
    Rel::MultiAt,
    Rel::SparedAt,
    Rel::ResumesAt,
    Rel::SpawnedAt,
    Rel::TaskReads,
    Rel::TaskWrites,
    Rel::Captures,
    Rel::MutThrough,
    Rel::Kept,
    Rel::SpawnsIn,
    Rel::Opaque,
    Rel::Uses,
    Rel::MovedAt,
    Rel::PointsInto,
];

/// The relations of a task start: the footprint of the task and its captures. A
/// spawn is a change at the spawn node (ADR 0006), and it does not suspend.
pub const TASK_START: &[Rel] = &[
    Rel::MutatesAt,
    Rel::CallMut,
    Rel::CallArg,
    Rel::SpawnedAt,
    Rel::TaskReads,
    Rel::TaskWrites,
    Rel::Captures,
    Rel::MutThrough,
    Rel::Kept,
    Rel::SpawnsIn,
    Rel::Opaque,
    Rel::EscapesAt,
    Rel::PerformsAt,
];

/// The template of a statement. `cleanup` is true on a cleanup path.
pub fn stmt_template(k: &StmtKind, cleanup: bool) -> Vec<Rel> {
    let mut v = vec![Rel::CfgEdge];
    match k {
        StmtKind::Live(_) => {}
        // `Dead` always ends the value: `scope_end` on a normal path (the free and the
        // W0601 point), `unwound_at` on a cleanup path (soundness judge, H9).
        StmtKind::Dead(_) => v.push(if cleanup { Rel::UnwoundAt } else { Rel::ScopeEnd }),
        StmtKind::Assign(..) => {
            v.extend(OPERANDS);
            v.extend([
                Rel::ReboundAt,
                Rel::PointsInto,
                Rel::EmptyAt,
                Rel::MutatesAt,
                Rel::Overwrites,
                Rel::WritesVia,
                Rel::RefAt,
                Rel::RefIn,
                Rel::SimRunAt,
                // the end of the drop pair of a `Drop` right before it
                Rel::ScopeEnd,
                Rel::Uses,
            ]);
        }
        // A place behind a pointer: the old value goes away. A drop pair variable binds
        // here and ends at the `Assign` after it (W0601 for a linear old value).
        StmtKind::Drop(_) => v.extend([Rel::ReboundAt, Rel::Uses, Rel::ReadsAt]),
        StmtKind::Consume(_) => v.extend([Rel::Uses, Rel::MovedAt]),
        StmtKind::Uninit(_) => v.push(Rel::UnsetAt),
        StmtKind::Bounds(..) => v.extend([Rel::Uses, Rel::ReadsAt]),
        StmtKind::Mention(_) => v.push(Rel::Uses),
        StmtKind::Print(_) => v.extend([Rel::Uses, Rel::ReadsAt]),
        StmtKind::UnwindValue(..) => {
            v.push(Rel::UnwoundAt);
            v.extend([Rel::MutatesAt, Rel::ReadsAt, Rel::LendsMut]);
        }
        StmtKind::UnwindKont(_) => {}
    }
    v.sort();
    v.dedup();
    v
}

/// The template of a terminator: the relations of each of its nodes.
pub fn term_template(k: &TermKind) -> Vec<(Phase, Vec<Rel>)> {
    let edge = || vec![Rel::CfgEdge];
    let with = |mut base: Vec<Rel>, more: &[Rel]| {
        base.extend(more);
        base.sort();
        base.dedup();
        base
    };
    let summary = with(edge(), SUMMARY);
    let ret = with(edge(), &[Rel::ReboundAt, Rel::PointsInto, Rel::EmptyAt]);
    match k {
        TermKind::Goto(_) | TermKind::Unreachable | TermKind::UnwindExit => vec![(Phase::Main, edge())],
        TermKind::Switch { .. } => vec![(Phase::Main, with(edge(), &[Rel::Uses, Rel::ReadsAt]))],
        TermKind::Return => vec![(Phase::Main, with(edge(), &[Rel::Uses, Rel::RefAt, Rel::RefIn]))],
        TermKind::Call { .. } => vec![
            (
                Phase::Main,
                with(
                    with(summary, OPERANDS),
                    &[
                        Rel::ArgAt,
                        Rel::ParamIn,
                        Rel::UniqParam,
                        Rel::ArgAliased,
                        Rel::FnArgEffect,
                        Rel::ParamEffect,
                        Rel::SimRunAt,
                        Rel::Handler,
                        Rel::SimRoot,
                    ],
                ),
            ),
            (Phase::Ret, with(ret.clone(), &[Rel::MovedAt])),
            (Phase::FrameEnd, with(edge(), &[Rel::ScopeEnd])),
            (Phase::AbortValue, ret),
            (Phase::Copy, with(edge(), &[Rel::ReboundAt, Rel::EmptyAt])),
        ],
        TermKind::Perform { .. } => vec![
            (
                Phase::Main,
                with(
                    with(summary, OPERANDS),
                    &[Rel::ArgAt, Rel::ParamIn, Rel::UniqParam, Rel::ArgAliased, Rel::FnArgEffect, Rel::ParamEffect],
                ),
            ),
            (Phase::Ret, ret.clone()),
            (Phase::AbortValue, ret),
            (Phase::Copy, with(edge(), &[Rel::ReboundAt, Rel::EmptyAt])),
        ],
        TermKind::Resume { .. } => vec![
            (Phase::Main, with(summary, OPERANDS)),
            (Phase::Ret, ret.clone()),
            (Phase::FrameEnd, with(edge(), &[Rel::ScopeEnd])),
            (Phase::AbortValue, ret),
        ],
        TermKind::Handle { .. } => vec![
            (
                Phase::Main,
                with(
                    edge(),
                    &[
                        Rel::Handler,
                        Rel::Footprint,
                        Rel::ClauseMulti,
                        Rel::BodyMulti,
                        Rel::ClausePerforms,
                        Rel::ReboundAt,
                        Rel::PointsInto,
                    ],
                ),
            ),
            (Phase::Exit, with(ret, &[Rel::Uses])),
            (Phase::Post, with(with(edge(), SUMMARY), &[Rel::ScopeEnd])),
            (Phase::Landing, with(edge(), &[Rel::ScopeEnd])),
            (Phase::Copy, with(edge(), &[Rel::ReboundAt, Rel::EmptyAt])),
        ],
        TermKind::Scope { .. } => vec![
            (
                Phase::Main,
                with(edge(), &[Rel::ReboundAt, Rel::PointsInto, Rel::EscapesAt, Rel::PerformsAt, Rel::MayAbort]),
            ),
            (Phase::Exit, with(ret, &[Rel::Uses])),
            (Phase::FrameEnd, with(edge(), &[Rel::ScopeEnd])),
        ],
        TermKind::ScopeWait { .. } => vec![(
            Phase::Main,
            with(
                edge(),
                &[Rel::Uses, Rel::JoinedAt, Rel::LendsMut, Rel::MayAbort, Rel::EscapesAt, Rel::PerformsAt, Rel::SparedAt, Rel::ReboundAt, Rel::ScopeEnd],
            ),
        )],
        TermKind::Spawn { .. } => vec![(
            Phase::Main,
            with(with(with(edge(), OPERANDS), TASK_START), &[Rel::ReboundAt, Rel::PointsInto]),
        )],
        TermKind::Join { .. } => vec![
            (
                Phase::Main,
                with(edge(), &[Rel::Uses, Rel::MovedAt, Rel::JoinedAt, Rel::MayAbort, Rel::EscapesAt, Rel::PerformsAt, Rel::SparedAt]),
            ),
            (Phase::Ret, with(ret, &[Rel::LendsMut])),
        ],
        TermKind::Detach { .. } => vec![(Phase::Main, with(edge(), &[Rel::Uses, Rel::MovedAt, Rel::ReboundAt, Rel::ScopeEnd]))],
        TermKind::Fork { .. } => vec![
            (Phase::Main, with(with(with(edge(), OPERANDS), TASK_START), &[Rel::MayAbort, Rel::SparedAt])),
            (Phase::Ret, with(ret, &[Rel::JoinedAt, Rel::LendsMut])),
        ],
        TermKind::Assert { .. } => vec![(Phase::Main, with(edge(), &[Rel::Uses, Rel::ReadsAt, Rel::MayAbort, Rel::SparedAt]))],
        TermKind::IterNext { .. } => vec![(Phase::Main, with(ret, &[Rel::Uses, Rel::ReadsAt]))],
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::*;
    use std::collections::BTreeSet;

    fn place() -> Place {
        Place { local: LocalId(0), proj: vec![] }
    }

    pub(crate) fn all_stmts() -> Vec<StmtKind> {
        vec![
            StmtKind::Live(LocalId(0)),
            StmtKind::Dead(LocalId(0)),
            StmtKind::Assign(place(), Rvalue::Use(Operand::Const(Const::Unit))),
            StmtKind::Drop(place()),
            StmtKind::Consume(place()),
            StmtKind::Uninit(place()),
            StmtKind::Bounds(place(), Operand::Const(Const::Unit)),
            StmtKind::Mention(place()),
            StmtKind::Print(vec![]),
            StmtKind::UnwindValue(place(), UnwindAction::Drop),
            StmtKind::UnwindKont(LocalId(0)),
        ]
    }

    pub(crate) fn all_terms() -> Vec<TermKind> {
        let b = BlockId(0);
        let o = || Operand::Const(Const::Unit);
        vec![
            TermKind::Goto(b),
            TermKind::Switch { on: o(), arms: vec![], otherwise: b },
            TermKind::Return,
            TermKind::UnwindExit,
            TermKind::Unreachable,
            TermKind::Call { callee: Callee::Value(o()), args: vec![], dest: place(), caps: CapArgs::Root, next: Some(b), unwind: None },
            TermKind::Perform { cap: CapOperand::Row(EffectId(0)), op: OpIdx(0), args: vec![], dest: place(), next: b, unwind: None },
            TermKind::Resume { kont: place(), arg: o(), dest: place(), next: b, unwind: None },
            TermKind::Handle { handler: HandlerId(0), dest: place(), next: b, unwind: None },
            TermKind::Scope { scope: ScopeId(0), dest: place(), next: b, unwind: None },
            TermKind::ScopeWait { scope: place(), orphans: vec![], next: b, unwind: None },
            TermKind::Spawn { site: SpawnId(0), scope: o(), task: o(), dest: None, next: b },
            TermKind::Join { task: o(), dest: place(), next: b, unwind: None },
            TermKind::Detach { task: o(), next: b },
            TermKind::Fork { sites: vec![], branches: vec![], dest: place(), next: b, unwind: None },
            TermKind::Assert { cond: o(), next: b, unwind: None },
            TermKind::IterNext { iter: place(), dest: place(), next: b, done: b },
        ]
    }

    /// The relations that some template, the place interner or the declarations emit.
    pub(crate) fn sources() -> BTreeSet<String> {
        let mut have = BTreeSet::new();
        for r in FROM_PLACES.iter().chain(FROM_DECLS) {
            have.insert(r.name());
        }
        for s in all_stmts() {
            for c in [false, true] {
                for r in stmt_template(&s, c) {
                    have.insert(r.name());
                }
            }
        }
        for t in all_terms() {
            for (_, rs) in term_template(&t) {
                for r in rs {
                    have.insert(r.name());
                }
            }
        }
        have
    }

    /// Each input relation of the spec has a source. The list of input relations comes
    /// from `spec/weft.dl` itself (`crate::rels::spec_inputs`), not from a string, so a
    /// new input relation of the spec fails this test until it has a source. The list
    /// of the machine sketch was a string and missed `rest_linear` (proofs judge).
    #[test]
    fn each_relation_has_a_source() {
        let spec = crate::rels::spec_inputs();
        let have = sources();
        let missing: Vec<&String> = spec.iter().filter(|n| !have.contains(*n)).collect();
        assert!(missing.is_empty(), "no source for {missing:?}");
        assert!(spec.contains("rest_linear"));
        assert_eq!(spec.len(), 74, "the spec at b25faf0 has 74 input relations");
    }

    /// Prints the templates as a Markdown table (`cargo test -- --nocapture print_table`).
    #[test]
    fn print_table() {
        for s in all_stmts() {
            let name = format!("{s:?}");
            let name = name.split('(').next().unwrap_or_default().to_string();
            let n: Vec<String> = stmt_template(&s, false).iter().map(|r| r.name()).collect();
            let c: Vec<String> = stmt_template(&s, true).iter().map(|r| r.name()).collect();
            let extra: Vec<&String> = c.iter().filter(|x| !n.contains(x)).collect();
            println!("| `{name}` | {} | {:?} |", n.join(", "), extra);
        }
        for t in all_terms() {
            let name = format!("{t:?}");
            let name = name.split([' ', '(', '{']).next().unwrap_or_default().to_string();
            for (p, rs) in term_template(&t) {
                let n: Vec<String> = rs.iter().map(|r| r.name()).collect();
                println!("| `{name}` | {p:?} | {} |", n.join(", "));
            }
        }
    }
}
