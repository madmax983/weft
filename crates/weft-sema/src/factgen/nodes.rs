//! Nodes and phases (`docs/ir.md` 6.2).
//!
//! Each statement is one node. Each terminator is one node (phase
//! [`Phase::Main`]), and some terminators have more nodes in a fixed order:
//! the order of the machine. A value binds where it exists (`Ret`, `Exit`,
//! `AbortValue`), before each free that comes after it (`FrameEnd`, `Post`,
//! `Landing`, the cleanup chain). So no node both binds and invalidates one
//! variable.
//!
//! A cleanup block has one copy of each node for each abort destination
//! that reaches it ([`NodeKey::dest`]). Destination [`NORMAL`] is the normal
//! path, [`PAST`] an abort past the function, and the destinations of local
//! handlers come after it (`super::frames`, stage F7). A terminator with no
//! destination has no abort edge. A handled body splices into its site
//! ([`NodeTable::splice`], plan stage F14), with the `Landing` of an abort to
//! its handler, and the `Copy` nodes of the re-entry edges of a clause that
//! runs more than once (plan stage F16). A scope body splices into its
//! site in the same way, with no `Landing` (plan stage F18).

use std::collections::{BTreeMap, BTreeSet};

use weft_facts::{FnFacts, NodeId, Span};
use weft_ir::{
    BlockId, Body, BodyId, Callee, CapOperand, LocalId, LocalKind, Operand, Program, Rvalue,
    StmtKind, TempKind, TermKind, TyTable,
};

use super::frames::{Dest, Frames};

/// The phase of a node (`docs/ir.md` 6.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Phase {
    /// The instruction itself: its operands, its effects, its suspension.
    Main,
    /// A call returns: the result binds, and held arguments move.
    Ret,
    /// The frame that gave the result ends: the callee frame of a call, the
    /// frames of the continuation of a `resume`, or the frame of a scope body.
    FrameEnd,
    /// A clause ended with no `resume` and aborts to its handler: the value of
    /// the clause binds to the destination of the `handle` before the frames
    /// unwind.
    AbortValue,
    /// The handled body or the scope body returned: its `_0` is used, and the
    /// value binds.
    Exit,
    /// After `Exit` of a `handle`: the code of each clause after its `resume`
    /// runs; then the capability and the frames of the clauses end.
    Post,
    /// The unwinding of a handled body ended at its `handle`: the capability
    /// and the frames of the clauses end.
    Landing,
    /// A `multi` resume runs the code after a suspension point again: the
    /// locals of the copied frames get their copies.
    Copy,
    /// A node of the tasks of a terminator, between `Main` and `Ret` (plan
    /// stage F19): a branch of a `fork` after the first one, the join of
    /// the branches, or a node of a function value that a callee runs as a
    /// task (`docs/ir.md` 6.7, OR7).
    Task(u32),
    /// Before `Main` of an assignment that moves a `Box` with a place field
    /// (follow-up F8.1): the old value of the destination goes away here, so
    /// the references of the new value, which point into the target of the
    /// `Box` below the destination now (`transfer::relocate_moved`), stay
    /// valid at `Main`.
    Overwrite,
}

impl Phase {
    /// The name of the phase in a node label.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Main => "main",
            Self::Ret => "ret",
            Self::FrameEnd => "frame end",
            Self::AbortValue => "abort value",
            Self::Exit => "exit",
            Self::Post => "post",
            Self::Landing => "landing",
            Self::Copy => "copy",
            Self::Task(_) => "task",
            Self::Overwrite => "overwrite",
        }
    }
}

/// The statements of body `b` that move a whole local whose type can hold
/// a place field behind a `Box` (`place = move t`): they get a node of
/// [`Phase::Overwrite`] (follow-up F8.1). The test is coarse: a program with
/// a place field, and a type with a `Box` part.
fn moves_boxed_place_field(tys: &TyTable, b: &Body) -> std::collections::BTreeSet<(BlockId, u32)> {
    use weft_ir::ty::AdtKind;
    let mut out = std::collections::BTreeSet::new();
    let place_fields = tys.adts().iter().any(|d| match &d.kind {
        AdtKind::Struct(fs) => fs.iter().any(|f| f.place),
        _ => false,
    });
    if !place_fields {
        return out;
    }
    let mut memo: BTreeMap<weft_ir::TyId, bool> = BTreeMap::new();
    for (bi, blk) in b.blocks.iter().enumerate() {
        for (si, s) in blk.stmts.iter().enumerate() {
            let StmtKind::Assign(_, weft_ir::Rvalue::Use(weft_ir::Operand::Move(t))) = &s.kind
            else {
                continue;
            };
            let Some(ty) = b.local(t.local).map(|d| d.ty).filter(|_| t.proj.is_empty()) else {
                continue;
            };
            if *memo.entry(ty).or_insert_with(|| has_box(tys, ty, 0)) {
                out.insert((
                    BlockId(u32::try_from(bi).unwrap_or(u32::MAX)),
                    u32::try_from(si).unwrap_or(u32::MAX - 1),
                ));
            }
        }
    }
    out
}

/// True if type `t` has a `Box` part: the type, a field of a struct, a
/// payload of an enum, a type argument, a part of a tuple or an element of
/// an array (not behind a reference). `depth` stops a type that grows.
fn has_box(tys: &TyTable, t: weft_ir::TyId, depth: u32) -> bool {
    use weft_ir::ty::{AdtKind, Lang};
    if depth > 8 {
        return false;
    }
    let go = |x: &weft_ir::TyId| has_box(tys, *x, depth + 1);
    match tys.try_get(t) {
        Some(weft_ir::Ty::Adt(a, args)) => {
            let Some(d) = tys.adts().get(a.index()) else {
                return false;
            };
            d.lang == Some(Lang::Box)
                || args.iter().any(go)
                || match &d.kind {
                    AdtKind::Struct(fs) => fs.iter().any(|f| go(&f.ty)),
                    AdtKind::Enum(vs) => vs.iter().flat_map(|v| v.fields.iter()).any(go),
                    AdtKind::Extern { .. } => false,
                }
        }
        Some(weft_ir::Ty::Tuple(ts)) => ts.iter().any(go),
        Some(weft_ir::Ty::Array(x, _)) => go(x),
        _ => false,
    }
}

/// The destination of the nodes of the normal path.
pub const NORMAL: u32 = 0;

/// The abort destination past the function: an abort that no local handler
/// stops.
pub const PAST: u32 = 1;

/// A node of the facts (`docs/ir.md` 6.2).
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
    /// The abort destination that this node serves ([`NORMAL`]: the normal
    /// path).
    pub dest: u32,
}

/// The index of the terminator in [`NodeKey::at`].
pub const TERM: u32 = u32::MAX;

/// The name of a terminator, for node labels.
pub const fn term_name(t: &TermKind) -> &'static str {
    match t {
        TermKind::Goto(_) => "goto",
        TermKind::Switch { .. } => "switch",
        TermKind::Return => "return",
        TermKind::UnwindExit => "unwind exit",
        TermKind::Unreachable => "unreachable",
        TermKind::Call { .. } => "call",
        TermKind::Perform { .. } => "perform",
        TermKind::Resume { .. } => "resume",
        TermKind::Handle { .. } => "handle",
        TermKind::Scope { .. } => "scope",
        TermKind::ScopeWait { .. } => "scope wait",
        TermKind::Spawn { .. } => "spawn",
        TermKind::Join { .. } => "join",
        TermKind::Detach { .. } => "detach",
        TermKind::Fork { .. } => "fork",
        TermKind::Assert { .. } => "assert",
        TermKind::IterNext { .. } => "iter next",
    }
}

/// The labels of the call and perform nodes of body `b`: the name of the
/// callee of each block whose terminator is a call or a perform, as the old
/// lowering: the name of a function item (`push`), of the local of a
/// function value (`f`), or of an operation (`note`). A block with no name
/// in the IR keeps the kind of its terminator.
fn callee_names(p: &Program, tys: &TyTable, id: BodyId, b: &Body) -> BTreeMap<BlockId, String> {
    // The local that each callee temporary copies.
    let mut copies: BTreeMap<LocalId, LocalId> = BTreeMap::new();
    for s in b.blocks.iter().flat_map(|blk| &blk.stmts) {
        if let StmtKind::Assign(dest, Rvalue::Use(Operand::Copy(x) | Operand::Move(x))) = &s.kind {
            let callee = b
                .local(dest.local)
                .is_some_and(|d| d.kind == LocalKind::Temp(TempKind::Callee));
            if callee && dest.proj.is_empty() {
                copies.insert(dest.local, x.local);
            }
        }
    }
    // The function item of each local whose each value is that one item
    // (`let g = grow`): a call of the local names the item, as the old
    // lowering does (stage F13).
    let mut items: BTreeMap<LocalId, Option<weft_ir::FnId>> = BTreeMap::new();
    for s in b.blocks.iter().flat_map(|blk| &blk.stmts) {
        if let StmtKind::Assign(dest, rv) = &s.kind {
            if !dest.proj.is_empty() {
                continue;
            }
            let item = match rv {
                Rvalue::Use(Operand::Const(weft_ir::Const::Fn(f, _))) => Some(*f),
                _ => None,
            };
            let e = items.entry(dest.local).or_insert(item);
            if *e != item {
                *e = None;
            }
        }
    }
    let value_name = |v: &Operand| -> Option<String> {
        let (Operand::Copy(q) | Operand::Move(q)) = v else {
            return None;
        };
        let l = copies.get(&q.local).copied().unwrap_or(q.local);
        // A capture of a closure: the name of its variable.
        if let Some((c, k, _)) = super::alpha::env_capture(p, id, q) {
            return Some(super::alpha::capture_name(p, c, k));
        }
        if let Some(Some(f)) = items.get(&l).filter(|_| q.proj.is_empty()) {
            if let Some(d) = p.fns.get(f.index()) {
                let name = d.name.rsplit('.').next().unwrap_or(&d.name);
                if !name.is_empty() {
                    return Some(name.to_string());
                }
            }
        }
        b.local(l).and_then(|d| d.name.clone())
    };
    let mut out = BTreeMap::new();
    for (bi, blk) in b.blocks.iter().enumerate() {
        let name = match &blk.term.kind {
            TermKind::Call {
                callee: Callee::Fn(f, _),
                ..
            } => p.fns.get(f.index()).and_then(|d| {
                let name = d.name.rsplit('.').next().unwrap_or(&d.name);
                (!name.is_empty()).then(|| name.to_string())
            }),
            TermKind::Call {
                callee: Callee::Value(v),
                ..
            } => value_name(v),
            TermKind::Perform { cap, op, .. } => match cap {
                CapOperand::Row(e) => Some(*e),
                CapOperand::Local(q) => weft_ir::print::cap_effect(p, tys, b, q),
            }
            .and_then(|e| tys.effects().get(e.index()))
            .and_then(|d| d.ops.get(op.index()))
            .map(|d| d.name.clone()),
            _ => None,
        };
        if let Some(n) = name {
            out.insert(BlockId(u32::try_from(bi).unwrap_or(u32::MAX)), n);
        }
    }
    out
}

/// The span of the node of statement `s` of body `b`: the span of its
/// origin. The end of a parameter of a function or a test has the span of
/// the function, as the old lowering: a diagnostic of the parameter at its
/// end (W0601) is at the declaration. The end of a discarded temporary has
/// the span of the temporary: the value that the statement discards (the
/// tail of a block statement, as the old lowering).
fn stmt_span(b: &Body, s: &weft_ir::Stmt) -> Span {
    if let StmtKind::Dead(l) = s.kind {
        let d = b.locals.get(l.index());
        let param = d.is_some_and(|d| matches!(d.kind, weft_ir::LocalKind::Param(_)));
        if param
            && matches!(
                b.kind,
                weft_ir::BodyKind::Fn(_) | weft_ir::BodyKind::Test(_)
            )
        {
            return span(b.origin.span);
        }
        // The end of the `TaskResult` local of a spawn statement has the
        // span of the spawn (plan stage F18): W0601 of a linear result is
        // there.
        if let Some(d) = d.filter(|d| {
            matches!(
                d.kind,
                weft_ir::LocalKind::Temp(weft_ir::TempKind::Discarded)
                    | weft_ir::LocalKind::TaskResult(_)
            )
        }) {
            return span(d.origin.span);
        }
    }
    span(s.origin.span)
}

/// The name of a statement, for node labels.
const fn stmt_name(s: &StmtKind) -> &'static str {
    match s {
        StmtKind::Live(_) => "live",
        StmtKind::Dead(_) => "dead",
        StmtKind::Assign(..) => "assign",
        StmtKind::Drop(_) => "drop",
        StmtKind::Consume(_) => "consume",
        StmtKind::Uninit(_) => "uninit",
        StmtKind::Bounds(..) => "bounds",
        StmtKind::Mention(_) => "mention",
        StmtKind::Print(_) => "print",
        StmtKind::UnwindValue(..) => "unwind value",
        StmtKind::UnwindKont(_) => "unwind continuation",
    }
}

/// The nodes of terminator `t` on the normal path, in order. The handled body
/// (`handle`) and the scope body (`scope`) run between `Main` and `Exit`.
pub fn normal_phases(t: &TermKind) -> Vec<Phase> {
    phases_with(t, 0)
}

/// The nodes of terminator `t` on the normal path, with `tasks` task nodes.
///
/// The [`Phase::Task`] nodes of a call come after `Main`. A `fork` has a node
/// for each branch and a node where the branches end, between `Main` and
/// `Ret` (plan stage F19): the abort edge of `Main` has no task that runs.
pub fn phases_with(t: &TermKind, tasks: u32) -> Vec<Phase> {
    use Phase::{Exit, FrameEnd, Main, Post, Ret, Task};
    match t {
        TermKind::Call { .. } => {
            let mut v = vec![Main];
            v.extend((1..=tasks).map(Task));
            v.extend([Ret, FrameEnd]);
            v
        }
        TermKind::Resume { .. } => vec![Main, Ret, FrameEnd],
        TermKind::Fork { branches, .. } => {
            let k = u32::try_from(branches.len()).unwrap_or(u32::MAX);
            let mut v = vec![Main];
            v.extend((1..=k.saturating_add(1)).map(Task));
            v.push(Ret);
            v
        }
        TermKind::Perform { .. } | TermKind::Join { .. } => vec![Main, Ret],
        TermKind::Handle { .. } => vec![Main, Exit, Post],
        TermKind::Scope { .. } => vec![Main, Exit, FrameEnd],
        _ => vec![Main],
    }
}

/// The nodes of terminator `t` on the path of an abort to one destination.
///
/// The nodes are in order, from `Main` to the node before the cleanup copy of
/// the destination. `value`: the destination is a local handler whose clause gives a value
/// (a `Fail` handler for `join`, `fork` and `scope wait`). A terminator that
/// cannot abort has no nodes.
///
/// The abort of a `handle` or a `scope` comes from the body that they run: it
/// goes through the cleanup chain of that body to the cleanup copy of the
/// terminator.
pub fn abort_phases(t: &TermKind, value: bool) -> Vec<Phase> {
    use Phase::{AbortValue, FrameEnd, Main};
    let mut v = vec![Main];
    match t {
        TermKind::Call { .. } | TermKind::Resume { .. } => {
            if value {
                v.push(AbortValue);
            }
            v.push(FrameEnd);
        }
        TermKind::Perform { .. }
        | TermKind::Join { .. }
        | TermKind::Fork { .. }
        | TermKind::ScopeWait { .. } => {
            if value {
                v.push(AbortValue);
            }
        }
        TermKind::Handle { .. } | TermKind::Scope { .. } | TermKind::Assert { .. } => {}
        _ => v.clear(),
    }
    v
}

/// The nodes at the end of an abort to the handler of terminator `t`: the
/// `Landing` of a `handle`, then its next block.
pub fn landing_phases(t: &TermKind) -> Vec<Phase> {
    match t {
        TermKind::Handle { .. } => vec![Phase::Landing],
        _ => Vec::new(),
    }
}

/// The destination ids of the copies of each cleanup block of body `b`
/// (body `body`): each destination of a terminator copies the cleanup
/// blocks that its abort reaches.
fn cleanup_copies(b: &Body, body: BodyId, frames: &Frames) -> BTreeMap<BlockId, BTreeSet<u32>> {
    let mut out: BTreeMap<BlockId, BTreeSet<u32>> = BTreeMap::new();
    for (bi, blk) in b.blocks.iter().enumerate() {
        if blk.cleanup {
            continue;
        }
        let Some(u) = blk.term.kind.unwind() else {
            continue;
        };
        let block = BlockId(u32::try_from(bi).unwrap_or(u32::MAX));
        for dst in frames.dests(body, block) {
            let d = dst.id();
            let mut work = vec![u];
            while let Some(c) = work.pop() {
                let Some(cb) = b.blocks.get(c.index()) else {
                    continue;
                };
                if !cb.cleanup || !out.entry(c).or_default().insert(d) {
                    continue;
                }
                work.extend(cb.term.kind.successors());
            }
        }
    }
    out
}

/// The span of the facts for an origin of the IR.
const fn span(s: weft_ir::Span) -> Span {
    Span { lo: s.lo, hi: s.hi }
}

/// The nodes of a component and their keys.
#[derive(Clone, Debug, Default)]
pub struct NodeTable {
    /// The node of each key.
    ids: BTreeMap<NodeKey, NodeId>,
    /// The first node of each copy of a block: the body, the block and the
    /// destination.
    firsts: BTreeMap<(BodyId, BlockId, u32), NodeId>,
    /// The statements of the body of now that get a node of
    /// [`Phase::Overwrite`] ([`moves_boxed_place_field`]).
    overwrites: std::collections::BTreeSet<(BlockId, u32)>,
}

impl NodeTable {
    /// Makes the nodes of body `body` of `p` in `facts`, with their edges
    /// (`cfg_edge`): the nodes of each block in order, the phases of each
    /// terminator in the order of [`normal_phases`], each normal successor,
    /// and for each abort destination of a terminator (`frames`) the path of
    /// the abort to the copy of its cleanup block for that destination
    /// ([`abort_phases`]). A cleanup block gets one copy for each destination
    /// whose abort reaches it.
    pub fn build(
        p: &Program,
        tys: &TyTable,
        body: BodyId,
        facts: &mut FnFacts,
        frames: &Frames,
    ) -> Self {
        let mut t = Self::default();
        t.add_body(p, tys, body, facts, frames);
        t
    }

    /// Adds the nodes and the edges of body `body` (see [`NodeTable::build`]).
    pub fn add_body(
        &mut self,
        p: &Program,
        tys: &TyTable,
        body: BodyId,
        facts: &mut FnFacts,
        frames: &Frames,
    ) {
        let Some(b) = p.bodies.get(body.index()) else {
            return;
        };
        let names = callee_names(p, tys, body, b);
        self.overwrites = moves_boxed_place_field(tys, b);
        let copies = cleanup_copies(b, body, frames);
        let copies_of = |block: BlockId, cleanup: bool| -> Vec<u32> {
            if cleanup {
                copies
                    .get(&block)
                    .map(|ds| ds.iter().copied().collect())
                    .unwrap_or_default()
            } else {
                vec![NORMAL]
            }
        };
        // The nodes of each copy of each block, and the edges inside it.
        for (bi, blk) in b.blocks.iter().enumerate() {
            let block = BlockId(u32::try_from(bi).unwrap_or(u32::MAX));
            for dest in copies_of(block, blk.cleanup) {
                let tasks = if dest == NORMAL {
                    frames.task_nodes(body, block)
                } else {
                    0
                };
                self.block_nodes(body, b, block, dest, names.get(&block), tasks, facts);
            }
        }
        // The edges between blocks.
        for (bi, blk) in b.blocks.iter().enumerate() {
            let block = BlockId(u32::try_from(bi).unwrap_or(u32::MAX));
            for dest in copies_of(block, blk.cleanup) {
                let dests = frames.dests(body, block);
                let open = !frames.no_return(body, block);
                self.block_edges(
                    body,
                    b,
                    block,
                    (dest, open),
                    dests,
                    names.get(&block),
                    facts,
                );
            }
        }
    }

    /// Adds the nodes of copy `dest` of block `block` and the edges between them.
    /// `callee` is the name of the callee of the terminator: the label of
    /// each of its nodes. A call has `tasks` nodes of [`Phase::Task`].
    #[allow(clippy::too_many_arguments)]
    fn block_nodes(
        &mut self,
        body: BodyId,
        b: &Body,
        block: BlockId,
        dest: u32,
        callee: Option<&String>,
        tasks: u32,
        facts: &mut FnFacts,
    ) {
        let Some(blk) = b.blocks.get(block.index()) else {
            return;
        };
        let detail = format!("b{} bb{}", body.0, block.0);
        let mut last: Option<NodeId> = None;
        for (i, s) in blk.stmts.iter().enumerate() {
            let key = NodeKey {
                body,
                block,
                at: u32::try_from(i).unwrap_or(u32::MAX - 1),
                phase: Phase::Main,
                dest,
            };
            let name = stmt_name(&s.kind);
            // A new value of a whole variable is `x =`, as the old lowering:
            // a W0301 note says `x : new value`.
            let label = match &s.kind {
                StmtKind::Assign(q, _) if q.proj.is_empty() => b
                    .local(q.local)
                    .filter(|d| d.kind == LocalKind::User)
                    .and_then(|d| d.name.as_ref())
                    .map(|x| format!("{x} =")),
                _ => None,
            };
            let label = label.as_deref().unwrap_or(name);
            let at = u32::try_from(i).unwrap_or(u32::MAX - 1);
            if self.overwrites.contains(&(block, at)) {
                let pre = NodeKey {
                    phase: Phase::Overwrite,
                    ..key
                };
                let o = self.node(facts, pre, stmt_span(b, s), [label, "overwrite", &detail]);
                self.chain(facts, &mut last, o, body, block, dest);
            }
            let n = self.node(facts, key, stmt_span(b, s), [label, name, &detail]);
            self.chain(facts, &mut last, n, body, block, dest);
        }
        let name = term_name(&blk.term.kind);
        // The handled body runs between `Main` and `Exit` of a `handle`,
        // and the scope body between `Main` and `Exit` of a `scope` (the
        // splice, [`NodeTable::splice`]): no edge from `Main` to `Exit`.
        let handle = matches!(
            blk.term.kind,
            TermKind::Handle { .. } | TermKind::Scope { .. }
        );
        for phase in phases_with(&blk.term.kind, tasks) {
            if handle && phase == Phase::Exit {
                last = None;
            }
            let key = NodeKey {
                body,
                block,
                at: TERM,
                phase,
                dest,
            };
            let kind = if phase == Phase::Main {
                name.to_string()
            } else {
                format!("{name} {}", phase.name())
            };
            let label = callee.map_or(kind.as_str(), String::as_str);
            // `ScopeWait` has the span of the `scope` (its body), as the
            // scope end of the old lowering (plan stage F18).
            let at = match blk.term.kind {
                TermKind::ScopeWait { .. } => span(b.origin.span),
                _ => span(blk.term.origin.span),
            };
            let n = self.node(facts, key, at, [label, &kind, &detail]);
            if handle && phase == Phase::Exit {
                last = Some(n);
                continue;
            }
            self.chain(facts, &mut last, n, body, block, dest);
        }
        // The end of an abort to the handler of a `handle`: no edge from the
        // nodes before it ([`NodeTable::splice`]).
        if handle && dest == NORMAL {
            for phase in landing_phases(&blk.term.kind) {
                let key = NodeKey {
                    body,
                    block,
                    at: TERM,
                    phase,
                    dest,
                };
                let kind = format!("{name} {}", phase.name());
                self.node(
                    facts,
                    key,
                    span(blk.term.origin.span),
                    [&kind, &kind, &detail],
                );
            }
        }
    }

    /// Links node `n` after node `last`, or makes it the first node of its
    /// block copy.
    fn chain(
        &mut self,
        facts: &mut FnFacts,
        last: &mut Option<NodeId>,
        n: NodeId,
        body: BodyId,
        block: BlockId,
        dest: u32,
    ) {
        match *last {
            Some(prev) => facts.cfg_edge.push((prev, n)),
            None => {
                self.firsts.insert((body, block, dest), n);
            }
        }
        *last = Some(n);
    }

    /// Adds the edges from copy `dest` of block `block` to its successors, and
    /// the paths of its aborts. `callee` is the name of the callee of the
    /// terminator (see [`Self::block_nodes`]). With `open` false the
    /// terminator has no normal successor.
    #[allow(clippy::too_many_arguments)]
    fn block_edges(
        &mut self,
        body: BodyId,
        b: &Body,
        block: BlockId,
        (dest, open): (u32, bool),
        dests: &[Dest],
        callee: Option<&String>,
        facts: &mut FnFacts,
    ) {
        let Some(blk) = b.blocks.get(block.index()) else {
            return;
        };
        let kind = &blk.term.kind;
        let at = |phase: Phase, dest: u32| NodeKey {
            body,
            block,
            at: TERM,
            phase,
            dest,
        };
        // A perform whose clause has no `resume` does not go on (plan stage
        // F19).
        let last = normal_phases(kind)
            .last()
            .and_then(|ph| self.get(at(*ph, dest)))
            .filter(|_| open);
        // The `Landing` of a `handle` goes on with the next block too.
        let landing = self.get(at(Phase::Landing, dest));
        for from in last.into_iter().chain(landing) {
            for s in kind.normal_successors() {
                let to_dest = match b.blocks.get(s.index()) {
                    Some(sb) if sb.cleanup => dest,
                    _ => NORMAL,
                };
                if let Some(first) = self.first(body, s, to_dest) {
                    facts.cfg_edge.push((from, first));
                }
            }
        }
        // An abort: from `Main` through the abort phases to the cleanup copy
        // of each destination. A terminator with no destination cannot abort
        // (`docs/ir.md` 6.5): it has no abort edge.
        let (Some(u), false) = (kind.unwind(), blk.cleanup) else {
            return;
        };
        // An abort of a handled body goes through its cleanup chain to the
        // cleanup chain of the site ([`NodeTable::splice`]).
        if matches!(kind, TermKind::Handle { .. }) {
            return;
        }
        let Some(main) = self.get(at(Phase::Main, NORMAL)) else {
            return;
        };
        let detail = format!("b{} bb{}", body.0, block.0);
        let name = term_name(kind);
        // The `Main` node of a `scope` aborts past the function only (a
        // cancel): an abort of the scope body goes through its cleanup
        // chain to the cleanup chain of the site (plan stage F18).
        let scope = matches!(kind, TermKind::Scope { .. });
        for dst in dests.iter().filter(|d| !scope || matches!(d, Dest::Past)) {
            let d = dst.id();
            let mut prev = main;
            for phase in abort_phases(kind, dst.value()).into_iter().skip(1) {
                let kind = format!("{name} {} (abort)", phase.name());
                let label = callee.map_or(kind.as_str(), String::as_str);
                let n = self.node(
                    facts,
                    at(phase, d),
                    span(blk.term.origin.span),
                    [label, &kind, &detail],
                );
                facts.cfg_edge.push((prev, n));
                prev = n;
            }
            if let Some(first) = self.first(body, u, d) {
                facts.cfg_edge.push((prev, first));
            }
        }
    }

    /// The splice of each handled body of the `handle` terminators of body
    /// `site` (`docs/ir.md` 6.5, plan stage F14): an edge from `Main` of the
    /// `handle` to the entry of the handled body, from each `Return` of the
    /// handled body to `Exit` of the `handle`, and from the end of the
    /// cleanup chain of the handled body for each destination past the
    /// handler to the copy of the cleanup block of the `handle` for that
    /// destination. The nodes of both bodies must be in the table.
    pub fn splice(&mut self, p: &Program, facts: &mut FnFacts, site: BodyId, frames: &Frames) {
        let Some(b) = p.bodies.get(site.index()) else {
            return;
        };
        self.splice_scopes(p, facts, site, b);
        for (bi, blk) in b.blocks.iter().enumerate() {
            let TermKind::Handle {
                handler, unwind, ..
            } = &blk.term.kind
            else {
                continue;
            };
            if blk.cleanup {
                continue;
            }
            let block = BlockId(u32::try_from(bi).unwrap_or(u32::MAX));
            let Some(hb) = p.handlers.get(handler.index()).map(|d| d.handled) else {
                continue;
            };
            let Some(h) = p.bodies.get(hb.index()) else {
                continue;
            };
            let at = |phase| NodeKey {
                body: site,
                block,
                at: TERM,
                phase,
                dest: NORMAL,
            };
            if let (Some(main), Some(first)) =
                (self.get(at(Phase::Main)), self.first(hb, h.entry, NORMAL))
            {
                facts.cfg_edge.push((main, first));
            }
            if let Some(exit) = self.get(at(Phase::Exit)) {
                for (ri, rb) in h.blocks.iter().enumerate() {
                    if rb.cleanup || !matches!(rb.term.kind, TermKind::Return) {
                        continue;
                    }
                    let r = NodeKey {
                        body: hb,
                        block: BlockId(u32::try_from(ri).unwrap_or(u32::MAX)),
                        at: TERM,
                        phase: Phase::Main,
                        dest: NORMAL,
                    };
                    if let Some(n) = self.get(r) {
                        facts.cfg_edge.push((n, exit));
                    }
                }
            }
            let own = Dest::Handler {
                handler: *handler,
                value: true,
            }
            .id();
            // An abort to this handler ends at the `Landing` of the `handle`
            // (plan stage F15, the minimal form of stage F14).
            let end = |d: u32| NodeKey {
                body: hb,
                block: h.unwind_exit,
                at: TERM,
                phase: Phase::Main,
                dest: d,
            };
            if let (Some(from), Some(to)) = (self.get(end(own)), self.get(at(Phase::Landing))) {
                facts.cfg_edge.push((from, to));
            }
            self.reentry_edges(facts, (site, block), *handler, frames);
            let Some(u) = unwind else {
                continue;
            };
            for d in self.copies(hb, h.unwind_exit) {
                if d == own {
                    continue;
                }
                let end = NodeKey {
                    body: hb,
                    block: h.unwind_exit,
                    at: TERM,
                    phase: Phase::Main,
                    dest: d,
                };
                if let (Some(from), Some(to)) = (self.get(end), self.first(site, *u, d)) {
                    facts.cfg_edge.push((from, to));
                }
            }
        }
    }

    /// The splice of each scope body of the `scope` terminators of body
    /// `site` (body `b`; `docs/ir.md` 6.5, plan stage F18): an edge from
    /// `Main` of the `scope` to the entry of the scope body, from each
    /// `Return` of the scope body to `Exit` of the `scope`, and from the end
    /// of the cleanup chain of the scope body for each destination to the
    /// copy of the cleanup block of the `scope` for that destination. No
    /// clause stops an abort there: a scope has no `Landing`.
    fn splice_scopes(&self, p: &Program, facts: &mut FnFacts, site: BodyId, b: &Body) {
        for (bi, blk) in b.blocks.iter().enumerate() {
            let TermKind::Scope { scope, unwind, .. } = &blk.term.kind else {
                continue;
            };
            if blk.cleanup {
                continue;
            }
            let block = BlockId(u32::try_from(bi).unwrap_or(u32::MAX));
            let Some(sb) = p.scopes.get(scope.index()).map(|d| d.body) else {
                continue;
            };
            let Some(s) = p.bodies.get(sb.index()) else {
                continue;
            };
            let at = |phase| NodeKey {
                body: site,
                block,
                at: TERM,
                phase,
                dest: NORMAL,
            };
            if let (Some(main), Some(first)) =
                (self.get(at(Phase::Main)), self.first(sb, s.entry, NORMAL))
            {
                facts.cfg_edge.push((main, first));
            }
            if let Some(exit) = self.get(at(Phase::Exit)) {
                for (ri, rb) in s.blocks.iter().enumerate() {
                    if rb.cleanup || !matches!(rb.term.kind, TermKind::Return) {
                        continue;
                    }
                    let r = NodeKey {
                        body: sb,
                        block: BlockId(u32::try_from(ri).unwrap_or(u32::MAX)),
                        at: TERM,
                        phase: Phase::Main,
                        dest: NORMAL,
                    };
                    if let Some(n) = self.get(r) {
                        facts.cfg_edge.push((n, exit));
                    }
                }
            }
            let Some(u) = unwind else {
                continue;
            };
            for d in self.copies(sb, s.unwind_exit) {
                let end = NodeKey {
                    body: sb,
                    block: s.unwind_exit,
                    at: TERM,
                    phase: Phase::Main,
                    dest: d,
                };
                if let (Some(from), Some(to)) = (self.get(end), self.first(site, *u, d)) {
                    facts.cfg_edge.push((from, to));
                }
            }
        }
    }

    /// Returns the node of `key`, and makes it if it does not exist, with
    /// the label, the kind and the IR location of `text` (see
    /// [`FnFacts::add_ir_node`]).
    fn node(&mut self, facts: &mut FnFacts, key: NodeKey, span: Span, text: [&str; 3]) -> NodeId {
        if let Some(&n) = self.ids.get(&key) {
            return n;
        }
        let [label, kind, at] = text;
        let n = facts.add_ir_node(span, label, kind, at);
        self.ids.insert(key, n);
        n
    }

    /// The re-entry edges of the `handle` of handler `h` at the end of block
    /// `block` of body `site` (`docs/ir.md` 6.5, plan stage F16).
    ///
    /// - A clause that can run more than once in one run of the handled
    ///   body runs its code after `resume` once for each run: a cycle from
    ///   `Post` through a `Copy` node of the `handle` back to `Post`.
    /// - A `multi` resume runs the code after each node of the handled body
    ///   that runs its clause again, from a copy of the frames of the
    ///   handled body: an edge from `Post` (the clause code between two
    ///   `resume`s ran there) to the `Copy` node of that node, then to its
    ///   `Ret`.
    fn reentry_edges(
        &mut self,
        facts: &mut FnFacts,
        (site, block): (BodyId, BlockId),
        h: weft_ir::HandlerId,
        frames: &Frames,
    ) {
        let at = |body, block, phase| NodeKey {
            body,
            block,
            at: TERM,
            phase,
            dest: NORMAL,
        };
        let Some(post) = self.get(at(site, block, Phase::Post)) else {
            return;
        };
        let info = facts.node(post).clone();
        if frames.runs_twice(h) {
            let c = self.node(
                facts,
                at(site, block, Phase::Copy),
                info.span,
                ["handle copy", "handle copy", &info.at],
            );
            facts.cfg_edge.push((post, c));
            facts.cfg_edge.push((c, post));
        }
        for &(pb, pblk) in frames.reentries(h) {
            let Some(ret) = self.get(at(pb, pblk, Phase::Ret)) else {
                continue;
            };
            let r = facts.node(ret).clone();
            let kind = r
                .kind
                .strip_suffix(" ret")
                .map_or_else(|| "copy".to_string(), |k| format!("{k} copy"));
            let c = self.node(
                facts,
                at(pb, pblk, Phase::Copy),
                r.span,
                [&r.label, &kind, &r.at],
            );
            facts.cfg_edge.push((post, c));
            facts.cfg_edge.push((c, ret));
        }
    }

    /// The re-entry edges after the nodes `rows` (of body `root` and of the
    /// handled bodies that splice into it) that can wait
    /// at a `multi` operation of a handler of a caller (OL-R2a, plan stage
    /// F16, `docs/ir.md` 6.5): a later `resume` runs the code after each of
    /// them again, up to the `Return` of the body. An edge from each
    /// `Return` of the body to the `Copy` node of the node, then to its
    /// `Ret`.
    pub fn row_reentry_edges(
        &mut self,
        p: &Program,
        facts: &mut FnFacts,
        root: BodyId,
        rows: &[(BodyId, BlockId)],
    ) {
        let Some(b) = p.bodies.get(root.index()) else {
            return;
        };
        let at = |body, block, phase| NodeKey {
            body,
            block,
            at: TERM,
            phase,
            dest: NORMAL,
        };
        let returns: Vec<NodeId> = b
            .blocks
            .iter()
            .enumerate()
            .filter(|(_, blk)| !blk.cleanup && matches!(blk.term.kind, TermKind::Return))
            .filter_map(|(i, _)| {
                self.get(at(
                    root,
                    BlockId(u32::try_from(i).unwrap_or(u32::MAX)),
                    Phase::Main,
                ))
            })
            .collect();
        for &(pb, pblk) in rows {
            let at = |block, phase| at(pb, block, phase);
            let Some(ret) = self.get(at(pblk, Phase::Ret)) else {
                continue;
            };
            let r = facts.node(ret).clone();
            let kind = r
                .kind
                .strip_suffix(" ret")
                .map_or_else(|| "copy".to_string(), |k| format!("{k} copy"));
            let c = self.node(
                facts,
                at(pblk, Phase::Copy),
                r.span,
                [&r.label, &kind, &r.at],
            );
            for &x in &returns {
                facts.cfg_edge.push((x, c));
            }
            facts.cfg_edge.push((c, ret));
        }
    }

    /// The node of `key`, if it exists.
    pub fn get(&self, key: NodeKey) -> Option<NodeId> {
        self.ids.get(&key).copied()
    }

    /// The first node of copy `dest` of block `block` of body `body`.
    pub fn first(&self, body: BodyId, block: BlockId, dest: u32) -> Option<NodeId> {
        self.firsts.get(&(body, block, dest)).copied()
    }

    /// The destinations of the copies of block `block` of body `body`.
    pub fn copies(&self, body: BodyId, block: BlockId) -> Vec<u32> {
        self.firsts
            .range((body, block, 0)..=(body, block, u32::MAX))
            .map(|(k, _)| k.2)
            .collect()
    }

    /// The nodes of statement `at` (or of the terminator, [`TERM`]) of block
    /// `block` of body `body`: each phase of each copy, in the order of the
    /// keys.
    pub fn nodes_at(
        &self,
        body: BodyId,
        block: BlockId,
        at: u32,
    ) -> impl Iterator<Item = (&NodeKey, &NodeId)> {
        let lo = NodeKey {
            body,
            block,
            at,
            phase: Phase::Main,
            dest: 0,
        };
        let hi = NodeKey {
            body,
            block,
            at,
            phase: Phase::Copy,
            dest: u32::MAX,
        };
        self.ids.range(lo..=hi)
    }

    /// The number of nodes.
    pub fn len(&self) -> usize {
        self.ids.len()
    }

    /// True if the table has no node.
    pub fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }

    /// The keys and the nodes, in the order of the keys.
    pub fn iter(&self) -> impl Iterator<Item = (&NodeKey, &NodeId)> {
        self.ids.iter()
    }
}
