//! The well-formedness rules of the IR (`docs/ir.md` section 4).
//!
//! The builder makes bodies that obey these rules. The verifier checks them in each
//! test, in debug builds after each build, and on each input of the gate. A broken
//! rule is a bug of the builder, not an error of the program. The invariants that
//! the design calls "by construction" follow from these rules and from one fact
//! template for each instruction.
//!
//! [`verify_program`] checks V1 to V18. Each [`Broken`] value names its rule, the
//! body, and the block and the local if the rule has them.
//!
//! Some rules are partly structural, because the IR does not keep all the facts that
//! the statement of the rule names:
//!
//! - V9: the builder moves a temporary when it uses the temporary, so a `Move` of a
//!   whole temporary is valid for each type (`move _3` of a `&Vec<u64>` receiver, as
//!   the M3 example of `docs/ir.md` 5.37 shows). For a whole local the verifier
//!   reads [`Props::copy`](crate::Props::copy) of the local. For a part it computes
//!   the property from the type table ([`TyTable::not_copy`], which
//!   `weft_sema::props::ir_props` uses too). A part of a function type can be a closure, whose
//!   properties come from the analysis and not from the type, so the verifier does
//!   not check `Copy` or `Move` of such a part. The same holds for a part of a
//!   continuation type: a `multi` continuation is plain data, a `once` one is not.
//! - V10: an extern function with an empty stated row and no intrinsic meaning
//!   cannot abort. The IR does not record an `assert` in an extern function.
//! - V12: the verifier checks that each temporary has one `Live`, and that at a
//!   `Return` the parameters, the capability and the continuation end last, after
//!   `_0` gets its value and after the temporaries end. A missing `Dead` of a
//!   temporary is a [`Rule::LeakedCell`] (V6).
//! - V16: the verifier takes "newest first" for temporaries as "highest index
//!   first", because the builder makes each temporary when it needs it.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt;

use crate::ty::{AdtKind, ExternDeref, FnTy, Lang, Ty};
use crate::{
    id_of, AggKind, BlockId, Body, BodyId, BodyKind, Callee, CapEnvId, CapOperand, CaptureMode,
    ClosureId, EffectId, IterSource, LocalId, LocalKind, Operand, Place, Program, Proj, Rvalue,
    StmtKind, TermKind, TyId, TyTable, VariantIdx,
};

/// One broken rule: the rule, and where the verifier found it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Broken {
    /// The rule and its details.
    pub rule: Rule,
    /// The body.
    pub body: BodyId,
    /// The block, if the rule is about one block.
    pub block: Option<BlockId>,
    /// The local, if the rule is about one local.
    pub local: Option<LocalId>,
}

/// A rule that a body or a program breaks. [`Rule::number`] gives the rule of
/// `docs/ir.md` section 4.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Rule {
    /// V1: a successor (this block) is not a block of the body. The entry or the
    /// unwind exit can be the missing block too.
    NoBlock(BlockId),
    /// V2: an edge to this block breaks the cleanup split: a normal edge goes from a
    /// normal block to a cleanup block or back, or an abort edge goes to a normal
    /// block.
    CleanupEdge(BlockId),
    /// V3: a cleanup block ends with a terminator other than `Goto` or `UnwindExit`
    /// (a `Return` among them).
    CleanupTerm,
    /// V4: a local is used where it has no cell on some path from the entry.
    NotLive,
    /// V5: a local gets `Live` while it has a cell.
    LiveTwice,
    /// V6: a local still has a cell at `Return` (other than `_0`) or at `UnwindExit`.
    /// The upvar locals and the environment are not in this rule.
    LeakedCell,
    /// V7: `UnwindExit` is in a block that is not the unwind exit, or the unwind exit
    /// has another terminator.
    UnwindExit,
    /// V8: the projection at this index of the place does not fit the type.
    BadProj(usize),
    /// V8: a `Variant` projection is in a block that no `Switch` on the discriminant
    /// of the same place (for this variant) dominates.
    VariantUntested,
    /// V9: a `Copy` of a value that is not plain data.
    CopyNotCopy,
    /// V9: a `Move` of plain data (not a temporary and not an upvar local).
    MoveOfCopy,
    /// V9: a `Move` through a reference.
    MoveThroughRef,
    /// V10: a terminator that can abort has no `unwind` block.
    NoUnwind,
    /// V11: a capability operand is not a capability value, or a `Row` operand names
    /// an effect that the capability environment of the body binds.
    BadCap,
    /// V11: a `Resume` names a place that is not a continuation of the clause, an
    /// upvar local of one, or a `Kont` field of an environment.
    BadKont,
    /// V12: a temporary does not have exactly one `Live`.
    TempLive,
    /// V12: at a `Return`, a statement other than the end of a parameter, the
    /// capability or the continuation comes after the end of one of them.
    FrameEndOrder,
    /// V13: a `Kept` capture is borrowed in the closure body, or its operand in the
    /// closure aggregate is not a copy of its source cell (a whole local, or a capture
    /// of the maker closure).
    KeptBorrowed,
    /// V13: the stated capture mode is not the mode of rule CAPTURE.
    CaptureMode {
        /// The mode in the closure declaration.
        stated: CaptureMode,
        /// The mode that rule CAPTURE gives.
        rule: CaptureMode,
    },
    /// V14: an upvar local is in a body that cannot have upvar locals, or names a
    /// local that the parent body does not have; the environment is in a body that
    /// is not a closure; or one of them has `Live` or `Dead`.
    BadUpvar,
    /// V14: a `Move` of a place below the environment in a closure that is not `once`.
    EnvMove,
    /// V15: a handled body or a scope body is not named by exactly one terminator, a
    /// clause by exactly one handler, or a closure body by exactly one closure.
    NotOnceRun,
    /// V15: the declaration that the body kind names does not name the body.
    BadKind,
    /// V16: the cleanup chain of a clause does not start with `UnwindKont` of its
    /// continuation.
    KontNotFirst,
    /// V16: a value of a cleanup chain is out of order: `_0` with a value, then the
    /// temporaries newest first, then the locals from the highest index, then `_0`
    /// with no value, then the parameters.
    UnwindOrder,
    /// V17: a `Drop` is on a place with no `Deref`, or the next statement is not an
    /// `Assign` of the same place.
    BadDrop,
    /// V18: a write of `_0` that reaches a `Return` is not inside the origin of the
    /// `Return`.
    ReturnOrigin,
}

impl Rule {
    /// Returns the number of the rule in `docs/ir.md` section 4.
    pub const fn number(&self) -> u8 {
        match self {
            Self::NoBlock(_) => 1,
            Self::CleanupEdge(_) => 2,
            Self::CleanupTerm => 3,
            Self::NotLive => 4,
            Self::LiveTwice => 5,
            Self::LeakedCell => 6,
            Self::UnwindExit => 7,
            Self::BadProj(_) | Self::VariantUntested => 8,
            Self::CopyNotCopy | Self::MoveOfCopy | Self::MoveThroughRef => 9,
            Self::NoUnwind => 10,
            Self::BadCap | Self::BadKont => 11,
            Self::TempLive | Self::FrameEndOrder => 12,
            Self::KeptBorrowed | Self::CaptureMode { .. } => 13,
            Self::BadUpvar | Self::EnvMove => 14,
            Self::NotOnceRun | Self::BadKind => 15,
            Self::KontNotFirst | Self::UnwindOrder => 16,
            Self::BadDrop => 17,
            Self::ReturnOrigin => 18,
        }
    }

    /// Returns a short text of the rule.
    pub fn text(&self) -> String {
        match self {
            Self::NoBlock(b) => format!("bb{} is not a block of the body", b.0),
            Self::CleanupEdge(b) => format!("the edge to bb{} breaks the cleanup split", b.0),
            Self::CleanupTerm => "a cleanup block ends with a wrong terminator".to_string(),
            Self::NotLive => "a local is used where it can have no cell".to_string(),
            Self::LiveTwice => "a local gets `Live` while it has a cell".to_string(),
            Self::LeakedCell => "a local still has a cell at the end of the frame".to_string(),
            Self::UnwindExit => "`UnwindExit` is not only in the unwind exit".to_string(),
            Self::BadProj(i) => format!("projection {i} does not fit the type"),
            Self::VariantUntested => {
                "a variant projection has no test of the variant before it".to_string()
            }
            Self::CopyNotCopy => "a copy of a value that is not plain data".to_string(),
            Self::MoveOfCopy => "a move of plain data".to_string(),
            Self::MoveThroughRef => "a move through a reference".to_string(),
            Self::NoUnwind => "a terminator that can abort has no unwind block".to_string(),
            Self::BadCap => "a capability operand is not valid here".to_string(),
            Self::BadKont => "a resume does not name a continuation".to_string(),
            Self::TempLive => "a temporary does not have exactly one `Live`".to_string(),
            Self::FrameEndOrder => "the frame end is out of order".to_string(),
            Self::KeptBorrowed => "a kept capture is borrowed".to_string(),
            Self::CaptureMode { stated, rule } => {
                format!("the capture is {stated:?}, but rule CAPTURE gives {rule:?}")
            }
            Self::BadUpvar => "an upvar local or the environment is not valid".to_string(),
            Self::EnvMove => {
                "a move below the environment of a closure that is not once".to_string()
            }
            Self::NotOnceRun => "a frame is not named exactly once".to_string(),
            Self::BadKind => "the declaration of the body kind does not name the body".to_string(),
            Self::KontNotFirst => {
                "the cleanup chain of a clause does not start with `UnwindKont`".to_string()
            }
            Self::UnwindOrder => "a value of the cleanup chain is out of order".to_string(),
            Self::BadDrop => {
                "a `Drop` is not right before an `Assign` behind a pointer".to_string()
            }
            Self::ReturnOrigin => {
                "a write of `_0` is not inside the origin of the `Return`".to_string()
            }
        }
    }
}

impl fmt::Display for Broken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "V{}: body b{}", self.rule.number(), self.body.0)?;
        if let Some(b) = self.block {
            write!(f, ", bb{}", b.0)?;
        }
        if let Some(l) = self.local {
            write!(f, ", _{}", l.0)?;
        }
        write!(f, ": {}", self.rule.text())
    }
}

/// Checks the rules V1 to V18 on each body of program `p`, with the type table
/// `tys`. Returns each broken rule once, in the order of the bodies.
pub fn verify_program(p: &Program, tys: &TyTable) -> Vec<Broken> {
    let mut out = Vec::new();
    for i in 0..p.bodies.len() {
        out.extend(verify_body(p, tys, BodyId(id_of(i))));
    }
    once_run(p, &mut out);
    for (ci, c) in p.closures.iter().enumerate() {
        kept(p, tys, ClosureId(id_of(ci)), c, &mut out);
    }
    let mut seen = HashSet::new();
    out.retain(|b| seen.insert(b.clone()));
    out
}

/// Checks the rules of one body of program `p`: V1 to V12, V14, V16 to V18. The
/// rules V13 and V15 are about more than one body; [`verify_program`] checks them.
pub fn verify_body(p: &Program, tys: &TyTable, id: BodyId) -> Vec<Broken> {
    let Some(body) = p.body(id) else {
        return Vec::new();
    };
    let mut cx = Cx {
        p,
        tys,
        id,
        body,
        out: Vec::new(),
    };
    cx.edges();
    if cx.out.iter().any(|b| matches!(b.rule, Rule::NoBlock(_))) {
        return cx.out;
    }
    let g = Graph::new(body);
    cx.storage(&g);
    cx.types(&g);
    cx.unwinds();
    cx.caps();
    cx.temps();
    cx.upvars();
    cx.chains(&g);
    cx.drops();
    cx.returns();
    cx.out
}

/// The suffixes of cleanup chains that a walk of V16 checked with no broken order:
/// the first value of each one (its rank and local), by its first block and the
/// rank of `_0` in the chain.
type CleanSuffixes = BTreeMap<(usize, Option<u8>), Option<(u8, LocalId)>>;

/// Returns block id `i`.
fn bid(i: usize) -> BlockId {
    BlockId(id_of(i))
}

/// Returns local id `i`.
fn lid(i: usize) -> LocalId {
    LocalId(id_of(i))
}

// ---------------------------------------------------------------------------
// The control-flow graph
// ---------------------------------------------------------------------------

/// The edges of one body (normal and abort edges), the blocks that the entry
/// reaches, and the immediate dominators.
struct Graph {
    /// The predecessors of each block, one for each edge.
    preds: Vec<Vec<usize>>,
    /// The blocks that the entry reaches, in reverse post-order.
    rpo: Vec<usize>,
    /// The immediate dominator of each block that the entry reaches. The entry is
    /// its own dominator.
    idom: Vec<Option<usize>>,
}

impl Graph {
    /// Makes the graph of `body`. Each successor is a block (rule V1 holds).
    fn new(body: &Body) -> Self {
        let n = body.blocks.len();
        let succs: Vec<Vec<usize>> = body
            .blocks
            .iter()
            .map(|b| {
                b.term
                    .kind
                    .successors()
                    .iter()
                    .map(|s| s.index())
                    .filter(|&s| s < n)
                    .collect()
            })
            .collect();
        let mut preds = vec![Vec::new(); n];
        for (b, ss) in succs.iter().enumerate() {
            for &s in ss {
                if let Some(p) = preds.get_mut(s) {
                    p.push(b);
                }
            }
        }
        // Post-order with an explicit stack: long chains of blocks must not use
        // the call stack.
        let entry = body.entry.index();
        let mut post = Vec::new();
        let mut seen = vec![false; n];
        if entry < n {
            let mut stack = vec![(entry, 0usize)];
            seen[entry] = true;
            while let Some((b, i)) = stack.pop() {
                if let Some(&s) = succs[b].get(i) {
                    stack.push((b, i + 1));
                    if !seen[s] {
                        seen[s] = true;
                        stack.push((s, 0));
                    }
                } else {
                    post.push(b);
                }
            }
        }
        let rpo: Vec<usize> = post.into_iter().rev().collect();
        let idom = dominators(&rpo, &preds, n);
        Self { preds, rpo, idom }
    }

    /// Returns true if the entry reaches block `b`.
    fn reached(&self, b: usize) -> bool {
        self.idom.get(b).is_some_and(Option::is_some)
    }
}

/// Returns the immediate dominator of each block (Cooper, Harvey and Kennedy, "A
/// simple, fast dominance algorithm").
fn dominators(rpo: &[usize], preds: &[Vec<usize>], n: usize) -> Vec<Option<usize>> {
    let mut order = vec![usize::MAX; n];
    for (i, &b) in rpo.iter().enumerate() {
        order[b] = i;
    }
    let mut idom: Vec<Option<usize>> = vec![None; n];
    let Some(&entry) = rpo.first() else {
        return idom;
    };
    idom[entry] = Some(entry);
    let intersect = |idom: &[Option<usize>], mut a: usize, mut b: usize| {
        while a != b {
            while order[a] > order[b] {
                match idom[a] {
                    Some(x) => a = x,
                    None => return b,
                }
            }
            while order[b] > order[a] {
                match idom[b] {
                    Some(x) => b = x,
                    None => return a,
                }
            }
        }
        a
    };
    let mut changed = true;
    while changed {
        changed = false;
        for &b in rpo.iter().skip(1) {
            let mut new: Option<usize> = None;
            for &pr in &preds[b] {
                if idom[pr].is_none() {
                    continue;
                }
                new = Some(new.map_or(pr, |x| intersect(&idom, pr, x)));
            }
            if new.is_some() && idom[b] != new {
                idom[b] = new;
                changed = true;
            }
        }
    }
    idom
}

// ---------------------------------------------------------------------------
// Uses of places
// ---------------------------------------------------------------------------

/// One use of a place or a local in a statement or a terminator.
#[derive(Clone, Copy)]
enum Use<'a> {
    /// An operand.
    Op(&'a Operand),
    /// A place that is written, read whole (a length, a discriminant) or named.
    Place(&'a Place),
    /// A place that a reference (or an iterator over elements) points into.
    Borrow(&'a Place),
    /// A local that is not in a place (the orphans of a `ScopeWait`).
    Local(LocalId),
}

/// Calls `f` for each use of a right side.
fn rvalue_uses<'a>(r: &'a Rvalue, f: &mut impl FnMut(Use<'a>)) {
    match r {
        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => f(Use::Op(o)),
        Rvalue::Binary(_, _, x, y) | Rvalue::Iter(IterSource::Range(x, y)) => {
            f(Use::Op(x));
            f(Use::Op(y));
        }
        Rvalue::Ref(p) | Rvalue::Iter(IterSource::Elems(p)) => f(Use::Borrow(p)),
        Rvalue::Len(p) | Rvalue::Discriminant(p) => f(Use::Place(p)),
        Rvalue::Aggregate(_, ops) | Rvalue::Concat(ops) => {
            for o in ops {
                f(Use::Op(o));
            }
        }
    }
}

/// Calls `f` for each use of a statement. `Live`, `Dead` and `UnwindKont` have no
/// uses: the storage rules check them.
fn stmt_uses<'a>(k: &'a StmtKind, f: &mut impl FnMut(Use<'a>)) {
    match k {
        StmtKind::Live(_) | StmtKind::Dead(_) | StmtKind::UnwindKont(_) => {}
        StmtKind::Assign(p, r) => {
            rvalue_uses(r, f);
            f(Use::Place(p));
        }
        StmtKind::Drop(p)
        | StmtKind::Consume(p)
        | StmtKind::Uninit(p)
        | StmtKind::Mention(p)
        | StmtKind::UnwindValue(p, _) => f(Use::Place(p)),
        StmtKind::Bounds(p, o) => {
            f(Use::Place(p));
            f(Use::Op(o));
        }
        StmtKind::Print(ops) => {
            for o in ops {
                f(Use::Op(o));
            }
        }
    }
}

/// Calls `f` for each use of a terminator.
fn term_uses<'a>(k: &'a TermKind, f: &mut impl FnMut(Use<'a>)) {
    match k {
        TermKind::Switch { on, .. } => f(Use::Op(on)),
        TermKind::Call {
            callee, args, dest, ..
        } => {
            if let Callee::Value(o) = callee {
                f(Use::Op(o));
            }
            for o in args {
                f(Use::Op(o));
            }
            f(Use::Place(dest));
        }
        TermKind::Perform {
            cap, args, dest, ..
        } => {
            if let CapOperand::Local(p) = cap {
                f(Use::Place(p));
            }
            for o in args {
                f(Use::Op(o));
            }
            f(Use::Place(dest));
        }
        TermKind::Resume {
            kont, arg, dest, ..
        } => {
            f(Use::Place(kont));
            f(Use::Op(arg));
            f(Use::Place(dest));
        }
        TermKind::Handle { dest, .. } | TermKind::Scope { dest, .. } => f(Use::Place(dest)),
        TermKind::ScopeWait { scope, orphans, .. } => {
            f(Use::Place(scope));
            for l in orphans {
                f(Use::Local(*l));
            }
        }
        TermKind::Spawn {
            scope, task, dest, ..
        } => {
            f(Use::Op(scope));
            f(Use::Op(task));
            if let Some(d) = dest {
                f(Use::Place(d));
            }
        }
        TermKind::Join { task, dest, .. } => {
            f(Use::Op(task));
            f(Use::Place(dest));
        }
        TermKind::Detach { task, .. } => f(Use::Op(task)),
        TermKind::Fork { branches, dest, .. } => {
            for o in branches {
                f(Use::Op(o));
            }
            f(Use::Place(dest));
        }
        TermKind::Assert { cond, .. } => f(Use::Op(cond)),
        TermKind::IterNext { iter, dest, .. } => {
            f(Use::Place(iter));
            f(Use::Place(dest));
        }
        TermKind::Goto(_) | TermKind::Return | TermKind::UnwindExit | TermKind::Unreachable => {}
    }
}

/// Returns the places of a use, if it has one.
const fn use_place<'a>(u: &Use<'a>) -> Option<&'a Place> {
    match u {
        Use::Op(o) => o.place(),
        Use::Place(p) | Use::Borrow(p) => Some(p),
        Use::Local(_) => None,
    }
}

// ---------------------------------------------------------------------------
// The type of a place
// ---------------------------------------------------------------------------

/// The type of a place after some projections.
#[derive(Clone, Copy, Debug)]
enum Pt {
    /// A value of this type.
    Ty(TyId),
    /// The payload of a variant of this enum type.
    Variant(TyId, VariantIdx),
    /// The environment of this closure.
    Env(ClosureId),
    /// The verifier cannot find the type (the table has no interned form of it).
    Unknown,
}

/// Returns type `t` with the type parameters replaced by `args`, if the table has
/// the result. A type with no parameter is the same type.
fn subst(tys: &TyTable, t: TyId, args: &[TyId]) -> Option<TyId> {
    if args.is_empty() || !tys.mentions_param(t) {
        return Some(t);
    }
    let s = |x: TyId| subst(tys, x, args);
    let list = |xs: &[TyId]| xs.iter().map(|&x| s(x)).collect::<Option<Vec<TyId>>>();
    let new = match tys.try_get(t)? {
        Ty::Param(i) => return args.get(*i as usize).copied(),
        Ty::Tuple(ts) => Ty::Tuple(list(ts)?),
        Ty::Array(x, n) => Ty::Array(s(*x)?, *n),
        Ty::Slice(x) => Ty::Slice(s(*x)?),
        Ty::Ref(x) => Ty::Ref(s(*x)?),
        Ty::Iter(x) => Ty::Iter(s(*x)?),
        Ty::Adt(a, xs) => Ty::Adt(*a, list(xs)?),
        Ty::Cont(a, b) => Ty::Cont(s(*a)?, s(*b)?),
        Ty::Fn(f) => Ty::Fn(FnTy {
            params: list(&f.params)?,
            ret: s(f.ret)?,
            row: f.row.clone(),
        }),
        Ty::Unit | Ty::Bool | Ty::Never | Ty::Int(_) | Ty::Scope | Ty::Cap(_) => return Some(t),
    };
    tys.find(&new)
}

/// Returns the first type argument as a place type, or `Unknown`.
fn first_arg(args: &[TyId]) -> Pt {
    args.first().map_or(Pt::Unknown, |&x| Pt::Ty(x))
}

// ---------------------------------------------------------------------------
// The rules of one body
// ---------------------------------------------------------------------------

/// The context of the checks of one body.
struct Cx<'a> {
    p: &'a Program,
    tys: &'a TyTable,
    id: BodyId,
    body: &'a Body,
    out: Vec<Broken>,
}

/// The cells of the locals at a point: one flag for each local.
type Cells = Vec<bool>;

/// The writes of `_0` that reach a point. A write is a statement (block, index) or
/// a terminator (block, `usize::MAX`).
type Writes = BTreeSet<(usize, usize)>;

impl<'a> Cx<'a> {
    /// Records a broken rule of this body.
    fn push(&mut self, rule: Rule, block: Option<BlockId>, local: Option<LocalId>) {
        self.out.push(Broken {
            rule,
            body: self.id,
            block,
            local,
        });
    }

    /// Returns the kind of local `l`.
    fn kind(&self, l: LocalId) -> Option<LocalKind> {
        self.body.local_kind(l)
    }

    /// Returns true for a local whose cell belongs to another frame: an upvar local
    /// or the environment of a closure. It has no `Live` and no `Dead`.
    fn foreign(&self, l: LocalId) -> bool {
        matches!(self.kind(l), Some(LocalKind::Upvar(_) | LocalKind::Env))
    }

    /// Returns true for a local that ends last at the frame end: a parameter, the
    /// capability parameter or the continuation.
    fn is_param(&self, l: LocalId) -> bool {
        self.body.params.contains(&l)
            || self.body.caps.iter().any(|(_, c)| *c == l)
            || self.body.kont.is_some_and(|(k, _)| k == l)
    }

    /// V1, V2, V3, V7: the edges and the exits.
    fn edges(&mut self) {
        let n = self.body.blocks.len();
        if self.body.entry.index() >= n {
            self.push(Rule::NoBlock(self.body.entry), None, None);
        }
        if self.body.unwind_exit.index() >= n {
            self.push(Rule::NoBlock(self.body.unwind_exit), None, None);
        }
        for (i, blk) in self.body.blocks.iter().enumerate() {
            let id = bid(i);
            for s in blk.term.kind.normal_successors() {
                match self.body.block(s) {
                    None => self.push(Rule::NoBlock(s), Some(id), None),
                    Some(t) if t.cleanup != blk.cleanup => {
                        self.push(Rule::CleanupEdge(s), Some(id), None);
                    }
                    Some(_) => {}
                }
            }
            if let Some(u) = blk.term.kind.unwind() {
                match self.body.block(u) {
                    None => self.push(Rule::NoBlock(u), Some(id), None),
                    Some(t) if !t.cleanup => self.push(Rule::CleanupEdge(u), Some(id), None),
                    Some(_) => {}
                }
            }
            let is_exit = id == self.body.unwind_exit;
            match &blk.term.kind {
                TermKind::UnwindExit if !is_exit => self.push(Rule::UnwindExit, Some(id), None),
                TermKind::Goto(_) | TermKind::UnwindExit => {}
                _ if blk.cleanup => self.push(Rule::CleanupTerm, Some(id), None),
                _ if is_exit => self.push(Rule::UnwindExit, Some(id), None),
                _ => {}
            }
        }
    }

    /// Applies the storage effect of statement `k` to `cells`.
    fn step_cells(&self, k: &StmtKind, cells: &mut Cells) {
        match k {
            StmtKind::Live(l) => {
                if let Some(x) = cells.get_mut(l.index()) {
                    *x = true;
                }
            }
            StmtKind::Dead(l) if !self.foreign(*l) => {
                if let Some(x) = cells.get_mut(l.index()) {
                    *x = false;
                }
            }
            _ => {}
        }
    }

    /// V4, V5, V6: a must analysis of the cells. A use needs a cell on each path from
    /// the entry. This rule is the source of `bound_before_use` for each component.
    fn storage(&mut self, g: &Graph) {
        let n = self.body.locals.len();
        let mut entry: Cells = vec![false; n];
        for l in self.body.entry_locals() {
            if let Some(x) = entry.get_mut(l.index()) {
                *x = true;
            }
        }
        let mut at: Vec<Option<Cells>> = vec![None; self.body.blocks.len()];
        let e = self.body.entry.index();
        at[e] = Some(entry);
        let mut work = vec![e];
        while let Some(b) = work.pop() {
            let Some(mut cells) = at[b].clone() else {
                continue;
            };
            let blk = &self.body.blocks[b];
            for s in &blk.stmts {
                self.step_cells(&s.kind, &mut cells);
            }
            for s in blk.term.kind.successors() {
                let s = s.index();
                match &mut at[s] {
                    slot @ None => {
                        *slot = Some(cells.clone());
                        work.push(s);
                    }
                    Some(old) => {
                        let mut changed = false;
                        for (a, c) in old.iter_mut().zip(&cells) {
                            if *a && !*c {
                                *a = false;
                                changed = true;
                            }
                        }
                        if changed {
                            work.push(s);
                        }
                    }
                }
            }
        }
        for &b in &g.rpo {
            let Some(mut cells) = at[b].clone() else {
                continue;
            };
            let id = bid(b);
            let blk = &self.body.blocks[b];
            for s in &blk.stmts {
                self.check_cells(&s.kind, &cells, id);
                self.step_cells(&s.kind, &mut cells);
            }
            let mut uses = Vec::new();
            term_uses(&blk.term.kind, &mut |u| uses.push(u));
            for u in uses {
                self.need_use(u, &cells, id);
            }
            let normal = match blk.term.kind {
                TermKind::Return => true,
                TermKind::UnwindExit => false,
                _ => continue,
            };
            for (i, has) in cells.iter().enumerate() {
                let l = lid(i);
                if *has && !self.foreign(l) && !(normal && l == self.body.ret) {
                    self.push(Rule::LeakedCell, Some(id), Some(l));
                }
            }
        }
    }

    /// Records V4 if local `l` has no cell.
    fn need(&mut self, l: LocalId, cells: &Cells, b: BlockId) {
        if !cells.get(l.index()).copied().unwrap_or(false) {
            self.push(Rule::NotLive, Some(b), Some(l));
        }
    }

    /// Records V4 for each local that use `u` names.
    fn need_use(&mut self, u: Use<'_>, cells: &Cells, b: BlockId) {
        if let Use::Local(l) = u {
            self.need(l, cells, b);
        }
        let Some(p) = use_place(&u) else { return };
        self.need(p.local, cells, b);
        for pr in &p.proj {
            if let Proj::Index(i) = pr {
                self.need(*i, cells, b);
            }
        }
    }

    /// V4 and V5 at one statement.
    fn check_cells(&mut self, k: &StmtKind, cells: &Cells, b: BlockId) {
        match k {
            StmtKind::Live(l) => {
                if cells.get(l.index()).copied().unwrap_or(false) {
                    self.push(Rule::LiveTwice, Some(b), Some(*l));
                }
            }
            StmtKind::Dead(l) | StmtKind::UnwindKont(l) => self.need(*l, cells, b),
            _ => {
                let mut uses = Vec::new();
                stmt_uses(k, &mut |u| uses.push(u));
                for u in uses {
                    self.need_use(u, cells, b);
                }
            }
        }
    }

    /// V8 and V9: each place fits its type, and each operand fits the properties of
    /// its place.
    fn types(&mut self, g: &Graph) {
        let discr = self.discriminants();
        for (i, blk) in self.body.blocks.iter().enumerate() {
            let id = bid(i);
            let mut uses = Vec::new();
            for s in &blk.stmts {
                // An `Uninit` names the path of a place field of a value built
                // in place, also below a variant that no test chose: it reads
                // nothing (`docs/ir.md` 5.2, 5.17). An `UnwindValue` names a
                // linear part, also the payload of a variant: the unwinder
                // finishes it only if the value has the variant (5.1.6).
                if let StmtKind::Uninit(p) | StmtKind::UnwindValue(p, _) = &s.kind {
                    if let Err(i) = self.place_ty(p) {
                        self.push(Rule::BadProj(i), Some(id), Some(p.local));
                    }
                    continue;
                }
                stmt_uses(&s.kind, &mut |u| uses.push(u));
            }
            term_uses(&blk.term.kind, &mut |u| uses.push(u));
            for u in uses {
                if let Some(p) = use_place(&u) {
                    self.place_fits(p, id, g, &discr);
                }
                if let Use::Op(o) = u {
                    self.operand_fits(o, id);
                }
            }
        }
    }

    /// Returns, for each local, the places whose discriminant the body assigns to it.
    fn discriminants(&self) -> BTreeMap<LocalId, Vec<&'a Place>> {
        let body: &'a Body = self.body;
        let mut m: BTreeMap<LocalId, Vec<&'a Place>> = BTreeMap::new();
        for blk in &body.blocks {
            for s in &blk.stmts {
                if let StmtKind::Assign(t, Rvalue::Discriminant(q)) = &s.kind {
                    if t.is_local() {
                        m.entry(t.local).or_default().push(q);
                    }
                }
            }
        }
        m
    }

    /// Returns the place type of the local of place `p`, before its projections.
    fn local_pt(&self, l: LocalId) -> Pt {
        let Some(d) = self.body.local(l) else {
            return Pt::Unknown;
        };
        match (d.kind, self.body.kind) {
            (LocalKind::Env, BodyKind::Closure(c)) => Pt::Env(c),
            _ => Pt::Ty(d.ty),
        }
    }

    /// Returns the type of place `p`, or the index of the first projection that does
    /// not fit the type.
    fn place_ty(&self, p: &Place) -> Result<Pt, usize> {
        let mut pt = self.local_pt(p.local);
        for (i, pr) in p.proj.iter().enumerate() {
            pt = self.project(pt, pr).ok_or(i)?;
        }
        Ok(pt)
    }

    /// Returns the type after projection `pr` of a place of type `pt`, or `None` if
    /// the projection does not fit the type.
    fn project(&self, pt: Pt, pr: &Proj) -> Option<Pt> {
        let t = match pt {
            Pt::Unknown => return Some(Pt::Unknown),
            Pt::Env(c) => {
                let Proj::Field(f) = pr else { return None };
                return self.env_field_ty(c, f.index());
            }
            Pt::Variant(t, v) => {
                let Proj::Field(f) = pr else { return None };
                let (Ty::Adt(_, args), Some(AdtKind::Enum(vs))) = self.adt_kind(t)? else {
                    return None;
                };
                let fty = *vs.get(v.index())?.fields.get(f.index())?;
                return Some(subst(self.tys, fty, args).map_or(Pt::Unknown, Pt::Ty));
            }
            Pt::Ty(t) => t,
        };
        let Some(ty) = self.tys.try_get(t) else {
            return Some(Pt::Unknown);
        };
        let lang = |a: &crate::AdtId| self.tys.adts().get(a.index()).and_then(|d| d.lang);
        let ext = |a: &crate::AdtId| match self.tys.adts().get(a.index()).map(|d| &d.kind) {
            Some(AdtKind::Extern {
                elem_unstable,
                deref,
            }) => Some((*elem_unstable, *deref)),
            _ => None,
        };
        match (pr, ty) {
            (Proj::Deref(k), Ty::Adt(a, args)) => {
                let ok = lang(a) != Some(Lang::Ptr)
                    && match (k, lang(a), ext(a)) {
                        (crate::DerefKind::Box, Some(Lang::Box), _)
                        | (crate::DerefKind::Rc, Some(Lang::Rc), _) => true,
                        (kind, _, Some((_, Some(d)))) => matches!(
                            (kind, d),
                            (
                                crate::DerefKind::Box | crate::DerefKind::Ref,
                                ExternDeref::Stable
                            ) | (crate::DerefKind::Box, ExternDeref::Unstable)
                                | (crate::DerefKind::Rc, ExternDeref::Group)
                        ),
                        _ => false,
                    };
                ok.then(|| first_arg(args))
            }
            (Proj::Field(f), Ty::Tuple(ts)) => ts.get(f.index()).map(|&x| Pt::Ty(x)),
            (Proj::Field(f), Ty::Adt(a, args)) => {
                match self.tys.adts().get(a.index()).map(|d| &d.kind) {
                    Some(AdtKind::Struct(fs)) => {
                        let fty = fs.get(f.index())?.ty;
                        Some(subst(self.tys, fty, args).map_or(Pt::Unknown, Pt::Ty))
                    }
                    _ => None,
                }
            }
            (Proj::Variant(v), Ty::Adt(a, _)) => {
                match self.tys.adts().get(a.index()).map(|d| &d.kind) {
                    Some(AdtKind::Enum(vs)) if v.index() < vs.len() => Some(Pt::Variant(t, *v)),
                    _ => None,
                }
            }
            (Proj::Deref(crate::DerefKind::Ref), Ty::Ref(x))
            | (Proj::Index(_), Ty::Array(x, _) | Ty::Slice(x)) => Some(Pt::Ty(*x)),
            (Proj::Index(_), Ty::Adt(a, args)) => (lang(a) == Some(Lang::Vec)
                || ext(a).is_some_and(|(e, _)| e.is_some()))
            .then(|| first_arg(args)),
            (Proj::Elems, Ty::Array(x, _) | Ty::Slice(x)) => Some(self.slice_of(*x)),
            (Proj::Elems, Ty::Adt(a, args)) => (lang(a) == Some(Lang::Vec)
                || ext(a).is_some_and(|(e, _)| e.is_some()))
            .then(|| args.first().map_or(Pt::Unknown, |&x| self.slice_of(x))),
            (Proj::Split(..), Ty::Slice(_)) => Some(Pt::Ty(t)),
            _ => None,
        }
    }

    /// Returns `[x]` as a place type.
    fn slice_of(&self, x: TyId) -> Pt {
        self.tys.find(&Ty::Slice(x)).map_or(Pt::Unknown, Pt::Ty)
    }

    /// Returns type `t` and the shape of its definition, if it is a definition.
    fn adt_kind(&self, t: TyId) -> Option<(&Ty, Option<&AdtKind>)> {
        let ty = self.tys.try_get(t)?;
        match ty {
            Ty::Adt(a, _) => Some((ty, self.tys.adts().get(a.index()).map(|d| &d.kind))),
            _ => None,
        }
    }

    /// Returns the type of field `k` of the environment of closure `c`: the type
    /// of its source place in the maker, or a reference to it for `ByRef`.
    fn env_field_ty(&self, c: ClosureId, k: usize) -> Option<Pt> {
        let decl = self.p.closures.get(c.index())?;
        let cap = decl.captures.get(k)?;
        let Some(src) = source_ty(self.p, self.tys, decl, &cap.source) else {
            return Some(Pt::Unknown);
        };
        Some(match cap.mode {
            CaptureMode::ByRef => self.tys.find(&Ty::Ref(src)).map_or(Pt::Unknown, Pt::Ty),
            _ => Pt::Ty(src),
        })
    }

    /// V8 for place `p` in block `b`.
    fn place_fits(
        &mut self,
        p: &Place,
        b: BlockId,
        g: &Graph,
        discr: &BTreeMap<LocalId, Vec<&Place>>,
    ) {
        if let Err(i) = self.place_ty(p) {
            self.push(Rule::BadProj(i), Some(b), Some(p.local));
            return;
        }
        for (i, pr) in p.proj.iter().enumerate() {
            match pr {
                Proj::Index(x) => {
                    let usize_ty = self
                        .body
                        .local(*x)
                        .and_then(|d| self.tys.try_get(d.ty))
                        .is_some_and(|t| *t == Ty::Int(crate::IntTy::Usize));
                    if !usize_ty {
                        self.push(Rule::BadProj(i), Some(b), Some(p.local));
                        return;
                    }
                }
                Proj::Variant(v) => {
                    let prefix = Place {
                        local: p.local,
                        proj: p.proj[..i].to_vec(),
                    };
                    if !self.tested(g, b, &prefix, *v, discr) {
                        self.push(Rule::VariantUntested, Some(b), Some(p.local));
                        return;
                    }
                }
                _ => {}
            }
        }
    }

    /// Returns true if a block that dominates `b` is the arm of variant `v` of a
    /// `Switch` on the discriminant of `prefix`, and that `Switch` is its only way in.
    fn tested(
        &self,
        g: &Graph,
        b: BlockId,
        prefix: &Place,
        v: VariantIdx,
        discr: &BTreeMap<LocalId, Vec<&Place>>,
    ) -> bool {
        if !g.reached(b.index()) {
            return true;
        }
        let mut cur = b.index();
        loop {
            if self.arm_of(g, cur, prefix, v, discr) {
                return true;
            }
            match g.idom.get(cur).copied().flatten() {
                Some(d) if d != cur => cur = d,
                _ => return false,
            }
        }
    }

    /// Returns true if block `a` has one edge in, from a `Switch` on the
    /// discriminant of `prefix`, on the arm of variant `v`.
    fn arm_of(
        &self,
        g: &Graph,
        a: usize,
        prefix: &Place,
        v: VariantIdx,
        discr: &BTreeMap<LocalId, Vec<&Place>>,
    ) -> bool {
        let [s] = g.preds.get(a).map_or(&[][..], Vec::as_slice) else {
            return false;
        };
        let Some(TermKind::Switch { on, arms, .. }) =
            self.body.block(bid(*s)).map(|x| &x.term.kind)
        else {
            return false;
        };
        let arm = arms
            .iter()
            .any(|(val, t)| t.index() == a && *val == u128::from(v.0));
        let on_discr = on.place().is_some_and(|t| {
            t.is_local() && discr.get(&t.local).is_some_and(|qs| qs.contains(&prefix))
        });
        arm && on_discr
    }

    /// Returns whether place `p` holds plain data, or `None` if the verifier cannot
    /// tell (a part of a function type or of a continuation type, or an unknown
    /// type). A continuation is plain data if its operation is `multi`, and its
    /// type does not show that.
    fn place_copy(&self, p: &Place) -> Option<bool> {
        if p.is_local() {
            return self.body.local(p.local).map(|d| d.props.copy);
        }
        let t = match self.place_ty(p).ok()? {
            Pt::Ty(t) | Pt::Variant(t, _) => t,
            Pt::Env(_) | Pt::Unknown => return None,
        };
        match self.tys.try_get(t)? {
            Ty::Fn(_) | Ty::Cont(..) => None,
            _ => Some(!self.tys.not_copy(t)),
        }
    }

    /// V9 for operand `o` in block `b`.
    fn operand_fits(&mut self, o: &Operand, b: BlockId) {
        match o {
            Operand::Const(_) => {}
            Operand::Copy(p) => {
                if self.place_copy(p) == Some(false) {
                    self.push(Rule::CopyNotCopy, Some(b), Some(p.local));
                }
            }
            Operand::Move(p) => {
                if p.proj.contains(&Proj::Deref(crate::DerefKind::Ref)) {
                    self.push(Rule::MoveThroughRef, Some(b), Some(p.local));
                    return;
                }
                let whole_ok = p.is_local()
                    && matches!(
                        self.kind(p.local),
                        Some(LocalKind::Temp(_) | LocalKind::Upvar(_))
                    );
                if !whole_ok && self.place_copy(p) == Some(true) {
                    self.push(Rule::MoveOfCopy, Some(b), Some(p.local));
                }
            }
        }
    }

    /// Returns true if a call of `f` cannot abort: an extern function with an empty
    /// stated row and no meaning of its own.
    fn cannot_abort(&self, callee: &Callee) -> bool {
        let Callee::Fn(f, _) = callee else {
            return false;
        };
        self.p.fns.get(f.index()).is_some_and(|d| {
            d.body.is_none()
                && d.intrinsic.is_none()
                && d.stated_row.as_ref().is_some_and(Vec::is_empty)
        })
    }

    /// V10: each terminator that can abort has an `unwind` block.
    fn unwinds(&mut self) {
        for (i, blk) in self.body.blocks.iter().enumerate() {
            let k = &blk.term.kind;
            if !k.can_abort() || k.unwind().is_some() {
                continue;
            }
            if let TermKind::Call { callee, .. } = k {
                if self.cannot_abort(callee) {
                    continue;
                }
            }
            self.push(Rule::NoUnwind, Some(bid(i)), None);
        }
    }

    /// Returns the capture mode of place `p` if it is field `k` of the environment of
    /// this closure body: `env.k`.
    fn env_field(&self, p: &Place) -> Option<CaptureMode> {
        let BodyKind::Closure(c) = self.body.kind else {
            return None;
        };
        if self.kind(p.local) != Some(LocalKind::Env) {
            return None;
        }
        let [Proj::Field(k)] = p.proj.as_slice() else {
            return None;
        };
        let decl = self.p.closures.get(c.index())?;
        decl.captures.get(k.index()).map(|x| x.mode)
    }

    /// Returns true if the capability environment chain from `env` binds `effect`.
    fn env_binds(&self, env: CapEnvId, effect: EffectId) -> bool {
        let mut cur = Some(env);
        let mut steps = 0;
        while let Some(e) = cur {
            let Some(ce) = self.p.cap_envs.get(e.index()) else {
                return false;
            };
            if ce.adds.iter().any(|(eff, _)| *eff == effect) {
                return true;
            }
            cur = ce.parent;
            steps += 1;
            if steps > self.p.cap_envs.len() {
                return false;
            }
        }
        false
    }

    /// V11: capability operands and continuations.
    fn caps(&mut self) {
        for (i, blk) in self.body.blocks.iter().enumerate() {
            let id = bid(i);
            match &blk.term.kind {
                TermKind::Perform {
                    cap: CapOperand::Local(pl),
                    ..
                } => {
                    let ok = if pl.is_local() {
                        let d = self.body.local(pl.local);
                        let cap_ty = d
                            .and_then(|d| self.tys.try_get(d.ty))
                            .is_some_and(|t| matches!(t, Ty::Cap(_)));
                        match d.map(|d| d.kind) {
                            Some(LocalKind::Cap(_)) => true,
                            Some(LocalKind::Upvar(_)) => cap_ty,
                            _ => false,
                        }
                    } else {
                        self.env_field(pl) == Some(CaptureMode::Cap)
                    };
                    if !ok {
                        self.push(Rule::BadCap, Some(id), Some(pl.local));
                    }
                }
                TermKind::Perform {
                    cap: CapOperand::Row(e),
                    ..
                } => {
                    if self.env_binds(self.body.cap_env, *e) {
                        self.push(Rule::BadCap, Some(id), None);
                    }
                }
                TermKind::Resume { kont, .. } => {
                    let ok = if kont.is_local() {
                        let d = self.body.local(kont.local);
                        let cont_ty = d
                            .and_then(|d| self.tys.try_get(d.ty))
                            .is_some_and(|t| matches!(t, Ty::Cont(..)));
                        match d.map(|d| d.kind) {
                            Some(LocalKind::Kont(_)) => {
                                matches!(self.body.kind, BodyKind::Clause(..))
                            }
                            // A body inside a clause names the continuation
                            // through an upvar local.
                            Some(LocalKind::Upvar(_)) => cont_ty,
                            _ => false,
                        }
                    } else {
                        self.env_field(kont) == Some(CaptureMode::Kont)
                    };
                    if !ok {
                        self.push(Rule::BadKont, Some(id), Some(kont.local));
                    }
                }
                _ => {}
            }
        }
    }

    /// V12: each temporary has one `Live`; at a `Return` the parameters end last.
    fn temps(&mut self) {
        let mut lives: Vec<(u32, Option<BlockId>)> = vec![(0, None); self.body.locals.len()];
        for (i, blk) in self.body.blocks.iter().enumerate() {
            for s in &blk.stmts {
                if let StmtKind::Live(l) = s.kind {
                    if let Some(x) = lives.get_mut(l.index()) {
                        x.0 += 1;
                        if x.0 == 2 {
                            x.1 = Some(bid(i));
                        }
                    }
                }
            }
        }
        for (i, d) in self.body.locals.iter().enumerate() {
            if matches!(d.kind, LocalKind::Temp(_)) && lives[i].0 != 1 {
                self.push(Rule::TempLive, lives[i].1, Some(lid(i)));
            }
        }
        for (i, blk) in self.body.blocks.iter().enumerate() {
            if blk.term.kind != TermKind::Return {
                continue;
            }
            let mut ended = false;
            for s in &blk.stmts {
                let local = match &s.kind {
                    StmtKind::Dead(l) if self.is_param(*l) => {
                        ended = true;
                        continue;
                    }
                    StmtKind::Live(l) | StmtKind::Dead(l) | StmtKind::UnwindKont(l) => Some(*l),
                    other => {
                        let mut first = None;
                        stmt_uses(other, &mut |u| {
                            if first.is_none() {
                                first = use_place(&u).map(|p| p.local);
                            }
                        });
                        first
                    }
                };
                if ended {
                    self.push(Rule::FrameEndOrder, Some(bid(i)), local);
                    break;
                }
            }
        }
    }

    /// V14: upvar locals and the environment of a closure.
    fn upvars(&mut self) {
        for (i, d) in self.body.locals.iter().enumerate() {
            let ok = match d.kind {
                LocalKind::Upvar(src) => {
                    self.body.kind.has_upvars()
                        && self
                            .body
                            .parent
                            .and_then(|pb| self.p.body(pb))
                            .is_some_and(|pb| src.index() < pb.locals.len())
                }
                LocalKind::Env => matches!(self.body.kind, BodyKind::Closure(_)),
                _ => continue,
            };
            if !ok {
                self.push(Rule::BadUpvar, None, Some(lid(i)));
            }
        }
        for (i, blk) in self.body.blocks.iter().enumerate() {
            for s in &blk.stmts {
                if let StmtKind::Live(l) | StmtKind::Dead(l) = s.kind {
                    if self.foreign(l) {
                        self.push(Rule::BadUpvar, Some(bid(i)), Some(l));
                    }
                }
            }
        }
        let once = match self.body.kind {
            BodyKind::Closure(c) => self.p.closures.get(c.index()).is_some_and(|d| d.once),
            _ => return,
        };
        if once {
            return;
        }
        for (i, blk) in self.body.blocks.iter().enumerate() {
            let mut uses = Vec::new();
            for s in &blk.stmts {
                stmt_uses(&s.kind, &mut |u| uses.push(u));
            }
            term_uses(&blk.term.kind, &mut |u| uses.push(u));
            for u in uses {
                if let Use::Op(Operand::Move(p)) = u {
                    if !p.proj.is_empty() && self.kind(p.local) == Some(LocalKind::Env) {
                        self.push(Rule::EnvMove, Some(bid(i)), Some(p.local));
                    }
                }
            }
        }
    }

    /// Returns, for each block that the entry reaches on normal edges, whether `_0`
    /// has a value on each path to the start of the block (`must`) and on some path
    /// (`may`).
    fn ret_written(&self) -> Vec<Option<(bool, bool)>> {
        let n = self.body.blocks.len();
        let mut at: Vec<Option<(bool, bool)>> = vec![None; n];
        let e = self.body.entry.index();
        at[e] = Some((false, false));
        let mut work = vec![e];
        while let Some(b) = work.pop() {
            let Some(mut st) = at[b] else { continue };
            let blk = &self.body.blocks[b];
            if blk.stmts.iter().any(|s| self.writes_ret_stmt(&s.kind)) {
                st = (true, true);
            }
            if blk
                .term
                .kind
                .dest()
                .is_some_and(|d| d.local == self.body.ret)
            {
                st = (true, true);
            }
            for s in blk.term.kind.normal_successors() {
                let s = s.index();
                let new = match at[s] {
                    None => st,
                    Some((m, y)) => (m && st.0, y || st.1),
                };
                if at[s] != Some(new) {
                    at[s] = Some(new);
                    work.push(s);
                }
            }
        }
        at
    }

    /// Returns true if statement `k` writes `_0` or a part of it.
    fn writes_ret_stmt(&self, k: &StmtKind) -> bool {
        matches!(k, StmtKind::Assign(p, _) if p.local == self.body.ret)
    }

    /// V16: the order of each cleanup chain.
    ///
    /// Chains share their suffixes (`docs/ir.md` 5.1.6). A suffix that one walk
    /// checked with no broken order is not walked again: the next walk compares
    /// its last value with the first value of the suffix and stops there. So the
    /// cost is linear in the blocks of the chains, not in their lengths.
    fn chains(&mut self, g: &Graph) {
        let written = self.ret_written();
        // The head of each chain, with the state of `_0` at each abort edge into it.
        let mut heads: BTreeMap<usize, Vec<(bool, bool)>> = BTreeMap::new();
        for (i, blk) in self.body.blocks.iter().enumerate() {
            if blk.cleanup || !g.reached(i) {
                continue;
            }
            let Some(u) = blk.term.kind.unwind() else {
                continue;
            };
            let Some(mut st) = written[i] else { continue };
            if blk.stmts.iter().any(|s| self.writes_ret_stmt(&s.kind)) {
                st = (true, true);
            }
            heads.entry(u.index()).or_default().push(st);
        }
        let mut clean = BTreeMap::new();
        for (head, states) in heads {
            let ret_rank = if states.iter().all(|s| s.0) {
                Some(1)
            } else if states.iter().all(|s| !s.1) {
                Some(4)
            } else {
                None
            };
            self.chain(head, ret_rank, &mut clean);
        }
    }

    /// Returns the rank of local `l` in a cleanup chain (V16): 1 for `_0` with a
    /// value, 2 for a temporary, 3 for another local, 4 for `_0` with no value, 5
    /// for a parameter. `None` for a value that the order skips: the continuation
    /// of a clause, a local of another frame, and `_0` if the paths into the chain
    /// do not agree (`ret_rank` is `None`).
    fn rank(&self, l: LocalId, kont: Option<LocalId>, ret_rank: Option<u8>) -> Option<u8> {
        if Some(l) == kont || self.foreign(l) {
            return None;
        }
        Some(if l == self.body.ret {
            ret_rank?
        } else if matches!(self.kind(l), Some(LocalKind::Temp(_))) {
            2
        } else if self.is_param(l) {
            5
        } else {
            3
        })
    }

    /// V16 for the chain that starts at block `head`. `ret_rank` is the place of `_0`
    /// in the order (1 with a value, 4 with no value), or `None` if the paths into
    /// the chain do not agree. `clean` has the first value of each suffix that a
    /// walk checked with no broken order, by its first block and `ret_rank`.
    fn chain(&mut self, head: usize, ret_rank: Option<u8>, clean: &mut CleanSuffixes) {
        let kont = match (self.body.kind, self.body.kont) {
            (BodyKind::Clause(..), Some((k, _))) => Some(k),
            _ => None,
        };
        let body = self.body;
        if let Some(k) = kont {
            // The first statement of the chain.
            let mut cur = head;
            let mut seen = BTreeSet::new();
            let mut first = None;
            while let Some(blk) = body.blocks.get(cur) {
                if !blk.cleanup || !seen.insert(cur) {
                    break;
                }
                if let Some(s) = blk.stmts.first() {
                    first = Some(&s.kind);
                    break;
                }
                match blk.term.kind {
                    TermKind::Goto(t) => cur = t.index(),
                    _ => break,
                }
            }
            if first != Some(&StmtKind::UnwindKont(k)) {
                self.push(Rule::KontNotFirst, Some(bid(head)), Some(k));
            }
        }
        let bad = |(lr, ll): (u8, LocalId), (rank, l): (u8, LocalId)| {
            rank < lr || (rank == lr && (rank == 2 || rank == 3) && l > ll)
        };
        let mut last: Option<(u8, LocalId)> = None;
        // The blocks of this walk, each with its first value.
        let mut walked: Vec<(usize, Option<(u8, LocalId)>)> = Vec::new();
        let mut ok = true;
        let mut tail: Option<(u8, LocalId)> = None;
        let mut cur = head;
        let mut seen = BTreeSet::new();
        while let Some(blk) = body.blocks.get(cur) {
            if !blk.cleanup || !seen.insert(cur) {
                break;
            }
            if ok {
                if let Some(&first) = clean.get(&(cur, ret_rank)) {
                    let fits = match (last, first) {
                        (Some(a), Some(b)) => a.1 == b.1 || !bad(a, b),
                        _ => true,
                    };
                    if fits {
                        tail = first;
                        break;
                    }
                }
            }
            let mut own = None;
            for s in &blk.stmts {
                let l = match &s.kind {
                    StmtKind::Dead(l) => *l,
                    StmtKind::UnwindValue(p, _) => p.local,
                    _ => continue,
                };
                let Some(rank) = self.rank(l, kont, ret_rank) else {
                    continue;
                };
                own = own.or(Some((rank, l)));
                let Some(prev) = last else {
                    last = Some((rank, l));
                    continue;
                };
                if prev.1 == l {
                    continue;
                }
                if bad(prev, (rank, l)) {
                    ok = false;
                    self.push(Rule::UnwindOrder, Some(bid(cur)), Some(l));
                } else {
                    last = Some((rank, l));
                }
            }
            walked.push((cur, own));
            match blk.term.kind {
                TermKind::Goto(t) => cur = t.index(),
                _ => break,
            }
        }
        if ok {
            for (b, own) in walked.into_iter().rev() {
                tail = own.or(tail);
                clean.insert((b, ret_rank), tail);
            }
        }
    }

    /// V17: `Drop` only behind a pointer, right before an `Assign` of the same place.
    fn drops(&mut self) {
        for (i, blk) in self.body.blocks.iter().enumerate() {
            for (j, s) in blk.stmts.iter().enumerate() {
                let StmtKind::Drop(p) = &s.kind else { continue };
                let next_ok = matches!(
                    blk.stmts.get(j + 1).map(|n| &n.kind),
                    Some(StmtKind::Assign(q, _)) if q == p
                );
                if !p.has_deref() || !next_ok {
                    self.push(Rule::BadDrop, Some(bid(i)), Some(p.local));
                }
            }
        }
    }

    /// V18: each write of `_0` that reaches a `Return` is inside the origin of the
    /// `Return`: the origin is the expression whose value the frame gives back.
    fn returns(&mut self) {
        let ret = self.body.ret;
        let n = self.body.blocks.len();
        let step = |set: &mut Writes, w: (usize, usize), p: &Place| {
            if p.is_local() {
                set.clear();
            }
            set.insert(w);
        };
        let mut at: Vec<Option<Writes>> = vec![None; n];
        let e = self.body.entry.index();
        at[e] = Some(Writes::new());
        let mut work = vec![e];
        let mut ends: Vec<(usize, Writes)> = Vec::new();
        while let Some(b) = work.pop() {
            let Some(mut set) = at[b].clone() else {
                continue;
            };
            let blk = &self.body.blocks[b];
            for (j, s) in blk.stmts.iter().enumerate() {
                if let StmtKind::Assign(p, _) = &s.kind {
                    if p.local == ret {
                        step(&mut set, (b, j), p);
                    }
                }
            }
            if let Some(d) = blk.term.kind.dest() {
                if d.local == ret {
                    step(&mut set, (b, usize::MAX), d);
                }
            }
            for s in blk.term.kind.normal_successors() {
                let s = s.index();
                let changed = match &mut at[s] {
                    slot @ None => {
                        *slot = Some(set.clone());
                        true
                    }
                    Some(old) => {
                        let before = old.len();
                        old.extend(set.iter().copied());
                        old.len() != before
                    }
                };
                if changed {
                    work.push(s);
                }
            }
        }
        for (b, blk) in self.body.blocks.iter().enumerate() {
            if blk.term.kind != TermKind::Return {
                continue;
            }
            let Some(mut set) = at[b].clone() else {
                continue;
            };
            for (j, s) in blk.stmts.iter().enumerate() {
                if let StmtKind::Assign(p, _) = &s.kind {
                    if p.local == ret {
                        step(&mut set, (b, j), p);
                    }
                }
            }
            ends.push((b, set));
        }
        for (b, set) in ends {
            let span = self.body.blocks[b].term.origin.span;
            let outside = set.iter().any(|&(wb, wi)| {
                let blk = &self.body.blocks[wb];
                let o = if wi == usize::MAX {
                    blk.term.origin
                } else {
                    blk.stmts[wi].origin
                };
                !span.contains(o.span)
            });
            if outside {
                self.push(Rule::ReturnOrigin, Some(bid(b)), Some(ret));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The rules of more than one body
// ---------------------------------------------------------------------------

/// V15: each handled body and each scope body is named by exactly one terminator,
/// each clause by exactly one handler, and each closure body by exactly one closure.
/// The declaration that a body kind names names the body.
fn once_run(p: &Program, out: &mut Vec<Broken>) {
    let mut named = vec![0u32; p.bodies.len()];
    let mut add = |b: BodyId| {
        if let Some(x) = named.get_mut(b.index()) {
            *x += 1;
        }
    };
    for body in &p.bodies {
        for blk in &body.blocks {
            match &blk.term.kind {
                TermKind::Handle { handler, .. } => {
                    if let Some(h) = p.handlers.get(handler.index()) {
                        add(h.handled);
                    }
                }
                TermKind::Scope { scope, .. } => {
                    if let Some(s) = p.scopes.get(scope.index()) {
                        add(s.body);
                    }
                }
                _ => {}
            }
        }
    }
    for h in &p.handlers {
        for (_, c) in &h.clauses {
            add(*c);
        }
    }
    for c in &p.closures {
        add(c.body);
    }
    for (i, body) in p.bodies.iter().enumerate() {
        let id = BodyId(id_of(i));
        let once = matches!(
            body.kind,
            BodyKind::Handled(_) | BodyKind::Scope(_) | BodyKind::Clause(..) | BodyKind::Closure(_)
        );
        let broken = |rule| Broken {
            rule,
            body: id,
            block: None,
            local: None,
        };
        if once && named[i] != 1 {
            out.push(broken(Rule::NotOnceRun));
            continue;
        }
        let names = match body.kind {
            BodyKind::Fn(f) => p.fns.get(f.index()).is_some_and(|d| d.body == Some(id)),
            BodyKind::Test(t) => p.tests.get(t.index()).is_some_and(|d| d.body == id),
            BodyKind::Closure(c) => p.closures.get(c.index()).is_some_and(|d| d.body == id),
            BodyKind::Clause(h, op) => p
                .handlers
                .get(h.index())
                .is_some_and(|d| d.clauses.contains(&(op, id))),
            BodyKind::Handled(h) => p.handlers.get(h.index()).is_some_and(|d| d.handled == id),
            BodyKind::Scope(s) => p.scopes.get(s.index()).is_some_and(|d| d.body == id),
        };
        if !names {
            out.push(broken(Rule::BadKind));
        }
    }
}

/// Returns true if place `p` of the closure body is at or below field `k` of the
/// environment local `env`.
fn below_field(p: &Place, env: LocalId, k: usize) -> bool {
    p.local == env && matches!(p.proj.first(), Some(Proj::Field(f)) if f.index() == k)
}

/// Returns true if a borrow of place `p` of the closure body borrows the captured
/// variable `k` (rule CAPTURE): `p` is at or below the variable (`env.k`, or
/// `(*env.k)` for a `ByRef` capture) and no `Deref(Ref)` follows it. A borrow
/// through a captured reference points into the target of the reference, not into
/// the cell of the variable.
fn borrows_var(p: &Place, env: LocalId, k: usize, mode: CaptureMode) -> bool {
    if !below_field(p, env, k) {
        return false;
    }
    let skip = if mode == CaptureMode::ByRef {
        if p.proj.get(1) != Some(&Proj::Deref(crate::DerefKind::Ref)) {
            return false;
        }
        2
    } else {
        1
    };
    !p.proj
        .iter()
        .skip(skip)
        .any(|x| *x == Proj::Deref(crate::DerefKind::Ref))
}

/// Returns the type of place `src` of the maker of closure `c`, if the verifier
/// can find it. The maker of a closure has a lower id than the closure body, so
/// the walk through the makers ends.
fn source_ty(p: &Program, tys: &TyTable, c: &crate::ClosureDecl, src: &Place) -> Option<TyId> {
    if c.maker.index() >= c.body.index() {
        return None;
    }
    let maker = p.body(c.maker)?;
    let cx = Cx {
        p,
        tys,
        id: c.maker,
        body: maker,
        out: Vec::new(),
    };
    match cx.place_ty(src).ok()? {
        Pt::Ty(t) => Some(t),
        Pt::Variant(..) | Pt::Env(_) | Pt::Unknown => None,
    }
}

/// Returns true if the source of capture `k` of closure `c` holds plain data: the
/// properties of a whole local, or of the capture of the maker that the source
/// names, or else the type.
fn source_copy(p: &Program, tys: &TyTable, c: &crate::ClosureDecl, k: usize) -> Option<bool> {
    let cap = c.captures.get(k)?;
    let maker = p.body(c.maker)?;
    let d = maker.local(cap.source.local)?;
    if cap.source.is_local() {
        return Some(d.props.copy);
    }
    let t = source_ty(p, tys, c, &cap.source)?;
    if !matches!(tys.try_get(t), Some(Ty::Fn(_))) {
        return Some(!tys.not_copy(t));
    }
    // A function value of a capture of the maker: the properties of its source.
    let (BodyKind::Closure(mc), LocalKind::Env, Some(Proj::Field(j))) =
        (maker.kind, d.kind, cap.source.proj.first())
    else {
        return None;
    };
    let outer = p.closures.get(mc.index())?;
    if outer.body.index() >= c.body.index() {
        return None;
    }
    source_copy(p, tys, outer, j.index())
}

/// Returns true if `src` is a cell that a `Kept` capture can share: a whole local
/// of the maker, or a capture `env.j` (or `(*env.j)`) of the maker closure.
fn kept_cell(maker: &Body, src: &Place) -> bool {
    if src.is_local() {
        return true;
    }
    maker.local_kind(src.local) == Some(LocalKind::Env)
        && matches!(
            src.proj.as_slice(),
            [Proj::Field(_)] | [Proj::Field(_), Proj::Deref(crate::DerefKind::Ref)]
        )
}

/// Returns the mode that rule CAPTURE (`docs/ir.md` 5.1.7) gives capture `k` of
/// closure `c`, from the closure body and the source local.
fn capture_rule(
    p: &Program,
    tys: &TyTable,
    c: &crate::ClosureDecl,
    k: usize,
) -> Option<CaptureMode> {
    let cap = c.captures.get(k)?;
    let src = p.body(c.maker)?.local(cap.source.local)?;
    let src_ty = if cap.source.is_local() {
        Some(src.ty)
    } else {
        source_ty(p, tys, c, &cap.source)
    };
    let kind = cap.source.is_local().then_some(src.kind);
    match (kind, src_ty.and_then(|t| tys.try_get(t))) {
        (Some(LocalKind::Cap(_)), _) | (_, Some(Ty::Cap(_))) => return Some(CaptureMode::Cap),
        (Some(LocalKind::Kont(_)), _) | (_, Some(Ty::Cont(..))) => return Some(CaptureMode::Kont),
        _ => {}
    }
    let body = p.body(c.body)?;
    let env = body
        .params
        .first()
        .copied()
        .filter(|&e| body.local_kind(e) == Some(LocalKind::Env))?;
    let mut moved = false;
    let mut consumed = false;
    let mut borrowed = false;
    for blk in &body.blocks {
        let mut f = |u: Use<'_>| match u {
            Use::Op(Operand::Move(q)) if below_field(q, env, k) => moved = true,
            Use::Borrow(q) if borrows_var(q, env, k, cap.mode) => borrowed = true,
            _ => {}
        };
        for s in &blk.stmts {
            // A by-value pattern that consumes a linear value takes it, as a move.
            if let StmtKind::Consume(q) = &s.kind {
                consumed |= below_field(q, env, k);
            }
            stmt_uses(&s.kind, &mut f);
        }
        term_uses(&blk.term.kind, &mut f);
    }
    moved |= consumed;
    let copy = source_copy(p, tys, c, k)?;
    Some(if moved {
        CaptureMode::ByMove
    } else if copy && !borrowed {
        CaptureMode::Kept
    } else {
        CaptureMode::ByRef
    })
}

/// V13 for closure `ci`: a `Kept` capture is never borrowed, its aggregate operand
/// is a copy of its source cell, and each stated mode is the mode of rule CAPTURE.
fn kept(p: &Program, tys: &TyTable, ci: ClosureId, c: &crate::ClosureDecl, out: &mut Vec<Broken>) {
    let mut first_agg: Option<BlockId> = None;
    if let Some(maker) = p.body(c.maker) {
        for (bi, blk) in maker.blocks.iter().enumerate() {
            for s in &blk.stmts {
                let StmtKind::Assign(_, Rvalue::Aggregate(AggKind::Closure(cid), ops)) = &s.kind
                else {
                    continue;
                };
                if *cid != ci {
                    continue;
                }
                first_agg.get_or_insert_with(|| bid(bi));
                for (k, cap) in c.captures.iter().enumerate() {
                    if cap.mode != CaptureMode::Kept {
                        continue;
                    }
                    let cell_copy = kept_cell(maker, &cap.source)
                        && matches!(ops.get(k), Some(Operand::Copy(pl)) if *pl == cap.source);
                    if !cell_copy {
                        out.push(Broken {
                            rule: Rule::KeptBorrowed,
                            body: c.maker,
                            block: Some(bid(bi)),
                            local: Some(cap.source.local),
                        });
                    }
                }
            }
        }
    }
    if let Some(body) = p.body(c.body) {
        if let Some(env) = body.params.first().copied() {
            for (bi, blk) in body.blocks.iter().enumerate() {
                let mut hit = false;
                let mut f = |u: Use<'_>| {
                    if let Use::Borrow(q) = u {
                        hit |= c.captures.iter().enumerate().any(|(k, cap)| {
                            cap.mode == CaptureMode::Kept
                                && borrows_var(q, env, k, CaptureMode::Kept)
                        });
                    }
                };
                for s in &blk.stmts {
                    stmt_uses(&s.kind, &mut f);
                }
                if hit {
                    out.push(Broken {
                        rule: Rule::KeptBorrowed,
                        body: c.body,
                        block: Some(bid(bi)),
                        local: Some(env),
                    });
                }
            }
        }
    }
    for (k, cap) in c.captures.iter().enumerate() {
        let Some(rule) = capture_rule(p, tys, c, k) else {
            continue;
        };
        if rule != cap.mode {
            out.push(Broken {
                rule: Rule::CaptureMode {
                    stated: cap.mode,
                    rule,
                },
                body: c.maker,
                block: first_agg,
                local: Some(cap.source.local),
            });
        }
    }
}
