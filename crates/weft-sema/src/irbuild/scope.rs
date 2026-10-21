//! The construct groups of each body (plan §2.6): the scope test of the
//! migration to the `ir` fact pipeline.
//!
//! The `ir` pipeline checks a program only when each of its bodies uses only
//! the groups that are on ([`crate::Options::ir_groups`]). [`groups`] reads the
//! groups of each body of the analysis from its IR: the function or test body
//! and each body inside it (closures, clauses, handled bodies, scope bodies).
//!
//! | Group | Constructs | What the IR shows |
//! | --- | --- | --- |
//! | A | straight-line code, calls of items, aggregates, performs through the row | each body that has IR |
//! | B | `while`, `loop`, `for`, `break`, `continue` | an edge back to a block on the current path, an `IterNext`, an iterator local |
//! | C | closures, function values, function items as values, stored function values, function parameters | a closure body, a closure aggregate, a constant function, a call of a value, a local whose type has a function part |
//! | D | `handle`, clauses, `resume`, `multi` | a clause or a handled body, `Handle`, `Resume`, a perform through a local capability, a capability or continuation |
//! | E | `scope`, `spawn`, `join`, `detach`, `fork`, `sim.run`, `with_timeout` | a scope body, the task terminators, a call of an intrinsic, a task or scope value |
//! | F | values of a type parameter | a local whose type names a type parameter |
//!
//! A loop that never goes back to its head (`loop { break }`) is straight-line
//! code in the IR: it is group A. A body with no IR uses no group: it has no
//! facts in the `ir` pipeline.

use std::collections::HashSet;
use std::fmt;

use weft_ir::ty::{AdtKind, Lang, TyProp};
use weft_ir::{
    AggKind, Body, BodyKind, Callee, CapOperand, Const, LocalKind, Operand, Program, Rvalue,
    StmtKind, TermKind, Ty, TyId, TyTable,
};

use super::{Built, Outcome};

/// A construct group (plan §2.6).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Group {
    /// Straight-line code: places, borrows, branches, calls of items,
    /// aggregates, performs through the row of the caller, `on abort`.
    A,
    /// Loops and jumps.
    B,
    /// Closures and function values.
    C,
    /// Handlers and continuations.
    D,
    /// Tasks.
    E,
    /// Type parameters.
    F,
}

impl Group {
    /// The groups, in order.
    pub const ALL: [Self; 6] = [Self::A, Self::B, Self::C, Self::D, Self::E, Self::F];

    /// The letter of the group.
    pub const fn letter(self) -> char {
        match self {
            Self::A => 'A',
            Self::B => 'B',
            Self::C => 'C',
            Self::D => 'D',
            Self::E => 'E',
            Self::F => 'F',
        }
    }

    /// The bit of the group in [`Groups`].
    const fn bit(self) -> u8 {
        1 << (self as u8)
    }
}

impl fmt::Display for Group {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.letter())
    }
}

/// A set of construct groups.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Groups(u8);

impl Groups {
    /// The empty set.
    pub const NONE: Self = Self(0);

    /// Each group.
    pub const ALL: Self = Self(0b11_1111);

    /// The set of one group.
    pub const fn of(g: Group) -> Self {
        Self(g.bit())
    }

    /// This set and group `g`.
    #[must_use]
    pub const fn with(self, g: Group) -> Self {
        Self(self.0 | g.bit())
    }

    /// True if group `g` is in the set.
    pub const fn has(self, g: Group) -> bool {
        self.0 & g.bit() != 0
    }

    /// True if each group of `other` is in this set.
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    /// The groups of this set and of `other`.
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// The groups of this set that are not in `other`.
    #[must_use]
    pub const fn minus(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }

    /// True if the set is empty.
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The first group of the set, in the order of [`Group::ALL`].
    pub fn first(self) -> Option<Group> {
        self.iter().next()
    }

    /// The groups of the set, in order.
    pub fn iter(self) -> impl Iterator<Item = Group> {
        Group::ALL.into_iter().filter(move |g| self.has(*g))
    }

    /// Reads a set: one or more letters `A` to `F`, in order, each one time.
    ///
    /// # Errors
    ///
    /// Returns a message for an empty text, a letter that is not a group, a
    /// letter that is not in order, and a letter that occurs two times.
    pub fn parse(text: &str) -> Result<Self, String> {
        if text.is_empty() {
            return Err("the group set is empty".to_string());
        }
        let mut out = Self::NONE;
        let mut last: Option<Group> = None;
        for c in text.chars() {
            let Some(g) = Group::ALL.into_iter().find(|g| g.letter() == c) else {
                return Err(format!("`{c}` is not a construct group (A to F)"));
            };
            if last.is_some_and(|l| l >= g) {
                return Err(format!(
                    "the group set `{text}` must have each letter one time, in order"
                ));
            }
            last = Some(g);
            out = out.with(g);
        }
        Ok(out)
    }
}

impl fmt::Display for Groups {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for g in self.iter() {
            write!(f, "{}", g.letter())?;
        }
        Ok(())
    }
}

/// The groups of each body of the analysis, in the order of [`Built::entries`].
///
/// The groups of a body are its groups and those of each body inside it. A
/// body with no IR, and a body that the builder does not lower, uses no
/// group.
pub fn groups(built: &Built) -> Vec<Groups> {
    let p = &built.program;
    let mut out = vec![Groups::NONE; built.entries.len()];
    let mut types = TypeGroups::new(&built.tys);
    for (b, entry) in p.bodies.iter().zip(body_entries(built)) {
        if let Some(g) = entry.and_then(|e| out.get_mut(e)) {
            *g = g.union(body_groups(p, b, &mut types));
        }
    }
    out
}

/// The entry of [`Built::entries`] of each body of the program: the entry of
/// the function or test whose body is the body or a parent of it.
pub fn body_entries(built: &Built) -> Vec<Option<usize>> {
    let p = &built.program;
    let mut entry_of: Vec<Option<usize>> = vec![None; p.bodies.len()];
    for (i, e) in built.entries.iter().enumerate() {
        if let Outcome::Built(id) = e.outcome {
            if let Some(slot) = entry_of.get_mut(id.index()) {
                *slot = Some(i);
            }
        }
    }
    // A body inside an entry body has a parent with a lower id, so one pass in
    // id order finds its entry.
    for bi in 0..p.bodies.len() {
        if entry_of.get(bi).copied().flatten().is_some() {
            continue;
        }
        let parent = p.bodies.get(bi).and_then(|b| b.parent);
        let entry = parent.and_then(|q| entry_of.get(q.index()).copied().flatten());
        if let Some(slot) = entry_of.get_mut(bi) {
            *slot = entry;
        }
    }
    entry_of
}

/// The groups of one body (not of the bodies inside it).
fn body_groups(p: &Program, b: &Body, types: &mut TypeGroups<'_>) -> Groups {
    let mut g = Groups::of(Group::A);
    match b.kind {
        BodyKind::Closure(_) => g = g.with(Group::C),
        BodyKind::Clause(..) | BodyKind::Handled(_) => g = g.with(Group::D),
        BodyKind::Scope(_) => g = g.with(Group::E),
        BodyKind::Fn(_) | BodyKind::Test(_) => {}
    }
    for l in &b.locals {
        g = g.union(match l.kind {
            LocalKind::Iterator => Groups::of(Group::B),
            LocalKind::Cap(_) | LocalKind::Kont(_) => Groups::of(Group::D),
            LocalKind::ScopeCap | LocalKind::TaskResult(_) => Groups::of(Group::E),
            _ => Groups::NONE,
        });
        g = g.union(types.of(l.ty));
    }
    for blk in &b.blocks {
        for s in &blk.stmts {
            if let StmtKind::Assign(_, rv) = &s.kind {
                g = g.union(rvalue_groups(p, rv));
            }
            if let StmtKind::Print(ops) = &s.kind {
                g = g.union(operands_groups(p, ops));
            }
        }
        g = g.union(term_groups(p, &blk.term.kind));
    }
    if goes_back(b) {
        g = g.with(Group::B);
    }
    g
}

/// True if function `f` of the program is `sim.run` or `with_timeout`.
fn intrinsic(p: &Program, f: weft_ir::FnId) -> bool {
    p.fns.get(f.index()).is_some_and(|d| d.intrinsic.is_some())
}

/// The groups of an operand: a function item as a value is group C, and
/// `sim.run` or `with_timeout` as a value is group E too.
fn operand_groups(p: &Program, o: &Operand) -> Groups {
    match o {
        Operand::Const(Const::Fn(f, _)) if intrinsic(p, *f) => Groups::of(Group::C).with(Group::E),
        Operand::Const(Const::Fn(..)) => Groups::of(Group::C),
        _ => Groups::NONE,
    }
}

/// The union of the groups of the operands.
fn operands_groups(p: &Program, ops: &[Operand]) -> Groups {
    ops.iter()
        .fold(Groups::NONE, |g, o| g.union(operand_groups(p, o)))
}

/// The groups of a right side.
fn rvalue_groups(p: &Program, rv: &Rvalue) -> Groups {
    match rv {
        Rvalue::Aggregate(AggKind::Closure(_), ops) => operands_groups(p, ops).with(Group::C),
        Rvalue::Aggregate(_, ops) | Rvalue::Concat(ops) => operands_groups(p, ops),
        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => operand_groups(p, o),
        Rvalue::Binary(_, _, x, y) => operand_groups(p, x).union(operand_groups(p, y)),
        Rvalue::Ref(_) | Rvalue::Len(_) | Rvalue::Discriminant(_) | Rvalue::Iter(_) => Groups::NONE,
    }
}

/// The groups of a terminator.
fn term_groups(p: &Program, t: &TermKind) -> Groups {
    match t {
        TermKind::Call { callee, args, .. } => {
            let g = operands_groups(p, args);
            match callee {
                Callee::Value(o) => g.union(operand_groups(p, o)).with(Group::C),
                Callee::Fn(f, _) if intrinsic(p, *f) => g.with(Group::E),
                Callee::Fn(..) => g,
            }
        }
        TermKind::Perform { cap, args, .. } => {
            let g = operands_groups(p, args);
            match cap {
                CapOperand::Local(_) => g.with(Group::D),
                CapOperand::Row(_) => g,
            }
        }
        TermKind::Handle { .. } | TermKind::Resume { .. } => Groups::of(Group::D),
        TermKind::Scope { .. }
        | TermKind::ScopeWait { .. }
        | TermKind::Spawn { .. }
        | TermKind::Join { .. }
        | TermKind::Detach { .. }
        | TermKind::Fork { .. } => Groups::of(Group::E),
        TermKind::IterNext { .. } => Groups::of(Group::B),
        TermKind::Switch { on, .. } | TermKind::Assert { cond: on, .. } => operand_groups(p, on),
        TermKind::Goto(_) | TermKind::Return | TermKind::UnwindExit | TermKind::Unreachable => {
            Groups::NONE
        }
    }
}

/// True if a path from the entry of `b` goes back to a block that is on the
/// path: the body has a loop that runs again.
fn goes_back(b: &Body) -> bool {
    /// The state of a block in the walk.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum State {
        New,
        Open,
        Done,
    }
    let n = b.blocks.len();
    let mut state = vec![State::New; n];
    let succ = |i: usize| -> Vec<usize> {
        b.blocks.get(i).map_or_else(Vec::new, |blk| {
            let mut v: Vec<usize> = blk
                .term
                .kind
                .normal_successors()
                .into_iter()
                .map(weft_ir::BlockId::index)
                .collect();
            v.extend(blk.term.kind.unwind().map(weft_ir::BlockId::index));
            v
        })
    };
    let start = b.entry.index();
    if start >= n {
        return false;
    }
    // Each frame: a block and its successors that the walk did not visit yet.
    let mut stack: Vec<(usize, Vec<usize>)> = vec![(start, succ(start))];
    if let Some(s) = state.get_mut(start) {
        *s = State::Open;
    }
    while let Some((at, rest)) = stack.last_mut() {
        let at = *at;
        let Some(next) = rest.pop() else {
            if let Some(s) = state.get_mut(at) {
                *s = State::Done;
            }
            stack.pop();
            continue;
        };
        match state.get(next).copied() {
            Some(State::Open) => return true,
            Some(State::New) => {
                if let Some(s) = state.get_mut(next) {
                    *s = State::Open;
                }
                let more = succ(next);
                stack.push((next, more));
            }
            Some(State::Done) | None => {}
        }
    }
    false
}

/// The groups that the values of a type need, with a memo for each type.
///
/// A function part is group C (the property row `Fns`, which goes through
/// fields). A task handle or a scope capability is group E, a capability or a
/// continuation is group D (through fields too). A type parameter is group F.
struct TypeGroups<'a> {
    tys: &'a TyTable,
    memo: std::collections::HashMap<TyId, Groups>,
}

impl<'a> TypeGroups<'a> {
    fn new(tys: &'a TyTable) -> Self {
        Self {
            tys,
            memo: std::collections::HashMap::new(),
        }
    }

    /// The groups of the values of type `ty`.
    fn of(&mut self, ty: TyId) -> Groups {
        if let Some(g) = self.memo.get(&ty) {
            return *g;
        }
        let mut g = Groups::NONE;
        if self.has_fn(ty) {
            g = g.with(Group::C);
        }
        if self.tys.mentions_param(ty) {
            g = g.with(Group::F);
        }
        let mut seen = HashSet::new();
        g = g.union(self.task_or_handler(ty, &mut seen));
        self.memo.insert(ty, g);
        g
    }

    /// True if a value of type `ty` can hold a function value.
    fn has_fn(&self, ty: TyId) -> bool {
        let Some(t) = self.tys.try_get(ty) else {
            return false;
        };
        match t {
            Ty::Fn(_) => true,
            Ty::Adt(a, args) => self.tys.adts().get(a.index()).is_some_and(|d| {
                let row = d.row(TyProp::Fns);
                row.always
                    || row
                        .params
                        .iter()
                        .any(|&j| args.get(j as usize).is_some_and(|&x| self.has_fn(x)))
            }),
            Ty::Tuple(ts) => ts.iter().any(|&x| self.has_fn(x)),
            Ty::Array(x, _) | Ty::Slice(x) | Ty::Ref(x) | Ty::Iter(x) => self.has_fn(*x),
            Ty::Cont(..)
            | Ty::Param(_)
            | Ty::Unit
            | Ty::Bool
            | Ty::Never
            | Ty::Int(_)
            | Ty::Scope
            | Ty::Cap(_) => false,
        }
    }

    /// Group E for a task handle or a scope capability, group D for a
    /// capability or a continuation, as a part of type `ty` (through the
    /// fields of structs and the payloads of enums).
    fn task_or_handler(&self, ty: TyId, seen: &mut HashSet<TyId>) -> Groups {
        if !seen.insert(ty) {
            return Groups::NONE;
        }
        let Some(t) = self.tys.try_get(ty) else {
            return Groups::NONE;
        };
        let mut g = Groups::NONE;
        let mut walk = |x: TyId, g: &mut Groups| *g = g.union(self.task_or_handler(x, seen));
        match t {
            Ty::Scope => g = g.with(Group::E),
            Ty::Cap(_) => g = g.with(Group::D),
            Ty::Cont(a, b) => {
                g = g.with(Group::D);
                walk(*a, &mut g);
                walk(*b, &mut g);
            }
            Ty::Adt(a, args) => {
                if let Some(d) = self.tys.adts().get(a.index()) {
                    if matches!(d.lang, Some(Lang::Task | Lang::Scope)) {
                        g = g.with(Group::E);
                    }
                    let fields: Vec<TyId> = match &d.kind {
                        AdtKind::Struct(fs) => fs.iter().map(|f| f.ty).collect(),
                        AdtKind::Enum(vs) => vs.iter().flat_map(|v| v.fields.clone()).collect(),
                        AdtKind::Extern { .. } => Vec::new(),
                    };
                    for x in fields {
                        walk(x, &mut g);
                    }
                }
                for x in args {
                    walk(*x, &mut g);
                }
            }
            Ty::Tuple(ts) => {
                for x in ts {
                    walk(*x, &mut g);
                }
            }
            Ty::Array(x, _) | Ty::Slice(x) | Ty::Ref(x) | Ty::Iter(x) => walk(*x, &mut g),
            // A function value holds no task: its result is a value of its call.
            Ty::Fn(_) | Ty::Param(_) | Ty::Unit | Ty::Bool | Ty::Never | Ty::Int(_) => {}
        }
        g
    }
}
