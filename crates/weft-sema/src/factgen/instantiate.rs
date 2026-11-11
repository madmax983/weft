//! Call-site copies of callees (plan stage R0k-a, `docs/ir.md` 6.1).
//!
//! A local handler can serve an operation that a callee performs with a
//! function value or a reference in its arguments or its result (the
//! reasons C2 and D3 of the scope report). A summary of the callee cannot
//! tell what the clause does with such a value, or when the callee runs a
//! value that the clause gives back. So the fact generator puts a copy of
//! the body of the callee at the call: [`instantiate`] gives a program in
//! which each such call is the code of the callee. Then the perform is a
//! perform of the local handler, and the machinery of a handled body
//! applies (the clause runs at the node of the perform, the resume regions,
//! the `multi` re-entry, the abort edges).
//!
//! The copy of the code of a callee at a call (body `b`, block `k`):
//!
//! - Each local of the callee is a new local of `b`. A parameter is a
//!   variable of the source; `_0` is a temporary.
//! - A new block binds the parameters to the operands of the call, then
//!   goes to the entry of the callee. A `Return` of the callee gives `_0` to
//!   the destination of the call and goes to the next block. The
//!   `UnwindExit` of the callee goes to the cleanup block of the call.
//! - Each body inside the callee (a closure, a handled body, a clause, a
//!   scope body) gets a copy, with a copy of its declaration. The root
//!   capability environment of the callee is the environment of the call.
//!   A body inside a closure of the callee is in the environment of the
//!   closure body.
//! - A perform through the row of the callee goes to the capability that
//!   the environment of the call gives for the operation (through upvar
//!   locals in a body inside the callee).
//! - A closure performs through the capabilities of the point where it is
//!   made. So a closure of the callee gets a `Cap` capture for each effect
//!   that the environment of the call serves and that its code can use, as
//!   the builder gives a closure of the site (`Builder::caps_for`).
//!
//! A call is copied only if the callee is not recursive, the chain of
//! copied calls is short ([`DEPTH_BOUND`]), and the copies stay small
//! ([`BLOCK_BOUND`]). The copy is a program of the IR: the verifier checks
//! it, and the fact oracle runs it (`weft-interp`). [`Instantiated::weak_ok`]
//! says if the facts of a callee can use the weak form of a perform through
//! its row (`analysis::transfer::WeakRowOps`).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use weft_ir::{
    BlockId, Body, BodyId, BodyKind, Callee, CapArgs, CapEnv, CapEnvId, CapOperand, ClosureId,
    EffectId, FnId, HandlerId, LocalDecl, LocalId, LocalKind, OpIdx, Operand, Place, Program, Proj,
    Rvalue, ScopeId, SpawnId, Stmt, StmtKind, TempKind, Term, TermKind, TyTable,
};

use crate::irbuild::Built;

/// The most blocks that the copies add to one program.
pub const BLOCK_BOUND: usize = 6000;

/// The longest chain of copied calls.
pub const DEPTH_BOUND: usize = 8;

/// The bounds of the copies ([`instantiate_with`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    /// The most blocks that the copies add to one program.
    pub blocks: usize,
    /// The longest chain of copied calls.
    pub depth: usize,
}

impl Default for Bounds {
    fn default() -> Self {
        Self {
            blocks: BLOCK_BOUND,
            depth: DEPTH_BOUND,
        }
    }
}

/// The result of [`instantiate`].
#[derive(Clone, Debug)]
pub struct Instantiated {
    /// The program with the copies.
    pub built: Built,
    /// The number of copied calls of function items.
    pub calls: usize,
    /// The number of copied calls of closures (stage R0k-a2).
    pub closure_calls: usize,
    /// True if the facts of a callee can use the weak form of a perform
    /// through its row (`analysis::transfer::WeakRowOps`).
    ///
    /// The weak form says that code of a caller runs the function values of
    /// the operation; it does not say what the clause keeps. It is sound for
    /// the facts of the callee itself. Its summary is not sound where a local
    /// handler serves the operation, so the invariant is: no call that a
    /// local handler serves applies a summary with the weak form, also
    /// through a callee that passes the effect on. This holds if each such
    /// call has a copy (no served call of a callee that gives a function
    /// value to an operation through its row is left), and if no other
    /// code can run such a callee: no closure performs such an operation or
    /// calls such a callee, no function item value names one, and `main`
    /// and the tests do not perform such an operation or call such a callee
    /// through their row (a root handler is code of the runtime). The
    /// analysis checks the invariant again at each call
    /// (`analysis::transfer::note_weak_call`).
    pub weak_ok: bool,
    /// The call site of each block that a copy adds: the body and the block
    /// of the call, and the callee.
    pub sites: BTreeMap<(BodyId, BlockId), (BodyId, BlockId, FnId)>,
    /// The call site of each body that a copy adds.
    pub body_sites: BTreeMap<BodyId, (BodyId, BlockId, FnId)>,
    /// The closures that resume the continuation of their clause and whose
    /// one run got a copy of their body (stage R0k-c1, [`instantiate_kont`]).
    /// No run applies their summary, so the facts of their bodies need no
    /// resume point (`analysis::clause::KontCovered`).
    pub covered: BTreeSet<ClosureId>,
}

/// The effects that the code of a function can perform through its row
/// with a function value or a reference (`any`), or with a function value
/// in an argument (`fns`), also through its callees and the bodies inside
/// it.
#[derive(Clone, Debug, Default)]
struct Needs {
    any: BTreeMap<FnId, BTreeSet<EffectId>>,
    fns: BTreeMap<FnId, BTreeSet<EffectId>>,
    /// Each effect that the code of a function can perform through its row.
    row: BTreeMap<FnId, BTreeSet<EffectId>>,
    /// The functions that call a function value whose type states no row:
    /// their code can perform each effect.
    unknown: BTreeSet<FnId>,
    /// The functions that a function calls, also in the bodies inside it.
    calls: BTreeMap<FnId, BTreeSet<FnId>>,
}

/// True if a value of operation `op` of effect `e` can hold a function
/// value or a reference: `(in an argument or the result, in an argument)`.
fn risky_op(tys: &TyTable, e: EffectId, op: OpIdx) -> (bool, bool) {
    let Some(o) = tys
        .effects()
        .get(e.index())
        .and_then(|d| d.ops.get(op.index()))
    else {
        return (true, true);
    };
    let holds = |t| crate::props::ir_props(tys, t).holds_refs || crate::props::ir_has_fns(tys, t);
    let fns = o.params.iter().any(|&t| crate::props::ir_has_fns(tys, t));
    let any = fns || o.params.iter().any(|&t| holds(t)) || holds(o.ret);
    (any, fns)
}

/// True if capability environment `env` binds effect `e`.
fn env_binds(p: &Program, env: CapEnvId, e: EffectId) -> bool {
    let mut at = Some(env);
    for _ in 0..=p.cap_envs.len() {
        let Some(id) = at else { return false };
        let Some(c) = p.cap_envs.get(id.index()) else {
            return false;
        };
        if c.adds.iter().any(|(x, _)| *x == e) {
            return true;
        }
        at = c.parent;
    }
    false
}

/// The function of each body: the function whose body is the body or a
/// lexical parent of it.
fn body_fns(p: &Program) -> Vec<Option<FnId>> {
    // Follow the parent chain of each body. This does not use the order of
    // the body ids: a copy can append a body after the bodies inside it.
    p.bodies
        .iter()
        .map(|b| {
            let mut at = Some(b);
            for _ in 0..=p.bodies.len() {
                let x = at?;
                if let BodyKind::Fn(f) = x.kind {
                    return Some(f);
                }
                at = x.parent.and_then(|q| p.body(q));
            }
            None
        })
        .collect()
}

/// The bodies inside body `root` (not `root`), in the order of their ids.
fn inner_bodies(p: &Program, root: BodyId) -> Vec<BodyId> {
    // Follow the parent chain of each body. This does not use the order of
    // the body ids: a copy can append a body after the bodies inside it.
    let mut out = Vec::new();
    for (i, b) in p.bodies.iter().enumerate() {
        let mut at = b.parent;
        for _ in 0..p.bodies.len() {
            match at {
                Some(q) if q == root => {
                    out.push(BodyId(u32::try_from(i).unwrap_or(u32::MAX)));
                    break;
                }
                Some(q) => at = p.body(q).and_then(|x| x.parent),
                None => break,
            }
        }
    }
    out
}

impl Needs {
    /// The needs of each function of program `p`: a fixpoint over the calls.
    fn of(p: &Program, tys: &TyTable) -> Self {
        let owner = body_fns(p);
        let mut n = Self::default();
        // The direct performs and the call edges with the environment of the
        // call.
        let mut edges: Vec<(FnId, FnId, CapEnvId)> = Vec::new();
        for (i, b) in p.bodies.iter().enumerate() {
            let Some(f) = owner.get(i).copied().flatten() else {
                continue;
            };
            for blk in &b.blocks {
                match &blk.term.kind {
                    TermKind::Call {
                        callee: Callee::Value(o),
                        ..
                    } => match value_row(tys, b, o) {
                        Some(r) => n.row.entry(f).or_default().extend(r),
                        None => {
                            n.unknown.insert(f);
                        }
                    },
                    TermKind::Perform {
                        cap: CapOperand::Row(e),
                        op,
                        ..
                    } => {
                        n.row.entry(f).or_default().insert(*e);
                        let (any, fns) = risky_op(tys, *e, *op);
                        if any {
                            n.any.entry(f).or_default().insert(*e);
                        }
                        if fns {
                            n.fns.entry(f).or_default().insert(*e);
                        }
                    }
                    TermKind::Call {
                        callee: Callee::Fn(g, _),
                        caps,
                        ..
                    } => {
                        n.calls.entry(f).or_default().insert(*g);
                        if let CapArgs::Lexical(env) = caps {
                            edges.push((f, *g, *env));
                        }
                    }
                    _ => {}
                }
            }
        }
        // A callee passes an effect on where the environment of the call
        // does not bind it.
        loop {
            let mut changed = false;
            for &(f, g, env) in &edges {
                if n.unknown.contains(&g) {
                    changed |= n.unknown.insert(f);
                }
                for set in [&mut n.any, &mut n.fns, &mut n.row] {
                    let add: Vec<EffectId> = set
                        .get(&g)
                        .map(|s| {
                            s.iter()
                                .copied()
                                .filter(|&e| !env_binds(p, env, e))
                                .collect()
                        })
                        .unwrap_or_default();
                    let to = set.entry(f).or_default();
                    for e in add {
                        changed |= to.insert(e);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        n
    }

    /// True if function `f` can call itself.
    fn recursive(&self, f: FnId) -> bool {
        let mut seen: BTreeSet<FnId> = BTreeSet::new();
        let mut work: Vec<FnId> = self
            .calls
            .get(&f)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default();
        while let Some(g) = work.pop() {
            if g == f {
                return true;
            }
            if seen.insert(g) {
                work.extend(self.calls.get(&g).into_iter().flatten().copied());
            }
        }
        false
    }
}

/// The place of the capability that serves operation `op` of effect `e`
/// in capability environment `env`, in the terms of the body that adds it,
/// with that body: the capability of a handled body whose handler has a
/// clause for `op`, or the `Cap` field of a closure environment.
fn serving_cap(p: &Program, env: CapEnvId, e: EffectId, op: OpIdx) -> Option<(BodyId, Place)> {
    let mut at = Some(env);
    for _ in 0..=p.cap_envs.len() {
        let id = at?;
        let c = p.cap_envs.get(id.index())?;
        if let Some((_, place)) = c.adds.iter().find(|(x, _)| *x == e) {
            let owner = p.bodies.iter().enumerate().find_map(|(i, b)| {
                let yes = b.cap_env == id
                    && match b.kind {
                        BodyKind::Handled(_) => b.caps.iter().any(|(x, _)| *x == e),
                        BodyKind::Closure(_) => true,
                        _ => false,
                    };
                yes.then(|| (BodyId(u32::try_from(i).unwrap_or(u32::MAX)), b.kind))
            })?;
            match owner.1 {
                BodyKind::Handled(h) => {
                    let has = p
                        .handlers
                        .get(h.index())
                        .is_some_and(|d| d.clauses.iter().any(|(o, _)| *o == op));
                    if has {
                        return Some((owner.0, place.clone()));
                    }
                    // A handler with no clause for the operation passes it on
                    // to the environment around it.
                }
                _ => return Some((owner.0, place.clone())),
            }
        }
        at = c.parent;
    }
    None
}

/// The copies of one program.
struct Inst<'a> {
    bounds: Bounds,
    orig: &'a Program,
    tys: TyTable,
    closure_calls: usize,
    needs: Needs,
    p: Program,
    added: usize,
    calls: usize,
    /// The chain of copied callees of each block that a copy adds.
    blk_chain: HashMap<(BodyId, BlockId), Vec<FnId>>,
    /// The chain of copied callees of each body that a copy adds.
    body_chain: HashMap<BodyId, Vec<FnId>>,
    sites: BTreeMap<(BodyId, BlockId), (BodyId, BlockId, FnId)>,
    body_sites: BTreeMap<BodyId, (BodyId, BlockId, FnId)>,
    /// The mode of stage R0k-c1: only the copies of a closure that resumes
    /// the continuation of its clause ([`instantiate_kont`]).
    kont: bool,
    /// The closures whose one run got a copy of their body in that mode.
    covered: BTreeSet<ClosureId>,
    /// The copy of a closure body whose make goes away gets no `Mention` of
    /// the closure value at its entry (the value is not made).
    skip_mention: bool,
}

/// The maps of one copy.
struct Copy {
    /// The first new local of the site body: local `l` of the callee is
    /// `local_base + l`.
    local_base: u32,
    /// The first new block of the site body: block `k` of the callee is
    /// `block_base + 1 + k`, and `block_base` is the entry of the copy.
    block_base: u32,
    bodies: BTreeMap<BodyId, BodyId>,
    closures: BTreeMap<ClosureId, ClosureId>,
    handlers: BTreeMap<HandlerId, HandlerId>,
    scopes: BTreeMap<ScopeId, ScopeId>,
    spawns: BTreeMap<SpawnId, SpawnId>,
    /// The environment of the call.
    call_env: CapEnvId,
    /// The root environment of the callee.
    root_env: CapEnvId,
    envs: BTreeMap<(CapEnvId, Option<ClosureId>), CapEnvId>,
    /// The closure of the copy that each body of the callee is inside (the
    /// closure itself for a closure body), or `None`.
    ctx: BTreeMap<BodyId, Option<ClosureId>>,
    /// The new `Cap` fields of each closure of the copy.
    extra: BTreeMap<ClosureId, Extra>,
    /// The chain of copied callees of the new code.
    chain: Vec<FnId>,
}

/// The new `Cap` fields of a closure of a copy.
#[derive(Clone, Debug)]
struct Extra {
    /// The body that makes the closure, in the copy.
    maker: BodyId,
    /// The environment of the maker where it makes the closure, in the copy.
    env: CapEnvId,
    /// The effect and the field of each new `Cap` field.
    fields: Vec<(EffectId, weft_ir::FieldIdx)>,
    /// The environment of the closure body in the callee.
    body_env: CapEnvId,
    /// The environment of the closure body in the copy.
    new_env: CapEnvId,
}

/// What a copy copies.
#[derive(Clone, Copy, Debug)]
enum What {
    /// The body of a function item at a call of it.
    Fn(FnId),
    /// The body of a closure at a call of a local that holds it.
    Closure(ClosureId),
}

/// The function whose body is body `b` or a lexical parent of it.
fn fn_of(p: &Program, b: BodyId) -> Option<FnId> {
    let mut at = b;
    for _ in 0..=p.bodies.len() {
        let body = p.body(at)?;
        match body.kind {
            BodyKind::Fn(f) => return Some(f),
            _ => at = body.parent?,
        }
    }
    None
}

/// Why a copy cannot be made: the program keeps the call.
#[derive(Debug)]
struct NoCopy;

/// The map of the places of a copy: each local with `local`, and for the
/// copy of a closure body, a place of its environment `env.k..` with the
/// place of capture `k` in the site (`env`).
#[derive(Clone, Copy)]
struct PlaceMap<'a> {
    local: &'a dyn Fn(LocalId) -> LocalId,
    env: Option<(LocalId, &'a [Place])>,
}

impl<'a> PlaceMap<'a> {
    /// The map of the locals `local`.
    fn new(local: &'a dyn Fn(LocalId) -> LocalId) -> Self {
        Self { local, env: None }
    }

    /// Local `l` in the copy.
    fn l(&self, l: LocalId) -> LocalId {
        (self.local)(l)
    }

    /// Place `pl` in the copy.
    fn place(&self, pl: &Place) -> Place {
        let rest = |proj: &[Proj]| -> Vec<Proj> {
            proj.iter()
                .map(|x| match x {
                    Proj::Index(l) => Proj::Index(self.l(*l)),
                    other => other.clone(),
                })
                .collect()
        };
        if let Some((env, caps)) = self.env {
            if pl.local == env {
                if let Some(Proj::Field(k)) = pl.proj.first() {
                    if let Some(base) = caps.get(k.index()) {
                        let mut out = base.clone();
                        out.proj.extend(rest(pl.proj.get(1..).unwrap_or(&[])));
                        return out;
                    }
                }
            }
        }
        Place {
            local: self.l(pl.local),
            proj: rest(&pl.proj),
        }
    }
}

/// Changes each local of place `pl` with `f`.
fn map_place(pl: &Place, f: &PlaceMap<'_>) -> Place {
    f.place(pl)
}

fn map_operand(o: &Operand, f: &PlaceMap<'_>) -> Operand {
    match o {
        Operand::Copy(p) => Operand::Copy(map_place(p, f)),
        Operand::Move(p) => Operand::Move(map_place(p, f)),
        Operand::Const(c) => Operand::Const(c.clone()),
    }
}

/// The statement `s` with locals `f` and closures `cl`.
fn map_stmt(s: &Stmt, f: &PlaceMap<'_>, cl: &impl Fn(ClosureId) -> ClosureId) -> Stmt {
    let mp = |p: &Place| map_place(p, f);
    let mo = |o: &Operand| map_operand(o, f);
    let kind = match &s.kind {
        StmtKind::Live(l) => StmtKind::Live(f.l(*l)),
        StmtKind::Dead(l) => StmtKind::Dead(f.l(*l)),
        StmtKind::Assign(p, rv) => {
            let rv = match rv {
                Rvalue::Use(o) => Rvalue::Use(mo(o)),
                Rvalue::Ref(q) => Rvalue::Ref(mp(q)),
                Rvalue::Binary(op, t, a, b) => Rvalue::Binary(*op, *t, mo(a), mo(b)),
                Rvalue::Unary(op, t, a) => Rvalue::Unary(*op, *t, mo(a)),
                Rvalue::Aggregate(k, ops) => {
                    let k = match k {
                        weft_ir::AggKind::Closure(c) => weft_ir::AggKind::Closure(cl(*c)),
                        other => other.clone(),
                    };
                    Rvalue::Aggregate(k, ops.iter().map(mo).collect())
                }
                Rvalue::Len(q) => Rvalue::Len(mp(q)),
                Rvalue::Discriminant(q) => Rvalue::Discriminant(mp(q)),
                Rvalue::Concat(ops) => Rvalue::Concat(ops.iter().map(mo).collect()),
                Rvalue::Iter(src) => Rvalue::Iter(match src {
                    weft_ir::IterSource::Elems(q) => weft_ir::IterSource::Elems(mp(q)),
                    weft_ir::IterSource::Range(a, b) => weft_ir::IterSource::Range(mo(a), mo(b)),
                }),
            };
            StmtKind::Assign(mp(p), rv)
        }
        StmtKind::Drop(p) => StmtKind::Drop(mp(p)),
        StmtKind::Consume(p) => StmtKind::Consume(mp(p)),
        StmtKind::Uninit(p) => StmtKind::Uninit(mp(p)),
        StmtKind::Bounds(p, o) => StmtKind::Bounds(mp(p), mo(o)),
        StmtKind::Mention(p) => StmtKind::Mention(mp(p)),
        StmtKind::Print(ops) => StmtKind::Print(ops.iter().map(mo).collect()),
        StmtKind::UnwindValue(p, a) => StmtKind::UnwindValue(mp(p), a.clone()),
        StmtKind::UnwindKont(l) => StmtKind::UnwindKont(f.l(*l)),
    };
    Stmt {
        kind,
        origin: s.origin,
    }
}

impl Inst<'_> {
    /// The chain of copied callees of block `k` of body `b`.
    fn chain(&self, b: BodyId, k: BlockId) -> Vec<FnId> {
        self.blk_chain
            .get(&(b, k))
            .or_else(|| self.body_chain.get(&b))
            .cloned()
            .unwrap_or_default()
    }

    /// The callee of the call at block `k` of body `b` if the call needs a
    /// copy: a local handler serves an operation that the callee performs
    /// through its row with a function value or a reference.
    fn wants(&self, b: BodyId, k: BlockId) -> Option<FnId> {
        let body = self.p.body(b)?;
        let blk = body.block(k)?;
        let TermKind::Call {
            callee: Callee::Fn(f, targs),
            caps: CapArgs::Lexical(env),
            unwind: Some(_),
            ..
        } = &blk.term.kind
        else {
            return None;
        };
        // A generic callee needs a type argument for each type parameter
        // (`can_copy`); the copy substitutes them (`subst_program`).
        let _ = targs;
        let served = self
            .needs
            .any
            .get(f)
            .is_some_and(|s| s.iter().any(|&e| env_binds(&self.p, *env, e)));
        served.then_some(*f)
    }

    /// True if the call of `f` at block `k` of body `b` can get a copy.
    fn can_copy(&self, b: BodyId, k: BlockId, f: FnId) -> bool {
        let Some(d) = self.orig.fns.get(f.index()) else {
            return false;
        };
        let targs = match self
            .p
            .body(b)
            .and_then(|x| x.block(k))
            .map(|x| &x.term.kind)
        {
            Some(TermKind::Call {
                callee: Callee::Fn(_, ts),
                ..
            }) => ts.len(),
            _ => return false,
        };
        if d.generics as usize != targs || d.intrinsic.is_some() || d.body.is_none() {
            return false;
        }
        let chain = self.chain(b, k);
        if chain.len() >= self.bounds.depth || chain.contains(&f) || self.needs.recursive(f) {
            return false;
        }
        let Some(cb) = d.body else { return false };
        let size: usize = std::iter::once(cb)
            .chain(inner_bodies(self.orig, cb))
            .filter_map(|x| self.orig.body(x))
            .map(|x| x.blocks.len())
            .sum();
        self.added + size <= self.bounds.blocks
    }

    /// The local and the closure of a call of a function value at block `k`
    /// of body `b` that can get a copy of the closure body (stage R0k-a2,
    /// the static closure copy): the callee is `copy l` of a local `l` of
    /// `b` that holds one closure that `b` makes, and the closure performs
    /// an operation with a function value or a reference through a captured
    /// capability, or calls a callee that performs one through its row.
    ///
    /// The copy is refused (the call keeps the summary of the closure) for
    /// another way to give `l` a value, a `move` or a borrow of `l`, a `once`
    /// closure, a `ByMove` or a `Kont` capture, a source of a `Kept` or a
    /// `ByRef` capture that ends or gets a new cell between the closure and
    /// the call, a use of the whole environment in the closure body, and a
    /// body inside the closure that names the environment.
    fn closure_copy(&self, b: BodyId, k: BlockId) -> Option<(LocalId, ClosureId)> {
        let body = self.p.body(b)?;
        let TermKind::Call {
            callee: Callee::Value(Operand::Copy(callee)),
            caps: CapArgs::Lexical(_),
            unwind: Some(_),
            ..
        } = &body.block(k)?.term.kind
        else {
            return None;
        };
        if !callee.is_local() {
            return None;
        }
        let l = callee.local;
        // The one value of `l`: a closure that the body makes, or a copy of
        // a local with such a value (the callee temporary of a call).
        let (mut at, mut found) = (l, None);
        for _ in 0..8 {
            // A body inside `b` (a clause, a handled body, a scope body, a
            // closure, and each body inside them) can write the cell of the
            // local through an upvar or a capture: then the local can hold
            // another value at the run (the review of R0k-a2: `u03` to `u10`).
            if nested_writes(&self.p, b, at) {
                return None;
            }
            match single_value(body, at)? {
                One::Closure(blk, si, c) => {
                    found = Some((blk, si, c));
                    break;
                }
                One::Copy(next) => at = next,
            }
        }
        let (mb, mi, cid) = found?;
        let decl = self.p.closures.get(cid.index())?;
        if decl.maker != b || decl.once {
            return None;
        }
        let cb = self.p.body(decl.body)?;
        let env = *cb.params.first()?;
        // The captures.
        let (fwd, bwd) = (reach(body, mb, true), reach(body, k, false));
        for cap in &decl.captures {
            match cap.mode {
                weft_ir::CaptureMode::Cap => {}
                weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef => {
                    if cap.source.has_deref() {
                        return None;
                    }
                    let src = cap.source.local;
                    if matches!(body.local_kind(src)?, LocalKind::Upvar(_)) {
                        continue;
                    }
                    for (bi, blk) in body.blocks.iter().enumerate() {
                        if !(fwd.get(bi).copied().unwrap_or(false)
                            && bwd.get(bi).copied().unwrap_or(false))
                        {
                            continue;
                        }
                        for (si, st) in blk.stmts.iter().enumerate() {
                            if bi == mb.index() && si <= mi {
                                continue;
                            }
                            if matches!(st.kind, StmtKind::Dead(x) | StmtKind::Live(x) if x == src)
                            {
                                return None;
                            }
                        }
                    }
                }
                weft_ir::CaptureMode::ByMove | weft_ir::CaptureMode::Kont => return None,
            }
        }
        // The environment: only its fields.
        let inner = inner_bodies(&self.p, decl.body);
        if !body_places(cb)
            .iter()
            .all(|q| q.local != env || matches!(q.proj.first(), Some(Proj::Field(_))))
        {
            return None;
        }
        for &ib in &inner {
            let x = self.p.body(ib)?;
            if x.parent == Some(decl.body)
                && x.locals.iter().any(|d| d.kind == LocalKind::Upvar(env))
            {
                return None;
            }
        }
        // The closure performs a served operation with a function value or a
        // reference, or calls a callee that performs one.
        let mut served = false;
        for x in std::iter::once(decl.body).chain(inner.iter().copied()) {
            let Some(xb) = self.p.body(x) else { continue };
            for blk in &xb.blocks {
                match &blk.term.kind {
                    TermKind::Perform {
                        cap: CapOperand::Local(q),
                        op,
                        ..
                    } => {
                        if let Some(e) = weft_ir::print::cap_effect(&self.p, &self.tys, xb, q) {
                            served |= risky_op(&self.tys, e, *op).0;
                        }
                    }
                    TermKind::Call {
                        callee: Callee::Fn(g, _),
                        caps: CapArgs::Lexical(e),
                        ..
                    } => {
                        served |= self
                            .needs
                            .any
                            .get(g)
                            .is_some_and(|s| s.iter().any(|&x| env_binds(&self.p, *e, x)));
                    }
                    _ => {}
                }
            }
        }
        let size: usize = std::iter::once(decl.body)
            .chain(inner)
            .filter_map(|x| self.p.body(x))
            .map(|x| x.blocks.len())
            .sum();
        (served && self.added + size <= self.bounds.blocks).then_some((l, cid))
    }

    /// The callee of the call at block `k` of body `b` that gets a copy in
    /// the mode of [`instantiate_kont`] (D1c): `b` is a clause, and an
    /// argument is a whole local that holds a closure that `b` makes and that
    /// captures the continuation of `b` ([`kont_closure`]).
    fn kont_wants(&self, b: BodyId, k: BlockId) -> Option<FnId> {
        let body = self.p.body(b)?;
        if !matches!(body.kind, BodyKind::Clause(..)) {
            return None;
        }
        let TermKind::Call {
            callee: Callee::Fn(f, _),
            args,
            caps: CapArgs::Lexical(_),
            unwind: Some(_),
            ..
        } = &body.block(k)?.term.kind
        else {
            return None;
        };
        args.iter()
            .filter_map(|a| a.place().filter(|q| q.is_local()).map(|q| q.local))
            .any(|l| kont_closure(&self.p, b, l).is_some())
            .then_some(*f)
    }

    /// The copy of stage R0k-c1 at block `k` of body `b` (D1a, and D1c in the
    /// copy of a callee): the call runs a closure that clause `b` makes and
    /// that captures the continuation of `b`. Each condition is a hard rule
    /// (`docs/ir.md` 6.1, "As built (plan stage R0k-c1)"); if one fails, the
    /// call keeps the summary of the closure and the program its fallback.
    ///
    /// - The run is a call of a function value `copy l` or `move l`.
    /// - The value goes from the make to `l` along a chain of whole locals
    ///   (`x = move y` or `x = copy y`): no field, no container, no
    ///   reference. Each local of the chain has one write, and one read
    ///   (the next step of the chain or the run) besides `Live`, `Dead` and
    ///   the drops of the cleanup blocks; no body inside `b` names it.
    /// - The closure is made by `b`, captures the `Kont` local of `b` and no
    ///   value `ByMove`, and its body uses only fields of its environment.
    /// - The `Kont` local appears after the make only in `Dead` and
    ///   `UnwindKont`, in no other statement or terminator, and no body
    ///   inside `b` names it.
    /// - Each path of the CFG from the make reaches the run, with no cycle,
    ///   through blocks whose terminators are `Goto` or `Switch` (no unwind
    ///   edge, no abort edge, no perform), and with no statement but `Live`
    ///   and `Dead` of other locals and the steps of the chain.
    ///
    /// A `once` continuation (a `move` capture) moves into the closure value:
    /// the copy resumes the `Kont` local, so the make and the steps of the
    /// chain go ([`KontPlan::removals`]). A `multi` continuation (a `copy`
    /// capture) keeps the make, and the copy reads the source, as in R0k-a2.
    fn kont_copy(&self, b: BodyId, k: BlockId) -> Option<KontPlan> {
        let body = self.p.body(b)?;
        if !matches!(body.kind, BodyKind::Clause(..)) {
            return None;
        }
        let TermKind::Call {
            callee: Callee::Value(op),
            caps: CapArgs::Lexical(_),
            unwind: Some(_),
            ..
        } = &body.block(k)?.term.kind
        else {
            return None;
        };
        let q = op.place()?;
        if !q.is_local() {
            return None;
        }
        let ch = kont_closure(&self.p, b, q.local)?;
        // The run is the one read of the last local of the chain.
        if !ch
            .locals
            .iter()
            .all(|&l| local_reads(body, l) == 1 && !nested_uses(&self.p, b, l))
        {
            return None;
        }
        let decl = self.p.closures.get(ch.closure.index())?;
        if nested_uses(&self.p, b, ch.kont) || kont_uses_after(body, ch.kont, ch.make) {
            return None;
        }
        // The captures: one `Kont` capture of the continuation, and `Kept`,
        // `ByRef` and `Cap` captures (as R0k-a2).
        for cap in &decl.captures {
            match cap.mode {
                weft_ir::CaptureMode::Kont | weft_ir::CaptureMode::Cap => {}
                weft_ir::CaptureMode::Kept | weft_ir::CaptureMode::ByRef => {
                    if cap.source.has_deref() {
                        return None;
                    }
                }
                weft_ir::CaptureMode::ByMove => return None,
            }
        }
        // The path from the make to the run.
        let mut sources: BTreeSet<LocalId> = decl.captures.iter().map(|c| c.source.local).collect();
        sources.insert(ch.kont);
        if !kont_region_ok(body, ch.make, k, &ch.steps, &sources) {
            return None;
        }
        // The body of the closure: only fields of its environment, and no
        // body inside it names the environment (as R0k-a2).
        let cb = self.p.body(decl.body)?;
        let env = *cb.params.first()?;
        if !body_places(cb)
            .iter()
            .all(|x| x.local != env || matches!(x.proj.first(), Some(Proj::Field(_))))
        {
            return None;
        }
        let inner = inner_bodies(&self.p, decl.body);
        for &ib in &inner {
            let x = self.p.body(ib)?;
            if x.parent == Some(decl.body)
                && x.locals.iter().any(|d| d.kind == LocalKind::Upvar(env))
            {
                return None;
            }
        }
        let size: usize = std::iter::once(decl.body)
            .chain(inner)
            .filter_map(|x| self.p.body(x))
            .map(|x| x.blocks.len())
            .sum();
        if self.added + size > self.bounds.blocks {
            return None;
        }
        let removals = if ch.once {
            std::iter::once(ch.make)
                .chain(ch.steps.iter().copied())
                .collect()
        } else {
            Vec::new()
        };
        Some(KontPlan {
            closure: ch.closure,
            removals,
        })
    }

    /// Removes the statements `at` (block, index) of body `b`: the make of a
    /// closure with a `once` continuation and the steps of its chain
    /// ([`KontPlan::removals`]).
    fn remove_make(&mut self, b: BodyId, at: &[(BlockId, usize)]) {
        let Some(body) = self.p.bodies.get_mut(b.index()) else {
            return;
        };
        let mut sorted = at.to_vec();
        sorted.sort_by_key(|y| std::cmp::Reverse((y.0, y.1)));
        for (blk, si) in sorted {
            if let Some(x) = body.blocks.get_mut(blk.index()) {
                if si < x.stmts.len() {
                    x.stmts.remove(si);
                }
            }
        }
    }

    /// The environment `e` of the callee, in the copy, for a body inside
    /// closure `ctx` of the copy: the root environment of the callee is the
    /// environment of the call, and the environment of the closure body is
    /// its new environment.
    fn env(&mut self, c: &mut Copy, e: CapEnvId, ctx: Option<ClosureId>) -> CapEnvId {
        if let Some(x) = ctx.and_then(|k| c.extra.get(&k)) {
            if e == x.body_env {
                return x.new_env;
            }
        }
        if e == c.root_env {
            return c.call_env;
        }
        if let Some(&x) = c.envs.get(&(e, ctx)) {
            return x;
        }
        let Some(old) = self.p.cap_envs.get(e.index()).cloned() else {
            return e;
        };
        let parent = old.parent.map(|q| self.env(c, q, ctx));
        let id = CapEnvId(u32::try_from(self.p.cap_envs.len()).unwrap_or(u32::MAX));
        self.p.cap_envs.push(CapEnv {
            parent,
            adds: old.adds,
        });
        c.envs.insert((e, ctx), id);
        id
    }

    /// The place in body `x` of the capability that serves operation `op`
    /// of effect `e` in environment `env`.
    fn cap_place(
        &mut self,
        x: BodyId,
        env: CapEnvId,
        e: EffectId,
        op: OpIdx,
    ) -> Result<Place, NoCopy> {
        let (owner, place) = serving_cap(&self.p, env, e, op).ok_or(NoCopy)?;
        self.upvar_chain(x, owner, place)
    }

    /// Place `place` of body `owner` in body `x`, a body inside it: an
    /// upvar local in each body on the way.
    fn upvar_chain(&mut self, x: BodyId, owner: BodyId, place: Place) -> Result<Place, NoCopy> {
        // The bodies from `x` up to `owner`.
        let mut path: Vec<BodyId> = vec![x];
        let mut at = x;
        while at != owner {
            let parent = self.p.body(at).and_then(|b| b.parent).ok_or(NoCopy)?;
            path.push(parent);
            at = parent;
            if path.len() > self.p.bodies.len() {
                return Err(NoCopy);
            }
        }
        // From the owner down: the local in each body.
        let mut local = place.local;
        for w in path.iter().rev().skip(1) {
            let parent = self.p.body(*w).and_then(|b| b.parent).ok_or(NoCopy)?;
            let body = self.p.body(*w).ok_or(NoCopy)?;
            if !body.kind.has_upvars() {
                return Err(NoCopy);
            }
            let found = body
                .locals
                .iter()
                .position(|d| d.kind == LocalKind::Upvar(local));
            local = if let Some(i) = found {
                LocalId(u32::try_from(i).unwrap_or(u32::MAX))
            } else {
                let decl = self
                    .p
                    .body(parent)
                    .and_then(|b| b.local(local))
                    .cloned()
                    .ok_or(NoCopy)?;
                let b = self.p.bodies.get_mut(w.index()).ok_or(NoCopy)?;
                let id = LocalId(u32::try_from(b.locals.len()).unwrap_or(u32::MAX));
                b.locals.push(LocalDecl {
                    kind: LocalKind::Upvar(local),
                    in_place: false,
                    ..decl
                });
                id
            };
        }
        Ok(Place {
            local,
            proj: place.proj,
        })
    }

    /// The terminator `t` of the copy in body `x`: the blocks with `blk`,
    /// the locals with `f`, and a perform
    /// through the row that environment `env` serves goes to its capability.
    fn map_term(
        &mut self,
        c: &mut Copy,
        x: BodyId,
        t: &TermKind,
        f: &PlaceMap<'_>,
        blk: &impl Fn(BlockId) -> BlockId,
        (env, ctx): (CapEnvId, Option<ClosureId>),
    ) -> Result<TermKind, NoCopy> {
        let mp = |p: &Place| map_place(p, f);
        let mo = |o: &Operand| map_operand(o, f);
        let mu = |u: &Option<BlockId>| u.map(blk);
        Ok(match t {
            TermKind::Goto(b) => TermKind::Goto(blk(*b)),
            TermKind::Switch {
                on,
                arms,
                otherwise,
            } => TermKind::Switch {
                on: mo(on),
                arms: arms.iter().map(|(v, b)| (*v, blk(*b))).collect(),
                otherwise: blk(*otherwise),
            },
            TermKind::Return => TermKind::Return,
            TermKind::UnwindExit => TermKind::UnwindExit,
            TermKind::Unreachable => TermKind::Unreachable,
            TermKind::Call {
                callee,
                args,
                dest,
                caps,
                next,
                unwind,
            } => TermKind::Call {
                callee: match callee {
                    Callee::Fn(g, ts) => Callee::Fn(*g, ts.clone()),
                    Callee::Value(o) => Callee::Value(mo(o)),
                },
                args: args.iter().map(mo).collect(),
                dest: mp(dest),
                caps: match caps {
                    CapArgs::Lexical(e) => CapArgs::Lexical(self.env(c, *e, ctx)),
                    CapArgs::Root => CapArgs::Root,
                },
                next: next.map(blk),
                unwind: mu(unwind),
            },
            TermKind::Perform {
                cap,
                op,
                args,
                dest,
                next,
                unwind,
            } => {
                let cap = match cap {
                    CapOperand::Row(e) if env_binds(&self.p, env, *e) => {
                        CapOperand::Local(self.cap_place(x, env, *e, *op)?)
                    }
                    CapOperand::Row(e) => CapOperand::Row(*e),
                    CapOperand::Local(q) => CapOperand::Local(mp(q)),
                };
                TermKind::Perform {
                    cap,
                    op: *op,
                    args: args.iter().map(mo).collect(),
                    dest: mp(dest),
                    next: blk(*next),
                    unwind: mu(unwind),
                }
            }
            TermKind::Resume {
                kont,
                arg,
                dest,
                next,
                unwind,
            } => TermKind::Resume {
                kont: mp(kont),
                arg: mo(arg),
                dest: mp(dest),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::Handle {
                handler,
                dest,
                next,
                unwind,
            } => TermKind::Handle {
                handler: c.handlers.get(handler).copied().ok_or(NoCopy)?,
                dest: mp(dest),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::Scope {
                scope,
                dest,
                next,
                unwind,
            } => TermKind::Scope {
                scope: c.scopes.get(scope).copied().ok_or(NoCopy)?,
                dest: mp(dest),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::ScopeWait {
                scope,
                orphans,
                next,
                unwind,
            } => TermKind::ScopeWait {
                scope: mp(scope),
                orphans: orphans.iter().map(|l| f.l(*l)).collect(),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::Spawn {
                site,
                scope,
                task,
                dest,
                next,
            } => TermKind::Spawn {
                site: c.spawns.get(site).copied().ok_or(NoCopy)?,
                scope: mo(scope),
                task: mo(task),
                dest: dest.as_ref().map(mp),
                next: blk(*next),
            },
            TermKind::Join {
                task,
                dest,
                next,
                unwind,
            } => TermKind::Join {
                task: mo(task),
                dest: mp(dest),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::Detach { task, next } => TermKind::Detach {
                task: mo(task),
                next: blk(*next),
            },
            TermKind::Fork {
                sites,
                branches,
                dest,
                next,
                unwind,
            } => TermKind::Fork {
                sites: sites
                    .iter()
                    .map(|s| c.spawns.get(s).copied().ok_or(NoCopy))
                    .collect::<Result<_, _>>()?,
                branches: branches.iter().map(mo).collect(),
                dest: mp(dest),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::Assert { cond, next, unwind } => TermKind::Assert {
                cond: mo(cond),
                next: blk(*next),
                unwind: mu(unwind),
            },
            TermKind::IterNext {
                iter,
                dest,
                next,
                done,
            } => TermKind::IterNext {
                iter: mp(iter),
                dest: mp(dest),
                next: blk(*next),
                done: blk(*done),
            },
        })
    }

    /// The kind of local `d` of a body of the copy.
    fn map_local(c: &Copy, d: &LocalDecl, upvar: &impl Fn(LocalId) -> LocalId) -> LocalDecl {
        let kind = match d.kind {
            LocalKind::Upvar(l) => LocalKind::Upvar(upvar(l)),
            LocalKind::TaskResult(s) => {
                LocalKind::TaskResult(c.spawns.get(&s).copied().unwrap_or(s))
            }
            k => k,
        };
        LocalDecl { kind, ..d.clone() }
    }

    /// Copies the callee of the call at block `k` of body `b` into `b`.
    fn copy(&mut self, b: BodyId, k: BlockId, what: What) -> Result<(), NoCopy> {
        match what {
            What::Fn(f) => {
                let ts = match self
                    .p
                    .body(b)
                    .and_then(|x| x.block(k))
                    .map(|x| &x.term.kind)
                {
                    Some(TermKind::Call {
                        callee: Callee::Fn(_, ts),
                        ..
                    }) => ts.clone(),
                    _ => return Err(NoCopy),
                };
                if ts.is_empty() {
                    let orig = self.orig;
                    self.copy_code(orig, b, k, what)
                } else {
                    // A generic callee: its body with the type arguments of the
                    // call (stage R0k-a2, `fixes/r0k/c09`).
                    let snap = subst_program(self.orig, &mut self.tys, f, &ts)?;
                    self.copy_code(&snap, b, k, what)
                }
            }
            What::Closure(_) => {
                let snap = self.p.clone();
                self.copy_code(&snap, b, k, what)
            }
        }
    }

    fn copy_code(
        &mut self,
        orig: &Program,
        b: BodyId,
        k: BlockId,
        what: What,
    ) -> Result<(), NoCopy> {
        let (cb, callee) = match what {
            What::Fn(f) => (
                orig.fns.get(f.index()).and_then(|d| d.body).ok_or(NoCopy)?,
                f,
            ),
            What::Closure(cid) => {
                let cb = orig.closures.get(cid.index()).ok_or(NoCopy)?.body;
                (cb, fn_of(orig, cb).ok_or(NoCopy)?)
            }
        };
        let cbody = orig.body(cb).ok_or(NoCopy)?.clone();
        // The environment of a closure body: its capability environment is
        // the one where the closure is made, in the site.
        let closure = match what {
            What::Closure(cid) => orig.closures.get(cid.index()).cloned(),
            What::Fn(_) => None,
        };
        let site = self.p.body(b).ok_or(NoCopy)?;
        let call = site.block(k).ok_or(NoCopy)?.term.clone();
        let TermKind::Call {
            args,
            dest,
            caps: CapArgs::Lexical(call_env),
            next,
            unwind: Some(unwind),
            ..
        } = call.kind.clone()
        else {
            return Err(NoCopy);
        };
        let call_env = closure.as_ref().map_or(call_env, |d| d.cap_env);
        let inner = inner_bodies(orig, cb);
        let mut chain = self.chain(b, k);
        if matches!(what, What::Fn(_)) {
            chain.push(callee);
        }
        let mut c = Copy {
            local_base: u32::try_from(site.locals.len()).map_err(|_| NoCopy)?,
            block_base: u32::try_from(site.blocks.len()).map_err(|_| NoCopy)?,
            bodies: BTreeMap::new(),
            closures: BTreeMap::new(),
            handlers: BTreeMap::new(),
            scopes: BTreeMap::new(),
            spawns: BTreeMap::new(),
            call_env,
            root_env: cbody.cap_env,
            envs: BTreeMap::new(),
            ctx: BTreeMap::new(),
            extra: BTreeMap::new(),
            chain,
        };
        // The new ids of the bodies and the declarations inside the callee.
        let first = self.p.bodies.len();
        for (i, &ib) in inner.iter().enumerate() {
            c.bodies
                .insert(ib, BodyId(u32::try_from(first + i).map_err(|_| NoCopy)?));
        }
        for (ci, d) in orig.closures.iter().enumerate() {
            if c.bodies.contains_key(&d.body) {
                let id = ClosureId(u32::try_from(self.p.closures.len()).map_err(|_| NoCopy)?);
                c.closures
                    .insert(ClosureId(u32::try_from(ci).map_err(|_| NoCopy)?), id);
                self.p.closures.push(d.clone());
            }
        }
        for &ib in &inner {
            let own = orig
                .closure_of(ib)
                .and_then(|(x, _)| c.closures.get(&x).copied());
            let up = orig
                .body(ib)
                .and_then(|x| x.parent)
                .and_then(|q| c.ctx.get(&q).copied())
                .flatten();
            c.ctx.insert(ib, own.or(up));
        }
        c.ctx.insert(cb, None);
        for (hi, d) in orig.handlers.iter().enumerate() {
            if c.bodies.contains_key(&d.handled) {
                let id = HandlerId(u32::try_from(self.p.handlers.len()).map_err(|_| NoCopy)?);
                c.handlers
                    .insert(HandlerId(u32::try_from(hi).map_err(|_| NoCopy)?), id);
                self.p.handlers.push(d.clone());
            }
        }
        for (si, d) in orig.scopes.iter().enumerate() {
            if c.bodies.contains_key(&d.body) {
                let id = ScopeId(u32::try_from(self.p.scopes.len()).map_err(|_| NoCopy)?);
                c.scopes
                    .insert(ScopeId(u32::try_from(si).map_err(|_| NoCopy)?), id);
                self.p.scopes.push(d.clone());
            }
        }
        // The spawn sites of the callee and of its bodies.
        let mut sites: BTreeSet<SpawnId> = BTreeSet::new();
        for x in std::iter::once(&cbody).chain(inner.iter().filter_map(|&x| orig.body(x))) {
            for blk in &x.blocks {
                match &blk.term.kind {
                    TermKind::Spawn { site, .. } => {
                        sites.insert(*site);
                    }
                    TermKind::Fork { sites: s, .. } => sites.extend(s.iter().copied()),
                    _ => {}
                }
            }
            for d in &x.locals {
                if let LocalKind::TaskResult(s) = d.kind {
                    sites.insert(s);
                }
            }
        }
        for s in sites {
            let mut d = orig.spawns.get(s.index()).cloned().ok_or(NoCopy)?;
            d.scope = d.scope.map(|q| c.scopes.get(&q).copied().unwrap_or(q));
            let id = SpawnId(u32::try_from(self.p.spawns.len()).map_err(|_| NoCopy)?);
            c.spawns.insert(s, id);
            self.p.spawns.push(d);
        }
        let body_map = c.bodies.clone();
        let bm = move |x: BodyId| -> BodyId {
            if x == cb {
                b
            } else {
                body_map.get(&x).copied().unwrap_or(x)
            }
        };
        // The new locals of the site go in first: an upvar local that a
        // perform of the copy needs comes after them.
        let base = c.local_base;
        let fl = move |l: LocalId| LocalId(base + l.0);
        let mut new_locals: Vec<LocalDecl> = Vec::new();
        for d in &cbody.locals {
            let mut nd = Self::map_local(&c, d, &fl);
            nd.kind = match d.kind {
                LocalKind::Return => LocalKind::Temp(TempKind::Value),
                LocalKind::Param(_) | LocalKind::Env => LocalKind::User,
                _ => nd.kind,
            };
            new_locals.push(nd);
        }
        // The places of the captures of a closure in the site: the source of
        // a `Kept` capture (the closure shares the cell of the variable), a
        // new reference to the source of a `ByRef` capture, the capability of
        // a `Cap` capture (`closure_copyable` refuses the other modes).
        let mut env_places: Vec<Place> = Vec::new();
        let mut borrows: Vec<(LocalId, Place)> = Vec::new();
        if let Some(d) = &closure {
            let mut next_local = base + u32::try_from(new_locals.len()).map_err(|_| NoCopy)?;
            for cap in &d.captures {
                match cap.mode {
                    // A `Kont` capture (stage R0k-c1, only in the mode of
                    // `instantiate_kont`): the continuation of the clause.
                    weft_ir::CaptureMode::Kept
                    | weft_ir::CaptureMode::Cap
                    | weft_ir::CaptureMode::Kont => {
                        env_places.push(cap.source.clone());
                    }
                    weft_ir::CaptureMode::ByRef => {
                        let t =
                            crate::factgen::alpha::place_ty(&self.p, &mut self.tys, b, &cap.source)
                                .ok_or(NoCopy)?;
                        let rt = self.tys.intern(weft_ir::Ty::Ref(t));
                        let origin = self
                            .p
                            .body(b)
                            .and_then(|x| x.block(k))
                            .map(|x| x.term.origin)
                            .unwrap_or_default();
                        new_locals.push(LocalDecl {
                            ty: rt,
                            kind: LocalKind::User,
                            name: None,
                            props: crate::props::ir_props(&self.tys, rt),
                            in_place: false,
                            origin,
                        });
                        let l = LocalId(next_local);
                        next_local += 1;
                        borrows.push((l, cap.source.clone()));
                        env_places.push(Place::local(l));
                    }
                    weft_ir::CaptureMode::ByMove => return Err(NoCopy),
                }
            }
        }
        let env_local = closure.as_ref().and_then(|_| cbody.params.first().copied());
        let pm = PlaceMap {
            local: &fl,
            env: env_local.map(|e| (e, env_places.as_slice())),
        };
        self.p
            .bodies
            .get_mut(b.index())
            .ok_or(NoCopy)?
            .locals
            .extend(new_locals);
        // The declarations of the copy name the new bodies. A closure of the
        // callee performs through the capabilities of the point where it is
        // made: in the copy, it gets a `Cap` field for each effect that the
        // environment of the call serves and that its code can use.
        let mut pairs: Vec<(ClosureId, ClosureId)> =
            c.closures.iter().map(|(x, y)| (*x, *y)).collect();
        pairs.sort_by_key(|(x, _)| orig.closures.get(x.index()).map(|d| d.body));
        for (old, new) in pairs {
            let d = orig.closures.get(old.index()).ok_or(NoCopy)?.clone();
            let captures: Vec<weft_ir::Capture> = d
                .captures
                .iter()
                .map(|cap| weft_ir::Capture {
                    source: if d.maker == cb {
                        map_place(&cap.source, &pm)
                    } else {
                        cap.source.clone()
                    },
                    mode: cap.mode,
                })
                .collect();
            let maker_ctx = c.ctx.get(&d.maker).copied().flatten();
            let maker_env = self.env(&mut c, d.cap_env, maker_ctx);
            let used = self.closure_uses(orig, d.body);
            let own: Vec<(EffectId, Place)> = orig
                .body(d.body)
                .filter(|x| x.cap_env != d.cap_env)
                .and_then(|x| orig.cap_envs.get(x.cap_env.index()))
                .map(|e| e.adds.clone())
                .unwrap_or_default();
            let extra: Vec<EffectId> = used
                .into_iter()
                .filter(|&e| !own.iter().any(|(x, _)| *x == e) && env_binds(&self.p, maker_env, e))
                .collect();
            let nd = self.p.closures.get_mut(new.index()).ok_or(NoCopy)?;
            nd.body = bm(d.body);
            nd.maker = bm(d.maker);
            let first_field = captures.len();
            nd.captures = captures;
            nd.cap_env = maker_env;
            let mut fields = Vec::new();
            for (i, e) in extra.into_iter().enumerate() {
                let field = weft_ir::FieldIdx(u32::try_from(first_field + i).map_err(|_| NoCopy)?);
                fields.push((e, field));
            }
            let ob = orig.body(d.body).ok_or(NoCopy)?;
            let new_env = self.closure_env(ob, maker_env, own, &fields)?;
            c.extra.insert(
                new,
                Extra {
                    maker: bm(d.maker),
                    env: maker_env,
                    fields,
                    body_env: ob.cap_env,
                    new_env,
                },
            );
        }
        // The maker body of a closure that a body of the copy makes goes into
        // the program below; the site is there now.
        self.add_cap_sources(&c, b)?;
        for (&old, &new) in &c.handlers {
            let d = orig.handlers.get(old.index()).ok_or(NoCopy)?;
            let nd = self.p.handlers.get_mut(new.index()).ok_or(NoCopy)?;
            nd.handled = bm(d.handled);
            nd.site = bm(d.site);
            nd.clauses = d.clauses.iter().map(|&(o, x)| (o, bm(x))).collect();
        }
        for (&old, &new) in &c.scopes {
            let d = orig.scopes.get(old.index()).ok_or(NoCopy)?;
            let nd = self.p.scopes.get_mut(new.index()).ok_or(NoCopy)?;
            nd.body = bm(d.body);
            nd.site = bm(d.site);
        }
        // The blocks of the copy.
        let bb = c.block_base;
        let fb = move |x: BlockId| BlockId(bb + 1 + x.0);
        let origin = call.origin;
        let mut entry_stmts: Vec<Stmt> = Vec::new();
        for &(l, ref q) in &borrows {
            entry_stmts.push(Stmt {
                kind: StmtKind::Live(l),
                origin,
            });
            entry_stmts.push(Stmt {
                kind: StmtKind::Assign(Place::local(l), Rvalue::Ref(q.clone())),
                origin,
            });
        }
        // The run of a closure uses the closure value: its references (a
        // `ByRef` capture) are live up to the run, as before the copy.
        if let (Some(_), Some(q), false) =
            (&closure, call_value_place(&call.kind), self.skip_mention)
        {
            entry_stmts.push(Stmt {
                kind: StmtKind::Mention(q),
                origin,
            });
        }
        let skip = usize::from(closure.is_some());
        if cbody.params.len() != args.len() + skip {
            return Err(NoCopy);
        }
        for (i, &pl) in cbody.params.iter().enumerate().skip(skip) {
            let arg = args.get(i - skip).cloned().ok_or(NoCopy)?;
            entry_stmts.push(Stmt {
                kind: StmtKind::Live(fl(pl)),
                origin,
            });
            entry_stmts.push(Stmt {
                kind: StmtKind::Assign(Place::local(fl(pl)), Rvalue::Use(arg)),
                origin,
            });
        }
        entry_stmts.push(Stmt {
            kind: StmtKind::Live(fl(cbody.ret)),
            origin,
        });
        let mut blocks: Vec<weft_ir::Block> = vec![weft_ir::Block {
            stmts: entry_stmts,
            term: Term {
                kind: TermKind::Goto(fb(cbody.entry)),
                origin,
            },
            cleanup: false,
        }];
        let closures_map = c.closures.clone();
        let clm = move |x: ClosureId| closures_map.get(&x).copied().unwrap_or(x);
        for blk in &cbody.blocks {
            let mut stmts: Vec<Stmt> = Vec::new();
            for st in &blk.stmts {
                stmts.push(self.copy_stmt(&c, st, &pm, &clm)?);
            }
            let ends: Vec<Stmt> = borrows
                .iter()
                .map(|&(l, _)| Stmt {
                    kind: StmtKind::Dead(l),
                    origin,
                })
                .collect();
            let term = match &blk.term.kind {
                TermKind::Return => match &next {
                    Some(n) => {
                        stmts.push(Stmt {
                            kind: StmtKind::Assign(
                                dest.clone(),
                                Rvalue::Use(Operand::Move(Place::local(fl(cbody.ret)))),
                            ),
                            origin,
                        });
                        stmts.push(Stmt {
                            kind: StmtKind::Dead(fl(cbody.ret)),
                            origin: blk.term.origin,
                        });
                        stmts.extend(ends.iter().cloned());
                        TermKind::Goto(*n)
                    }
                    None => TermKind::Unreachable,
                },
                TermKind::UnwindExit => {
                    stmts.extend(ends.iter().cloned());
                    TermKind::Goto(unwind)
                }
                t => self.map_term(&mut c, b, t, &pm, &fb, (call_env, None))?,
            };
            blocks.push(weft_ir::Block {
                stmts,
                term: Term {
                    kind: term,
                    origin: blk.term.origin,
                },
                cleanup: blk.cleanup,
            });
        }
        // The bodies inside the callee.
        for &ib in &inner {
            let ob = orig.body(ib).ok_or(NoCopy)?.clone();
            let nid = bm(ib);
            let parent_is_callee = ob.parent == Some(cb);
            let up = move |l: LocalId| {
                if parent_is_callee {
                    LocalId(base + l.0)
                } else {
                    l
                }
            };
            let locals: Vec<LocalDecl> = ob
                .locals
                .iter()
                .map(|d| Self::map_local(&c, d, &up))
                .collect();
            let kind = match ob.kind {
                BodyKind::Closure(x) => BodyKind::Closure(clm(x)),
                BodyKind::Clause(h, o) => {
                    BodyKind::Clause(c.handlers.get(&h).copied().ok_or(NoCopy)?, o)
                }
                BodyKind::Handled(h) => {
                    BodyKind::Handled(c.handlers.get(&h).copied().ok_or(NoCopy)?)
                }
                BodyKind::Scope(s) => BodyKind::Scope(c.scopes.get(&s).copied().ok_or(NoCopy)?),
                k => k,
            };
            let ctx = c.ctx.get(&ib).copied().flatten();
            let env = self.env(&mut c, ob.cap_env, ctx);
            // The new body goes into the program first, so that a perform in it
            // can add the upvar locals of the capability.
            if self.p.bodies.len() != nid.index() {
                return Err(NoCopy);
            }
            self.p.bodies.push(Body {
                kind,
                parent: ob.parent.map(&bm),
                locals,
                blocks: Vec::new(),
                cap_env: env,
                ..ob.clone()
            });
            // The `Cap` captures of the closures that this body makes.
            self.add_cap_sources(&c, nid)?;
            let same_l = |l: LocalId| l;
            let same = PlaceMap::new(&same_l);
            let id = |x: BlockId| x;
            let mut nblocks = Vec::new();
            for blk in &ob.blocks {
                let mut stmts = Vec::new();
                for st in &blk.stmts {
                    stmts.push(self.copy_stmt(&c, st, &same, &clm)?);
                }
                let term = self.map_term(&mut c, nid, &blk.term.kind, &same, &id, (env, ctx))?;
                nblocks.push(weft_ir::Block {
                    stmts,
                    term: Term {
                        kind: term,
                        origin: blk.term.origin,
                    },
                    cleanup: blk.cleanup,
                });
            }
            if let Some(x) = self.p.bodies.get_mut(nid.index()) {
                x.blocks = nblocks;
            }
        }
        // The code goes into the site.
        let nblocks = blocks.len();
        let site = self.p.bodies.get_mut(b.index()).ok_or(NoCopy)?;
        let entry = BlockId(c.block_base);
        if let Some(blk) = site.blocks.get_mut(k.index()) {
            blk.term.kind = TermKind::Goto(entry);
        }
        site.blocks.extend(blocks);
        for i in 0..nblocks {
            let id = BlockId(c.block_base + u32::try_from(i).unwrap_or(u32::MAX));
            self.blk_chain.insert((b, id), c.chain.clone());
            self.sites.insert((b, id), (b, k, callee));
        }
        for &nid in c.bodies.values() {
            self.body_chain.insert(nid, c.chain.clone());
            self.body_sites.insert(nid, (b, k, callee));
        }
        self.added += nblocks
            + inner
                .iter()
                .filter_map(|&x| orig.body(x))
                .map(|x| x.blocks.len())
                .sum::<usize>();
        if matches!(what, What::Fn(_)) {
            self.calls += 1;
        } else {
            self.closure_calls += 1;
        }
        Ok(())
    }

    /// The statement `st` of the copy: the locals with `f`, the closures with
    /// `cl`, and a closure with new `Cap` captures gets their operands.
    fn copy_stmt(
        &self,
        c: &Copy,
        st: &Stmt,
        f: &PlaceMap<'_>,
        cl: &impl Fn(ClosureId) -> ClosureId,
    ) -> Result<Stmt, NoCopy> {
        let mut out = map_stmt(st, f, cl);
        if let StmtKind::Assign(_, Rvalue::Aggregate(weft_ir::AggKind::Closure(cid), ops)) =
            &mut out.kind
        {
            if let Some(Extra { fields, .. }) = c.extra.get(cid) {
                let d = self.p.closures.get(cid.index()).ok_or(NoCopy)?;
                let have = ops.len();
                for cap in d.captures.iter().skip(have) {
                    ops.push(Operand::Copy(cap.source.clone()));
                }
                if ops.len() != have + fields.len() {
                    return Err(NoCopy);
                }
            }
        }
        Ok(out)
    }

    /// The `Cap` capture sources of each closure of the copy that body `maker`
    /// makes, now that `maker` is in the program.
    fn add_cap_sources(&mut self, c: &Copy, maker: BodyId) -> Result<(), NoCopy> {
        let keys: Vec<ClosureId> = c
            .extra
            .iter()
            .filter(|(_, x)| x.maker == maker && !x.fields.is_empty())
            .map(|(k, _)| *k)
            .collect();
        for cid in keys {
            let Some(Extra { env, fields, .. }) = c.extra.get(&cid).cloned() else {
                continue;
            };
            let mut srcs = Vec::new();
            for &(e, _) in &fields {
                srcs.push(self.cap_source(maker, env, e)?);
            }
            let nd = self.p.closures.get_mut(cid.index()).ok_or(NoCopy)?;
            for src in srcs {
                nd.captures.push(weft_ir::Capture {
                    source: src,
                    mode: weft_ir::CaptureMode::Cap,
                });
            }
        }
        Ok(())
    }

    /// The place in body `x` of the capability of effect `e` that
    /// environment `env` binds first (the capability that a closure made in
    /// `x` captures, as `Builder::cap_of`).
    fn cap_source(&mut self, x: BodyId, env: CapEnvId, e: EffectId) -> Result<Place, NoCopy> {
        let (owner, place) = first_cap(&self.p, env, e).ok_or(NoCopy)?;
        self.upvar_chain(x, owner, place)
    }

    /// The environment of closure body `ob` in the copy: its own `Cap`
    /// fields `own` and the new ones `fields`, on environment `maker_env` of
    /// its maker.
    fn closure_env(
        &mut self,
        ob: &Body,
        maker_env: CapEnvId,
        own: Vec<(EffectId, Place)>,
        fields: &[(EffectId, weft_ir::FieldIdx)],
    ) -> Result<CapEnvId, NoCopy> {
        let mut adds = own;
        let env_local = ob.params.first().copied().ok_or(NoCopy)?;
        for &(e, field) in fields {
            adds.push((
                e,
                Place {
                    local: env_local,
                    proj: vec![Proj::Field(field)],
                },
            ));
        }
        if adds.is_empty() {
            return Ok(maker_env);
        }
        let id = CapEnvId(u32::try_from(self.p.cap_envs.len()).map_err(|_| NoCopy)?);
        self.p.cap_envs.push(CapEnv {
            parent: Some(maker_env),
            adds,
        });
        Ok(id)
    }

    /// The effects that the code of closure body `cb` of the original
    /// program can perform through the capabilities of its maker: its
    /// performs through the row, the rows of its calls, also in the bodies
    /// inside it.
    fn closure_uses(&self, orig: &Program, cb: BodyId) -> BTreeSet<EffectId> {
        let all: BTreeSet<EffectId> = (0..self.tys.effects().len())
            .map(|i| EffectId(u32::try_from(i).unwrap_or(u32::MAX)))
            .collect();
        let mut out = BTreeSet::new();
        for x in std::iter::once(cb).chain(inner_bodies(orig, cb)) {
            let Some(body) = orig.body(x) else {
                continue;
            };
            for blk in &body.blocks {
                match &blk.term.kind {
                    TermKind::Perform {
                        cap: CapOperand::Row(e),
                        ..
                    } => {
                        out.insert(*e);
                    }
                    TermKind::Call {
                        callee: Callee::Fn(g, _),
                        ..
                    } => {
                        if self.needs.unknown.contains(g) {
                            return all;
                        }
                        out.extend(self.needs.row.get(g).into_iter().flatten().copied());
                    }
                    TermKind::Call {
                        callee: Callee::Value(o),
                        ..
                    } => match value_row(&self.tys, body, o) {
                        Some(r) => out.extend(r),
                        None => return all,
                    },
                    _ => {}
                }
            }
        }
        out
    }
}

/// The stated row of the function value of operand `o` of body `body`, or
/// `None` if the type states no row (a call passes each effect through) or
/// the operand is not a whole local.
fn value_row(tys: &TyTable, body: &Body, o: &Operand) -> Option<Vec<EffectId>> {
    let pl = o.place()?;
    if !pl.is_local() {
        return None;
    }
    let t = body.local(pl.local)?.ty;
    match tys.try_get(t)? {
        weft_ir::Ty::Fn(f) => f.row.clone(),
        _ => None,
    }
}

/// The first environment of the chain of `env` that adds effect `e`, as the
/// body that adds it and the place of the capability there.
fn first_cap(p: &Program, env: CapEnvId, e: EffectId) -> Option<(BodyId, Place)> {
    let mut at = Some(env);
    for _ in 0..=p.cap_envs.len() {
        let id = at?;
        let c = p.cap_envs.get(id.index())?;
        if let Some((_, place)) = c.adds.iter().find(|(x, _)| *x == e) {
            let owner = owner_of_env(p, id, e)?;
            return Some((owner, place.clone()));
        }
        at = c.parent;
    }
    None
}

/// The body that opens environment `id` with the capability of effect `e`:
/// a handled body, or a closure body with a `Cap` field.
fn owner_of_env(p: &Program, id: CapEnvId, e: EffectId) -> Option<BodyId> {
    p.bodies.iter().enumerate().find_map(|(i, b)| {
        let yes = b.cap_env == id
            && match b.kind {
                BodyKind::Handled(_) => b.caps.iter().any(|(x, _)| *x == e),
                BodyKind::Closure(_) => true,
                _ => false,
            };
        yes.then(|| BodyId(u32::try_from(i).unwrap_or(u32::MAX)))
    })
}

/// The program of `built` with the copies of the callees at their calls.
///
/// A call gets a copy if a local handler serves an operation that the
/// callee performs with a function value or a reference (see the module
/// text). `None` if no call gets a copy or a copy breaks a rule of the IR.
pub fn instantiate(built: &Built) -> Option<Instantiated> {
    instantiate_with(built, Bounds::default())
}

/// [`instantiate`] with the bounds `bounds`.
pub fn instantiate_with(built: &Built, bounds: Bounds) -> Option<Instantiated> {
    instantiate_mode(built, bounds, false)
}

/// The copies of stage R0k-c1 (`docs/ir.md` 6.1).
///
/// A closure that a clause makes and that resumes the continuation of the
/// clause gets a copy of its body at its one run in the clause (D1a), also
/// in the copy of a callee that gets the closure (D1c). Then the `resume` is
/// a resume point of the clause. `None` if no copy is made.
pub fn instantiate_kont(built: &Built) -> Option<Instantiated> {
    instantiate_mode(built, Bounds::default(), true)
}

/// [`instantiate_with`], or [`instantiate_kont`] with `kont`.
fn instantiate_mode(built: &Built, bounds: Bounds, kont: bool) -> Option<Instantiated> {
    let orig = &built.program;
    let needs = Needs::of(orig, &built.tys);
    let mut inst = Inst {
        bounds,
        orig,
        tys: built.tys.clone(),
        closure_calls: 0,
        needs,
        p: orig.clone(),
        added: 0,
        calls: 0,
        blk_chain: HashMap::new(),
        body_chain: HashMap::new(),
        sites: BTreeMap::new(),
        body_sites: BTreeMap::new(),
        kont,
        covered: BTreeSet::new(),
        skip_mention: false,
    };
    let mut bi = 0usize;
    while bi < inst.p.bodies.len() {
        let b = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
        let mut k = 0usize;
        while k < inst.p.bodies.get(bi).map_or(0, |x| x.blocks.len()) {
            let blk = BlockId(u32::try_from(k).unwrap_or(u32::MAX));
            let mut plan: Option<KontPlan> = None;
            let what = if inst.kont {
                match inst.kont_wants(b, blk) {
                    Some(f) if inst.can_copy(b, blk, f) => Some(What::Fn(f)),
                    Some(_) => None,
                    None => {
                        plan = inst.kont_copy(b, blk);
                        plan.as_ref().map(|x| What::Closure(x.closure))
                    }
                }
            } else {
                match inst.wants(b, blk) {
                    Some(f) if inst.can_copy(b, blk, f) => Some(What::Fn(f)),
                    Some(_) => None,
                    None => inst.closure_copy(b, blk).map(|(_, c)| What::Closure(c)),
                }
            };
            if let Some(what) = what {
                {
                    let save = (
                        (inst.p.clone(), inst.tys.clone(), inst.closure_calls),
                        inst.added,
                        inst.calls,
                        inst.blk_chain.clone(),
                        inst.body_chain.clone(),
                        inst.sites.clone(),
                        inst.body_sites.clone(),
                    );
                    inst.skip_mention = plan.as_ref().is_some_and(|x| !x.removals.is_empty());
                    let done = inst.copy(b, blk, what);
                    inst.skip_mention = false;
                    if let (Ok(()), Some(x)) = (&done, &plan) {
                        inst.covered.insert(x.closure);
                        inst.remove_make(b, &x.removals);
                    }
                    if done.is_err() {
                        inst.p = save.0 .0;
                        inst.tys = save.0 .1;
                        inst.closure_calls = save.0 .2;
                        inst.added = save.1;
                        inst.calls = save.2;
                        inst.blk_chain = save.3;
                        inst.body_chain = save.4;
                        inst.sites = save.5;
                        inst.body_sites = save.6;
                    }
                }
            }
            k += 1;
        }
        bi += 1;
    }
    if inst.calls + inst.closure_calls == 0 {
        return None;
    }
    let tys = &inst.tys;
    let before = weft_ir::verify::verify_program(orig, &built.tys).len();
    // The cleanup chain of a copy ends the values of the callee first, then
    // those of the site: the order of one frame (V16) does not hold across
    // the two, and the machine ends them in the same order as before.
    let broken: Vec<weft_ir::verify::Broken> = weft_ir::verify::verify_program(&inst.p, tys)
        .into_iter()
        .filter(|x| {
            !(x.rule == weft_ir::verify::Rule::UnwindOrder
                && inst.sites.keys().any(|(b, _)| *b == x.body))
        })
        // The cleanup chain of a copy of a closure body in a clause (stage
        // R0k-c1) ends the values of the closure frame, then goes to the
        // chain of the clause, which starts with `UnwindKont`: the order of
        // the machine, as before the copy.
        .filter(|x| {
            !(inst.kont
                && x.rule == weft_ir::verify::Rule::KontNotFirst
                && x.block
                    .is_some_and(|k| inst.sites.contains_key(&(x.body, k))))
        })
        .collect();
    if broken.len() > before {
        if std::env::var_os("WEFT_INST_DEBUG").is_some() {
            eprintln!("instantiate: broken {broken:?}");
        }
        return None;
    }
    if std::env::var_os("WEFT_INST_PRINT").is_some() {
        eprintln!("{}", weft_ir::print::print_program(&inst.p, tys));
    }
    let weak_ok = weak_ok(&inst.p, tys, &inst.needs);
    let mut out = built.clone();
    out.program = inst.p;
    out.tys = inst.tys;
    Some(Instantiated {
        built: out,
        calls: inst.calls,
        closure_calls: inst.closure_calls,
        weak_ok,
        sites: inst.sites,
        body_sites: inst.body_sites,
        covered: inst.covered,
    })
}

/// True if no code of program `p` can run a callee that gives a function
/// value to an operation through its row where a local handler serves it
/// (see [`Instantiated::weak_ok`]).
fn weak_ok(p: &Program, tys: &TyTable, needs: &Needs) -> bool {
    let has = |f: &FnId| needs.fns.get(f).is_some_and(|s| !s.is_empty());
    // The direct performs of each closure body and of the bodies inside it.
    let mut closure_needs: BTreeMap<BodyId, BTreeSet<EffectId>> = BTreeMap::new();
    let mut closure_of: Vec<Option<BodyId>> = vec![None; p.bodies.len()];
    for (i, b) in p.bodies.iter().enumerate() {
        let id = BodyId(u32::try_from(i).unwrap_or(u32::MAX));
        let c = match b.kind {
            BodyKind::Closure(_) => Some(id),
            BodyKind::Fn(_) | BodyKind::Test(_) => None,
            _ => b
                .parent
                .and_then(|q| closure_of.get(q.index()).copied().flatten()),
        };
        if let Some(s) = closure_of.get_mut(i) {
            *s = c;
        }
    }
    for (i, b) in p.bodies.iter().enumerate() {
        let entry = matches!(b.kind, BodyKind::Test(_))
            || matches!(b.kind, BodyKind::Fn(f) if p.fns.get(f.index()).is_some_and(|d| d.name == "main"));
        for blk in &b.blocks {
            for s in &blk.stmts {
                if let StmtKind::Assign(_, rv) = &s.kind {
                    let ops: Vec<&Operand> = match rv {
                        Rvalue::Use(o) => vec![o],
                        Rvalue::Aggregate(_, os) | Rvalue::Concat(os) => os.iter().collect(),
                        _ => Vec::new(),
                    };
                    for o in ops {
                        if let Operand::Const(weft_ir::Const::Fn(f, _)) = o {
                            if has(f) {
                                return false;
                            }
                        }
                    }
                }
            }
            match &blk.term.kind {
                TermKind::Call {
                    callee: Callee::Fn(f, _),
                    caps,
                    args,
                    ..
                } => {
                    for o in args {
                        if let Operand::Const(weft_ir::Const::Fn(g, _)) = o {
                            if has(g) {
                                return false;
                            }
                        }
                    }
                    let env = match caps {
                        CapArgs::Lexical(e) => Some(*e),
                        CapArgs::Root => None,
                    };
                    let set = needs.fns.get(f).cloned().unwrap_or_default();
                    for e in set {
                        let served = env.is_some_and(|env| env_binds(p, env, e));
                        if served || entry {
                            return false;
                        }
                        if let Some(c) = closure_of.get(i).copied().flatten() {
                            closure_needs.entry(c).or_default().insert(e);
                        }
                    }
                }
                TermKind::Perform {
                    cap: CapOperand::Row(e),
                    op,
                    ..
                } if risky_op(tys, *e, *op).1 => {
                    if entry {
                        return false;
                    }
                    if let Some(c) = closure_of.get(i).copied().flatten() {
                        closure_needs.entry(c).or_default().insert(*e);
                    }
                }
                _ => {}
            }
        }
    }
    closure_needs.values().all(BTreeSet::is_empty)
}

/// True if a copy at the call can remove the reason `u` of a fallback.
///
/// The reasons are a function value that an operation gives to a handler of
/// a caller (C2), and a call that runs a clause of a local handler that
/// gives a function value or a reference back to the callee (D3).
pub fn wanted(u: &super::Unsupported) -> bool {
    u.reason == crate::analysis::transfer::OP_KEPT
        || u.reason == crate::analysis::clause::GIVES_BACK
}

/// The place of the callee of a call of a function value `copy q`.
fn call_value_place(t: &TermKind) -> Option<Place> {
    match t {
        TermKind::Call {
            callee: Callee::Value(Operand::Copy(q)),
            ..
        } => Some(q.clone()),
        _ => None,
    }
}

/// `(writes, made)` for statement `st` and local `l`: the statement writes
/// `l` or a part of it, and the closure that it makes into the whole `l`.
fn stmt_writes(st: &Stmt, l: LocalId) -> (bool, Option<ClosureId>) {
    match &st.kind {
        StmtKind::Assign(q, rv) if q.local == l => {
            let made = match rv {
                Rvalue::Aggregate(weft_ir::AggKind::Closure(c), _) if q.is_local() => Some(*c),
                _ => None,
            };
            (true, made)
        }
        StmtKind::Drop(q) | StmtKind::Uninit(q) | StmtKind::Consume(q) if q.local == l => {
            (true, None)
        }
        _ => (false, None),
    }
}

/// True if statement `st` borrows or moves local `l` (or a part of it).
fn stmt_borrows_or_moves(st: &Stmt, l: LocalId) -> bool {
    let moved = |o: &Operand| matches!(o, Operand::Move(q) if q.local == l);
    match &st.kind {
        StmtKind::Assign(_, rv) => match rv {
            Rvalue::Ref(q) | Rvalue::Iter(weft_ir::IterSource::Elems(q)) => q.local == l,
            Rvalue::Use(o) | Rvalue::Unary(_, _, o) => moved(o),
            Rvalue::Binary(_, _, a, b) => moved(a) || moved(b),
            Rvalue::Aggregate(_, ops) | Rvalue::Concat(ops) => ops.iter().any(moved),
            _ => false,
        },
        StmtKind::Print(ops) => ops.iter().any(moved),
        _ => false,
    }
}

/// True if terminator `t` moves local `l` (or a part of it).
fn term_moves(t: &TermKind, l: LocalId) -> bool {
    let moved = |o: &Operand| matches!(o, Operand::Move(q) if q.local == l);
    match t {
        TermKind::Call { callee, args, .. } => {
            matches!(callee, Callee::Value(o) if moved(o)) || args.iter().any(moved)
        }
        TermKind::Perform { args, .. } => args.iter().any(moved),
        TermKind::Resume { arg, .. } => moved(arg),
        TermKind::Spawn { task, scope, .. } => moved(task) || moved(scope),
        TermKind::Join { task, .. } | TermKind::Detach { task, .. } => moved(task),
        TermKind::Fork { branches, .. } => branches.iter().any(moved),
        TermKind::Switch { on, .. } => moved(on),
        TermKind::Assert { cond, .. } => moved(cond),
        _ => false,
    }
}

/// The blocks of body `b` that a path reaches from block `from` (`fwd`), or
/// that reach block `from` (not `fwd`), with `from` itself.
fn reach(b: &Body, from: BlockId, fwd: bool) -> Vec<bool> {
    let n = b.blocks.len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    if !fwd {
        for (i, blk) in b.blocks.iter().enumerate() {
            for s in blk.term.kind.successors() {
                if let Some(p) = preds.get_mut(s.index()) {
                    p.push(i);
                }
            }
        }
    }
    let mut seen = vec![false; n];
    let mut work = vec![from.index()];
    while let Some(x) = work.pop() {
        match seen.get_mut(x) {
            Some(v) if !*v => *v = true,
            _ => continue,
        }
        if fwd {
            if let Some(blk) = b.blocks.get(x) {
                work.extend(blk.term.kind.successors().iter().map(|s| s.index()));
            }
        } else if let Some(p) = preds.get(x) {
            work.extend(p.iter().copied());
        }
    }
    seen
}

/// Each place that a statement or a terminator of body `b` names.
fn body_places(b: &Body) -> Vec<Place> {
    let mut out = Vec::new();
    for blk in &b.blocks {
        for st in &blk.stmts {
            stmt_places(st, &mut out);
        }
        term_places(&blk.term.kind, &mut out);
    }
    out
}

/// Adds the place of operand `o` to `out`.
fn op_place(o: &Operand, out: &mut Vec<Place>) {
    if let Some(q) = o.place() {
        out.push(q.clone());
    }
}

/// Adds each place that statement `st` names to `out`.
fn stmt_places(st: &Stmt, out: &mut Vec<Place>) {
    match &st.kind {
        StmtKind::Assign(q, rv) => {
            out.push(q.clone());
            match rv {
                Rvalue::Use(o) | Rvalue::Unary(_, _, o) => op_place(o, out),
                Rvalue::Binary(_, _, a, c) | Rvalue::Iter(weft_ir::IterSource::Range(a, c)) => {
                    op_place(a, out);
                    op_place(c, out);
                }
                Rvalue::Aggregate(_, os) | Rvalue::Concat(os) => {
                    for o in os {
                        op_place(o, out);
                    }
                }
                Rvalue::Ref(q) | Rvalue::Len(q) | Rvalue::Discriminant(q) => {
                    out.push(q.clone());
                }
                Rvalue::Iter(weft_ir::IterSource::Elems(q)) => out.push(q.clone()),
            }
        }
        StmtKind::Drop(q)
        | StmtKind::Consume(q)
        | StmtKind::Uninit(q)
        | StmtKind::Mention(q)
        | StmtKind::UnwindValue(q, _) => out.push(q.clone()),
        StmtKind::Bounds(q, o) => {
            out.push(q.clone());
            op_place(o, out);
        }
        StmtKind::Print(os) => {
            for o in os {
                op_place(o, out);
            }
        }
        StmtKind::Live(l) | StmtKind::Dead(l) | StmtKind::UnwindKont(l) => {
            out.push(Place::local(*l));
        }
    }
}

/// Adds each place that terminator `t` names to `out`.
fn term_places(t: &TermKind, out: &mut Vec<Place>) {
    if let Some(d) = t.dest() {
        out.push(d.clone());
    }
    match t {
        TermKind::Call { callee, args, .. } => {
            if let Callee::Value(o) = callee {
                op_place(o, out);
            }
            for o in args {
                op_place(o, out);
            }
        }
        TermKind::Perform { cap, args, .. } => {
            if let CapOperand::Local(q) = cap {
                out.push(q.clone());
            }
            for o in args {
                op_place(o, out);
            }
        }
        TermKind::Resume { kont, arg, .. } => {
            out.push(kont.clone());
            op_place(arg, out);
        }
        TermKind::Switch { on, .. } => op_place(on, out),
        TermKind::Assert { cond, .. } => op_place(cond, out),
        TermKind::ScopeWait { scope, .. } => out.push(scope.clone()),
        TermKind::Spawn { scope, task, .. } => {
            op_place(scope, out);
            op_place(task, out);
        }
        TermKind::Join { task, .. } | TermKind::Detach { task, .. } => op_place(task, out),
        TermKind::Fork { branches, .. } => {
            for o in branches {
                op_place(o, out);
            }
        }
        TermKind::IterNext { iter, .. } => out.push(iter.clone()),
        _ => {}
    }
}

/// Type `t` with the type arguments `targs` for its type parameters.
fn subst_ty(tys: &mut TyTable, t: weft_ir::TyId, targs: &[weft_ir::TyId]) -> weft_ir::TyId {
    use weft_ir::Ty;
    if !tys.mentions_param(t) {
        return t;
    }
    let Some(ty) = tys.try_get(t).cloned() else {
        return t;
    };
    let s = |x: weft_ir::TyId, tys: &mut TyTable| subst_ty(tys, x, targs);
    let new = match ty {
        Ty::Param(i) => return targs.get(i as usize).copied().unwrap_or(t),
        Ty::Tuple(v) => Ty::Tuple(v.into_iter().map(|x| s(x, tys)).collect()),
        Ty::Array(a, n) => Ty::Array(s(a, tys), n),
        Ty::Slice(a) => Ty::Slice(s(a, tys)),
        Ty::Ref(a) => Ty::Ref(s(a, tys)),
        Ty::Adt(id, args) => Ty::Adt(id, args.into_iter().map(|x| s(x, tys)).collect()),
        Ty::Fn(f) => Ty::Fn(weft_ir::ty::FnTy {
            params: f.params.into_iter().map(|x| s(x, tys)).collect(),
            ret: s(f.ret, tys),
            row: f.row,
        }),
        Ty::Cont(a, c) => Ty::Cont(s(a, tys), s(c, tys)),
        Ty::Iter(a) => Ty::Iter(s(a, tys)),
        other => other,
    };
    tys.intern(new)
}

/// The program `p` with the body of the generic function `f` and the bodies
/// inside it under the type arguments `targs`: the types of the locals, of
/// the aggregates, and the type arguments of the calls and of the function
/// item values. A local whose type changes gets the properties of its new
/// type (`props::ir_props`).
fn subst_program(
    p: &Program,
    tys: &mut TyTable,
    f: FnId,
    targs: &[weft_ir::TyId],
) -> Result<Program, NoCopy> {
    let cb = p.fns.get(f.index()).and_then(|d| d.body).ok_or(NoCopy)?;
    let mut out = p.clone();
    let st = |t: weft_ir::TyId, tys: &mut TyTable| subst_ty(tys, t, targs);
    let sub_op = |o: &mut Operand, tys: &mut TyTable| {
        if let Operand::Const(weft_ir::Const::Fn(_, ts)) = o {
            for t in ts.iter_mut() {
                *t = st(*t, tys);
            }
        }
    };
    for x in std::iter::once(cb).chain(inner_bodies(p, cb)) {
        let body = out.bodies.get_mut(x.index()).ok_or(NoCopy)?;
        for d in &mut body.locals {
            let nt = st(d.ty, tys);
            if nt != d.ty {
                d.ty = nt;
                d.props = crate::props::ir_props(tys, nt);
            }
        }
        for blk in &mut body.blocks {
            for s in &mut blk.stmts {
                match &mut s.kind {
                    StmtKind::Assign(_, rv) => match rv {
                        Rvalue::Aggregate(k, ops) => {
                            match k {
                                weft_ir::AggKind::Struct(t) | weft_ir::AggKind::Variant(t, _) => {
                                    *t = st(*t, tys);
                                }
                                _ => {}
                            }
                            for o in ops.iter_mut() {
                                sub_op(o, tys);
                            }
                        }
                        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => sub_op(o, tys),
                        Rvalue::Binary(_, _, a, c) => {
                            sub_op(a, tys);
                            sub_op(c, tys);
                        }
                        Rvalue::Concat(ops) => {
                            for o in ops.iter_mut() {
                                sub_op(o, tys);
                            }
                        }
                        _ => {}
                    },
                    StmtKind::Print(ops) => {
                        for o in ops.iter_mut() {
                            sub_op(o, tys);
                        }
                    }
                    _ => {}
                }
            }
            match &mut blk.term.kind {
                TermKind::Call { callee, args, .. } => {
                    match callee {
                        Callee::Fn(_, ts) => {
                            for t in ts.iter_mut() {
                                *t = st(*t, tys);
                            }
                        }
                        Callee::Value(o) => sub_op(o, tys),
                    }
                    for o in args.iter_mut() {
                        sub_op(o, tys);
                    }
                }
                TermKind::Perform { args, .. } => {
                    for o in args.iter_mut() {
                        sub_op(o, tys);
                    }
                }
                TermKind::Resume { arg, .. } => sub_op(arg, tys),
                _ => {}
            }
        }
    }
    // A `move` of a place of a type that is a copy type now is a copy (V9).
    for x in std::iter::once(cb).chain(inner_bodies(p, cb)) {
        let Some(mut body) = out.body(x).cloned() else {
            continue;
        };
        let is_copy = |q: &Place, tys: &mut TyTable| -> bool {
            let temp = matches!(body_kind_of(&out, x, q.local), Some(LocalKind::Temp(_)));
            !temp
                && crate::factgen::alpha::place_ty(&out, tys, x, q)
                    .is_some_and(|t| !tys.not_copy(t))
        };
        let fix = |o: &mut Operand, tys: &mut TyTable| {
            if let Operand::Move(q) = o {
                if is_copy(q, tys) {
                    *o = Operand::Copy(q.clone());
                }
            }
        };
        for blk in &mut body.blocks {
            for s in &mut blk.stmts {
                if let StmtKind::Assign(_, rv) = &mut s.kind {
                    match rv {
                        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => fix(o, tys),
                        Rvalue::Binary(_, _, a, c) => {
                            fix(a, tys);
                            fix(c, tys);
                        }
                        Rvalue::Aggregate(_, ops) | Rvalue::Concat(ops) => {
                            for o in ops.iter_mut() {
                                fix(o, tys);
                            }
                        }
                        _ => {}
                    }
                }
            }
            match &mut blk.term.kind {
                TermKind::Call { args, .. } | TermKind::Perform { args, .. } => {
                    for o in args.iter_mut() {
                        fix(o, tys);
                    }
                }
                TermKind::Resume { arg, .. } => fix(arg, tys),
                _ => {}
            }
        }
        if let Some(slot) = out.bodies.get_mut(x.index()) {
            *slot = body;
        }
    }
    Ok(out)
}

/// The kind of local `l` of body `b` of program `p`.
fn body_kind_of(p: &Program, b: BodyId, l: LocalId) -> Option<LocalKind> {
    p.body(b).and_then(|x| x.local_kind(l))
}

/// The one value that a local gets ([`single_value`]).
enum One {
    /// A closure that the statement `si` of block `blk` makes.
    Closure(BlockId, usize, ClosureId),
    /// A copy of another local.
    Copy(LocalId),
}

/// The one value of local `l` of body `body`: `l` is a variable or a
/// temporary that one statement gives a whole value (a closure, or a copy of
/// a whole local), and no statement or terminator moves it, borrows it or
/// writes it (also a part of it) in another way.
fn single_value(body: &Body, l: LocalId) -> Option<One> {
    if !matches!(body.local_kind(l)?, LocalKind::User | LocalKind::Temp(_)) {
        return None;
    }
    let mut one: Option<One> = None;
    let mut writes = 0usize;
    for (bi, blk) in body.blocks.iter().enumerate() {
        let id = BlockId(u32::try_from(bi).ok()?);
        for (si, st) in blk.stmts.iter().enumerate() {
            let (w, made) = stmt_writes(st, l);
            if w {
                writes += 1;
                one = match (&st.kind, made) {
                    (_, Some(c)) => Some(One::Closure(id, si, c)),
                    (StmtKind::Assign(_, Rvalue::Use(Operand::Copy(q))), None) if q.is_local() => {
                        Some(One::Copy(q.local))
                    }
                    _ => None,
                };
            }
            if stmt_borrows_or_moves(st, l) {
                return None;
            }
        }
        if blk.term.kind.dest().is_some_and(|d| d.local == l) || term_moves(&blk.term.kind, l) {
            return None;
        }
    }
    if writes == 1 {
        one
    } else {
        None
    }
}

/// The cell that place `q` of body `x` names, as a local of the body that
/// owns it: an upvar local goes to the local of the parent, a field `env.k`
/// of a closure body goes to the source of a `Kept` capture `k`, and
/// `(*env.k)` to the source of a `ByRef` capture `k`, in the maker. `None`
/// for a place that names no local cell (a place behind a reference).
fn cell_of(p: &Program, x: BodyId, q: &Place) -> Option<(BodyId, LocalId)> {
    let (mut body, mut q) = (x, q.clone());
    for _ in 0..=p.bodies.len() {
        let b = p.body(body)?;
        match b.local_kind(q.local)? {
            LocalKind::Upvar(t) => {
                body = b.parent?;
                q.local = t;
            }
            LocalKind::Env => {
                let (_, d) = p.closure_of(body)?;
                let Some(Proj::Field(k)) = q.proj.first() else {
                    return None;
                };
                let cap = d.captures.get(k.index())?;
                let rest: Vec<Proj> = match cap.mode {
                    weft_ir::CaptureMode::Kept => q.proj.get(1..)?.to_vec(),
                    weft_ir::CaptureMode::ByRef => match q.proj.get(1) {
                        Some(Proj::Deref(weft_ir::DerefKind::Ref)) => q.proj.get(2..)?.to_vec(),
                        _ => return None,
                    },
                    _ => return None,
                };
                let mut src = cap.source.clone();
                src.proj.extend(rest);
                body = d.maker;
                q = src;
            }
            _ => {
                if q.proj.first() == Some(&Proj::Deref(weft_ir::DerefKind::Ref))
                    || q.proj.first() == Some(&Proj::Deref(weft_ir::DerefKind::Box))
                    || q.proj.first() == Some(&Proj::Deref(weft_ir::DerefKind::Rc))
                {
                    return None;
                }
                return Some((body, q.local));
            }
        }
    }
    None
}

/// The places that body `b` writes, moves or borrows: the targets of the
/// assignments and of the terminators, the places of `drop`, `uninit` and
/// `consume`, each `move` operand, each borrow, and the place of an
/// iterator over elements.
fn body_writes(b: &Body) -> Vec<Place> {
    let mut out = Vec::new();
    let mv = |o: &Operand, out: &mut Vec<Place>| {
        if let Operand::Move(q) = o {
            out.push(q.clone());
        }
    };
    for blk in &b.blocks {
        for st in &blk.stmts {
            match &st.kind {
                StmtKind::Assign(q, rv) => {
                    out.push(q.clone());
                    match rv {
                        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => mv(o, &mut out),
                        Rvalue::Binary(_, _, a, c)
                        | Rvalue::Iter(weft_ir::IterSource::Range(a, c)) => {
                            mv(a, &mut out);
                            mv(c, &mut out);
                        }
                        Rvalue::Aggregate(_, os) | Rvalue::Concat(os) => {
                            for o in os {
                                mv(o, &mut out);
                            }
                        }
                        Rvalue::Ref(q) | Rvalue::Iter(weft_ir::IterSource::Elems(q)) => {
                            out.push(q.clone());
                        }
                        Rvalue::Len(_) | Rvalue::Discriminant(_) => {}
                    }
                }
                StmtKind::Drop(q) | StmtKind::Consume(q) | StmtKind::Uninit(q) => {
                    out.push(q.clone());
                }
                StmtKind::Print(os) => {
                    for o in os {
                        mv(o, &mut out);
                    }
                }
                _ => {}
            }
        }
        let t = &blk.term.kind;
        if let Some(d) = t.dest() {
            out.push(d.clone());
        }
        match t {
            TermKind::Call { callee, args, .. } => {
                if let Callee::Value(o) = callee {
                    mv(o, &mut out);
                }
                for o in args {
                    mv(o, &mut out);
                }
            }
            TermKind::Perform { args, .. } => {
                for o in args {
                    mv(o, &mut out);
                }
            }
            TermKind::Resume { arg, .. } => mv(arg, &mut out),
            TermKind::Spawn { scope, task, .. } => {
                mv(scope, &mut out);
                mv(task, &mut out);
            }
            TermKind::Join { task, .. } | TermKind::Detach { task, .. } => mv(task, &mut out),
            TermKind::Fork { branches, .. } => {
                for o in branches {
                    mv(o, &mut out);
                }
            }
            TermKind::Switch { on, .. } => mv(on, &mut out),
            TermKind::Assert { cond, .. } => mv(cond, &mut out),
            TermKind::IterNext { iter, .. } => out.push(iter.clone()),
            _ => {}
        }
    }
    out
}

/// True if a body inside body `b` (each body whose lexical parent chain goes
/// to `b`: clauses, handled bodies, scope bodies, closures, and the bodies
/// inside them) writes, moves or borrows the cell of local `l` of `b`,
/// through an upvar local or a capture of a closure (stage R0k-a2 fix).
fn nested_writes(p: &Program, b: BodyId, l: LocalId) -> bool {
    inner_bodies(p, b).into_iter().any(|x| {
        p.body(x).is_some_and(|xb| {
            body_writes(xb)
                .iter()
                .any(|q| cell_of(p, x, q) == Some((b, l)))
        })
    })
}

/// A copy of stage R0k-c1 ([`Inst::kont_copy`]).
#[derive(Clone, Debug)]
struct KontPlan {
    /// The closure whose body the run gets.
    closure: ClosureId,
    /// The make and the steps of the chain, which go for a `once`
    /// continuation; empty for a `multi` one.
    removals: Vec<(BlockId, usize)>,
}

/// The chain of a closure that a clause makes and that captures the
/// continuation of the clause ([`kont_closure`]).
#[derive(Clone, Debug)]
struct KontChain {
    closure: ClosureId,
    /// The make: the block and the index of the statement.
    make: (BlockId, usize),
    /// The steps `x = move y` or `x = copy y` after the make, in order.
    steps: Vec<(BlockId, usize)>,
    /// The locals of the chain: the local of the make first.
    locals: Vec<LocalId>,
    /// The `Kont` local of the clause.
    kont: LocalId,
    /// True if the closure moves the continuation (a `once` one).
    once: bool,
}

/// The one write of local `l` of body `body`: a statement that gives the
/// whole `l` a value. `None` if `l` is not a variable or a temporary, or if
/// another statement or a terminator writes `l` or a part of it.
fn one_write(body: &Body, l: LocalId) -> Option<(BlockId, usize)> {
    if !matches!(body.local_kind(l)?, LocalKind::User | LocalKind::Temp(_)) {
        return None;
    }
    let mut found = None;
    for (bi, blk) in body.blocks.iter().enumerate() {
        for (si, st) in blk.stmts.iter().enumerate() {
            if stmt_writes(st, l).0 {
                let whole = matches!(&st.kind, StmtKind::Assign(q, _) if q.is_local());
                if found.is_some() || !whole {
                    return None;
                }
                found = Some((BlockId(u32::try_from(bi).ok()?), si));
            }
        }
        if blk.term.kind.dest().is_some_and(|d| d.local == l) {
            return None;
        }
    }
    found
}

/// The chain from the make of a closure to local `l` of clause `b`, if the
/// closure captures the `Kont` local of `b` ([`KontChain`]).
fn kont_closure(p: &Program, b: BodyId, l: LocalId) -> Option<KontChain> {
    let body = p.body(b)?;
    let mut locals = vec![l];
    let mut steps = Vec::new();
    let mut at = l;
    for _ in 0..16 {
        let (blk, si) = one_write(body, at)?;
        let StmtKind::Assign(_, rv) = &body.block(blk)?.stmts.get(si)?.kind else {
            return None;
        };
        match rv {
            Rvalue::Aggregate(weft_ir::AggKind::Closure(c), ops) => {
                let decl = p.closures.get(c.index())?;
                if decl.maker != b {
                    return None;
                }
                let mut kont = None;
                for (cap, o) in decl.captures.iter().zip(ops) {
                    if cap.mode != weft_ir::CaptureMode::Kont {
                        continue;
                    }
                    let src = &cap.source;
                    let own = src.is_local()
                        && matches!(body.local_kind(src.local), Some(LocalKind::Kont(_)));
                    if !own || kont.is_some() {
                        return None;
                    }
                    kont = Some((src.local, matches!(o, Operand::Move(_))));
                }
                let (kont, once) = kont?;
                steps.reverse();
                locals.reverse();
                return Some(KontChain {
                    closure: *c,
                    make: (blk, si),
                    steps,
                    locals,
                    kont,
                    once,
                });
            }
            Rvalue::Use(Operand::Move(q) | Operand::Copy(q)) if q.is_local() => {
                steps.push((blk, si));
                at = q.local;
                locals.push(at);
            }
            _ => return None,
        }
    }
    None
}

/// The number of reads of local `l` in body `body`: each statement or
/// terminator that names `l`, but `Live`, `Dead`, the one write of `l`, and
/// the drops of a cleanup block (`UnwindValue`).
fn local_reads(body: &Body, l: LocalId) -> usize {
    let mut n = 0usize;
    for blk in &body.blocks {
        for st in &blk.stmts {
            match &st.kind {
                StmtKind::Live(_) | StmtKind::Dead(_) => continue,
                StmtKind::UnwindValue(_, _) if blk.cleanup => continue,
                StmtKind::Assign(q, rv) if q.local == l && q.is_local() => {
                    let mut out = Vec::new();
                    stmt_places(
                        &Stmt {
                            kind: StmtKind::Assign(Place::local(LocalId(u32::MAX)), rv.clone()),
                            origin: st.origin,
                        },
                        &mut out,
                    );
                    n += usize::from(out.iter().any(|x| x.local == l));
                    continue;
                }
                _ => {}
            }
            let mut out = Vec::new();
            stmt_places(st, &mut out);
            n += usize::from(out.iter().any(|x| x.local == l));
        }
        let mut out = Vec::new();
        term_places(&blk.term.kind, &mut out);
        n += usize::from(out.iter().any(|x| x.local == l));
    }
    n
}

/// True if `Kont` local `kont` of body `body` appears after the make `make`
/// in a statement or a terminator but `Dead` and `UnwindKont` (anywhere but
/// the make itself: the rule of R0k-c1 is stricter than "after").
fn kont_uses_after(body: &Body, kont: LocalId, make: (BlockId, usize)) -> bool {
    for (bi, blk) in body.blocks.iter().enumerate() {
        for (si, st) in blk.stmts.iter().enumerate() {
            if (bi, si) == (make.0.index(), make.1) {
                continue;
            }
            if matches!(st.kind, StmtKind::Dead(_) | StmtKind::UnwindKont(_)) {
                continue;
            }
            let mut out = Vec::new();
            stmt_places(st, &mut out);
            if out.iter().any(|x| x.local == kont) {
                return true;
            }
        }
        let mut out = Vec::new();
        term_places(&blk.term.kind, &mut out);
        if out.iter().any(|x| x.local == kont) {
            return true;
        }
    }
    false
}

/// True if a body inside body `b` names the cell of local `l` of `b`
/// through an upvar local or a capture ([`cell_of`]).
fn nested_uses(p: &Program, b: BodyId, l: LocalId) -> bool {
    inner_bodies(p, b).into_iter().any(|x| {
        p.body(x).is_some_and(|xb| {
            body_places(xb)
                .iter()
                .any(|q| cell_of(p, x, q) == Some((b, l)))
        })
    })
}

/// True if each path of the CFG of `body` from the make `make` reaches the
/// run at block `run`, with no cycle, through blocks that are not cleanup
/// blocks and whose terminators are `Goto` or `Switch`, and with no
/// statement but `Live` and `Dead` of a local that is not in `sources` and
/// the steps `steps` of the chain (R0k-c1).
fn kont_region_ok(
    body: &Body,
    make: (BlockId, usize),
    run: BlockId,
    steps: &[(BlockId, usize)],
    sources: &BTreeSet<LocalId>,
) -> bool {
    let stmt_ok = |blk: BlockId, si: usize, st: &Stmt| match &st.kind {
        StmtKind::Live(x) | StmtKind::Dead(x) => !sources.contains(x),
        _ => steps.contains(&(blk, si)),
    };
    let block_ok = |id: BlockId, from: usize| -> bool {
        body.block(id).is_some_and(|x| {
            !x.cleanup
                && x.stmts
                    .iter()
                    .enumerate()
                    .skip(from)
                    .all(|(si, st)| stmt_ok(id, si, st))
        })
    };
    if !block_ok(make.0, make.1 + 1) {
        return false;
    }
    if make.0 == run {
        return true;
    }
    // A depth-first walk with colors: grey on the path, black when done.
    let n = body.blocks.len();
    let mut color = vec![0u8; n];
    let mut stack: Vec<(BlockId, usize)> = vec![(make.0, 0)];
    while let Some(&mut (x, ref mut i)) = stack.last_mut() {
        let Some(blk) = body.block(x) else {
            return false;
        };
        if *i == 0 {
            if let Some(c) = color.get_mut(x.index()) {
                *c = 1;
            }
            if !matches!(blk.term.kind, TermKind::Goto(_) | TermKind::Switch { .. }) {
                return false;
            }
            if blk.term.kind.unwind().is_some() {
                return false;
            }
        }
        let succs = blk.term.kind.normal_successors();
        let Some(&next) = succs.get(*i) else {
            if let Some(c) = color.get_mut(x.index()) {
                *c = 2;
            }
            stack.pop();
            continue;
        };
        *i += 1;
        if next == run {
            if !block_ok(run, 0) {
                return false;
            }
            continue;
        }
        match color.get(next.index()).copied() {
            Some(0) => {
                if !block_ok(next, 0) {
                    return false;
                }
                stack.push((next, 0));
            }
            Some(1) | None => return false,
            _ => {}
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A program with a closure inside a closure inside `main`.
    fn nested() -> Program {
        let src = "fn main() {\n    let a = 1;\n    let f = || {\n        let g = || { print(a); };\n        g();\n    };\n    f();\n}\n";
        let a = crate::analyze_source(src, crate::Options::default())
            .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
        crate::irbuild::build(&a).program
    }

    #[test]
    fn inner_bodies_and_body_fns_do_not_use_the_order_of_the_ids() {
        let mut p = nested();
        let main = p
            .bodies
            .iter()
            .position(|b| matches!(b.kind, BodyKind::Fn(_)) && b.parent.is_none())
            .map(|i| BodyId(u32::try_from(i).unwrap_or(u32::MAX)));
        let main = main.unwrap_or_else(|| panic!("no body for `main`"));
        let before = inner_bodies(&p, main);
        assert!(before.len() >= 2, "two closures inside main: {before:?}");
        let fns = body_fns(&p);
        // Append a copy of the first inner body, and make it the parent of
        // that body: the parent now has a higher id than the child.
        let first = before[0];
        let Some(copy) = p.body(first).cloned() else {
            panic!("no body {first:?}");
        };
        let new = BodyId(u32::try_from(p.bodies.len()).unwrap_or(u32::MAX));
        p.bodies.push(copy);
        if let Some(b) = p.bodies.get_mut(first.index()) {
            b.parent = Some(new);
        }
        let after = inner_bodies(&p, main);
        for x in &before {
            assert!(after.contains(x), "{x:?} is still inside main: {after:?}");
        }
        assert!(after.contains(&new));
        let fns2 = body_fns(&p);
        assert_eq!(fns2.get(first.index()), fns.get(first.index()));
        assert_eq!(fns2.get(new.index()), fns.get(first.index()));
    }
}
