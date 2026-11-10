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
    /// The number of copied calls.
    pub calls: usize,
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
    let mut out: Vec<Option<FnId>> = vec![None; p.bodies.len()];
    for (i, b) in p.bodies.iter().enumerate() {
        let f = match b.kind {
            BodyKind::Fn(f) => Some(f),
            _ => b.parent.and_then(|q| out.get(q.index()).copied().flatten()),
        };
        if let Some(slot) = out.get_mut(i) {
            *slot = f;
        }
    }
    out
}

/// The bodies inside body `root` (not `root`), in the order of their ids.
fn inner_bodies(p: &Program, root: BodyId) -> Vec<BodyId> {
    let mut inside = vec![false; p.bodies.len()];
    let mut out = Vec::new();
    for (i, b) in p.bodies.iter().enumerate() {
        let yes = b
            .parent
            .is_some_and(|q| q == root || inside.get(q.index()).copied().unwrap_or(false));
        if yes {
            if let Some(s) = inside.get_mut(i) {
                *s = true;
            }
            out.push(BodyId(u32::try_from(i).unwrap_or(u32::MAX)));
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
    tys: &'a TyTable,
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

/// Why a copy cannot be made: the program keeps the call.
#[derive(Debug)]
struct NoCopy;

/// Changes each local of place `pl` with `f`.
fn map_place(pl: &Place, f: &impl Fn(LocalId) -> LocalId) -> Place {
    Place {
        local: f(pl.local),
        proj: pl
            .proj
            .iter()
            .map(|x| match x {
                Proj::Index(l) => Proj::Index(f(*l)),
                other => other.clone(),
            })
            .collect(),
    }
}

fn map_operand(o: &Operand, f: &impl Fn(LocalId) -> LocalId) -> Operand {
    match o {
        Operand::Copy(p) => Operand::Copy(map_place(p, f)),
        Operand::Move(p) => Operand::Move(map_place(p, f)),
        Operand::Const(c) => Operand::Const(c.clone()),
    }
}

/// The statement `s` with locals `f` and closures `cl`.
fn map_stmt(
    s: &Stmt,
    f: &impl Fn(LocalId) -> LocalId,
    cl: &impl Fn(ClosureId) -> ClosureId,
) -> Stmt {
    let mp = |p: &Place| map_place(p, f);
    let mo = |o: &Operand| map_operand(o, f);
    let kind = match &s.kind {
        StmtKind::Live(l) => StmtKind::Live(f(*l)),
        StmtKind::Dead(l) => StmtKind::Dead(f(*l)),
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
        StmtKind::UnwindKont(l) => StmtKind::UnwindKont(f(*l)),
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
        if !targs.is_empty() {
            return None;
        }
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
        if d.generics != 0 || d.intrinsic.is_some() || d.body.is_none() {
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
        let Some(old) = self.orig.cap_envs.get(e.index()).cloned() else {
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
        f: &impl Fn(LocalId) -> LocalId,
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
                orphans: orphans.iter().map(|l| f(*l)).collect(),
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
    fn copy_call(&mut self, b: BodyId, k: BlockId, callee: FnId) -> Result<(), NoCopy> {
        let orig = self.orig;
        let cb = orig
            .fns
            .get(callee.index())
            .and_then(|d| d.body)
            .ok_or(NoCopy)?;
        let cbody = orig.body(cb).ok_or(NoCopy)?.clone();
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
        let inner = inner_bodies(orig, cb);
        let mut chain = self.chain(b, k);
        chain.push(callee);
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
                LocalKind::Param(_) => LocalKind::User,
                _ => nd.kind,
            };
            new_locals.push(nd);
        }
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
                        map_place(&cap.source, &fl)
                    } else {
                        cap.source.clone()
                    },
                    mode: cap.mode,
                })
                .collect();
            let maker_ctx = c.ctx.get(&d.maker).copied().flatten();
            let maker_env = self.env(&mut c, d.cap_env, maker_ctx);
            let used = self.closure_uses(d.body);
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
        for (i, &pl) in cbody.params.iter().enumerate() {
            let arg = args.get(i).cloned().ok_or(NoCopy)?;
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
                stmts.push(self.copy_stmt(&c, st, &fl, &clm)?);
            }
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
                        TermKind::Goto(*n)
                    }
                    None => TermKind::Unreachable,
                },
                TermKind::UnwindExit => TermKind::Goto(unwind),
                t => self.map_term(&mut c, b, t, &fl, &fb, (call_env, None))?,
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
            let same = |l: LocalId| l;
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
        self.calls += 1;
        Ok(())
    }

    /// The statement `st` of the copy: the locals with `f`, the closures with
    /// `cl`, and a closure with new `Cap` captures gets their operands.
    fn copy_stmt(
        &self,
        c: &Copy,
        st: &Stmt,
        f: &impl Fn(LocalId) -> LocalId,
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
    fn closure_uses(&self, cb: BodyId) -> BTreeSet<EffectId> {
        let all: BTreeSet<EffectId> = (0..self.tys.effects().len())
            .map(|i| EffectId(u32::try_from(i).unwrap_or(u32::MAX)))
            .collect();
        let mut out = BTreeSet::new();
        for x in std::iter::once(cb).chain(inner_bodies(self.orig, cb)) {
            let Some(body) = self.orig.body(x) else {
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
                    } => match value_row(self.tys, body, o) {
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
    let orig = &built.program;
    let tys = &built.tys;
    let needs = Needs::of(orig, tys);
    if needs.any.values().all(BTreeSet::is_empty) {
        return None;
    }
    let mut inst = Inst {
        bounds,
        orig,
        tys,
        needs,
        p: orig.clone(),
        added: 0,
        calls: 0,
        blk_chain: HashMap::new(),
        body_chain: HashMap::new(),
        sites: BTreeMap::new(),
        body_sites: BTreeMap::new(),
    };
    let mut bi = 0usize;
    while bi < inst.p.bodies.len() {
        let b = BodyId(u32::try_from(bi).unwrap_or(u32::MAX));
        let mut k = 0usize;
        while k < inst.p.bodies.get(bi).map_or(0, |x| x.blocks.len()) {
            let blk = BlockId(u32::try_from(k).unwrap_or(u32::MAX));
            if let Some(f) = inst.wants(b, blk) {
                if inst.can_copy(b, blk, f) {
                    let save = (
                        inst.p.clone(),
                        inst.added,
                        inst.calls,
                        inst.blk_chain.clone(),
                        inst.body_chain.clone(),
                        inst.sites.clone(),
                        inst.body_sites.clone(),
                    );
                    if inst.copy_call(b, blk, f).is_err() {
                        inst.p = save.0;
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
    if inst.calls == 0 {
        return None;
    }
    let before = weft_ir::verify::verify_program(orig, tys).len();
    // The cleanup chain of a copy ends the values of the callee first, then
    // those of the site: the order of one frame (V16) does not hold across
    // the two, and the machine ends them in the same order as before.
    let broken: Vec<weft_ir::verify::Broken> = weft_ir::verify::verify_program(&inst.p, tys)
        .into_iter()
        .filter(|x| {
            !(x.rule == weft_ir::verify::Rule::UnwindOrder
                && inst.sites.keys().any(|(b, _)| *b == x.body))
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
    Some(Instantiated {
        built: out,
        calls: inst.calls,
        weak_ok,
        sites: inst.sites,
        body_sites: inst.body_sites,
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
