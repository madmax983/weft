//! The well-formedness rules of a body and of a program (final design sketch).
//!
//! The builder makes bodies that obey these rules. The verifier checks them in each
//! test, in debug builds, and on each input of the diff gate. The invariants that the
//! design calls "by construction" follow from these rules and from one fact template
//! for each instruction (`facts.rs`).
//!
//! This sketch implements the rules that need no type table: V1 to V7, V11, V13 to
//! V17. The rules about types (V8, V9, V10, V12) need the type table of `typeck`.

use crate::{
    AggKind, Block, BlockId, Body, BodyId, BodyKind, CapOperand, CaptureMode, LocalId,
    LocalKind, Operand, Place, Program, Proj, Rvalue, StmtKind, TermKind,
};

/// A broken rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Broken {
    /// V1: a successor is not a block of the body.
    NoBlock(BlockId),
    /// V2: a normal edge enters a cleanup block, or an abort edge enters a normal block.
    CleanupEdge(BlockId, BlockId),
    /// V3: a cleanup block ends with a terminator other than `Goto` (to a cleanup
    /// block) or `UnwindExit`, or a `Return` is on a cleanup path.
    CleanupTerm(BlockId),
    /// V4: a local is used where it can have no cell (no `Live` on some path).
    NotLive(BlockId, LocalId),
    /// V5: a local is `Live` twice with no `Dead` between.
    LiveTwice(BlockId, LocalId),
    /// V6: a local other than `_0` still has a cell at `Return`, or any local still has
    /// a cell at `UnwindExit` (upvar locals excepted: their cells belong to the parent).
    LeakedCell(BlockId, LocalId),
    /// V7: `UnwindExit` is not in the unwind exit block, or that block has another
    /// terminator.
    UnwindExit(BlockId),
    /// V11: a capability operand is not a capability value of this body, or a `Row`
    /// operand names an effect that the capability environment of the body binds.
    BadCap(BodyId, BlockId),
    /// V13: a `Kept` capture is borrowed in the closure body, or its operand in the
    /// closure aggregate is not a copy of a whole local.
    KeptBorrowed(BodyId, BlockId),
    /// V14: an upvar local is in a body that cannot have upvar locals, is `Live` or
    /// `Dead`, or names a local that the parent body does not have; or the environment
    /// of a closure is `Live` or `Dead`, or is in a body that is not a closure.
    BadUpvar(BodyId, LocalId),
    /// V15: a handled body or a scope body is not named by exactly one terminator,
    /// or a clause by exactly one handler.
    NotOnceRun(BodyId),
    /// V16: the cleanup chain of a clause does not start with `UnwindKont` of its
    /// continuation.
    KontNotFirst(BodyId, BlockId),
    /// V17: a `Drop` is on a place with no `Deref`, or the next statement is not an
    /// `Assign` of the same place.
    BadDrop(BodyId, BlockId),
}

/// Checks the rules of one body: V1 to V7 and the local parts of V14 and V17.
pub fn verify(body: &Body) -> Vec<Broken> {
    let mut out = Vec::new();
    edges(body, &mut out);
    if !out.is_empty() {
        return out;
    }
    storage(body, &mut out);
    out
}

/// Checks the rules of a program: each body, and V11 and V13 to V17.
pub fn verify_program(p: &Program) -> Vec<Broken> {
    let mut out = Vec::new();
    for (i, b) in p.bodies.iter().enumerate() {
        let id = BodyId(i as u32);
        out.extend(verify(b));
        upvars(p, id, b, &mut out);
        caps(p, id, b, &mut out);
        drops(id, b, &mut out);
        kont_first(id, b, &mut out);
    }
    once_run(p, &mut out);
    kept(p, &mut out);
    out
}

fn block(body: &Body, b: BlockId) -> Option<&Block> {
    body.blocks.get(b.index())
}

/// V1, V2, V3, V7.
fn edges(body: &Body, out: &mut Vec<Broken>) {
    for (i, blk) in body.blocks.iter().enumerate() {
        let id = BlockId(i as u32);
        for s in blk.term.kind.normal_successors() {
            match block(body, s) {
                None => out.push(Broken::NoBlock(s)),
                Some(t) if t.cleanup != blk.cleanup => out.push(Broken::CleanupEdge(id, s)),
                Some(_) => {}
            }
        }
        if let Some(u) = blk.term.kind.unwind() {
            match block(body, u) {
                None => out.push(Broken::NoBlock(u)),
                Some(t) if !t.cleanup => out.push(Broken::CleanupEdge(id, u)),
                Some(_) => {}
            }
        }
        let is_exit = id == body.unwind_exit;
        match &blk.term.kind {
            TermKind::UnwindExit if !is_exit => out.push(Broken::UnwindExit(id)),
            TermKind::Return if blk.cleanup => out.push(Broken::CleanupTerm(id)),
            TermKind::Goto(_) | TermKind::UnwindExit => {}
            _ if blk.cleanup => out.push(Broken::CleanupTerm(id)),
            _ if is_exit => out.push(Broken::UnwindExit(id)),
            _ => {}
        }
    }
}

/// The set of locals with a cell, as a bit vector.
#[derive(Clone, PartialEq, Eq)]
struct Live(Vec<bool>);

impl Live {
    fn join(&mut self, other: &Self) -> bool {
        // A local has a cell after a join only if it has one on each edge.
        let mut changed = false;
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            if *a && !*b {
                *a = false;
                changed = true;
            }
        }
        changed
    }
}

/// Returns true for a local whose cell belongs to another frame: an upvar local (the
/// cell of a site local) or the environment of a closure (the closure value of the run
/// node). Such a local has no `Live` and no `Dead`.
fn is_upvar(body: &Body, l: LocalId) -> bool {
    body.locals.get(l.index()).is_some_and(|d| matches!(d.kind, LocalKind::Upvar(_) | LocalKind::Env))
}

/// V4, V5, V6: a must analysis of the cells. A use needs a cell on each path. This
/// rule is the source of `bound_before_use` for each component (not only the
/// component of the function).
fn storage(body: &Body, out: &mut Vec<Broken>) {
    let n = body.locals.len();
    let mut entry = Live(vec![false; n]);
    for l in body.entry_locals() {
        if let Some(x) = entry.0.get_mut(l.index()) {
            *x = true;
        }
    }
    let mut at: Vec<Option<Live>> = vec![None; body.blocks.len()];
    at[body.entry.index()] = Some(entry);
    let mut work = vec![body.entry];
    while let Some(b) = work.pop() {
        let Some(blk) = block(body, b) else { continue };
        let Some(mut live) = at[b.index()].clone() else { continue };
        for s in &blk.stmts {
            step(body, &s.kind, &mut live, b, out);
        }
        term_uses(&blk.term.kind, &live, b, out);
        let exit = match blk.term.kind {
            TermKind::Return => Some(true),
            TermKind::UnwindExit => Some(false),
            _ => None,
        };
        if let Some(normal) = exit {
            for (i, has) in live.0.iter().enumerate() {
                let l = LocalId(i as u32);
                let kept = is_upvar(body, l) || (normal && l == body.ret);
                if *has && !kept {
                    out.push(Broken::LeakedCell(b, l));
                }
            }
        }
        let succs = blk.term.kind.normal_successors().into_iter().chain(blk.term.kind.unwind());
        for s in succs {
            match &mut at[s.index()] {
                slot @ None => {
                    *slot = Some(live.clone());
                    work.push(s);
                }
                Some(old) => {
                    if old.join(&live) {
                        work.push(s);
                    }
                }
            }
        }
    }
}

fn need(live: &Live, l: LocalId, b: BlockId, out: &mut Vec<Broken>) {
    if !live.0.get(l.index()).copied().unwrap_or(false) {
        out.push(Broken::NotLive(b, l));
    }
}

fn place_uses(p: &Place, live: &Live, b: BlockId, out: &mut Vec<Broken>) {
    need(live, p.local, b, out);
    for pr in &p.proj {
        if let Proj::Index(i) = pr {
            need(live, *i, b, out);
        }
    }
}

fn operand_uses(o: &Operand, live: &Live, b: BlockId, out: &mut Vec<Broken>) {
    match o {
        Operand::Copy(p) | Operand::Move(p) => place_uses(p, live, b, out),
        Operand::Const(_) => {}
    }
}

fn rvalue_uses(r: &Rvalue, live: &Live, b: BlockId, out: &mut Vec<Broken>) {
    match r {
        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => operand_uses(o, live, b, out),
        Rvalue::Binary(_, _, x, y) => {
            operand_uses(x, live, b, out);
            operand_uses(y, live, b, out);
        }
        Rvalue::Ref(p) | Rvalue::Len(p) | Rvalue::Discriminant(p) => place_uses(p, live, b, out),
        Rvalue::Aggregate(_, ops) | Rvalue::Concat(ops) => {
            for o in ops {
                operand_uses(o, live, b, out);
            }
        }
        Rvalue::Iter(crate::IterSource::Elems(p)) => place_uses(p, live, b, out),
        Rvalue::Iter(crate::IterSource::Range(x, y)) => {
            operand_uses(x, live, b, out);
            operand_uses(y, live, b, out);
        }
    }
}

fn step(body: &Body, k: &StmtKind, live: &mut Live, b: BlockId, out: &mut Vec<Broken>) {
    match k {
        StmtKind::Live(l) => {
            if live.0.get(l.index()).copied().unwrap_or(false) {
                out.push(Broken::LiveTwice(b, *l));
            }
            if let Some(x) = live.0.get_mut(l.index()) {
                *x = true;
            }
        }
        StmtKind::Dead(l) => {
            need(live, *l, b, out);
            if !is_upvar(body, *l) {
                if let Some(x) = live.0.get_mut(l.index()) {
                    *x = false;
                }
            }
        }
        StmtKind::Assign(p, r) => {
            rvalue_uses(r, live, b, out);
            place_uses(p, live, b, out);
        }
        StmtKind::Drop(p)
        | StmtKind::Consume(p)
        | StmtKind::Uninit(p)
        | StmtKind::Mention(p)
        | StmtKind::UnwindValue(p, _) => place_uses(p, live, b, out),
        StmtKind::Bounds(p, o) => {
            place_uses(p, live, b, out);
            operand_uses(o, live, b, out);
        }
        StmtKind::Print(ops) => {
            for o in ops {
                operand_uses(o, live, b, out);
            }
        }
        StmtKind::UnwindKont(l) => need(live, *l, b, out),
    }
}

fn term_uses(k: &TermKind, live: &Live, b: BlockId, out: &mut Vec<Broken>) {
    let mut ops: Vec<&Operand> = Vec::new();
    let mut places: Vec<&Place> = Vec::new();
    match k {
        TermKind::Switch { on, .. } => ops.push(on),
        TermKind::Call { callee, args, dest, .. } => {
            if let crate::Callee::Value(o) = callee {
                ops.push(o);
            }
            ops.extend(args);
            places.push(dest);
        }
        TermKind::Perform { cap, args, dest, .. } => {
            if let CapOperand::Local(p) = cap {
                places.push(p);
            }
            ops.extend(args);
            places.push(dest);
        }
        TermKind::Resume { kont, arg, dest, .. } => {
            places.push(kont);
            ops.push(arg);
            places.push(dest);
        }
        TermKind::Handle { dest, .. } | TermKind::Scope { dest, .. } => places.push(dest),
        TermKind::ScopeWait { scope, .. } => places.push(scope),
        TermKind::Spawn { scope, task, dest, .. } => {
            ops.push(scope);
            ops.push(task);
            places.extend(dest);
        }
        TermKind::Join { task, dest, .. } => {
            ops.push(task);
            places.push(dest);
        }
        TermKind::Detach { task, .. } => ops.push(task),
        TermKind::Fork { branches, dest, .. } => {
            ops.extend(branches);
            places.push(dest);
        }
        TermKind::Assert { cond, .. } => ops.push(cond),
        TermKind::IterNext { iter, dest, .. } => {
            places.push(iter);
            places.push(dest);
        }
        TermKind::Goto(_) | TermKind::Return | TermKind::UnwindExit | TermKind::Unreachable => {}
    }
    for o in ops {
        operand_uses(o, live, b, out);
    }
    for p in places {
        place_uses(p, live, b, out);
    }
}

/// V14: upvar locals and the environment of a closure.
fn upvars(p: &Program, id: BodyId, body: &Body, out: &mut Vec<Broken>) {
    for (i, d) in body.locals.iter().enumerate() {
        let l = LocalId(i as u32);
        let ok = match d.kind {
            LocalKind::Upvar(src) => {
                body.kind.has_upvars()
                    && body
                        .parent
                        .and_then(|pb| p.bodies.get(pb.index()))
                        .is_some_and(|pb| src.index() < pb.locals.len())
            }
            LocalKind::Env => matches!(body.kind, BodyKind::Closure(_)),
            _ => continue,
        };
        if !ok {
            out.push(Broken::BadUpvar(id, l));
        }
        for blk in &body.blocks {
            for s in &blk.stmts {
                if matches!(s.kind, StmtKind::Live(x) | StmtKind::Dead(x) if x == l) {
                    out.push(Broken::BadUpvar(id, l));
                }
            }
        }
    }
}

/// Returns true if the capability environment chain from `env` binds `effect`.
fn env_binds(p: &Program, mut env: Option<crate::CapEnvId>, effect: crate::EffectId) -> bool {
    let mut steps = 0;
    while let Some(e) = env {
        let Some(ce) = p.cap_envs.get(e.index()) else { return false };
        if ce.adds.iter().any(|(eff, _)| *eff == effect) {
            return true;
        }
        env = ce.parent;
        steps += 1;
        if steps > p.cap_envs.len() {
            return false;
        }
    }
    false
}

/// V11: capability operands. A `Local` names a `Cap` local, an upvar local, or a field
/// of the environment; a `Row(E)` appears only where no handler of the body binds `E`.
fn caps(p: &Program, id: BodyId, body: &Body, out: &mut Vec<Broken>) {
    for (i, blk) in body.blocks.iter().enumerate() {
        let TermKind::Perform { cap, .. } = &blk.term.kind else { continue };
        let ok = match cap {
            CapOperand::Local(pl) => body.locals.get(pl.local.index()).is_some_and(|d| {
                matches!(d.kind, LocalKind::Cap(_) | LocalKind::Upvar(_) | LocalKind::Env)
            }),
            CapOperand::Row(e) => !env_binds(p, Some(body.cap_env), *e),
        };
        if !ok {
            out.push(Broken::BadCap(id, BlockId(i as u32)));
        }
    }
}

/// V17: `Drop` only behind a pointer, right before an `Assign` of the same place.
fn drops(id: BodyId, body: &Body, out: &mut Vec<Broken>) {
    for (i, blk) in body.blocks.iter().enumerate() {
        for (j, s) in blk.stmts.iter().enumerate() {
            let StmtKind::Drop(p) = &s.kind else { continue };
            let next_ok = matches!(
                blk.stmts.get(j + 1).map(|n| &n.kind),
                Some(StmtKind::Assign(q, _)) if q == p
            );
            if !p.has_deref() || !next_ok {
                out.push(Broken::BadDrop(id, BlockId(i as u32)));
            }
        }
    }
}

/// V16: a clause cleanup chain starts with `UnwindKont` of the continuation. A
/// cleanup block that an abort edge enters from a normal block is the head of a
/// chain.
fn kont_first(id: BodyId, body: &Body, out: &mut Vec<Broken>) {
    let (BodyKind::Clause(..), Some((k, _))) = (body.kind, body.kont) else { return };
    for blk in &body.blocks {
        if blk.cleanup {
            continue;
        }
        let Some(u) = blk.term.kind.unwind() else { continue };
        let Some(head) = block(body, u) else { continue };
        let first = head.stmts.first().map(|s| &s.kind);
        if !matches!(first, Some(StmtKind::UnwindKont(x)) if *x == k) {
            out.push(Broken::KontNotFirst(id, u));
        }
    }
}

/// V15: each handled body and each scope body is named by exactly one terminator,
/// and each clause by exactly one handler. The splice of a once-run frame needs it.
fn once_run(p: &Program, out: &mut Vec<Broken>) {
    let mut named = vec![0u32; p.bodies.len()];
    for body in &p.bodies {
        for blk in &body.blocks {
            match &blk.term.kind {
                TermKind::Handle { handler, .. } => {
                    if let Some(h) = p.handlers.get(handler.index()) {
                        named[h.handled.index()] += 1;
                    }
                }
                TermKind::Scope { scope, .. } => {
                    if let Some(s) = p.scopes.get(scope.index()) {
                        named[s.body.index()] += 1;
                    }
                }
                _ => {}
            }
        }
    }
    for h in &p.handlers {
        for (_, c) in &h.clauses {
            named[c.index()] += 1;
        }
    }
    for (i, body) in p.bodies.iter().enumerate() {
        let once = matches!(body.kind, BodyKind::Handled(_) | BodyKind::Scope(_) | BodyKind::Clause(..));
        if once && named[i] != 1 {
            out.push(Broken::NotOnceRun(BodyId(i as u32)));
        }
    }
}

/// V13: a `Kept` capture is never borrowed. Its operand in the aggregate is a copy of a
/// whole local; in the closure body no `Ref` names a place below `env.k`.
fn kept(p: &Program, out: &mut Vec<Broken>) {
    for (ci, c) in p.closures.iter().enumerate() {
        let kept: Vec<usize> = c
            .captures
            .iter()
            .enumerate()
            .filter(|(_, cap)| cap.mode == CaptureMode::Kept)
            .map(|(k, _)| k)
            .collect();
        if kept.is_empty() {
            continue;
        }
        let Some(maker) = p.bodies.get(c.maker.index()) else { continue };
        for (bi, blk) in maker.blocks.iter().enumerate() {
            for s in &blk.stmts {
                let StmtKind::Assign(_, Rvalue::Aggregate(AggKind::Closure(cid), ops)) = &s.kind else {
                    continue;
                };
                if cid.index() != ci {
                    continue;
                }
                for k in &kept {
                    let whole_copy = matches!(ops.get(*k), Some(Operand::Copy(pl)) if pl.proj.is_empty());
                    if !whole_copy {
                        out.push(Broken::KeptBorrowed(c.maker, BlockId(bi as u32)));
                    }
                }
            }
        }
        let Some(body) = p.bodies.get(c.body.index()) else { continue };
        let Some(env) = body.params.first().copied() else { continue };
        for (bi, blk) in body.blocks.iter().enumerate() {
            for s in &blk.stmts {
                let StmtKind::Assign(_, Rvalue::Ref(pl)) = &s.kind else { continue };
                let below_kept = pl.local == env
                    && matches!(pl.proj.first(), Some(Proj::Field(f)) if kept.contains(&f.index()));
                if below_kept {
                    out.push(Broken::KeptBorrowed(c.body, BlockId(bi as u32)));
                }
            }
        }
    }
}
