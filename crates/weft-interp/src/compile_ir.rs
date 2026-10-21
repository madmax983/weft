//! The IR compiler: core IR to code units (`docs/ir.md` 8.1).
//!
//! The compiler translates each body of the core IR to one [`Code`] unit of
//! the stack machine. The builder of the IR (`weft_sema::irbuild`) decides
//! the order of evaluation, the temporaries and the end of each local, so the
//! compiler only follows the IR:
//!
//! - A parameter, `_0`, a variable and the iterator of a `for` loop get a
//!   slot: `Live` is `BindEmpty`, `Dead` is `DropSlots`. A temporary gets a
//!   slot that holds a temporary cell: `Live` is `LiveTemp`, `Dead` is
//!   `EndTemp`. The cell is also on the temporary list of the frame, so the
//!   unwinder finds the temporaries newest first and then the slots, as for
//!   the code of the AST compiler. The unwinder still uses the frame values:
//!   the cleanup blocks of the IR do not run before the landing pads (plan
//!   stage I6).
//! - An assignment is the ops of the right side, the ops of the place, then
//!   `Store`. A place is `Var`, then `Deref`, `Part` and `Index` for its
//!   projections. A read is the place, then `Read`.
//! - The blocks come in the order of the IR (reverse post-order). A jump to
//!   the next block is left out. A jump back is a back edge: `BackEdge`, the
//!   preemption point of the scheduler, then `Jump`.
//! - Each op carries its IR location ([`IrLoc`]) and the span of its origin.
//! - A closure body gets the arguments of the call in its parameter slots.
//!   Its environment local has no slot: a capture `env.k` is the captured
//!   cell `Var(Cap(k))`. A closure value is [`Op::MakeClosureIr`]: a `Kept`
//!   capture shares the cell of the variable, a `ByMove` capture takes the
//!   value, and a `ByRef` capture holds the reference that `&x` made, so
//!   `(*env.k)` reads through it. The modes come from the IR.
//! - A handled body and a clause are code units of kind
//!   [`CodeKind::HandleBody`] and [`CodeKind::Clause`]. An upvar local has no
//!   slot: it is a captured cell `Var(Cap(i))` of the frame, and the
//!   `Handle` op of the site gives the frame the cell of the site local. An
//!   upvar local of a closure environment (a view, `docs/ir.md` 5.1.7) has
//!   one captured cell for each field of the environment: `u.k` is the cell
//!   of field `k`. The capability local of a handled body is its parameter,
//!   and the continuation of a clause is its parameter after the operation
//!   arguments. A perform through a capability is [`Op::PerformCap`], and a
//!   `resume` is a call of the continuation (`CallValue`).
//!
//! The compiler handles the construct groups A to D: functions, tests,
//! places, calls of items, performs, operators, aggregates, `match`, loops,
//! `assert`, closures, function values, handlers and continuations. For a
//! task it gives a [`Fallback`] that names the plan stage of the construct
//! (I4), and the AST compiler runs the program.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::rc::Rc;

use weft_ir::{
    AggKind, Block, BlockId, Body, BodyId, BodyKind, Callee, CapOperand, CaptureMode, ClosureId,
    Const, HandlerId, IterSource, LocalId, LocalKind, OpIdx, Operand, Origin, Place, Proj, Rvalue,
    Stmt, StmtKind, Term, TermKind, Ty, TyTable,
};
use weft_sema::irbuild::{Built, Outcome};
use weft_sema::program::{EffectId, FnId, Program};
use weft_sema::types::{AdtId, IntTy};
use weft_syntax::ast::{BinOp, Span};
use weft_syntax::diag::Code as DiagCode;

use crate::code::{CapHold, ClauseSpec, Code, CodeKind, HandleSpec, IrLoc, Op, VarRef};
use crate::compile::Compiled;

/// Why the IR compiler does not compile a program. The AST compiler runs it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fallback {
    /// The reason, with the plan stage that adds the construct.
    pub reason: String,
}

impl fmt::Display for Fallback {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.reason)
    }
}

/// The result type of the IR compiler.
type R<T> = Result<T, Fallback>;

/// A construct that the IR compiler does not compile yet.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Later {
    /// A `scope`, a task, a `fork`.
    Task,
    /// `sim.run` or `with_timeout`.
    Intrinsic,
}

impl Later {
    const fn what(self) -> (&'static str, &'static str) {
        match self {
            Self::Task => ("a scope or a task", "I4"),
            Self::Intrinsic => ("`sim.run` or `with_timeout`", "I4"),
        }
    }
}

/// Compiles the IR of each function and each test of a program.
///
/// `prog` is the program of the analysis that `built` comes from: the code
/// names its functions, types and effects.
///
/// # Errors
///
/// A [`Fallback`] if a body has no IR, or if the IR has a construct that the
/// IR compiler does not compile yet.
pub fn compile_ir(prog: &Program, built: &Built) -> Result<Compiled, Fallback> {
    if let Some(b) = built.broken.first() {
        return Err(Fallback {
            reason: format!("the IR breaks a rule of the verifier: {b}"),
        });
    }
    let mut names: BTreeMap<BodyId, String> = BTreeMap::new();
    for e in &built.entries {
        match &e.outcome {
            Outcome::Built(id) => {
                names.insert(*id, e.name.clone());
            }
            Outcome::NoIr(n) => {
                return Err(Fallback {
                    reason: format!("`{}` has no IR: {}", e.name, n.reason()),
                })
            }
            Outcome::Unsupported(u) => {
                return Err(Fallback {
                    reason: format!("`{}` has no IR: {}", e.name, u.construct.name()),
                })
            }
        }
    }
    let fns: BTreeMap<weft_ir::FnId, FnId> = built.fns.iter().map(|(s, i)| (*i, *s)).collect();
    let p = &built.program;
    let mut shared = Shared {
        upvars: Vec::with_capacity(p.bodies.len()),
        jumps: BTreeMap::new(),
    };
    for i in 0..p.bodies.len() {
        let id = BodyId(u32_of(i));
        let ups = upvars_of(p, id).map_err(|m| internal(&top_name(p, id, &names), &m))?;
        shared.upvars.push(ups);
    }
    for d in built.diags.iter().filter(|d| d.code == DiagCode::W0315) {
        let key = (d.unit, d.span.lo, d.span.hi);
        shared.jumps.insert(key, Rc::from(d.message.as_str()));
    }
    let mut codes = Vec::new();
    for (i, body) in p.bodies.iter().enumerate() {
        let id = BodyId(u32::try_from(i).unwrap_or(u32::MAX));
        let name = top_name(p, id, &names);
        let later = |l: Later| {
            let (what, stage) = l.what();
            Fallback {
                reason: format!("`{name}` has {what} (stage {stage})"),
            }
        };
        let (code_name, kind) = match body.kind {
            BodyKind::Fn(f) => {
                let Some(&sf) = fns.get(&f) else {
                    return Err(internal(&name, "a function of the IR has no function"));
                };
                (prog.fns[sf].path.clone(), CodeKind::Fn(sf))
            }
            BodyKind::Test(t) => {
                let test = p.tests.get(t.index()).map_or("", |d| d.name.as_str());
                (format!("test \"{test}\""), CodeKind::Test)
            }
            BodyKind::Closure(_) => ("closure".to_string(), CodeKind::Closure),
            BodyKind::Clause(h, op) => (clause_name(prog, p, h, op), CodeKind::Clause),
            BodyKind::Handled(_) => ("handled computation".to_string(), CodeKind::HandleBody),
            BodyKind::Scope(_) => return Err(later(Later::Task)),
        };
        let cx = BodyCx::new(p, &built.tys, &fns, &shared, body, id, &name)?;
        let code = cx.compile(code_name, kind).map_err(|e| match e {
            Stop::Later(l) => later(l),
            Stop::Internal(m) => internal(&name, &m),
        })?;
        codes.push(Rc::new(code));
    }
    let mut fn_code = vec![None; prog.fns.len()];
    for (i, d) in p.fns.iter().enumerate() {
        let f = weft_ir::FnId(u32::try_from(i).unwrap_or(u32::MAX));
        if let (Some(b), Some(sf)) = (d.body, fns.get(&f)) {
            if let Some(slot) = fn_code.get_mut(sf.index()) {
                *slot = Some(b.index());
            }
        }
    }
    let tests = p
        .tests
        .iter()
        .map(|t| (t.name.clone(), t.body.index()))
        .collect();
    Ok(Compiled {
        codes,
        fn_code,
        tests,
    })
}

/// Returns the name of the function or the test that body `id` is part of.
fn top_name(p: &weft_ir::Program, id: BodyId, names: &BTreeMap<BodyId, String>) -> String {
    let mut cur = id;
    for _ in 0..p.bodies.len() {
        if let Some(n) = names.get(&cur) {
            return n.clone();
        }
        match p.body(cur).and_then(|b| b.parent) {
            Some(parent) => cur = parent,
            None => break,
        }
    }
    format!("body b{}", id.0)
}

/// Returns the name of the code of a clause, as the AST compiler gives it.
fn clause_name(prog: &Program, p: &weft_ir::Program, h: HandlerId, op: OpIdx) -> String {
    p.handlers
        .get(h.index())
        .and_then(|d| prog.effects.get(d.effect.index()))
        .and_then(|e| e.ops.get(op.index()))
        .map_or_else(|| "handler".to_string(), |o| format!("handler {}", o.name))
}

/// What the compilation of each body reads about the other bodies.
struct Shared {
    /// The upvar locals of each body (`upvars_of`).
    upvars: Vec<Vec<(LocalId, Upvar)>>,
    /// The text of each W0315 of the builder, by its unit and span: the
    /// builder ends the path of the jump with `Unreachable` there.
    jumps: BTreeMap<(usize, u32, u32), Rc<str>>,
}

/// How a handled body or a clause names a local of its site: an upvar
/// local (`docs/ir.md` 5.1.7).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Upvar {
    /// An upvar local of a local of the site: one captured cell.
    Whole,
    /// An upvar local of a closure environment (a view) with this number of
    /// fields: one captured cell for each field.
    View(u32),
}

impl Upvar {
    const fn cells(self) -> u32 {
        match self {
            Self::Whole => 1,
            Self::View(n) => n,
        }
    }
}

/// Returns the upvar locals of body `id`, in the order of their ids. Their
/// cells are the captured cells of the frame of the body, in that order.
fn upvars_of(p: &weft_ir::Program, id: BodyId) -> Result<Vec<(LocalId, Upvar)>, String> {
    let Some(body) = p.body(id) else {
        return Err(format!("the body b{} is missing", id.0));
    };
    let mut out = Vec::new();
    for (i, d) in body.locals.iter().enumerate() {
        if !matches!(d.kind, LocalKind::Upvar(_)) {
            continue;
        }
        let l = LocalId(u32_of(i));
        let u = match view_of(p, id, l) {
            Some(c) => {
                let Some(decl) = p.closures.get(c.index()) else {
                    return Err(format!("the closure c{} has no declaration", c.0));
                };
                Upvar::View(u32_of(decl.captures.len()))
            }
            None => Upvar::Whole,
        };
        out.push((l, u));
    }
    Ok(out)
}

/// Returns the closure whose environment the upvar local `l` of body `body`
/// views: the chain of its `Upvar` kinds ends at the environment local of
/// the closure body (`docs/ir.md` 5.1.7). A parent has a lower id than the
/// bodies in it, so the walk ends.
fn view_of(p: &weft_ir::Program, body: BodyId, l: LocalId) -> Option<ClosureId> {
    let (mut at, mut l) = (body, l);
    loop {
        let b = p.body(at)?;
        match b.local_kind(l)? {
            LocalKind::Env => {
                return match b.kind {
                    BodyKind::Closure(c) if b.params.first() == Some(&l) => Some(c),
                    _ => None,
                };
            }
            LocalKind::Upvar(src) => {
                at = b.parent.filter(|x| x.index() < at.index())?;
                l = src;
            }
            _ => return None,
        }
    }
}

fn internal(name: &str, msg: &str) -> Fallback {
    Fallback {
        reason: format!("internal: `{name}`: {msg}"),
    }
}

/// Why the compilation of one body stops.
enum Stop {
    /// A construct of a later stage.
    Later(Later),
    /// The IR does not have the shape that the compiler expects.
    Internal(String),
}

/// The result type of the compilation of one body.
type S<T> = Result<T, Stop>;

fn bad<T>(msg: impl Into<String>) -> S<T> {
    Err(Stop::Internal(msg.into()))
}

/// A jump target before the layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Label {
    /// The first op of a block.
    Block(BlockId),
    /// A back edge to a block: `BackEdge`, then `Jump` to the block.
    Back(BlockId),
}

/// The state of the compilation of one body.
struct BodyCx<'a> {
    p: &'a weft_ir::Program,
    tys: &'a TyTable,
    fns: &'a BTreeMap<weft_ir::FnId, FnId>,
    shared: &'a Shared,
    body: &'a Body,
    id: BodyId,
    /// The environment local of a closure body. It has no slot: its fields
    /// are the captured cells of the frame.
    env: Option<LocalId>,
    /// The slot of each local, if it has one.
    slots: Vec<Option<u32>>,
    /// The upvar locals: how each one names the site, and its first
    /// captured cell.
    upv: Vec<Option<(Upvar, u32)>>,
    /// The local is a temporary.
    temp: Vec<bool>,
    n_slots: u32,
    n_params: u32,
    temp_slots: u32,
    ops: Vec<Op>,
    spans: Vec<Span>,
    locs: Vec<IrLoc>,
    /// The ops whose targets are labels, and the labels in the order of the
    /// targets of the op.
    fixups: Vec<(usize, Vec<Label>)>,
    /// The location and the span of the ops that come next.
    loc: IrLoc,
    span: Span,
}

impl<'a> BodyCx<'a> {
    fn new(
        p: &'a weft_ir::Program,
        tys: &'a TyTable,
        fns: &'a BTreeMap<weft_ir::FnId, FnId>,
        shared: &'a Shared,
        body: &'a Body,
        id: BodyId,
        name: &str,
    ) -> R<Self> {
        let n = body.locals.len();
        let mut slots = vec![None; n];
        let mut temp = vec![false; n];
        let mut next = 0u32;
        // The environment of a closure is its first parameter. The call gives
        // no argument for it.
        let env = match body.kind {
            BodyKind::Closure(_) => body.params.first().copied().filter(|&l| {
                body.local(l)
                    .is_some_and(|d| matches!(d.kind, LocalKind::Env))
            }),
            _ => None,
        };
        if matches!(body.kind, BodyKind::Closure(_)) && env.is_none() {
            return Err(internal(name, "a closure body has no environment"));
        }
        // The parameters are the first slots: the frame puts the arguments
        // there. The capability of a handled body and the continuation of a
        // clause are parameters too: the `Handle` op and the perform give
        // them, after the operation arguments. `_0` comes next, so the
        // unwinder finds it after the locals.
        let params = body.params.iter().copied().filter(|&l| Some(l) != env);
        let caps = body.caps.iter().map(|(_, l)| *l);
        for l in params.chain(caps).chain(body.kont.map(|(l, _)| l)) {
            if let Some(s) = slots.get_mut(l.index()) {
                if s.is_none() {
                    *s = Some(next);
                    next += 1;
                }
            }
        }
        let n_params = next;
        if let Some(s) = slots.get_mut(body.ret.index()) {
            if s.is_none() {
                *s = Some(next);
                next += 1;
            }
        }
        // The upvar locals are the captured cells of the frame.
        let mut upv = vec![None; n];
        let mut cell = 0u32;
        for &(l, u) in shared.upvars.get(id.index()).map_or(&[][..], Vec::as_slice) {
            if let Some(x) = upv.get_mut(l.index()) {
                *x = Some((u, cell));
            }
            cell += u.cells();
        }
        for (i, d) in body.locals.iter().enumerate() {
            match d.kind {
                LocalKind::Return | LocalKind::Param(_) => {}
                LocalKind::Cap(_) | LocalKind::Kont(_) if slots[i].is_some() => {}
                LocalKind::Cap(_) | LocalKind::Kont(_) => {
                    return Err(internal(
                        name,
                        "a capability or a continuation local is not a parameter",
                    ));
                }
                LocalKind::Upvar(_) if upv[i].is_some() => {}
                LocalKind::Upvar(_) => return Err(internal(name, "an upvar local has no cell")),
                LocalKind::User | LocalKind::Iterator => {
                    slots[i] = Some(next);
                    next += 1;
                }
                LocalKind::Temp(_) => temp[i] = true,
                LocalKind::Env if env == Some(LocalId(u32_of(i))) => {}
                LocalKind::Env => return Err(internal(name, "a body has a second environment")),
                LocalKind::ScopeCap | LocalKind::TaskResult(_) => {
                    let (what, stage) = Later::Task.what();
                    return Err(Fallback {
                        reason: format!("`{name}` has {what} (stage {stage})"),
                    });
                }
            }
        }
        let locals = next;
        for (i, t) in temp.iter().enumerate() {
            if *t {
                slots[i] = Some(next);
                next += 1;
            }
        }
        Ok(Self {
            p,
            tys,
            fns,
            shared,
            body,
            id,
            env,
            slots,
            upv,
            temp,
            n_slots: next,
            n_params,
            temp_slots: next - locals,
            ops: Vec::new(),
            spans: Vec::new(),
            locs: Vec::new(),
            fixups: Vec::new(),
            loc: IrLoc::default(),
            span: Span::default(),
        })
    }

    fn compile(mut self, name: String, kind: CodeKind) -> S<Code> {
        let body = self.body;
        // The blocks that run on a normal path, in the order of the IR. The
        // cleanup blocks run only in the landing pads of plan stage I6.
        let order: Vec<BlockId> = body
            .block_ids()
            .filter(|&b| {
                body.block(b)
                    .is_some_and(|x| !x.cleanup && x.term.kind != TermKind::UnwindExit)
            })
            .collect();
        self.loc = IrLoc {
            body: self.id.0,
            block: body.entry.0,
            stmt: 0,
        };
        self.span = span_of(body.origin);
        let ret = self.slot(body.ret)?;
        self.emit(Op::BindEmpty(ret));
        if order.first() != Some(&body.entry) {
            self.jump(Label::Block(body.entry));
        }
        let mut starts: BTreeMap<BlockId, usize> = BTreeMap::new();
        for (k, &b) in order.iter().enumerate() {
            starts.insert(b, self.ops.len());
            let Some(block) = body.block(b) else {
                return bad("a block is missing");
            };
            let next = order.get(k + 1).copied();
            self.block(b, block, next)?;
        }
        // The back edges: one stub for each block that a back edge enters.
        let mut backs: BTreeSet<BlockId> = BTreeSet::new();
        for (_, ls) in &self.fixups {
            for l in ls {
                if let Label::Back(b) = l {
                    backs.insert(*b);
                }
            }
        }
        let mut stubs: BTreeMap<BlockId, usize> = BTreeMap::new();
        for b in backs {
            stubs.insert(b, self.ops.len());
            self.emit(Op::BackEdge);
            self.jump(Label::Block(b));
        }
        let target = |l: &Label| -> S<usize> {
            let at = match l {
                Label::Block(b) => starts.get(b),
                Label::Back(b) => stubs.get(b),
            };
            at.copied()
                .map_or_else(|| bad(format!("no code for the target {l:?}")), Ok)
        };
        let fixups = std::mem::take(&mut self.fixups);
        for (at, ls) in fixups {
            let ts: Vec<usize> = ls.iter().map(target).collect::<S<_>>()?;
            match (self.ops.get_mut(at), ts.as_slice()) {
                (Some(Op::Jump(t) | Op::JumpIfFalse(t) | Op::JumpIfTrue(t)), [x]) => *t = *x,
                (Some(Op::IterNext { exit, .. }), [x]) => *exit = *x,
                (Some(Op::JumpTable { arms, otherwise }), [ts @ .., o])
                    if ts.len() == arms.len() =>
                {
                    for (a, t) in arms.iter_mut().zip(ts) {
                        a.1 = *t;
                    }
                    *otherwise = *o;
                }
                _ => return bad("a jump has no target"),
            }
        }
        Ok(Code {
            name,
            kind,
            ops: self.ops,
            spans: self.spans,
            n_slots: self.n_slots,
            n_params: self.n_params,
            unit: body.origin.span.unit as usize,
            temp_slots: self.temp_slots,
            locs: self.locs,
        })
    }

    // -----------------------------------------------------------------------
    // Ops
    // -----------------------------------------------------------------------

    fn emit(&mut self, op: Op) -> usize {
        self.ops.push(op);
        self.spans.push(self.span);
        self.locs.push(self.loc);
        self.ops.len() - 1
    }

    /// Emits an op whose targets are `labels`.
    fn emit_to(&mut self, op: Op, labels: Vec<Label>) {
        let at = self.emit(op);
        self.fixups.push((at, labels));
    }

    fn jump(&mut self, l: Label) {
        self.emit_to(Op::Jump(0), vec![l]);
    }

    /// Returns the label of an edge from block `from` to block `to`: a back
    /// edge goes through `BackEdge`.
    const fn label(from: BlockId, to: BlockId) -> Label {
        if to.0 <= from.0 {
            Label::Back(to)
        } else {
            Label::Block(to)
        }
    }

    /// Goes from block `from` to block `to`. `next` is the block whose code
    /// comes next.
    fn goto(&mut self, from: BlockId, to: BlockId, next: Option<BlockId>) {
        if to.0 <= from.0 {
            self.emit(Op::BackEdge);
            self.jump(Label::Block(to));
        } else if next != Some(to) {
            self.jump(Label::Block(to));
        }
    }

    fn slot(&self, l: LocalId) -> S<u32> {
        match self.slots.get(l.index()).copied().flatten() {
            Some(s) => Ok(s),
            None => bad(format!("_{} has no slot", l.0)),
        }
    }

    fn upvar(&self, l: LocalId) -> Option<(Upvar, u32)> {
        self.upv.get(l.index()).copied().flatten()
    }

    /// Returns the cell of local `s` of this body for an upvar local of a
    /// nested body: its slot, or its captured cell.
    fn cell_ref(&self, s: LocalId) -> S<VarRef> {
        if let Some(slot) = self.slots.get(s.index()).copied().flatten() {
            return Ok(VarRef::Local(slot));
        }
        match self.upvar(s) {
            Some((Upvar::Whole, cell)) => Ok(VarRef::Cap(cell)),
            _ => bad(format!("an upvar local names _{}, which has no cell", s.0)),
        }
    }

    /// Returns the cell of field `k` of the environment that local `s` of
    /// this body is or views, for a view of a nested body.
    fn field_ref(&self, s: LocalId, k: u32) -> S<VarRef> {
        if Some(s) == self.env {
            return Ok(VarRef::Cap(k));
        }
        match self.upvar(s) {
            Some((Upvar::View(n), cell)) if k < n => Ok(VarRef::Cap(cell + k)),
            _ => bad(format!(
                "a view names _{}, which is not an environment",
                s.0
            )),
        }
    }

    /// Returns the cells of this body that the frame of the nested body
    /// `child` captures: the cells of the site locals of its upvar locals,
    /// in the order of `upvars_of`.
    fn child_cells(&self, child: BodyId) -> S<Vec<VarRef>> {
        let (Some(body), Some(ups)) = (self.p.body(child), self.shared.upvars.get(child.index()))
        else {
            return bad(format!("the body b{} is missing", child.0));
        };
        if body.parent != Some(self.id) {
            return bad(format!(
                "the site of the body b{} is not its parent",
                child.0
            ));
        }
        let mut out = Vec::new();
        for &(l, u) in ups {
            let Some(LocalKind::Upvar(s)) = body.local_kind(l) else {
                return bad("an upvar local is not an upvar");
            };
            match u {
                Upvar::Whole => out.push(self.cell_ref(s)?),
                Upvar::View(n) => {
                    for k in 0..n {
                        out.push(self.field_ref(s, k)?);
                    }
                }
            }
        }
        Ok(out)
    }

    fn is_temp(&self, l: LocalId) -> bool {
        self.temp.get(l.index()).copied().unwrap_or(false)
    }

    // -----------------------------------------------------------------------
    // Blocks and statements
    // -----------------------------------------------------------------------

    fn block(&mut self, b: BlockId, block: &Block, next: Option<BlockId>) -> S<()> {
        for (i, s) in block.stmts.iter().enumerate() {
            self.at(b, i, s.origin);
            if let StmtKind::Assign(dest, Rvalue::Aggregate(AggKind::Struct(ty), ops)) = &s.kind {
                let missing = missing_fields(dest, block.stmts.get(i + 1..).unwrap_or(&[]));
                self.struct_value(*ty, ops, &missing)?;
                self.place(dest)?;
                self.emit(Op::Store);
                continue;
            }
            self.stmt(s)?;
        }
        self.at(b, block.stmts.len(), block.term.origin);
        self.term(b, &block.term, next)
    }

    fn at(&mut self, b: BlockId, i: usize, o: Origin) {
        self.loc = IrLoc {
            body: self.id.0,
            block: b.0,
            stmt: u32::try_from(i).unwrap_or(u32::MAX),
        };
        self.span = span_of(o);
    }

    fn stmt(&mut self, s: &Stmt) -> S<()> {
        match &s.kind {
            StmtKind::Live(l) => {
                let slot = self.slot(*l)?;
                if self.is_temp(*l) {
                    self.emit(Op::LiveTemp(slot));
                } else {
                    self.emit(Op::BindEmpty(slot));
                }
            }
            StmtKind::Dead(l) => {
                let slot = self.slot(*l)?;
                if self.is_temp(*l) {
                    self.emit(Op::EndTemp(slot));
                } else {
                    self.emit(Op::DropSlots(vec![slot]));
                }
            }
            StmtKind::Assign(p, rv) => {
                self.rvalue(rv)?;
                self.place(p)?;
                self.emit(Op::Store);
            }
            StmtKind::Drop(p) => {
                self.place(p)?;
                self.emit(Op::DropPlace);
            }
            StmtKind::Consume(p) => {
                self.place(p)?;
                self.emit(Op::Consume);
            }
            // A whole local has no value after `BindEmpty`. A missing field
            // of a struct literal is `Moved` (`struct_value`). The place
            // fields of a parameter or of a call result need nothing.
            StmtKind::Uninit(_) => {}
            StmtKind::Bounds(p, i) => {
                self.place(p)?;
                self.operand(i)?;
                self.emit(Op::Bounds);
            }
            StmtKind::Mention(p) => {
                self.place(p)?;
                self.emit(Op::Pop);
            }
            StmtKind::Print(ops) => {
                for o in ops {
                    self.operand(o)?;
                }
                self.emit(Op::Print(u32_of(ops.len())));
                self.emit(Op::Pop);
            }
            StmtKind::UnwindValue(..) | StmtKind::UnwindKont(_) => {
                return bad("an unwind statement on a normal path");
            }
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Right sides, operands and places
    // -----------------------------------------------------------------------

    fn rvalue(&mut self, rv: &Rvalue) -> S<()> {
        match rv {
            Rvalue::Use(o) => self.operand(o)?,
            Rvalue::Ref(p) => {
                if let Some(base) = elems_base(p) {
                    self.place(&base)?;
                    self.emit(Op::BorrowAll);
                } else {
                    self.place(p)?;
                    self.emit(Op::Borrow);
                }
            }
            Rvalue::Binary(op, ty, a, b) => {
                self.operand(a)?;
                self.operand(b)?;
                self.emit(Op::Bin(bin_op(*op)));
                self.check_int(*ty);
            }
            Rvalue::Unary(op, ty, a) => {
                self.operand(a)?;
                match op {
                    weft_ir::UnOp::Neg => {
                        self.emit(Op::Neg);
                        self.check_int(*ty);
                    }
                    weft_ir::UnOp::Not => {
                        self.emit(Op::Not);
                    }
                }
            }
            Rvalue::Aggregate(kind, ops) => self.aggregate(kind, ops)?,
            Rvalue::Len(p) => {
                self.place(&elems_base(p).unwrap_or_else(|| p.clone()))?;
                self.emit(Op::Len);
            }
            Rvalue::Discriminant(p) => {
                self.place(p)?;
                self.emit(Op::Tag);
            }
            Rvalue::Concat(ops) => {
                for o in ops {
                    self.operand(o)?;
                    self.emit(Op::ToStr);
                }
                self.emit(Op::Concat(u32_of(ops.len())));
            }
            Rvalue::Iter(IterSource::Elems(p)) => {
                self.place(&elems_base(p).unwrap_or_else(|| p.clone()))?;
                self.emit(Op::ElemIter);
            }
            Rvalue::Iter(IterSource::Range(a, b)) => {
                self.operand(a)?;
                self.operand(b)?;
                self.emit(Op::RangeIter);
            }
        }
        Ok(())
    }

    fn check_int(&mut self, ty: Option<weft_ir::IntTy>) {
        if let Some(it) = ty.and_then(|t| IntTy::from_name(t.name())) {
            self.emit(Op::CheckInt(it));
        }
    }

    fn aggregate(&mut self, kind: &AggKind, ops: &[Operand]) -> S<()> {
        match kind {
            AggKind::Tuple => {
                self.operands(ops)?;
                self.emit(Op::Tuple(u32_of(ops.len())));
            }
            AggKind::Array | AggKind::Vec => {
                self.operands(ops)?;
                self.emit(Op::MakeVec(u32_of(ops.len())));
            }
            AggKind::Struct(ty) => self.struct_value(*ty, ops, &BTreeSet::new())?,
            AggKind::Variant(ty, v) => {
                let adt = self.adt(*ty)?;
                self.operands(ops)?;
                self.emit(Op::MakeEnum {
                    adt,
                    variant: v.0,
                    n: u32_of(ops.len()),
                });
            }
            AggKind::Closure(c) => self.closure(*c, ops)?,
        }
        Ok(())
    }

    /// A closure value (`docs/ir.md` 5.22, 8.1). The operand of a `Kept`
    /// capture is the place of the variable (`copy x`): the closure shares
    /// its cell. The operand of a `ByMove` capture is the moved value, and
    /// the operand of a `ByRef` capture is the reference `&x`: the closure
    /// holds each in a cell of its own.
    fn closure(&mut self, c: ClosureId, ops: &[Operand]) -> S<()> {
        let Some(decl) = self.p.closures.get(c.index()) else {
            return bad(format!("the closure c{} has no declaration", c.0));
        };
        if decl.captures.len() != ops.len() {
            return bad("a closure has a wrong number of operands");
        }
        let mut holds = Vec::with_capacity(ops.len());
        for (cap, o) in decl.captures.iter().zip(ops) {
            let hold = match (cap.mode, o) {
                (CaptureMode::Kept, Operand::Copy(p)) => {
                    self.place(p)?;
                    CapHold::Shared
                }
                (CaptureMode::Kept, _) => return bad("a kept capture is not a place"),
                (CaptureMode::ByMove, o) => {
                    self.operand(o)?;
                    CapHold::Moved
                }
                (CaptureMode::ByRef, o) => {
                    self.operand(o)?;
                    CapHold::Ref
                }
                // A capability and a `multi` continuation are copy values:
                // the closure holds a copy. A `once` continuation moves into
                // the closure (`docs/ir.md` 5.27).
                (CaptureMode::Cap | CaptureMode::Kont, Operand::Copy(p)) => {
                    self.place(p)?;
                    self.emit(Op::Read);
                    CapHold::Copied
                }
                (CaptureMode::Kont, Operand::Move(p)) => {
                    self.place(p)?;
                    self.emit(Op::Take);
                    CapHold::Moved
                }
                (CaptureMode::Cap | CaptureMode::Kont, _) => {
                    return bad("a capability or a continuation capture is not a place")
                }
            };
            holds.push(hold);
        }
        // The code unit of body `i` is code unit `i` (`compile_ir`).
        self.emit(Op::MakeClosureIr {
            code: decl.body.index(),
            holds,
            span: self.span,
        });
        Ok(())
    }

    /// A struct value. A field in `missing` is a field that the literal does
    /// not give: it gets no value (`Moved`), as with the AST compiler.
    fn struct_value(
        &mut self,
        ty: weft_ir::TyId,
        ops: &[Operand],
        missing: &BTreeSet<u32>,
    ) -> S<()> {
        let adt = self.adt(ty)?;
        let mut fields = Vec::new();
        for (i, o) in ops.iter().enumerate() {
            let i = u32_of(i);
            if missing.contains(&i) {
                continue;
            }
            self.operand(o)?;
            fields.push(i);
        }
        self.emit(Op::MakeStruct {
            adt,
            fields,
            total: u32_of(ops.len()),
        });
        Ok(())
    }

    fn adt(&self, ty: weft_ir::TyId) -> S<AdtId> {
        match self.tys.try_get(ty) {
            Some(Ty::Adt(a, _)) => Ok(AdtId(a.index())),
            _ => bad("an aggregate of a type that is not a definition"),
        }
    }

    fn operands(&mut self, ops: &[Operand]) -> S<()> {
        for o in ops {
            self.operand(o)?;
        }
        Ok(())
    }

    fn operand(&mut self, o: &Operand) -> S<()> {
        match o {
            Operand::Copy(p) => {
                self.place(p)?;
                self.emit(Op::Read);
            }
            Operand::Move(p) => {
                self.place(p)?;
                self.emit(Op::Take);
            }
            Operand::Const(c) => {
                let op = match c {
                    Const::Unit => Op::Unit,
                    Const::Bool(b) => Op::Bool(*b),
                    Const::Int(v, _) => match i64::try_from(*v) {
                        Ok(v) => Op::Int(v),
                        Err(_) => Op::Fault(Rc::from("integer literal is too large")),
                    },
                    Const::Str(s) => Op::Str(Rc::from(s.as_str())),
                    Const::Duration(ms) => Op::Dur(*ms),
                    Const::Fn(f, _) => Op::FnValue(self.item(*f)?),
                };
                self.emit(op);
            }
        }
        Ok(())
    }

    fn place(&mut self, p: &Place) -> S<()> {
        let mut proj: &[Proj] = &p.proj;
        if Some(p.local) == self.env {
            // A field of the environment is a captured cell.
            let Some((Proj::Field(k), rest)) = proj.split_first() else {
                return bad("the environment is used as a whole");
            };
            self.emit(Op::Var(VarRef::Cap(k.0)));
            proj = rest;
        } else if let Some((u, cell)) = self.upvar(p.local) {
            // An upvar local is a captured cell. A field of a view is the
            // captured cell of the field.
            match u {
                Upvar::Whole => {
                    self.emit(Op::Var(VarRef::Cap(cell)));
                }
                Upvar::View(n) => {
                    let Some((Proj::Field(k), rest)) = proj.split_first() else {
                        return bad("an environment view is used as a whole");
                    };
                    if k.0 >= n {
                        return bad("a view has no such field");
                    }
                    self.emit(Op::Var(VarRef::Cap(cell + k.0)));
                    proj = rest;
                }
            }
        } else {
            let s = self.slot(p.local)?;
            self.emit(Op::Var(VarRef::Local(s)));
        }
        for proj in proj {
            match proj {
                Proj::Deref(_) => {
                    self.emit(Op::Deref);
                }
                Proj::Field(k) => {
                    self.emit(Op::Part(k.0));
                }
                // The tag was tested before: the payload values are the
                // parts of the enum value.
                Proj::Variant(_) => {}
                Proj::Index(l) => {
                    let i = self.slot(*l)?;
                    self.emit(Op::Var(VarRef::Local(i)));
                    self.emit(Op::Read);
                    self.emit(Op::Index);
                }
                Proj::Elems | Proj::Split(..) => return bad("a place has an element step"),
            }
        }
        Ok(())
    }

    /// Returns the function of the analysis for function `f` of the IR. An
    /// intrinsic (`sim.run`, `with_timeout`) is a construct of stage I4.
    fn item(&self, f: weft_ir::FnId) -> S<FnId> {
        if self
            .p
            .fns
            .get(f.index())
            .is_some_and(|d| d.intrinsic.is_some())
        {
            return Err(Stop::Later(Later::Intrinsic));
        }
        match self.fns.get(&f) {
            Some(&sf) => Ok(sf),
            None => bad(format!("the function f{} has no function", f.0)),
        }
    }

    // -----------------------------------------------------------------------
    // Terminators
    // -----------------------------------------------------------------------

    fn term(&mut self, b: BlockId, t: &Term, next: Option<BlockId>) -> S<()> {
        match &t.kind {
            TermKind::Goto(to) => self.goto(b, *to, next),
            TermKind::Switch {
                on,
                arms,
                otherwise,
            } => {
                self.operand(on)?;
                self.switch(b, self.is_bool(on), arms, *otherwise, next);
            }
            TermKind::Return => {
                let s = self.slot(self.body.ret)?;
                self.emit(Op::Var(VarRef::Local(s)));
                self.emit(Op::Take);
                self.emit(Op::Return);
            }
            TermKind::Unreachable => {
                let o = t.origin.span;
                let msg = if let Some(m) = self.shared.jumps.get(&(o.unit as usize, o.lo, o.hi)) {
                    Rc::clone(m)
                } else if self.variant_test(b) {
                    Rc::from("this value is another variant: it has no such field")
                } else {
                    Rc::from("no `match` arm matches the value")
                };
                self.emit(Op::Fault(msg));
            }
            TermKind::UnwindExit => return bad("`UnwindExit` on a normal path"),
            TermKind::Call {
                callee,
                args,
                dest,
                next: to,
                ..
            } => {
                match callee {
                    Callee::Fn(f, _) => {
                        let sf = self.item(*f)?;
                        self.operands(args)?;
                        self.emit(Op::Call {
                            f: sf,
                            n: u32_of(args.len()),
                        });
                    }
                    // The callee is read before the arguments (`docs/ir.md`
                    // 5.21).
                    Callee::Value(v) => {
                        self.operand(v)?;
                        self.operands(args)?;
                        self.emit(Op::CallValue(u32_of(args.len())));
                    }
                }
                self.result(b, dest, *to, next)?;
            }
            TermKind::Perform {
                cap,
                op,
                args,
                dest,
                next: to,
                ..
            } => {
                match cap {
                    CapOperand::Row(e) => {
                        self.operands(args)?;
                        self.emit(Op::Perform {
                            effect: EffectId(e.index()),
                            op: op.index(),
                            n: u32_of(args.len()),
                        });
                    }
                    // The capability value, then the arguments. The machine
                    // finds the handler; in a debug build it checks that the
                    // handler is the one of the capability.
                    CapOperand::Local(c) => {
                        self.place(c)?;
                        self.emit(Op::Read);
                        self.operands(args)?;
                        self.emit(Op::PerformCap {
                            op: op.index(),
                            n: u32_of(args.len()),
                        });
                    }
                }
                self.result(b, dest, Some(*to), next)?;
            }
            TermKind::Assert { cond, next: to, .. } => {
                self.operand(cond)?;
                self.emit(Op::Assert);
                self.goto(b, *to, next);
            }
            TermKind::IterNext {
                iter,
                dest,
                next: to,
                done,
            } => {
                if !iter.is_local() {
                    return bad("an iterator that is not a whole local");
                }
                let slot = self.slot(iter.local)?;
                self.emit_to(Op::IterNext { slot, exit: 0 }, vec![Self::label(b, *done)]);
                self.result(b, dest, Some(*to), next)?;
            }
            // A `resume` is a call of the continuation.
            TermKind::Resume {
                kont,
                arg,
                dest,
                next: to,
                ..
            } => {
                self.place(kont)?;
                self.emit(Op::Read);
                self.operand(arg)?;
                self.emit(Op::CallValue(1));
                self.result(b, dest, Some(*to), next)?;
            }
            TermKind::Handle {
                handler,
                dest,
                next: to,
                ..
            } => {
                self.handle(*handler)?;
                self.result(b, dest, Some(*to), next)?;
            }
            TermKind::Scope { .. }
            | TermKind::ScopeWait { .. }
            | TermKind::Spawn { .. }
            | TermKind::Join { .. }
            | TermKind::Detach { .. }
            | TermKind::Fork { .. } => return Err(Stop::Later(Later::Task)),
        }
        Ok(())
    }

    /// A `handle` (`docs/ir.md` 5.24): the `Handle` op gives the frames of
    /// the handled body and of each clause the cells of their upvar locals.
    /// The code unit of body `i` is code unit `i` (`compile_ir`).
    fn handle(&mut self, h: HandlerId) -> S<()> {
        let Some(decl) = self.p.handlers.get(h.index()) else {
            return bad(format!("the handler h{} has no declaration", h.0));
        };
        let mut clauses = Vec::with_capacity(decl.clauses.len());
        for &(op, body) in &decl.clauses {
            clauses.push(ClauseSpec {
                op: op.index(),
                code: body.index(),
                caps: self.child_cells(body)?,
            });
        }
        let spec = HandleSpec {
            effect: EffectId(decl.effect.index()),
            clauses,
            body: decl.handled.index(),
            body_caps: self.child_cells(decl.handled)?,
            cap: true,
        };
        self.emit(Op::Handle(Rc::new(spec)));
        Ok(())
    }

    /// Jumps on the value on top of the stack. A test of a `bool` with one
    /// arm is `JumpIfFalse` or `JumpIfTrue`; each other test is a
    /// `JumpTable`.
    fn switch(
        &mut self,
        b: BlockId,
        is_bool: bool,
        arms: &[(u128, BlockId)],
        otherwise: BlockId,
        next: Option<BlockId>,
    ) {
        if let ([(v @ (0 | 1), arm)], true) = (arms, is_bool) {
            let op = if *v == 1 {
                Op::JumpIfFalse(0)
            } else {
                Op::JumpIfTrue(0)
            };
            self.emit_to(op, vec![Self::label(b, otherwise)]);
            self.goto(b, *arm, next);
            return;
        }
        let mut labels: Vec<Label> = arms.iter().map(|(_, a)| Self::label(b, *a)).collect();
        labels.push(Self::label(b, otherwise));
        let table = Op::JumpTable {
            arms: arms.iter().map(|(v, _)| (*v, 0)).collect(),
            otherwise: 0,
        };
        self.emit_to(table, labels);
    }

    /// Stores the value on top of the stack at `dest`, then goes to `to`. A
    /// call with no next block does not return.
    fn result(
        &mut self,
        b: BlockId,
        dest: &Place,
        to: Option<BlockId>,
        next: Option<BlockId>,
    ) -> S<()> {
        let Some(to) = to else {
            self.emit(Op::Fault(Rc::from(
                "internal: a call that does not return returned",
            )));
            return Ok(());
        };
        self.place(dest)?;
        self.emit(Op::Store);
        self.goto(b, to, next);
        Ok(())
    }

    /// Returns true if the operand is a whole local of type `bool`.
    fn is_bool(&self, o: &Operand) -> bool {
        match o {
            Operand::Copy(p) | Operand::Move(p) => {
                p.is_local()
                    && self
                        .body
                        .local(p.local)
                        .is_some_and(|d| matches!(self.tys.try_get(d.ty), Some(Ty::Bool)))
            }
            Operand::Const(Const::Bool(_)) => true,
            Operand::Const(_) => false,
        }
    }

    /// Returns true if block `b` is the failure of the test of a variant
    /// before a payload place `(p as V).0` (`docs/ir.md` 5.8): the
    /// `otherwise` block of a `Switch` with one arm and the same origin.
    fn variant_test(&self, b: BlockId) -> bool {
        let Some(origin) = self.body.block(b).map(|x| x.term.origin) else {
            return false;
        };
        self.body.blocks.iter().any(|x| match &x.term.kind {
            TermKind::Switch {
                arms, otherwise, ..
            } => *otherwise == b && arms.len() == 1 && x.term.origin == origin,
            _ => false,
        })
    }
}

/// Returns the fields that a struct literal into `dest` does not give: the
/// first field step of each `Uninit` of a place below `dest` right after it
/// (`docs/ir.md` 5.17).
fn missing_fields(dest: &Place, after: &[Stmt]) -> BTreeSet<u32> {
    let mut out = BTreeSet::new();
    for s in after {
        let StmtKind::Uninit(q) = &s.kind else {
            break;
        };
        if q.local != dest.local || !q.proj.starts_with(&dest.proj) {
            continue;
        }
        if let Some(Proj::Field(k)) = q.proj.get(dest.proj.len()) {
            out.insert(k.0);
        }
    }
    out
}

/// Returns the place before the last step of `p[]`, if `p` ends with the
/// element step.
fn elems_base(p: &Place) -> Option<Place> {
    match p.proj.split_last() {
        Some((Proj::Elems, rest)) => Some(Place {
            local: p.local,
            proj: rest.to_vec(),
        }),
        _ => None,
    }
}

const fn span_of(o: Origin) -> Span {
    Span {
        lo: o.span.lo,
        hi: o.span.hi,
    }
}

fn u32_of(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}

const fn bin_op(op: weft_ir::BinOp) -> BinOp {
    match op {
        weft_ir::BinOp::Add => BinOp::Add,
        weft_ir::BinOp::Sub => BinOp::Sub,
        weft_ir::BinOp::Mul => BinOp::Mul,
        weft_ir::BinOp::Div => BinOp::Div,
        weft_ir::BinOp::Rem => BinOp::Rem,
        weft_ir::BinOp::Eq => BinOp::Eq,
        weft_ir::BinOp::Ne => BinOp::Ne,
        weft_ir::BinOp::Lt => BinOp::Lt,
        weft_ir::BinOp::Le => BinOp::Le,
        weft_ir::BinOp::Gt => BinOp::Gt,
        weft_ir::BinOp::Ge => BinOp::Ge,
    }
}
