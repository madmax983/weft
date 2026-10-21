//! The compiler: AST to code units.
//!
//! The compiler resolves names with the same rules as semantic analysis: locals
//! first, then items, then unqualified enum variants, then bare effect operations.
//! A path such as `sim.net.partition` names a module item. `x.op()` performs an
//! operation when `x` names an effect or an effect alias.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use weft_sema::effects;
use weft_sema::program::{AdtKind, EffectId, FnId, ItemRef, ModId, Program, PRELUDE};
use weft_sema::types::{AdtId, IntTy};
use weft_sema::FnSig;
use weft_syntax::ast::{
    Arg, BinOp, Block, EffectPath, Expr, ExprKind, Ident, Lit, Param, Pattern, PatternKind, Span,
    Stmt, StmtKind, StrPart, UnOp,
};

use crate::code::{CPat, ClauseSpec, Code, CodeKind, HandleSpec, LitPat, Op, VarRef};
use crate::value::CodeId;

/// The captures that each closure takes by value when it is made.
///
/// The key is the unit and the span of the closure. The value has the names of
/// the captured variables. Semantic analysis gives them (`FnFacts::by_value`):
/// they are the captures that the closure moves.
pub type ByValue = BTreeMap<(usize, u32, u32), BTreeSet<String>>;

/// The order of the arguments of the calls with named arguments whose callee
/// the compiler does not know: a method of a value receiver and a function item
/// in a local.
///
/// The key is the unit and the span of the call. The value has, for each
/// parameter after the receiver, the index of its argument; the trailing block
/// has the index after the last written argument. Semantic analysis gives it
/// (`FnFacts::arg_order`), so both bind a named argument by name (ADR 0009).
pub type ArgOrder = BTreeMap<(usize, u32, u32), Vec<Option<u32>>>;

/// The integer type of each arithmetic result, by unit and span (see
/// `FnFacts::int_ops`). The machine checks that the result fits.
pub type IntOps = BTreeMap<(usize, u32, u32), IntTy>;

/// What semantic analysis gives the compiler about the program.
#[derive(Clone, Debug, Default)]
pub struct Exports {
    /// The captures that each closure takes by value.
    pub by_value: ByValue,
    /// The order of the arguments of some calls with named arguments.
    pub arg_order: ArgOrder,
    /// The integer type of each arithmetic result.
    pub int_ops: IntOps,
}

/// The compiled program.
#[derive(Debug)]
pub struct Compiled {
    /// All code units.
    pub codes: Vec<Rc<Code>>,
    /// The code of each function with a body.
    pub fn_code: Vec<Option<CodeId>>,
    /// The tests: name and code.
    pub tests: Vec<(String, CodeId)>,
}

/// A path that names something other than a value.
#[derive(Clone, Copy, Debug)]
enum PathRef {
    Mod(ModId),
    Adt(AdtId),
    Effect(EffectId),
}

struct LoopCtx {
    scope_depth: usize,
    breaks: Vec<usize>,
    conts: Vec<usize>,
}

struct Ctx {
    module: ModId,
    kind: CodeKind,
    name: String,
    ops: Vec<Op>,
    spans: Vec<Span>,
    scopes: Vec<Vec<(String, u32)>>,
    n_slots: u32,
    n_params: u32,
    caps: Vec<(String, VarRef)>,
    loops: Vec<LoopCtx>,
    closure: bool,
    span: Span,
}

/// The compiler state.
pub struct Compiler<'a> {
    prog: &'a Program,
    sigs: &'a [FnSig],
    by_value: &'a ByValue,
    arg_order: &'a ArgOrder,
    int_ops: &'a IntOps,
    codes: Vec<Option<Code>>,
    ctxs: Vec<Ctx>,
}

fn fault(msg: impl Into<String>) -> Op {
    Op::Fault(Rc::from(msg.into().as_str()))
}

fn u32_of(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}

impl<'a> Compiler<'a> {
    /// Compiles every function body and every test of a program. A closure
    /// takes the captures that `exports` names for it by value.
    pub fn compile(prog: &'a Program, sigs: &'a [FnSig], exports: &'a Exports) -> Compiled {
        let mut c = Self {
            prog,
            sigs,
            by_value: &exports.by_value,
            arg_order: &exports.arg_order,
            int_ops: &exports.int_ops,
            codes: Vec::new(),
            ctxs: Vec::new(),
        };
        let mut fn_code = vec![None; prog.fns.len()];
        for (f, slot) in fn_code.iter_mut().enumerate() {
            if prog.fns[f].decl.body.is_some() {
                *slot = Some(c.compile_fn(FnId(f)));
            }
        }
        let mut tests = Vec::new();
        for t in &prog.tests {
            let id = c.reserve();
            c.push_ctx(
                t.module,
                CodeKind::Test,
                format!("test \"{}\"", t.name),
                false,
            );
            c.set_span(t.body.span);
            c.block(&t.body);
            c.emit(Op::Return);
            let ctx = c.pop_ctx();
            c.finish(id, ctx);
            tests.push((t.name.clone(), id));
        }
        let codes = c
            .codes
            .into_iter()
            .map(|x| Rc::new(x.unwrap_or_else(empty_code)))
            .collect();
        Compiled {
            codes,
            fn_code,
            tests,
        }
    }

    fn compile_fn(&mut self, f: FnId) -> CodeId {
        let def = &self.prog.fns[f];
        let id = self.reserve();
        self.push_ctx(def.module, CodeKind::Fn(f), def.path.clone(), false);
        self.set_span(def.span);
        for p in &def.decl.params {
            self.declare(&p.name.name);
        }
        self.top().n_params = u32_of(def.decl.params.len());
        if let Some(body) = &def.decl.body {
            self.block(body);
        } else {
            self.emit(Op::Unit);
        }
        self.emit(Op::Return);
        let ctx = self.pop_ctx();
        self.finish(id, ctx);
        id
    }

    // -----------------------------------------------------------------------
    // Contexts
    // -----------------------------------------------------------------------

    fn reserve(&mut self) -> CodeId {
        self.codes.push(None);
        self.codes.len() - 1
    }

    fn finish(&mut self, id: CodeId, ctx: Ctx) {
        self.codes[id] = Some(Code {
            name: ctx.name,
            kind: ctx.kind,
            ops: ctx.ops,
            spans: ctx.spans,
            n_slots: ctx.n_slots,
            n_params: ctx.n_params,
            unit: self
                .prog
                .mods
                .get(ctx.module.index())
                .map_or(usize::MAX, |m| m.unit),
            temp_slots: 0,
            locs: Vec::new(),
        });
    }

    fn push_ctx(&mut self, module: ModId, kind: CodeKind, name: String, closure: bool) {
        let span = self.ctxs.last().map_or_else(Span::default, |c| c.span);
        self.ctxs.push(Ctx {
            module,
            kind,
            name,
            ops: Vec::new(),
            spans: Vec::new(),
            scopes: vec![Vec::new()],
            n_slots: 0,
            n_params: 0,
            caps: Vec::new(),
            loops: Vec::new(),
            closure,
            span,
        });
    }

    fn pop_ctx(&mut self) -> Ctx {
        self.ctxs.pop().unwrap_or_else(|| Ctx {
            module: PRELUDE,
            kind: CodeKind::Closure,
            name: String::new(),
            ops: Vec::new(),
            spans: Vec::new(),
            scopes: Vec::new(),
            n_slots: 0,
            n_params: 0,
            caps: Vec::new(),
            loops: Vec::new(),
            closure: false,
            span: Span::default(),
        })
    }

    fn top(&mut self) -> &mut Ctx {
        let i = self.ctxs.len() - 1;
        &mut self.ctxs[i]
    }

    fn module(&self) -> ModId {
        self.ctxs.last().map_or(PRELUDE, |c| c.module)
    }

    fn set_span(&mut self, s: Span) {
        self.top().span = s;
    }

    fn emit(&mut self, op: Op) -> usize {
        let ctx = self.top();
        ctx.ops.push(op);
        ctx.spans.push(ctx.span);
        ctx.ops.len() - 1
    }

    fn here(&mut self) -> usize {
        self.top().ops.len()
    }

    fn patch(&mut self, at: usize, target: usize) {
        let ctx = self.top();
        match &mut ctx.ops[at] {
            Op::Jump(t) | Op::JumpIfFalse(t) | Op::JumpIfTrue(t) | Op::Break(t) => *t = target,
            Op::Match { fail, .. } | Op::IterNext { exit: fail, .. } => *fail = target,
            _ => {}
        }
    }

    fn declare(&mut self, name: &str) -> u32 {
        let ctx = self.top();
        let s = ctx.n_slots;
        ctx.n_slots += 1;
        if let Some(sc) = ctx.scopes.last_mut() {
            sc.push((name.to_string(), s));
        }
        s
    }

    fn push_scope(&mut self) {
        self.top().scopes.push(Vec::new());
    }

    fn pop_scope(&mut self) -> Vec<u32> {
        self.top()
            .scopes
            .pop()
            .unwrap_or_default()
            .into_iter()
            .map(|(_, s)| s)
            .collect()
    }

    fn drop_slots(&mut self, slots: Vec<u32>) {
        if !slots.is_empty() {
            self.emit(Op::DropSlots(slots));
        }
    }

    /// Finds a variable. A variable of an enclosing closure context becomes a capture.
    fn lookup(&mut self, name: &str) -> Option<VarRef> {
        let top = self.ctxs.len().checked_sub(1)?;
        self.lookup_at(top, name)
    }

    fn lookup_at(&mut self, lvl: usize, name: &str) -> Option<VarRef> {
        let ctx = &self.ctxs[lvl];
        for sc in ctx.scopes.iter().rev() {
            if let Some((_, s)) = sc.iter().rev().find(|(n, _)| n == name) {
                return Some(VarRef::Local(*s));
            }
        }
        if let Some(i) = ctx.caps.iter().position(|(n, _)| n == name) {
            return Some(VarRef::Cap(u32_of(i)));
        }
        if !ctx.closure || lvl == 0 {
            return None;
        }
        let outer = self.lookup_at(lvl - 1, name)?;
        let ctx = &mut self.ctxs[lvl];
        ctx.caps.push((name.to_string(), outer));
        Some(VarRef::Cap(u32_of(ctx.caps.len() - 1)))
    }

    /// Returns true if a name is a variable, without recording a capture.
    fn is_var(&self, name: &str) -> bool {
        for ctx in self.ctxs.iter().rev() {
            if ctx
                .scopes
                .iter()
                .any(|sc| sc.iter().any(|(n, _)| n == name))
                || ctx.caps.iter().any(|(n, _)| n == name)
            {
                return true;
            }
            if !ctx.closure {
                break;
            }
        }
        false
    }

    // -----------------------------------------------------------------------
    // Name resolution
    // -----------------------------------------------------------------------

    fn path_ref(&self, e: &Expr) -> Option<PathRef> {
        match &e.kind {
            ExprKind::Name(id) => {
                if self.is_var(&id.name) {
                    return None;
                }
                let m = self.module();
                match self.prog.lookup(m, &id.name) {
                    Some(ItemRef::Mod(x)) => Some(PathRef::Mod(x)),
                    Some(ItemRef::Adt(a)) => Some(PathRef::Adt(a)),
                    Some(ItemRef::Effect(x)) => Some(PathRef::Effect(x)),
                    Some(ItemRef::Fn(_)) => None,
                    None => {
                        let names = effects::canonical(self.prog, m, &id.name)?;
                        if names.len() != 1 {
                            return None;
                        }
                        effects::by_identity(self.prog, &names[0]).map(PathRef::Effect)
                    }
                }
            }
            ExprKind::Field { base, name } => match self.path_ref(base)? {
                PathRef::Mod(m) => match self.prog.lookup_in(m, &name.name)? {
                    ItemRef::Mod(s) => Some(PathRef::Mod(s)),
                    ItemRef::Adt(a) => Some(PathRef::Adt(a)),
                    ItemRef::Effect(x) => Some(PathRef::Effect(x)),
                    ItemRef::Fn(_) => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    fn adt_by_path(&self, path: &[Ident]) -> Option<AdtId> {
        let mut m = self.module();
        for (i, seg) in path.iter().enumerate() {
            let r = if i == 0 {
                self.prog.lookup(m, &seg.name)
            } else {
                self.prog.lookup_in(m, &seg.name)
            };
            match r? {
                ItemRef::Mod(s) => m = s,
                ItemRef::Adt(a) if i + 1 == path.len() => return Some(a),
                _ => return None,
            }
        }
        None
    }

    /// Finds the effect that a written name or path names, as semantic
    /// analysis does (`effects::resolve`). It gives an identity: in a module that
    /// defines `Log`, `log` is still the standard effect, and `a.Note` is the
    /// effect `Note` of module `a`.
    fn effect_of(&self, path: &EffectPath) -> Option<EffectId> {
        let m = self.module();
        match effects::resolve(self.prog, m, path) {
            Ok(names) if names.len() == 1 => effects::by_identity(self.prog, &names[0]),
            _ => None,
        }
    }

    fn variant(&self, name: &str) -> Option<(AdtId, usize)> {
        self.prog
            .variants
            .get(name)
            .and_then(|v| v.first())
            .copied()
    }

    fn variant_arity(&self, adt: AdtId, vi: usize) -> usize {
        match &self.prog.adts[adt].kind {
            AdtKind::Enum(vs) => vs.get(vi).map_or(0, |v| v.fields.len()),
            _ => 0,
        }
    }

    // -----------------------------------------------------------------------
    // Blocks and statements
    // -----------------------------------------------------------------------

    fn block(&mut self, b: &Block) {
        self.push_scope();
        self.block_body(b);
        let slots = self.pop_scope();
        self.drop_slots(slots);
    }

    /// Compiles the statements of a block. Leaves the block value on the stack.
    fn block_body(&mut self, b: &Block) {
        let n = b.stmts.len();
        let mut has_value = false;
        for (i, s) in b.stmts.iter().enumerate() {
            self.set_span(s.span);
            if i + 1 == n {
                if let StmtKind::Expr(e) = &s.kind {
                    self.expr(e);
                    has_value = true;
                    continue;
                }
            }
            self.emit(Op::StmtBegin);
            self.stmt(s);
            self.set_span(s.span);
            self.emit(Op::StmtEnd);
        }
        if !has_value {
            self.emit(Op::Unit);
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Let { pat, init, .. } => match init {
                Some(e) => {
                    self.expr(e);
                    self.set_span(s.span);
                    self.bind_pat(pat);
                }
                None => self.declare_uninit(pat),
            },
            StmtKind::Expr(e) => {
                // A place of a local only names the place: it moves nothing
                // and drops nothing. Its operands run (ADR 0003).
                if !(self.local_place(e) && self.place(e)) {
                    self.expr(e);
                }
                self.emit(Op::Pop);
            }
            StmtKind::Assign { target, op, value } => {
                self.expr(value);
                // Semantic analysis gives the integer type of a compound
                // assignment at the span of its value.
                let int = self.int_type(value.span);
                self.set_span(s.span);
                if self.place(target) {
                    match op {
                        weft_syntax::ast::AssignOp::Assign => self.emit(Op::Store),
                        weft_syntax::ast::AssignOp::Add => {
                            self.emit(Op::CompoundStore(BinOp::Add, int))
                        }
                        weft_syntax::ast::AssignOp::Sub => {
                            self.emit(Op::CompoundStore(BinOp::Sub, int))
                        }
                        weft_syntax::ast::AssignOp::Mul => {
                            self.emit(Op::CompoundStore(BinOp::Mul, int))
                        }
                    };
                } else {
                    self.emit(fault("the left side of an assignment must be a place"));
                }
            }
            StmtKind::Return(e) => {
                match e {
                    Some(e) => self.expr(e),
                    None => {
                        self.emit(Op::Unit);
                    }
                }
                self.set_span(s.span);
                self.emit(Op::Return);
            }
            StmtKind::Break | StmtKind::Continue => {
                self.jump_out(matches!(s.kind, StmtKind::Break));
            }
            StmtKind::While { cond, body } => {
                self.emit(Op::LoopEnter);
                let head = self.here();
                self.emit(Op::StmtBegin);
                self.expr(cond);
                self.emit(Op::StmtEnd);
                let exit_jump = self.emit(Op::JumpIfFalse(0));
                self.loop_body(head, |c| {
                    c.block(body);
                    c.emit(Op::Pop);
                });
                let exit = self.here();
                self.patch(exit_jump, exit);
                self.emit(Op::LoopExit);
            }
            StmtKind::Loop(body) => {
                self.emit(Op::LoopEnter);
                let head = self.here();
                self.loop_body(head, |c| {
                    c.block(body);
                    c.emit(Op::Pop);
                });
                self.emit(Op::LoopExit);
            }
            StmtKind::For { pat, iter, body } => self.for_loop(pat, iter, body),
            StmtKind::Assert(e) => {
                self.expr(e);
                self.set_span(e.span);
                self.emit(Op::Assert);
            }
        }
    }

    /// Compiles a loop body with its back-edge. Patches `break` and `continue`.
    /// The exit is the instruction right after the back-edge jump.
    fn loop_body(&mut self, head: usize, body: impl FnOnce(&mut Self)) {
        let depth = self.top().scopes.len();
        self.top().loops.push(LoopCtx {
            scope_depth: depth,
            breaks: Vec::new(),
            conts: Vec::new(),
        });
        body(self);
        let cont = self.here();
        self.emit(Op::BackEdge);
        self.emit(Op::Jump(head));
        let exit = self.here();
        let lp = self.top().loops.pop();
        if let Some(lp) = lp {
            for b in lp.breaks {
                self.patch(b, exit);
            }
            for c in lp.conts {
                self.patch(c, cont);
            }
        }
    }

    fn jump_out(&mut self, is_break: bool) {
        let Some(depth) = self.top().loops.last().map(|l| l.scope_depth) else {
            self.emit(fault("`break` or `continue` outside a loop"));
            return;
        };
        let slots: Vec<u32> = self.top().scopes[depth..]
            .iter()
            .flatten()
            .map(|(_, s)| *s)
            .collect();
        self.drop_slots(slots);
        let at = self.emit(Op::Break(0));
        if let Some(lp) = self.top().loops.last_mut() {
            if is_break {
                lp.breaks.push(at);
            } else {
                lp.conts.push(at);
            }
        }
    }

    fn for_loop(&mut self, pat: &Pattern, iter: &Expr, body: &Block) {
        self.push_scope();
        match &iter.kind {
            ExprKind::Range { lo, hi } => {
                self.expr(lo);
                self.expr(hi);
                self.emit(Op::RangeIter);
            }
            ExprKind::Index { base, index: None } => {
                self.place_or_temp(base);
                self.emit(Op::ElemIter);
            }
            _ => {
                self.place_or_temp(iter);
                self.emit(Op::ElemIter);
            }
        }
        let hidden = self.declare("{iterator}");
        self.emit(Op::Bind(hidden));
        self.emit(Op::LoopEnter);
        let head = self.here();
        let next = self.emit(Op::IterNext {
            slot: hidden,
            exit: 0,
        });
        self.loop_body(head, |c| {
            c.push_scope();
            c.bind_pat(pat);
            c.block(body);
            c.emit(Op::Pop);
            let slots = c.pop_scope();
            c.drop_slots(slots);
        });
        let exit = self.here();
        self.patch(next, exit);
        self.emit(Op::LoopExit);
        let slots = self.pop_scope();
        self.drop_slots(slots);
    }

    // -----------------------------------------------------------------------
    // Patterns
    // -----------------------------------------------------------------------

    /// Binds the value on top of the stack to a `let` pattern.
    fn bind_pat(&mut self, pat: &Pattern) {
        match &pat.kind {
            PatternKind::Bind(id) => {
                let s = self.declare(&id.name);
                self.emit(Op::Bind(s));
            }
            PatternKind::Wild(_) | PatternKind::Lit(..) => {
                self.emit(Op::Pop);
            }
            PatternKind::Tuple(ps, _) => {
                self.emit(Op::Untuple(u32_of(ps.len())));
                for p in ps {
                    self.bind_pat(p);
                }
            }
            PatternKind::Variant { path, fields, .. } => {
                let is_struct = self
                    .adt_by_path(path)
                    .is_some_and(|a| matches!(self.prog.adts[a].kind, AdtKind::Struct(_)));
                if is_struct {
                    self.emit(Op::Unstruct(u32_of(fields.len())));
                    for p in fields {
                        self.bind_pat(p);
                    }
                } else {
                    self.emit(fault("a variant pattern needs `match`"));
                }
            }
        }
    }

    fn declare_uninit(&mut self, pat: &Pattern) {
        match &pat.kind {
            PatternKind::Bind(id) => {
                let s = self.declare(&id.name);
                self.emit(Op::BindEmpty(s));
            }
            PatternKind::Tuple(ps, _) => {
                for p in ps {
                    self.declare_uninit(p);
                }
            }
            _ => {}
        }
    }

    fn cpat(&mut self, pat: &Pattern) -> CPat {
        match &pat.kind {
            PatternKind::Wild(_) => CPat::Wild,
            PatternKind::Bind(id) => CPat::Bind(self.declare(&id.name)),
            PatternKind::Lit(l, _) => CPat::Lit(match l {
                Lit::Int(v) => LitPat::Int(i64::try_from(*v).unwrap_or(i64::MAX)),
                Lit::Bool(b) => LitPat::Bool(*b),
                Lit::Unit => LitPat::Unit,
                Lit::Str(parts) => {
                    let mut s = String::new();
                    for p in parts {
                        if let StrPart::Text(t) = p {
                            s.push_str(t);
                        }
                    }
                    LitPat::Str(Rc::from(s.as_str()))
                }
            }),
            PatternKind::Tuple(ps, _) => CPat::Tuple(ps.iter().map(|p| self.cpat(p)).collect()),
            PatternKind::Variant { path, fields, .. } => CPat::Variant {
                name: Rc::from(path.last().map_or("", |p| p.name.as_str())),
                fields: fields.iter().map(|p| self.cpat(p)).collect(),
            },
        }
    }

    // -----------------------------------------------------------------------
    // Expressions
    // -----------------------------------------------------------------------

    fn expr(&mut self, e: &Expr) {
        let saved = self.top().span;
        self.set_span(e.span);
        self.expr_inner(e);
        self.set_span(saved);
    }

    #[allow(clippy::too_many_lines)]
    fn expr_inner(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Lit(l) => self.lit(l),
            ExprKind::Name(id) => self.name(id),
            ExprKind::Field { base, name } => {
                if let ExprKind::Lit(Lit::Int(n)) = &base.kind {
                    match name.name.as_str() {
                        "s" => {
                            self.emit(Op::Dur(n.saturating_mul(1000)));
                            return;
                        }
                        "ms" => {
                            self.emit(Op::Dur(*n));
                            return;
                        }
                        _ => {}
                    }
                }
                match self.path_ref(base) {
                    Some(PathRef::Adt(a)) => {
                        if let AdtKind::Enum(vs) = &self.prog.adts[a].kind {
                            if let Some(vi) = vs.iter().position(|v| v.name == name.name) {
                                self.emit(Op::MakeEnum {
                                    adt: a,
                                    variant: u32_of(vi),
                                    n: 0,
                                });
                                return;
                            }
                        }
                        self.emit(fault(format!("no value `{}` here", name.name)));
                    }
                    Some(PathRef::Mod(m)) => match self.prog.lookup_in(m, &name.name) {
                        Some(ItemRef::Fn(f)) => {
                            self.emit(Op::FnValue(f));
                        }
                        _ => {
                            self.emit(fault(format!("no value `{}` in this module", name.name)));
                        }
                    },
                    Some(PathRef::Effect(_)) => {
                        self.emit(fault("an effect operation needs a call"));
                    }
                    // A literal has no fields, so `place` gives no place.
                    None if self.place(e) => {
                        self.emit(Op::Read);
                    }
                    None => {
                        self.emit(fault(format!("no field `{}` here", name.name)));
                    }
                }
            }
            ExprKind::Index { index: Some(_), .. } => {
                self.place(e);
                self.emit(Op::Read);
            }
            ExprKind::Index { base, index: None } => {
                self.place_or_temp(base);
                self.emit(Op::BorrowAll);
            }
            ExprKind::Call {
                callee,
                args,
                trailing,
            } => self.call(callee, args, trailing.as_deref(), e.span),
            ExprKind::MethodCall {
                receiver,
                method,
                args,
                trailing,
            } => self.method_call(receiver, method, args, trailing.as_deref()),
            ExprKind::Unary { op, expr } => match op {
                UnOp::Ref => self.borrow(expr),
                UnOp::Neg => {
                    self.operand(expr);
                    self.emit(Op::Neg);
                    self.check_int(e.span);
                }
                UnOp::Not => {
                    self.operand(expr);
                    self.emit(Op::Not);
                }
            },
            ExprKind::Binary { op, lhs, rhs } => match op {
                BinOp::And => {
                    self.expr(lhs);
                    let j = self.emit(Op::JumpIfFalse(0));
                    self.expr(rhs);
                    let end = self.emit(Op::Jump(0));
                    let f = self.here();
                    self.patch(j, f);
                    self.emit(Op::Bool(false));
                    let h = self.here();
                    self.patch(end, h);
                }
                BinOp::Or => {
                    self.expr(lhs);
                    let j = self.emit(Op::JumpIfTrue(0));
                    self.expr(rhs);
                    let end = self.emit(Op::Jump(0));
                    let t = self.here();
                    self.patch(j, t);
                    self.emit(Op::Bool(true));
                    let h = self.here();
                    self.patch(end, h);
                }
                _ => {
                    self.operand(lhs);
                    self.operand(rhs);
                    self.set_span(e.span);
                    self.emit(Op::Bin(*op));
                    self.check_int(e.span);
                }
            },
            ExprKind::Range { .. } => {
                self.emit(fault("a range is only valid in `for`"));
            }
            ExprKind::Tuple(es) => {
                for x in es {
                    self.expr(x);
                }
                self.emit(Op::Tuple(u32_of(es.len())));
            }
            ExprKind::Array(es) => {
                for x in es {
                    self.expr(x);
                }
                self.emit(Op::MakeVec(u32_of(es.len())));
            }
            ExprKind::StructLit { path, fields } => self.struct_lit(path, fields),
            ExprKind::Closure { params, body } => {
                let unit = self
                    .prog
                    .mods
                    .get(self.module().index())
                    .map_or(0, |m| m.unit);
                let (code, named) = self.closure_named(params, body, CodeKind::Closure);
                let set = self.by_value.get(&(unit, e.span.lo, e.span.hi));
                let owned = named
                    .iter()
                    .enumerate()
                    .filter(|(_, (n, _))| set.is_some_and(|s| s.contains(n)))
                    .map(|(i, _)| u32_of(i))
                    .collect();
                let caps = named.into_iter().map(|(_, v)| v).collect();
                self.emit(Op::MakeClosure {
                    code,
                    caps,
                    owned,
                    span: e.span,
                });
            }
            ExprKind::Block(b) => self.block(b),
            ExprKind::If { cond, then, else_ } => {
                self.expr(cond);
                let j = self.emit(Op::JumpIfFalse(0));
                self.block(then);
                let end = self.emit(Op::Jump(0));
                let el = self.here();
                self.patch(j, el);
                match else_ {
                    Some(x) => self.expr(x),
                    None => {
                        self.emit(Op::Unit);
                    }
                }
                let h = self.here();
                self.patch(end, h);
            }
            ExprKind::Match { scrutinee, arms } => {
                self.place_or_temp(scrutinee);
                let mut ends = Vec::new();
                for arm in arms {
                    self.set_span(arm.span);
                    self.push_scope();
                    let pat = self.cpat(&arm.pat);
                    let m = self.emit(Op::Match {
                        pat: Rc::new(pat),
                        fail: 0,
                    });
                    self.expr(&arm.body);
                    let slots = self.pop_scope();
                    self.drop_slots(slots);
                    ends.push(self.emit(Op::Jump(0)));
                    let next = self.here();
                    self.patch(m, next);
                }
                self.set_span(e.span);
                self.emit(fault("no `match` arm matches the value"));
                let end = self.here();
                for j in ends {
                    self.patch(j, end);
                }
                self.emit(Op::Nip);
            }
            ExprKind::Handle {
                effect,
                clauses,
                body,
            } => {
                let Some(eid) = self.effect_of(effect) else {
                    self.emit(fault(format!("unknown effect `{}`", effect.text())));
                    return;
                };
                let def = &self.prog.effects[eid];
                let mut specs = Vec::new();
                for c in clauses {
                    let Some(op) = def.ops.iter().position(|o| o.name == c.op.name) else {
                        continue;
                    };
                    let id = self.reserve();
                    let m = self.module();
                    self.push_ctx(m, CodeKind::Clause, format!("handler {}", c.op.name), true);
                    self.set_span(c.span);
                    for p in &c.params {
                        self.declare(&p.name.name);
                    }
                    self.declare("resume");
                    self.top().n_params = u32_of(c.params.len() + 1);
                    self.block(&c.body);
                    self.emit(Op::Return);
                    let ctx = self.pop_ctx();
                    let caps = ctx.caps.iter().map(|(_, v)| *v).collect();
                    self.finish(id, ctx);
                    specs.push(ClauseSpec { op, code: id, caps });
                }
                let (bcode, bcaps) = self.closure(&[], body, CodeKind::HandleBody);
                self.set_span(e.span);
                self.emit(Op::Handle(Rc::new(HandleSpec {
                    effect: eid,
                    clauses: specs,
                    body: bcode,
                    body_caps: bcaps,
                })));
            }
            ExprKind::Scope { binder, body } => {
                let id = self.reserve();
                let m = self.module();
                self.push_ctx(m, CodeKind::ScopeBody, "scope".into(), true);
                self.set_span(e.span);
                let s = self.declare(&binder.name);
                self.top().n_params = 1;
                self.push_scope();
                self.block_body(body);
                self.set_span(e.span);
                self.emit(Op::ScopeWait(s));
                let slots = self.pop_scope();
                self.drop_slots(slots);
                self.emit(Op::Return);
                let ctx = self.pop_ctx();
                let caps = ctx.caps.iter().map(|(_, v)| *v).collect();
                self.finish(id, ctx);
                self.emit(Op::Scope { code: id, caps });
            }
        }
    }

    /// Returns the integer type that semantic analysis gives the arithmetic
    /// expression at `span`, if any.
    fn int_type(&self, span: Span) -> Option<IntTy> {
        let unit = self
            .prog
            .mods
            .get(self.module().index())
            .map_or(0, |m| m.unit);
        self.int_ops.get(&(unit, span.lo, span.hi)).copied()
    }

    /// Checks that the arithmetic result at `span` fits in its integer type.
    fn check_int(&mut self, span: Span) {
        if let Some(it) = self.int_type(span) {
            self.emit(Op::CheckInt(it));
        }
    }

    fn lit(&mut self, l: &Lit) {
        match l {
            Lit::Int(v) => match i64::try_from(*v) {
                Ok(v) => self.emit(Op::Int(v)),
                Err(_) => self.emit(fault("integer literal is too large")),
            },
            Lit::Bool(b) => self.emit(Op::Bool(*b)),
            Lit::Unit => self.emit(Op::Unit),
            Lit::Str(parts) => {
                if parts.iter().all(|p| matches!(p, StrPart::Text(_))) {
                    let mut s = String::new();
                    for p in parts {
                        if let StrPart::Text(t) = p {
                            s.push_str(t);
                        }
                    }
                    self.emit(Op::Str(Rc::from(s.as_str())))
                } else {
                    for p in parts {
                        match p {
                            StrPart::Text(t) => {
                                self.emit(Op::Str(Rc::from(t.as_str())));
                            }
                            StrPart::Interp(e) => {
                                self.operand(e);
                                self.emit(Op::ToStr);
                            }
                        }
                    }
                    self.emit(Op::Concat(u32_of(parts.len())))
                }
            }
        };
    }

    fn name(&mut self, id: &Ident) {
        if let Some(v) = self.lookup(&id.name) {
            self.emit(Op::Var(v));
            self.emit(Op::Read);
            return;
        }
        let m = self.module();
        if let Some(ItemRef::Fn(f)) = self.prog.lookup(m, &id.name) {
            self.emit(Op::FnValue(f));
            return;
        }
        if let Some((adt, vi)) = self.variant(&id.name) {
            if self.variant_arity(adt, vi) == 0 {
                self.emit(Op::MakeEnum {
                    adt,
                    variant: u32_of(vi),
                    n: 0,
                });
                return;
            }
        }
        self.emit(fault(format!("unknown name `{}`", id.name)));
    }

    /// Returns true if `e` is a place below a local: the local, a field or an
    /// element. Sema checks a statement of this form as a plain use.
    fn local_place(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Name(id) => self.is_var(&id.name),
            ExprKind::Field { base, .. }
            | ExprKind::Index {
                base,
                index: Some(_),
            } => self.local_place(base),
            _ => false,
        }
    }

    /// Pushes the place that an expression names. Returns false, and emits
    /// nothing, if the expression is not a place.
    fn place(&mut self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Name(id) => match self.lookup(&id.name) {
                Some(v) => {
                    self.emit(Op::Var(v));
                    true
                }
                None => false,
            },
            ExprKind::Field { base, name } => {
                if matches!(base.kind, ExprKind::Lit(_)) || self.path_ref(base).is_some() {
                    return false;
                }
                self.place_or_temp(base);
                self.set_span(e.span);
                self.emit(Op::Field(Rc::from(name.name.as_str())));
                true
            }
            ExprKind::Index {
                base,
                index: Some(ix),
            } => {
                self.place_or_temp(base);
                self.expr(ix);
                self.set_span(e.span);
                self.emit(Op::Index);
                true
            }
            _ => false,
        }
    }

    /// Compiles an operand that is only read: a place stays a place, so a
    /// non-copy value does not move.
    fn operand(&mut self, e: &Expr) {
        if !self.place(e) {
            self.expr(e);
        }
    }

    fn place_or_temp(&mut self, e: &Expr) {
        if !self.place(e) {
            self.expr(e);
            self.emit(Op::ToTemp);
        }
    }

    fn borrow(&mut self, inner: &Expr) {
        if let ExprKind::Index { base, index: None } = &inner.kind {
            self.place_or_temp(base);
            self.emit(Op::BorrowAll);
            return;
        }
        if !self.place(inner) {
            self.expr(inner);
            self.emit(Op::ToTemp);
        }
        self.emit(Op::Borrow);
    }

    fn struct_lit(&mut self, path: &[Ident], fields: &[(Ident, Expr)]) {
        let Some(adt) = self.adt_by_path(path) else {
            self.emit(fault("unknown struct"));
            return;
        };
        let AdtKind::Struct(defs) = &self.prog.adts[adt].kind else {
            self.emit(fault("this type is not a struct"));
            return;
        };
        let total = u32_of(defs.len());
        let mut idx = Vec::new();
        for (name, value) in fields {
            let Some(i) = defs.iter().position(|d| d.name == name.name) else {
                self.emit(fault(format!("no field `{}`", name.name)));
                return;
            };
            idx.push(u32_of(i));
            self.expr(value);
        }
        self.emit(Op::MakeStruct {
            adt,
            fields: idx,
            total,
        });
    }

    /// Builds a struct from a call of its name. A named argument gives the
    /// field with its name, the others fill the free fields in order, and a
    /// trailing block goes to the last free field, as in semantic analysis. The
    /// arguments run in the order of the fields.
    fn positional_struct(&mut self, adt: AdtId, args: &[Arg], trailing: Option<&Expr>) {
        let AdtKind::Struct(defs) = &self.prog.adts[adt].kind else {
            self.emit(fault("this type has no constructor"));
            return;
        };
        let n = defs.len();
        let mut slots: Vec<Option<&Expr>> = vec![None; n];
        let mut pos = 0;
        for a in args {
            let idx = if let Some(nm) = &a.name {
                let Some(i) = defs.iter().position(|d| d.name == nm.name) else {
                    self.emit(fault(format!("no field `{}`", nm.name)));
                    return;
                };
                i
            } else {
                while pos < n && slots[pos].is_some() {
                    pos += 1;
                }
                pos
            };
            if let Some(s) = slots.get_mut(idx) {
                *s = Some(&a.value);
            }
        }
        if let Some(t) = trailing {
            if let Some(i) = slots.iter().rposition(Option::is_none) {
                slots[i] = Some(t);
            }
        }
        let mut fields = Vec::new();
        for (i, slot) in slots.iter().enumerate() {
            if let Some(e) = slot {
                self.fn_arg(e);
                fields.push(u32_of(i));
            }
        }
        self.emit(Op::MakeStruct {
            adt,
            fields,
            total: u32_of(n),
        });
    }

    fn closure(&mut self, params: &[Param], body: &Expr, kind: CodeKind) -> (CodeId, Vec<VarRef>) {
        let (id, named) = self.closure_named(params, body, kind);
        (id, named.into_iter().map(|(_, v)| v).collect())
    }

    /// Compiles a closure body. Returns the code and each capture with its name.
    fn closure_named(
        &mut self,
        params: &[Param],
        body: &Expr,
        kind: CodeKind,
    ) -> (CodeId, Vec<(String, VarRef)>) {
        let id = self.reserve();
        let m = self.module();
        let name = match kind {
            CodeKind::HandleBody => "handled computation".to_string(),
            _ => "closure".to_string(),
        };
        self.push_ctx(m, kind, name, true);
        self.set_span(body.span);
        for p in params {
            self.declare(&p.name.name);
        }
        self.top().n_params = u32_of(params.len());
        self.expr(body);
        self.emit(Op::Return);
        let ctx = self.pop_ctx();
        let caps = ctx.caps.clone();
        self.finish(id, ctx);
        (id, caps)
    }

    /// Compiles a value that a native function calls: closures become closure values.
    fn fn_arg(&mut self, e: &Expr) {
        self.expr(e);
    }

    // -----------------------------------------------------------------------
    // Calls
    // -----------------------------------------------------------------------

    /// Pushes the arguments of operation `op` of effect `e` in parameter order. A
    /// named argument goes to the parameter with its name, and a trailing block to
    /// the last free parameter, as in semantic analysis.
    fn op_args(&mut self, e: EffectId, op: usize, args: &[Arg], trailing: Option<&Expr>) -> u32 {
        let names: Vec<String> = self.prog.effects[e]
            .ops
            .get(op)
            .map(|o| o.param_names.clone())
            .unwrap_or_default();
        let n = names.len();
        let mut slots: Vec<Option<&Expr>> = vec![None; n];
        let mut pos = 0;
        for a in args {
            let idx = if let Some(nm) = &a.name {
                names.iter().position(|p| *p == nm.name)
            } else {
                while pos < n && slots[pos].is_some() {
                    pos += 1;
                }
                Some(pos)
            };
            if let Some(i) = idx.filter(|&i| i < n) {
                slots[i] = Some(&a.value);
            }
        }
        if let Some(t) = trailing {
            if let Some(i) = slots.iter().rposition(Option::is_none) {
                slots[i] = Some(t);
            }
        }
        for slot in &slots {
            match slot {
                Some(x) => self.fn_arg(x),
                None => {
                    self.emit(fault("an operation misses an argument"));
                }
            }
        }
        u32_of(n)
    }

    /// Pushes the arguments of a call of a method of a value or of a function
    /// item in a local. Semantic analysis gives the order of a call with named
    /// arguments (see [`ArgOrder`]): the arguments run in the order of the
    /// parameters. The other calls give their arguments in written order.
    fn ordered_args(&mut self, args: &[Arg], trailing: Option<&Expr>, span: Span) -> u32 {
        let unit = self
            .prog
            .mods
            .get(self.module().index())
            .map_or(0, |m| m.unit);
        let Some(order) = self.arg_order.get(&(unit, span.lo, span.hi)) else {
            return self.args(args, trailing);
        };
        let exprs: Vec<&Expr> = args.iter().map(|a| &a.value).chain(trailing).collect();
        for slot in order {
            match slot.and_then(|k| exprs.get(k as usize)) {
                Some(e) => self.fn_arg(e),
                None => {
                    self.emit(fault("a call misses an argument"));
                }
            }
        }
        u32_of(order.len())
    }

    fn args(&mut self, args: &[Arg], trailing: Option<&Expr>) -> u32 {
        for a in args {
            self.expr(&a.value);
        }
        if let Some(t) = trailing {
            self.fn_arg(t);
        }
        u32_of(args.len() + usize::from(trailing.is_some()))
    }

    fn call(&mut self, callee: &Expr, args: &[Arg], trailing: Option<&Expr>, span: Span) {
        let ExprKind::Name(id) = &callee.kind else {
            self.expr(callee);
            let n = self.args(args, trailing);
            self.set_span(span);
            self.emit(Op::CallValue(n));
            return;
        };
        if let Some(v) = self.lookup(&id.name) {
            self.emit(Op::Var(v));
            self.emit(Op::Read);
            let n = self.ordered_args(args, trailing, span);
            self.set_span(span);
            self.emit(Op::CallValue(n));
            return;
        }
        match id.name.as_str() {
            "print" => {
                for a in args {
                    self.operand(&a.value);
                }
                let n = u32_of(args.len());
                self.set_span(span);
                self.emit(Op::Print(n));
                return;
            }
            "fork" => {
                let mut spans = Vec::new();
                for e in args.iter().map(|a| &a.value).chain(trailing) {
                    self.fn_arg(e);
                    spans.push(e.span);
                }
                self.set_span(span);
                self.emit(Op::Fork {
                    n: u32_of(spans.len()),
                    spans,
                });
                return;
            }
            _ => {}
        }
        let m = self.module();
        match self.prog.lookup(m, &id.name) {
            Some(ItemRef::Fn(f)) => return self.call_fn(f, false, args, trailing, span),
            Some(ItemRef::Adt(a)) => return self.positional_struct(a, args, trailing),
            _ => {}
        }
        if let Some((adt, vi)) = self.variant(&id.name) {
            let n = self.args(args, trailing);
            self.emit(Op::MakeEnum {
                adt,
                variant: u32_of(vi),
                n,
            });
            return;
        }
        if let Some((e, op)) = self.prog.find_op(self.module(), &id.name) {
            let n = self.op_args(e, op, args, trailing);
            self.set_span(span);
            self.emit(Op::Perform { effect: e, op, n });
            return;
        }
        self.emit(fault(format!("unknown function `{}`", id.name)));
    }

    /// Calls a function item. Named arguments go to their parameter, and a trailing
    /// block goes to the last free parameter, as in semantic analysis.
    fn call_fn(&mut self, f: FnId, recv: bool, args: &[Arg], trailing: Option<&Expr>, span: Span) {
        let params: Vec<String> = self.sigs.get(f.index()).map_or_else(
            || {
                self.prog.fns[f]
                    .decl
                    .params
                    .iter()
                    .map(|p| p.name.name.clone())
                    .collect()
            },
            |s| s.params.iter().map(|p| p.name.clone()).collect(),
        );
        let n = params.len();
        let first = usize::from(recv);
        let mut slots: Vec<Option<&Expr>> = vec![None; n];
        let mut pos = first;
        for a in args {
            let idx = if let Some(nm) = &a.name {
                params.iter().position(|p| *p == nm.name)
            } else {
                while pos < n && slots[pos].is_some() {
                    pos += 1;
                }
                Some(pos)
            };
            if let Some(i) = idx.filter(|&i| i < n && i >= first) {
                slots[i] = Some(&a.value);
            }
        }
        if let Some(t) = trailing {
            if let Some(i) = slots
                .iter()
                .rposition(Option::is_none)
                .filter(|&i| i >= first)
            {
                slots[i] = Some(t);
            }
        }
        let sim_run = self.is_sim_run(f);
        for (i, slot) in slots.iter().enumerate().skip(first) {
            match slot {
                Some(e) => self.fn_arg(e),
                // `sim.run` has a default number of simulated workers.
                None if sim_run && params.get(i).is_some_and(|p| p == "workers") => {
                    let w = i64::try_from(crate::machine::SIM_WORKERS).unwrap_or(4);
                    self.emit(Op::Int(w));
                }
                None => {
                    self.emit(fault("a call misses an argument"));
                }
            }
        }
        self.set_span(span);
        self.emit(Op::Call { f, n: u32_of(n) });
    }

    /// Returns true for `sim.run` of the prelude.
    fn is_sim_run(&self, f: FnId) -> bool {
        let def = &self.prog.fns[f];
        def.is_std
            && def.path == "run"
            && self
                .prog
                .mods
                .get(def.module.index())
                .is_some_and(|m| m.name == "sim")
    }

    fn method_call(&mut self, recv: &Expr, method: &Ident, args: &[Arg], trailing: Option<&Expr>) {
        let span = self.top().span;
        match self.path_ref(recv) {
            Some(PathRef::Mod(m)) => {
                match self.prog.lookup_in(m, &method.name) {
                    Some(ItemRef::Fn(f)) => self.call_fn(f, false, args, trailing, span),
                    Some(ItemRef::Adt(a)) => self.positional_struct(a, args, trailing),
                    _ => {
                        self.emit(fault(format!(
                            "no function `{}` in this module",
                            method.name
                        )));
                    }
                }
                return;
            }
            Some(PathRef::Adt(a)) => {
                if let Some(&f) = self.prog.methods.get(&(a, method.name.clone())) {
                    self.call_fn(f, false, args, trailing, span);
                    return;
                }
                if let AdtKind::Enum(vs) = &self.prog.adts[a].kind {
                    if let Some(vi) = vs.iter().position(|v| v.name == method.name) {
                        let n = self.args(args, trailing);
                        self.emit(Op::MakeEnum {
                            adt: a,
                            variant: u32_of(vi),
                            n,
                        });
                        return;
                    }
                }
                self.emit(fault(format!(
                    "`{}` has no function `{}`",
                    self.prog.adts[a].name, method.name
                )));
                return;
            }
            Some(PathRef::Effect(e)) => {
                match self.prog.effects[e]
                    .ops
                    .iter()
                    .position(|o| o.name == method.name)
                {
                    Some(op) => {
                        let n = self.op_args(e, op, args, trailing);
                        self.set_span(span);
                        self.emit(Op::Perform { effect: e, op, n });
                    }
                    None => {
                        self.emit(fault(format!("no operation `{}`", method.name)));
                    }
                }
                return;
            }
            None => {}
        }
        self.place_or_temp(recv);
        let arg_span = args
            .first()
            .map(|a| a.value.span)
            .or_else(|| trailing.map(|t| t.span))
            .unwrap_or(span);
        let n = self.ordered_args(args, trailing, span);
        self.set_span(span);
        self.emit(Op::CallMethod {
            name: Rc::from(method.name.as_str()),
            n,
            arg_span,
        });
    }
}

fn empty_code() -> Code {
    Code {
        name: String::new(),
        kind: CodeKind::Closure,
        ops: vec![Op::Unit, Op::Return],
        spans: vec![Span::default(); 2],
        n_slots: 0,
        n_params: 0,
        unit: usize::MAX,
        temp_slots: 0,
        locs: Vec::new(),
    }
}
