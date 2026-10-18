//! Lowering of function bodies to facts.
//!
//! The lowering walks the AST once. It infers types, computes places, and writes a
//! control-flow graph where each node does one thing. A node uses its inputs
//! before it mutates places, so a use and a mutation can share a node.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use weft_facts::{
    CapId, FnFacts, HandlerInfo, NodeId, PlaceId, RootId, RootKind, Span, Step, StepKind, TaskId,
    TaskKind, VarId, VarInfo, VarKind,
};
use weft_syntax::ast::{
    self, Arg, AssignOp, BinOp, Block, Expr, ExprKind, Lit, Pattern, Stmt, StmtKind, StrPart, UnOp,
};
use weft_syntax::diag::Diagnostic;

use crate::effects;
use crate::program::{
    elem_step, field_step, AdtKind, Builtins, Deref, EffectSig, FnId, FnSig, ItemRef, ModId,
    Program, SigPlace, SigRoot, SigStep, PRELUDE,
};
use crate::types::{subst, Display, FnTy, Infer, IntTy, Ty};

mod call;
mod expr;
mod fnval;
mod stmt;

use fnval::{Applied, FnInfo, OpArg, Reach};

/// What a body does, in the places of the enclosing function.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// Mutated places.
    pub muts: BTreeSet<PlaceId>,
    /// Read places.
    pub reads: BTreeSet<PlaceId>,
    /// Effects that no local handler handles.
    pub escapes: BTreeSet<String>,
    /// Local capabilities used.
    pub performs: BTreeSet<CapId>,
    /// Some node can abort.
    pub may_abort: bool,
    /// Some node can resume a `multi` continuation.
    pub multi: bool,
    /// Function parameters that the body calls.
    pub passthrough: BTreeSet<usize>,
    /// Roots made inside the body. They are not visible outside.
    pub own_roots: BTreeSet<RootId>,
    /// Variables of the enclosing function that the body uses.
    pub captures: BTreeSet<VarId>,
    /// Captured variables that the body moves.
    pub moved_captures: BTreeSet<VarId>,
    /// Owners that the body declares. They go out of scope when the body returns.
    pub dropped: BTreeSet<VarId>,
    /// The places that the result of a closure points into.
    pub ret_refs: Vec<PlaceId>,
    /// The root place of each reference parameter of a function value, with the
    /// parameter index. A place below it stands for a place that the call gives.
    pub param_roots: BTreeMap<PlaceId, usize>,
    /// The value is a closure of the body, or can be one: it moves, it is not copied.
    pub literal: bool,
    /// Function items that a call of the value can call. Their effects resolve where it is called.
    pub items: BTreeSet<FnId>,
    /// Function parameters that the value can be.
    pub params: BTreeSet<usize>,
    /// The value can be a function value that the body does not know.
    pub unknown: bool,
    /// Effects that a call of the value performs where it is called: the effect
    /// rows of the parameters and unknown values that it can be.
    pub row: BTreeSet<String>,
    /// Places that the body gives to its function parameters: the parameter, the
    /// argument position (`None`: any position), and the place.
    pub lent: Vec<(usize, Option<usize>, PlaceId)>,
    /// Places that the body gives to operations of local handlers: the capability,
    /// the operation and the argument position (`None`: any), and the place.
    pub op_args: Vec<(CapId, Option<usize>, Option<usize>, PlaceId)>,
    /// The closures of the body that the value can be.
    pub members: BTreeSet<usize>,
    /// Function parameters that the body stores.
    pub stores: BTreeSet<usize>,
    /// Places that the body gives to code that can mutate through them: a function
    /// parameter, an unknown function value or an operation of an outer handler.
    pub lends: BTreeSet<PlaceId>,
}

impl Summary {
    /// Adds what `o` does: a call of the result can do either.
    fn union(&mut self, o: &Self) {
        self.muts.extend(o.muts.iter().copied());
        self.reads.extend(o.reads.iter().copied());
        self.escapes.extend(o.escapes.iter().cloned());
        self.performs.extend(o.performs.iter().copied());
        self.may_abort |= o.may_abort;
        self.multi |= o.multi;
        self.passthrough.extend(o.passthrough.iter().copied());
        self.own_roots.extend(o.own_roots.iter().copied());
        self.captures.extend(o.captures.iter().copied());
        self.moved_captures.extend(o.moved_captures.iter().copied());
        self.dropped.extend(o.dropped.iter().copied());
        self.ret_refs.extend(o.ret_refs.iter().copied());
        self.param_roots
            .extend(o.param_roots.iter().map(|(&r, &i)| (r, i)));
        self.literal |= o.literal;
        self.items.extend(o.items.iter().copied());
        self.params.extend(o.params.iter().copied());
        self.unknown |= o.unknown;
        self.row.extend(o.row.iter().cloned());
        self.lent.extend(o.lent.iter().copied());
        self.op_args.extend(o.op_args.iter().copied());
        self.members.extend(o.members.iter().copied());
        self.stores.extend(o.stores.iter().copied());
        self.lends.extend(o.lends.iter().copied());
    }
}

/// The result of lowering one function.
#[derive(Clone, Debug)]
pub struct Lowered {
    /// The facts.
    pub facts: FnFacts,
    /// The effects of the body, for signature inference.
    pub effects: EffectSig,
    /// Type and signature diagnostics.
    pub diags: Vec<Diagnostic>,
}

#[derive(Clone, Debug)]
struct ContInfo {
    arg: Ty,
    ret: Ty,
    multi: bool,
    muts: Vec<PlaceId>,
    cap: CapId,
}

#[derive(Clone, Debug)]
struct Local {
    name: String,
    var: VarId,
    ty: Ty,
    root: Option<PlaceId>,
    refs: Vec<PlaceId>,
    uniq: bool,
    task: Option<TaskId>,
    summary: Option<usize>,
    /// A function parameter: the summary index of its body and the parameter index.
    fn_param: Option<(usize, usize)>,
    cont: Option<ContInfo>,
    /// The local has a value: a new value joins the function values.
    bound: bool,
}

#[derive(Clone, Debug, Default)]
struct Val {
    ty: Ty,
    refs: Vec<PlaceId>,
    var: Option<VarId>,
    local: Option<usize>,
    uniq: bool,
    summary: Option<usize>,
    task: Option<TaskId>,
    parts: Option<Vec<Self>>,
    place: Option<LVal>,
    fn_param: Option<(usize, usize)>,
    item: Option<FnId>,
}

#[derive(Clone, Debug, Default)]
struct LVal {
    places: Vec<PlaceId>,
    ty: Ty,
    owner: Option<usize>,
    through_ref: bool,
    uniq: bool,
    /// The `Rc` handles on the way to the place. The place stays valid only
    /// while each handle keeps its value. A reference to the place also points
    /// into these handle places.
    deps: Vec<PlaceId>,
}

struct Frame {
    names: Vec<(String, usize)>,
    barrier: Option<usize>,
}

struct HandlerFrame {
    effect: String,
    cap: CapId,
    multi: bool,
}

struct LoopFrame {
    header: NodeId,
    exit: NodeId,
    frames: usize,
}

/// Returns the effect row of a function type.
fn fn_row(t: &Ty) -> Option<Vec<String>> {
    match t {
        Ty::Fn(f) => f.effects.clone(),
        _ => None,
    }
}

/// The span of the value of a block: its last statement.
fn block_tail(b: &Block) -> Span {
    match b.stmts.last() {
        Some(Stmt {
            kind: StmtKind::Expr(e),
            ..
        }) => expr_tail(e),
        Some(s) => s.span,
        None => b.span,
    }
}

/// The span of the value of an expression: the last statement of a block.
fn expr_tail(e: &Expr) -> Span {
    match &e.kind {
        ExprKind::Block(b) => block_tail(b),
        _ => e.span,
    }
}

/// A path that names something other than a value.
enum PathRef {
    Mod(ModId),
    Adt(usize),
    Effect(usize),
}

/// The lowering state of one function.
pub struct Lower<'p> {
    prog: &'p Program,
    sigs: &'p [FnSig],
    b: Builtins,
    module: ModId,
    /// The facts being written.
    pub facts: FnFacts,
    diags: Vec<Diagnostic>,
    inf: Infer,
    locals: Vec<Local>,
    frames: Vec<Frame>,
    sums: Vec<Summary>,
    closures: Vec<Summary>,
    handlers: Vec<HandlerFrame>,
    loops: Vec<LoopFrame>,
    cur: Option<NodeId>,
    pend_uses: Vec<VarId>,
    pend_reads: Vec<PlaceId>,
    groups: BTreeMap<usize, PlaceId>,
    scopes: Vec<Vec<TaskId>>,
    ret_ty: Ty,
    in_test: bool,
    library: bool,
    self_fn: Option<FnId>,
    split: u32,
    cap_calls: Vec<(NodeId, CapId)>,
    resumes: Vec<(NodeId, CapId)>,
    match_moves: bool,
    match_deps: Vec<PlaceId>,
    /// The handle places of `LVal::deps`.
    dep_places: BTreeSet<PlaceId>,
    /// The open statements: the frame depth at the start, and the owners of
    /// the temporaries that go out of scope at the end.
    stmt_temps: Vec<(usize, Vec<VarId>)>,
    /// The function values that the function returns.
    rets: Vec<fnval::RowFn>,
    /// The places that nodes give to operations of local handlers.
    op_args: Vec<OpArg>,
    /// Function values that the body stores where it does not follow them.
    escaped: Vec<fnval::RowFn>,
    /// The nodes where a stored function value can run.
    reaches: Vec<Reach>,
    /// The nodes where a summary runs.
    applied: Vec<Applied>,
}

impl<'p> Lower<'p> {
    /// Makes a lowering state.
    pub fn new(
        prog: &'p Program,
        sigs: &'p [FnSig],
        module: ModId,
        name: &str,
        library: bool,
    ) -> Self {
        Self {
            prog,
            sigs,
            b: prog.builtins(),
            module,
            facts: FnFacts {
                name: name.into(),
                library,
                ..FnFacts::default()
            },
            diags: Vec::new(),
            inf: Infer::default(),
            locals: Vec::new(),
            frames: vec![Frame {
                names: Vec::new(),
                barrier: None,
            }],
            sums: vec![Summary::default()],
            closures: Vec::new(),
            handlers: Vec::new(),
            loops: Vec::new(),
            cur: None,
            pend_uses: Vec::new(),
            pend_reads: Vec::new(),
            groups: BTreeMap::new(),
            scopes: Vec::new(),
            ret_ty: Ty::Unit,
            in_test: false,
            library,
            self_fn: None,
            split: 0,
            cap_calls: Vec::new(),
            resumes: Vec::new(),
            match_moves: false,
            match_deps: Vec::new(),
            dep_places: BTreeSet::new(),
            stmt_temps: Vec::new(),
            rets: Vec::new(),
            op_args: Vec::new(),
            escaped: Vec::new(),
            reaches: Vec::new(),
            applied: Vec::new(),
        }
    }

    fn err(&mut self, code: &str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, msg, span));
    }

    fn show(&self, t: &Ty) -> String {
        let names = self.prog.adt_names();
        Display {
            ty: &self.inf.resolve(t),
            names: &names,
        }
        .to_string()
    }

    fn unify(&mut self, a: &Ty, b: &Ty, span: Span) {
        if !self.inf.unify(a, b) {
            let (x, y) = (self.show(a), self.show(b));
            self.err(
                "W0102",
                format!("type mismatch: expected `{x}`, found `{y}`"),
                span,
            );
        }
    }

    // -----------------------------------------------------------------------
    // Nodes and facts
    // -----------------------------------------------------------------------

    fn emit(&mut self, span: Span, label: &str, detail: String) -> NodeId {
        let n = self.facts.add_node(span, label, detail);
        if let Some(c) = self.cur {
            self.facts.cfg_edge.push((c, n));
        }
        self.cur = Some(n);
        for v in std::mem::take(&mut self.pend_uses) {
            self.facts.uses.push((v, n));
        }
        for p in std::mem::take(&mut self.pend_reads) {
            self.facts.reads_at.push((n, p));
        }
        n
    }

    /// Starts a new component: a node with no predecessor.
    fn start(&mut self, span: Span, label: &str) -> NodeId {
        self.cur = None;
        self.emit(span, label, String::new())
    }

    /// Writes the queued uses and reads into a new node on the current path.
    /// Call it before control leaves a branch, a loop body or a component, so
    /// that the queue does not go into a node of another path.
    fn flush(&mut self, span: Span) {
        if self.pend_uses.is_empty() && self.pend_reads.is_empty() {
            return;
        }
        if self.cur.is_none() {
            // The queue belongs to code that cannot run.
            self.pend_uses.clear();
            self.pend_reads.clear();
            return;
        }
        let _ = self.emit(span, "use", String::new());
    }

    /// Takes the queue away before a new component starts.
    fn take_pending(&mut self) -> (Vec<VarId>, Vec<PlaceId>) {
        (
            std::mem::take(&mut self.pend_uses),
            std::mem::take(&mut self.pend_reads),
        )
    }

    /// Puts back a queue that `take_pending` took.
    fn restore_pending(&mut self, saved: (Vec<VarId>, Vec<PlaceId>)) {
        let (mut uses, mut reads) = saved;
        uses.append(&mut self.pend_uses);
        reads.append(&mut self.pend_reads);
        self.pend_uses = uses;
        self.pend_reads = reads;
    }

    /// Holds a reference value in a temporary from this point, so that later
    /// code that invalidates it is seen. The consumer must use the temporary.
    fn hold(&mut self, v: &Val, name: &str, span: Span) -> Option<VarId> {
        if v.var.is_some() {
            return None;
        }
        self.hold_as(v, name, VarKind::Temp, span)
    }

    /// Holds an operand while the later operands run. It holds the value of a
    /// variable too, because a later operand can give the variable a new value.
    fn hold_later(&mut self, v: &Val, name: &str, span: Span) -> Option<VarId> {
        self.hold_as(v, name, VarKind::Temp, span)
    }

    /// Returns the variable that a call uses for an argument: a held copy if
    /// later arguments follow, else the variable of the value or a temporary.
    fn hold_operand(&mut self, v: &Val, later: bool, span: Span) -> Option<VarId> {
        if later {
            self.hold_later(v, "argument", span).or(v.var)
        } else {
            v.var.or_else(|| self.hold(v, "argument", span))
        }
    }

    /// Holds a reference value in a new variable of kind `kind`.
    fn hold_as(&mut self, v: &Val, name: &str, kind: VarKind, span: Span) -> Option<VarId> {
        if v.refs.is_empty() || self.cur.is_none() {
            return None;
        }
        let info = self.var_info(name, kind, span, &v.ty, v.uniq);
        let var = self.facts.add_var(info);
        let n = self.emit(span, name, String::new());
        self.bind(var, n);
        for &p in &v.refs {
            self.facts.points_into.push((var, p));
        }
        Some(var)
    }

    fn sum(&mut self) -> &mut Summary {
        let i = self.sums.len() - 1;
        &mut self.sums[i]
    }

    fn mutate(&mut self, n: NodeId, p: PlaceId) {
        self.facts.mutates_at.push((n, p));
        self.sum().muts.insert(p);
    }

    fn read(&mut self, p: PlaceId) {
        self.pend_reads.push(p);
        self.sum().reads.insert(p);
    }

    fn use_local(&mut self, l: usize) {
        let v = self.locals[l].var;
        self.pend_uses.push(v);
        self.note_capture(l);
    }

    fn note_capture(&mut self, l: usize) {
        // A local declared outside the current closure is a capture of it.
        let v = self.locals[l].var;
        let depth = self.local_frame(l);
        for (fi, f) in self.frames.iter().enumerate() {
            if let Some(si) = f.barrier {
                if fi > depth {
                    self.sums[si].captures.insert(v);
                }
            }
        }
    }

    fn local_frame(&self, l: usize) -> usize {
        self.frames
            .iter()
            .rposition(|f| f.names.iter().any(|(_, i)| *i == l))
            .unwrap_or(0)
    }

    fn bind(&mut self, v: VarId, n: NodeId) {
        self.facts.rebound_at.push((v, n));
    }

    fn move_var(&mut self, v: VarId, n: NodeId) {
        self.facts.uses.push((v, n));
        self.facts.moved_at.push((v, n));
        let sums_len = self.sums.len();
        for s in &mut self.sums[..sums_len] {
            if s.captures.contains(&v) {
                s.moved_captures.insert(v);
            }
        }
    }

    fn abortive(&mut self, n: NodeId) {
        self.facts.may_abort.push(n);
        self.sum().may_abort = true;
    }

    fn multi_node(&mut self, n: NodeId) {
        self.facts.multi_at.push(n);
        self.sum().multi = true;
    }

    /// Records that node `n` performs effect `e`. A lexical handler takes it if one is in scope.
    fn perform_effect(&mut self, n: NodeId, e: &str) {
        if let Some(h) = self.handlers.iter().rev().find(|h| h.effect == e) {
            let cap = h.cap;
            let multi = h.multi;
            self.facts.performs_at.push((n, cap));
            self.sum().performs.insert(cap);
            if multi {
                self.multi_node(n);
            }
        } else {
            self.facts.escapes_at.push((n, e.to_string()));
            self.sum().escapes.insert(e.to_string());
            if self.effect_has_multi(e) {
                self.multi_node(n);
            }
        }
    }

    fn effect_has_multi(&self, e: &str) -> bool {
        self.prog
            .effect_named(self.module, e)
            .is_some_and(|id| self.prog.effects[id].has_multi())
    }

    // -----------------------------------------------------------------------
    // Places
    // -----------------------------------------------------------------------

    fn root(&mut self, name: &str, kind: RootKind) -> PlaceId {
        let p = self.facts.add_root(name, kind);
        let r = self.facts.place(p).root;
        self.sum().own_roots.insert(r);
        p
    }

    /// Makes the root place of a temporary value. A temporary that is not plain
    /// data goes out of scope at the end of its statement, as in the interpreter.
    fn temp_root(&mut self, span: Span, ty: &Ty) -> PlaceId {
        let r = self.root("temporary", RootKind::Local);
        if !self.may_free(ty) {
            return r;
        }
        let shown = self.show(ty);
        let var = self
            .facts
            .add_var(VarInfo::plain("temporary", VarKind::Temp, span, shown));
        self.facts.owner.push((r, var));
        if let Some(si) = self.frames.iter().rev().find_map(|f| f.barrier) {
            self.sums[si].dropped.insert(var);
        }
        if let Some((_, temps)) = self.stmt_temps.last_mut() {
            temps.push(var);
        }
        r
    }

    /// Opens a statement. The temporaries from here go out of scope at its end.
    fn open_stmt(&mut self) {
        let depth = self.frames.len();
        self.stmt_temps.push((depth, Vec::new()));
    }

    /// Closes a statement: its temporaries go out of scope at its end.
    fn close_stmt(&mut self, span: Span) {
        let Some((_, temps)) = self.stmt_temps.pop() else {
            return;
        };
        if temps.is_empty() || self.cur.is_none() {
            return;
        }
        let end = Span::new(span.hi.saturating_sub(1), span.hi);
        let n = self.emit(end, "end of statement", String::new());
        for v in temps {
            self.facts.scope_end.push((v, n));
        }
    }

    fn group_root(&mut self, adt: usize) -> PlaceId {
        if let Some(&p) = self.groups.get(&adt) {
            return p;
        }
        let name = self.prog.adts[adt].name.clone();
        let p = self.facts.add_root(name, RootKind::Group);
        self.groups.insert(adt, p);
        p
    }

    fn child(&mut self, p: PlaceId, s: Step, text: &str) -> PlaceId {
        self.facts.child(p, s, text)
    }

    const fn fresh_split(&mut self) -> u32 {
        self.split += 1;
        self.split
    }

    /// Substitutes a signature place with the places of the arguments.
    fn subst_place(
        &mut self,
        sp: &SigPlace,
        args: &[Vec<PlaceId>],
        split_base: u32,
    ) -> Vec<PlaceId> {
        let bases = match &sp.root {
            SigRoot::Param(i) => args.get(*i).cloned().unwrap_or_default(),
            SigRoot::Group(a) => vec![self.group_root(*a)],
        };
        let mut out = Vec::new();
        for base in bases {
            let mut p = base;
            for st in &sp.steps {
                p = match st {
                    SigStep::Step(s, text) => self.child(p, *s, text),
                    SigStep::Wild => self.facts.wildcard(p),
                    SigStep::Seg {
                        label,
                        hi,
                        unstable,
                    } => {
                        let split = split_base * 64 + u32::try_from(*label).unwrap_or(0);
                        let text = if *hi { "[k..]" } else { "[..k]" };
                        self.child(
                            p,
                            Step {
                                kind: StepKind::Seg { split, hi: *hi },
                                unstable: *unstable,
                            },
                            text,
                        )
                    }
                };
            }
            out.push(p);
        }
        out
    }

    /// Returns the handle places of `Rc` handles at `ps`. A reference through a
    /// handle depends on the handle: a move, a scope end or a new value of the
    /// handle can free the object.
    fn handle_deps(&mut self, ps: &[PlaceId]) -> Vec<PlaceId> {
        let step = Step {
            kind: StepKind::Deref,
            unstable: true,
        };
        let mut out = Vec::new();
        for &p in ps {
            let d = self.child(p, step, ".*");
            self.dep_places.insert(d);
            out.push(d);
        }
        out
    }

    /// Returns the handle places of the `Rc` handles in a value of type `ty` at
    /// place `p`. A group place that a callee reaches through the value depends
    /// on them. Past the depth limit, it depends on any handle inside `p`.
    fn inner_handle_deps(&mut self, p: PlaceId, ty: &Ty, depth: usize) -> Vec<PlaceId> {
        if depth > 4 {
            let any = self.facts.wildcard(p);
            return self.handle_deps(&[any]);
        }
        let t = self.inf.deep(ty);
        let mut out = Vec::new();
        match &t {
            Ty::Ref(_) => out = self.handle_deps(&[p]),
            Ty::Tuple(ts) => {
                for (i, ft) in ts.iter().enumerate() {
                    let step = Step {
                        kind: StepKind::Field {
                            id: u32::try_from(i).unwrap_or(0),
                        },
                        unstable: false,
                    };
                    let c = self.child(p, step, &format!(".{i}"));
                    out.extend(self.inner_handle_deps(c, ft, depth + 1));
                }
            }
            Ty::Adt(a, args) => match &self.prog.adts[*a].kind {
                AdtKind::Extern {
                    deref: Some(Deref::Group),
                    ..
                } => out = self.handle_deps(&[p]),
                AdtKind::Struct(_) | AdtKind::Enum(_) => {
                    let names: Vec<String> = match &self.prog.adts[*a].kind {
                        AdtKind::Struct(fs) => fs.iter().map(|f| f.name.clone()).collect(),
                        AdtKind::Enum(vs) => vs.iter().map(|v| v.name.clone()).collect(),
                        AdtKind::Extern { .. } => Vec::new(),
                    };
                    for name in &names {
                        if let Some((steps, next, _)) = field_step(self.prog, &t, name) {
                            let mut c = p;
                            for (st, text) in &steps {
                                c = self.child(c, *st, text);
                            }
                            out.extend(self.inner_handle_deps(c, &next, depth + 1));
                        }
                    }
                }
                AdtKind::Extern { .. } => {
                    if let Some((Some(step), elem)) = elem_step(self.prog, &t) {
                        let c = self.child(p, step, "[]");
                        out.extend(self.inner_handle_deps(c, &elem, depth + 1));
                    } else if let (AdtKind::Extern { deref: Some(d), .. }, Some(inner)) =
                        (&self.prog.adts[*a].kind, args.first())
                    {
                        let step = Step {
                            kind: StepKind::Deref,
                            unstable: *d == Deref::Unstable,
                        };
                        let inner = inner.clone();
                        let c = self.child(p, step, "");
                        out.extend(self.inner_handle_deps(c, &inner, depth + 1));
                    }
                }
            },
            _ => {}
        }
        out
    }

    /// Returns the handle places that a group place in a call result depends
    /// on: the handle places of the arguments, and the `Rc` handles inside the
    /// values that the reference arguments point to.
    fn group_arg_deps(&mut self, args: &[Vec<PlaceId>], ptys: &[Ty]) -> Vec<PlaceId> {
        let mut out = Vec::new();
        for (i, ps) in args.iter().enumerate() {
            let pointee = match ptys.get(i).map(|t| self.inf.shallow(t)) {
                Some(Ty::Ref(inner)) => Some(*inner),
                _ => None,
            };
            for &p in ps {
                if self.is_dep(p) {
                    out.push(p);
                } else if let Some(t) = &pointee {
                    out.extend(self.inner_handle_deps(p, t, 0));
                }
            }
        }
        out.sort();
        out.dedup();
        out
    }

    /// Returns true if `p` is a handle place of `handle_deps` or inside one.
    fn is_dep(&self, p: PlaceId) -> bool {
        let mut at = Some(p);
        while let Some(a) = at {
            if self.dep_places.contains(&a) {
                return true;
            }
            at = self.facts.place(a).parent;
        }
        false
    }

    /// Splits the places of a reference into the places it names and its handle places.
    fn split_deps(&self, refs: &[PlaceId]) -> (Vec<PlaceId>, Vec<PlaceId>) {
        refs.iter().partition(|&&p| !self.is_dep(p))
    }

    /// Returns true if the signature place `a` allows a reference into `r`.
    /// Below a plain place only stable steps can follow, because a caller sees
    /// the reference at `a`. Below a wildcard place any step can follow.
    fn sig_allows(&self, a: PlaceId, r: PlaceId) -> bool {
        let (pa, pr) = (self.facts.place(a), self.facts.place(r));
        if pa.root != pr.root {
            return false;
        }
        match (pa.is_wildcard(), pa.parent) {
            (true, Some(base)) => {
                weft_verified::places::within(&pr.steps, &self.facts.place(base).steps)
            }
            _ => {
                weft_verified::places::within(&pr.steps, &pa.steps)
                    && pr.steps[pa.steps.len()..].iter().all(|s| !s.unstable)
            }
        }
    }

    /// Returns true if `r` is inside `a` only through an unstable step below it.
    fn below_unstable(&self, a: PlaceId, r: PlaceId) -> bool {
        let (pa, pr) = (self.facts.place(a), self.facts.place(r));
        pa.root == pr.root
            && !pa.is_wildcard()
            && weft_verified::places::within(&pr.steps, &pa.steps)
            && !self.sig_allows(a, r)
    }

    fn place_text(&self, ps: &[PlaceId]) -> String {
        let v: Vec<&str> = ps
            .iter()
            .map(|p| self.facts.place(*p).display.as_str())
            .collect();
        v.join(" | ")
    }

    // -----------------------------------------------------------------------
    // Locals
    // -----------------------------------------------------------------------

    fn lookup_local(&self, name: &str) -> Option<usize> {
        for f in self.frames.iter().rev() {
            if let Some((_, i)) = f.names.iter().rev().find(|(n, _)| n == name) {
                return Some(*i);
            }
        }
        None
    }

    fn var_info(&self, name: &str, kind: VarKind, span: Span, ty: &Ty, uniq: bool) -> VarInfo {
        let t = self.inf.resolve(ty);
        let mut v = VarInfo::plain(name, kind, span, self.show(&t));
        v.linear = self.is_linear(&t);
        v.has_on_abort = self.has_on_abort(&t);
        v.immovable = self.is_immovable(&t);
        v.nonportable = self.is_nonportable(&t);
        v.uniq = uniq;
        v.once = v.linear || uniq || matches!(kind, VarKind::Continuation);
        v
    }

    fn new_local(&mut self, name: &str, kind: VarKind, span: Span, ty: Ty, uniq: bool) -> usize {
        let info = self.var_info(name, kind, span, &ty, uniq);
        let var = self.facts.add_var(info);
        self.locals.push(Local {
            name: name.into(),
            var,
            ty,
            root: None,
            refs: Vec::new(),
            uniq,
            task: None,
            summary: None,
            fn_param: None,
            cont: None,
            bound: false,
        });
        let l = self.locals.len() - 1;
        let top = self.frames.len() - 1;
        self.frames[top].names.push((name.into(), l));
        l
    }

    /// Gives local `l` the root place `r`: the local owns the memory under `r`.
    fn set_root(&mut self, l: usize, r: PlaceId) {
        self.locals[l].root = Some(r);
        let var = self.locals[l].var;
        self.facts.owner.push((r, var));
        let depth = self.local_frame(l);
        if let Some(si) = self.frames[..=depth].iter().rev().find_map(|f| f.barrier) {
            self.sums[si].dropped.insert(var);
        }
    }

    /// Gives a local the value `v` at node `n`.
    fn assign_local(&mut self, l: usize, v: &Val, n: NodeId) {
        let var = self.locals[l].var;
        self.bind(var, n);
        for &p in &v.refs {
            self.facts.points_into.push((var, p));
            if !self.locals[l].refs.contains(&p) {
                self.locals[l].refs.push(p);
            }
        }
        if v.task.is_some() {
            self.locals[l].task = v.task;
        }
        // A function value. A new value of the local joins the old one: a later
        // call can call either.
        if let Ty::Fn(fty) = self.inf.shallow(&self.locals[l].ty) {
            let new = (self.fn_info(v), fn_row(&self.inf.shallow(&v.ty)));
            let info = if self.locals[l].bound {
                let old = (self.local_fn_info(l), fty.effects.clone());
                self.join_fn(&old, &new)
            } else {
                new.0
            };
            self.locals[l].summary = info.summary;
            self.locals[l].fn_param = info.param;
        }
        self.locals[l].bound = true;
        if v.uniq {
            self.locals[l].uniq = true;
            self.facts.vars[var.index()].uniq = true;
            self.facts.vars[var.index()].once = true;
        }
        if let Some(s) = v.summary {
            if self.closure_is_once(s) {
                self.facts.vars[var.index()].once = true;
            }
        }
        // An owned value gets a root place.
        if !matches!(self.inf.shallow(&self.locals[l].ty), Ty::Ref(_))
            && self.locals[l].root.is_none()
        {
            let name = self.locals[l].name.clone();
            let r = self.root(&name, RootKind::Local);
            self.set_root(l, r);
        }
    }

    fn closure_is_once(&self, s: usize) -> bool {
        let sum = &self.closures[s];
        sum.moved_captures.iter().any(|v| !self.is_copy_var(*v))
    }

    fn is_copy_var(&self, v: VarId) -> bool {
        self.locals
            .iter()
            .find(|l| l.var == v)
            .is_some_and(|l| self.is_copy(&l.ty))
    }

    // -----------------------------------------------------------------------
    // Type properties
    // -----------------------------------------------------------------------

    pub(super) fn adt_fields(&self, t: &Ty) -> Vec<Ty> {
        match t {
            Ty::Adt(a, args) => match &self.prog.adts[*a].kind {
                AdtKind::Struct(fs) => fs.iter().map(|f| subst(&f.ty, args)).collect(),
                AdtKind::Enum(vs) => vs
                    .iter()
                    .flat_map(|v| v.fields.iter().map(|t| subst(t, args)))
                    .collect(),
                AdtKind::Extern { .. } => args.clone(),
            },
            Ty::Tuple(ts) => ts.clone(),
            Ty::Array(t, _) => vec![(**t).clone()],
            _ => Vec::new(),
        }
    }

    fn deep_any(&self, t: &Ty, pred: &dyn Fn(&Self, &Ty) -> bool, depth: usize) -> bool {
        if depth > 6 {
            return false;
        }
        let t = self.inf.shallow(t);
        if pred(self, &t) {
            return true;
        }
        if matches!(t, Ty::Ref(_) | Ty::Fn(_)) {
            return false;
        }
        self.adt_fields(&t)
            .iter()
            .any(|f| self.deep_any(f, pred, depth + 1))
    }

    /// Returns true if a value of type `t` can hold a reference.
    fn holds_refs(&self, t: &Ty) -> bool {
        self.deep_any(t, &|_, t| matches!(t, Ty::Ref(_) | Ty::Slice(_)), 0)
    }

    fn is_linear(&self, t: &Ty) -> bool {
        self.deep_any(
            t,
            &|s, t| matches!(t, Ty::Adt(a, _) if s.prog.adts[*a].linear),
            0,
        )
    }

    fn has_on_abort(&self, t: &Ty) -> bool {
        match self.inf.shallow(t) {
            Ty::Adt(a, _) => self.prog.adts[a].has_on_abort || !self.is_linear(t),
            _ => true,
        }
    }

    fn is_immovable(&self, t: &Ty) -> bool {
        matches!(self.inf.shallow(t), Ty::Adt(a, _) if self.prog.adts[a].immovable)
    }

    fn is_nonportable(&self, t: &Ty) -> bool {
        self.deep_any(
            t,
            &|s, t| matches!(t, Ty::Adt(a, _) if s.prog.adts[*a].nonportable),
            0,
        )
    }

    /// Plain data is copied, not moved: integers, `bool`, references, and
    /// structs and enums of plain data.
    fn is_copy(&self, t: &Ty) -> bool {
        self.is_copy_d(t, 0)
    }

    fn is_copy_d(&self, t: &Ty, d: usize) -> bool {
        if d > 6 {
            return false;
        }
        match self.inf.shallow(t) {
            Ty::Int(_)
            | Ty::IntVar(_)
            | Ty::Bool
            | Ty::Unit
            | Ty::Never
            | Ty::Ref(_)
            | Ty::Error
            | Ty::Var(_)
            | Ty::Scope => true,
            Ty::Fn(f) => f.summary.is_none_or(|s| !self.closures[s].literal),
            Ty::Tuple(ts) => ts.iter().all(|t| self.is_copy_d(t, d + 1)),
            Ty::Adt(a, args) => {
                let def = &self.prog.adts[a];
                if def.linear || def.immovable {
                    return false;
                }
                match &def.kind {
                    AdtKind::Extern { .. } => {
                        def.copy
                            || (def.generics.is_empty()
                                && !def.nonportable
                                && !def.linear
                                && def.name != "String"
                                && self.capability_like(a))
                    }
                    AdtKind::Struct(fs) => fs
                        .iter()
                        .all(|f| self.is_copy_d(&subst(&f.ty, &args), d + 1)),
                    AdtKind::Enum(vs) => vs.iter().all(|v| {
                        v.fields
                            .iter()
                            .all(|t| self.is_copy_d(&subst(t, &args), d + 1))
                    }),
                }
            }
            _ => false,
        }
    }

    /// Returns true if the end of a variable of type `t` can free memory: the
    /// value is not plain data, or its type is not known yet.
    fn may_free(&self, t: &Ty) -> bool {
        let t = self.inf.shallow(t);
        matches!(t, Ty::Var(_)) || !self.is_copy(&t)
    }

    /// Scalars: integers, `bool`, unit, `String` and `Duration`. A loop or a match
    /// binds a scalar by value and other values by reference.
    fn is_scalar(&self, t: &Ty) -> bool {
        match self.inf.shallow(t) {
            Ty::Int(_) | Ty::IntVar(_) | Ty::Bool | Ty::Unit => true,
            Ty::Adt(a, _) => Some(a) == self.b.string || Some(a) == self.b.duration,
            _ => false,
        }
    }

    /// Capability types and opaque handles from the prelude are copied.
    fn capability_like(&self, a: usize) -> bool {
        self.prog.adts[a].module == PRELUDE
            || matches!(
                self.prog.adts[a].kind,
                AdtKind::Extern {
                    elem_unstable: None,
                    deref: None
                }
            )
    }

    fn deref_ty(&self, t: &Ty) -> Ty {
        match self.inf.shallow(t) {
            Ty::Ref(inner) => self.deref_ty(&inner),
            t => t,
        }
    }
}
