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
mod stmt;

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
    fn_param: Option<usize>,
    cont: Option<ContInfo>,
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
    fn_param: Option<usize>,
    item: Option<FnId>,
}

#[derive(Clone, Debug)]
struct LVal {
    places: Vec<PlaceId>,
    ty: Ty,
    owner: Option<usize>,
    through_ref: bool,
    uniq: bool,
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
        });
        let l = self.locals.len() - 1;
        let top = self.frames.len() - 1;
        self.frames[top].names.push((name.into(), l));
        l
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
        if v.summary.is_some() {
            self.locals[l].summary = v.summary;
        }
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
            self.locals[l].root = Some(r);
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

    fn adt_fields(&self, t: &Ty) -> Vec<Ty> {
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
            Ty::Fn(f) => f.summary.is_none(),
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
