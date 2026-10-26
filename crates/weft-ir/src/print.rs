//! The text form of the IR (`docs/ir.md` 3.3).
//!
//! `weft ir FILE [FUNCTION]` prints this form, and the golden files of the builder
//! use it. The program prints its declarations first, then each body. A body prints
//! each local (`_n`, its type, its kind and its name), then each block (`bbN`;
//! `(cleanup)` marks a cleanup block). A terminator shows its normal successors and
//! its cleanup block: `-> [bb1, unwind: bb4]`.
//!
//! A place prints as `(*_1).0[_3]`: `*` for each `Deref`, `.k` for a field,
//! `(p as #v)` for a variant, `[_i]` for an index, `[]` for all elements and
//! `[..sN]` or `[sN..]` for a side of a split. An operand prints as `copy p`,
//! `move p` or `const c`. The printer does not print origins.

use std::fmt::Write as _;

use crate::ty::{AdtKind, Ty};
use crate::{
    AggKind, BinOp, BlockId, Body, BodyId, BodyKind, Callee, CapArgs, CapOperand, CaptureMode,
    Const, EffectId, FnId, IterSource, LocalId, LocalKind, OpIdx, Operand, Place, Program, Proj,
    Rvalue, Side, StmtKind, TempKind, TermKind, TyId, TyTable, UnOp, UnwindAction,
};

/// Returns the text of a whole program: the declarations, then each body.
pub fn print_program(p: &Program, tys: &TyTable) -> String {
    Printer::new(p, tys).program()
}

/// Returns the text of one body of a program.
pub fn print_body(p: &Program, tys: &TyTable, id: BodyId) -> String {
    Printer::new(p, tys).body(id)
}

/// Prints the parts of one program. The program gives the names of functions,
/// handlers and operations; the type table gives the text of types.
#[derive(Clone, Copy, Debug)]
pub struct Printer<'a> {
    p: &'a Program,
    tys: &'a TyTable,
}

impl<'a> Printer<'a> {
    /// Makes a printer for program `p` with type table `tys`.
    pub const fn new(p: &'a Program, tys: &'a TyTable) -> Self {
        Self { p, tys }
    }

    /// Returns the text of the whole program.
    pub fn program(&self) -> String {
        let mut out = String::new();
        self.decls(&mut out);
        for i in 0..self.p.bodies.len() {
            out.push('\n');
            out.push_str(&self.body(BodyId(crate::id_of(i))));
        }
        out
    }

    /// Writes the declarations of the program: one line each.
    fn decls(&self, out: &mut String) {
        for (i, f) in self.p.fns.iter().enumerate() {
            let _ = write!(out, "fn f{i} {}", f.name);
            if f.generics > 0 {
                let ps: Vec<String> = (0..f.generics).map(|j| format!("T{j}")).collect();
                let _ = write!(out, "<{}>", ps.join(", "));
            }
            let ps: Vec<String> = f.params.iter().map(|t| self.ty(*t)).collect();
            let _ = write!(out, "({}) -> {}", ps.join(", "), self.ty(f.ret));
            if let Some(row) = &f.stated_row {
                let es: Vec<&str> = row.iter().map(|e| self.effect(*e)).collect();
                if es.is_empty() {
                    out.push_str(" / ()");
                } else {
                    let _ = write!(out, " / {}", es.join(", "));
                }
            }
            match f.intrinsic {
                Some(crate::Intrinsic::SimRun) => out.push_str(" [sim.run]"),
                Some(crate::Intrinsic::WithTimeout) => out.push_str(" [with_timeout]"),
                None => {}
            }
            match f.body {
                Some(b) => {
                    let _ = writeln!(out, ": b{}", b.0);
                }
                None => out.push_str(": extern\n"),
            }
        }
        for (i, t) in self.p.tests.iter().enumerate() {
            let _ = writeln!(out, "test t{i} {:?}: b{}", t.name, t.body.0);
        }
        for (i, c) in self.p.closures.iter().enumerate() {
            let caps: Vec<String> = c
                .captures
                .iter()
                .map(|k| format!("{} {}", capture_mode(k.mode), place(&k.source)))
                .collect();
            let _ = write!(
                out,
                "closure c{i}: body b{}, maker b{}, cap_env e{}, captures [{}]",
                c.body.0,
                c.maker.0,
                c.cap_env.0,
                caps.join(", ")
            );
            if c.once {
                out.push_str(", once");
            }
            out.push('\n');
        }
        for (i, h) in self.p.handlers.iter().enumerate() {
            let cs: Vec<String> = h
                .clauses
                .iter()
                .map(|(op, b)| format!("{}: b{}", self.op(h.effect, *op), b.0))
                .collect();
            let _ = write!(
                out,
                "handler h{i} {}: handled b{}, site b{}, clauses [{}]",
                self.effect(h.effect),
                h.handled.0,
                h.site.0,
                cs.join(", ")
            );
            if h.multi {
                out.push_str(", multi");
            }
            out.push('\n');
        }
        for (i, s) in self.p.scopes.iter().enumerate() {
            let _ = writeln!(out, "scope s{i}: body b{}, site b{}", s.body.0, s.site.0);
        }
        for (i, s) in self.p.spawns.iter().enumerate() {
            match (s.scope, s.fork) {
                (_, true) => {
                    let _ = writeln!(out, "spawn sp{i}: fork");
                }
                (Some(sc), false) => {
                    let _ = writeln!(out, "spawn sp{i}: scope s{}", sc.0);
                }
                (None, false) => {
                    let _ = writeln!(out, "spawn sp{i}");
                }
            }
        }
        for (i, e) in self.p.cap_envs.iter().enumerate() {
            let _ = write!(out, "cap_env e{i}");
            let mut parts = Vec::new();
            if let Some(par) = e.parent {
                parts.push(format!("parent e{}", par.0));
            }
            for (eff, pl) in &e.adds {
                parts.push(format!("{} {}", self.effect(*eff), place(pl)));
            }
            if !parts.is_empty() {
                let _ = write!(out, ": {}", parts.join(", "));
            }
            out.push('\n');
        }
    }

    /// Returns the text of body `id`: a header line, the locals and the blocks.
    pub fn body(&self, id: BodyId) -> String {
        let mut out = String::new();
        let Some(b) = self.p.body(id) else {
            let _ = writeln!(out, "body b{}: missing", id.0);
            return out;
        };
        let _ = write!(out, "body b{}: {}", id.0, self.body_kind(b.kind));
        if let Some(par) = b.parent {
            let _ = write!(out, "; parent b{}", par.0);
        }
        let _ = write!(out, "; cap_env e{}", b.cap_env.0);
        if b.entry != BlockId(0) {
            let _ = write!(out, "; entry bb{}", b.entry.0);
        }
        let _ = writeln!(out, "; unwind_exit bb{}", b.unwind_exit.0);
        for l in b.local_ids() {
            let _ = writeln!(out, "  {}", self.local(b, l));
        }
        for (bi, blk) in b.blocks.iter().enumerate() {
            let tag = if blk.cleanup { " (cleanup)" } else { "" };
            let _ = writeln!(out, "  bb{bi}{tag}:");
            for s in &blk.stmts {
                let _ = writeln!(out, "    {}", self.stmt(&s.kind));
            }
            let _ = writeln!(out, "    {}", self.term(b, &blk.term.kind));
        }
        out
    }

    /// Returns the text of a body kind: `fn main`, `handled h0`, `clause h0 pick`.
    pub fn body_kind(&self, k: BodyKind) -> String {
        match k {
            BodyKind::Fn(f) => format!("fn {}", self.fn_name(f)),
            BodyKind::Test(t) => match self.p.tests.get(t.index()) {
                Some(d) => format!("test {:?}", d.name),
                None => format!("test t{}", t.0),
            },
            BodyKind::Closure(c) => format!("closure c{}", c.0),
            BodyKind::Clause(h, op) => {
                let name = self
                    .p
                    .handlers
                    .get(h.index())
                    .map_or_else(|| format!("op{}", op.0), |d| self.op(d.effect, op));
                format!("clause h{} {name}", h.0)
            }
            BodyKind::Handled(h) => format!("handled h{}", h.0),
            BodyKind::Scope(s) => format!("scope s{}", s.0),
        }
    }

    /// Returns the text of local `l` of body `b`: `_1: &u64 (User `r`)`.
    pub fn local(&self, b: &Body, l: LocalId) -> String {
        let Some(d) = b.local(l) else {
            return format!("_{}: missing", l.0);
        };
        let mut kind = match d.kind {
            LocalKind::Return => "Return".to_string(),
            LocalKind::Param(i) => format!("Param({i})"),
            LocalKind::Env => "Env".to_string(),
            LocalKind::User => "User".to_string(),
            LocalKind::Temp(t) => format!("Temp({})", temp_kind(t)),
            LocalKind::Iterator => "Iterator".to_string(),
            LocalKind::Cap(e) => format!("Cap({})", self.effect(e)),
            LocalKind::Kont(multi) => {
                format!("Kont({})", if multi { "multi" } else { "once" })
            }
            LocalKind::ScopeCap => "ScopeCap".to_string(),
            LocalKind::TaskResult(s) => format!("TaskResult(sp{})", s.0),
            LocalKind::Upvar(x) => format!("Upvar(_{})", x.0),
        };
        if let Some(n) = &d.name {
            let _ = write!(kind, " `{n}`");
        }
        if d.in_place {
            kind.push_str(", in place");
        }
        format!("_{}: {} ({kind})", l.0, self.ty(d.ty))
    }

    /// Returns the text of a statement.
    pub fn stmt(&self, k: &StmtKind) -> String {
        match k {
            StmtKind::Live(l) => format!("Live(_{})", l.0),
            StmtKind::Dead(l) => format!("Dead(_{})", l.0),
            StmtKind::Assign(p, r) => format!("{} = {}", place(p), self.rvalue(r)),
            StmtKind::Drop(p) => format!("Drop({})", place(p)),
            StmtKind::Consume(p) => format!("Consume({})", place(p)),
            StmtKind::Uninit(p) => format!("Uninit({})", place(p)),
            StmtKind::Bounds(p, o) => format!("Bounds({}, {})", place(p), self.operand(o)),
            StmtKind::Mention(p) => format!("Mention({})", place(p)),
            StmtKind::Print(ops) => format!("Print({})", self.operands(ops)),
            StmtKind::UnwindValue(p, a) => {
                let a = match a {
                    UnwindAction::OnAbort(f) => format!("OnAbort({})", self.fn_name(*f)),
                    UnwindAction::Drop => "Drop".to_string(),
                    UnwindAction::Fault => "Fault".to_string(),
                };
                format!("UnwindValue({}, {a})", place(p))
            }
            StmtKind::UnwindKont(l) => format!("UnwindKont(_{})", l.0),
        }
    }

    /// Returns the text of a right side.
    pub fn rvalue(&self, r: &Rvalue) -> String {
        match r {
            Rvalue::Use(o) => self.operand(o),
            Rvalue::Ref(p) => format!("&{}", place(p)),
            Rvalue::Binary(op, it, x, y) => format!(
                "{}{}({}, {})",
                bin_op(*op),
                int_suffix(*it),
                self.operand(x),
                self.operand(y)
            ),
            Rvalue::Unary(op, it, x) => {
                let name = match op {
                    UnOp::Neg => "Neg",
                    UnOp::Not => "Not",
                };
                format!("{name}{}({})", int_suffix(*it), self.operand(x))
            }
            Rvalue::Aggregate(k, ops) => self.aggregate(k, ops),
            Rvalue::Len(p) => format!("Len({})", place(p)),
            Rvalue::Discriminant(p) => format!("Discriminant({})", place(p)),
            Rvalue::Concat(ops) => format!("Concat({})", self.operands(ops)),
            Rvalue::Iter(IterSource::Elems(p)) => format!("Iter(elems {})", place(p)),
            Rvalue::Iter(IterSource::Range(lo, hi)) => {
                format!("Iter({}..{})", self.operand(lo), self.operand(hi))
            }
        }
    }

    /// Returns the text of an aggregate.
    fn aggregate(&self, k: &AggKind, ops: &[crate::Operand]) -> String {
        let args = self.operands(ops);
        match k {
            AggKind::Tuple if ops.len() == 1 => format!("({args},)"),
            AggKind::Tuple => format!("({args})"),
            AggKind::Array => format!("[{args}]"),
            AggKind::Vec => format!("vec[{args}]"),
            AggKind::Struct(t) => format!("{} {{ {args} }}", self.ty(*t)),
            AggKind::Variant(t, v) => {
                let name = match self.tys.try_get(*t) {
                    Some(Ty::Adt(a, _)) => match self.tys.adts().get(a.index()).map(|d| &d.kind) {
                        Some(AdtKind::Enum(vs)) => vs.get(v.index()).map(|d| d.name.clone()),
                        _ => None,
                    },
                    _ => None,
                };
                let name = name.unwrap_or_else(|| format!("#{}", v.0));
                format!("{}::{name}({args})", self.ty(*t))
            }
            AggKind::Closure(c) => format!("closure c{}({args})", c.0),
        }
    }

    /// Returns the text of an operand: `copy p`, `move p` or `const c`.
    pub fn operand(&self, o: &Operand) -> String {
        match o {
            Operand::Copy(p) => format!("copy {}", place(p)),
            Operand::Move(p) => format!("move {}", place(p)),
            Operand::Const(c) => format!("const {}", self.constant(c)),
        }
    }

    /// Returns the text of a list of operands, with commas.
    fn operands(&self, ops: &[Operand]) -> String {
        let v: Vec<String> = ops.iter().map(|o| self.operand(o)).collect();
        v.join(", ")
    }

    /// Returns the text of a constant.
    fn constant(&self, c: &Const) -> String {
        match c {
            Const::Unit => "()".to_string(),
            Const::Bool(b) => b.to_string(),
            Const::Int(v, it) => format!("{v}{}", it.name()),
            Const::Str(s) => format!("{s:?}"),
            Const::Duration(ms) => format!("{ms}ms"),
            Const::Fn(f, targs) => format!("{}{}", self.fn_name(*f), self.targs(targs)),
        }
    }

    /// Returns the text of type arguments: `<u64>`, or nothing.
    fn targs(&self, targs: &[TyId]) -> String {
        if targs.is_empty() {
            return String::new();
        }
        let v: Vec<String> = targs.iter().map(|t| self.ty(*t)).collect();
        format!("<{}>", v.join(", "))
    }

    /// Returns the text of a terminator of body `b`, with its successors.
    pub fn term(&self, b: &Body, k: &TermKind) -> String {
        match k {
            TermKind::Goto(t) => format!("Goto(bb{})", t.0),
            TermKind::Switch {
                on,
                arms,
                otherwise,
            } => {
                let mut v: Vec<String> = arms
                    .iter()
                    .map(|(val, t)| format!("{val}: bb{}", t.0))
                    .collect();
                v.push(format!("otherwise: bb{}", otherwise.0));
                format!("switch {} -> [{}]", self.operand(on), v.join(", "))
            }
            TermKind::Return => "Return".to_string(),
            TermKind::UnwindExit => "UnwindExit".to_string(),
            TermKind::Unreachable => "Unreachable".to_string(),
            TermKind::Call {
                callee,
                args,
                dest,
                caps,
                next,
                unwind,
            } => {
                let callee = match callee {
                    Callee::Fn(f, targs) => format!("{}{}", self.fn_name(*f), self.targs(targs)),
                    Callee::Value(o) => format!("({})", self.operand(o)),
                };
                let caps = match caps {
                    CapArgs::Lexical(e) => format!("e{}", e.0),
                    CapArgs::Root => "root".to_string(),
                };
                format!(
                    "{} = call {callee}({}) / {caps} -> {}",
                    place(dest),
                    self.operands(args),
                    succ(*next, *unwind)
                )
            }
            TermKind::Perform {
                cap,
                op,
                args,
                dest,
                next,
                unwind,
            } => {
                let (cap_text, effect) = match cap {
                    CapOperand::Local(p) => (format!("Local({})", place(p)), self.cap_effect(b, p)),
                    CapOperand::Row(e) => (format!("Row({})", self.effect(*e)), Some(*e)),
                };
                let op = effect.map_or_else(|| format!("op{}", op.0), |e| self.op(e, *op));
                format!(
                    "{} = perform {cap_text}.{op}({}) -> {}",
                    place(dest),
                    self.operands(args),
                    succ(Some(*next), *unwind)
                )
            }
            TermKind::Resume {
                kont,
                arg,
                dest,
                next,
                unwind,
            } => format!(
                "{} = resume {}({}) -> {}",
                place(dest),
                place(kont),
                self.operand(arg),
                succ(Some(*next), *unwind)
            ),
            TermKind::Handle {
                handler,
                dest,
                next,
                unwind,
            } => format!(
                "{} = handle h{} -> {}",
                place(dest),
                handler.0,
                succ(Some(*next), *unwind)
            ),
            TermKind::Scope {
                scope,
                dest,
                next,
                unwind,
            } => format!(
                "{} = scope s{} -> {}",
                place(dest),
                scope.0,
                succ(Some(*next), *unwind)
            ),
            TermKind::ScopeWait {
                scope,
                orphans,
                next,
                unwind,
            } => {
                let orphans = if orphans.is_empty() {
                    String::new()
                } else {
                    let v: Vec<String> = orphans.iter().map(|l| format!("_{}", l.0)).collect();
                    format!(", orphans [{}]", v.join(", "))
                };
                format!(
                    "scope_wait {}{orphans} -> {}",
                    place(scope),
                    succ(Some(*next), *unwind)
                )
            }
            TermKind::Spawn {
                site,
                scope,
                task,
                dest,
                next,
            } => {
                let lhs = dest
                    .as_ref()
                    .map_or_else(String::new, |d| format!("{} = ", place(d)));
                format!(
                    "{lhs}spawn sp{}({}, {}) -> [bb{}]",
                    site.0,
                    self.operand(scope),
                    self.operand(task),
                    next.0
                )
            }
            TermKind::Join {
                task,
                dest,
                next,
                unwind,
            } => format!(
                "{} = join {} -> {}",
                place(dest),
                self.operand(task),
                succ(Some(*next), *unwind)
            ),
            TermKind::Detach { task, next } => {
                format!("detach {} -> [bb{}]", self.operand(task), next.0)
            }
            TermKind::Fork {
                sites,
                branches,
                dest,
                next,
                unwind,
            } => {
                let v: Vec<String> = sites
                    .iter()
                    .zip(branches)
                    .map(|(s, o)| format!("sp{}: {}", s.0, self.operand(o)))
                    .collect();
                format!(
                    "{} = fork [{}] -> {}",
                    place(dest),
                    v.join(", "),
                    succ(Some(*next), *unwind)
                )
            }
            TermKind::Assert { cond, next, unwind } => format!(
                "assert {} -> {}",
                self.operand(cond),
                succ(Some(*next), *unwind)
            ),
            TermKind::IterNext {
                iter,
                dest,
                next,
                done,
            } => format!(
                "{} = next {} -> [bb{}, done: bb{}]",
                place(dest),
                place(iter),
                next.0,
                done.0
            ),
        }
    }

    /// Returns the effect of a capability place (see [`cap_effect`]).
    fn cap_effect(&self, b: &Body, p: &Place) -> Option<EffectId> {
        cap_effect(self.p, self.tys, b, p)
    }

    /// Returns the text of a type.
    fn ty(&self, t: TyId) -> String {
        self.tys.show(t)
    }

    /// Returns the name of an effect.
    fn effect(&self, e: EffectId) -> &str {
        self.tys
            .effects()
            .get(e.index())
            .map_or("?", |d| d.identity.as_str())
    }

    /// Returns the name of operation `op` of effect `e`.
    fn op(&self, e: EffectId, op: OpIdx) -> String {
        self.tys
            .effects()
            .get(e.index())
            .and_then(|d| d.ops.get(op.index()))
            .map_or_else(|| format!("op{}", op.0), |d| d.name.clone())
    }

    /// Returns the name of a function.
    fn fn_name(&self, f: FnId) -> String {
        self.p
            .fns
            .get(f.index())
            .map_or_else(|| format!("f{}", f.0), |d| d.name.clone())
    }
}

/// Returns the effect of a capability place.
///
/// For a whole local, the effect comes from the kind or the type of the local.
/// Else it comes from the capability environment of the closure body (a `Cap`
/// field of a closure environment, also through a view of the environment in a
/// nested body, `docs/ir.md` 5.1.7).
pub fn cap_effect(prog: &Program, tys: &TyTable, b: &Body, p: &Place) -> Option<EffectId> {
    if !p.is_local() {
        // Walk the chain of upvar locals to the environment local.
        let (mut body, mut l) = (b, p.local);
        for _ in 0..=prog.bodies.len() {
            match body.local(l)?.kind {
                LocalKind::Env => {
                    let env = prog.cap_envs.get(body.cap_env.index())?;
                    let q = Place {
                        local: l,
                        proj: p.proj.clone(),
                    };
                    return env.adds.iter().find(|(_, x)| *x == q).map(|(e, _)| *e);
                }
                LocalKind::Upvar(src) => {
                    body = prog.body(body.parent?)?;
                    l = src;
                }
                _ => return None,
            }
        }
        return None;
    }
    let d = b.local(p.local)?;
    if let LocalKind::Cap(e) = d.kind {
        return Some(e);
    }
    match tys.try_get(d.ty)? {
        Ty::Cap(e) => Some(*e),
        _ => None,
    }
}

/// Returns the text of a place: `(*_1).0[_3]`.
pub fn place(p: &Place) -> String {
    let mut t = format!("_{}", p.local.0);
    for pr in &p.proj {
        t = match pr {
            Proj::Deref(_) => format!("(*{t})"),
            Proj::Field(f) => format!("{t}.{}", f.0),
            Proj::Variant(v) => format!("({t} as #{})", v.0),
            Proj::Index(i) => format!("{t}[_{}]", i.0),
            Proj::Elems => format!("{t}[]"),
            Proj::Split(s, Side::Left) => format!("{t}[..s{}]", s.0),
            Proj::Split(s, Side::Right) => format!("{t}[s{}..]", s.0),
        };
    }
    t
}

/// Returns the successor list of a terminator: `[bb1, unwind: bb4]`.
fn succ(next: Option<BlockId>, unwind: Option<BlockId>) -> String {
    let mut v = Vec::new();
    if let Some(n) = next {
        v.push(format!("bb{}", n.0));
    }
    if let Some(u) = unwind {
        v.push(format!("unwind: bb{}", u.0));
    }
    format!("[{}]", v.join(", "))
}

/// Returns the name of a binary operator.
const fn bin_op(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "Add",
        BinOp::Sub => "Sub",
        BinOp::Mul => "Mul",
        BinOp::Div => "Div",
        BinOp::Rem => "Rem",
        BinOp::Eq => "Eq",
        BinOp::Ne => "Ne",
        BinOp::Lt => "Lt",
        BinOp::Le => "Le",
        BinOp::Gt => "Gt",
        BinOp::Ge => "Ge",
    }
}

/// Returns `<u64>` for an integer operator, or nothing.
fn int_suffix(it: Option<crate::IntTy>) -> String {
    it.map_or_else(String::new, |i| format!("<{}>", i.name()))
}

/// Returns the name of a temporary kind.
const fn temp_kind(t: TempKind) -> &'static str {
    match t {
        TempKind::Operand => "Operand",
        TempKind::Callee => "Callee",
        TempKind::Receiver => "Receiver",
        TempKind::Scrutinee => "Scrutinee",
        TempKind::Borrowed => "Borrowed",
        TempKind::Promoted => "Promoted",
        TempKind::Discarded => "Discarded",
        TempKind::Value => "Value",
    }
}

/// Returns the name of a capture mode.
const fn capture_mode(m: CaptureMode) -> &'static str {
    match m {
        CaptureMode::ByRef => "ByRef",
        CaptureMode::ByMove => "ByMove",
        CaptureMode::Kept => "Kept",
        CaptureMode::Cap => "Cap",
        CaptureMode::Kont => "Kont",
    }
}
