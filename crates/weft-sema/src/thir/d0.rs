//! Test D0, part 1 (plan stage T3): the THIR tables against the syntax tree,
//! the facts and the final types.
//!
//! For each body with no `typeck` error, D0 checks:
//!
//! - (a) each expression that the old lowering lowers as a value has a type,
//!   and no two visits of a key gave different values ([`Tables::conflicts`]);
//! - (b) each name has a [`Res`];
//! - (c) each call has a [`CallInfo`], and its argument order equals
//!   `FnFacts::arg_order` for its span;
//! - (d) each integer type of [`Tables::int_ty`] equals `FnFacts::int_ops` for
//!   its span, and the reverse;
//! - (e) the implicit dereferences of [`Tables::adjust`] fit the final types: a
//!   field, an index, a method receiver, a borrow, an operator, a condition and
//!   a destructuring pattern see a value of the right type after them.
//!
//! The interpreter (`compile.rs`) follows pointers at run time and emits no
//! dereference, so (e) compares with the final types, not with `compile.rs`.
//!
//! A body is not checked if its tables hold the error type, if the program
//! has no final declarations, or if a `typeck` diagnostic (W01xx) is inside it:
//! such a body gets no IR (`docs/ir.md` 2.4, 5).

use std::collections::{BTreeMap, BTreeSet};

use weft_ir::ty::{AdtKind, ExternDeref, Ty as T};
use weft_syntax::ast::Span;
use weft_syntax::ast::{self, Block, Expr, ExprKind, Lit, Pattern, PatternKind, Stmt, StmtKind};

use super::{CallInfo, DerefKind, FieldIdx, Key, RecvMode, Res, Tables, TyId, TyTable};
use crate::Analysis;

/// The checks of D0.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Check {
    /// Two visits of one key gave different values.
    Conflict,
    /// (a) An expression has no type, or a pattern has no type or binding.
    Type,
    /// (b) A name has no meaning.
    Res,
    /// (c) A call has no call record, or its argument order differs from the facts.
    Call,
    /// (d) An integer type differs from the facts.
    IntTy,
    /// (e) The dereferences do not fit the final types.
    Adjust,
}

impl Check {
    /// All checks, in order.
    pub const ALL: [Self; 6] = [
        Self::Conflict,
        Self::Type,
        Self::Res,
        Self::Call,
        Self::IntTy,
        Self::Adjust,
    ];

    /// The name of the check.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Conflict => "conflict",
            Self::Type => "a-type",
            Self::Res => "b-res",
            Self::Call => "c-call",
            Self::IntTy => "d-int-ty",
            Self::Adjust => "e-adjust",
        }
    }
}

/// One failure of D0.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Finding {
    /// The check.
    pub check: Check,
    /// The name of the body.
    pub body: String,
    /// The unit of the body.
    pub unit: usize,
    /// The location in the unit.
    pub span: Span,
    /// What is wrong.
    pub text: String,
}

/// The result of D0 on one analysis.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Report {
    /// The bodies.
    pub bodies: usize,
    /// The bodies that D0 checked.
    pub checked: usize,
    /// The expressions of the checked bodies.
    pub exprs: usize,
    /// The expressions of the checked bodies whose type had a free type variable.
    pub free: usize,
    /// The conflicts in the bodies that D0 did not check.
    pub skipped_conflicts: usize,
    /// The failures.
    pub findings: Vec<Finding>,
    /// Facts that are not failures: each conflict in a body that D0 did not
    /// check, and each expression of a checked body whose type had a free
    /// type variable.
    pub notes: Vec<Finding>,
}

impl Report {
    /// Returns true if D0 holds.
    pub fn holds(&self) -> bool {
        self.findings.is_empty()
    }
}

/// Runs D0 on each body of `a`.
pub fn d0(a: &Analysis) -> Report {
    let mut r = Report {
        bodies: a.bodies.len(),
        ..Report::default()
    };
    let funcs = a.bodies.iter().filter(|b| b.func.is_some()).count();
    for (i, (b, t)) in a.bodies.iter().zip(&a.thir).enumerate() {
        let (name, block, span, params) = if let Some(f) = b.func {
            let def = &a.program.fns[f];
            let Some(body) = def.decl.body.as_ref() else {
                continue;
            };
            (def.path.clone(), body, def.span, def.decl.params.len())
        } else {
            let Some(test) = a.program.tests.get(i - funcs) else {
                continue;
            };
            (format!("test \"{}\"", test.name), &test.body, test.span, 0)
        };
        let typeck_error = a.diags.iter().any(|d| {
            d.unit == b.unit
                && d.code.as_str().starts_with("W01")
                && d.span.lo >= span.lo
                && d.span.hi <= span.hi.max(block.span.hi)
        });
        if t.error || typeck_error || a.thir_decl_error.is_some() {
            r.skipped_conflicts += t.conflicts.len();
            for c in &t.conflicts {
                r.notes.push(Finding {
                    check: Check::Conflict,
                    body: name.clone(),
                    unit: b.unit,
                    span,
                    text: format!(
                        "in a body that D0 does not check: {} of {:?}: {}",
                        c.table,
                        c.key,
                        c.values.join(" / ")
                    ),
                });
            }
            continue;
        }
        r.checked += 1;
        let mut w = Walk {
            a,
            t,
            tys: &a.thir_tys,
            body: name,
            unit: b.unit,
            spans: BTreeMap::new(),
            findings: Vec::new(),
            exprs: 0,
        };
        for p in 0..params {
            let k = u32::try_from(p).unwrap_or(u32::MAX);
            if !t
                .bindings
                .iter()
                .any(|x| x.binder == super::Binder::Param(k))
            {
                w.fail(Check::Type, span, format!("parameter {p} has no binding"));
            }
        }
        w.block(block);
        w.conflicts();
        w.facts(&b.facts);
        r.exprs += w.exprs;
        r.free += t.free.len();
        for e in &t.free {
            let at = w.spans.get(e).copied().unwrap_or(span);
            let ty = t
                .expr_ty
                .get(e)
                .map_or_else(String::new, |&x| a.thir_tys.show(x));
            r.notes.push(Finding {
                check: Check::Type,
                body: w.body.clone(),
                unit: b.unit,
                span: at,
                text: format!("a free type variable: the type is `{ty}`"),
            });
        }
        r.findings.append(&mut w.findings);
    }
    r
}

/// How an expression is used.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Use {
    /// A value or a place: it has a type.
    Value,
    /// A name or a field in a path: a module, a type or an effect.
    Path,
    /// The callee name of a call.
    Callee,
    /// The literal of a duration `2.s`: the lowering does not lower it.
    Duration,
}

/// The walk over one body.
struct Walk<'a> {
    a: &'a Analysis,
    t: &'a Tables,
    tys: &'a TyTable,
    body: String,
    unit: usize,
    /// The span of each expression.
    spans: BTreeMap<ast::ExprId, Span>,
    findings: Vec<Finding>,
    exprs: usize,
}

impl Walk<'_> {
    fn fail(&mut self, check: Check, span: Span, text: String) {
        self.findings.push(Finding {
            check,
            body: self.body.clone(),
            unit: self.unit,
            span,
            text,
        });
    }

    /// Returns true if `e` names a module, a type or an effect.
    fn is_path(&self, e: &Expr) -> bool {
        matches!(
            self.t.res.get(&e.id),
            Some(Res::Mod(_) | Res::Adt(_) | Res::Effect(_))
        )
    }

    fn block(&mut self, b: &Block) {
        for s in &b.stmts {
            self.stmt(s);
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Let { pat, init, .. } => {
                if let Some(e) = init {
                    self.expr(e, Use::Value);
                }
                self.pat(pat);
            }
            StmtKind::Expr(e) | StmtKind::Assert(e) => {
                self.expr(e, Use::Value);
                if matches!(s.kind, StmtKind::Assert(_)) {
                    self.no_ref_after(e, "an `assert` condition");
                }
            }
            StmtKind::Assign { target, op, value } => {
                self.expr(value, Use::Value);
                self.expr(target, Use::Value);
                if *op != ast::AssignOp::Assign {
                    self.no_ref_after(value, "the right side of a compound assignment");
                    self.no_ref_after(target, "the target of a compound assignment");
                }
            }
            StmtKind::Return(e) => {
                if let Some(e) = e {
                    self.expr(e, Use::Value);
                }
            }
            StmtKind::Break | StmtKind::Continue => {}
            StmtKind::While { cond, body } => {
                self.expr(cond, Use::Value);
                self.block(body);
            }
            StmtKind::For { pat, iter, body } => {
                match &iter.kind {
                    ExprKind::Range { lo, hi } => {
                        self.spans.insert(iter.id, iter.span);
                        self.expr(lo, Use::Value);
                        self.expr(hi, Use::Value);
                    }
                    ExprKind::Index { base, index: None } => {
                        self.need_ty(iter);
                        self.spans.insert(iter.id, iter.span);
                        self.expr(base, Use::Value);
                        self.elems_after(base);
                    }
                    _ => {
                        self.expr(iter, Use::Value);
                        self.elems_after(iter);
                    }
                }
                self.pat(pat);
                self.block(body);
            }
            StmtKind::Loop(body) => self.block(body),
        }
    }

    /// Checks that expression `e` has a type.
    fn need_ty(&mut self, e: &Expr) {
        if !self.t.expr_ty.contains_key(&e.id) {
            let text = format!("{} has no type", kind_name(e));
            self.fail(Check::Type, e.span, text);
        }
    }

    fn expr(&mut self, e: &Expr, u: Use) {
        self.spans.insert(e.id, e.span);
        self.exprs += 1;
        match u {
            Use::Value => self.need_ty(e),
            Use::Duration => return,
            Use::Path | Use::Callee => {}
        }
        if matches!(e.kind, ExprKind::Name(_)) && !self.t.res.contains_key(&e.id) {
            self.fail(Check::Res, e.span, "a name has no meaning".to_string());
        }
        if u == Use::Callee {
            if let Some(Res::Local(_)) = self.t.res.get(&e.id) {
                self.need_ty(e);
            }
        }
        match &e.kind {
            ExprKind::Lit(Lit::Str(parts)) => {
                for p in parts {
                    if let ast::StrPart::Interp(x) = p {
                        self.expr(x, Use::Value);
                    }
                }
            }
            ExprKind::Lit(_) | ExprKind::Name(_) => {}
            ExprKind::Field { base, name } => {
                if matches!(&base.kind, ExprKind::Lit(Lit::Int(_)))
                    && matches!(name.name.as_str(), "s" | "ms")
                {
                    self.expr(base, Use::Duration);
                } else if self.is_path(base) {
                    self.expr(base, Use::Path);
                } else if u == Use::Path {
                    // A part of a path whose base is not a path: the
                    // lowering does not lower it.
                    self.expr(base, Use::Path);
                } else {
                    self.expr(base, Use::Value);
                    self.field_after(e, base, &name.name);
                }
            }
            ExprKind::Index { base, index } => {
                self.expr(base, Use::Value);
                if let Some(i) = index {
                    self.expr(i, Use::Value);
                    self.no_ref_after(i, "an index");
                }
                self.elems_after(base);
            }
            ExprKind::Call {
                callee,
                args,
                trailing,
            } => {
                self.need_call(e);
                if matches!(callee.kind, ExprKind::Name(_)) {
                    self.expr(callee, Use::Callee);
                } else {
                    self.expr(callee, Use::Value);
                }
                for a in args {
                    self.expr(&a.value, Use::Value);
                }
                if let Some(t) = trailing {
                    self.expr(t, Use::Value);
                }
            }
            ExprKind::MethodCall {
                receiver,
                args,
                trailing,
                ..
            } => {
                self.need_call(e);
                if self.is_path(receiver) {
                    self.expr(receiver, Use::Path);
                } else {
                    self.expr(receiver, Use::Value);
                    self.recv_after(e, receiver);
                }
                for a in args {
                    self.expr(&a.value, Use::Value);
                }
                if let Some(t) = trailing {
                    self.expr(t, Use::Value);
                }
            }
            ExprKind::Unary { op, expr } => {
                self.expr(expr, Use::Value);
                if *op == ast::UnOp::Ref {
                    self.borrow_after(e, expr);
                } else {
                    self.no_ref_after(expr, "an operand");
                }
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                self.expr(lhs, Use::Value);
                self.expr(rhs, Use::Value);
                self.no_ref_after(lhs, "an operand");
                self.no_ref_after(rhs, "an operand");
            }
            ExprKind::Range { lo, hi } => {
                self.expr(lo, Use::Value);
                self.expr(hi, Use::Value);
            }
            ExprKind::Tuple(es) | ExprKind::Array(es) => {
                for x in es {
                    self.expr(x, Use::Value);
                }
            }
            ExprKind::StructLit { fields, .. } => {
                for (_, x) in fields {
                    self.expr(x, Use::Value);
                }
            }
            ExprKind::Closure { params, body } => {
                match self.t.closure.get(&e.id) {
                    Some(c) if c.params.len() == params.len() => {}
                    Some(_) => self.fail(
                        Check::Type,
                        e.span,
                        "a closure has the wrong number of parameters".to_string(),
                    ),
                    None => self.fail(Check::Type, e.span, "a closure has no record".to_string()),
                }
                self.expr(body, Use::Value);
            }
            ExprKind::Block(b) => self.block(b),
            ExprKind::If { cond, then, else_ } => {
                self.expr(cond, Use::Value);
                self.no_ref_after(cond, "a condition");
                self.block(then);
                if let Some(x) = else_ {
                    self.expr(x, Use::Value);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee, Use::Value);
                for arm in arms {
                    self.pat(&arm.pat);
                    self.expr(&arm.body, Use::Value);
                }
            }
            ExprKind::Handle { clauses, body, .. } => {
                match self.t.handle.get(&e.id) {
                    Some(h) if h.clauses.len() == clauses.len() => {}
                    _ => self.fail(Check::Type, e.span, "a `handle` has no record".to_string()),
                }
                if !self.t.effect.contains_key(&e.id) {
                    self.fail(Check::Res, e.span, "a `handle` has no effect".to_string());
                }
                self.expr(body, Use::Value);
                for c in clauses {
                    self.block(&c.body);
                }
            }
            ExprKind::Scope { body, .. } => self.block(body),
        }
    }

    /// Checks that a call has a call record.
    fn need_call(&mut self, e: &Expr) {
        if !self.t.call.contains_key(&e.id) {
            self.fail(Check::Call, e.span, "a call has no call record".to_string());
        }
    }

    fn pat(&mut self, p: &Pattern) {
        if !self.t.pat_ty.contains_key(&p.id) {
            self.fail(Check::Type, p.span(), "a pattern has no type".to_string());
        }
        match &p.kind {
            PatternKind::Bind(_) => {
                if !self.t.binding.contains_key(&p.id) {
                    self.fail(
                        Check::Type,
                        p.span(),
                        "a name pattern has no binding".to_string(),
                    );
                }
            }
            PatternKind::Wild(_) | PatternKind::Lit(..) => {}
            PatternKind::Tuple(ps, _) => {
                self.pat_after(p, true);
                for q in ps {
                    self.pat(q);
                }
            }
            PatternKind::Variant { fields, .. } => {
                self.pat_after(p, false);
                for q in fields {
                    self.pat(q);
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // (e) The dereferences against the final types
    // -----------------------------------------------------------------------

    /// The type of expression `e` after its dereferences, or a text that tells
    /// why the steps do not fit.
    fn after(&self, e: &Expr) -> Option<Result<TyId, String>> {
        let &t = self.t.expr_ty.get(&e.id)?;
        let steps = self.t.adjust.get(&e.id).map_or(&[][..], Vec::as_slice);
        Some(self.apply(t, steps))
    }

    /// Applies dereference `steps` to type `t`.
    fn apply(&self, mut t: TyId, steps: &[DerefKind]) -> Result<TyId, String> {
        for &s in steps {
            match (s, self.pointee(t)) {
                (s, Some((k, inner))) if s == k => t = inner,
                _ => {
                    return Err(format!(
                        "the step {s:?} does not fit the type `{}`",
                        self.tys.show(t)
                    ))
                }
            }
        }
        Ok(t)
    }

    /// The kind of pointer that type `t` is, and its pointee.
    fn pointee(&self, t: TyId) -> Option<(DerefKind, TyId)> {
        match self.tys.get(t) {
            T::Ref(x) => Some((DerefKind::Ref, *x)),
            T::Adt(a, args) => match &self.tys.adt(*a).kind {
                AdtKind::Extern { deref: Some(d), .. } => {
                    let k = if *d == ExternDeref::Group {
                        DerefKind::Rc
                    } else {
                        DerefKind::Box
                    };
                    args.first().map(|&x| (k, x))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Records a failure of (e) for expression `e`.
    fn adjust_fail(&mut self, e: &Expr, text: String) {
        self.fail(Check::Adjust, e.span, text);
    }

    /// The value of `e` after its dereferences is not a reference.
    fn no_ref_after(&mut self, e: &Expr, what: &str) {
        match self.after(e) {
            Some(Ok(t)) if matches!(self.tys.get(t), T::Ref(_)) => {
                let text = format!("{what} is still a reference `{}`", self.tys.show(t));
                self.adjust_fail(e, text);
            }
            Some(Err(text)) => self.adjust_fail(e, text),
            _ => {}
        }
    }

    /// The base `base` of field expression `e` has field `name` after its
    /// dereferences, and the field record names it.
    fn field_after(&mut self, e: &Expr, base: &Expr, name: &str) {
        let t = match self.after(base) {
            Some(Ok(t)) => t,
            Some(Err(text)) => return self.adjust_fail(base, text),
            None => return,
        };
        let want = match self.tys.get(t) {
            T::Tuple(ts) => name
                .parse::<usize>()
                .ok()
                .filter(|&i| i < ts.len())
                .map(|i| FieldIdx::Field(u32::try_from(i).unwrap_or(u32::MAX))),
            T::Adt(a, _) => match &self.tys.adt(*a).kind {
                AdtKind::Struct(fs) => fs
                    .iter()
                    .position(|f| f.name == name)
                    .map(|i| FieldIdx::Field(u32::try_from(i).unwrap_or(u32::MAX))),
                AdtKind::Enum(vs) => vs
                    .iter()
                    .position(|v| v.name == name)
                    .map(|i| FieldIdx::Variant(u32::try_from(i).unwrap_or(u32::MAX))),
                AdtKind::Extern { .. } => None,
            },
            _ => None,
        };
        match want {
            None => {
                let text = format!(
                    "the base has no field `{name}` after its dereferences: `{}`",
                    self.tys.show(t)
                );
                self.adjust_fail(e, text);
            }
            Some(f) if self.t.field.get(&e.id) != Some(&f) => {
                let text = format!(
                    "the field record is {:?}, the type gives {f:?}",
                    self.t.field.get(&e.id)
                );
                self.adjust_fail(e, text);
            }
            Some(_) => {}
        }
    }

    /// The value of `e` after its dereferences has elements.
    fn elems_after(&mut self, e: &Expr) {
        let t = match self.after(e) {
            Some(Ok(t)) => t,
            Some(Err(text)) => return self.adjust_fail(e, text),
            None => return,
        };
        let ok = match self.tys.get(t) {
            T::Array(..) | T::Slice(_) => true,
            T::Adt(a, _) => matches!(
                self.tys.adt(*a).kind,
                AdtKind::Extern {
                    elem_unstable: Some(_),
                    ..
                }
            ),
            _ => false,
        };
        if !ok {
            let text = format!(
                "the value has no elements after its dereferences: `{}`",
                self.tys.show(t)
            );
            self.adjust_fail(e, text);
        }
    }

    /// The receiver `recv` of method call `e` reaches `self` with the depth of
    /// references that `self` has.
    fn recv_after(&mut self, e: &Expr, recv: &Expr) {
        let Some(CallInfo {
            callee: super::Callee::Item { item, .. },
            recv: Some(r),
            ..
        }) = self.t.call.get(&e.id)
        else {
            return;
        };
        let t = match self.after(recv) {
            Some(Ok(t)) => t,
            Some(Err(text)) => return self.adjust_fail(recv, text),
            None => return,
        };
        let Some(own) = self.a.sigs.get(item.index()).and_then(|s| s.params.first()) else {
            return;
        };
        let want = usize::from(own.ty.is_ref());
        let mut depth = 0;
        let mut x = t;
        while let T::Ref(inner) = self.tys.get(x) {
            depth += 1;
            x = *inner;
        }
        let have = match r.mode {
            RecvMode::Borrow => depth + 1,
            RecvMode::Ref | RecvMode::Value | RecvMode::Deref => depth,
        };
        if have != want {
            let text = format!(
                "the receiver `{}` reaches `self` with {have} references, `self` has {want} ({:?})",
                self.tys.show(t),
                r.mode
            );
            self.adjust_fail(recv, text);
        }
    }

    /// The type of borrow `e` of `inner` is a reference to the value of
    /// `inner` after its dereferences.
    fn borrow_after(&mut self, e: &Expr, inner: &Expr) {
        if matches!(inner.kind, ExprKind::Index { index: None, .. }) {
            return;
        }
        let (Some(&te), Some(after)) = (self.t.expr_ty.get(&e.id), self.after(inner)) else {
            return;
        };
        match after {
            Ok(t) if self.tys.find(&T::Ref(t)) == Some(te) => {}
            Ok(t) => {
                let text = format!(
                    "the borrow has type `{}`, its place has type `{}`",
                    self.tys.show(te),
                    self.tys.show(t)
                );
                self.adjust_fail(e, text);
            }
            Err(text) => self.adjust_fail(inner, text),
        }
    }

    /// The value at destructuring pattern `p` is a tuple (`tuple`), or a
    /// struct or an enum, after its dereferences.
    fn pat_after(&mut self, p: &Pattern, tuple: bool) {
        let Some(&t) = self.t.pat_ty.get(&p.id) else {
            return;
        };
        let steps = self.t.pat_adjust.get(&p.id).map_or(&[][..], Vec::as_slice);
        let t = match self.apply(t, steps) {
            Ok(t) => t,
            Err(text) => return self.fail(Check::Adjust, p.span(), text),
        };
        let ok = match self.tys.get(t) {
            T::Tuple(_) => tuple,
            T::Adt(..) => !tuple,
            _ => false,
        };
        if !ok {
            let text = format!(
                "the pattern sees `{}` after its dereferences",
                self.tys.show(t)
            );
            self.fail(Check::Adjust, p.span(), text);
        }
    }

    // -----------------------------------------------------------------------
    // Conflicts, (c) and (d)
    // -----------------------------------------------------------------------

    fn conflicts(&mut self) {
        for c in &self.t.conflicts {
            let span = match c.key {
                Key::Expr(e) => self.spans.get(&e).copied().unwrap_or_default(),
                Key::Pat(_) | Key::Param(_) => Span::default(),
            };
            let text = format!("{} of {:?}: {}", c.table, c.key, c.values.join(" / "));
            self.findings.push(Finding {
                check: Check::Conflict,
                body: self.body.clone(),
                unit: self.unit,
                span,
                text,
            });
        }
    }

    fn facts(&mut self, f: &weft_facts::FnFacts) {
        let by_span: BTreeMap<(u32, u32), Vec<ast::ExprId>> =
            self.spans.iter().fold(BTreeMap::new(), |mut m, (&e, s)| {
                m.entry((s.lo, s.hi)).or_insert_with(Vec::new).push(e);
                m
            });
        // (c) The argument order of the facts.
        for (span, order) in &f.arg_order {
            let calls: Vec<&CallInfo> = by_span
                .get(&(span.lo, span.hi))
                .into_iter()
                .flatten()
                .filter_map(|e| self.t.call.get(e))
                .collect();
            if !calls.iter().any(|c| &c.args == order) {
                let text = format!(
                    "the facts give the argument order {order:?}, the call records {:?}",
                    calls.iter().map(|c| &c.args).collect::<Vec<_>>()
                );
                self.fail(Check::Call, *span, text);
            }
        }
        // (d) The integer types of the facts.
        let facts: BTreeSet<((u32, u32), String)> = f
            .int_ops
            .iter()
            .map(|(s, n)| ((s.lo, s.hi), n.clone()))
            .collect();
        let mut tables: BTreeSet<((u32, u32), String)> = BTreeSet::new();
        for (e, i) in &self.t.int_ty {
            if let Some(s) = self.spans.get(e) {
                tables.insert(((s.lo, s.hi), i.name().to_string()));
            }
        }
        for ((lo, hi), n) in facts.difference(&tables) {
            let text = format!("the facts give `{n}`, the tables give none or another");
            self.fail(Check::IntTy, Span::new(*lo, *hi), text);
        }
        for ((lo, hi), n) in tables.difference(&facts) {
            let text = format!("the tables give `{n}`, the facts give none or another");
            self.fail(Check::IntTy, Span::new(*lo, *hi), text);
        }
    }
}

/// The name of the kind of expression `e`, for a message.
const fn kind_name(e: &Expr) -> &'static str {
    match &e.kind {
        ExprKind::Lit(_) => "a literal",
        ExprKind::Name(_) => "a name",
        ExprKind::Field { .. } => "a field",
        ExprKind::Index { .. } => "an index",
        ExprKind::Call { .. } => "a call",
        ExprKind::MethodCall { .. } => "a method call",
        ExprKind::Unary { .. } => "a unary operation",
        ExprKind::Binary { .. } => "a binary operation",
        ExprKind::Range { .. } => "a range",
        ExprKind::Tuple(_) => "a tuple",
        ExprKind::Array(_) => "an array",
        ExprKind::StructLit { .. } => "a struct literal",
        ExprKind::Closure { .. } => "a closure",
        ExprKind::Block(_) => "a block",
        ExprKind::If { .. } => "an `if`",
        ExprKind::Match { .. } => "a `match`",
        ExprKind::Handle { .. } => "a `handle`",
        ExprKind::Scope { .. } => "a `scope`",
    }
}
