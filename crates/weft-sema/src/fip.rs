//! Checks for fully in-place (`fip`) functions.
//!
//! A `fip` function must compile to in-place updates with no allocation. The
//! rules follow FP² (Koka), simplified:
//!
//! - W1004: the function has no effects.
//! - W1003: it calls only `fip` functions and constructors.
//! - W1002: each owned parameter and each owned pattern variable is used exactly
//!   once on every path.
//! - W1001: each constructor with fields reuses a cell of the same size that a
//!   `match` on an owned value freed on the same path.

use std::collections::BTreeMap;

use weft_syntax::ast::{Block, Expr, ExprKind, Pattern, StmtKind, StrPart};
use weft_syntax::diag::Diagnostic;

use crate::program::{FnId, FnSig, ItemRef, Program};
use crate::types::Ty;

/// Checks one `fip` function.
pub fn check(prog: &Program, sigs: &[FnSig], f: FnId) -> Vec<Diagnostic> {
    let def = &prog.fns[f];
    let mut c = Fip {
        prog,
        sigs,
        module: def.module,
        diags: Vec::new(),
        owned: Vec::new(),
        pattern_owned: Vec::new(),
    };
    if !sigs[f].effects.is_empty() {
        c.diags.push(Diagnostic::error(
            "W1004",
            format!("`fip fn {}` must have no effects", def.name),
            def.decl.name.span,
        ));
    }
    for p in &sigs[f].params {
        if is_owned(&p.ty) {
            c.owned.push(p.name.clone());
        }
    }
    let Some(body) = &def.decl.body else {
        return c.diags;
    };
    let mut credits = BTreeMap::new();
    c.block(body, &mut credits);
    for name in c.owned.clone() {
        let (lo, hi) = uses_block(body, &name);
        if lo != 1 || hi != 1 {
            c.diags.push(Diagnostic::error(
                "W1002",
                format!(
                    "`fip` needs `{name}` used exactly once on every path (found {lo} to {hi})"
                ),
                def.decl.name.span,
            ));
        }
    }
    c.diags
}

fn is_owned(t: &Ty) -> bool {
    !matches!(t, Ty::Int(_) | Ty::Bool | Ty::Unit | Ty::Ref(_) | Ty::Fn(_))
}

struct Fip<'a> {
    prog: &'a Program,
    sigs: &'a [FnSig],
    module: usize,
    diags: Vec<Diagnostic>,
    owned: Vec<String>,
    pattern_owned: Vec<String>,
}

/// Free cells by size, along the current path.
type Credits = BTreeMap<usize, usize>;

impl Fip<'_> {
    /// Returns the payload types of a variant, found by name.
    fn payload_types(&self, name: &str) -> Vec<Ty> {
        let Some(&(adt, vi)) = self.prog.variants.get(name).and_then(|v| v.first()) else {
            return Vec::new();
        };
        match &self.prog.adts[adt].kind {
            crate::program::AdtKind::Enum(vs) => vs[vi].fields.clone(),
            _ => Vec::new(),
        }
    }

    fn block(&mut self, b: &Block, credits: &mut Credits) {
        for s in &b.stmts {
            match &s.kind {
                StmtKind::Let {
                    init: Some(e), pat, ..
                } => {
                    self.expr(e, credits);
                    let _ = pat;
                }
                StmtKind::Expr(e) | StmtKind::Assert(e) | StmtKind::Return(Some(e)) => {
                    self.expr(e, credits)
                }
                StmtKind::Assign { target, value, .. } => {
                    self.expr(target, credits);
                    self.expr(value, credits);
                }
                StmtKind::While { cond, body }
                | StmtKind::For {
                    iter: cond, body, ..
                } => {
                    self.expr(cond, credits);
                    self.block(body, &mut credits.clone());
                }
                StmtKind::Loop(body) => self.block(body, &mut credits.clone()),
                _ => {}
            }
        }
    }

    fn alloc(&mut self, size: usize, e: &Expr, credits: &mut Credits) {
        if size == 0 {
            return;
        }
        match credits.get_mut(&size) {
            Some(n) if *n > 0 => *n -= 1,
            _ => self.diags.push(Diagnostic::error(
                "W1001",
                format!("`fip` function allocates a cell of size {size} with no cell to reuse"),
                e.span,
            )),
        }
    }

    fn expr(&mut self, e: &Expr, credits: &mut Credits) {
        match &e.kind {
            ExprKind::Call {
                callee,
                args,
                trailing,
            } => {
                for a in args {
                    self.expr(&a.value, credits);
                }
                if let Some(t) = trailing {
                    self.expr(t, credits);
                }
                let ExprKind::Name(id) = &callee.kind else {
                    return;
                };
                match self.prog.lookup(self.module, &id.name) {
                    Some(ItemRef::Fn(f)) => {
                        if !self.prog.fns[f].decl.is_fip {
                            self.diags.push(Diagnostic::error(
                                "W1003",
                                format!("`fip` function calls `{}`, which is not `fip`", id.name),
                                id.span,
                            ));
                        }
                        let _ = self.sigs;
                    }
                    Some(ItemRef::Adt(_)) => self.alloc(args.len(), e, credits),
                    _ => {
                        if self.prog.variants.contains_key(&id.name) {
                            self.alloc(args.len(), e, credits);
                        } else {
                            self.diags.push(Diagnostic::error(
                                "W1003",
                                format!("`fip` function calls `{}`, which is not `fip`", id.name),
                                id.span,
                            ));
                        }
                    }
                }
            }
            ExprKind::MethodCall {
                receiver,
                method,
                args,
                ..
            } => {
                self.expr(receiver, credits);
                for a in args {
                    self.expr(&a.value, credits);
                }
                self.diags.push(Diagnostic::error(
                    "W1003",
                    format!(
                        "`fip` function calls method `{}`; only `fip` functions are allowed",
                        method.name
                    ),
                    method.span,
                ));
            }
            ExprKind::StructLit { fields, .. } => {
                for (_, v) in fields {
                    self.expr(v, credits);
                }
                self.alloc(fields.len(), e, credits);
            }
            ExprKind::Tuple(es) | ExprKind::Array(es) => {
                for x in es {
                    self.expr(x, credits);
                }
                if matches!(e.kind, ExprKind::Array(_)) {
                    self.alloc(usize::MAX, e, credits);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee, credits);
                let owned_scrut = matches!(&scrutinee.kind, ExprKind::Name(n)
                    if self.owned.contains(&n.name) || self.pattern_owned.contains(&n.name));
                for arm in arms {
                    let mut c = credits.clone();
                    if owned_scrut {
                        if let Pattern::Variant { fields, path, .. } = &arm.pat {
                            *c.entry(fields.len()).or_insert(0) += 1;
                            let name = path.last().map_or("", |p| p.name.as_str());
                            let ftys = self.payload_types(name);
                            for (fi, f) in fields.iter().enumerate() {
                                if let Pattern::Bind(b) = f {
                                    if !ftys.get(fi).is_some_and(is_owned) {
                                        continue;
                                    }
                                    self.pattern_owned.push(b.name.clone());
                                    let (lo, hi) = uses_expr(&arm.body, &b.name);
                                    if lo != 1 || hi != 1 {
                                        self.diags.push(Diagnostic::error(
                                            "W1002",
                                            format!(
                                                "`fip` needs `{}` used exactly once on every path",
                                                b.name
                                            ),
                                            b.span,
                                        ));
                                    }
                                }
                            }
                        }
                    }
                    self.expr(&arm.body, &mut c);
                }
            }
            ExprKind::If { cond, then, else_ } => {
                self.expr(cond, credits);
                self.block(then, &mut credits.clone());
                if let Some(x) = else_ {
                    self.expr(x, &mut credits.clone());
                }
            }
            ExprKind::Block(b) => self.block(b, credits),
            ExprKind::Field { base, .. } | ExprKind::Unary { expr: base, .. } => {
                self.expr(base, credits)
            }
            ExprKind::Index { base, index } => {
                self.expr(base, credits);
                if let Some(i) = index {
                    self.expr(i, credits);
                }
            }
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::Range { lo: lhs, hi: rhs } => {
                self.expr(lhs, credits);
                self.expr(rhs, credits);
            }
            ExprKind::Closure { .. } | ExprKind::Handle { .. } | ExprKind::Scope { .. } => {
                self.diags.push(Diagnostic::error(
                    "W1003",
                    "`fip` function cannot make closures, handlers or scopes",
                    e.span,
                ));
            }
            ExprKind::Lit(_) | ExprKind::Name(_) => {}
        }
    }
}

/// Counts the uses of a name: the least and the most over all paths.
fn uses_block(b: &Block, name: &str) -> (usize, usize) {
    let mut lo = 0;
    let mut hi = 0;
    for s in &b.stmts {
        let (a, z) = match &s.kind {
            StmtKind::Let { init: Some(e), .. }
            | StmtKind::Expr(e)
            | StmtKind::Assert(e)
            | StmtKind::Return(Some(e)) => uses_expr(e, name),
            StmtKind::Assign { target, value, .. } => {
                add(uses_expr(target, name), uses_expr(value, name))
            }
            StmtKind::While { cond, body }
            | StmtKind::For {
                iter: cond, body, ..
            } => {
                let c = uses_expr(cond, name);
                let b = uses_block(body, name);
                (c.0, c.1 + b.1 * 2)
            }
            StmtKind::Loop(body) => {
                let b = uses_block(body, name);
                (0, b.1 * 2)
            }
            _ => (0, 0),
        };
        lo += a;
        hi += z;
    }
    (lo, hi)
}

const fn add(a: (usize, usize), b: (usize, usize)) -> (usize, usize) {
    (a.0 + b.0, a.1 + b.1)
}

fn uses_expr(e: &Expr, name: &str) -> (usize, usize) {
    match &e.kind {
        ExprKind::Name(id) => {
            if id.name == name {
                (1, 1)
            } else {
                (0, 0)
            }
        }
        ExprKind::Lit(weft_syntax::ast::Lit::Str(parts)) => {
            parts.iter().fold((0, 0), |acc, p| match p {
                StrPart::Interp(x) => add(acc, uses_expr(x, name)),
                StrPart::Text(_) => acc,
            })
        }
        ExprKind::Lit(_) => (0, 0),
        ExprKind::Field { base, .. } | ExprKind::Unary { expr: base, .. } => uses_expr(base, name),
        ExprKind::Index { base, index } => {
            let b = uses_expr(base, name);
            index.as_ref().map_or(b, |i| add(b, uses_expr(i, name)))
        }
        ExprKind::Call {
            callee,
            args,
            trailing,
        } => {
            let mut acc = uses_expr(callee, name);
            for a in args {
                acc = add(acc, uses_expr(&a.value, name));
            }
            if let Some(t) = trailing {
                acc = add(acc, uses_expr(t, name));
            }
            acc
        }
        ExprKind::MethodCall {
            receiver,
            args,
            trailing,
            ..
        } => {
            let mut acc = uses_expr(receiver, name);
            for a in args {
                acc = add(acc, uses_expr(&a.value, name));
            }
            if let Some(t) = trailing {
                acc = add(acc, uses_expr(t, name));
            }
            acc
        }
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::Range { lo: lhs, hi: rhs } => {
            add(uses_expr(lhs, name), uses_expr(rhs, name))
        }
        ExprKind::Tuple(es) | ExprKind::Array(es) => es
            .iter()
            .fold((0, 0), |acc, x| add(acc, uses_expr(x, name))),
        ExprKind::StructLit { fields, .. } => fields
            .iter()
            .fold((0, 0), |acc, (_, x)| add(acc, uses_expr(x, name))),
        ExprKind::Closure { body, .. } => uses_expr(body, name),
        ExprKind::Block(b) => uses_block(b, name),
        ExprKind::If { cond, then, else_ } => {
            let c = uses_expr(cond, name);
            let t = uses_block(then, name);
            let f = else_.as_ref().map_or((0, 0), |x| uses_expr(x, name));
            (c.0 + t.0.min(f.0), c.1 + t.1.max(f.1))
        }
        ExprKind::Match { scrutinee, arms } => {
            let s = uses_expr(scrutinee, name);
            let mut lo = usize::MAX;
            let mut hi = 0;
            for a in arms {
                let (x, y) = uses_expr(&a.body, name);
                lo = lo.min(x);
                hi = hi.max(y);
            }
            if arms.is_empty() {
                lo = 0;
            }
            (s.0 + lo, s.1 + hi)
        }
        ExprKind::Handle { body, clauses, .. } => {
            let mut acc = uses_expr(body, name);
            for c in clauses {
                acc = add(acc, uses_block(&c.body, name));
            }
            acc
        }
        ExprKind::Scope { body, .. } => uses_block(body, name),
    }
}
