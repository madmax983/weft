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
use weft_syntax::diag::Code;

use weft_syntax::ast::{BinOp, Block, Expr, ExprKind, Pattern, StmtKind, StrPart};
use weft_syntax::diag::Diagnostic;

use crate::program::{FnId, FnSig, ItemRef, Program};
use crate::types::Ty;

/// Checks one `fip` function.
pub fn check(prog: &Program, sigs: &[FnSig], f: FnId) -> Vec<Diagnostic> {
    let def = &prog.fns[f];
    let mut c = Fip {
        prog,
        module: def.module,
        diags: Vec::new(),
        owned: Vec::new(),
        pattern_owned: Vec::new(),
    };
    if !sigs[f].effects.is_empty() {
        c.diags.push(Diagnostic::error(
            Code::W1004,
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
        let (lo, hi) = uses_block(body, &name).all();
        if lo != 1 || hi != 1 {
            let found = if lo == hi {
                show_count(lo)
            } else {
                format!("{} to {}", show_count(lo), show_count(hi))
            };
            c.diags.push(Diagnostic::error(
                Code::W1002,
                format!("`fip` needs `{name}` used exactly once on every path (found {found})"),
                def.decl.name.span,
            ));
        }
    }
    c.diags
}

const fn is_owned(t: &Ty) -> bool {
    !matches!(t, Ty::Int(_) | Ty::Bool | Ty::Unit | Ty::Ref(_) | Ty::Fn(_))
}

struct Fip<'a> {
    prog: &'a Program,
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
                StmtKind::Let { init: Some(e), .. }
                | StmtKind::Expr(e)
                | StmtKind::Assert(e)
                | StmtKind::Return(Some(e)) => self.expr(e, credits),
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
                Code::W1001,
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
                                Code::W1003,
                                format!("`fip` function calls `{}`, which is not `fip`", id.name),
                                id.span,
                            ));
                        }
                    }
                    Some(ItemRef::Adt(_)) => self.alloc(args.len(), e, credits),
                    _ => {
                        if self.prog.variants.contains_key(&id.name) {
                            self.alloc(args.len(), e, credits);
                        } else {
                            self.diags.push(Diagnostic::error(
                                Code::W1003,
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
                    Code::W1003,
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
            ExprKind::Tuple(es) => {
                for x in es {
                    self.expr(x, credits);
                }
            }
            ExprKind::Array(es) => {
                for x in es {
                    self.expr(x, credits);
                }
                self.diags.push(Diagnostic::error(
                    Code::W1001,
                    "`fip` function makes an array; no freed cell can hold an array",
                    e.span,
                ));
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
                                    let (lo, hi) = uses_expr(&arm.body, &b.name).all();
                                    if lo != 1 || hi != 1 {
                                        self.diags.push(Diagnostic::error(
                                            Code::W1002,
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
                self.expr(base, credits);
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
                    Code::W1003,
                    "`fip` function cannot make closures, handlers or scopes",
                    e.span,
                ));
            }
            ExprKind::Lit(_) | ExprKind::Name(_) => {}
        }
    }
}

/// The highest use count. The check asks only for exactly one use, so the
/// counts stop here: [`MANY`] means two or more uses.
const MANY: usize = 2;

/// The least and the most uses of a name on a set of paths.
type Count = (usize, usize);

/// Shows a use count.
fn show_count(n: usize) -> String {
    if n >= MANY {
        format!("{MANY} or more")
    } else {
        n.to_string()
    }
}

/// Stops a count at [`MANY`].
const fn cap(n: usize) -> usize {
    if n > MANY {
        MANY
    } else {
        n
    }
}

/// Adds the counts of two parts of one path.
const fn add(a: Count, b: Count) -> Count {
    (cap(a.0.saturating_add(b.0)), cap(a.1.saturating_add(b.1)))
}

/// The counts of two sets of paths together. `None` is an empty set.
fn join(a: Option<Count>, b: Option<Count>) -> Option<Count> {
    match (a, b) {
        (Some(x), Some(y)) => Some((x.0.min(y.0), x.1.max(y.1))),
        (x, None) | (None, x) => x,
    }
}

/// The uses of a name in a part of the code, on four sets of paths.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Uses {
    /// The paths that go on after the part. `None` if no path goes on.
    next: Option<Count>,
    /// The paths that return inside the part. `None` if no path returns.
    ret: Option<Count>,
    /// The paths that leave the innermost loop with `break`.
    brk: Option<Count>,
    /// The paths that go to the next run of the innermost loop with
    /// `continue`.
    cont: Option<Count>,
}

/// Adds the counts of `a` to each path of `b`, if a path of `a` goes on.
fn after(a: Option<Count>, b: Option<Count>) -> Option<Count> {
    a.zip(b).map(|(x, y)| add(x, y))
}

impl Uses {
    /// No use, and each path goes on.
    const ZERO: Self = Self::of((0, 0));

    /// A `break`: each path leaves the loop.
    const BREAK: Self = Self {
        next: None,
        ret: None,
        brk: Some((0, 0)),
        cont: None,
    };

    /// A `continue`: each path goes to the next run of the loop.
    const CONTINUE: Self = Self {
        next: None,
        ret: None,
        brk: None,
        cont: Some((0, 0)),
    };

    /// The counts of paths that go on.
    const fn of(c: Count) -> Self {
        Self {
            next: Some(c),
            ret: None,
            brk: None,
            cont: None,
        }
    }

    /// The counts over all paths.
    fn all(self) -> Count {
        [self.ret, self.brk, self.cont]
            .into_iter()
            .fold(self.next, join)
            .unwrap_or((0, 0))
    }

    /// This part, then part `b`.
    fn then(self, b: Self) -> Self {
        Self {
            next: after(self.next, b.next),
            ret: join(self.ret, after(self.next, b.ret)),
            brk: join(self.brk, after(self.next, b.brk)),
            cont: join(self.cont, after(self.next, b.cont)),
        }
    }

    /// This part or part `b`: two branches.
    fn or(self, b: Self) -> Self {
        Self {
            next: join(self.next, b.next),
            ret: join(self.ret, b.ret),
            brk: join(self.brk, b.brk),
            cont: join(self.cont, b.cont),
        }
    }

    /// A `return` after this part: each path that goes on ends.
    fn returns(self) -> Self {
        Self {
            next: None,
            ret: join(self.ret, self.next),
            ..self
        }
    }

    /// A loop with this part as one run: the body, and for `while` the
    /// condition after it. The loop runs it zero or more times. A repeated
    /// use counts as [`MANY`]. A path leaves the loop at `break`, at
    /// `return`, or at the end if `ends` is true (`while` and `for`).
    fn repeated(self, ends: bool) -> Self {
        let again = join(self.next, self.cont);
        let grows = again.is_some_and(|n| n.1 > 0);
        let most = |(lo, hi): Count| (lo, if grows { MANY } else { hi });
        let end = ends.then_some((0, 0)).map(most);
        Self {
            next: join(end, self.brk.map(most)),
            ret: self.ret.map(most),
            brk: None,
            cont: None,
        }
    }
}

/// Counts the uses of a name in a block. The counts stop at [`MANY`].
fn uses_block(b: &Block, name: &str) -> Uses {
    let mut acc = Uses::ZERO;
    for s in &b.stmts {
        let part = match &s.kind {
            StmtKind::Let { init: Some(e), .. } | StmtKind::Expr(e) | StmtKind::Assert(e) => {
                uses_expr(e, name)
            }
            StmtKind::Return(e) => e
                .as_ref()
                .map_or(Uses::ZERO, |e| uses_expr(e, name))
                .returns(),
            StmtKind::Assign { target, value, .. } => {
                uses_expr(target, name).then(uses_expr(value, name))
            }
            StmtKind::While { cond, body } => {
                // The condition runs once, then once after each run of the body.
                // A `continue` goes to the condition. A `break` skips it.
                let c = uses_expr(cond, name);
                let body = uses_block(body, name);
                let run = Uses {
                    next: join(body.next, body.cont),
                    cont: None,
                    ..body
                };
                c.then(run.then(c).repeated(true))
            }
            StmtKind::For { iter, body, .. } => {
                uses_expr(iter, name).then(uses_block(body, name).repeated(true))
            }
            StmtKind::Loop(body) => uses_block(body, name).repeated(false),
            StmtKind::Break => Uses::BREAK,
            StmtKind::Continue => Uses::CONTINUE,
            StmtKind::Let { init: None, .. } => Uses::ZERO,
        };
        acc = acc.then(part);
    }
    acc
}

/// Counts the uses of a name in the parts of one path.
fn uses_seq<'e>(es: impl IntoIterator<Item = &'e Expr>, name: &str) -> Uses {
    es.into_iter()
        .fold(Uses::ZERO, |acc, x| acc.then(uses_expr(x, name)))
}

fn uses_expr(e: &Expr, name: &str) -> Uses {
    match &e.kind {
        ExprKind::Name(id) => Uses::of(if id.name == name { (1, 1) } else { (0, 0) }),
        ExprKind::Lit(weft_syntax::ast::Lit::Str(parts)) => uses_seq(
            parts.iter().filter_map(|p| match p {
                StrPart::Interp(x) => Some(x),
                StrPart::Text(_) => None,
            }),
            name,
        ),
        ExprKind::Lit(_) => Uses::ZERO,
        ExprKind::Field { base, .. } | ExprKind::Unary { expr: base, .. } => uses_expr(base, name),
        ExprKind::Index { base, index } => {
            uses_seq(std::iter::once(&**base).chain(index.as_deref()), name)
        }
        ExprKind::Call {
            callee,
            args,
            trailing,
        } => uses_seq(
            std::iter::once(&**callee)
                .chain(args.iter().map(|a| &a.value))
                .chain(trailing.as_deref()),
            name,
        ),
        ExprKind::MethodCall {
            receiver,
            args,
            trailing,
            ..
        } => uses_seq(
            std::iter::once(&**receiver)
                .chain(args.iter().map(|a| &a.value))
                .chain(trailing.as_deref()),
            name,
        ),
        // `&&` and `||` run the right operand on some paths only.
        ExprKind::Binary {
            op: BinOp::And | BinOp::Or,
            lhs,
            rhs,
        } => uses_expr(lhs, name).then(uses_expr(rhs, name).or(Uses::ZERO)),
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::Range { lo: lhs, hi: rhs } => {
            uses_expr(lhs, name).then(uses_expr(rhs, name))
        }
        ExprKind::Tuple(es) | ExprKind::Array(es) => uses_seq(es, name),
        ExprKind::StructLit { fields, .. } => uses_seq(fields.iter().map(|(_, x)| x), name),
        // A `return` in a closure ends the closure, not the function.
        ExprKind::Closure { body, .. } => Uses::of(uses_expr(body, name).all()),
        ExprKind::Block(b) => uses_block(b, name),
        ExprKind::If { cond, then, else_ } => {
            let t = uses_block(then, name);
            let f = else_.as_ref().map_or(Uses::ZERO, |x| uses_expr(x, name));
            uses_expr(cond, name).then(t.or(f))
        }
        ExprKind::Match { scrutinee, arms } => {
            let arms = arms
                .iter()
                .map(|a| uses_expr(&a.body, name))
                .reduce(Uses::or)
                .unwrap_or(Uses::ZERO);
            uses_expr(scrutinee, name).then(arms)
        }
        ExprKind::Handle { body, clauses, .. } => {
            clauses.iter().fold(uses_expr(body, name), |acc, c| {
                acc.then(uses_block(&c.body, name))
            })
        }
        ExprKind::Scope { body, .. } => uses_block(body, name),
    }
}
