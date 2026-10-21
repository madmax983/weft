//! Pretty printer: turns an AST back into Weft source.
//!
//! The output parses back to the same tree, spans and ids aside. The printer
//! does not print ids. It adds parentheses only where precedence or the
//! grammar needs them. It prints the block that the parser makes for a long
//! chain of binary operators as the chain.

use crate::ast::{
    is_chain_part, Arg, BinOp, Block, EffectItem, EffectRow, Expr, ExprKind, File, FnDecl, Item,
    ItemKind, Lit, Param, Pattern, PatternKind, PlaceExpr, PlaceStep, Stmt, StmtKind, StrPart,
    StructDecl, TypeExpr, TypeExprKind, UnOp,
};
use crate::lexer::escape_text;

/// Prints a file as Weft source.
pub fn pretty(file: &File) -> String {
    let mut p = Printer::default();
    for (i, item) in file.items.iter().enumerate() {
        if i > 0 {
            p.out.push_str("\n\n");
        }
        p.item(item);
    }
    if !file.items.is_empty() {
        p.out.push('\n');
    }
    p.out
}

/// Prints one expression as Weft source.
pub fn pretty_expr(e: &Expr) -> String {
    let mut p = Printer::default();
    p.expr(e, 0, false);
    p.out
}

/// Prints one block as Weft source.
pub fn pretty_block(b: &Block) -> String {
    let mut p = Printer::default();
    p.block(b);
    p.out
}

/// Returns the parts of the block that the parser makes for a long chain: the
/// values of the hidden locals, and the rest of the chain.
fn chain_parts(e: &Expr) -> Option<(Vec<&Expr>, &Expr)> {
    let ExprKind::Block(b) = &e.kind else {
        return None;
    };
    let (last, lets) = b.stmts.split_last()?;
    let StmtKind::Expr(rest) = &last.kind else {
        return None;
    };
    if lets.is_empty() || !matches!(rest.kind, ExprKind::Binary { .. }) {
        return None;
    }
    lets.iter()
        .map(|s| match &s.kind {
            StmtKind::Let {
                pat:
                    Pattern {
                        kind: PatternKind::Bind(id),
                        ..
                    },
                ty: None,
                init: Some(init),
            } if is_chain_part(&id.name) => Some(init),
            _ => None,
        })
        .collect::<Option<Vec<&Expr>>>()
        .map(|inits| (inits, rest))
}

/// Binding strength of an expression. A long chain binds like its last operator.
fn prec(e: &Expr) -> u8 {
    match chain_parts(e) {
        Some((_, rest)) => prec_kind(&rest.kind),
        None => prec_kind(&e.kind),
    }
}

/// Binding strength of an expression form. Closures and `handle` are 0
/// because their bodies extend as far to the right as possible.
const fn prec_kind(kind: &ExprKind) -> u8 {
    match kind {
        ExprKind::Closure { .. } | ExprKind::Handle { .. } => 0,
        ExprKind::Range { .. } => 1,
        ExprKind::Binary { op, .. } => bin_prec(*op),
        ExprKind::Unary { .. } => 7,
        ExprKind::Field { .. }
        | ExprKind::Index { .. }
        | ExprKind::Call { .. }
        | ExprKind::MethodCall { .. } => 8,
        _ => 9,
    }
}

const fn bin_prec(op: BinOp) -> u8 {
    match op {
        BinOp::Or => 2,
        BinOp::And => 3,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 4,
        BinOp::Add | BinOp::Sub => 5,
        BinOp::Mul | BinOp::Div | BinOp::Rem => 6,
    }
}

const fn bin_text(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
    }
}

/// True if the inner type of `*T` needs parentheses.
fn wrap_ptr_inner(inner: &TypeExpr) -> bool {
    !inner.modes.is_empty() || matches!(inner.kind, TypeExprKind::Fn { .. })
}

/// True if a type, printed with no parentheses, takes an `in place` that
/// follows it: it ends in a reference with no place.
fn takes_in(t: &TypeExpr) -> bool {
    if !t.modes.is_empty() {
        return false;
    }
    match &t.kind {
        TypeExprKind::Ref { place, .. } => place.is_none(),
        TypeExprKind::Ptr(inner) => !wrap_ptr_inner(inner) && takes_in(inner),
        _ => false,
    }
}

/// True if the expression cannot stand at the top of an `if`, `while`, `for`
/// or `match` head without parentheses.
const fn needs_parens_in_head(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::StructLit { .. } | ExprKind::Closure { .. } | ExprKind::Handle { .. } => true,
        ExprKind::Call { trailing, .. } | ExprKind::MethodCall { trailing, .. } => {
            trailing.is_some()
        }
        _ => false,
    }
}

#[derive(Default)]
struct Printer {
    out: String,
    indent: usize,
    /// True inside an interpolation: everything stays on one line.
    inline: bool,
}

impl Printer {
    fn push(&mut self, s: &str) {
        self.out.push_str(s);
    }

    fn newline(&mut self) {
        self.out.push('\n');
        for _ in 0..self.indent {
            self.out.push_str("    ");
        }
    }

    /// Writes items with `sep` between them.
    fn list<T>(&mut self, items: &[T], sep: &str, mut f: impl FnMut(&mut Self, &T)) {
        for (i, x) in items.iter().enumerate() {
            if i > 0 {
                self.push(sep);
            }
            f(self, x);
        }
    }

    /// Writes `{ a, b }` items: one per line in block mode, else on one line.
    fn brace_items<T>(&mut self, items: &[T], mut f: impl FnMut(&mut Self, &T)) {
        if items.is_empty() {
            self.push("{}");
            return;
        }
        if self.inline {
            self.push("{ ");
            self.list(items, ", ", f);
            self.push(" }");
            return;
        }
        self.push("{");
        self.indent += 1;
        for x in items {
            self.newline();
            f(self, x);
            self.push(",");
        }
        self.indent -= 1;
        self.newline();
        self.push("}");
    }

    // -------------------------------------------------------------- items

    fn item(&mut self, item: &Item) {
        if item.is_pub {
            self.push("pub ");
        }
        match &item.kind {
            ItemKind::Fn(f) => self.fn_decl(f),
            ItemKind::Struct(s) => self.struct_decl(s),
            ItemKind::Enum(e) => {
                self.push("enum ");
                self.push(&e.name.name);
                self.generics(&e.generics);
                self.push(" ");
                self.brace_items(&e.variants, |p, v| {
                    p.push(&v.name.name);
                    if !v.fields.is_empty() {
                        p.push("(");
                        p.list(&v.fields, ", ", Self::ty);
                        p.push(")");
                    }
                });
            }
            ItemKind::Effect(e) => {
                self.push("effect ");
                self.push(&e.name.name);
                self.push(" ");
                self.brace_items(&e.ops, |p, op| {
                    if op.is_multi {
                        p.push("multi ");
                    }
                    p.push("fn ");
                    p.push(&op.name.name);
                    p.params(&op.params);
                    p.ret(op.ret.as_ref());
                });
            }
            ItemKind::Impl(b) => {
                self.push("impl");
                self.generics(&b.generics);
                self.push(" ");
                self.ty(&b.self_ty);
                self.push(" ");
                self.item_body(&b.items);
            }
            ItemKind::Mod(m) => {
                self.push("mod ");
                self.push(&m.name.name);
                self.push(" ");
                self.item_body(&m.items);
            }
            ItemKind::Test(t) => {
                self.push("test \"");
                self.push(&escape_text(&t.name));
                self.push("\" ");
                self.block(&t.body);
            }
            ItemKind::ExternType(t) => {
                self.push("extern type ");
                self.push(&t.name.name);
                self.generics(&t.generics);
                if !t.props.is_empty() {
                    self.push(" { ");
                    self.list(&t.props, ", ", |p, prop| {
                        p.push(&prop.key.name);
                        if let Some(v) = &prop.value {
                            p.push(": ");
                            p.push(&v.name);
                        }
                    });
                    self.push(" }");
                }
            }
        }
    }

    fn item_body(&mut self, items: &[Item]) {
        if items.is_empty() {
            self.push("{}");
            return;
        }
        self.push("{");
        self.indent += 1;
        for item in items {
            self.newline();
            self.item(item);
        }
        self.indent -= 1;
        self.newline();
        self.push("}");
    }

    fn fn_decl(&mut self, f: &FnDecl) {
        if f.is_extern {
            self.push("extern ");
        }
        if f.is_fip {
            self.push("fip ");
        }
        self.push("fn ");
        self.push(&f.name.name);
        self.generics(&f.generics);
        self.params(&f.params);
        self.ret(f.ret.as_ref());
        if let Some(row) = &f.effects {
            self.push(" / ");
            self.row(row);
        }
        if let Some(body) = &f.body {
            self.push(" ");
            self.block(body);
        }
    }

    fn struct_decl(&mut self, s: &StructDecl) {
        if s.is_linear {
            self.push("linear ");
        }
        self.push("struct ");
        self.push(&s.name.name);
        self.generics(&s.generics);
        if s.is_immovable {
            self.push(": !Move");
        }
        self.push(" ");
        self.brace_items(&s.fields, |p, f| {
            p.push(&f.name.name);
            p.push(": ");
            p.ty(&f.ty);
        });
        if let Some(f) = &s.on_abort {
            self.push(" on abort = ");
            self.push(&f.name);
        }
    }

    fn generics(&mut self, names: &[crate::ast::Ident]) {
        if names.is_empty() {
            return;
        }
        self.push("<");
        self.list(names, ", ", |p, n| p.push(&n.name));
        self.push(">");
    }

    fn params(&mut self, params: &[Param]) {
        self.push("(");
        self.list(params, ", ", Self::param);
        self.push(")");
    }

    fn param(&mut self, p: &Param) {
        self.push(&p.name.name);
        if let Some(t) = &p.ty {
            self.push(": ");
            self.ty(t);
        }
    }

    /// Writes ` -> T`. A function type gets parentheses, so that a later `/`
    /// row stays with the outer function.
    fn ret(&mut self, ret: Option<&TypeExpr>) {
        let Some(t) = ret else { return };
        self.push(" -> ");
        if matches!(t.kind, TypeExprKind::Fn { .. }) && t.modes.is_empty() {
            self.push("(");
            self.ty(t);
            self.push(")");
        } else {
            self.ty(t);
        }
    }

    // -------------------------------------------------------------- types

    fn ty(&mut self, t: &TypeExpr) {
        let wrap = !t.modes.is_empty() && matches!(t.kind, TypeExprKind::Fn { .. });
        if wrap {
            self.push("(");
        }
        self.ty_kind(&t.kind);
        if wrap {
            self.push(")");
        }
        if !t.modes.is_empty() {
            self.push(" @");
            for m in &t.modes {
                self.push(" ");
                self.push(m.name());
            }
        }
    }

    fn ty_kind(&mut self, kind: &TypeExprKind) {
        match kind {
            TypeExprKind::Path { segments, args } => {
                self.list(segments, ".", |p, s| p.push(&s.name));
                if !args.is_empty() {
                    self.push("<");
                    self.list(args, ", ", Self::ty);
                    self.push(">");
                }
            }
            TypeExprKind::Ref { inner, place } => {
                self.push("&");
                // `&&T in p` gives `p` to the inner reference. Parentheses are
                // needed only if the inner type would take the `in`.
                let wrap = !inner.modes.is_empty()
                    || matches!(inner.kind, TypeExprKind::Fn { .. })
                    || (place.is_some() && takes_in(inner));
                if wrap {
                    self.push("(");
                    self.ty(inner);
                    self.push(")");
                } else {
                    self.ty(inner);
                }
                if let Some(pl) = place {
                    self.push(" in ");
                    self.place(pl);
                }
            }
            TypeExprKind::Ptr(inner) => {
                self.push("*");
                // `*T @ m` gives the mode to the pointer, and a function type
                // takes a later `/` row. Parentheses keep both with the inner type.
                if wrap_ptr_inner(inner) {
                    self.push("(");
                    self.ty(inner);
                    self.push(")");
                } else {
                    self.ty(inner);
                }
            }
            TypeExprKind::Tuple(ts) => {
                self.push("(");
                self.list(ts, ", ", Self::ty);
                if ts.len() == 1 {
                    self.push(",");
                }
                self.push(")");
            }
            TypeExprKind::Array { elem, len } => {
                self.push("[");
                self.ty(elem);
                self.push(&format!("; {len}]"));
            }
            TypeExprKind::Slice(elem) => {
                self.push("[");
                self.ty(elem);
                self.push("]");
            }
            TypeExprKind::Fn {
                params,
                ret,
                effects,
            } => {
                self.push("fn(");
                self.list(params, ", ", Self::ty);
                self.push(")");
                self.ret(ret.as_deref());
                if let Some(row) = effects {
                    self.push(" / ");
                    if row.items.len() == 1 {
                        self.row(row);
                    } else {
                        self.push("(");
                        self.row(row);
                        self.push(")");
                    }
                }
            }
            TypeExprKind::SelfType => self.push("Self"),
        }
    }

    fn place(&mut self, p: &PlaceExpr) {
        self.push(&p.root.name);
        for step in &p.steps {
            match step {
                PlaceStep::Field(n) => {
                    self.push(".");
                    self.push(&n.name);
                }
                PlaceStep::Elem => self.push("[]"),
                PlaceStep::SegLo(n) => {
                    self.push("[..");
                    self.push(&n.name);
                    self.push("]");
                }
                PlaceStep::SegHi(n) => {
                    self.push("[");
                    self.push(&n.name);
                    self.push("..]");
                }
                PlaceStep::Wildcard => self.push(".."),
            }
        }
    }

    fn row(&mut self, row: &EffectRow) {
        self.list(&row.items, ", ", |p, item| match item {
            EffectItem::Mut(places) => {
                p.push("mut(");
                p.list(places, ", ", Self::place);
                p.push(")");
            }
            EffectItem::Named(n) => p.push(&n.text()),
        });
    }

    // -------------------------------------------------------------- statements

    fn block(&mut self, b: &Block) {
        self.stmts_in_braces(&b.stmts, "");
    }

    /// Writes `{ head stmts }`. `head` is the `s =>` of a scope.
    fn stmts_in_braces(&mut self, stmts: &[Stmt], head: &str) {
        if stmts.is_empty() {
            self.push(if head.is_empty() { "{}" } else { "{ " });
            if !head.is_empty() {
                self.push(head);
                self.push(" }");
            }
            return;
        }
        if self.inline {
            self.push("{ ");
            if !head.is_empty() {
                self.push(head);
                self.push(" ");
            }
            self.list(stmts, "; ", Self::stmt);
            self.push(" }");
            return;
        }
        self.push("{");
        if !head.is_empty() {
            self.push(" ");
            self.push(head);
        }
        self.indent += 1;
        for s in stmts {
            self.newline();
            self.stmt(s);
        }
        self.indent -= 1;
        self.newline();
        self.push("}");
    }

    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Let { pat, ty, init } => {
                self.push("let ");
                self.pattern(pat);
                if let Some(t) = ty {
                    self.push(": ");
                    self.ty(t);
                }
                if let Some(e) = init {
                    self.push(" = ");
                    self.expr(e, 0, false);
                }
            }
            StmtKind::Expr(e) => self.expr(e, 0, false),
            StmtKind::Assign { target, op, value } => {
                self.expr(target, 1, false);
                self.push(match op {
                    crate::ast::AssignOp::Assign => " = ",
                    crate::ast::AssignOp::Add => " += ",
                    crate::ast::AssignOp::Sub => " -= ",
                    crate::ast::AssignOp::Mul => " *= ",
                });
                self.expr(value, 0, false);
            }
            StmtKind::Return(e) => {
                self.push("return");
                if let Some(e) = e {
                    self.push(" ");
                    self.expr(e, 0, false);
                }
            }
            StmtKind::Break => self.push("break"),
            StmtKind::Continue => self.push("continue"),
            StmtKind::While { cond, body } => {
                self.push("while ");
                self.expr(cond, 0, true);
                self.push(" ");
                self.block(body);
            }
            StmtKind::For { pat, iter, body } => {
                self.push("for ");
                self.pattern(pat);
                self.push(" in ");
                self.expr(iter, 0, true);
                self.push(" ");
                self.block(body);
            }
            StmtKind::Loop(body) => {
                self.push("loop ");
                self.block(body);
            }
            StmtKind::Assert(e) => {
                self.push("assert ");
                self.expr(e, 0, false);
            }
        }
    }

    fn pattern(&mut self, p: &Pattern) {
        match &p.kind {
            PatternKind::Bind(id) => self.push(&id.name),
            PatternKind::Wild(_) => self.push("_"),
            PatternKind::Tuple(ps, _) => {
                self.push("(");
                self.list(ps, ", ", Self::pattern);
                if ps.len() == 1 {
                    self.push(",");
                }
                self.push(")");
            }
            PatternKind::Variant { path, fields, .. } => {
                self.list(path, ".", |p, s| p.push(&s.name));
                if !fields.is_empty() {
                    self.push("(");
                    self.list(fields, ", ", Self::pattern);
                    self.push(")");
                }
            }
            PatternKind::Lit(l, _) => self.lit(l),
        }
    }

    // -------------------------------------------------------------- expressions

    /// Writes `e`. It gets parentheses if it binds weaker than `min`, or if
    /// `head` is true and `e` cannot stand at the top of a head.
    fn expr(&mut self, e: &Expr, min: u8, head: bool) {
        if prec(e) < min || (head && needs_parens_in_head(e)) {
            self.push("(");
            self.expr(e, 0, false);
            self.push(")");
            return;
        }
        if let Some((inits, rest)) = chain_parts(e) {
            // Each part starts with the hidden local of the part before it.
            let mut parts = inits.into_iter().chain(std::iter::once(rest));
            if let Some(first) = parts.next() {
                self.expr(first, 0, head);
            }
            for part in parts {
                self.chain_rest(part, head);
            }
            return;
        }
        match &e.kind {
            ExprKind::Lit(l) => self.lit(l),
            ExprKind::Name(id) => self.push(&id.name),
            ExprKind::Field { base, name } => {
                self.expr(base, 8, head);
                self.push(".");
                self.push(&name.name);
            }
            ExprKind::Index { base, index } => {
                self.expr(base, 8, head);
                self.push("[");
                if let Some(i) = index {
                    self.expr(i, 0, false);
                }
                self.push("]");
            }
            ExprKind::Call {
                callee,
                args,
                trailing,
            } => {
                // A field callee needs parentheses, or it reads as a method call.
                let min = if matches!(callee.kind, ExprKind::Field { .. }) {
                    9
                } else {
                    8
                };
                self.expr(callee, min, head);
                self.args(args);
                self.trailing(trailing.as_deref());
            }
            ExprKind::MethodCall {
                receiver,
                method,
                args,
                trailing,
            } => {
                self.expr(receiver, 8, head);
                self.push(".");
                self.push(&method.name);
                self.args(args);
                self.trailing(trailing.as_deref());
            }
            ExprKind::Unary { op, expr } => {
                self.push(match op {
                    UnOp::Neg => "-",
                    UnOp::Not => "!",
                    UnOp::Ref => "&",
                });
                self.expr(expr, 7, head);
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let p = bin_prec(*op);
                // A long chain on the left keeps its parentheses, or the
                // parser makes it one chain with this operator.
                let lhs_min = if chain_parts(lhs).is_some() {
                    u8::MAX
                } else if p == 4 {
                    p + 1
                } else {
                    p
                };
                self.expr(lhs, lhs_min, head);
                self.push(" ");
                self.push(bin_text(*op));
                self.push(" ");
                self.expr(rhs, p + 1, head);
            }
            ExprKind::Range { lo, hi } => {
                self.expr(lo, 2, head);
                self.push("..");
                self.expr(hi, 2, head);
            }
            ExprKind::Tuple(es) => {
                self.push("(");
                self.list(es, ", ", |p, e| p.expr(e, 0, false));
                if es.len() == 1 {
                    self.push(",");
                }
                self.push(")");
            }
            ExprKind::Array(es) => {
                self.push("[");
                self.list(es, ", ", |p, e| p.expr(e, 0, false));
                self.push("]");
            }
            ExprKind::StructLit { path, fields } => {
                self.list(path, ".", |p, s| p.push(&s.name));
                if fields.is_empty() {
                    self.push(" {}");
                } else {
                    self.push(" { ");
                    self.list(fields, ", ", |p, (n, v)| {
                        p.push(&n.name);
                        p.push(": ");
                        p.expr(v, 0, false);
                    });
                    self.push(" }");
                }
            }
            ExprKind::Closure { params, body } => {
                if params.is_empty() {
                    self.push("||");
                } else {
                    self.push("|");
                    self.list(params, ", ", Self::param);
                    self.push("|");
                }
                self.push(" ");
                self.expr(body, 0, false);
            }
            ExprKind::Block(b) => self.block(b),
            ExprKind::If { cond, then, else_ } => self.if_expr(cond, then, else_.as_deref()),
            ExprKind::Match { scrutinee, arms } => {
                self.push("match ");
                self.expr(scrutinee, 0, true);
                self.push(" ");
                self.brace_items(arms, |p, arm| {
                    p.pattern(&arm.pat);
                    p.push(" => ");
                    p.expr(&arm.body, 0, false);
                });
            }
            ExprKind::Handle {
                effect,
                clauses,
                body,
            } => {
                self.push("handle ");
                self.push(&effect.text());
                if clauses.is_empty() {
                    self.push(" {}");
                } else if self.inline {
                    self.push(" {");
                    for c in clauses {
                        self.push(" fn ");
                        self.push(&c.op.name);
                        self.params(&c.params);
                        self.push(" ");
                        self.block(&c.body);
                    }
                    self.push(" }");
                } else {
                    self.push(" {");
                    self.indent += 1;
                    for c in clauses {
                        self.newline();
                        self.push("fn ");
                        self.push(&c.op.name);
                        self.params(&c.params);
                        self.push(" ");
                        self.block(&c.body);
                    }
                    self.indent -= 1;
                    self.newline();
                    self.push("}");
                }
                self.push(" in ");
                self.expr(body, 0, false);
            }
            ExprKind::Scope { binder, body } => {
                self.push("scope ");
                self.stmts_in_braces(&body.stmts, &format!("{} =>", binder.name));
            }
        }
    }

    /// Writes an `if` chain. It loops over `else if`, so it does not recurse.
    fn if_expr(&mut self, cond: &Expr, then: &Block, else_: Option<&Expr>) {
        let (mut cond, mut then, mut else_) = (cond, then, else_);
        loop {
            self.push("if ");
            self.expr(cond, 0, true);
            self.push(" ");
            self.block(then);
            let Some(next) = else_ else { return };
            self.push(" else ");
            match &next.kind {
                ExprKind::If {
                    cond: c,
                    then: t,
                    else_: e,
                } => {
                    (cond, then, else_) = (c, t, e.as_deref());
                }
                ExprKind::Block(b) if chain_parts(next).is_none() => {
                    self.block(b);
                    return;
                }
                _ => {
                    self.push("{ ");
                    self.expr(next, 0, false);
                    self.push(" }");
                    return;
                }
            }
        }
    }

    /// Writes a part of a long chain after its first operand: ` + b + c`. The
    /// first operand is the hidden local of the part before it.
    fn chain_rest(&mut self, e: &Expr, head: bool) {
        let ExprKind::Binary { op, lhs, rhs } = &e.kind else {
            return;
        };
        if !matches!(&lhs.kind, ExprKind::Name(id) if is_chain_part(&id.name)) {
            self.chain_rest(lhs, head);
        }
        let p = bin_prec(*op);
        self.push(" ");
        self.push(bin_text(*op));
        self.push(" ");
        self.expr(rhs, p + 1, head);
    }

    fn args(&mut self, args: &[Arg]) {
        self.push("(");
        self.list(args, ", ", |p, a| {
            if let Some(n) = &a.name {
                p.push(&n.name);
                p.push(": ");
            }
            p.expr(&a.value, 0, false);
        });
        self.push(")");
    }

    fn trailing(&mut self, t: Option<&Expr>) {
        let Some(t) = t else { return };
        self.push(" ");
        match &t.kind {
            ExprKind::Closure { params, body } if params.is_empty() => {
                if let (ExprKind::Block(b), None) = (&body.kind, chain_parts(body)) {
                    self.block(b);
                } else {
                    self.push("{ ");
                    self.expr(body, 0, false);
                    self.push(" }");
                }
            }
            _ => {
                self.push("{ ");
                self.expr(t, 0, false);
                self.push(" }");
            }
        }
    }

    fn lit(&mut self, l: &Lit) {
        match l {
            Lit::Int(v) => self.push(&v.to_string()),
            Lit::Bool(b) => self.push(if *b { "true" } else { "false" }),
            Lit::Unit => self.push("()"),
            Lit::Str(parts) => {
                self.push("\"");
                for part in parts {
                    match part {
                        StrPart::Text(t) => self.push(&escape_text(t)),
                        StrPart::Interp(e) => {
                            let old = std::mem::replace(&mut self.inline, true);
                            self.push("{");
                            self.expr(e, 0, false);
                            self.push("}");
                            self.inline = old;
                        }
                    }
                }
                self.push("\"");
            }
        }
    }
}
