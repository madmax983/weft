//! Shared test helpers: parse wrappers and an S-expression printer.

#![allow(dead_code)]

use std::fmt::Write as _;

use weft_syntax::ast::{
    Arg, AssignOp, BinOp, Block, EffectItem, EffectRow, Expr, ExprKind, File, FnDecl, Item,
    ItemKind, Lit, Mode, Param, Pattern, PlaceExpr, PlaceStep, Stmt, StmtKind, StrPart, TypeExpr,
    TypeExprKind, UnOp,
};
use weft_syntax::{parse_file, ParseError};

/// Parses `src` and panics with the error and its location if it fails.
pub fn parse(src: &str) -> File {
    match parse_file(src) {
        Ok(f) => f,
        Err(e) => {
            let lo = (e.span.lo as usize).min(src.len());
            let hi = (e.span.hi as usize).clamp(lo, src.len());
            panic!(
                "parse failed: {} at {:?} ({:?})\n{src}",
                e.message,
                e.span,
                src.get(lo..hi)
            );
        }
    }
}

/// Parses `src` and returns the error. Panics if the parse succeeds.
pub fn parse_err(src: &str) -> ParseError {
    match parse_file(src) {
        Ok(f) => panic!("expected an error for {src:?}, got {f:#?}"),
        Err(e) => e,
    }
}

/// Returns the message of the error for `src`.
pub fn err_msg(src: &str) -> String {
    parse_err(src).message
}

/// Wraps `body` in a function and returns the statements of the body.
pub fn stmts(body: &str) -> Vec<Stmt> {
    let src = format!("fn t() {{\n{body}\n}}");
    let mut file = parse(&src);
    let item = file.items.remove(0);
    match item.kind {
        ItemKind::Fn(FnDecl { body: Some(b), .. }) => b.stmts,
        other => panic!("not a fn: {other:?}"),
    }
}

/// Returns the S-expression of the statements of a function body.
pub fn sx_body(body: &str) -> String {
    stmts(body)
        .iter()
        .map(sx_stmt)
        .collect::<Vec<_>>()
        .join("; ")
}

/// Returns the S-expression of one expression statement.
pub fn sx_expr(src: &str) -> String {
    let s = stmts(src);
    assert_eq!(s.len(), 1, "expected one statement in {src:?}: {s:#?}");
    match &s[0].kind {
        StmtKind::Expr(e) => sx(e),
        other => panic!("not an expression: {other:?}"),
    }
}

/// Returns the first function with this name in a file.
pub fn find_fn<'a>(file: &'a File, name: &str) -> &'a FnDecl {
    find_fn_in(&file.items, name).unwrap_or_else(|| panic!("no fn {name}"))
}

fn find_fn_in<'a>(items: &'a [Item], name: &str) -> Option<&'a FnDecl> {
    items.iter().find_map(|i| match &i.kind {
        ItemKind::Fn(f) if f.name.name == name => Some(f),
        ItemKind::Impl(b) => find_fn_in(&b.items, name),
        ItemKind::Mod(m) => find_fn_in(&m.items, name),
        _ => None,
    })
}

/// Returns the body statements of a function.
pub fn fn_body<'a>(file: &'a File, name: &str) -> &'a [Stmt] {
    find_fn(file, name)
        .body
        .as_ref()
        .map_or(&[], |b| b.stmts.as_slice())
}

/// S-expression of an expression.
pub fn sx(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Lit(l) => sx_lit(l),
        ExprKind::Name(id) => id.name.clone(),
        ExprKind::Field { base, name } => format!("(. {} {})", sx(base), name.name),
        ExprKind::Index {
            base,
            index: Some(i),
        } => format!("(idx {} {})", sx(base), sx(i)),
        ExprKind::Index { base, index: None } => format!("(idx {})", sx(base)),
        ExprKind::Call {
            callee,
            args,
            trailing,
        } => {
            format!(
                "(call {}{}{})",
                sx(callee),
                sx_args(args),
                sx_trailing(trailing.as_deref())
            )
        }
        ExprKind::MethodCall {
            receiver,
            method,
            args,
            trailing,
        } => format!(
            "(mcall {} {}{}{})",
            sx(receiver),
            method.name,
            sx_args(args),
            sx_trailing(trailing.as_deref())
        ),
        ExprKind::Unary { op, expr } => {
            let o = match op {
                UnOp::Neg => "-",
                UnOp::Not => "!",
                UnOp::Ref => "&",
            };
            format!("({o} {})", sx(expr))
        }
        ExprKind::Binary { op, lhs, rhs } => format!("({} {} {})", binop(*op), sx(lhs), sx(rhs)),
        ExprKind::Range { lo, hi } => format!("(.. {} {})", sx(lo), sx(hi)),
        ExprKind::Tuple(es) => format!("(tuple{})", sx_list(es)),
        ExprKind::Array(es) => format!("(array{})", sx_list(es)),
        ExprKind::StructLit { path, fields } => {
            let mut s = format!("(struct {}", path_s(path.iter().map(|i| i.name.as_str())));
            for (n, v) in fields {
                let _ = write!(s, " {}: {}", n.name, sx(v));
            }
            s.push(')');
            s
        }
        ExprKind::Closure { params, body } => format!("(fn [{}] {})", params_s(params), sx(body)),
        ExprKind::Block(b) => sx_block(b),
        ExprKind::If { cond, then, else_ } => {
            let tail = else_
                .as_ref()
                .map_or_else(String::new, |e| format!(" {}", sx(e)));
            format!("(if {} {}{tail})", sx(cond), sx_block(then))
        }
        ExprKind::Match { scrutinee, arms } => {
            let mut s = format!("(match {}", sx(scrutinee));
            for a in arms {
                let _ = write!(s, " ({} => {})", sx_pat(&a.pat), sx(&a.body));
            }
            s.push(')');
            s
        }
        ExprKind::Handle {
            effect,
            clauses,
            body,
        } => {
            let mut s = format!("(handle {}", effect.name);
            for c in clauses {
                let _ = write!(
                    s,
                    " ({} [{}] {})",
                    c.op.name,
                    params_s(&c.params),
                    sx_block(&c.body)
                );
            }
            let _ = write!(s, " in {})", sx(body));
            s
        }
        ExprKind::Scope { binder, body } => format!("(scope {} {})", binder.name, sx_block(body)),
    }
}

fn path_s<'a>(segs: impl Iterator<Item = &'a str>) -> String {
    segs.collect::<Vec<_>>().join(".")
}

fn sx_list(es: &[Expr]) -> String {
    es.iter().fold(String::new(), |mut out, e| {
        let _ = write!(out, " {}", sx(e));
        out
    })
}

fn sx_args(args: &[Arg]) -> String {
    args.iter().fold(String::new(), |mut out, a| {
        let name = a
            .name
            .as_ref()
            .map_or_else(String::new, |n| format!("{}: ", n.name));
        let _ = write!(out, " {name}{}", sx(&a.value));
        out
    })
}

fn sx_trailing(t: Option<&Expr>) -> String {
    t.map_or_else(String::new, |e| format!(" trailing {}", sx(e)))
}

const fn binop(op: BinOp) -> &'static str {
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

/// S-expression of a literal.
pub fn sx_lit(l: &Lit) -> String {
    match l {
        Lit::Int(v) => v.to_string(),
        Lit::Bool(b) => b.to_string(),
        Lit::Unit => "()".into(),
        Lit::Str(parts) => {
            let mut s = String::from("\"");
            for p in parts {
                match p {
                    StrPart::Text(t) => s.push_str(t),
                    StrPart::Interp(e) => {
                        let _ = write!(s, "{{{}}}", sx(e));
                    }
                }
            }
            s.push('"');
            s
        }
    }
}

/// S-expression of a block.
pub fn sx_block(b: &Block) -> String {
    format!(
        "{{{}}}",
        b.stmts.iter().map(sx_stmt).collect::<Vec<_>>().join("; ")
    )
}

/// S-expression of a statement.
pub fn sx_stmt(s: &Stmt) -> String {
    match &s.kind {
        StmtKind::Let { pat, ty, init } => {
            let mut out = format!("(let {}", sx_pat(pat));
            if let Some(t) = ty {
                let _ = write!(out, ": {}", sx_ty(t));
            }
            if let Some(i) = init {
                let _ = write!(out, " = {}", sx(i));
            }
            out.push(')');
            out
        }
        StmtKind::Expr(e) => sx(e),
        StmtKind::Assign { target, op, value } => {
            let o = match op {
                AssignOp::Assign => "=",
                AssignOp::Add => "+=",
                AssignOp::Sub => "-=",
                AssignOp::Mul => "*=",
            };
            format!("({o} {} {})", sx(target), sx(value))
        }
        StmtKind::Return(Some(e)) => format!("(return {})", sx(e)),
        StmtKind::Return(None) => "(return)".into(),
        StmtKind::Break => "break".into(),
        StmtKind::Continue => "continue".into(),
        StmtKind::While { cond, body } => format!("(while {} {})", sx(cond), sx_block(body)),
        StmtKind::For { pat, iter, body } => {
            format!("(for {} {} {})", sx_pat(pat), sx(iter), sx_block(body))
        }
        StmtKind::Loop(b) => format!("(loop {})", sx_block(b)),
        StmtKind::Assert(e) => format!("(assert {})", sx(e)),
    }
}

/// S-expression of a pattern.
pub fn sx_pat(p: &Pattern) -> String {
    match p {
        Pattern::Bind(id) => id.name.clone(),
        Pattern::Wild(_) => "_".into(),
        Pattern::Tuple(ps, _) => {
            format!("({})", ps.iter().map(sx_pat).collect::<Vec<_>>().join(", "))
        }
        Pattern::Variant { path, fields, .. } => {
            let p = path_s(path.iter().map(|i| i.name.as_str()));
            if fields.is_empty() {
                p
            } else {
                format!(
                    "{p}({})",
                    fields.iter().map(sx_pat).collect::<Vec<_>>().join(", ")
                )
            }
        }
        Pattern::Lit(l, _) => sx_lit(l),
    }
}

fn params_s(ps: &[Param]) -> String {
    ps.iter()
        .map(|p| {
            let ty =
                p.ty.as_ref()
                    .map_or_else(String::new, |t| format!(": {}", sx_ty(t)));
            format!("{}{ty}", p.name.name)
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Compact text of a type.
pub fn sx_ty(t: &TypeExpr) -> String {
    let mut s = match &t.kind {
        TypeExprKind::Path { segments, args } => {
            let mut s = path_s(segments.iter().map(|i| i.name.as_str()));
            if !args.is_empty() {
                let _ = write!(
                    s,
                    "<{}>",
                    args.iter().map(sx_ty).collect::<Vec<_>>().join(", ")
                );
            }
            s
        }
        TypeExprKind::Ref {
            inner,
            place: Some(p),
        } => {
            format!("(& {} in {})", sx_ty(inner), sx_place(p))
        }
        TypeExprKind::Ref { inner, place: None } => format!("(& {})", sx_ty(inner)),
        TypeExprKind::Tuple(ts) => {
            format!("({})", ts.iter().map(sx_ty).collect::<Vec<_>>().join(", "))
        }
        TypeExprKind::Array { elem, len } => format!("[{}; {len}]", sx_ty(elem)),
        TypeExprKind::Slice(e) => format!("[{}]", sx_ty(e)),
        TypeExprKind::Fn {
            params,
            ret,
            effects,
        } => {
            let mut s = format!(
                "(fn ({})",
                params.iter().map(sx_ty).collect::<Vec<_>>().join(", ")
            );
            if let Some(r) = ret {
                let _ = write!(s, " -> {}", sx_ty(r));
            }
            if let Some(e) = effects {
                let _ = write!(s, " / {}", sx_row(e));
            }
            s.push(')');
            s
        }
        TypeExprKind::SelfType => "Self".into(),
    };
    for m in &t.modes {
        let _ = write!(s, " @{}", mode_s(*m));
    }
    s
}

const fn mode_s(m: Mode) -> &'static str {
    match m {
        Mode::Uniq => "uniq",
        Mode::Aliased => "aliased",
        Mode::Portable => "portable",
        Mode::Nonportable => "nonportable",
        Mode::Uncontended => "uncontended",
        Mode::Shared => "shared",
        Mode::Once => "once",
        Mode::Many => "many",
    }
}

/// Compact text of a place.
pub fn sx_place(p: &PlaceExpr) -> String {
    let mut s = p.root.name.clone();
    for step in &p.steps {
        match step {
            PlaceStep::Field(n) => {
                let _ = write!(s, ".{}", n.name);
            }
            PlaceStep::Elem => s.push_str("[]"),
            PlaceStep::SegLo(n) => {
                let _ = write!(s, "[..{}]", n.name);
            }
            PlaceStep::SegHi(n) => {
                let _ = write!(s, "[{}..]", n.name);
            }
            PlaceStep::Wildcard => s.push_str(".."),
        }
    }
    s
}

/// Compact text of an effect row.
pub fn sx_row(r: &EffectRow) -> String {
    r.items
        .iter()
        .map(|i| match i {
            EffectItem::Mut(ps) => {
                format!(
                    "mut({})",
                    ps.iter().map(sx_place).collect::<Vec<_>>().join(", ")
                )
            }
            EffectItem::Named(n) => n.name.clone(),
        })
        .collect::<Vec<_>>()
        .join(", ")
}
