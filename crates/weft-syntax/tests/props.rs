//! Property tests: the lexer and the parser never panic, and printed trees
//! parse back to the same tree.

#![allow(clippy::unwrap_used)]

use std::fmt::Debug;
use std::fs;
use std::path::PathBuf;

use proptest::prelude::*;
use weft_syntax::ast::{
    Arg, Arm, AssignOp, BinOp, Block, EffectDecl, EffectItem, EffectRow, EnumDecl, Expr, ExprKind,
    ExternTypeDecl, FieldDecl, File, FnDecl, HandlerClause, Ident, ImplBlock, Item, ItemKind, Lit,
    ModDecl, Mode, OpDecl, Param, Pattern, PlaceExpr, PlaceStep, Span, Stmt, StmtKind, StrPart,
    StructDecl, TestDecl, TypeExpr, TypeExprKind, TypeProp, UnOp, VariantDecl,
};
use weft_syntax::lexer::lex;
use weft_syntax::parse_file;
use weft_syntax::parser::parse_expr;
use weft_syntax::pretty::{pretty, pretty_expr};

// ---------------------------------------------------------------- helpers

/// Returns the `Debug` text with every span (`lo..hi`) replaced by `_`.
fn erase<T: Debug>(x: &T) -> String {
    let s = format!("{x:?}");
    let b = s.as_bytes();
    let mut out = String::with_capacity(s.len());
    let (mut i, mut copied) = (0, 0);
    while i < b.len() {
        let starts = b[i].is_ascii_digit() && (i == 0 || !b[i - 1].is_ascii_alphanumeric());
        if starts {
            let mut j = i;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if b[j..].starts_with(b"..") && b.get(j + 2).is_some_and(u8::is_ascii_digit) {
                let mut k = j + 2;
                while k < b.len() && b[k].is_ascii_digit() {
                    k += 1;
                }
                out.push_str(&s[copied..i]);
                out.push('_');
                i = k;
                copied = k;
                continue;
            }
        }
        i += 1;
    }
    out.push_str(&s[copied..]);
    out
}

fn snippets() -> Vec<(String, String)> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/snippets");
    let mut out: Vec<_> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .map(|p| (p.display().to_string(), fs::read_to_string(&p).unwrap()))
        .collect();
    out.sort();
    out
}

/// Prints `file`, parses the text, and checks that the trees are equal.
fn check_round_trip(file: &File) -> Result<(), TestCaseError> {
    let text = pretty(file);
    let back = parse_file(&text)
        .map_err(|e| TestCaseError::fail(format!("{} at {:?} in:\n{text}", e.message, e.span)))?;
    prop_assert_eq!(erase(file), erase(&back), "text:\n{}", text);
    prop_assert_eq!(pretty(&back), text);
    Ok(())
}

#[test]
fn erase_replaces_spans_only() {
    assert_eq!(erase(&Span::new(3, 14)), "_");
    assert_eq!(erase(&"a1..2"), "\"a1..2\"");
    assert_eq!(
        erase(&(Span::new(1, 2), "é", Span::new(30, 40))),
        "(_, \"é\", _)"
    );
}

#[test]
fn snippets_round_trip() {
    for (name, src) in snippets() {
        let file = parse_file(&src).unwrap();
        if let Err(e) = check_round_trip(&file) {
            panic!("{name}: {e}");
        }
    }
}

#[test]
fn pretty_output_examples() {
    let f =
        parse_file("fn f(x: &T in a.b[] @ uniq) -> u32 / mut(a..), io { let y = (a + b) * c; y }")
            .unwrap();
    assert_eq!(
        pretty(&f),
        "fn f(x: &T in a.b[] @ uniq) -> u32 / mut(a..), io {\n    let y = (a + b) * c\n    y\n}\n"
    );
    let e = parse_expr("if (P {}).x { f(|| 1) { 2 } } else if y { \"a{ {1} }\\n\" }").unwrap();
    assert_eq!(
        pretty_expr(&e),
        "if (P {}).x {\n    f(|| 1) {\n        2\n    }\n} else if y {\n    \"a{{ 1 }}\\n\"\n}"
    );
    assert_eq!(pretty(&File::default()), "");
    let f = parse_file(
        "extern fn g(a: *T, b: &*T in p, c: *(T @ uniq), d: *(fn() / io)) -> *(fn()) / io",
    )
    .unwrap();
    assert_eq!(
        pretty(&f),
        "extern fn g(a: *T, b: &*T in p, c: *(T @ uniq), d: *(fn() / io)) -> *(fn()) / io\n"
    );
    check_round_trip(&f).unwrap();
    // Parentheses only where an inner reference would take the `in`.
    let f =
        parse_file("fn g(a: &&&T, b: &(&T) in p, c: &&T in a in b, d: &(*&T) in p) {}").unwrap();
    assert_eq!(
        pretty(&f),
        "fn g(a: &&&T, b: &(&T) in p, c: &&T in a in b, d: &(*&T) in p) {}\n"
    );
    check_round_trip(&f).unwrap();
}

#[test]
fn pretty_adds_needed_parentheses() {
    let cases = [
        ("(a.b)(c)", "(a.b)(c)"),
        ("a.b(c)", "a.b(c)"),
        ("(a..b)..c", "(a..b)..c"),
        ("(a < b) == c", "(a < b) == c"),
        ("a - (b - c)", "a - (b - c)"),
        ("-(a + b)", "-(a + b)"),
        ("(|| a)(b)", "(|| a)(b)"),
        ("(|| a) + b", "(|| a) + b"),
        ("a + (|| b)", "a + (|| b)"),
        ("(handle E {} in a).b", "(handle E {} in a).b"),
        ("&&x", "&&x"),
        ("(a, )", "(a,)"),
    ];
    for (src, want) in cases {
        assert_eq!(pretty_expr(&parse_expr(src).unwrap()), want, "for {src:?}");
    }
    let f = parse_file("fn f() { if (P {}) == x {}\n (|| a) = b\n while (f() {}) {} }").unwrap();
    assert_eq!(
        pretty(&f),
        "fn f() {\n    if (P {}) == x {}\n    (|| a) = b\n    while (f() {}) {}\n}\n"
    );
}

// ---------------------------------------------------------------- no panics

fn fragment() -> impl Strategy<Value = &'static str> {
    prop::sample::select(vec![
        "fn ",
        "let ",
        "if ",
        "else ",
        "while ",
        "for ",
        " in ",
        "loop ",
        "break",
        "continue",
        "return ",
        "match ",
        "struct ",
        "enum ",
        "effect ",
        "impl ",
        "mod ",
        "pub ",
        "extern ",
        "true",
        "false",
        "self",
        "Self",
        "handle ",
        "scope ",
        "linear ",
        "fip ",
        "multi ",
        "test ",
        "type ",
        "on ",
        "abort",
        "mut",
        "assert ",
        "uniq",
        "@",
        "x",
        "y",
        "Foo",
        "Bar",
        "1",
        "42",
        "2.s",
        "\"s\"",
        "\"a{x}b\"",
        "\"{\"",
        "(",
        ")",
        "[",
        "]",
        "{",
        "}",
        ",",
        ";",
        ":",
        ".",
        "..",
        "->",
        "=>",
        "=",
        "==",
        "!=",
        "<",
        "<=",
        ">",
        ">=",
        "+",
        "-",
        "*",
        "/",
        "%",
        "!",
        "&",
        "&&",
        "|",
        "||",
        "+=",
        "-=",
        "*=",
        "\n",
        " ",
        "// c\n",
        "_",
    ])
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn lexer_never_panics(s in any::<String>()) {
        let _ = lex(&s);
    }

    #[test]
    fn parser_never_panics(s in any::<String>()) {
        let _ = parse_file(&s);
        let _ = parse_expr(&s);
    }

    #[test]
    fn parser_never_panics_on_token_soup(parts in prop::collection::vec(fragment(), 0..120)) {
        let src = parts.concat();
        let _ = parse_expr(&src);
        if let Ok(file) = parse_file(&src) {
            check_round_trip(&file)?;
        }
    }

    #[test]
    fn parser_never_panics_on_damaged_snippets(
        which in 0usize..64,
        at in 0usize..2000,
        len in 0usize..12,
        insert in fragment(),
    ) {
        let all = snippets();
        let (_, src) = &all[which % all.len()];
        let mut s: Vec<char> = src.chars().collect();
        let at = at % (s.len() + 1);
        let end = (at + len).min(s.len());
        s.splice(at..end, insert.chars());
        let damaged: String = s.into_iter().collect();
        if let Ok(file) = parse_file(&damaged) {
            check_round_trip(&file)?;
        }
    }
}

// ---------------------------------------------------------------- generated trees

fn sp() -> Span {
    Span::default()
}

fn id(name: &str) -> Ident {
    Ident::new(name, sp())
}

fn ex(kind: ExprKind) -> Expr {
    Expr { kind, span: sp() }
}

fn lower() -> impl Strategy<Value = Ident> + Clone {
    prop::sample::select(&["a", "b", "x", "y", "foo", "bar_2", "_z"][..]).prop_map(id)
}

fn upper() -> impl Strategy<Value = Ident> + Clone {
    prop::sample::select(&["A", "B", "Foo", "Bar2"][..]).prop_map(id)
}

fn any_name() -> impl Strategy<Value = Ident> + Clone {
    prop_oneof![lower(), upper()]
}

fn field_name() -> impl Strategy<Value = Ident> + Clone {
    prop_oneof![any_name(), (0u64..3).prop_map(|v| id(&v.to_string()))]
}

fn text() -> impl Strategy<Value = String> + Clone {
    prop::collection::vec(
        prop::sample::select(&['a', 'b', ' ', '{', '}', '"', '\\', '\n', '\t', 'é', '/'][..]),
        1..5,
    )
    .prop_map(|v| v.into_iter().collect())
}

fn mode() -> impl Strategy<Value = Mode> + Clone {
    prop::sample::select(
        &[
            Mode::Uniq,
            Mode::Aliased,
            Mode::Portable,
            Mode::Nonportable,
            Mode::Uncontended,
            Mode::Shared,
            Mode::Once,
            Mode::Many,
        ][..],
    )
}

fn place() -> impl Strategy<Value = PlaceExpr> + Clone {
    let step = prop_oneof![
        field_name().prop_map(PlaceStep::Field),
        Just(PlaceStep::Elem),
        lower().prop_map(PlaceStep::SegLo),
        lower().prop_map(PlaceStep::SegHi),
    ];
    let root = prop_oneof![lower(), Just(id("self"))];
    (root, prop::collection::vec(step, 0..3), any::<bool>()).prop_map(|(root, mut steps, wild)| {
        if wild {
            steps.push(PlaceStep::Wildcard);
        }
        PlaceExpr {
            root,
            steps,
            span: sp(),
        }
    })
}

fn row() -> impl Strategy<Value = EffectRow> + Clone {
    let item = prop_oneof![
        prop::collection::vec(place(), 1..3).prop_map(EffectItem::Mut),
        any_name().prop_map(EffectItem::Named),
    ];
    prop::collection::vec(item, 1..3).prop_map(|items| EffectRow { items, span: sp() })
}

fn ty() -> impl Strategy<Value = TypeExpr> + Clone {
    let leaf = prop_oneof![
        prop::collection::vec(any_name(), 1..3).prop_map(|segments| TypeExprKind::Path {
            segments,
            args: Vec::new()
        }),
        Just(TypeExprKind::SelfType),
    ]
    .prop_map(|kind| TypeExpr {
        kind,
        modes: Vec::new(),
        span: sp(),
    });
    leaf.prop_recursive(3, 16, 3, |inner| {
        let kind = prop_oneof![
            (
                prop::collection::vec(upper(), 1..3),
                prop::collection::vec(inner.clone(), 1..3)
            )
                .prop_map(|(segments, args)| TypeExprKind::Path { segments, args }),
            (inner.clone(), prop::option::of(place())).prop_map(|(t, place)| TypeExprKind::Ref {
                inner: Box::new(t),
                place
            }),
            inner.clone().prop_map(|t| TypeExprKind::Ptr(Box::new(t))),
            prop::collection::vec(inner.clone(), 0..3).prop_map(TypeExprKind::Tuple),
            (inner.clone(), any::<u64>()).prop_map(|(t, len)| TypeExprKind::Array {
                elem: Box::new(t),
                len
            }),
            inner.clone().prop_map(|t| TypeExprKind::Slice(Box::new(t))),
            (
                prop::collection::vec(inner.clone(), 0..3),
                prop::option::of(inner),
                prop::option::of(row()),
            )
                .prop_map(|(params, ret, effects)| TypeExprKind::Fn {
                    params,
                    ret: ret.map(Box::new),
                    effects,
                }),
        ];
        (kind, prop::collection::vec(mode(), 0..3)).prop_map(|(kind, modes)| TypeExpr {
            kind,
            modes,
            span: sp(),
        })
    })
}

fn pattern() -> impl Strategy<Value = Pattern> + Clone {
    let leaf = prop_oneof![
        lower().prop_map(Pattern::Bind),
        Just(Pattern::Wild(sp())),
        any::<u64>().prop_map(|v| Pattern::Lit(Lit::Int(v), sp())),
        any::<bool>().prop_map(|v| Pattern::Lit(Lit::Bool(v), sp())),
        Just(Pattern::Lit(Lit::Unit, sp())),
        text().prop_map(|t| Pattern::Lit(Lit::Str(vec![StrPart::Text(t)]), sp())),
        prop::collection::vec(upper(), 1..3).prop_map(|path| Pattern::Variant {
            path,
            fields: Vec::new(),
            span: sp()
        }),
    ];
    leaf.prop_recursive(3, 12, 3, |inner| {
        prop_oneof![
            prop::collection::vec(inner.clone(), 1..3).prop_map(|ps| Pattern::Tuple(ps, sp())),
            (
                prop::collection::vec(upper(), 1..3),
                prop::collection::vec(inner, 1..3)
            )
                .prop_map(|(path, fields)| Pattern::Variant {
                    path,
                    fields,
                    span: sp()
                }),
        ]
    })
}

fn param() -> impl Strategy<Value = Param> + Clone {
    (
        prop_oneof![lower(), Just(id("self"))],
        prop::option::of(ty()),
    )
        .prop_map(|(name, ty)| Param {
            name,
            ty,
            span: sp(),
        })
}

fn block_of(stmt: impl Strategy<Value = Stmt> + Clone) -> impl Strategy<Value = Block> + Clone {
    prop::collection::vec(stmt, 0..3).prop_map(|stmts| Block { stmts, span: sp() })
}

fn st(kind: StmtKind) -> Stmt {
    Stmt { kind, span: sp() }
}

/// Statements whose sub-expressions come from `e`. Loop bodies hold only
/// expression statements, to keep the trees small.
fn stmt(e: impl Strategy<Value = Expr> + Clone + 'static) -> impl Strategy<Value = Stmt> + Clone {
    let simple = block_of(e.clone().prop_map(|x| st(StmtKind::Expr(x))));
    let op = prop::sample::select(
        &[
            AssignOp::Assign,
            AssignOp::Add,
            AssignOp::Sub,
            AssignOp::Mul,
        ][..],
    );
    prop_oneof![
        3 => e.clone().prop_map(|x| st(StmtKind::Expr(x))),
        1 => (pattern(), prop::option::of(ty()), prop::option::of(e.clone()))
            .prop_map(|(pat, ty, init)| st(StmtKind::Let { pat, ty, init })),
        1 => (e.clone(), op, e.clone())
            .prop_map(|(target, op, value)| st(StmtKind::Assign { target, op, value })),
        1 => prop::option::of(e.clone()).prop_map(|x| st(StmtKind::Return(x))),
        1 => Just(st(StmtKind::Break)),
        1 => Just(st(StmtKind::Continue)),
        1 => (e.clone(), simple.clone())
            .prop_map(|(cond, body)| st(StmtKind::While { cond, body })),
        1 => (pattern(), e.clone(), simple.clone())
            .prop_map(|(pat, iter, body)| st(StmtKind::For { pat, iter, body })),
        1 => simple.prop_map(|b| st(StmtKind::Loop(b))),
        1 => e.prop_map(|x| st(StmtKind::Assert(x))),
    ]
}

fn trailing_closure(b: Block) -> Expr {
    let body = Box::new(ex(ExprKind::Block(b)));
    ex(ExprKind::Closure {
        params: Vec::new(),
        body,
    })
}

fn args(e: impl Strategy<Value = Expr> + Clone) -> impl Strategy<Value = Vec<Arg>> + Clone {
    prop::collection::vec(
        (prop::option::of(lower()), e).prop_map(|(name, value)| Arg { name, value }),
        0..3,
    )
}

/// String parts with no empty text and no two texts in a row, as the parser makes.
fn str_parts(e: impl Strategy<Value = Expr> + Clone) -> impl Strategy<Value = Vec<StrPart>> {
    let part = prop_oneof![text().prop_map(StrPart::Text), e.prop_map(StrPart::Interp)];
    prop::collection::vec(part, 0..4).prop_map(|parts| {
        let mut out: Vec<StrPart> = Vec::new();
        for p in parts {
            match (out.last_mut(), p) {
                (Some(StrPart::Text(a)), StrPart::Text(b)) => a.push_str(&b),
                (_, p) => out.push(p),
            }
        }
        out
    })
}

fn expr() -> impl Strategy<Value = Expr> + Clone {
    let leaf = prop_oneof![
        any_name().prop_map(|i| ex(ExprKind::Name(i))),
        prop::sample::select(&["self", "Self"][..]).prop_map(|n| ex(ExprKind::Name(id(n)))),
        any::<u64>().prop_map(|v| ex(ExprKind::Lit(Lit::Int(v)))),
        any::<bool>().prop_map(|v| ex(ExprKind::Lit(Lit::Bool(v)))),
        Just(ex(ExprKind::Lit(Lit::Unit))),
        text().prop_map(|t| ex(ExprKind::Lit(Lit::Str(vec![StrPart::Text(t)])))),
    ];
    leaf.prop_recursive(4, 40, 3, |inner| {
        let block = block_of(stmt(inner.clone()));
        let unop = prop::sample::select(&[UnOp::Neg, UnOp::Not, UnOp::Ref][..]);
        let binop = prop::sample::select(
            &[
                BinOp::Add,
                BinOp::Sub,
                BinOp::Mul,
                BinOp::Div,
                BinOp::Rem,
                BinOp::Eq,
                BinOp::Ne,
                BinOp::Lt,
                BinOp::Le,
                BinOp::Gt,
                BinOp::Ge,
                BinOp::And,
                BinOp::Or,
            ][..],
        );
        let else_branch = prop_oneof![
            Just(None),
            block.clone().prop_map(|b| Some(Box::new(ex(ExprKind::Block(b))))),
            (inner.clone(), block.clone()).prop_map(|(c, t)| Some(Box::new(ex(ExprKind::If {
                cond: Box::new(c),
                then: t,
                else_: None,
            })))),
        ];
        let arm = (pattern(), inner.clone()).prop_map(|(pat, body)| Arm { pat, body, span: sp() });
        let clause = (lower(), prop::collection::vec(param(), 0..2), block.clone())
            .prop_map(|(op, params, body)| HandlerClause { op, params, body, span: sp() });
        prop_oneof![
            3 => (inner.clone(), field_name())
                .prop_map(|(b, name)| ex(ExprKind::Field { base: Box::new(b), name })),
            2 => (inner.clone(), prop::option::of(inner.clone())).prop_map(|(b, i)| ex(
                ExprKind::Index { base: Box::new(b), index: i.map(Box::new) }
            )),
            3 => (inner.clone(), args(inner.clone()), prop::option::of(block.clone())).prop_map(
                |(c, args, t)| ex(ExprKind::Call {
                    callee: Box::new(c),
                    args,
                    trailing: t.map(|b| Box::new(trailing_closure(b))),
                })
            ),
            3 => (inner.clone(), field_name(), args(inner.clone()), prop::option::of(block.clone()))
                .prop_map(|(r, method, args, t)| ex(ExprKind::MethodCall {
                    receiver: Box::new(r),
                    method,
                    args,
                    trailing: t.map(|b| Box::new(trailing_closure(b))),
                })),
            3 => (unop, inner.clone())
                .prop_map(|(op, e)| ex(ExprKind::Unary { op, expr: Box::new(e) })),
            6 => (binop, inner.clone(), inner.clone()).prop_map(|(op, l, r)| ex(ExprKind::Binary {
                op,
                lhs: Box::new(l),
                rhs: Box::new(r),
            })),
            2 => (inner.clone(), inner.clone())
                .prop_map(|(l, h)| ex(ExprKind::Range { lo: Box::new(l), hi: Box::new(h) })),
            1 => prop::collection::vec(inner.clone(), 1..3).prop_map(|es| ex(ExprKind::Tuple(es))),
            1 => prop::collection::vec(inner.clone(), 0..3).prop_map(|es| ex(ExprKind::Array(es))),
            1 => (prop::collection::vec(upper(), 1..3), prop::collection::vec((lower(), inner.clone()), 0..3))
                .prop_map(|(path, fields)| ex(ExprKind::StructLit { path, fields })),
            1 => (prop::collection::vec(param(), 0..3), inner.clone()).prop_map(|(params, b)| ex(
                ExprKind::Closure { params, body: Box::new(b) }
            )),
            1 => block.clone().prop_map(|b| ex(ExprKind::Block(b))),
            1 => (inner.clone(), block.clone(), else_branch).prop_map(|(c, then, else_)| ex(
                ExprKind::If { cond: Box::new(c), then, else_ }
            )),
            1 => (inner.clone(), prop::collection::vec(arm, 0..3)).prop_map(|(s, arms)| ex(
                ExprKind::Match { scrutinee: Box::new(s), arms }
            )),
            1 => (upper(), prop::collection::vec(clause, 0..2), inner.clone()).prop_map(
                |(effect, clauses, b)| ex(ExprKind::Handle { effect, clauses, body: Box::new(b) })
            ),
            1 => (lower(), block).prop_map(|(binder, body)| ex(ExprKind::Scope { binder, body })),
            1 => str_parts(inner).prop_map(|p| ex(ExprKind::Lit(Lit::Str(p)))),
        ]
    })
}

fn item(body: impl Strategy<Value = Block> + Clone + 'static) -> impl Strategy<Value = Item> {
    let generics = || prop::collection::vec(upper(), 0..3);
    let fn_decl = (
        lower(),
        generics(),
        prop::collection::vec(param(), 0..3),
        prop::option::of(ty()),
        prop::option::of(row()),
        prop::option::of(body.clone()),
        any::<bool>(),
    )
        .prop_map(|(name, generics, params, ret, effects, body, fip)| {
            let is_extern = body.is_none();
            FnDecl {
                name,
                generics,
                params,
                ret,
                effects,
                body,
                is_extern,
                is_fip: fip && !is_extern,
            }
        });
    let field = (lower(), ty()).prop_map(|(name, ty)| FieldDecl {
        name,
        ty,
        span: sp(),
    });
    let struct_decl = (
        upper(),
        generics(),
        prop::collection::vec(field, 0..3),
        any::<bool>(),
        any::<bool>(),
        prop::option::of(lower()),
    )
        .prop_map(
            |(name, generics, fields, is_linear, is_immovable, on_abort)| StructDecl {
                name,
                generics,
                fields,
                is_linear,
                is_immovable,
                on_abort,
            },
        );
    let variant =
        (upper(), prop::collection::vec(ty(), 0..3)).prop_map(|(name, fields)| VariantDecl {
            name,
            fields,
            span: sp(),
        });
    let enum_decl = (upper(), generics(), prop::collection::vec(variant, 0..3)).prop_map(
        |(name, generics, variants)| EnumDecl {
            name,
            generics,
            variants,
        },
    );
    let op = (
        lower(),
        prop::collection::vec(param(), 0..3),
        prop::option::of(ty()),
        any::<bool>(),
    )
        .prop_map(|(name, params, ret, is_multi)| OpDecl {
            name,
            params,
            ret,
            is_multi,
            span: sp(),
        });
    let effect =
        (upper(), prop::collection::vec(op, 0..3)).prop_map(|(name, ops)| EffectDecl { name, ops });
    let prop_ =
        (any_name(), prop::option::of(any_name())).prop_map(|(key, value)| TypeProp { key, value });
    let extern_type = (upper(), generics(), prop::collection::vec(prop_, 0..3)).prop_map(
        |(name, generics, props)| ExternTypeDecl {
            name,
            generics,
            props,
        },
    );
    let test = (text(), body).prop_map(|(name, body)| TestDecl { name, body });
    let leaf = prop_oneof![
        3 => fn_decl.prop_map(ItemKind::Fn),
        1 => struct_decl.prop_map(ItemKind::Struct),
        1 => enum_decl.prop_map(ItemKind::Enum),
        1 => effect.prop_map(ItemKind::Effect),
        1 => extern_type.prop_map(ItemKind::ExternType),
        1 => test.prop_map(ItemKind::Test),
    ];
    let item = (leaf, any::<bool>()).prop_map(|(kind, is_pub)| Item {
        kind,
        is_pub,
        span: sp(),
    });
    item.prop_recursive(2, 8, 3, |inner| {
        let kind = prop_oneof![
            (lower(), prop::collection::vec(inner.clone(), 0..3))
                .prop_map(|(name, items)| ItemKind::Mod(ModDecl { name, items })),
            (
                prop::collection::vec(upper(), 0..2),
                prop::collection::vec(upper(), 1..3),
                prop::collection::vec(inner, 0..3)
            )
                .prop_map(|(generics, segments, items)| ItemKind::Impl(ImplBlock {
                    generics,
                    self_ty: TypeExpr {
                        kind: TypeExprKind::Path {
                            segments,
                            args: Vec::new()
                        },
                        modes: Vec::new(),
                        span: sp(),
                    },
                    items,
                })),
        ];
        (kind, any::<bool>()).prop_map(|(kind, is_pub)| Item {
            kind,
            is_pub,
            span: sp(),
        })
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(600))]

    #[test]
    fn generated_expressions_round_trip(e in expr()) {
        let body = Block { stmts: vec![st(StmtKind::Expr(e))], span: sp() };
        let f = FnDecl {
            name: id("f"),
            generics: Vec::new(),
            params: Vec::new(),
            ret: None,
            effects: None,
            body: Some(body),
            is_extern: false,
            is_fip: false,
        };
        let file = File { items: vec![Item { kind: ItemKind::Fn(f), is_pub: false, span: sp() }] };
        check_round_trip(&file)?;
    }

    #[test]
    fn generated_statements_round_trip(stmts in prop::collection::vec(stmt(expr()), 0..4)) {
        let body = Block { stmts, span: sp() };
        let test = TestDecl { name: "t".into(), body };
        let file =
            File { items: vec![Item { kind: ItemKind::Test(test), is_pub: false, span: sp() }] };
        check_round_trip(&file)?;
    }

    #[test]
    fn generated_files_round_trip(
        items in prop::collection::vec(item(block_of(stmt(expr()))), 0..4)
    ) {
        check_round_trip(&File { items })?;
    }

    #[test]
    fn generated_types_round_trip(t in ty()) {
        let p = Param { name: id("x"), ty: Some(t), span: sp() };
        let f = FnDecl {
            name: id("f"),
            generics: Vec::new(),
            params: vec![p],
            ret: None,
            effects: None,
            body: None,
            is_extern: true,
            is_fip: false,
        };
        let file = File { items: vec![Item { kind: ItemKind::Fn(f), is_pub: false, span: sp() }] };
        check_round_trip(&file)?;
    }
}

/// Trees that the parser does not make still print as code that parses.
#[test]
fn pretty_prints_hand_built_trees() {
    let name = |n: &str| ex(ExprKind::Name(id(n)));
    let block = |e: Expr| Block {
        stmts: vec![st(StmtKind::Expr(e))],
        span: sp(),
    };
    let odd_else = ex(ExprKind::If {
        cond: Box::new(name("c")),
        then: block(name("a")),
        else_: Some(Box::new(name("b"))),
    });
    assert_eq!(pretty_expr(&odd_else), "if c {\n    a\n} else { b }");
    let odd_trailing = ex(ExprKind::Call {
        callee: Box::new(name("f")),
        args: Vec::new(),
        trailing: Some(Box::new(name("t"))),
    });
    assert_eq!(pretty_expr(&odd_trailing), "f() { t }");
    let closure = ex(ExprKind::Closure {
        params: Vec::new(),
        body: Box::new(name("t")),
    });
    let odd_body = ex(ExprKind::Call {
        callee: Box::new(name("f")),
        args: Vec::new(),
        trailing: Some(Box::new(closure)),
    });
    assert_eq!(pretty_expr(&odd_body), "f() { t }");
    for e in [odd_else, odd_trailing, odd_body] {
        assert!(parse_expr(&pretty_expr(&e)).is_ok());
    }
}
