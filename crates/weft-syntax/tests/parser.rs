//! Parser tests: statement ends, precedence, contextual keywords, items, types and errors.

#![allow(clippy::unwrap_used)]
// Weft string literals in these tests use `{x}` interpolation on purpose.
#![allow(clippy::literal_string_with_formatting_args)]

mod common;

use common::{
    assert_dense, err_msg, find_fn, parse, parse_err, stmts, sx, sx_body, sx_expr, sx_place,
    sx_row, sx_ty, Ids,
};
use weft_syntax::ast::{
    is_chain_part, EffectItem, ExprId, ExprKind, ItemKind, Lit, Mode, PatId, Pattern, PatternKind,
    PlaceStep, Span, StmtKind, StrPart, TypeExprKind,
};
use weft_syntax::parser::parse_expr;

// ---------------------------------------------------------------- ids

/// A program with each kind of expression and pattern, interpolations in
/// strings and in patterns, trailing blocks and an `else if` chain.
const ID_PROGRAM: &str = r#"
effect Log { fn log(msg: String) }

impl Point {
    fn norm(self) -> u32 { self.x * self.x + self.y * self.y }
}

mod m {
    fn inner(p: Point) -> u32 { p.norm() }
}

fn all(v: &Vec<u32>, o: Opt) -> u32 / Log {
    let (a, (b, _)) = (1, (2, 3))
    let p = Point { x: a, y: b }
    let xs = [1, 2, 3]
    let f = |x: u32, y| x + y
    let r = &mut_free(v[0], v[], -a, !true)
    let s = "a {a + 1} and {"nested {b}"}"
    match o {
        Opt.Some(Pair(1, x)) => x,
        Some((y, _)) => y,
        "s{a}" => 0,
        None => 0,
        _ => 0,
    }
    for i in 0..10 { print(i) }
    while a < 3 && b > 1 || false { a += 1 }
    loop { break }
    let h = handle Log { fn log(msg) { resume(()) } } in run(seed: 1) { log("x") }
    let t = if a == 1 { 1 } else if a == 2 { 2 } else { 3 }
    scope { sc => sc.spawn(|| 1) }
    assert a != 0
    xs.len().max(p.norm())
}

test "ids" { let z = 1
 assert z == 1 }
"#;

#[test]
fn ids_of_a_unit_are_unique_and_dense() {
    let file = parse(ID_PROGRAM);
    let ids = Ids::of_file(&file);
    assert!(ids.exprs.len() > 100, "{}", ids.exprs.len());
    assert!(ids.pats.len() > 15, "{}", ids.pats.len());
    assert_dense("expression", &ids.exprs);
    assert_dense("pattern", &ids.pats);
}

#[test]
fn ids_of_each_snippet_are_unique_and_dense() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/snippets");
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        let Ok(file) = weft_syntax::parse_file(&std::fs::read_to_string(&path).unwrap()) else {
            continue;
        };
        let ids = Ids::of_file(&file);
        assert_dense(&format!("expression ({})", path.display()), &ids.exprs);
        assert_dense(&format!("pattern ({})", path.display()), &ids.pats);
    }
}

#[test]
fn ids_start_again_in_each_unit() {
    let one = Ids::of_file(&parse("fn f() { let x = 1\n x }"));
    let two = Ids::of_file(&parse("fn g() { let (a, b) = (2, 3) }"));
    assert_dense("expression", &one.exprs);
    assert_dense("expression", &two.exprs);
    assert_dense("pattern", &two.pats);
    assert!(one.exprs.contains(&0) && two.exprs.contains(&0));
    assert!(one.pats.contains(&0) && two.pats.contains(&0));
}

#[test]
fn ids_of_one_expression_are_dense() {
    let e = parse_expr("f(a, \"{b + 1}\") { match c { Some(x) => x, _ => 0 } }").unwrap();
    let ids = Ids::of_expr(&e);
    assert_dense("expression", &ids.exprs);
    assert_dense("pattern", &ids.pats);
    assert_eq!(ids.pats.len(), 3);
}

#[test]
fn hidden_locals_of_long_chains_get_ids() {
    let chain = format!("x{}", " + x".repeat(100));
    let f = parse(&format!("fn f() {{ let y = {chain}\n y }}"));
    let ids = Ids::of_file(&f);
    assert_dense("expression", &ids.exprs);
    assert_dense("pattern", &ids.pats);
    let body = &find_fn(&f, "f").body.as_ref().unwrap().stmts;
    let StmtKind::Let {
        init: Some(init), ..
    } = &body[0].kind
    else {
        panic!()
    };
    let ExprKind::Block(b) = &init.kind else {
        panic!("{}", sx(init))
    };
    let mut hidden = Vec::new();
    for s in &b.stmts {
        if let StmtKind::Let {
            pat:
                Pattern {
                    id,
                    kind: PatternKind::Bind(name),
                },
            ..
        } = &s.kind
        {
            assert!(is_chain_part(&name.name));
            hidden.push(*id);
        }
    }
    assert!(hidden.len() >= 3, "{}", hidden.len());
    // The `let y` pattern and the hidden locals: each has its own id.
    assert_eq!(ids.pats.len(), hidden.len() + 1);
    // Each hidden local is read by a name with its own id.
    let reads = Ids::of_expr(init);
    let names = 101 + hidden.len();
    let ops = 100;
    assert_eq!(reads.exprs.len(), names + ops + 1);
}

#[test]
fn equality_ignores_ids() {
    let e = parse_expr("a + b").unwrap();
    let mut other = e.clone();
    other.id = ExprId(e.id.0 + 7);
    assert_eq!(e, other);
    let s = stmts("let (a, b) = t");
    let StmtKind::Let { pat, .. } = &s[0].kind else {
        panic!()
    };
    let mut q = pat.clone();
    q.id = PatId(q.id.0 + 7);
    assert_eq!(*pat, q);
}

// ---------------------------------------------------------------- statement ends

#[test]
fn asi_method_chain_across_lines() {
    assert_eq!(
        sx_expr("world\n    .entities\n    .clear()"),
        "(mcall (. world entities) clear)"
    );
    assert_eq!(sx_body("a\n  // c\n  .b()\nd"), "(mcall a b); d");
}

#[test]
fn asi_newline_ends_statements() {
    assert_eq!(sx_body("a\nb\nc"), "a; b; c");
    assert_eq!(sx_body("a; b;; c;"), "a; b; c");
    assert_eq!(sx_body("\n\n a \n\n"), "a");
}

#[test]
fn asi_operator_at_line_end_continues() {
    assert_eq!(sx_body("a +\n b"), "(+ a b)");
    assert_eq!(sx_body("let x =\n 1"), "(let x = 1)");
    assert_eq!(sx_body("a &&\n b ||\n c"), "(|| (&& a b) c)");
}

#[test]
fn asi_close_brace_newline_else() {
    assert_eq!(sx_body("if a {\n b\n}\nelse {\n c\n}"), "(if a {b} {c})");
    assert_eq!(
        sx_body("if a { b }\n\n else if c { d }\n else { e }"),
        "(if a {b} (if c {d} {e}))"
    );
    assert_eq!(sx_body("if a { b }; else { c }"), "(if a {b} {c})");
    assert_eq!(sx_body("if a { b }\nc"), "(if a {b}); c");
}

#[test]
fn asi_newlines_inside_parens_and_brackets() {
    assert_eq!(sx_body("f(a,\n b,\n)"), "(call f a b)");
    assert_eq!(sx_body("f(\n a\n)"), "(call f a)");
    assert_eq!(sx_body("[1,\n 2\n]"), "(array 1 2)");
    assert_eq!(sx_body("(a\n + b)"), "(+ a b)");
}

#[test]
fn asi_return_at_line_end() {
    assert_eq!(sx_body("return\nx"), "(return); x");
    assert_eq!(sx_body("return x"), "(return x)");
    assert_eq!(sx_body("{ return }"), "{(return)}");
    assert_eq!(sx_body("return; x"), "(return); x");
}

#[test]
fn asi_line_break_after_type_arguments_ends_a_statement() {
    assert_eq!(sx_body("let x: Vec<T>\nx"), "(let x: Vec<T>); x");
    assert_eq!(sx_body("let x: &T in w..\nx"), "(let x: (& T in w..)); x");
    // A next statement that starts with a step token (`[`, `.`, `..`) is a
    // new statement, not a step after the wildcard (a seed of the
    // `generated_statements_round_trip` property).
    assert_eq!(
        sx_body("let x: &T in w..\n[]"),
        "(let x: (& T in w..)); (array)"
    );
    let f = parse("struct S {\n a: Vec<T>\n b: u32\n}");
    let ItemKind::Struct(s) = &f.items[0].kind else {
        panic!()
    };
    assert_eq!(s.fields.len(), 2);
    let f = parse("effect E {\n fn a() -> Vec<T>\n fn b()\n}");
    let ItemKind::Effect(e) = &f.items[0].kind else {
        panic!()
    };
    assert_eq!(e.ops.len(), 2);
}

#[test]
fn asi_handle_in_on_next_line() {
    assert_eq!(
        sx_body("handle E { fn op(x) { resume(x) } }\nin run()"),
        "(handle E (op [x] {(call resume x)}) in (call run))"
    );
    assert_eq!(
        sx_body("handle E {\n fn a() { 1 }\n\n fn b(x, y) { 2 }\n}\n\nin go()"),
        "(handle E (a [] {1}) (b [x, y] {2}) in (call go))"
    );
}

#[test]
fn asi_on_abort_on_next_line() {
    let f = parse("linear struct T { a: u32 }\n\n  on abort = undo\nfn f() {}");
    let ItemKind::Struct(s) = &f.items[0].kind else {
        panic!()
    };
    assert_eq!(s.on_abort.as_ref().unwrap().name, "undo");
    assert_eq!(f.items.len(), 2);
    let f = parse("struct T {}\nfn on() {}");
    assert_eq!(f.items.len(), 2);
}

#[test]
fn trailing_block_must_start_on_the_same_line() {
    assert_eq!(sx_body("g()\n{ x }"), "(call g); {x}");
    assert_eq!(sx_body("g() { x }"), "(call g trailing (fn [] {x}))");
    assert_eq!(
        err_msg("fn f() { h(g()\n{ x }) }"),
        "expected `)` after arguments, found `{`"
    );
}

#[test]
fn trailing_block_on_method_and_chain_after_it() {
    assert_eq!(
        sx_body("a.b(1) { c }.d"),
        "(. (mcall a b 1 trailing (fn [] {c})) d)"
    );
    assert_eq!(sx_body("f() {}"), "(call f trailing (fn [] {}))");
}

// ---------------------------------------------------------------- precedence

#[test]
fn precedence_arithmetic() {
    assert_eq!(sx_expr("a + b * c"), "(+ a (* b c))");
    assert_eq!(sx_expr("a * b + c"), "(+ (* a b) c)");
    assert_eq!(sx_expr("a - b - c"), "(- (- a b) c)");
    assert_eq!(sx_expr("a / b % c * d"), "(* (% (/ a b) c) d)");
    assert_eq!(sx_expr("(a + b) * c"), "(* (+ a b) c)");
}

#[test]
fn precedence_logic_and_comparison() {
    assert_eq!(sx_expr("a || b && c"), "(|| a (&& b c))");
    assert_eq!(sx_expr("a && b || c"), "(|| (&& a b) c)");
    assert_eq!(sx_expr("a == b + 1"), "(== a (+ b 1))");
    assert_eq!(sx_expr("a < b && c >= d"), "(&& (< a b) (>= c d))");
    assert_eq!(sx_expr("a != b || c <= d"), "(|| (!= a b) (<= c d))");
    assert_eq!(sx_expr("a > b"), "(> a b)");
}

#[test]
fn precedence_prefix_and_postfix() {
    assert_eq!(sx_expr("-a.b"), "(- (. a b))");
    assert_eq!(sx_expr("!a && b"), "(&& (! a) b)");
    assert_eq!(
        sx_expr("&world.entities[0]"),
        "(& (idx (. world entities) 0))"
    );
    assert_eq!(sx_expr("--x"), "(- (- x))");
    assert_eq!(sx_expr("&&x"), "(& (& x))");
    assert_eq!(sx_expr("-a * b"), "(* (- a) b)");
    assert_eq!(sx_expr("!f(x)[1]"), "(! (idx (call f x) 1))");
}

#[test]
fn precedence_range_is_lowest() {
    assert_eq!(sx_expr("0..n + 1"), "(.. 0 (+ n 1))");
    assert_eq!(sx_expr("a || b..c && d"), "(.. (|| a b) (&& c d))");
}

#[test]
fn non_associative_operators() {
    let chained = "comparison operators cannot be chained; use `&&`";
    assert_eq!(err_msg("fn f() { a < b < c }"), chained);
    assert_eq!(err_msg("fn f() { a == b != c }"), chained);
    assert_eq!(
        err_msg("fn f() { a..b..c }"),
        "range operators cannot be chained; add parentheses"
    );
}

// ---------------------------------------------------------------- contextual keywords

#[test]
fn contextual_handle() {
    let f = parse("fn handle(req: Request) {}");
    assert_eq!(find_fn(&f, "handle").params[0].name.name, "req");
    assert_eq!(
        sx_expr("http.serve(x, handle)"),
        "(mcall http serve x handle)"
    );
    assert_eq!(
        sx_body("let handle = 1\nhandle + 1"),
        "(let handle = 1); (+ handle 1)"
    );
    assert_eq!(sx_expr("handle"), "handle");
    assert_eq!(sx_expr("handle.x"), "(. handle x)");
    assert_eq!(sx_expr("handle(x)"), "(call handle x)");
}

/// `handle {` has no effect name, so `handle` is a name there.
#[test]
fn contextual_handle_without_effect_name_is_a_name() {
    assert_eq!(
        err_msg("fn f() { handle { x } }"),
        "expected a line break or `;` after the statement, found `{`"
    );
}

#[test]
fn contextual_scope() {
    assert_eq!(
        sx_expr("scope { s => s.spawn(f) }"),
        "(scope s {(mcall s spawn f)})"
    );
    assert_eq!(sx_expr("scope {\n s =>\n a\n b\n}"), "(scope s {a; b})");
    assert_eq!(
        sx_body("let scope = 1\nscope.x"),
        "(let scope = 1); (. scope x)"
    );
    assert_eq!(sx_expr("f(scope)"), "(call f scope)");
}

#[test]
fn contextual_assert() {
    assert_eq!(sx_body("assert x == 1"), "(assert (== x 1))");
    assert_eq!(sx_body("assert(x)"), "(assert x)");
    assert_eq!(sx_body("assert !done"), "(assert (! done))");
    assert_eq!(sx_body("assert = 1"), "(= assert 1)");
    assert_eq!(sx_body("assert.check()"), "(mcall assert check)");
    assert_eq!(sx_body("assert\nx"), "assert; x");
    assert_eq!(sx_body("assert"), "assert");
    assert_eq!(sx_body("f(assert)"), "(call f assert)");
}

#[test]
fn contextual_item_words_are_names_elsewhere() {
    let f = parse("fn test() {}\nfn fip() {}\nfn linear(multi: u32, on: u32, abort: u32) {}");
    assert_eq!(f.items.len(), 3);
    assert_eq!(find_fn(&f, "linear").params.len(), 3);
    assert_eq!(
        sx_body("let type = linear + fip * multi"),
        "(let type = (+ linear (* fip multi)))"
    );
    assert_eq!(
        sx_body("let uniq = shared\nmut(x)"),
        "(let uniq = shared); (call mut x)"
    );
    assert_eq!(sx_body("test(1)"), "(call test 1)");
}

#[test]
fn test_items() {
    let f = parse("test \"a b\" { assert true }\npub test \"c\" {}");
    let ItemKind::Test(t) = &f.items[0].kind else {
        panic!()
    };
    assert_eq!(t.name, "a b");
    assert_eq!(t.body.stmts.len(), 1);
    assert!(f.items[1].is_pub);
}

// ---------------------------------------------------------------- strings

#[test]
fn interpolation_spans_are_absolute() {
    let src = "fn f() { \"a {x.y} b\" }";
    let f = parse(src);
    let body = &find_fn(&f, "f").body.as_ref().unwrap().stmts;
    let StmtKind::Expr(e) = &body[0].kind else {
        panic!()
    };
    assert_eq!(e.span, Span::new(9, 20));
    let ExprKind::Lit(Lit::Str(parts)) = &e.kind else {
        panic!()
    };
    let StrPart::Interp(inner) = &parts[1] else {
        panic!()
    };
    let lo = u32::try_from(src.find("x.y").unwrap()).unwrap();
    assert_eq!(inner.span, Span::new(lo, lo + 3));
    let ExprKind::Field { base, name } = &inner.kind else {
        panic!()
    };
    assert_eq!(base.span, Span::new(lo, lo + 1));
    assert_eq!(name.span, Span::new(lo + 2, lo + 3));
}

#[test]
fn nested_interpolation_spans() {
    let src = "\"{f(\"{y}\")}\"";
    let e = parse_expr(src).unwrap();
    let ExprKind::Lit(Lit::Str(parts)) = &e.kind else {
        panic!()
    };
    let StrPart::Interp(call) = &parts[0] else {
        panic!()
    };
    let ExprKind::Call { args, .. } = &call.kind else {
        panic!()
    };
    let ExprKind::Lit(Lit::Str(inner)) = &args[0].value.kind else {
        panic!()
    };
    let StrPart::Interp(y) = &inner[0] else {
        panic!()
    };
    let lo = u32::try_from(src.find('y').unwrap()).unwrap();
    assert_eq!(y.span, Span::new(lo, lo + 1));
    assert_eq!(sx(&e), "\"{(call f \"{y}\")}\"");
}

#[test]
fn interpolation_errors() {
    let e = parse_err("fn f() { \"a {} b\" }");
    assert!(e.message.contains("empty interpolation"), "{}", e.message);
    assert_eq!(e.span, Span::new(12, 14));
    let e = parse_err("fn f() { \"{a b}\" }");
    assert_eq!(
        e.message,
        "expected `}` to end the interpolation, found `b`"
    );
    assert_eq!(e.span, Span::new(13, 14));
    let e = parse_err("fn f() { \"{)}\" }");
    assert_eq!(e.message, "expected an expression, found `)`");
    assert_eq!(e.span, Span::new(11, 12));
    let e = parse_err("fn f() { \"{a\n}\" }");
    assert!(e.message.contains("interpolation"), "{}", e.message);
}

#[test]
fn string_patterns_and_literals() {
    assert_eq!(sx_body("let \"a\" = x"), "(let \"a\" = x)");
    assert_eq!(sx_expr("\"\""), "\"\"");
    assert_eq!(sx_expr("\"{a}{b}\""), "\"{a}{b}\"");
}

// ---------------------------------------------------------------- expressions

#[test]
fn literals_and_names() {
    assert_eq!(sx_expr("42"), "42");
    assert_eq!(sx_expr("true"), "true");
    assert_eq!(sx_expr("false"), "false");
    assert_eq!(sx_expr("()"), "()");
    assert_eq!(sx_expr("self"), "self");
    assert_eq!(sx_expr("Self.new()"), "(mcall Self new)");
    assert_eq!(sx_expr("_"), "_");
}

#[test]
fn tuples_arrays_and_parens() {
    assert_eq!(sx_expr("(a)"), "a");
    assert_eq!(sx_expr("(a,)"), "(tuple a)");
    assert_eq!(sx_expr("(a, b)"), "(tuple a b)");
    assert_eq!(sx_expr("(a, b,)"), "(tuple a b)");
    assert_eq!(sx_expr("[]"), "(array)");
    assert_eq!(sx_expr("[1, 2, 3,]"), "(array 1 2 3)");
    assert_eq!(sx_expr("(a, b).0"), "(. (tuple a b) 0)");
}

#[test]
fn paren_span_covers_the_parens() {
    let e = parse_expr("(a + b)").unwrap();
    assert_eq!(e.span, Span::new(0, 7));
}

#[test]
fn postfix_forms() {
    assert_eq!(sx_expr("t.0.1"), "(. (. t 0) 1)");
    assert_eq!(sx_expr("2.s"), "(. 2 s)");
    assert_eq!(sx_expr("x[i][]"), "(idx (idx x i))");
    assert_eq!(sx_expr("f(a)(b)"), "(call (call f a) b)");
    assert_eq!(
        sx_expr("a.b.c(d).e[f]"),
        "(idx (. (mcall (. a b) c d) e) f)"
    );
    assert_eq!(sx_expr("x.0(y)"), "(mcall x 0 y)");
}

#[test]
fn named_arguments() {
    assert_eq!(
        sx_expr("f(seed: 42, x, n: a + 1)"),
        "(call f seed: 42 x n: (+ a 1))"
    );
    assert_eq!(sx_expr("s.run(seed: 1)"), "(mcall s run seed: 1)");
}

#[test]
fn closures() {
    assert_eq!(sx_expr("|| e"), "(fn [] e)");
    assert_eq!(sx_expr("| | e"), "(fn [] e)");
    assert_eq!(sx_expr("|x, y: u32| x + y"), "(fn [x, y: u32] (+ x y))");
    assert_eq!(sx_expr("|x,| x"), "(fn [x] x)");
    assert_eq!(sx_expr("|| || 1"), "(fn [] (fn [] 1))");
    assert_eq!(sx_expr("f(|x| x, || y)"), "(call f (fn [x] x) (fn [] y))");
    assert_eq!(sx_expr("|| a = 1"), "(fn [] {(= a 1)})");
    assert_eq!(sx_expr("|| a -= 1"), "(fn [] {(-= a 1)})");
    assert_eq!(sx_expr("|| a *= 2"), "(fn [] {(*= a 2)})");
    assert_eq!(sx_expr("|| { x }"), "(fn [] {x})");
}

#[test]
fn struct_literals() {
    assert_eq!(sx_expr("Point { x: 1, y: 2 }"), "(struct Point x: 1 y: 2)");
    assert_eq!(sx_expr("Point {}"), "(struct Point)");
    assert_eq!(
        sx_expr("Point {\n x: 1\n y: 2\n}"),
        "(struct Point x: 1 y: 2)"
    );
    assert_eq!(sx_expr("Point { x: 1, }"), "(struct Point x: 1)");
    assert_eq!(
        sx_expr("Shape.Circle { r: 1 }"),
        "(struct Shape.Circle r: 1)"
    );
    assert_eq!(
        sx_body("let p = P { a: Q {} }"),
        "(let p = (struct P a: (struct Q)))"
    );
    // Lowercase names are never struct literals.
    assert_eq!(
        err_msg("fn f() { p { x: 1 } }"),
        "expected a line break or `;` after the statement, found `{`"
    );
    // `{` not followed by `NAME :` or `}` is not a struct literal.
    assert_eq!(
        err_msg("fn f() { Foo { x } }"),
        "expected a line break or `;` after the statement, found `{`"
    );
    assert_eq!(sx_body("Foo\n{ x }"), "Foo; {x}");
    assert_eq!(sx_body("Shape.Circle"), "(. Shape Circle)");
}

#[test]
fn no_struct_literal_or_trailing_block_in_heads() {
    assert_eq!(sx_body("if x == Foo {}"), "(if (== x Foo) {})");
    assert_eq!(
        sx_body("if x == (Foo {}) {}"),
        "(if (== x (struct Foo)) {})"
    );
    assert_eq!(
        sx_body("if x.ready() { go() }"),
        "(if (mcall x ready) {(call go)})"
    );
    assert_eq!(sx_body("while f() { g() }"), "(while (call f) {(call g)})");
    assert_eq!(
        sx_body("for e in xs.iter() { e }"),
        "(for e (mcall xs iter) {e})"
    );
    assert_eq!(sx_body("match f() { A => 1 }"), "(match (call f) (A => 1))");
    assert_eq!(sx_body("while Foo {}"), "(while Foo {})");
    assert_eq!(
        sx_body("if f(|| P {}) {}"),
        "(if (call f (fn [] (struct P))) {})"
    );
    assert_eq!(
        sx_body("if [P {}] == a {}"),
        "(if (== (array (struct P)) a) {})"
    );
    assert_eq!(
        sx_body("if a { P {} } else { P {} }"),
        "(if a {(struct P)} {(struct P)})"
    );
}

#[test]
fn if_else_chains() {
    assert_eq!(sx_expr("if a { 1 }"), "(if a {1})");
    assert_eq!(sx_expr("if a { 1 } else { 2 }"), "(if a {1} {2})");
    assert_eq!(
        sx_expr("if a { 1 } else if b { 2 } else if c { 3 } else { 4 }"),
        "(if a {1} (if b {2} (if c {3} {4})))"
    );
    assert_eq!(
        sx_expr("if a { 1 } else if b { 2 }"),
        "(if a {1} (if b {2}))"
    );
    assert_eq!(
        sx_body("let x = if a { 1 } else { 2 }"),
        "(let x = (if a {1} {2}))"
    );
}

#[test]
fn if_spans() {
    let src = "if a { 1 } else if b { 2 }";
    let e = parse_expr(src).unwrap();
    let end = u32::try_from(src.len()).unwrap();
    assert_eq!(e.span, Span::new(0, end));
    let ExprKind::If {
        else_: Some(inner), ..
    } = &e.kind
    else {
        panic!()
    };
    assert_eq!(inner.span, Span::new(16, end));
}

#[test]
fn match_arms() {
    assert_eq!(
        sx_expr("match x { A => 1, B(y) => y, _ => 0 }"),
        "(match x (A => 1) (B(y) => y) (_ => 0))"
    );
    assert_eq!(
        sx_expr("match x {\n A => 1\n E.B(y, _) => { y }\n\n 3 => 4,\n}"),
        "(match x (A => 1) (E.B(y, _) => {y}) (3 => 4))"
    );
    assert_eq!(sx_expr("match x {}"), "(match x)");
    assert_eq!(
        sx_expr("match x { () => 1, (a, (b, c)) => a, \"s\" => 2, true => 3 }"),
        "(match x (() => 1) ((a, (b, c)) => a) (\"s\" => 2) (true => 3))"
    );
}

#[test]
fn patterns() {
    assert_eq!(sx_body("let (a, b) = t"), "(let (a, b) = t)");
    assert_eq!(sx_body("let (a) = t"), "(let a = t)");
    assert_eq!(sx_body("let (a,) = t"), "(let (a) = t)");
    assert_eq!(sx_body("let Some(x) = o"), "(let Some(x) = o)");
    assert_eq!(sx_body("let Opt.Some(x,) = o"), "(let Opt.Some(x) = o)");
    assert_eq!(sx_body("let None = o"), "(let None = o)");
    assert_eq!(sx_body("let _ = o"), "(let _ = o)");
    assert_eq!(sx_body("let 1 = o"), "(let 1 = o)");
    assert_eq!(sx_body("let false = o"), "(let false = o)");
    assert_eq!(sx_body("let x: u32"), "(let x: u32)");
    assert_eq!(sx_body("let x"), "(let x)");
    let s = stmts("let (a, _) = t");
    let StmtKind::Let {
        pat: Pattern {
            kind: PatternKind::Tuple(ps, span),
            ..
        },
        ..
    } = &s[0].kind
    else {
        panic!()
    };
    assert_eq!(ps.len(), 2);
    assert_eq!(*span, Span::new(13, 19));
    assert!(matches!(ps[1].kind, PatternKind::Wild(_)));
    let s = stmts("let Some(x) = o");
    let StmtKind::Let { pat, .. } = &s[0].kind else {
        panic!()
    };
    assert_eq!(pat.span(), Span::new(13, 20));
}

#[test]
fn statements() {
    assert_eq!(
        sx_body("x = 1\nx += 2\nx -= 3\nx *= 4"),
        "(= x 1); (+= x 2); (-= x 3); (*= x 4)"
    );
    assert_eq!(sx_body("a.b[0] = c"), "(= (idx (. a b) 0) c)");
    assert_eq!(
        sx_body("loop { break\ncontinue }"),
        "(loop {break; continue})"
    );
    assert_eq!(
        sx_body("while i < n { i += 1 }"),
        "(while (< i n) {(+= i 1)})"
    );
    assert_eq!(
        sx_body("for (i, x) in 0..n { f(i) }"),
        "(for (i, x) (.. 0 n) {(call f i)})"
    );
    assert_eq!(
        sx_body("for e in world.entities[] {}"),
        "(for e (idx (. world entities)) {})"
    );
    assert_eq!(sx_body("{ a }\n{ b }"), "{a}; {b}");
}

#[test]
fn statement_spans() {
    let s = stmts("  let x = a + b");
    assert_eq!(s[0].span, Span::new(11, 24));
    let s = stmts("x += 1 // c");
    assert_eq!(s[0].span, Span::new(9, 15));
}

#[test]
fn handle_and_scope_expressions() {
    assert_eq!(
        sx_body("let r = handle Choice { fn choose() { resume(true) } } in pick()"),
        "(let r = (handle Choice (choose [] {(call resume true)}) in (call pick)))"
    );
    assert_eq!(sx_body("handle E {} in x"), "(handle E in x)");
    assert_eq!(
        sx_body("handle E { fn f(a: u32) {} } in x + 1"),
        "(handle E (f [a: u32] {}) in (+ x 1))"
    );
    assert_eq!(sx_body("scope { s => }"), "(scope s {})");
}

#[test]
fn block_expression() {
    assert_eq!(sx_body("let x = { a; b }"), "(let x = {a; b})");
}

// ---------------------------------------------------------------- items

#[test]
fn fn_items() {
    let f = parse("pub fn f<T, U>(a: T, b: U,) -> (T, U) / io { (a, b) }");
    let d = find_fn(&f, "f");
    assert!(f.items[0].is_pub);
    assert_eq!(
        d.generics
            .iter()
            .map(|g| g.name.as_str())
            .collect::<Vec<_>>(),
        ["T", "U"]
    );
    assert_eq!(d.params.len(), 2);
    assert_eq!(sx_ty(d.ret.as_ref().unwrap()), "(T, U)");
    assert_eq!(sx_row(d.effects.as_ref().unwrap()), "io");
    assert!(!d.is_extern && !d.is_fip);
    assert_eq!(f.items[0].span, Span::new(0, 53));
    let f = parse("fn g() {}");
    let g = find_fn(&f, "g");
    assert!(g.ret.is_none() && g.effects.is_none() && g.generics.is_empty());
    assert_eq!(f.items[0].span, Span::new(0, 9));
}

#[test]
fn fip_and_extern_fns() {
    let f = parse(
        "fip fn a() {}\nextern fn b(x: u32) -> u32\nextern fn c<T>() / io, net\npub extern fn d()",
    );
    assert!(find_fn(&f, "a").is_fip);
    let b = find_fn(&f, "b");
    assert!(b.is_extern && b.body.is_none());
    assert_eq!(
        sx_row(find_fn(&f, "c").effects.as_ref().unwrap()),
        "io, net"
    );
    assert!(f.items[3].is_pub);
}

#[test]
fn extern_types() {
    let f = parse(
        "extern type A\nextern type B<T> { elem: unstable, linear, }\n\
         extern type C {\n deref: stable\n nonportable\n}\nextern type D {}",
    );
    let props: Vec<usize> = f
        .items
        .iter()
        .map(|i| match &i.kind {
            ItemKind::ExternType(t) => t.props.len(),
            _ => panic!(),
        })
        .collect();
    assert_eq!(props, [0, 2, 2, 0]);
    let ItemKind::ExternType(b) = &f.items[1].kind else {
        panic!()
    };
    assert_eq!(b.props[1].key.name, "linear");
    assert!(b.props[1].value.is_none());
}

#[test]
fn struct_items() {
    let f =
        parse("struct P<T> { x: T, y: T }\nstruct Q: !Move {}\nstruct R {\n a: u32,\n b: u32\n}");
    let ItemKind::Struct(p) = &f.items[0].kind else {
        panic!()
    };
    assert_eq!(p.generics.len(), 1);
    assert_eq!(p.fields.len(), 2);
    assert_eq!(p.fields[0].span, Span::new(14, 18));
    assert!(p.on_abort.is_none() && !p.is_linear);
    let ItemKind::Struct(q) = &f.items[1].kind else {
        panic!()
    };
    assert!(q.is_immovable);
    let ItemKind::Struct(r) = &f.items[2].kind else {
        panic!()
    };
    assert_eq!(r.fields.len(), 2);
}

#[test]
fn enum_items() {
    let f = parse("enum E<T> {\n A(T)\n B(u32, T),\n C\n}\nenum F {}");
    let ItemKind::Enum(e) = &f.items[0].kind else {
        panic!()
    };
    assert_eq!(e.variants.len(), 3);
    assert_eq!(e.variants[1].fields.len(), 2);
    assert_eq!(e.generics[0].name, "T");
}

#[test]
fn effect_items() {
    let f = parse("effect E {\n fn a(x: u32) -> u32\n multi fn b()\n fn multi()\n}");
    let ItemKind::Effect(e) = &f.items[0].kind else {
        panic!()
    };
    assert_eq!(e.ops.len(), 3);
    assert!(!e.ops[0].is_multi && e.ops[1].is_multi && !e.ops[2].is_multi);
    assert_eq!(e.ops[2].name.name, "multi");
    assert_eq!(sx_ty(e.ops[0].ret.as_ref().unwrap()), "u32");
}

#[test]
fn impl_and_mod_items() {
    let f = parse(
        "impl Point {\n pub fn new() -> Self { Point {} }\n\n fn x(self) -> u32 { self.x }\n}\n\
         mod m {\n mod n { fn f() {} }\n}\nimpl<T> List<T> {}",
    );
    let ItemKind::Impl(i) = &f.items[0].kind else {
        panic!()
    };
    assert!(i.generics.is_empty());
    assert_eq!(i.items.len(), 2);
    assert!(i.items[0].is_pub);
    assert_eq!(sx_ty(find_fn(&f, "new").ret.as_ref().unwrap()), "Self");
    let ItemKind::Mod(m) = &f.items[1].kind else {
        panic!()
    };
    assert_eq!(m.items.len(), 1);
    assert!(find_fn(&f, "f").body.is_some());
}

#[test]
fn items_on_one_line_and_semicolons() {
    let f = parse("fn a() {} fn b() {}; ; struct S {}");
    assert_eq!(f.items.len(), 3);
    assert_eq!(parse("").items.len(), 0);
    assert_eq!(parse("\n// c\n\n").items.len(), 0);
}

// ---------------------------------------------------------------- types

fn param_ty(src: &str) -> String {
    let f = parse(&format!("fn f(x: {src}) {{}}"));
    sx_ty(find_fn(&f, "f").params[0].ty.as_ref().unwrap())
}

#[test]
fn types() {
    assert_eq!(param_ty("u32"), "u32");
    assert_eq!(param_ty("http.Request"), "http.Request");
    assert_eq!(param_ty("Vec<Vec<T>>"), "Vec<Vec<T>>");
    assert_eq!(param_ty("Map<K, V,>"), "Map<K, V>");
    assert_eq!(param_ty("&World @ shared"), "(& World) @shared");
    assert_eq!(param_ty("T @ uniq portable"), "T @uniq @portable");
    assert_eq!(param_ty("[u8; 16]"), "[u8; 16]");
    assert_eq!(param_ty("&[T]"), "(& [T])");
    assert_eq!(param_ty("()"), "()");
    assert_eq!(param_ty("(A)"), "A");
    assert_eq!(param_ty("(A,)"), "(A)");
    assert_eq!(param_ty("(A, B)"), "(A, B)");
    assert_eq!(param_ty("Self"), "Self");
    assert_eq!(param_ty("&&T"), "(& (& T))");
    assert_eq!(param_ty("*Stmt"), "(* Stmt)");
    assert_eq!(param_ty("**T"), "(* (* T))");
    assert_eq!(param_ty("*&T in a"), "(* (& T in a))");
    assert_eq!(param_ty("&*T in a"), "(& (* T) in a)");
    assert_eq!(param_ty("*T @ uniq"), "(* T) @uniq");
    assert_eq!(param_ty("*(T @ uniq)"), "(* T @uniq)");
    assert_eq!(param_ty("Vec<*T>"), "Vec<(* T)>");
    assert_eq!(param_ty("*fn() -> T"), "(* (fn () -> T))");
    assert_eq!(param_ty("&&T in a in b"), "(& (& T in a) in b)");
    assert_eq!(param_ty("&(T @ uniq) @ many"), "(& T @uniq) @many");
    assert_eq!(param_ty("fn()"), "(fn ())");
    assert_eq!(param_ty("fn(A, B) -> C"), "(fn (A, B) -> C)");
    assert_eq!(param_ty("fn(A) / net"), "(fn (A) / net)");
    assert_eq!(
        param_ty("fn(A) -> B / (net, log)"),
        "(fn (A) -> B / net, log)"
    );
    assert_eq!(param_ty("fn() / mut(x.y)"), "(fn () / mut(x.y))");
    assert_eq!(param_ty("fn() / (mut(a), io,)"), "(fn () / mut(a), io)");
}

#[test]
fn type_modes_are_parsed() {
    let f = parse("fn f(x: T @ uniq aliased portable nonportable uncontended shared once many) {}");
    let ty = find_fn(&f, "f").params[0].ty.as_ref().unwrap();
    assert_eq!(
        ty.modes,
        [
            Mode::Uniq,
            Mode::Aliased,
            Mode::Portable,
            Mode::Nonportable,
            Mode::Uncontended,
            Mode::Shared,
            Mode::Once,
            Mode::Many
        ]
    );
    assert_eq!(ty.span, Span::new(8, 74));
}

#[test]
fn greater_equal_after_type_arguments_is_split() {
    assert_eq!(sx_body("let x: Vec<T>= y"), "(let x: Vec<T> = y)");
    assert_eq!(sx_body("let x: Vec<Vec<T>>= y"), "(let x: Vec<Vec<T>> = y)");
}

#[test]
fn places() {
    let place = |src: &str| -> String {
        let f = parse(&format!("fn f() / mut({src}) {{}}"));
        let row = find_fn(&f, "f").effects.clone().unwrap();
        let EffectItem::Mut(ps) = &row.items[0] else {
            panic!()
        };
        ps.iter().map(sx_place).collect::<Vec<_>>().join(", ")
    };
    assert_eq!(place("world.entities[]"), "world.entities[]");
    assert_eq!(place("self[..mid]"), "self[..mid]");
    assert_eq!(place("self[mid..]"), "self[mid..]");
    assert_eq!(place("world.."), "world..");
    assert_eq!(place("opt.Some"), "opt.Some");
    assert_eq!(place("t.0"), "t.0");
    assert_eq!(place("a, b.c,"), "a, b.c");
    let f = parse("fn f() / mut(t.0[]) {}");
    let row = find_fn(&f, "f").effects.clone().unwrap();
    let EffectItem::Mut(ps) = &row.items[0] else {
        panic!()
    };
    assert!(matches!(&ps[0].steps[0], PlaceStep::Field(n) if n.name == "0"));
    assert_eq!(ps[0].span, Span::new(13, 18));
    assert_eq!(row.span, Span::new(9, 19));
}

#[test]
fn effect_rows() {
    let f = parse("fn f() / mut(e), Log, par {}");
    assert_eq!(
        sx_row(find_fn(&f, "f").effects.as_ref().unwrap()),
        "mut(e), Log, par"
    );
    let f = parse("fn f() / mut {}");
    assert_eq!(sx_row(find_fn(&f, "f").effects.as_ref().unwrap()), "mut");
}

#[test]
fn ref_type_kinds() {
    let f = parse("fn f(x: &T in a.b) {}");
    let ty = find_fn(&f, "f").params[0].ty.as_ref().unwrap();
    let TypeExprKind::Ref { place: Some(p), .. } = &ty.kind else {
        panic!()
    };
    assert_eq!(p.root.name, "a");
    assert_eq!(ty.span, Span::new(8, 17));
}

// ---------------------------------------------------------------- errors

const ITEM: &str = "an item (`fn`, `struct`, `enum`, `effect`, `impl`, `mod`, `extern` or `test`)";

#[test]
fn error_messages_for_items() {
    let cases: &[(&str, String)] = &[
        (
            "fn f() {",
            "expected `}` at the end of the block, found end of file".into(),
        ),
        (
            "fn f()",
            "expected `{` to start the function body, found end of file".into(),
        ),
        (
            "fn f()\n{}",
            "expected `{` to start the function body, found end of line".into(),
        ),
        ("let x = 1", format!("expected {ITEM}, found `let`")),
        ("pub", format!("expected {ITEM}, found end of file")),
        (
            "extern foo",
            "expected `fn` or `type` after `extern`, found `foo`".into(),
        ),
        (
            "extern fn f() {}",
            "an `extern fn` cannot have a body".into(),
        ),
        (
            "struct S: Move {}",
            "expected `!` after `:` in a struct header, found `Move`".into(),
        ),
        (
            "struct S: !Copy {}",
            "expected `Move` after `!`, found `Copy`".into(),
        ),
        (
            "struct S {} on x = f",
            "expected `abort` after `on`, found `x`".into(),
        ),
        (
            "struct S {} on abort f",
            "expected `=` after `on abort`, found `f`".into(),
        ),
        (
            "struct S { a }",
            "expected `:` after the field name, found `}`".into(),
        ),
        (
            "struct S { a: T b: T }",
            "expected `,`, a line break or `}` after the field, found `b`".into(),
        ),
        ("struct S { a: T", "expected `}`, found end of file".into()),
        ("struct S {", "expected `}`, found end of file".into()),
        (
            "enum E { A(T B) }",
            "expected `,` or `)` after a type, found `B`".into(),
        ),
        (
            "enum E { 1 }",
            "expected the variant name, found `1`".into(),
        ),
        (
            "effect E { let }",
            "expected `fn` to start an effect operation, found `let`".into(),
        ),
        (
            "effect E { multi x }",
            "expected `fn` to start an effect operation, found `multi`".into(),
        ),
        ("impl T { let }", format!("expected {ITEM}, found `let`")),
        (
            "impl T {",
            "expected `}` at the end of the item list, found end of file".into(),
        ),
        (
            "impl T x",
            "expected `{` to start the impl body, found `x`".into(),
        ),
        (
            "mod m x",
            "expected `{` to start the module body, found `x`".into(),
        ),
        ("mod 1 {}", "expected the module name, found `1`".into()),
        (
            "test \"a {b}\" {}",
            "a test name cannot contain interpolation".into(),
        ),
        (
            "fn f<T U>() {}",
            "expected `,` or `>` after a type parameter, found `U`".into(),
        ),
        (
            "fn f<1>() {}",
            "expected a type parameter name, found `1`".into(),
        ),
        ("fn f(1) {}", "expected a parameter name, found `1`".into()),
        (
            "fn f(a b) {}",
            "expected `,` or `)` after a parameter, found `b`".into(),
        ),
        ("fn () {}", "expected the function name, found `(`".into()),
        (
            "fn f {}",
            "expected `(` after the function name, found `{`".into(),
        ),
    ];
    for (src, want) in cases {
        assert_eq!(&parse_err(src).message, want, "for {src:?}");
    }
}

#[test]
fn error_messages_for_types_places_and_rows() {
    let cases: &[(&str, &str)] = &[
        (
            "fn f(x: T @ bogus) {}",
            "unknown mode `bogus`; expected one of uniq, aliased, portable, nonportable, \
             uncontended, shared, once, many",
        ),
        ("fn f(x: T @) {}", "expected a mode after `@`, found `)`"),
        (
            "fn f(x: Vec<T U>) {}",
            "expected `,` or `>` after a type argument, found `U`",
        ),
        ("fn f(x: 1) {}", "expected a type, found `1`"),
        (
            "fn f(x: [u8; n]) {}",
            "expected an integer array length after `;`, found `n`",
        ),
        (
            "fn f(x: [u8; 4 }) {}",
            "expected `]` after the array length, found `}`",
        ),
        (
            "fn f(x: [u8 16]) {}",
            "expected `]` after the element type, found `16`",
        ),
        (
            "fn f(x: fn) {}",
            "expected `(` after `fn` in a function type, found `)`",
        ),
        (
            "fn f(x: (A B)) {}",
            "expected `,` or `)` after a type, found `B`",
        ),
        (
            "fn f() / mut(w..x) {}",
            "expected `,` or `)` after a place, found `x`",
        ),
        (
            "fn f() / mut(w...x) {}",
            "the wildcard step `..` must be the last step",
        ),
        (
            "fn f() / mut(w..[]) {}",
            "the wildcard step `..` must be the last step",
        ),
        ("fn f() / mut() {}", "`mut(...)` needs at least one place"),
        ("fn f() / mut(1) {}", "expected a place, found `1`"),
        (
            "fn f() / mut(a.) {}",
            "expected a field name after `.` in a place, found `)`",
        ),
        (
            "fn f() / mut(a[b]) {}",
            "expected `]`, `..name]` or `name..]` in a place, found `b`",
        ),
        (
            "fn f() / mut(a[..b) {}",
            "expected `]` after the segment, found `)`",
        ),
        (
            "fn f() / mut(a[..1]) {}",
            "expected a split index name after `[..`, found `1`",
        ),
        (
            "fn f() / mut(a[b..) {}",
            "expected `]` after the segment, found `)`",
        ),
        (
            "fn f() / 1 {}",
            "expected an effect name or `mut(...)`, found `1`",
        ),
        (
            "fn f(g: fn() / ()) {}",
            "an effect row needs at least one effect",
        ),
        (
            "fn f(g: fn() / (a b)) {}",
            "expected `,` or `)` after an effect, found `b`",
        ),
    ];
    for (src, want) in cases {
        assert_eq!(&parse_err(src).message, want, "for {src:?}");
    }
}

#[test]
fn error_messages_for_statements_and_expressions() {
    let cases: &[(&str, &str)] = &[
        (
            "fn f() { g(a {) }",
            "expected `)` after arguments, found `{`",
        ),
        ("fn f() { let x = ) }", "expected an expression, found `)`"),
        ("fn f() { let = 1 }", "expected a pattern, found `=`"),
        (
            "fn f() { let (a b) = 1 }",
            "expected `,` or `)` after a pattern, found `b`",
        ),
        (
            "fn f() { x.) }",
            "expected a field or method name after `.`, found `)`",
        ),
        (
            "fn f() { a b }",
            "expected a line break or `;` after the statement, found `b`",
        ),
        ("fn f() { x[1 }", "expected `]` after the index, found `}`"),
        ("fn f() { (a b) }", "expected `,` or `)`, found `b`"),
        ("fn f() { [a b] }", "expected `,` or `]`, found `b`"),
        (
            "fn f() { handle E { fn op() {} } x }",
            "expected `in` after the handler, found `x`",
        ),
        (
            "fn f() { handle E { op() {} } in x }",
            "expected `fn` to start a handler clause, found `op`",
        ),
        (
            "fn f() { handle E { fn op() {}",
            "expected `}`, found end of file",
        ),
        (
            "fn f() { handle E { fn 1() {} } in x }",
            "expected the operation name, found `1`",
        ),
        (
            "fn f() { handle E { fn op {} } in x }",
            "expected `(` after the operation name, found `{`",
        ),
        (
            "fn f() { scope { s } }",
            "expected `=>` after the scope name, found `}`",
        ),
        (
            "fn f() { scope { 1 => x } }",
            "expected the scope name after `scope {`, found `1`",
        ),
        (
            "fn f() { |a b| a }",
            "expected `,` or `|` after a closure parameter, found `b`",
        ),
        (
            "fn f() { match x { A 1 } }",
            "expected `=>` after the pattern, found `1`",
        ),
        (
            "fn f() { match x { A => 1 B => 2 } }",
            "expected `,`, a line break or `}` after the match arm, found `B`",
        ),
        (
            "fn f() { match x y }",
            "expected `{` after the `match` value, found `y`",
        ),
        (
            "fn f() { P { a: 1 b: 2 } }",
            "expected `,`, a line break or `}` after the field, found `b`",
        ),
        (
            "fn f() { P { a 1 } }",
            "expected a line break or `;` after the statement, found `{`",
        ),
        ("fn f() { P { a: } }", "expected an expression, found `}`"),
        (
            "fn f() { P { a: 1, 2: 3 } }",
            "expected a field name, found `2`",
        ),
        (
            "fn f() { if a {} else x }",
            "expected `{` or `if` after `else`, found `x`",
        ),
        (
            "fn f() { if a b }",
            "expected `{` after the `if` condition, found `b`",
        ),
        (
            "fn f() { while a b }",
            "expected `{` after the `while` condition, found `b`",
        ),
        (
            "fn f() { for x of y {} }",
            "expected `in` after the `for` pattern, found `of`",
        ),
        (
            "fn f() { for x in y z }",
            "expected `{` after the `for` value, found `z`",
        ),
        ("fn f() { loop x }", "expected `{` after `loop`, found `x`"),
        ("fn f() { f(a: ) }", "expected an expression, found `)`"),
        ("fn f() { # }", "unexpected character `#`"),
    ];
    for (src, want) in cases {
        assert_eq!(&parse_err(src).message, want, "for {src:?}");
    }
}

#[test]
fn error_spans() {
    let e = parse_err("fn f() { g(a {) }");
    assert_eq!(e.span, Span::new(13, 14));
    let e = parse_err("fn f() {");
    assert_eq!(e.span, Span::new(8, 8));
    let e = parse_err("fn f()\n{}");
    assert_eq!(e.span, Span::new(6, 7));
    let e = parse_err("fn f(x: T @ bogus) {}");
    assert_eq!(e.span, Span::new(12, 17));
}

#[test]
fn deep_nesting_is_an_error_not_a_crash() {
    let deep = |open: &str, mid: &str, close: &str, n: usize| {
        format!("fn f() {{ {}{mid}{} }}", open.repeat(n), close.repeat(n))
    };
    let nested = "the code is nested too deeply";
    let long = "the expression is too long or nested too deeply; split it";
    for src in [
        deep("(", "x", ")", 5000),
        deep("[", "x", "]", 5000),
        deep("{", "x", "}", 5000),
        deep("|| ", "x", "", 5000),
        deep("-", "x", "", 100_000),
        deep("!", "x", "", 100_000),
        deep("&&", "x", "", 100_000),
        deep("if a { ", "x", " }", 5000),
        deep("f(", "x", ")", 5000),
        deep("", "x", ".y", 100_000),
        deep("", "x", "[0]", 100_000),
        deep("", "x", "()", 100_000),
        deep("\"{", "x", "}\"", 2000),
        deep("", "if a {} ", "else if b {} ", 100_000),
        format!("fn f(x: {}T) {{}}", "&".repeat(5000)),
        format!("fn f(x: {}T) {{}}", "&&".repeat(5000)),
        format!("fn f(x: {}T) {{}}", "*".repeat(5000)),
        format!("fn f(x: {}T) {{}}", "*&".repeat(5000)),
        format!("fn f(x: {}T{}) {{}}", "(".repeat(5000), ")".repeat(5000)),
        format!("fn f(x: {}T{}) {{}}", "Vec<".repeat(5000), ">".repeat(5000)),
        format!(
            "fn f() {{ let {}x{} = 1 }}",
            "(".repeat(5000),
            ")".repeat(5000)
        ),
        format!(
            "fn f() {{ let {}x{} = 1 }}",
            "A(".repeat(5000),
            ")".repeat(5000)
        ),
        format!("{}{}", "mod m { ".repeat(5000), "}".repeat(5000)),
    ] {
        let e = parse_err(&src);
        assert!(
            e.message == nested || e.message == long,
            "for {:?}: {}",
            &src[..40.min(src.len())],
            e.message
        );
    }
}

/// A flat chain of binary operators has no limit. The parser keeps each part of
/// 32 operators in a hidden local, and the printer prints the chain again.
#[test]
fn long_binary_chains_parse() {
    for (src, head) in [
        (
            format!("fn f() {{ x{} }}", " + x".repeat(100_000)),
            "x + x + x",
        ),
        (
            format!("fn f() {{ x{} }}", " || x".repeat(100_000)),
            "x || x",
        ),
        (format!("fn f() {{ {}x }}", "x * ".repeat(100_000)), "x * x"),
        (
            format!("fn f() {{ x{} }}", " - y * z".repeat(50_000)),
            "x - y * z - y * z",
        ),
    ] {
        let f = parse(&src);
        let text = weft_syntax::pretty::pretty(&f);
        assert!(text.contains(head), "{}", &text[..60]);
        assert_eq!(
            text.split_whitespace().collect::<String>(),
            src.split_whitespace().collect::<String>()
        );
        assert_eq!(weft_syntax::pretty::pretty(&parse(&text)), text);
    }
    // The hidden locals keep the value of each part, and the chain goes on.
    let src = format!("fn f() {{ a{} }}", " + b".repeat(40));
    let f = parse(&src);
    let body = &find_fn(&f, "f").body.as_ref().unwrap().stmts;
    let StmtKind::Expr(e) = &body[0].kind else {
        panic!()
    };
    let ExprKind::Block(b) = &e.kind else {
        panic!("{}", sx(e))
    };
    assert_eq!(b.stmts.len(), 2);
    let StmtKind::Let {
        pat: Pattern {
            kind: PatternKind::Bind(id),
            ..
        },
        init: Some(part),
        ..
    } = &b.stmts[0].kind
    else {
        panic!()
    };
    assert!(weft_syntax::ast::is_chain_part(&id.name));
    assert!(sx(part).starts_with("(+ (+ (+"));
    let StmtKind::Expr(rest) = &b.stmts[1].kind else {
        panic!()
    };
    assert_eq!(
        sx(rest),
        format!(
            "(+ (+ (+ (+ (+ (+ (+ (+ {} b) b) b) b) b) b) b) b)",
            id.name
        )
    );
    // A short chain stays one tree.
    assert_eq!(
        sx_expr_in(&format!("fn f() {{ a{} }}", " + b".repeat(2))),
        "(+ (+ a b) b)"
    );
    // In parentheses, a long chain binds like its last operator.
    let src = format!("fn f() {{ (a{}) * c }}", " + b".repeat(40));
    let text = weft_syntax::pretty::pretty(&parse(&src));
    assert!(text.contains(" + b) * c"), "{text}");
}

#[test]
fn moderate_nesting_is_fine() {
    let n = 40;
    let src = format!("fn f() {{ {}x{} }}", "(".repeat(n), ")".repeat(n));
    assert_eq!(sx_expr_in(&src), "x");
    parse(&format!("fn f() {{ {}x }}", "-".repeat(140)));
    parse(&format!("fn f() {{ x{} }}", " + x".repeat(300)));
    parse(&format!("fn f() {{ x{} }}", ".y()".repeat(140)));
    let src = format!("fn f() {{ if a {{}}{} }}", " else if b {}".repeat(140));
    parse(&src);
    parse(&format!("fn f() {{ {}x{} }}", "{".repeat(n), "}".repeat(n)));
    // A block costs one nesting level, like parentheses: about 96 levels.
    parse(&format!(
        "fn f() {{ {}x{} }}",
        "{".repeat(94),
        "}".repeat(94)
    ));
    parse(&format!(
        "fn f() {{ {}x{} }}",
        "(".repeat(94),
        ")".repeat(94)
    ));
    parse(&format!(
        "fn f() {{ {}x{} }}",
        "if a { ".repeat(94),
        " }".repeat(94)
    ));
}

fn sx_expr_in(src: &str) -> String {
    let f = parse(src);
    let body = &find_fn(&f, "f").body.as_ref().unwrap().stmts;
    let StmtKind::Expr(e) = &body[0].kind else {
        panic!()
    };
    sx(e)
}

#[test]
fn parse_expr_entry_point() {
    assert_eq!(sx(&parse_expr("a + b").unwrap()), "(+ a b)");
    assert_eq!(sx(&parse_expr("\n a \n").unwrap()), "a");
    assert_eq!(
        parse_expr("a b").unwrap_err().message,
        "expected end of input after the expression, found `b`"
    );
    assert_eq!(
        parse_expr("").unwrap_err().message,
        "expected an expression, found end of file"
    );
    assert!(parse_expr("\"").is_err());
}

#[test]
fn parse_error_display() {
    let e = parse_err("fn f(");
    assert_eq!(e.to_string(), e.message);
}

/// The worst inputs, and the deepest trees, fit in a 1.5 MB stack in a debug
/// build. `crates/weft-cli/tests/limits.rs` tests the stages after the parser.
#[test]
fn worst_inputs_fit_in_a_small_stack() {
    let cases = vec![
        format!("fn f() {{ {}x }}", "|| ".repeat(5000)),
        format!("fn f() {{ {}x{} }}", "\"{".repeat(2000), "}\"".repeat(2000)),
        format!("fn f() {{ {}x{} }}", "(".repeat(5000), ")".repeat(5000)),
        format!("fn f() {{ {}x{} }}", "{".repeat(5000), "}".repeat(5000)),
        format!("fn f() {{ x{} }}", " + x".repeat(100_000)),
        format!("fn f() {{ x{} }}", ".y".repeat(370)),
        format!("fn f() {{ {}x }}", "|| ".repeat(90)),
    ];
    for src in cases {
        let worker = std::thread::Builder::new()
            .stack_size(1536 * 1024)
            .spawn(move || {
                let r = weft_syntax::parse_file(&src);
                format!("{r:?}").len()
            });
        assert!(worker.unwrap().join().is_ok());
    }
}
