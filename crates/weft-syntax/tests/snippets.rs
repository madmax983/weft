//! Acceptance tests: every design doc snippet parses, with structural checks.

#![allow(clippy::unwrap_used)]

mod common;

use std::fs;
use std::path::PathBuf;

use common::{find_fn, fn_body, parse, sx, sx_pat, sx_place, sx_row, sx_stmt, sx_ty};
use weft_syntax::ast::{
    EffectItem, Expr, ExprKind, File, ItemKind, Lit, Mode, PlaceStep, Stmt, StmtKind, StrPart,
    TypeExprKind,
};

fn snippet_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/snippets")
}

fn load(name: &str) -> File {
    let src = fs::read_to_string(snippet_dir().join(name)).unwrap();
    parse(&src)
}

#[test]
fn every_snippet_parses() {
    let mut names: Vec<_> = fs::read_dir(snippet_dir())
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    names.sort();
    assert!(names.len() >= 11, "found only {} snippets", names.len());
    for path in names {
        let src = fs::read_to_string(&path).unwrap();
        if let Err(e) = weft_syntax::parse_file(&src) {
            panic!("{}: {} at {:?}", path.display(), e.message, e.span);
        }
    }
}

/// Returns the expression of an expression statement.
fn expr_stmt(s: &Stmt) -> &Expr {
    match &s.kind {
        StmtKind::Expr(e) => e,
        other => panic!("not an expression statement: {other:?}"),
    }
}

#[test]
fn s01_step_param_has_place_and_row() {
    let f = load("01_places.wf");
    let step = find_fn(&f, "step");
    assert_eq!(step.params.len(), 2);
    let e = &step.params[1];
    assert_eq!(e.name.name, "e");
    let ty = e.ty.as_ref().unwrap();
    let TypeExprKind::Ref {
        inner,
        place: Some(place),
    } = &ty.kind
    else {
        panic!("not a ref with a place: {ty:?}");
    };
    assert_eq!(sx_ty(inner), "Entity");
    assert_eq!(place.root.name, "world");
    assert_eq!(place.steps.len(), 2);
    assert!(matches!(&place.steps[0], PlaceStep::Field(n) if n.name == "entities"));
    assert_eq!(place.steps[1], PlaceStep::Elem);
    let row = step.effects.as_ref().unwrap();
    assert_eq!(row.items.len(), 1);
    let EffectItem::Mut(places) = &row.items[0] else {
        panic!("not mut: {row:?}")
    };
    assert_eq!(places.len(), 1);
    assert_eq!(sx_place(&places[0]), "e");
    let body = fn_body(&f, "step");
    assert_eq!(sx_stmt(&body[0]), "(mcall e advance)");
    assert_eq!(
        sx_stmt(&body[1]),
        "(let hit = (mcall world collision_for e))"
    );
}

#[test]
fn s01_tick_loop_and_compound_assignment() {
    let f = load("01_places.wf");
    let tick = find_fn(&f, "tick");
    assert_eq!(
        sx_row(tick.effects.as_ref().unwrap()),
        "mut(world.entities[], world.events, world.score)"
    );
    let body = fn_body(&f, "tick");
    assert_eq!(body.len(), 1);
    let StmtKind::For {
        pat,
        iter,
        body: loop_body,
    } = &body[0].kind
    else {
        panic!()
    };
    assert_eq!(sx_pat(pat), "e");
    assert_eq!(sx(iter), "(idx (. world entities))");
    assert_eq!(loop_body.stmts.len(), 2);
    let ExprKind::If {
        cond,
        then,
        else_: None,
    } = &expr_stmt(&loop_body.stmts[1]).kind
    else {
        panic!()
    };
    assert_eq!(sx(cond), "(<= (. e hp) 0)");
    assert_eq!(
        sx_stmt(&then.stmts[0]),
        "(mcall (. world events) push (call Died (. e id)))"
    );
    assert_eq!(sx_stmt(&then.stmts[1]), "(+= (. world score) 10)");
}

#[test]
fn s02_reference_to_an_element() {
    let f = load("02_bad.wf");
    let body = fn_body(&f, "bad");
    assert_eq!(
        sx_stmt(&body[0]),
        "(let first = (& (idx (. world entities) 0)))"
    );
    assert_eq!(
        sx_stmt(&body[1]),
        "(mcall (. world entities) push (mcall Entity new))"
    );
    assert_eq!(sx_stmt(&body[2]), "(call print (. first hp))");
}

#[test]
fn s03_modes_and_par() {
    let f = load("03_modes.wf");
    let total = find_fn(&f, "total_hp");
    let ty = total.params[0].ty.as_ref().unwrap();
    assert_eq!(ty.modes, vec![Mode::Shared]);
    assert!(matches!(ty.kind, TypeExprKind::Ref { place: None, .. }));
    assert_eq!(sx_ty(total.ret.as_ref().unwrap()), "u64");
    assert_eq!(sx_row(total.effects.as_ref().unwrap()), "par");
    let body = fn_body(&f, "total_hp");
    assert_eq!(
        sx_stmt(&body[0]),
        "(let (l, r) = (mcall (. world entities) split_at (/ (mcall (. world entities) len) 2)))"
    );
    assert_eq!(
        sx_stmt(&body[1]),
        "(let (a, b) = (call fork (fn [] (call sum_hp l)) (fn [] (call sum_hp r))))"
    );
    assert_eq!(sx_stmt(&body[2]), "(+ a b)");
    let heal = find_fn(&f, "heal_all");
    assert_eq!(
        sx_row(heal.effects.as_ref().unwrap()),
        "mut(world.entities[]), par"
    );
}

#[test]
fn s04_linear_struct_with_on_abort_on_next_line() {
    let f = load("04_linear.wf");
    let ItemKind::Struct(s) = &f.items[0].kind else {
        panic!()
    };
    assert!(s.is_linear);
    assert!(!s.is_immovable);
    assert_eq!(s.name.name, "Tx");
    assert_eq!(s.fields.len(), 2);
    assert_eq!(s.on_abort.as_ref().unwrap().name, "rollback");
    let tr = find_fn(&f, "transfer");
    assert_eq!(tr.params.len(), 4);
    assert_eq!(sx_row(tr.effects.as_ref().unwrap()), "io, fail");
    assert_eq!(fn_body(&f, "transfer").len(), 4);
}

#[test]
fn s05_handle_body_is_a_call_to_simulate() {
    let f = load("05_effects.wf");
    let ItemKind::Effect(eff) = &f.items[0].kind else {
        panic!()
    };
    assert_eq!(eff.name.name, "Log");
    assert_eq!(eff.ops.len(), 1);
    assert_eq!(eff.ops[0].name.name, "log");
    assert!(!eff.ops[0].is_multi);

    let sim = find_fn(&f, "simulate");
    assert_eq!(
        sx_row(sim.effects.as_ref().unwrap()),
        "mut(world.entities[]), Log"
    );
    let StmtKind::For { body, .. } = &fn_body(&f, "simulate")[0].kind else {
        panic!()
    };
    let ExprKind::Call { args, .. } = &expr_stmt(&body.stmts[1]).kind else {
        panic!()
    };
    let ExprKind::Lit(Lit::Str(parts)) = &args[0].value.kind else {
        panic!()
    };
    assert_eq!(parts.len(), 2);
    assert_eq!(parts[0], StrPart::Text("stepped ".into()));
    let StrPart::Interp(e) = &parts[1] else {
        panic!()
    };
    assert_eq!(sx(e), "(. e id)");

    let main = fn_body(&f, "main");
    assert_eq!(main.len(), 4);
    let ExprKind::Handle {
        effect,
        clauses,
        body,
    } = &expr_stmt(&main[2]).kind
    else {
        panic!("not a handle: {:?}", main[2]);
    };
    assert_eq!(effect.name, "Log");
    assert_eq!(clauses.len(), 1);
    assert_eq!(clauses[0].op.name, "log");
    assert_eq!(clauses[0].params.len(), 1);
    assert!(clauses[0].params[0].ty.is_none());
    assert_eq!(clauses[0].body.stmts.len(), 2);
    assert_eq!(sx(body), "(call simulate (& world))");
    let ExprKind::Call { callee, .. } = &body.kind else {
        panic!()
    };
    assert_eq!(sx(callee), "simulate");
    assert_eq!(sx_stmt(&main[3]), "(mcall (. env stdout) write_all lines)");
}

#[test]
fn s06_handle_as_a_name() {
    let f = load("06_http.wf");
    let main = fn_body(&f, "main");
    assert_eq!(
        sx_stmt(&main[0]),
        "(mcall http serve (mcall (. env net) listen \":8080\") handle)"
    );
    let h = find_fn(&f, "handle");
    assert_eq!(h.params[0].name.name, "req");
    assert_eq!(sx_ty(h.ret.as_ref().unwrap()), "Response");
    assert_eq!(sx_row(h.effects.as_ref().unwrap()), "net, log");
    let body = fn_body(&f, "handle");
    assert_eq!(
        sx_stmt(&body[1]),
        "(mcall log info \"served {(. user id)}\")"
    );
}

#[test]
fn s07_scope_and_trailing_closure() {
    let f = load("07_scopes.wf");
    let body = fn_body(&f, "profile_page");
    let ExprKind::Scope { binder, body } = &expr_stmt(&body[0]).kind else {
        panic!()
    };
    assert_eq!(binder.name, "s");
    assert_eq!(body.stmts.len(), 3);
    assert_eq!(
        sx_stmt(&body.stmts[0]),
        "(let user = (mcall s spawn (fn [] (mcall api user id))))"
    );
    assert_eq!(
        sx_stmt(&body.stmts[2]),
        "(call Page (mcall user join) (mcall posts join))"
    );

    let timed = fn_body(&f, "timed");
    let StmtKind::Let {
        init: Some(init), ..
    } = &timed[0].kind
    else {
        panic!()
    };
    let ExprKind::Call {
        callee,
        args,
        trailing: Some(t),
    } = &init.kind
    else {
        panic!()
    };
    assert_eq!(sx(callee), "with_timeout");
    assert_eq!(sx(&args[0].value), "(. 2 s)");
    let ExprKind::Closure { params, body } = &t.kind else {
        panic!("not a closure: {t:?}")
    };
    assert!(params.is_empty());
    let ExprKind::Block(b) = &body.kind else {
        panic!()
    };
    assert_eq!(b.stmts.len(), 1);
    assert_eq!(sx_stmt(&b.stmts[0]), "(call profile_page id)");
    assert_eq!(sx_stmt(&timed[1]), "page");
}

#[test]
fn s08_closure_body_with_assignment() {
    let f = load("08_ingest.wf");
    let body = fn_body(&f, "ingest");
    let ExprKind::Scope { body, .. } = &expr_stmt(&body[0]).kind else {
        panic!()
    };
    assert_eq!(
        sx_stmt(&body.stmts[0]),
        "(mcall s spawn (fn [] {(+= (. stats count) (mcall batch len))}))"
    );
    assert_eq!(
        sx_stmt(&body.stmts[2]),
        "(mcall s spawn (fn [] (call print (. stats count))))"
    );
}

#[test]
fn s09_extern_fn() {
    let f = load("09_blocking.wf");
    let ItemKind::Fn(d) = &f.items[0].kind else {
        panic!()
    };
    assert!(d.is_extern);
    assert!(d.body.is_none());
    assert_eq!(d.name.name, "sqlite3_step");
    assert_eq!(sx_ty(d.params[0].ty.as_ref().unwrap()), "(* Stmt)");
    assert_eq!(sx_ty(d.ret.as_ref().unwrap()), "i32");
    assert_eq!(sx_row(d.effects.as_ref().unwrap()), "blocking");
}

#[test]
fn s10_test_item_and_named_arg() {
    let f = load("10_sim.wf");
    let ItemKind::Test(t) = &f.items[0].kind else {
        panic!()
    };
    assert_eq!(t.name, "election survives a partition");
    let ExprKind::MethodCall {
        receiver,
        method,
        args,
        trailing: Some(tr),
    } = &expr_stmt(&t.body.stmts[0]).kind
    else {
        panic!()
    };
    assert_eq!(sx(receiver), "sim");
    assert_eq!(method.name, "run");
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].name.as_ref().unwrap().name, "seed");
    assert_eq!(sx(&args[0].value), "42");
    let ExprKind::Closure { body, .. } = &tr.kind else {
        panic!()
    };
    let ExprKind::Block(b) = &body.kind else {
        panic!()
    };
    assert_eq!(b.stmts.len(), 4);
    assert_eq!(
        sx_stmt(&b.stmts[1]),
        "(mcall (. sim net) partition (array 0 1) (array 2 3 4))"
    );
    assert_eq!(
        sx_stmt(&b.stmts[2]),
        "(mcall (. sim clock) advance (. 30 s))"
    );
    assert_eq!(
        sx_stmt(&b.stmts[3]),
        "(assert (== (mcall (mcall cluster leaders) len) 1))"
    );
}

#[test]
fn s11_misc_items() {
    let f = load("11_misc.wf");
    let kinds: Vec<&str> = f
        .items
        .iter()
        .map(|i| match &i.kind {
            ItemKind::Fn(_) => "fn",
            ItemKind::Struct(_) => "struct",
            ItemKind::Enum(_) => "enum",
            ItemKind::Effect(_) => "effect",
            ItemKind::Impl(_) => "impl",
            ItemKind::Mod(_) => "mod",
            ItemKind::Test(_) => "test",
            ItemKind::ExternType(_) => "extern type",
        })
        .collect();
    assert_eq!(
        kinds,
        [
            "extern type",
            "extern type",
            "impl",
            "struct",
            "enum",
            "effect",
            "mod",
            "fn",
            "fn",
            "fn"
        ]
    );
    let ItemKind::ExternType(v) = &f.items[0].kind else {
        panic!()
    };
    assert_eq!(v.name.name, "Vec");
    assert_eq!(v.generics[0].name, "T");
    assert_eq!(v.props[0].key.name, "elem");
    assert_eq!(v.props[0].value.as_ref().unwrap().name, "unstable");

    let ItemKind::Impl(imp) = &f.items[2].kind else {
        panic!()
    };
    assert_eq!(imp.generics[0].name, "T");
    assert_eq!(sx_ty(&imp.self_ty), "Vec<T>");
    assert_eq!(imp.items.len(), 3);
    let push = find_fn(&f, "push");
    assert_eq!(push.params[0].name.name, "self");
    assert!(push.params[0].ty.is_none());
    assert_eq!(sx_row(push.effects.as_ref().unwrap()), "mut(self)");
    let split = find_fn(&f, "split_mut");
    assert_eq!(
        sx_ty(split.ret.as_ref().unwrap()),
        "((& [T] in self[..mid]) @uniq, (& [T] in self[mid..]) @uniq)"
    );

    let ItemKind::Struct(fr) = &f.items[3].kind else {
        panic!()
    };
    assert!(fr.is_immovable);
    assert_eq!(sx_ty(&fr.fields[0].ty), "[u8; 16]");
    assert_eq!(sx_ty(&fr.fields[1].ty), "(& u8 in self.buf[])");

    let ItemKind::Enum(en) = &f.items[4].kind else {
        panic!()
    };
    assert_eq!(en.variants.len(), 3);
    assert_eq!(en.variants[1].fields.len(), 2);
    assert!(en.variants[2].fields.is_empty());

    let ItemKind::Effect(ch) = &f.items[5].kind else {
        panic!()
    };
    assert!(ch.ops[0].is_multi);
    assert_eq!(sx_ty(ch.ops[0].ret.as_ref().unwrap()), "bool");

    let ItemKind::Mod(m) = &f.items[6].kind else {
        panic!()
    };
    assert_eq!(m.name.name, "api");
    assert!(m.items[0].is_pub);

    let rev = find_fn(&f, "rev");
    assert!(rev.is_fip);
    assert_eq!(
        sx_stmt(&fn_body(&f, "rev")[0]),
        "(match xs (Cons(x, rest) => (call rev rest (call Cons x acc))) (Nil => acc))"
    );

    let wide = find_fn(&f, "wide");
    assert_eq!(sx_row(wide.effects.as_ref().unwrap()), "mut(world..)");
    let body = fn_body(&f, "wide");
    assert_eq!(
        sx_stmt(&body[0]),
        "(= (. world score) (+ (* (. world score) 2) 1))"
    );
    assert_eq!(
        sx_stmt(&body[1]),
        "(let msg = \"a {literal} brace and {(+ (. world score) 1)}\")"
    );
    assert_eq!(
        sx_stmt(&body[2]),
        "(while (&& (> (. world score) 0) (! (. world done))) {(-= (. world score) 1)})"
    );
    assert_eq!(sx_stmt(&body[3]), "(loop {break})");
    assert_eq!(sx_stmt(&body[4]), "(let f = (fn [x: u32, y] (+ x y)))");
    assert_eq!(sx_stmt(&body[5]), "(let g = (call fn_taking fn_value))");
    assert_eq!(sx_stmt(&body[6]), "(mcall (. world entities) clear)");
    assert_eq!(body.len(), 7);

    let hof = find_fn(&f, "hof");
    assert_eq!(
        sx_ty(hof.params[0].ty.as_ref().unwrap()),
        "(fn (Request) -> Response / net, log)"
    );
    assert_eq!(
        sx_ty(hof.params[1].ty.as_ref().unwrap()),
        "(fn () / mut(x))"
    );
}

#[test]
fn s11_string_escapes_are_text() {
    let f = load("11_misc.wf");
    let body = fn_body(&f, "wide");
    let StmtKind::Let {
        init: Some(init), ..
    } = &body[1].kind
    else {
        panic!()
    };
    let ExprKind::Lit(Lit::Str(parts)) = &init.kind else {
        panic!()
    };
    assert_eq!(parts[0], StrPart::Text("a {literal} brace and ".into()));
    assert!(matches!(parts[1], StrPart::Interp(_)));
}
