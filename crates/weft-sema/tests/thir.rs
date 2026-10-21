//! Tests of the THIR tables that the old lowering records (plan stage T3,
//! `weft_sema::thir`), and of test D0 (`weft_sema::thir::d0`).
//!
//! D0 on each program of tier 1 runs in `crates/weft-gate/tests/thir.rs`: it
//! needs the packages of the gate.

use weft_sema::thir::d0::{self, Check};
use weft_sema::thir::{
    Binder, Builtin, CallInfo, Callee, DerefKind, ExprId, FieldIdx, PatId, RecvMode, Res, Tables,
};
use weft_sema::{analyze_source, Analysis, Options};
use weft_syntax::ast::{Block, Expr, ExprKind, Pattern, PatternKind, Stmt, StmtKind};

/// Analyzes `src`.
fn analyze(src: &str) -> Analysis {
    analyze_source(src, Options::default())
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message))
}

/// The index of body `name`.
fn body(a: &Analysis, name: &str) -> usize {
    a.bodies
        .iter()
        .position(|b| b.facts.name == name)
        .unwrap_or_else(|| panic!("no body `{name}`"))
}

/// The syntax of body `i`.
fn block(a: &Analysis, i: usize) -> &Block {
    let f = a.bodies[i]
        .func
        .unwrap_or_else(|| panic!("body {i} is a test"));
    a.program.fns[f]
        .decl
        .body
        .as_ref()
        .unwrap_or_else(|| panic!("body {i} has no block"))
}

/// Calls `f` with each expression and each pattern of `b`.
fn walk(b: &Block, f: &mut dyn FnMut(Option<&Expr>, Option<&Pattern>)) {
    fn pat(p: &Pattern, f: &mut dyn FnMut(Option<&Expr>, Option<&Pattern>)) {
        f(None, Some(p));
        match &p.kind {
            PatternKind::Tuple(ps, _) => ps.iter().for_each(|q| pat(q, f)),
            PatternKind::Variant { fields, .. } => fields.iter().for_each(|q| pat(q, f)),
            _ => {}
        }
    }
    fn stmt(s: &Stmt, f: &mut dyn FnMut(Option<&Expr>, Option<&Pattern>)) {
        match &s.kind {
            StmtKind::Let { pat: p, init, .. } => {
                if let Some(e) = init {
                    expr(e, f);
                }
                pat(p, f);
            }
            StmtKind::Expr(e) | StmtKind::Assert(e) | StmtKind::Return(Some(e)) => expr(e, f),
            StmtKind::Assign { target, value, .. } => {
                expr(target, f);
                expr(value, f);
            }
            StmtKind::While { cond, body } => {
                expr(cond, f);
                walk(body, f);
            }
            StmtKind::For { pat: p, iter, body } => {
                expr(iter, f);
                pat(p, f);
                walk(body, f);
            }
            StmtKind::Loop(body) => walk(body, f),
            StmtKind::Return(None) | StmtKind::Break | StmtKind::Continue => {}
        }
    }
    fn expr(e: &Expr, f: &mut dyn FnMut(Option<&Expr>, Option<&Pattern>)) {
        f(Some(e), None);
        match &e.kind {
            ExprKind::Field { base, .. } => expr(base, f),
            ExprKind::Index { base, index } => {
                expr(base, f);
                if let Some(i) = index {
                    expr(i, f);
                }
            }
            ExprKind::Call {
                callee,
                args,
                trailing,
            } => {
                expr(callee, f);
                for a in args {
                    expr(&a.value, f);
                }
                if let Some(t) = trailing {
                    expr(t, f);
                }
            }
            ExprKind::MethodCall {
                receiver,
                args,
                trailing,
                ..
            } => {
                expr(receiver, f);
                for a in args {
                    expr(&a.value, f);
                }
                if let Some(t) = trailing {
                    expr(t, f);
                }
            }
            ExprKind::Unary { expr: x, .. } => expr(x, f),
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::Range { lo: lhs, hi: rhs } => {
                expr(lhs, f);
                expr(rhs, f);
            }
            ExprKind::Tuple(es) | ExprKind::Array(es) => es.iter().for_each(|x| expr(x, f)),
            ExprKind::StructLit { fields, .. } => fields.iter().for_each(|(_, x)| expr(x, f)),
            ExprKind::Closure { body, .. } => expr(body, f),
            ExprKind::Block(b) | ExprKind::Scope { body: b, .. } => walk(b, f),
            ExprKind::If { cond, then, else_ } => {
                expr(cond, f);
                walk(then, f);
                if let Some(x) = else_ {
                    expr(x, f);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                expr(scrutinee, f);
                for a in arms {
                    pat(&a.pat, f);
                    expr(&a.body, f);
                }
            }
            ExprKind::Handle { clauses, body, .. } => {
                expr(body, f);
                for c in clauses {
                    walk(&c.body, f);
                }
            }
            ExprKind::Lit(_) | ExprKind::Name(_) => {}
        }
    }
    for s in &b.stmts {
        stmt(s, f);
    }
}

/// A body with its source, to find its expressions by their text.
struct Body<'a> {
    src: &'a str,
    a: &'a Analysis,
    i: usize,
}

impl<'a> Body<'a> {
    fn new(src: &'a str, a: &'a Analysis, name: &str) -> Self {
        let i = body(a, name);
        Self { src, a, i }
    }

    fn t(&self) -> &'a Tables {
        &self.a.thir[self.i]
    }

    /// The first expression whose text is `text`.
    fn expr(&self, text: &str) -> ExprId {
        let mut found = None;
        walk(block(self.a, self.i), &mut |e, _| {
            if let (None, Some(e)) = (found, e) {
                if &self.src[e.span.lo as usize..e.span.hi as usize] == text {
                    found = Some(e.id);
                }
            }
        });
        found.unwrap_or_else(|| panic!("no expression `{text}`"))
    }

    /// The first pattern whose text is `text`.
    fn pat(&self, text: &str) -> PatId {
        let mut found = None;
        walk(block(self.a, self.i), &mut |_, p| {
            if let (None, Some(p)) = (found, p) {
                let s = p.span();
                if &self.src[s.lo as usize..s.hi as usize] == text {
                    found = Some(p.id);
                }
            }
        });
        found.unwrap_or_else(|| panic!("no pattern `{text}`"))
    }

    /// The type of expression `text`, as text.
    fn ty(&self, text: &str) -> String {
        let id = self.expr(text);
        let t = self
            .t()
            .expr_ty
            .get(&id)
            .unwrap_or_else(|| panic!("`{text}` has no type"));
        self.a.thir_tys.show(*t)
    }

    /// The dereferences of expression `text`.
    fn adjust(&self, text: &str) -> Vec<DerefKind> {
        self.t()
            .adjust
            .get(&self.expr(text))
            .cloned()
            .unwrap_or_default()
    }

    /// The call record of call `text`.
    fn call(&self, text: &str) -> &'a CallInfo {
        self.t()
            .call
            .get(&self.expr(text))
            .unwrap_or_else(|| panic!("`{text}` has no call record"))
    }

    /// The meaning of name `text`.
    fn res(&self, text: &str) -> &'a Res {
        self.t()
            .res
            .get(&self.expr(text))
            .unwrap_or_else(|| panic!("`{text}` has no meaning"))
    }

    /// The binding of the local that name `text` means.
    fn binding_of(&self, text: &str) -> (Binder, String, String) {
        let Res::Local(b) = self.res(text) else {
            panic!("`{text}` is not a local");
        };
        let b = &self.t().bindings[b.index()];
        (b.binder, b.name.clone(), self.a.thir_tys.show(b.ty))
    }

    /// Asserts that D0 holds on the body.
    fn d0_holds(&self) {
        let r = d0::d0(self.a);
        assert!(r.holds(), "{:#?}", r.findings);
        assert!(self.t().conflicts.is_empty(), "{:#?}", self.t().conflicts);
    }
}

#[test]
fn names_fields_and_operators_through_a_reference() {
    let src = "struct P { x: i64, y: i64 }\nfn get(p: &P) -> i64 { p.x + p.y }\n";
    let a = analyze(src);
    let b = Body::new(src, &a, "get");
    assert_eq!(b.ty("p.x + p.y"), "i64");
    assert_eq!(b.ty("p.x"), "i64");
    assert_eq!(b.ty("p"), "&P");
    assert_eq!(
        b.binding_of("p"),
        (Binder::Param(0), "p".into(), "&P".into())
    );
    assert_eq!(b.adjust("p"), vec![DerefKind::Ref]);
    assert_eq!(b.t().field.get(&b.expr("p.x")), Some(&FieldIdx::Field(0)));
    assert_eq!(
        b.t().int_ty.get(&b.expr("p.x + p.y")),
        Some(&weft_ir::IntTy::I64)
    );
    b.d0_holds();
}

#[test]
fn fields_through_box_and_rc() {
    let src = "struct P { x: i64, y: i64 }
fn f() -> i64 {
    let b = Box.new(P { x: 1, y: 2 })
    let h = Rc.new(P { x: 3, y: 4 })
    let t = (1, 2)
    b.y + h.x + t.1
}
";
    let a = analyze(src);
    let b = Body::new(src, &a, "f");
    assert_eq!(b.adjust("b"), vec![DerefKind::Box]);
    assert_eq!(b.adjust("h"), vec![DerefKind::Rc]);
    assert!(b.adjust("t").is_empty());
    assert_eq!(b.t().field.get(&b.expr("b.y")), Some(&FieldIdx::Field(1)));
    assert_eq!(b.t().field.get(&b.expr("t.1")), Some(&FieldIdx::Field(1)));
    assert_eq!(b.ty("b"), "Box<P>");
    b.d0_holds();
}

#[test]
fn calls_record_callee_receiver_and_argument_order() {
    let src = "fn pair(a: i64, b: bool) -> i64 { a }
fn f() {
    let n = pair(b: true, a: 1)
    let v = Vec.new()
    let w: u8 = 7
    v.push(w)
    let g = |x: i64| x * 2
    let m = g(n)
    let o = Some(m)
    print(o, v.len())
}
";
    let a = analyze(src);
    let b = Body::new(src, &a, "f");
    let pair = b.call("pair(b: true, a: 1)");
    assert!(matches!(pair.callee, Callee::Item { ref targs, .. } if targs.is_empty()));
    assert_eq!(pair.args, vec![Some(1), Some(0)]);
    assert!(matches!(b.res("pair"), Res::Fn { .. }));
    let push = b.call("v.push(w)");
    assert_eq!(push.recv.map(|r| r.mode), Some(RecvMode::Borrow));
    let Callee::Item { targs, .. } = &push.callee else {
        panic!("`push` is not an item call");
    };
    assert_eq!(a.thir_tys.show(targs[0]), "u8");
    assert_eq!(b.ty("v"), "Vec<u8>");
    let g = b.call("g(n)");
    let Callee::Value(gb) = g.callee else {
        panic!("`g(n)` is not a call of a value");
    };
    assert_eq!(b.t().bindings[gb.index()].name, "g");
    assert_eq!(b.ty("g"), "fn(i64) -> i64");
    assert!(matches!(b.call("Some(m)").callee, Callee::Variant { .. }));
    assert!(matches!(b.res("Some"), Res::Variant { .. }));
    assert_eq!(
        b.call("print(o, v.len())").callee,
        Callee::Builtin(Builtin::Print)
    );
    let c = b.t().closure.get(&b.expr("|x: i64| x * 2"));
    let c = c.unwrap_or_else(|| panic!("the closure has no record"));
    assert_eq!(c.params.len(), 1);
    assert_eq!(a.thir_tys.show(c.ret), "i64");
    let (binder, name, ty) = b.binding_of("x");
    assert!(matches!(binder, Binder::ClosureParam(..)));
    assert_eq!((name.as_str(), ty.as_str()), ("x", "i64"));
    b.d0_holds();
}

#[test]
fn paths_handles_and_operations() {
    let src = "effect Note { fn note(x: u64) -> u64 }
fn f() -> u64 {
    handle Note { fn note(x) { resume(x + 1) } } in Note.note(1) + note(2)
}
";
    let a = analyze(src);
    let b = Body::new(src, &a, "f");
    let h = b
        .t()
        .handle
        .values()
        .next()
        .unwrap_or_else(|| panic!("no handle record"));
    assert_eq!(h.clauses, vec![Some(0)]);
    assert!(!h.multi);
    assert!(matches!(b.res("Note"), Res::Effect(_)));
    assert!(b.t().effect.contains_key(&b.expr("Note")));
    assert!(matches!(
        b.call("Note.note(1)").callee,
        Callee::Op { op: 0, .. }
    ));
    assert!(matches!(b.res("note"), Res::Op { op: 0, .. }));
    assert!(b.t().effect.contains_key(&b.expr("note")));
    assert!(matches!(b.binding_of("x").0, Binder::ClauseParam(_, 0, 0)));
    assert!(matches!(b.call("resume(x + 1)").callee, Callee::Resume(_)));
    assert!(matches!(b.binding_of("resume").0, Binder::Resume(_, 0)));
    b.d0_holds();
}

#[test]
fn a_match_through_a_reference_binds_by_reference() {
    let src = "struct Q { n: i64 }
fn f(o: &Option<Q>) -> bool {
    match o {
        Some(s) => true,
        None => false,
    }
}
";
    let a = analyze(src);
    let b = Body::new(src, &a, "f");
    assert_eq!(b.adjust("o"), vec![DerefKind::Ref]);
    let s = b.pat("s");
    let id = b.t().binding[&s];
    assert_eq!(a.thir_tys.show(b.t().bindings[id.index()].ty), "&Q");
    assert_eq!(a.thir_tys.show(b.t().pat_ty[&s]), "Q");
    assert_eq!(
        a.thir_tys.show(b.t().pat_ty[&b.pat("Some(s)")]),
        "Option<Q>"
    );
    b.d0_holds();
}

#[test]
fn a_tuple_pattern_through_a_reference_dereferences() {
    let src = "fn f(t: &(i64, i64)) -> i64 {
    let (a, b) = t
    a + b
}
";
    let a = analyze(src);
    let b = Body::new(src, &a, "f");
    let p = b.pat("(a, b)");
    assert_eq!(b.t().pat_adjust.get(&p), Some(&vec![DerefKind::Ref]));
    assert_eq!(b.binding_of("a").2, "&i64");
    assert_eq!(b.adjust("a"), vec![DerefKind::Ref]);
    b.d0_holds();
}

#[test]
fn a_compound_assignment_through_a_reference() {
    let src = "fn inc(c: &u32) / mut(c) { c += 1 }\n";
    let a = analyze(src);
    let b = Body::new(src, &a, "inc");
    assert_eq!(b.adjust("c"), vec![DerefKind::Ref]);
    assert_eq!(b.t().int_ty.get(&b.expr("1")), Some(&weft_ir::IntTy::U32));
    b.d0_holds();
}

#[test]
fn the_passes_of_a_loop_give_one_value() {
    let src = "fn f() -> u64 {
    let s = 0
    let i = 0
    while i < 10 {
        let k = i * 2
        s += k
        i += 1
    }
    for j in 0..3 { s += j }
    s
}
";
    let a = analyze(src);
    let b = Body::new(src, &a, "f");
    assert_eq!(b.ty("k"), "u64");
    assert_eq!(b.binding_of("j").2, "u64");
    b.d0_holds();
}

#[test]
fn a_free_type_variable_is_unit() {
    let src = "fn f() { let v = Vec.new() }\n";
    let a = analyze(src);
    let b = Body::new(src, &a, "f");
    assert_eq!(b.ty("Vec.new()"), "Vec<()>");
    assert!(b.t().free.contains(&b.expr("Vec.new()")));
}

#[test]
fn a_body_with_a_type_error_has_error_tables() {
    let src = "fn f() -> i64 { let x = nothing\n x }\n";
    let a = analyze(src);
    let i = body(&a, "f");
    assert!(a.thir[i].error);
    assert_eq!(d0::d0(&a).checked, a.bodies.len() - 1);
}

/// A program on which D0 holds, for the tests that break its tables.
const GOOD: &str = "struct P { x: i64 }
fn pair(a: i64, b: bool) -> i64 { a }
fn get(p: &P) -> i64 { p.x }
fn f(p: &P) -> i64 {
    let v = Vec.new()
    v.push(p.x)
    let n = v.len()
    get(p) + pair(b: true, a: 1)
}
";

/// The findings of D0 on `GOOD` after `change` on the tables of body `f`.
fn broken(change: &dyn Fn(&mut Tables, &Body<'_>)) -> Vec<Check> {
    let mut a = analyze(GOOD);
    let i = body(&a, "f");
    let b = Body::new(GOOD, &a, "f");
    let mut t = b.t().clone();
    change(&mut t, &b);
    a.thir[i] = t;
    d0::d0(&a).findings.into_iter().map(|f| f.check).collect()
}

#[test]
fn d0_holds_on_the_good_program() {
    assert!(broken(&|_, _| {}).is_empty());
}

#[test]
fn d0_finds_a_missing_type() {
    let c = broken(&|t, b| {
        t.expr_ty.remove(&b.expr("v.len()"));
    });
    assert_eq!(c, vec![Check::Type]);
}

#[test]
fn d0_finds_a_missing_meaning() {
    let c = broken(&|t, b| {
        t.res.remove(&b.expr("get"));
    });
    assert_eq!(c, vec![Check::Res]);
}

#[test]
fn d0_finds_a_missing_call_and_a_wrong_argument_order() {
    let c = broken(&|t, b| {
        t.call.remove(&b.expr("get(p)"));
    });
    assert_eq!(c, vec![Check::Call]);
    let c = broken(&|t, b| {
        if let Some(c) = t.call.get_mut(&b.expr("v.push(p.x)")) {
            c.args = vec![None];
        }
        let _ = b;
    });
    // `push` has no named argument: the facts have no order for it.
    assert!(c.is_empty());
    let src_named = "fn pair(a: i64, b: bool) -> i64 { a }
fn f() -> i64 {
    let g = pair
    g(b: true, a: 1)
}
";
    let mut a = analyze(src_named);
    let i = body(&a, "f");
    let b = Body::new(src_named, &a, "f");
    let mut t = b.t().clone();
    if let Some(c) = t.call.get_mut(&b.expr("g(b: true, a: 1)")) {
        c.args.reverse();
    }
    a.thir[i] = t;
    let checks: Vec<Check> = d0::d0(&a).findings.into_iter().map(|f| f.check).collect();
    assert_eq!(checks, vec![Check::Call]);
}

#[test]
fn d0_finds_a_wrong_integer_type() {
    let c = broken(&|t, b| {
        t.int_ty
            .insert(b.expr("get(p) + pair(b: true, a: 1)"), weft_ir::IntTy::U8);
    });
    assert_eq!(c, vec![Check::IntTy, Check::IntTy]);
}

#[test]
fn d0_finds_a_missing_or_a_wrong_dereference() {
    let c = broken(&|t, b| {
        t.adjust.remove(&b.expr("p"));
    });
    assert_eq!(c, vec![Check::Adjust]);
    let c = broken(&|t, b| {
        t.adjust
            .insert(b.expr("p"), vec![DerefKind::Ref, DerefKind::Ref]);
    });
    assert_eq!(c, vec![Check::Adjust]);
    let c = broken(&|t, b| {
        t.field.insert(b.expr("p.x"), FieldIdx::Variant(0));
    });
    assert_eq!(c, vec![Check::Adjust]);
}

#[test]
fn d0_finds_a_conflict() {
    let c = broken(&|t, _| {
        t.conflicts.push(weft_sema::thir::Conflict {
            table: "expr_ty",
            key: weft_sema::thir::Key::Expr(ExprId(0)),
            values: vec!["i64".into(), "u8".into()],
        });
    });
    assert_eq!(c, vec![Check::Conflict]);
}
