//! The builder of the IR (plan stage B3, `weft_sema::irbuild`).
//!
//! Each program in `tests/ir_golden/` has the text of its IR in a `.ir` file
//! next to it. The test builds the IR, runs the verifier on it, and compares
//! the text. Set `WEFT_BLESS=1` to write the `.ir` files again; then read each
//! changed file against `docs/ir.md` section 5 before you commit it.
//!
//! The other tests check the rules of `docs/ir.md` that the golden files show,
//! and that the builder is total on the corpus: each body builds or is
//! `Unsupported`, and no body panics.

use std::path::{Path, PathBuf};

use weft_ir::{
    Body, DerefKind, LocalId, LocalKind, Operand, Place, Proj, Rvalue, StmtKind, TempKind, TermKind,
};
use weft_sema::irbuild::{self, Built, Outcome};
use weft_sema::{analyze_source, Analysis, Options};
use weft_syntax::ast::StmtKind as AstStmt;

/// The directory of the golden programs.
fn golden_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/ir_golden")
}

/// Analyzes `src` and builds its IR.
fn build(src: &str) -> (Analysis, Built) {
    let a = analyze_source(src, Options::from_markers(src))
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let b = irbuild::build(&a);
    (a, b)
}

/// Returns the broken rules of `b`, one on each line.
fn rules(b: &Built) -> String {
    b.broken
        .iter()
        .map(|x| format!("  {x}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Returns the line and the column of byte `at` of `src`.
fn line_col(src: &str, at: u32) -> String {
    let at = usize::try_from(at).unwrap_or(usize::MAX).min(src.len());
    let before = &src[..at];
    let line = before.matches('\n').count() + 1;
    let col = at - before.rfind('\n').map_or(0, |i| i + 1) + 1;
    format!("{line}:{col}")
}

/// Builds the golden program `name`, checks that each body verifies, and
/// compares the text with `name.ir`.
fn golden(name: &str) {
    let dir = golden_dir();
    let wf = dir.join(format!("{name}.wf"));
    let src = std::fs::read_to_string(&wf).unwrap_or_else(|e| panic!("read {}: {e}", wf.display()));
    let (_, b) = build(&src);
    assert!(
        b.broken.is_empty(),
        "{name}: the IR breaks rules:\n{}",
        rules(&b)
    );
    let text = irbuild::text(&b, &|_, s| line_col(&src, s.lo));
    let ir = dir.join(format!("{name}.ir"));
    if std::env::var_os("WEFT_BLESS").is_some_and(|v| v == "1") {
        std::fs::write(&ir, &text).unwrap_or_else(|e| panic!("write {}: {e}", ir.display()));
        return;
    }
    let want = std::fs::read_to_string(&ir).unwrap_or_else(|e| {
        panic!(
            "read {}: {e}\nset WEFT_BLESS=1 to write it; the IR is:\n{text}",
            ir.display()
        )
    });
    assert!(
        want == text,
        "{name}: the IR differs from {}; set WEFT_BLESS=1 to write it.\n--- want\n{want}\n--- got\n{text}",
        ir.display()
    );
}

#[test]
fn golden_let_tail() {
    golden("let_tail");
}

#[test]
fn golden_ops() {
    golden("ops");
}

#[test]
fn golden_ret_ref() {
    golden("ret_ref");
}

#[test]
fn golden_block_tail() {
    golden("block_tail");
}

#[test]
fn golden_places() {
    golden("places");
}

#[test]
fn golden_deref_rc_box() {
    golden("deref_rc_box");
}

#[test]
fn golden_index_bounds() {
    golden("index_bounds");
}

#[test]
fn golden_compound() {
    golden("compound");
}

#[test]
fn golden_borrow_value() {
    golden("borrow_value");
}

#[test]
fn golden_assign_through() {
    golden("assign_through");
}

/// Returns the built body of the function or test `name`.
fn body<'b>(b: &'b Built, name: &str) -> &'b Body {
    let e = b
        .entries
        .iter()
        .find(|e| e.name == name)
        .unwrap_or_else(|| panic!("no body `{name}`"));
    match &e.outcome {
        Outcome::Built(id) => b
            .program
            .body(*id)
            .unwrap_or_else(|| panic!("no body {id:?}")),
        other => panic!("`{name}` has no IR: {other:?}"),
    }
}

/// Returns the local of `body` with the source name `name`.
fn named(body: &Body, name: &str) -> LocalId {
    let i = body
        .locals
        .iter()
        .position(|d| d.name.as_deref() == Some(name))
        .unwrap_or_else(|| panic!("no local `{name}`"));
    LocalId(u32::try_from(i).unwrap_or(u32::MAX))
}

/// Returns the statements of `body` in block order.
fn stmts(body: &Body) -> Vec<&StmtKind> {
    body.blocks
        .iter()
        .flat_map(|b| b.stmts.iter().map(|s| &s.kind))
        .collect()
}

#[test]
fn choice_a_reads_the_operand_before_the_block() {
    let (_, b) = build("fn f() -> u64 {\n    let x = 1\n    x + { x = 5; 1 }\n}\n");
    assert!(b.broken.is_empty(), "{:?}", b.broken);
    let f = body(&b, "f");
    let x = named(f, "x");
    let ss = stmts(f);
    let read = ss
        .iter()
        .position(|s| {
            matches!(s, StmtKind::Assign(t, Rvalue::Use(Operand::Copy(p)))
                if *p == Place::local(x)
                    && matches!(f.locals[t.local.index()].kind, LocalKind::Temp(TempKind::Operand)))
        })
        .unwrap_or_else(|| panic!("no read of `x` into a temporary: {ss:?}"));
    let write = ss
        .iter()
        .position(|s| matches!(s, StmtKind::Assign(p, Rvalue::Use(Operand::Move(_))) if *p == Place::local(x)))
        .unwrap_or_else(|| panic!("no write of `x`: {ss:?}"));
    assert!(
        read < write,
        "the read of `x` must come before `x = 5`: {ss:?}"
    );
    // The sum reads the temporary, not `x`.
    let sum = ss.iter().find_map(|s| match s {
        StmtKind::Assign(p, Rvalue::Binary(_, _, a, _)) if p.local == f.ret => Some(a),
        _ => None,
    });
    assert!(
        matches!(sum, Some(Operand::Move(p)) if p.local != x),
        "the sum must read the temporary: {sum:?}"
    );
}

#[test]
fn a_block_tail_moves_before_the_block_locals_end() {
    let (_, b) = build("fn f(a: Vec<u64>) -> Vec<u64> {\n    let s = {\n        let t = a\n        t\n    }\n    s\n}\n");
    assert!(b.broken.is_empty(), "{:?}", b.broken);
    let f = body(&b, "f");
    let (s, t) = (named(f, "s"), named(f, "t"));
    let ss = stmts(f);
    let moved = ss
        .iter()
        .position(|k| {
            matches!(k, StmtKind::Assign(p, Rvalue::Use(Operand::Move(q)))
                if *p == Place::local(s) && *q == Place::local(t))
        })
        .unwrap_or_else(|| panic!("no `s = move t`: {ss:?}"));
    let dead = ss
        .iter()
        .position(|k| **k == StmtKind::Dead(t))
        .unwrap_or_else(|| panic!("no `Dead(t)`: {ss:?}"));
    assert!(moved < dead, "the tail must move before `Dead(t)`: {ss:?}");
}

#[test]
fn a_returned_reference_to_a_local_ends_the_local_first() {
    let src = "fn f() -> &u64 {\n    let x = 1\n    &x\n}\n";
    let (a, b) = build(src);
    assert!(b.broken.is_empty(), "{:?}", b.broken);
    let f = body(&b, "f");
    let x = named(f, "x");
    let ret = f
        .blocks
        .iter()
        .find(|blk| blk.term.kind == TermKind::Return)
        .unwrap_or_else(|| panic!("no `Return`"));
    let kinds: Vec<&StmtKind> = ret.stmts.iter().map(|s| &s.kind).collect();
    let dead = kinds.iter().position(|k| **k == StmtKind::Dead(x));
    let borrow = kinds
        .iter()
        .position(|k| matches!(k, StmtKind::Assign(p, Rvalue::Ref(q)) if p.local == f.ret && *q == Place::local(x)));
    assert!(
        matches!((borrow, dead), (Some(r), Some(d)) if r < d),
        "`_0 = &x` must come before `Dead(x)`: {kinds:?}"
    );
    // The origin of `Return` is the tail `&x`.
    let def = a
        .program
        .fns
        .iter()
        .find(|d| d.name == "f")
        .unwrap_or_else(|| panic!("no `f`"));
    let tail = match def
        .decl
        .body
        .as_ref()
        .and_then(|b| b.stmts.last())
        .map(|s| &s.kind)
    {
        Some(AstStmt::Expr(e)) => e,
        other => panic!("no tail: {other:?}"),
    };
    assert_eq!(ret.term.origin.span.lo, tail.span.lo);
    assert_eq!(ret.term.origin.span.hi, tail.span.hi);
    assert_eq!(ret.term.origin.expr, Some(tail.id));
}

#[test]
fn a_construct_of_a_later_stage_is_unsupported() {
    let (_, b) = build("fn f(c: bool) -> u64 {\n    if c { 1 } else { 2 }\n}\n");
    let e = b
        .entries
        .iter()
        .find(|e| e.name == "f")
        .unwrap_or_else(|| panic!("no `f`"));
    match &e.outcome {
        Outcome::Unsupported(u) => assert_eq!(u.construct.name(), "if"),
        other => panic!("`if` is for stage B5: {other:?}"),
    }
}

/// The programs of the corpus.
fn corpus() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut v: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    v.sort();
    v
}

#[test]
fn the_builder_is_total_on_the_corpus() {
    let mut built = 0;
    let mut unsupported = std::collections::BTreeMap::<&str, usize>::new();
    let mut no_ir = 0;
    let programs = corpus();
    assert!(
        programs.len() > 100,
        "the corpus has {} programs",
        programs.len()
    );
    for p in &programs {
        let src =
            std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        let Ok(a) = analyze_source(&src, Options::from_markers(&src)) else {
            continue;
        };
        let b = std::panic::catch_unwind(|| irbuild::build(&a))
            .unwrap_or_else(|_| panic!("the builder panics on {}", p.display()));
        assert!(
            b.broken.is_empty(),
            "{}: the IR breaks rules:\n{}",
            p.display(),
            rules(&b)
        );
        assert_eq!(b.entries.len(), a.bodies.len(), "{}", p.display());
        for e in &b.entries {
            match &e.outcome {
                Outcome::Built(_) => built += 1,
                Outcome::Unsupported(u) => *unsupported.entry(u.construct.name()).or_default() += 1,
                Outcome::NoIr(_) => no_ir += 1,
            }
        }
    }
    eprintln!("corpus: {built} bodies built, {no_ir} with no IR, unsupported: {unsupported:?}");
    assert!(built > 0);
}

/// Returns the golden program `name` and its IR.
fn golden_built(name: &str) -> Built {
    let wf = golden_dir().join(format!("{name}.wf"));
    let src = std::fs::read_to_string(&wf).unwrap_or_else(|e| panic!("read {}: {e}", wf.display()));
    let (_, b) = build(&src);
    assert!(b.broken.is_empty(), "{name}: {}", rules(&b));
    b
}

/// Returns the first `Deref` kind of each place of the statements of `body`.
fn derefs(body: &Body) -> Vec<DerefKind> {
    let mut v = Vec::new();
    for s in stmts(body) {
        let mut add = |p: &Place| {
            v.extend(p.proj.iter().filter_map(|x| match x {
                Proj::Deref(k) => Some(*k),
                _ => None,
            }));
        };
        match s {
            StmtKind::Assign(p, rv) => {
                add(p);
                match rv {
                    Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) | Rvalue::Ref(q) => add(q),
                    Rvalue::Binary(_, _, a, b) => {
                        for o in [a, b] {
                            if let Some(q) = o.place() {
                                add(q);
                            }
                        }
                    }
                    _ => {}
                }
            }
            StmtKind::Drop(p) | StmtKind::Mention(p) | StmtKind::Bounds(p, _) => add(p),
            _ => {}
        }
    }
    v
}

#[test]
fn a_field_through_a_pointer_is_a_deref_projection() {
    let b = golden_built("deref_rc_box");
    assert_eq!(derefs(body(&b, "by_ref")), vec![DerefKind::Ref]);
    assert_eq!(derefs(body(&b, "by_box")), vec![DerefKind::Box]);
    assert_eq!(derefs(body(&b, "by_rc")), vec![DerefKind::Rc]);
    assert_eq!(
        derefs(body(&b, "ref_ref")),
        vec![DerefKind::Ref, DerefKind::Ref]
    );
    assert_eq!(
        derefs(body(&b, "ref_box")),
        vec![DerefKind::Ref, DerefKind::Box]
    );
}

#[test]
fn a_store_behind_a_pointer_drops_only_a_maybe_linear_old_value() {
    let b = golden_built("assign_through");
    for (name, drop) in [
        ("set_field", false),
        ("set_through", false),
        ("set_linear", true),
        ("set_generic", true),
        ("set_box", false),
        ("set_elem_ref", false),
    ] {
        let f = body(&b, name);
        let ss = stmts(f);
        let at = ss.iter().position(|s| matches!(s, StmtKind::Drop(_)));
        assert_eq!(at.is_some(), drop, "{name}: {ss:?}");
        if let Some(i) = at {
            // V17: the next statement stores into the same place.
            match (ss[i], ss.get(i + 1)) {
                (StmtKind::Drop(p), Some(StmtKind::Assign(q, _))) => assert_eq!(p, q, "{name}"),
                other => panic!("{name}: no store after the drop: {other:?}"),
            }
        }
    }
}

#[test]
fn a_place_store_runs_the_value_before_the_target() {
    let b = golden_built("assign_through");
    let f = body(&b, "set_elem");
    let (i, j) = (named(f, "i"), named(f, "j"));
    let ss = stmts(f);
    // The index temporary of `v[j]` gets `copy j` before the one of `v[i]`
    // gets `copy i`.
    let read = |x: LocalId| {
        ss.iter()
            .position(|s| matches!(s, StmtKind::Assign(_, Rvalue::Use(Operand::Copy(p))) if *p == Place::local(x)))
            .unwrap_or_else(|| panic!("no read of _{}: {ss:?}", x.0))
    };
    assert!(read(j) < read(i), "the value must run first: {ss:?}");
    let bounds = ss
        .iter()
        .filter(|s| matches!(s, StmtKind::Bounds(..)))
        .count();
    assert_eq!(bounds, 2, "{ss:?}");
}

#[test]
fn a_compound_store_on_a_reference_local_writes_through_it() {
    let b = golden_built("compound");
    let f = body(&b, "through_ref");
    let r = named(f, "r");
    let through = Place {
        local: r,
        proj: vec![Proj::Deref(DerefKind::Ref)],
    };
    let ss = stmts(f);
    assert!(
        ss.iter().any(
            |s| matches!(s, StmtKind::Assign(p, Rvalue::Use(Operand::Move(_))) if *p == through)
        ),
        "no store into (*r): {ss:?}"
    );
    assert!(
        !ss.iter()
            .any(|s| matches!(s, StmtKind::Assign(p, _) if *p == Place::local(r))),
        "the store must not give `r` a new value: {ss:?}"
    );
}

#[test]
fn a_borrow_of_a_value_borrows_a_temporary_of_the_statement() {
    let b = golden_built("borrow_value");
    let f = body(&b, "value");
    let tv = f
        .locals
        .iter()
        .position(|d| d.kind == LocalKind::Temp(TempKind::Borrowed))
        .map_or_else(
            || panic!("no `Borrowed` temporary"),
            |i| LocalId(u32::try_from(i).unwrap_or(u32::MAX)),
        );
    let ss = stmts(f);
    let r = named(f, "r");
    let borrow = ss
        .iter()
        .position(|s| matches!(s, StmtKind::Assign(p, Rvalue::Ref(q)) if *p == Place::local(r) && *q == Place::local(tv)))
        .unwrap_or_else(|| panic!("no `r = &tv`: {ss:?}"));
    let dead = ss
        .iter()
        .position(|s| **s == StmtKind::Dead(tv))
        .unwrap_or_else(|| panic!("no `Dead(tv)`: {ss:?}"));
    let dead_r = ss
        .iter()
        .position(|s| **s == StmtKind::Dead(r))
        .unwrap_or_else(|| panic!("no `Dead(r)`: {ss:?}"));
    assert!(borrow < dead && dead < dead_r, "{ss:?}");
}

#[test]
fn a_place_in_statement_position_is_a_mention() {
    let b = golden_built("places");
    let f = body(&b, "mention");
    let ss = stmts(f);
    let mentions = ss
        .iter()
        .filter(|s| matches!(s, StmtKind::Mention(_)))
        .count();
    assert_eq!(mentions, 2, "{ss:?}");
    assert!(
        !ss.iter()
            .any(|s| matches!(s, StmtKind::Assign(_, Rvalue::Use(Operand::Move(_))))),
        "a mention moves nothing: {ss:?}"
    );
}
