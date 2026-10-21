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
    AggKind, Body, BodyId, Callee, CapArgs, CapOperand, CaptureMode, ClosureDecl, Const, DerefKind,
    LocalId, LocalKind, Operand, Place, Proj, Rvalue, StmtKind, TempKind, TermKind,
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

#[test]
fn golden_if_tail() {
    golden("if_tail");
}

#[test]
fn golden_and_or() {
    golden("and_or");
}

#[test]
fn golden_match_bind() {
    golden("match_bind");
}

#[test]
fn golden_match_ref() {
    golden("match_ref");
}

#[test]
fn golden_let_tuple() {
    golden("let_tuple");
}

#[test]
fn golden_linear_destructure() {
    golden("linear_destructure");
}

#[test]
fn golden_wild_part() {
    golden("wild_part");
}

#[test]
fn golden_place_fields() {
    golden("place_fields");
}

#[test]
fn golden_match_literals() {
    golden("match_literals");
}

#[test]
fn golden_match_nested() {
    golden("match_nested");
}

#[test]
fn golden_match_string() {
    golden("match_string");
}

#[test]
fn golden_while_cond() {
    golden("while_cond");
}

#[test]
fn golden_for_elems() {
    golden("for_elems");
}

#[test]
fn golden_for_range() {
    golden("for_range");
}

#[test]
fn golden_break_nested_block() {
    golden("break_nested_block");
}

#[test]
fn golden_continue_temps() {
    golden("continue_temps");
}

#[test]
fn golden_return_in_arg() {
    golden("return_in_arg");
}

#[test]
fn golden_loop_tail_temp() {
    golden("loop_tail_temp");
}

#[test]
fn golden_break_in_closure() {
    golden("break_in_closure");
}

#[test]
fn golden_call_args() {
    golden("call_args");
}

#[test]
fn golden_named_args() {
    golden("named_args");
}

#[test]
fn golden_method_ref() {
    golden("method_ref");
}

#[test]
fn golden_method_value() {
    golden("method_value");
}

#[test]
fn golden_struct_lit() {
    golden("struct_lit");
}

#[test]
fn golden_positional() {
    golden("positional");
}

#[test]
fn golden_vec_lit() {
    golden("vec_lit");
}

#[test]
fn golden_array_lit() {
    golden("array_lit");
}

#[test]
fn golden_print_borrow() {
    golden("print_borrow");
}

#[test]
fn golden_interp_borrow() {
    golden("interp_borrow");
}

#[test]
fn golden_duration_lit() {
    golden("duration_lit");
}

#[test]
fn golden_trailing_block() {
    golden("trailing_block");
}

#[test]
fn golden_perform_path() {
    golden("perform_path");
}

#[test]
fn golden_assert() {
    golden("assert");
}

#[test]
fn golden_perform_row() {
    golden("perform_row");
}

#[test]
fn golden_generic_extern() {
    golden("generic_extern");
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
    let (_, b) = build("struct S { v: Vec<u64> }\nfn f(r: &S) -> Vec<u64> {\n    r.v\n}\n");
    let e = b
        .entries
        .iter()
        .find(|e| e.name == "f")
        .unwrap_or_else(|| panic!("no `f`"));
    match &e.outcome {
        Outcome::Unsupported(u) => {
            assert_eq!(u.construct.name(), "move through a reference");
            assert_eq!(u.construct.stage(), "B12");
        }
        other => panic!("a move through a reference is for stage B12: {other:?}"),
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

/// Returns the statements of `body` that give a local of kind `User` a value
/// from a place of the parameter `param`, with their blocks.
fn bindings_from(body: &Body, param: LocalId) -> Vec<(usize, LocalId, Rvalue)> {
    let mut v = Vec::new();
    for (i, blk) in body.blocks.iter().enumerate() {
        for s in &blk.stmts {
            if let StmtKind::Assign(p, rv) = &s.kind {
                let from = match rv {
                    Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) | Rvalue::Ref(q) => {
                        q.local == param
                    }
                    _ => false,
                };
                if from && p.is_local() && body.locals[p.local.index()].kind == LocalKind::User {
                    v.push((i, p.local, rv.clone()));
                }
            }
        }
    }
    v
}

/// Returns the blocks that block `from` reaches by normal edges, `from` too.
fn reached(body: &Body, from: usize) -> Vec<usize> {
    let mut seen = vec![false; body.blocks.len()];
    let mut work = vec![from];
    while let Some(b) = work.pop() {
        if std::mem::replace(&mut seen[b], true) {
            continue;
        }
        for s in body.blocks[b].term.kind.normal_successors() {
            work.push(s.index());
        }
    }
    (0..seen.len()).filter(|&i| seen[i]).collect()
}

#[test]
fn a_match_on_a_reference_binds_by_reference() {
    let b = golden_built("match_ref");
    let f = body(&b, "pick");
    let r = named(f, "r");
    let binds = bindings_from(f, r);
    assert_eq!(binds.len(), 2, "{binds:?}");
    for (_, _, rv) in &binds {
        match rv {
            Rvalue::Ref(q) => {
                assert_eq!(q.proj.first(), Some(&Proj::Deref(DerefKind::Ref)), "{q:?}");
                assert!(
                    q.proj.iter().any(|p| matches!(p, Proj::Variant(_))),
                    "{q:?}"
                );
            }
            other => panic!("a binding through a reference must borrow: {other:?}"),
        }
    }
    // A scalar part through a reference is a copy.
    let f = body(&b, "count");
    let r = named(f, "r");
    let binds = bindings_from(f, r);
    assert!(
        matches!(binds.as_slice(), [(_, _, Rvalue::Use(Operand::Copy(_)))]),
        "{binds:?}"
    );
}

#[test]
fn a_wild_linear_part_moves_into_a_temporary_and_ends() {
    let b = golden_built("wild_part");
    for (name, wild) in [
        ("let_wild", true),
        ("arm_wild", true),
        ("arm_keeps", false),
        ("plain_wild", false),
    ] {
        let f = body(&b, name);
        let ss = stmts(f);
        // A discarded temporary that gets a part of a value by a move.
        let moved: Vec<LocalId> = ss
            .iter()
            .filter_map(|s| match s {
                StmtKind::Assign(p, Rvalue::Use(Operand::Move(q)))
                    if p.is_local()
                        && !q.is_local()
                        && f.locals[p.local.index()].kind
                            == LocalKind::Temp(TempKind::Discarded) =>
                {
                    Some(p.local)
                }
                _ => None,
            })
            .collect();
        assert_eq!(!moved.is_empty(), wild, "{name}: {ss:?}");
        for t in moved {
            let at = ss
                .iter()
                .position(|s| matches!(s, StmtKind::Assign(p, _) if p.local == t))
                .unwrap_or(0);
            assert!(
                ss[at..].iter().any(|s| **s == StmtKind::Dead(t)),
                "{name}: no `Dead` of the part: {ss:?}"
            );
        }
    }
}

#[test]
fn a_variant_with_no_payload_of_a_linear_scrutinee_is_a_consume() {
    let b = golden_built("linear_destructure");
    let f = body(&b, "none_or");
    let o = named(f, "o");
    let ss = stmts(f);
    assert!(
        ss.iter().any(|s| **s == StmtKind::Consume(Place::local(o))),
        "no `Consume(o)`: {ss:?}"
    );
    // A `let` with a struct pattern of a linear struct consumes it.
    let f = body(&b, "open");
    let l = named(f, "l");
    let ss = stmts(f);
    assert!(
        ss.iter().any(|s| **s == StmtKind::Consume(Place::local(l))),
        "no `Consume(l)`: {ss:?}"
    );
    // `Option<u64>` is not linear: no `Consume`.
    let b = golden_built("match_bind");
    let ss = stmts(body(&b, "of_block"));
    assert!(
        !ss.iter().any(|s| matches!(s, StmtKind::Consume(_))),
        "{ss:?}"
    );
}

#[test]
fn patterns_test_in_pre_order_and_bind_after_the_last_test() {
    for (file, name) in [
        ("match_literals", "int"),
        ("match_literals", "boolean"),
        ("match_literals", "unit"),
        ("match_literals", "int_ref"),
        ("match_string", "word"),
        ("match_string", "in_option"),
        ("match_nested", "nested"),
        ("match_nested", "deep"),
        ("match_nested", "bind_then_test"),
        ("match_bind", "area"),
    ] {
        let b = golden_built(file);
        let f = body(&b, name);
        let param = f.params[0];
        // No test (a switch) comes after a binding: each match here is the
        // tail, and its arms have no branch.
        for (blk, l, _) in bindings_from(f, param) {
            for r in reached(f, blk) {
                assert!(
                    !matches!(f.blocks[r].term.kind, TermKind::Switch { .. }),
                    "{file}/{name}: a test after the binding _{} in bb{blk}",
                    l.0
                );
            }
        }
    }
    // Pre-order: in the first arm `(Some(1), true)`, the discriminant of
    // `p.0`, then the payload, then `p.1`.
    let b = golden_built("match_nested");
    let f = body(&b, "nested");
    let p = f.params[0];
    let mut tested = Vec::new();
    let mut at = f.entry.index();
    for _ in 0..3 {
        let blk = &f.blocks[at];
        let TermKind::Switch { on, arms, .. } = &blk.term.kind else {
            panic!("no switch in bb{at}: {:?}", blk.term.kind);
        };
        let place = match on {
            Operand::Copy(q) if q.local == p => q.clone(),
            Operand::Move(t) => blk
                .stmts
                .iter()
                .find_map(|s| match &s.kind {
                    StmtKind::Assign(d, Rvalue::Discriminant(q)) if d == t => Some(q.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("no discriminant for {t:?}")),
            other => panic!("a test of {other:?}"),
        };
        tested.push(place.proj.len());
        at = arms[0].1.index();
    }
    // `p.0` (one step), `(p.0 as Some).0` (three steps), `p.1` (one step).
    assert_eq!(tested, vec![1, 3, 1]);
}

#[test]
fn place_fields_of_recursive_and_polymorphic_types_end() {
    // A recursive type, two types in one cycle, and types that grow at each
    // depth. The build ends, and each place field gets an `Uninit`.
    let src = "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }
struct Node: !Move { fr: Frame, next: Option<Box<Node>> }
struct A { fr: Frame, b: Option<Box<B>> }
struct B { a: A, fr: Frame }
struct Nest<T> { x: T, next: Option<Box<Nest<Box<T>>>> }
struct Grow<T> { x: T, next: Option<Box<Grow<(T, T)>>> }
struct List<T> { x: T, next: Option<Box<List<T>>> }
fn node(n: Node) {}
fn a(x: A) {}
fn nest(n: Nest<Frame>) {}
fn grow(g: Grow<Frame>) {}
fn list(l: List<List<Frame>>) {}
fn plain(l: List<u64>, g: Grow<u64>) {}
";
    let (_, b) = build(src);
    assert!(b.broken.is_empty(), "{}", rules(&b));
    for (name, at_least) in [
        ("node", 2),
        ("a", 2),
        ("nest", 2),
        ("grow", 2),
        ("list", 2),
        ("plain", 0),
    ] {
        let f = body(&b, name);
        let n = stmts(f)
            .iter()
            .filter(|s| matches!(s, StmtKind::Uninit(_)))
            .count();
        assert!(
            n >= at_least && (at_least > 0 || n == 0),
            "{name}: {n} `Uninit` statements"
        );
    }
}

#[test]
fn a_variant_field_place_tests_the_variant_first() {
    let (_, b) = build("fn f(o: Option<u64>) -> Option<u64> {\n    o.Some = 5\n    o\n}\n");
    assert!(b.broken.is_empty(), "{}", rules(&b));
    let f = body(&b, "f");
    let o = named(f, "o");
    let store = f
        .blocks
        .iter()
        .position(|blk| {
            blk.stmts.iter().any(|s| {
                matches!(&s.kind, StmtKind::Assign(p, _)
                    if p.local == o && matches!(p.proj.first(), Some(Proj::Variant(_))))
            })
        })
        .unwrap_or_else(|| panic!("no store into `(o as Some).0`: {:?}", stmts(f)));
    // The block of the store is the arm of a switch on the discriminant.
    let from = f
        .blocks
        .iter()
        .filter(|blk| {
            blk.term
                .kind
                .normal_successors()
                .iter()
                .any(|s| s.index() == store)
        })
        .count();
    assert_eq!(from, 1);
    assert!(
        stmts(f).iter().any(
            |s| matches!(s, StmtKind::Assign(_, Rvalue::Discriminant(q)) if *q == Place::local(o))
        ),
        "no test of `o`"
    );
}

/// Returns the locals of `body` of kind `kind`.
fn temps_of(body: &Body, kind: TempKind) -> Vec<LocalId> {
    (0..body.locals.len())
        .filter(|&i| body.locals[i].kind == LocalKind::Temp(kind))
        .map(|i| LocalId(u32::try_from(i).unwrap_or(u32::MAX)))
        .collect()
}

/// Returns the index of the block of `body` with statement `s`.
fn block_with(body: &Body, s: &StmtKind) -> Option<usize> {
    body.blocks
        .iter()
        .position(|b| b.stmts.iter().any(|x| x.kind == *s))
}

#[test]
fn a_return_in_a_later_operand_ends_the_earlier_operand_temporaries() {
    // OL-3c with an operator: `{ v } == { if c { return false }; w }`. The
    // left operand is a borrowed temporary of the `Vec`; the `return` path
    // ends it (its `Dead` drops the value) before `Return`.
    let b = golden_built("return_in_arg");
    let f = body(&b, "cmp");
    let borrowed = temps_of(f, TempKind::Borrowed);
    assert!(!borrowed.is_empty(), "no borrowed temporary");
    let early: Vec<&weft_ir::Block> = f
        .blocks
        .iter()
        .filter(|blk| {
            blk.term.kind == TermKind::Return
                && blk.stmts.iter().any(|s| {
                    matches!(&s.kind, StmtKind::Assign(p, Rvalue::Use(Operand::Const(weft_ir::Const::Bool(false))))
                        if *p == Place::local(LocalId(0)))
                })
        })
        .collect();
    assert_eq!(early.len(), 1, "one `return false` path");
    let ends: Vec<&StmtKind> = early[0].stmts.iter().map(|s| &s.kind).collect();
    for t in &borrowed {
        assert!(
            ends.contains(&&StmtKind::Dead(*t)),
            "the `return` path does not end {t:?}: {ends:?}"
        );
    }
    // From inside a `for`: `s + i * { if i > 5 { return s }; 1 }`. Each
    // operand temporary, the element and the iterator end on the `return`
    // path.
    let f = body(&b, "in_loop");
    let s_local = named(f, "s");
    let early: Vec<&weft_ir::Block> = f
        .blocks
        .iter()
        .filter(|blk| {
            blk.term.kind == TermKind::Return
                && blk.stmts.iter().any(|s| {
                    matches!(&s.kind, StmtKind::Assign(p, Rvalue::Use(Operand::Copy(q)))
                        if *p == Place::local(LocalId(0)) && *q == Place::local(s_local))
                })
                && blk
                    .stmts
                    .iter()
                    .any(|s| matches!(s.kind, StmtKind::Dead(l) if f.locals[l.index()].kind == LocalKind::Temp(TempKind::Scrutinee)))
        })
        .collect();
    assert_eq!(early.len(), 1, "one `return s` path in the loop");
    let ends: Vec<&StmtKind> = early[0].stmts.iter().map(|s| &s.kind).collect();
    let operands = temps_of(f, TempKind::Operand);
    assert!(operands.len() >= 3, "operand temporaries: {operands:?}");
    let iterators = (0..f.locals.len())
        .filter(|&i| f.locals[i].kind == LocalKind::Iterator)
        .map(|i| LocalId(u32::try_from(i).unwrap_or(u32::MAX)));
    for t in operands
        .iter()
        .copied()
        .chain(temps_of(f, TempKind::Scrutinee))
        .chain(iterators)
    {
        assert!(
            ends.contains(&&StmtKind::Dead(t)),
            "the `return` path does not end {t:?}: {ends:?}"
        );
    }
}

#[test]
fn the_tail_temporaries_of_a_loop_body_end_at_each_iteration() {
    // `while i < n { i += 1; i * 2 }`: the tail temporary gets its `Dead` in
    // the block that takes the back edge to the head, before the next `Live`.
    let b = golden_built("loop_tail_temp");
    let f = body(&b, "tail_value");
    let tails = temps_of(f, TempKind::Discarded);
    assert_eq!(tails.len(), 1, "one tail temporary: {tails:?}");
    let t = tails[0];
    let live = block_with(f, &StmtKind::Live(t)).unwrap_or_else(|| panic!("no Live"));
    let dead = block_with(f, &StmtKind::Dead(t)).unwrap_or_else(|| panic!("no Dead"));
    let blk = &f.blocks[dead];
    let pos = |k: &StmtKind| blk.stmts.iter().position(|s| s.kind == *k);
    // The `Dead` comes after the `Live` in the same iteration, and the block
    // goes back to a block at or before the block of the `Live`.
    match blk.term.kind {
        TermKind::Goto(h) => assert!(
            h.index() <= live,
            "the tail temporary ends in bb{dead}, which does not go back to the head"
        ),
        ref k => panic!("the block of the Dead ends with {k:?}, not a back edge"),
    }
    if dead == live {
        assert!(pos(&StmtKind::Live(t)) < pos(&StmtKind::Dead(t)));
    }
}

/// Returns the terminators of `body` in block order.
fn terms(body: &Body) -> Vec<&TermKind> {
    body.blocks.iter().map(|b| &b.term.kind).collect()
}

/// Returns the name of the function of each call of `body`, in block order.
fn callees(b: &Built, body: &Body) -> Vec<String> {
    terms(body)
        .into_iter()
        .filter_map(|k| match k {
            TermKind::Call {
                callee: Callee::Fn(f, _),
                ..
            } => Some(b.program.fns[f.index()].name.clone()),
            _ => None,
        })
        .collect()
}

/// Returns the arguments and the destination of the call of function
/// `name` in `body`.
fn call_of<'a>(b: &Built, body: &'a Body, name: &str) -> (&'a [Operand], &'a Place) {
    terms(body)
        .into_iter()
        .find_map(|k| match k {
            TermKind::Call {
                callee: Callee::Fn(f, _),
                args,
                dest,
                ..
            } if b.program.fns[f.index()].name == name => Some((args.as_slice(), dest)),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no call of `{name}`"))
}

/// Returns the index of the block whose terminator is the call of `name`.
fn call_block(b: &Built, body: &Body, name: &str) -> usize {
    terms(body)
        .into_iter()
        .position(|k| matches!(k, TermKind::Call { callee: Callee::Fn(f, _), .. } if b.program.fns[f.index()].name == name))
        .unwrap_or_else(|| panic!("no call of `{name}`"))
}

/// Returns the right side that `body` assigns to the whole local `l`.
fn assigned(body: &Body, l: LocalId) -> Option<&Rvalue> {
    body.blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .find_map(|s| match &s.kind {
            StmtKind::Assign(p, rv) if *p == Place::local(l) => Some(rv),
            _ => None,
        })
}

#[test]
fn named_arguments_run_in_the_order_of_the_parameters() {
    // `sub(b: one(), a: two())`: `two` (for `a`) runs first.
    let b = golden_built("named_args");
    let f = body(&b, "named");
    assert_eq!(callees(&b, f), ["two", "one", "sub"]);
    let (args, _) = call_of(&b, f, "sub");
    let (_, two) = call_of(&b, f, "two");
    let (_, one) = call_of(&b, f, "one");
    assert_eq!(
        args,
        [Operand::Move(two.clone()), Operand::Move(one.clone())],
        "the arguments of `sub` are in the order of its parameters"
    );
}

#[test]
fn a_method_receiver_is_read_after_the_arguments() {
    // `a.plus(one())`: the borrow of `a` comes after the call of `one`.
    let b = golden_built("method_ref");
    let f = body(&b, "on_place");
    let a = named(f, "a");
    let one = call_block(&b, f, "one");
    let borrow = f
        .blocks
        .iter()
        .position(|blk| {
            blk.stmts.iter().any(
                |s| matches!(&s.kind, StmtKind::Assign(_, Rvalue::Ref(p)) if *p == Place::local(a)),
            )
        })
        .unwrap_or_else(|| panic!("no borrow of `a`"));
    assert!(one < borrow, "the receiver is borrowed after the argument");
    let (args, _) = call_of(&b, f, "Acc.plus");
    assert!(
        matches!(&args[0], Operand::Move(p) if f.locals[p.local.index()].kind == LocalKind::Temp(TempKind::Receiver)),
        "the receiver is a `Receiver` temporary: {args:?}"
    );
    // `v.push(v.len())`: `&v` for `push` comes after the call of `len`.
    let f = body(&b, "prelude");
    let v = named(f, "v");
    let len = call_block(&b, f, "Vec.len");
    let (args, _) = call_of(&b, f, "Vec.push");
    let Operand::Move(r) = &args[0] else {
        panic!("the receiver of `push` is not a temporary: {args:?}");
    };
    assert_eq!(assigned(f, r.local), Some(&Rvalue::Ref(Place::local(v))));
    let at = f
        .blocks
        .iter()
        .position(|blk| blk.stmts.iter().any(|s| s.kind == StmtKind::Live(r.local)))
        .unwrap_or_else(|| panic!("no Live of the receiver"));
    assert!(len < at, "`&v` for `push` comes after `len`");
    // A value receiver moves at the call, after the arguments.
    let b = golden_built("method_value");
    let f = body(&b, "consume");
    let t = named(f, "t");
    let (args, _) = call_of(&b, f, "Tok.into_id");
    assert_eq!(args[0], Operand::Move(Place::local(t)));
}

#[test]
fn a_struct_literal_runs_in_written_order_and_builds_in_field_order() {
    // `P { b: two(), a: one() }`: `two` runs first; the aggregate is `(a, b)`.
    let b = golden_built("struct_lit");
    let f = body(&b, "written");
    assert_eq!(callees(&b, f), ["two", "one"]);
    let (_, two) = call_of(&b, f, "two");
    let (_, one) = call_of(&b, f, "one");
    let agg = assigned(f, f.ret);
    assert!(
        matches!(agg, Some(Rvalue::Aggregate(AggKind::Struct(_), ops))
            if *ops == [Operand::Move(one.clone()), Operand::Move(two.clone())]),
        "{agg:?}"
    );
    // A place field that the literal does not give: `Uninit` after it.
    let f = body(&b, "frame");
    assert!(
        stmts(f).iter().any(|s| matches!(s, StmtKind::Uninit(p)
            if p.local == f.ret && p.proj == [Proj::Field(weft_ir::FieldIdx(1))])),
        "no `Uninit(_0.1)`"
    );
    // A call result: its place field has no value either.
    let f = body(&b, "result");
    let x = named(f, "f");
    assert!(
        stmts(f).iter().any(|s| matches!(s, StmtKind::Uninit(p)
            if p.local == x && p.proj == [Proj::Field(weft_ir::FieldIdx(1))])),
        "no `Uninit(f.1)`"
    );
}

#[test]
fn print_and_an_interpolation_borrow_a_value_that_is_not_plain_data() {
    let b = golden_built("print_borrow");
    let f = body(&b, "show");
    let v = named(f, "v");
    let x = named(f, "x");
    let prints: Vec<&Vec<Operand>> = stmts(f)
        .into_iter()
        .filter_map(|s| match s {
            StmtKind::Print(ops) => Some(ops),
            _ => None,
        })
        .collect();
    assert_eq!(prints.len(), 2);
    let Operand::Copy(r) = &prints[0][0] else {
        panic!("`print` reads a borrow: {:?}", prints[0]);
    };
    assert_eq!(assigned(f, r.local), Some(&Rvalue::Ref(Place::local(v))));
    // The plain value `x` is copied where it is written.
    let Operand::Copy(cx) = &prints[0][1] else {
        panic!("`x` is a copy: {:?}", prints[0]);
    };
    assert_eq!(
        assigned(f, cx.local),
        Some(&Rvalue::Use(Operand::Copy(Place::local(x))))
    );
    assert!(!stmts(f).iter().any(|s| matches!(s, StmtKind::Assign(_, Rvalue::Use(Operand::Move(p))) if *p == Place::local(v))), "`v` does not move");
    let b = golden_built("interp_borrow");
    let f = body(&b, "text");
    let v = named(f, "v");
    let concat = stmts(f).into_iter().find_map(|s| match s {
        StmtKind::Assign(_, Rvalue::Concat(ops)) => Some(ops),
        _ => None,
    });
    let Some(Operand::Move(r)) = concat.and_then(|ops| ops.first()) else {
        panic!("no borrow in the interpolation: {concat:?}");
    };
    assert_eq!(assigned(f, r.local), Some(&Rvalue::Ref(Place::local(v))));
}

#[test]
fn a_duration_literal_is_a_constant_argument() {
    let b = golden_built("duration_lit");
    let f = body(&b, "waits");
    let (args, _) = call_of(&b, f, "wait");
    assert_eq!(
        args,
        [
            Operand::Const(weft_ir::Const::Duration(2000)),
            Operand::Const(weft_ir::Const::Duration(500))
        ]
    );
}

#[test]
fn an_array_literal_is_a_vec_or_an_array_aggregate() {
    let b = golden_built("vec_lit");
    let f = body(&b, "nums");
    assert!(
        matches!(assigned(f, f.ret), Some(Rvalue::Aggregate(AggKind::Vec, ops)) if ops.len() == 2),
        "{:?}",
        assigned(f, f.ret)
    );
    let b = golden_built("array_lit");
    let f = body(&b, "arr");
    assert!(
        stmts(f)
            .iter()
            .any(|s| matches!(s, StmtKind::Assign(_, Rvalue::Aggregate(AggKind::Array, ops)) if ops.len() == 2)),
        "no `Array` aggregate"
    );
}

#[test]
fn a_trailing_block_is_a_closure_argument() {
    // `twice(1) { x }` is `twice(1, || { x })`: the last argument is a
    // closure aggregate with no parameters.
    let b = golden_built("trailing_block");
    let f = body(&b, "block");
    let (args, _) = call_of(&b, f, "twice");
    let last = args
        .last()
        .and_then(Operand::place)
        .unwrap_or_else(|| panic!("no last argument"));
    let Some(Rvalue::Aggregate(AggKind::Closure(c), ops)) = assigned(f, last.local) else {
        panic!("the trailing block is not a closure aggregate");
    };
    let decl = &b.program.closures[c.index()];
    let clo = b
        .program
        .body(decl.body)
        .unwrap_or_else(|| panic!("no closure body"));
    assert_eq!(
        clo.params.len(),
        1,
        "a trailing block has only its environment"
    );
    assert_eq!(ops.len(), 1, "it captures `x`");
    assert_eq!(decl.captures[0].mode, CaptureMode::Kept);
}

#[test]
fn log_info_is_a_perform_through_the_row() {
    let b = golden_built("perform_path");
    let f = body(&b, "tell");
    let performs: Vec<&TermKind> = terms(f)
        .into_iter()
        .filter(|k| matches!(k, TermKind::Perform { .. }))
        .collect();
    assert_eq!(performs.len(), 2);
    for k in performs {
        let TermKind::Perform { cap, unwind, .. } = k else {
            continue;
        };
        let CapOperand::Row(e) = cap else {
            panic!("the capability is the row: {cap:?}");
        };
        assert_eq!(b.tys.effects()[e.index()].name, "Log");
        assert!(unwind.is_some(), "a perform can abort");
    }
}

#[test]
fn assert_has_an_unwind_block() {
    let b = golden_built("assert");
    let f = body(&b, "check");
    let asserts: Vec<Option<weft_ir::BlockId>> = terms(f)
        .into_iter()
        .filter_map(|k| match k {
            TermKind::Assert { unwind, .. } => Some(*unwind),
            _ => None,
        })
        .collect();
    assert_eq!(asserts.len(), 2);
    for u in asserts {
        let u = u.unwrap_or_else(|| panic!("`assert` has no unwind block"));
        assert!(
            f.blocks[u.index()].cleanup,
            "the unwind block is a cleanup block"
        );
    }
}

#[test]
fn box_new_and_a_parameter_of_its_own_type_build_in_place() {
    let b = golden_built("generic_extern");
    for (name, callee, in_place) in [
        ("boxes", "Box.new", true),
        ("kept", "keep", true),
        ("held", "hold", false),
    ] {
        let f = body(&b, name);
        let (args, _) = call_of(&b, f, callee);
        let Operand::Move(p) = &args[0] else {
            panic!("{name}: the argument is not a temporary: {args:?}");
        };
        assert_eq!(
            f.locals[p.local.index()].in_place,
            in_place,
            "{name}: `in_place` of the argument of `{callee}`"
        );
    }
}

#[test]
fn an_extern_function_with_an_empty_row_has_no_unwind_block() {
    let b = golden_built("generic_extern");
    let f = body(&b, "vecs");
    for k in terms(f) {
        if let TermKind::Call { unwind, .. } = k {
            assert_eq!(*unwind, None, "{k:?}");
        }
    }
    // A function with a body can abort: its call has an unwind block.
    let b = golden_built("call_args");
    let f = body(&b, "first_place");
    for k in terms(f) {
        if let TermKind::Call { unwind, .. } = k {
            assert!(unwind.is_some(), "{k:?}");
        }
    }
}

#[test]
fn each_call_passes_the_lexical_capability_environment() {
    for name in ["call_args", "perform_row", "method_ref", "generic_extern"] {
        let b = golden_built(name);
        for body in &b.program.bodies {
            for k in terms(body) {
                if let TermKind::Call { caps, .. } = k {
                    assert_eq!(*caps, CapArgs::Lexical(body.cap_env), "{name}: {k:?}");
                }
            }
        }
    }
}

#[test]
fn a_return_in_a_later_argument_ends_the_earlier_argument_temporaries() {
    // OL-3c with a call: `add2(two(), { if n > 3 { return 0 }; n })`. The
    // result of `two()` is in a temporary; the `return` path ends it.
    let b = golden_built("return_in_arg");
    let f = body(&b, "call");
    let (_, two) = call_of(&b, f, "two");
    let early: Vec<&weft_ir::Block> = f
        .blocks
        .iter()
        .filter(|blk| {
            blk.term.kind == TermKind::Return
                && blk.stmts.iter().any(|s| {
                    matches!(&s.kind, StmtKind::Assign(p, Rvalue::Use(Operand::Const(_)))
                        if *p == Place::local(LocalId(0)))
                })
        })
        .collect();
    assert_eq!(early.len(), 1, "one `return 0` path");
    assert!(
        early[0]
            .stmts
            .iter()
            .any(|s| s.kind == StmtKind::Dead(two.local)),
        "the `return` path does not end the result of `two()`"
    );
}

#[test]
fn golden_abort_chain() {
    golden("abort_chain");
}

#[test]
fn golden_on_abort_value() {
    golden("on_abort_value");
}

#[test]
fn golden_linear_parts() {
    golden("linear_parts");
}

#[test]
fn golden_scope_value_chain() {
    golden("scope_value_chain");
}

#[test]
fn golden_temps_in_chain() {
    golden("temps_in_chain");
}

/// Returns the statements of the cleanup chain that starts at block `from`
/// of `body`, to the unwind exit.
fn chain(body: &Body, from: weft_ir::BlockId) -> Vec<StmtKind> {
    let mut v = Vec::new();
    let mut cur = from.index();
    let mut seen = std::collections::BTreeSet::new();
    while seen.insert(cur) {
        let blk = &body.blocks[cur];
        assert!(blk.cleanup, "block bb{cur} of a chain is a cleanup block");
        v.extend(blk.stmts.iter().map(|s| s.kind.clone()));
        match blk.term.kind {
            TermKind::Goto(t) => cur = t.index(),
            TermKind::UnwindExit => return v,
            ref k => panic!("a chain ends with {k:?}"),
        }
    }
    panic!("the chain from {from:?} has a cycle")
}

/// Returns the unwind block of each terminator of `body` that has one, in
/// block order.
fn unwinds(body: &Body) -> Vec<weft_ir::BlockId> {
    terms(body)
        .into_iter()
        .filter_map(TermKind::unwind)
        .collect()
}

/// Returns the locals that the `Dead` statements of `stmts` end, in order.
fn deads(stmts: &[StmtKind]) -> Vec<LocalId> {
    stmts
        .iter()
        .filter_map(|s| match s {
            StmtKind::Dead(l) => Some(*l),
            _ => None,
        })
        .collect()
}

/// Returns the place and the action of each `UnwindValue` of `stmts`, as
/// text: `_3.0 OnAbort(rollback)`.
fn unwound(b: &Built, stmts: &[StmtKind]) -> Vec<String> {
    stmts
        .iter()
        .filter_map(|s| match s {
            StmtKind::UnwindValue(p, a) => {
                let a = match a {
                    weft_ir::UnwindAction::OnAbort(f) => {
                        format!("OnAbort({})", b.program.fns[f.index()].name)
                    }
                    other => format!("{other:?}"),
                };
                Some(format!("{p:?} {a}"))
            }
            _ => None,
        })
        .collect()
}

/// Returns the chain of the call of `name` in `body` (the last one, if
/// there are more).
fn chain_of_call(b: &Built, body: &Body, name: &str) -> Vec<StmtKind> {
    let i = terms(body)
        .into_iter()
        .rposition(|k| matches!(k, TermKind::Call { callee: Callee::Fn(f, _), .. } if b.program.fns[f.index()].name == name))
        .unwrap_or_else(|| panic!("no call of `{name}`"));
    let u = body.blocks[i]
        .term
        .kind
        .unwind()
        .unwrap_or_else(|| panic!("the call of `{name}` has no unwind block"));
    chain(body, u)
}

#[test]
fn a_chain_ends_temporaries_newest_first_then_locals_then_the_parameters() {
    let b = golden_built("abort_chain");
    let f = body(&b, "order");
    let c = chain_of_call(&b, f, "g");
    let (p, n, a, bb) = (named(f, "p"), named(f, "n"), named(f, "a"), named(f, "b"));
    let temps = temps_of(f, TempKind::Operand);
    let mut want_temps: Vec<LocalId> = temps
        .iter()
        .copied()
        .filter(|t| deads(&c).contains(t))
        .collect();
    want_temps.sort();
    want_temps.reverse();
    assert_eq!(
        want_temps.len(),
        2,
        "the chain of `g(b)` has two temporaries"
    );
    let mut want = want_temps.clone();
    want.extend([bb, a, LocalId(0), n, p]);
    assert_eq!(deads(&c), want);
    // A value that is not plain data is finished before its `Dead`; plain
    // data has only its `Dead`.
    let vec_temp = want_temps[1];
    let drops: Vec<LocalId> = c
        .iter()
        .filter_map(|s| match s {
            StmtKind::UnwindValue(q, weft_ir::UnwindAction::Drop) => Some(q.local),
            _ => None,
        })
        .collect();
    assert_eq!(drops, [vec_temp, a, p]);
    for (i, s) in c.iter().enumerate() {
        if let StmtKind::UnwindValue(q, _) = s {
            assert_eq!(c.get(i + 1), Some(&StmtKind::Dead(q.local)));
        }
    }
}

#[test]
fn two_chains_with_one_suffix_share_its_blocks() {
    let b = golden_built("abort_chain");
    let f = body(&b, "share");
    let u: Vec<weft_ir::BlockId> = terms(f)
        .into_iter()
        .filter(|k| matches!(k, TermKind::Call { callee: Callee::Fn(g, _), .. } if b.program.fns[g.index()].name == "g"))
        .filter_map(TermKind::unwind)
        .collect();
    assert_eq!(u.len(), 2, "two calls of `g`");
    // The chain of `g(a)` ends `b`, then goes on to the chain of `g(x)`.
    assert_eq!(f.blocks[u[1].index()].term.kind, TermKind::Goto(u[0]));
    assert_eq!(
        deads(
            &f.blocks[u[1].index()]
                .stmts
                .iter()
                .map(|s| s.kind.clone())
                .collect::<Vec<_>>()
        ),
        [named(f, "b")]
    );
    // Each cleanup block of the body is in a chain of a call: no block is
    // made twice.
    let mut blocks = std::collections::BTreeSet::new();
    for h in unwinds(f) {
        let mut cur = h.index();
        loop {
            blocks.insert(cur);
            match f.blocks[cur].term.kind {
                TermKind::Goto(t) => cur = t.index(),
                _ => break,
            }
        }
    }
    let cleanup = f.blocks.iter().filter(|x| x.cleanup).count();
    assert_eq!(blocks.len(), cleanup);
}

#[test]
fn a_type_with_on_abort_gets_on_abort() {
    let b = golden_built("on_abort_value");
    let f = body(&b, "local");
    let tx = named(f, "tx");
    assert_eq!(
        unwound(&b, &chain_of_call(&b, f, "step")),
        [format!("{:?} OnAbort(rollback)", Place::local(tx))]
    );
    let f = body(&b, "param");
    let tx = named(f, "tx");
    assert_eq!(
        unwound(&b, &chain_of_call(&b, f, "step")),
        [format!("{:?} OnAbort(rollback)", Place::local(tx))]
    );
    let f = body(&b, "temp");
    let c = chain_of_call(&b, f, "step");
    let got = unwound(&b, &c);
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(got[0].ends_with("OnAbort(rollback)"), "{got:?}");
}

#[test]
fn a_linear_part_with_no_on_abort_is_a_fault() {
    let b = golden_built("linear_parts");
    let field = |l: LocalId, k: u32| Place {
        local: l,
        proj: vec![Proj::Field(weft_ir::FieldIdx(k))],
    };
    let f = body(&b, "fields");
    let m = named(f, "m");
    assert_eq!(
        unwound(&b, &chain_of_call(&b, f, "step")),
        [
            format!("{:?} OnAbort(rollback)", field(m, 0)),
            format!("{:?} Fault", field(m, 2)),
        ]
    );
    let f = body(&b, "tuple");
    let t = named(f, "t");
    assert_eq!(
        unwound(&b, &chain_of_call(&b, f, "step")),
        [
            format!("{:?} OnAbort(rollback)", field(t, 0)),
            format!("{:?} Fault", field(t, 1)),
        ]
    );
    let f = body(&b, "guard");
    assert_eq!(
        unwound(&b, &chain_of_call(&b, f, "step")),
        [format!(
            "{:?} OnAbort(release)",
            Place::local(named(f, "g"))
        )]
    );
    let f = body(&b, "lock");
    assert_eq!(
        unwound(&b, &chain_of_call(&b, f, "step")),
        [format!("{:?} Fault", Place::local(named(f, "l")))]
    );
    let f = body(&b, "generic");
    assert_eq!(
        unwound(&b, &chain_of_call(&b, f, "step")),
        [format!("{:?} Drop", Place::local(named(f, "x")))]
    );
}

#[test]
fn the_value_of_a_frame_is_in_a_chain_only_after_it_gets_one() {
    let b = golden_built("scope_value_chain");
    let f = body(&b, "early");
    let c = chain_of_call(&b, f, "g");
    assert_eq!(
        deads(&c),
        [named(f, "v"), LocalId(0), named(f, "c")],
        "`Dead(_0)` comes after the locals"
    );
    assert!(unwound(&b, &c).iter().all(|u| !u.starts_with("_0")));
}

#[test]
fn a_chain_in_a_loop_has_the_iterator_the_element_and_the_iteration_locals() {
    let b = golden_built("temps_in_chain");
    let f = body(&b, "each");
    let c = chain_of_call(&b, f, "g");
    let it = f
        .locals
        .iter()
        .position(|d| d.kind == LocalKind::Iterator)
        .map_or_else(
            || panic!("no iterator"),
            |i| LocalId(u32::try_from(i).unwrap_or(u32::MAX)),
        );
    let x = temps_of(f, TempKind::Scrutinee)[0];
    let d = deads(&c);
    for l in [named(f, "w"), named(f, "r"), x, it, named(f, "s")] {
        assert!(d.contains(&l), "{l:?} is in the chain {d:?}");
    }
    assert!(unwound(&b, &c).contains(&format!("{:?} Drop", Place::local(it))));
}

/// Returns a text for each `Dead` of a value that is not plain data on a
/// cleanup path of `body` with no `UnwindValue` of the value before it in
/// its block (`docs/ir.md` 5.1.6).
fn unfinished(body: &Body) -> Vec<String> {
    let mut v = Vec::new();
    for (i, blk) in body.blocks.iter().enumerate() {
        if !blk.cleanup {
            continue;
        }
        for (j, s) in blk.stmts.iter().enumerate() {
            let StmtKind::Dead(l) = s.kind else { continue };
            // `Dead(_0)` with no value finishes nothing.
            if l == body.ret || body.locals[l.index()].props.copy {
                continue;
            }
            // `UnwindKont` finishes the continuation of a clause.
            let before = blk.stmts[..j].iter().any(|x| match &x.kind {
                StmtKind::UnwindValue(p, _) => p.local == l,
                StmtKind::UnwindKont(k) => *k == l,
                _ => false,
            });
            if !before {
                v.push(format!("bb{i}: Dead(_{})", l.0));
            }
        }
    }
    v
}

#[test]
fn each_value_that_is_not_plain_data_is_finished_in_a_chain() {
    for p in corpus() {
        let src =
            std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        let Ok(a) = analyze_source(&src, Options::from_markers(&src)) else {
            continue;
        };
        let b = irbuild::build(&a);
        for body in &b.program.bodies {
            let bad = unfinished(body);
            assert!(bad.is_empty(), "{}: {bad:?}", p.display());
        }
    }
}

// ---------------------------------------------------------------------------
// Plan stage B9: closures, function values, items as values (rule CAPTURE).

#[test]
fn golden_closure_ref() {
    golden("closure_ref");
}

#[test]
fn golden_closure_move() {
    golden("closure_move");
}

#[test]
fn golden_closure_kept_counter() {
    golden("closure_kept_counter");
}

#[test]
fn golden_closure_borrow_plain() {
    golden("closure_borrow_plain");
}

#[test]
fn golden_closure_nested_move() {
    golden("closure_nested_move");
}

#[test]
fn golden_fn_value_call() {
    golden("fn_value_call");
}

#[test]
fn golden_item_value() {
    golden("item_value");
}

#[test]
fn golden_once_closure() {
    golden("once_closure");
}

#[test]
fn golden_j5d_maker_borrow() {
    golden("j5d_maker_borrow");
}

#[test]
fn golden_j5b_kept_write() {
    golden("j5b_kept_write");
}

/// Returns the id of the built body of the function or test `name`.
fn body_id(b: &Built, name: &str) -> BodyId {
    let e = b
        .entries
        .iter()
        .find(|e| e.name == name)
        .unwrap_or_else(|| panic!("no body `{name}`"));
    match &e.outcome {
        Outcome::Built(id) => *id,
        other => panic!("`{name}` has no IR: {other:?}"),
    }
}

/// Returns the closures that body `maker` makes, in the order of their ids.
fn made_by(b: &Built, maker: BodyId) -> Vec<&ClosureDecl> {
    b.program
        .closures
        .iter()
        .filter(|c| c.maker == maker)
        .collect()
}

/// Returns the name of the source local of each capture of closure `c`, and
/// its mode. A capture of a capture of the maker has the name `env.k`.
fn captures(b: &Built, c: &ClosureDecl) -> Vec<(String, CaptureMode)> {
    let maker = b
        .program
        .body(c.maker)
        .unwrap_or_else(|| panic!("no maker"));
    c.captures
        .iter()
        .map(|k| {
            let name = match maker
                .local(k.source.local)
                .map(|d| (d.kind, d.name.clone()))
            {
                Some((LocalKind::Env, _)) => format!("env{:?}", k.source.proj),
                Some((_, Some(n))) => n,
                _ => format!("_{}", k.source.local.0),
            };
            (name, k.mode)
        })
        .collect()
}

/// Returns the one closure that function `name` makes.
fn one_closure<'b>(b: &'b Built, name: &str) -> &'b ClosureDecl {
    let v = made_by(b, body_id(b, name));
    assert_eq!(v.len(), 1, "`{name}` makes one closure");
    v[0]
}

#[test]
fn rule_capture_keeps_a_written_plain_value() {
    // `|| count += 1` writes `count` and does not borrow it: `Kept`.
    let b = golden_built("closure_kept_counter");
    let c = one_closure(&b, "main");
    assert_eq!(captures(&b, c), [("count".to_string(), CaptureMode::Kept)]);
    assert!(!c.once);
    let c = one_closure(&b, "counter");
    assert_eq!(captures(&b, c), [("n".to_string(), CaptureMode::Kept)]);
    let b = golden_built("j5b_kept_write");
    let c = one_closure(&b, "main");
    assert_eq!(captures(&b, c), [("n".to_string(), CaptureMode::Kept)]);
}

#[test]
fn rule_capture_borrows_a_borrowed_plain_value() {
    // `|| print(norm(&p))`: the closure borrows `p`, so it holds a reference
    // to the cell of `p` (J5d), and the aggregate operand is `&p`.
    let b = golden_built("j5d_maker_borrow");
    let make = body(&b, "make");
    let c = one_closure(&b, "make");
    assert_eq!(captures(&b, c), [("p".to_string(), CaptureMode::ByRef)]);
    let p = named(make, "p");
    assert!(
        stmts(make)
            .iter()
            .any(|s| matches!(s, StmtKind::Assign(_, Rvalue::Ref(q)) if *q == Place::local(p))),
        "the maker borrows `p` for the environment"
    );
    // In the closure body the capture is `(*env.0)`.
    let clo = b.program.body(c.body).unwrap_or_else(|| panic!("no body"));
    let env = clo.params[0];
    assert_eq!(clo.local_kind(env), Some(LocalKind::Env));
    assert!(
        stmts(clo).iter().any(|s| matches!(s, StmtKind::Assign(_, Rvalue::Ref(q))
            if q.local == env && q.proj == [Proj::Field(weft_ir::FieldIdx(0)), Proj::Deref(DerefKind::Ref)])),
        "the closure body borrows `(*env.0)`"
    );
    // J5: a borrow of a plain value inside the closure body.
    let b = golden_built("closure_borrow_plain");
    let c = one_closure(&b, "main");
    assert_eq!(captures(&b, c), [("n".to_string(), CaptureMode::ByRef)]);
    // A borrow through a captured reference does not borrow its cell.
    let c = one_closure(&b, "through");
    assert_eq!(captures(&b, c), [("p".to_string(), CaptureMode::Kept)]);
}

#[test]
fn rule_capture_reads_a_value_that_is_not_plain_data_by_reference() {
    let b = golden_built("closure_ref");
    let c = one_closure(&b, "main");
    assert_eq!(captures(&b, c), [("v".to_string(), CaptureMode::ByRef)]);
    assert!(!c.once);
}

#[test]
fn rule_capture_moves_a_moved_value() {
    let b = golden_built("closure_move");
    let main = body(&b, "main");
    let c = one_closure(&b, "main");
    assert_eq!(
        captures(&b, c),
        [
            ("v".to_string(), CaptureMode::ByMove),
            ("n".to_string(), CaptureMode::Kept)
        ]
    );
    assert!(c.once, "a closure that moves a capture is once");
    let v = named(main, "v");
    let n = named(main, "n");
    assert!(
        stmts(main).iter().any(|s| matches!(s,
            StmtKind::Assign(_, Rvalue::Aggregate(AggKind::Closure(_), ops))
                if *ops == [Operand::Move(Place::local(v)), Operand::Copy(Place::local(n))])),
        "the aggregate moves `v` and copies the cell of `n`"
    );
}

#[test]
fn an_inner_move_makes_the_outer_closure_move() {
    let b = golden_built("closure_nested_move");
    let outer = one_closure(&b, "nested");
    assert_eq!(
        captures(&b, outer),
        [("v".to_string(), CaptureMode::ByMove)]
    );
    assert!(outer.once);
    let inner = made_by(&b, outer.body);
    assert_eq!(inner.len(), 1);
    assert_eq!(
        captures(&b, inner[0]),
        [("env[Field(FieldIdx(0))]".to_string(), CaptureMode::ByMove)]
    );
    // An inner borrow makes the outer closure borrow.
    let outer = one_closure(&b, "nested_ref");
    assert_eq!(captures(&b, outer), [("w".to_string(), CaptureMode::ByRef)]);
    let inner = made_by(&b, outer.body);
    assert_eq!(
        captures(&b, inner[0]),
        [(
            "env[Field(FieldIdx(0)), Deref(Ref)]".to_string(),
            CaptureMode::ByRef
        )]
    );
}

/// Returns the callee operand of each call of a function value in `body`.
fn value_callees(body: &Body) -> Vec<&Operand> {
    terms(body)
        .into_iter()
        .filter_map(|k| match k {
            TermKind::Call {
                callee: Callee::Value(o),
                ..
            } => Some(o),
            _ => None,
        })
        .collect()
}

#[test]
fn a_once_closure_is_moved_at_its_call() {
    let b = golden_built("once_closure");
    let main = body(&b, "main");
    let c = one_closure(&b, "main");
    assert!(c.once);
    let f = named(main, "f");
    assert!(
        !main.locals[f.index()].props.copy,
        "`f` holds a once closure"
    );
    assert_eq!(value_callees(main), [&Operand::Move(Place::local(f))]);
    // A closure that calls a once closure moves it, so it is once too.
    let n = body(&b, "nested_once");
    let made = made_by(&b, body_id(&b, "nested_once"));
    assert_eq!(made.len(), 2);
    let g = made[1];
    assert_eq!(captures(&b, g), [("f".to_string(), CaptureMode::ByMove)]);
    assert!(g.once);
    let gl = named(n, "g");
    assert_eq!(value_callees(n), [&Operand::Move(Place::local(gl))]);
}

#[test]
fn a_function_value_call_reads_the_callee_first_and_can_abort() {
    let b = golden_built("fn_value_call");
    // `f(x + 1, { x })`: the callee is read into a temporary before the
    // arguments, because a later argument can run code.
    let later = body(&b, "later");
    let callee = temps_of(later, TempKind::Callee);
    assert_eq!(callee.len(), 1, "one callee temporary");
    let f = named(later, "f");
    assert_eq!(
        assigned(later, callee[0]),
        Some(&Rvalue::Use(Operand::Copy(Place::local(f))))
    );
    for k in terms(later) {
        if let TermKind::Call { unwind, .. } = k {
            assert!(unwind.is_some(), "a call of a function value can abort");
        }
    }
    // `f(x)`: no later argument runs code, so the callee is the place itself.
    let apply = body(&b, "apply");
    assert_eq!(
        value_callees(apply),
        [&Operand::Copy(Place::local(named(apply, "f")))]
    );
    // Named arguments of a function value bind by the parameter names of the
    // item in the local (`add(a, b)`): `g(b: 1, a: 2)` passes `2, 1`.
    let n = body(&b, "named");
    let args = terms(n)
        .into_iter()
        .find_map(|k| match k {
            TermKind::Call {
                callee: Callee::Value(_),
                args,
                ..
            } => Some(args.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no value call"));
    let ints: Vec<i128> = args
        .iter()
        .map(|o| match o {
            Operand::Const(Const::Int(v, _)) => *v,
            other => panic!("not a constant: {other:?}"),
        })
        .collect();
    assert_eq!(ints, [2, 1]);
}

#[test]
fn a_function_item_as_a_value_is_a_constant() {
    let b = golden_built("item_value");
    let main = body(&b, "main");
    let consts: Vec<String> = stmts(main)
        .into_iter()
        .filter_map(|s| match s {
            StmtKind::Assign(_, Rvalue::Use(Operand::Const(Const::Fn(f, tys)))) => Some(format!(
                "{}<{}>",
                b.program.fns[f.index()].name,
                tys.iter()
                    .map(|t| b.tys.show(*t))
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
            _ => None,
        })
        .collect();
    assert_eq!(consts, ["double<>", "double<>", "id<u64>"]);
}

// ---------------------------------------------------------------------------
// Plan stage B10: `handle`, clauses, `resume`, upvars (`docs/ir.md` 5.24 to
// 5.27, 5.1.7, 5.1.8).
// ---------------------------------------------------------------------------

#[test]
fn golden_m8_abort_value_into_body() {
    golden("m8_abort_value_into_body");
}

#[test]
fn golden_handle_value() {
    golden("handle_value");
}

#[test]
fn golden_clause_resume() {
    golden("clause_resume");
}

#[test]
fn golden_clause_no_resume() {
    golden("clause_no_resume");
}

#[test]
fn golden_multi_tail_upvar() {
    golden("multi_tail_upvar");
}

#[test]
fn golden_perform_local() {
    golden("perform_local");
}

#[test]
fn golden_resume_closure() {
    golden("resume_closure");
}

#[test]
fn golden_cont_field() {
    golden("cont_field");
}

#[test]
fn golden_cap_field() {
    golden("cap_field");
}

#[test]
fn golden_nested_handle() {
    golden("nested_handle");
}

/// Returns `body` with the blocks that the entry does not reach left out, each
/// `Goto` to a block of the same kind with one edge in merged into its
/// predecessor, and the blocks in breadth-first order from the entry (the
/// normal successors first, the unwind exit last). Two bodies that have the
/// same paths give the same text.
fn normalized(body: &Body) -> Body {
    let n = body.blocks.len();
    let exit = body.unwind_exit.index();
    let mut preds = vec![0_usize; n];
    let mut reached = vec![false; n];
    let mut work = vec![body.entry.index()];
    reached[body.entry.index()] = true;
    while let Some(i) = work.pop() {
        for s in body.blocks[i].term.kind.successors() {
            preds[s.index()] += 1;
            if !reached[s.index()] {
                reached[s.index()] = true;
                work.push(s.index());
            }
        }
    }
    let mut blocks: Vec<Option<weft_ir::Block>> = body
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (reached[i] || i == exit).then(|| b.clone()))
        .collect();
    for i in 0..n {
        while let Some(b) = blocks[i].as_ref() {
            let TermKind::Goto(t) = b.term.kind else {
                break;
            };
            let t = t.index();
            let cleanup = b.cleanup;
            if t == i || t == exit || preds[t] != 1 {
                break;
            }
            if blocks[t].as_ref().is_none_or(|x| x.cleanup != cleanup) {
                break;
            }
            let Some(next) = blocks[t].take() else { break };
            if let Some(b) = blocks[i].as_mut() {
                b.stmts.extend(next.stmts);
                b.term = next.term;
            }
        }
    }
    let mut order = Vec::new();
    let mut seen = vec![false; n];
    let mut queue = std::collections::VecDeque::from([body.entry.index()]);
    seen[body.entry.index()] = true;
    while let Some(i) = queue.pop_front() {
        if i != exit {
            order.push(i);
        }
        if let Some(b) = blocks[i].as_ref() {
            for s in b.term.kind.successors() {
                if !seen[s.index()] {
                    seen[s.index()] = true;
                    queue.push_back(s.index());
                }
            }
        }
    }
    order.push(exit);
    let mut new_id = vec![weft_ir::BlockId(0); n];
    for (k, &i) in order.iter().enumerate() {
        new_id[i] = weft_ir::BlockId(u32::try_from(k).unwrap_or(u32::MAX));
    }
    let mut out = body.clone();
    out.blocks = order
        .iter()
        .map(|&i| {
            let mut b = blocks[i].clone().unwrap_or_else(|| panic!("no block {i}"));
            renumber(&mut b.term.kind, &new_id);
            b
        })
        .collect();
    out.entry = new_id[body.entry.index()];
    out.unwind_exit = new_id[exit];
    out
}

/// Renames each block of terminator `k` by `new_id`.
fn renumber(k: &mut TermKind, new_id: &[weft_ir::BlockId]) {
    let f = |b: &mut weft_ir::BlockId| *b = new_id[b.index()];
    match k {
        TermKind::Goto(b) => f(b),
        TermKind::Switch {
            arms, otherwise, ..
        } => {
            for (_, b) in arms {
                f(b);
            }
            f(otherwise);
        }
        TermKind::Call { next, unwind, .. } => {
            if let Some(b) = next {
                f(b);
            }
            if let Some(b) = unwind {
                f(b);
            }
        }
        TermKind::Perform { next, unwind, .. }
        | TermKind::Resume { next, unwind, .. }
        | TermKind::Handle { next, unwind, .. } => {
            f(next);
            if let Some(b) = unwind {
                f(b);
            }
        }
        TermKind::Return | TermKind::UnwindExit | TermKind::Unreachable => {}
        other => panic!("not in M3: {other:?}"),
    }
}

#[test]
fn the_m3_program_gives_the_ir_of_section_5_37() {
    let mut b = golden_built("m8_abort_value_into_body");
    b.program.bodies = b.program.bodies.iter().map(normalized).collect();
    // The type table of the example names the effect by its source name; the
    // analysis gives its identity.
    let got = weft_ir::print::print_program(&b.program, &b.tys).replace("main.Pick", "Pick");
    // Two differences from the example of `docs/ir.md` 5.37, both of
    // earlier stages:
    // - The clause of the example has a cleanup chain that no edge enters: no
    //   terminator of the clause can abort. The builder makes a chain only
    //   for a terminator that can abort (B7, B8).
    // - The temporary of an expression statement gets its `Live` before the
    //   temporaries of its value (B7): `_3` is the `Discarded` temporary of
    //   `w.push(3)`, `_4` its receiver.
    let want = include_str!("../../weft-ir/tests/data/m3.ir")
        .replace(
            "  _3: &Vec<u64> (Temp(Receiver))\n  _4: () (Temp(Discarded))\n",
            "  _3: () (Temp(Discarded))\n  _4: &Vec<u64> (Temp(Receiver))\n",
        )
        .replace(
            "    Live(_3)\n    _3 = &_2\n    Live(_4)\n    _4 = call Vec.push<u64>(move _3, const 3u64)",
            "    Live(_3)\n    Live(_4)\n    _4 = &_2\n    _3 = call Vec.push<u64>(move _4, const 3u64)",
        )
        .replace(
            "body b2: clause h0 pick; parent b0; cap_env e0; unwind_exit bb2",
            "body b2: clause h0 pick; parent b0; cap_env e0; unwind_exit bb1",
        )
        .replace(
            "  bb1 (cleanup):\n    UnwindKont(_2)\n    Dead(_2)\n    Dead(_0)\n    Dead(_1)\n    Goto(bb2)\n  bb2 (cleanup):\n    UnwindExit\n",
            "  bb1 (cleanup):\n    UnwindExit\n",
        );
    assert!(
        got == want,
        "the IR of M3 differs from docs/ir.md 5.37:\n--- want\n{want}\n--- got\n{got}"
    );
}

/// Returns the handlers whose `handle` is in body `site`.
fn handlers_of(b: &Built, site: BodyId) -> Vec<&weft_ir::HandlerDecl> {
    b.program
        .handlers
        .iter()
        .filter(|h| h.site == site)
        .collect()
}

/// Returns the one handler of function `name`.
fn one_handler<'b>(b: &'b Built, name: &str) -> &'b weft_ir::HandlerDecl {
    let v = handlers_of(b, body_id(b, name));
    assert_eq!(v.len(), 1, "`{name}` has one `handle`");
    v[0]
}

/// Returns body `id` of `b`.
fn body_at(b: &Built, id: BodyId) -> &Body {
    b.program
        .body(id)
        .unwrap_or_else(|| panic!("no body {id:?}"))
}

/// Returns the capability operand of each perform of `body`, in block order.
fn perform_caps(body: &Body) -> Vec<&CapOperand> {
    terms(body)
        .into_iter()
        .filter_map(|k| match k {
            TermKind::Perform { cap, .. } => Some(cap),
            _ => None,
        })
        .collect()
}

/// Returns the locals of `body` that are upvar locals.
fn upvars(body: &Body) -> Vec<LocalId> {
    body.local_ids()
        .filter(|&l| matches!(body.local_kind(l), Some(LocalKind::Upvar(_))))
        .collect()
}

#[test]
fn a_handle_is_a_terminator_with_a_handled_body_and_clause_bodies() {
    let b = golden_built("handle_value");
    let main = body(&b, "main");
    let h = one_handler(&b, "main");
    let handles: Vec<&TermKind> = terms(main)
        .into_iter()
        .filter(|k| matches!(k, TermKind::Handle { .. }))
        .collect();
    assert_eq!(handles.len(), 1);
    let TermKind::Handle { dest, unwind, .. } = handles[0] else {
        unreachable!()
    };
    assert_eq!(*dest, Place::local(named(main, "r")));
    assert!(unwind.is_some(), "an abort can go past the handler");
    let handled = body_at(&b, h.handled);
    assert!(matches!(handled.kind, weft_ir::BodyKind::Handled(_)));
    assert_eq!(handled.parent, Some(body_id(&b, "main")));
    assert_eq!(
        handled.caps.len(),
        1,
        "the handled body gets the capability"
    );
    assert!(handled.params.is_empty());
    let (_, clause) = h.clauses[0];
    let clause = body_at(&b, clause);
    assert_eq!(clause.parent, Some(body_id(&b, "main")));
    assert!(clause.kont.is_some(), "a clause has its continuation");
    // The clause runs in the capability environment of the site.
    assert_eq!(clause.cap_env, main.cap_env);
    assert_eq!(
        b.program.cap_envs[handled.cap_env.index()].parent,
        Some(main.cap_env)
    );
}

#[test]
fn an_upvar_local_has_no_live_or_dead() {
    for name in ["multi_tail_upvar", "nested_handle", "resume_closure"] {
        let b = golden_built(name);
        let mut seen = 0;
        for body in &b.program.bodies {
            let ups = upvars(body);
            seen += ups.len();
            for s in stmts(body) {
                if let StmtKind::Live(l) | StmtKind::Dead(l) = s {
                    assert!(!ups.contains(l), "{name}: Live or Dead of upvar {l:?}");
                }
            }
        }
        assert!(seen > 0, "{name} has upvar locals");
    }
}

#[test]
fn the_tail_of_a_multi_handled_body_moves_its_upvar_local() {
    let b = golden_built("multi_tail_upvar");
    let h = one_handler(&b, "main");
    assert!(h.multi);
    let handled = body_at(&b, h.handled);
    let main = body(&b, "main");
    let u = named(main, "u");
    let up = upvars(handled);
    assert_eq!(up.len(), 1);
    assert_eq!(handled.local_kind(up[0]), Some(LocalKind::Upvar(u)));
    assert_eq!(
        assigned(handled, LocalId(0)),
        Some(&Rvalue::Use(Operand::Move(Place::local(up[0]))))
    );
}

#[test]
fn a_clause_chain_starts_with_unwind_kont() {
    let b = golden_built("clause_resume");
    let h = one_handler(&b, "run");
    let clause = body_at(&b, h.clauses[0].1);
    let (k, multi) = clause.kont.unwrap_or_else(|| panic!("no continuation"));
    assert!(!multi);
    assert_eq!(clause.local_kind(k), Some(LocalKind::Kont(false)));
    let us = unwinds(clause);
    assert!(!us.is_empty(), "the resume can abort");
    for u in us {
        let c = chain(clause, u);
        assert_eq!(c.first(), Some(&StmtKind::UnwindKont(k)), "{c:?}");
    }
    let resumes = terms(clause)
        .into_iter()
        .filter(|t| matches!(t, TermKind::Resume { kont, .. } if *kont == Place::local(k)))
        .count();
    assert_eq!(resumes, 1);
}

#[test]
fn a_perform_in_a_handled_body_names_its_capability_and_a_clause_uses_the_row() {
    let b = golden_built("perform_local");
    let effect = |b: &Built, name: &str| {
        let i = b
            .tys
            .effects()
            .iter()
            .position(|e| e.name == name)
            .unwrap_or_else(|| panic!("no effect {name}"));
        weft_ir::EffectId(u32::try_from(i).unwrap_or(u32::MAX))
    };
    let note = |b: &Built| effect(b, "Note");
    let say = |b: &Built| effect(b, "Say");
    let h = one_handler(&b, "work");
    let handled = body_at(&b, h.handled);
    let cap = handled.caps[0].1;
    assert_eq!(
        perform_caps(handled),
        [
            &CapOperand::Local(Place::local(cap)),
            &CapOperand::Row(note(&b))
        ]
    );
    // The clause runs in the environment of the site: `Note` comes from the
    // caller of `work`.
    let clause = body_at(&b, h.clauses[0].1);
    assert_eq!(perform_caps(clause), [&CapOperand::Row(note(&b))]);
    // A clause runs without the capability of its own handler (rule 6 of the
    // effects proof): `say` in the clause of `Say` is the `Say` of the caller.
    let h = one_handler(&b, "again");
    let clause = body_at(&b, h.clauses[0].1);
    assert_eq!(perform_caps(clause), [&CapOperand::Row(say(&b))]);
}

#[test]
fn a_perform_in_a_closure_in_a_handled_body_names_a_cap_field() {
    let b = golden_built("cap_field");
    let h = one_handler(&b, "main");
    let handled = body_at(&b, h.handled);
    let cap = handled.caps[0].1;
    let made = made_by(&b, h.handled);
    assert_eq!(made.len(), 1);
    let c = made[0];
    let k = c
        .captures
        .iter()
        .position(|x| x.mode == CaptureMode::Cap)
        .unwrap_or_else(|| panic!("no Cap field"));
    assert_eq!(c.captures[k].source, Place::local(cap));
    let cb = body_at(&b, c.body);
    let field = Place {
        local: cb.params[0],
        proj: vec![Proj::Field(weft_ir::FieldIdx(
            u32::try_from(k).unwrap_or(u32::MAX),
        ))],
    };
    assert_eq!(perform_caps(cb), [&CapOperand::Local(field.clone())]);
    // The environment of the closure body binds the effect to the field.
    let env = &b.program.cap_envs[cb.cap_env.index()];
    assert_eq!(env.adds, [(h.effect, field)]);
    // The aggregate copies the capability.
    let ops = stmts(handled)
        .into_iter()
        .find_map(|s| match s {
            StmtKind::Assign(_, Rvalue::Aggregate(AggKind::Closure(_), ops)) => Some(ops.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no closure aggregate"));
    assert_eq!(ops[k], Operand::Copy(Place::local(cap)));
}

#[test]
fn a_closure_in_a_clause_resumes_through_a_kont_field() {
    // A `once` continuation moves into the field: the closure is `once`.
    let b = golden_built("resume_closure");
    let h = one_handler(&b, "main");
    let clause = body_at(&b, h.clauses[0].1);
    let (k, _) = clause.kont.unwrap_or_else(|| panic!("no continuation"));
    let made = made_by(&b, h.clauses[0].1);
    assert_eq!(made.len(), 1);
    let c = made[0];
    assert_eq!(c.captures.len(), 1);
    assert_eq!(c.captures[0].mode, CaptureMode::Kont);
    assert_eq!(c.captures[0].source, Place::local(k));
    assert!(c.once, "a closure that holds a once continuation is once");
    let ops = stmts(clause)
        .into_iter()
        .find_map(|s| match s {
            StmtKind::Assign(_, Rvalue::Aggregate(AggKind::Closure(_), ops)) => Some(ops.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no closure aggregate"));
    assert_eq!(ops, [Operand::Move(Place::local(k))]);
    let cb = body_at(&b, c.body);
    let field = Place {
        local: cb.params[0],
        proj: vec![Proj::Field(weft_ir::FieldIdx(0))],
    };
    assert!(terms(cb)
        .into_iter()
        .any(|t| matches!(t, TermKind::Resume { kont, .. } if *kont == field)));
    // A `multi` continuation is copied: the closure can run more than once.
    let b = golden_built("cont_field");
    let h = one_handler(&b, "count");
    let made = made_by(&b, h.clauses[0].1);
    assert_eq!(made.len(), 1);
    assert_eq!(made[0].captures[0].mode, CaptureMode::Kont);
    assert!(!made[0].once);
}

#[test]
fn a_nested_body_names_the_locals_of_the_function_through_upvar_locals() {
    let b = golden_built("nested_handle");
    let main = body(&b, "main");
    let outer = one_handler(&b, "main");
    let ob = body_at(&b, outer.handled);
    let inner = handlers_of(&b, outer.handled);
    assert_eq!(inner.len(), 1);
    let inner = inner[0];
    let clause = body_at(&b, inner.clauses[0].1);
    assert_eq!(clause.parent, Some(outer.handled));
    // `base` in the inner clause: an upvar of an upvar of `base`.
    let base = named(main, "base");
    let in_outer = upvars(ob)
        .into_iter()
        .find(|&l| ob.local_kind(l) == Some(LocalKind::Upvar(base)))
        .unwrap_or_else(|| panic!("no upvar of `base` in the outer handled body"));
    assert!(upvars(clause)
        .into_iter()
        .any(|l| clause.local_kind(l) == Some(LocalKind::Upvar(in_outer))));
    // `outer()` in the inner clause performs through an upvar local of the
    // capability of the outer handled body.
    let cap = ob.caps[0].1;
    let caps = perform_caps(clause);
    assert_eq!(caps.len(), 1);
    let CapOperand::Local(p) = caps[0] else {
        panic!("not a local capability: {:?}", caps[0])
    };
    assert_eq!(clause.local_kind(p.local), Some(LocalKind::Upvar(cap)));
}

#[test]
fn a_jump_out_of_a_handled_body_or_a_clause_is_w0315() {
    let (_, b) = build(
        "effect Note { fn note(n: u64) }\nfn f() -> u64 {\n    handle Note { fn note(n) { resume(()) } } in { return 3 }\n}\nfn g() {\n    loop {\n        handle Note { fn note(n) { break } } in note(1)\n    }\n}\n",
    );
    let f = body(&b, "f");
    assert!(b.broken.is_empty(), "{}", rules(&b));
    let msgs: Vec<String> = b
        .diags
        .iter()
        .map(|d| format!("{} {}", d.code.as_str(), d.message))
        .collect();
    assert_eq!(
        msgs,
        [
            "W0315 `return` cannot leave a handled body",
            "W0315 `break` cannot leave a handler clause"
        ]
    );
    let h = one_handler(&b, "f");
    let handled = body_at(&b, h.handled);
    assert!(terms(handled)
        .into_iter()
        .any(|t| matches!(t, TermKind::Unreachable)));
    assert!(matches!(f.kind, weft_ir::BodyKind::Fn(_)));
}

#[test]
fn a_closure_inside_a_closure_takes_the_continuation_field_of_its_maker() {
    let (_, b) = build(
        "effect Choose { multi fn choose() -> bool }\neffect Pick { fn pick() -> u64 }\nfn count() -> u64 {\n    handle Choose {\n        fn choose() {\n            let a = || { let b = |x: bool| resume(x); b(true) }\n            a()\n        }\n    } in { if choose() { 1 } else { 2 } }\n}\nfn once_nested() -> u64 {\n    handle Pick {\n        fn pick() {\n            let a = || { let b = || resume(3); b() }\n            a()\n        }\n    } in { pick() }\n}\n",
    );
    assert!(b.broken.is_empty(), "{}", rules(&b));
    for (name, once) in [("count", false), ("once_nested", true)] {
        let h = one_handler(&b, name);
        let outer = made_by(&b, h.clauses[0].1);
        assert_eq!(outer.len(), 1);
        let inner = made_by(&b, outer[0].body);
        assert_eq!(inner.len(), 1);
        for c in [outer[0], inner[0]] {
            assert_eq!(c.captures.len(), 1);
            assert_eq!(c.captures[0].mode, CaptureMode::Kont);
            assert_eq!(c.once, once, "{name}");
        }
        assert_eq!(
            inner[0].captures[0].source,
            Place {
                local: LocalId(1),
                proj: vec![Proj::Field(weft_ir::FieldIdx(0))]
            }
        );
    }
}

#[test]
fn a_closure_that_uses_no_effect_holds_no_capability() {
    let (_, b) = build(
        "effect Say { fn say(msg: String) }\nfn f(n: u64) -> u64 {\n    handle Say { fn say(m) { resume(()) } } in {\n        let add = |x: u64| x + n\n        let g = || say(\"x\")\n        let h = || print(n)\n        g()\n        h()\n        add(1)\n    }\n}\n",
    );
    assert!(b.broken.is_empty(), "{}", rules(&b));
    let h = one_handler(&b, "f");
    let made = made_by(&b, h.handled);
    assert_eq!(made.len(), 3);
    let modes: Vec<Vec<CaptureMode>> = made
        .iter()
        .map(|c| c.captures.iter().map(|x| x.mode).collect())
        .collect();
    assert_eq!(
        modes,
        [
            vec![CaptureMode::Kept],
            vec![CaptureMode::Cap],
            vec![CaptureMode::Kept]
        ]
    );
}

// ---------------------------------------------------------------------------
// Plan stage B11: tasks, `sim.run`, `with_timeout` (`docs/ir.md` 5.29 to 5.31).

#[test]
fn golden_scope_wait() {
    golden("scope_wait");
}

#[test]
fn golden_spawn_handle() {
    golden("spawn_handle");
}

#[test]
fn golden_spawn_stmt_result() {
    golden("spawn_stmt_result");
}

#[test]
fn golden_join() {
    golden("join");
}

#[test]
fn golden_detach() {
    golden("detach");
}

#[test]
fn golden_fork() {
    golden("fork");
}

#[test]
fn golden_sim_run() {
    golden("sim_run");
}

#[test]
fn golden_with_timeout() {
    golden("with_timeout");
}

/// Returns the one scope body of `b`.
fn one_scope_body(b: &Built) -> &Body {
    let v: Vec<&Body> = b
        .program
        .bodies
        .iter()
        .filter(|x| matches!(x.kind, weft_ir::BodyKind::Scope(_)))
        .collect();
    assert_eq!(v.len(), 1, "the program has one scope body");
    v[0]
}

/// Returns the `ScopeWait` terminator of `body`: its orphans and its unwind
/// block.
fn scope_wait(body: &Body) -> (Vec<LocalId>, weft_ir::BlockId) {
    let found: Vec<_> = terms(body)
        .into_iter()
        .filter_map(|k| match k {
            TermKind::ScopeWait {
                orphans, unwind, ..
            } => Some((orphans.clone(), *unwind)),
            _ => None,
        })
        .collect();
    assert_eq!(found.len(), 1, "the scope body has one `ScopeWait`");
    let (orphans, unwind) = found[0].clone();
    (
        orphans,
        unwind.unwrap_or_else(|| panic!("`ScopeWait` has no unwind block")),
    )
}

#[test]
fn a_spawn_in_statement_position_gives_a_task_result_that_scope_wait_fills() {
    let b = golden_built("spawn_stmt_result");
    let s = one_scope_body(&b);
    let mut sites: Vec<weft_ir::SpawnId> = terms(s)
        .into_iter()
        .filter_map(|k| match k {
            TermKind::Spawn {
                site, dest: None, ..
            } => Some(*site),
            _ => None,
        })
        .collect();
    sites.sort();
    assert_eq!(sites.len(), 3, "three spawns in statement position");
    let results: Vec<(LocalId, weft_ir::SpawnId)> = s
        .locals
        .iter()
        .enumerate()
        .filter_map(|(i, d)| match d.kind {
            LocalKind::TaskResult(site) => Some((LocalId(u32::try_from(i).unwrap_or(0)), site)),
            _ => None,
        })
        .collect();
    let mut of: Vec<weft_ir::SpawnId> = results.iter().map(|r| r.1).collect();
    of.sort();
    assert_eq!(of, sites, "one `TaskResult` local for each spawn site");
    let (mut orphans, _) = scope_wait(s);
    orphans.sort();
    let mut locals: Vec<LocalId> = results.iter().map(|r| r.0).collect();
    locals.sort();
    assert_eq!(orphans, locals, "`ScopeWait` gives each result its value");
    // Each result has a cell from the entry: one `Live` in the entry block.
    for (l, _) in &results {
        let lives: Vec<usize> = s
            .blocks
            .iter()
            .enumerate()
            .flat_map(|(i, blk)| {
                blk.stmts
                    .iter()
                    .filter(|x| x.kind == StmtKind::Live(*l))
                    .map(move |_| i)
            })
            .collect();
        assert_eq!(lives, vec![s.entry.index()], "`Live` of {l:?}");
    }
}

#[test]
fn the_value_of_a_scope_body_is_first_in_the_chain_of_scope_wait() {
    let b = golden_built("scope_wait");
    let s = one_scope_body(&b);
    let (_, unwind) = scope_wait(s);
    let c = chain(s, unwind);
    assert_eq!(
        c.first(),
        Some(&StmtKind::UnwindValue(
            Place::local(LocalId(0)),
            weft_ir::UnwindAction::Drop
        )),
        "{c:?}"
    );
    assert_eq!(c.get(1), Some(&StmtKind::Dead(LocalId(0))), "{c:?}");
}

#[test]
fn the_scope_capability_is_finished_on_each_chain() {
    for name in ["scope_wait", "spawn_handle", "join"] {
        let b = golden_built(name);
        let s = one_scope_body(&b);
        let cap = s.params[0];
        assert_eq!(s.locals[cap.index()].kind, LocalKind::ScopeCap, "{name}");
        let us = unwinds(s);
        assert!(!us.is_empty(), "{name}: the scope body has chains");
        for u in us {
            let c = chain(s, u);
            let at = c
                .iter()
                .position(|x| *x == StmtKind::Dead(cap))
                .unwrap_or_else(|| panic!("{name}: the chain does not end `s`: {c:?}"));
            assert!(
                at > 0
                    && c[at - 1]
                        == StmtKind::UnwindValue(Place::local(cap), weft_ir::UnwindAction::Drop),
                "{name}: the chain cancels and joins the tasks at `s`: {c:?}"
            );
        }
    }
}

#[test]
fn spawn_sites_name_their_scope_and_fork_branches_have_none() {
    let b = golden_built("spawn_handle");
    assert_eq!(b.program.scopes.len(), 1);
    assert_eq!(b.program.spawns.len(), 1);
    assert_eq!(b.program.spawns[0].scope, Some(weft_ir::ScopeId(0)));
    assert!(!b.program.spawns[0].fork);
    let b = golden_built("fork");
    let forks: Vec<Vec<weft_ir::SpawnId>> = b
        .program
        .bodies
        .iter()
        .flat_map(terms)
        .filter_map(|k| match k {
            TermKind::Fork { sites, .. } => Some(sites.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(forks.len(), 2);
    assert_eq!(forks[0].len(), 2);
    assert_eq!(forks[1].len(), 2);
    for d in &b.program.spawns {
        assert!(d.fork && d.scope.is_none());
    }
    assert_eq!(b.program.spawns.len(), 4);
}

#[test]
fn sim_run_has_four_workers_by_default() {
    let b = golden_built("sim_run");
    for (name, workers) in [("test \"default workers\"", 4), ("test \"two workers\"", 2)] {
        let t = body(&b, name);
        let (args, _) = call_of(&b, t, "run");
        assert_eq!(
            args.get(1),
            Some(&Operand::Const(Const::Int(workers, weft_ir::IntTy::U64))),
            "{name}: {args:?}"
        );
        let f = b
            .program
            .fns
            .iter()
            .find(|d| d.name == "run")
            .unwrap_or_else(|| panic!("no `sim.run`"));
        assert_eq!(f.intrinsic, Some(weft_ir::Intrinsic::SimRun));
    }
}

#[test]
fn with_timeout_is_a_call_that_can_abort() {
    let b = golden_built("with_timeout");
    let f = body(&b, "timed");
    let c = chain_of_call(&b, f, "with_timeout");
    assert!(!c.is_empty());
}

#[test]
fn a_spawn_statement_in_a_nested_body_gives_its_result_to_the_scope_of_s() {
    let src = "effect Ask { fn ask() -> u64 }\nfn main() / async {\n    let r = scope { s =>\n        let f = || {\n            s.spawn(|| 1)\n            2\n        }\n        f()\n        handle Ask {\n            fn ask() { resume(1) }\n        } in {\n            s.spawn(|| 3)\n            ask()\n        }\n    }\n    print(r)\n}\n";
    let (_, b) = build(src);
    assert!(b.broken.is_empty(), "{}", rules(&b));
    let s = one_scope_body(&b);
    let mut results: Vec<weft_ir::SpawnId> = s
        .locals
        .iter()
        .filter_map(|d| match d.kind {
            LocalKind::TaskResult(site) => Some(site),
            _ => None,
        })
        .collect();
    results.sort();
    assert_eq!(results.len(), 2, "two results: {results:?}");
    let (orphans, _) = scope_wait(s);
    assert_eq!(orphans.len(), 2);
    // The spawns are in the closure body and in the handled body.
    let mut sites: Vec<weft_ir::SpawnId> = b
        .program
        .bodies
        .iter()
        .filter(|x| {
            matches!(
                x.kind,
                weft_ir::BodyKind::Closure(_) | weft_ir::BodyKind::Handled(_)
            )
        })
        .flat_map(terms)
        .filter_map(|k| match k {
            TermKind::Spawn {
                site, dest: None, ..
            } => Some(*site),
            _ => None,
        })
        .collect();
    sites.sort();
    assert_eq!(sites, results);
    for site in sites {
        assert_eq!(
            b.program.spawns[site.index()].scope,
            Some(weft_ir::ScopeId(0))
        );
    }
}

#[test]
fn a_jump_out_of_a_scope_body_is_w0315() {
    let (a, b) = build(
        "fn f() -> u64 / async {\n    scope { s =>\n        return 3\n    }\n}\nfn g() / async {\n    loop {\n        scope { s => break }\n    }\n}\n",
    );
    assert!(b.broken.is_empty(), "{}", rules(&b));
    let msgs: Vec<String> = b
        .diags
        .iter()
        .map(|d| format!("{} {}", d.code.as_str(), d.message))
        .collect();
    assert_eq!(
        msgs,
        [
            "W0315 `return` cannot leave a scope body",
            "W0315 `break` cannot leave a scope body"
        ]
    );
    // The old pipeline gives the same diagnostics.
    let old: Vec<String> = a
        .diags
        .iter()
        .filter(|d| d.code.as_str() == "W0315")
        .map(|d| format!("{} {}", d.code.as_str(), d.message))
        .collect();
    assert_eq!(old, msgs);
}

#[test]
fn each_task_result_has_one_spawn_in_statement_position() {
    for p in corpus() {
        let src =
            std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        let Ok(a) = analyze_source(&src, Options::from_markers(&src)) else {
            continue;
        };
        let b = irbuild::build(&a);
        let mut spawns = std::collections::BTreeMap::new();
        for body in &b.program.bodies {
            for k in terms(body) {
                if let TermKind::Spawn { site, dest, .. } = k {
                    let n = spawns.entry(*site).or_insert((0, 0));
                    n.0 += 1;
                    n.1 += u32::from(dest.is_none());
                }
            }
        }
        for body in &b.program.bodies {
            for d in &body.locals {
                if let LocalKind::TaskResult(site) = d.kind {
                    assert_eq!(
                        spawns.get(&site),
                        Some(&(1, 1)),
                        "{}: {site:?}",
                        p.display()
                    );
                }
            }
        }
    }
}

#[test]
fn print_borrows_a_local_that_holds_a_once_closure() {
    let (_, b) = build(
        "fn take(v: Vec<u64>) -> usize { v.len() }\nfn main() {\n    let v = Vec.new()\n    v.push(1)\n    let f = || take(v)\n    print(f)\n    print(\"{f}\")\n    print(f())\n}\n",
    );
    assert!(b.broken.is_empty(), "{}", rules(&b));
    let m = body(&b, "main");
    let f = named(m, "f");
    assert!(!m.locals[f.index()].props.copy, "`f` is a once closure");
    // `print(f)` and the interpolation read `f` through a borrow; only the
    // call moves it.
    let borrows = stmts(m)
        .into_iter()
        .filter(|s| matches!(s, StmtKind::Assign(_, Rvalue::Ref(p)) if *p == Place::local(f)))
        .count();
    assert_eq!(borrows, 2);
}
