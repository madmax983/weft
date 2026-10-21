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
    AggKind, Body, Callee, CapArgs, CapOperand, DerefKind, LocalId, LocalKind, Operand, Place,
    Proj, Rvalue, StmtKind, TempKind, TermKind,
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
    let (_, b) = build("fn f() -> u64 {\n    let g = || 1\n    1\n}\n");
    let e = b
        .entries
        .iter()
        .find(|e| e.name == "f")
        .unwrap_or_else(|| panic!("no `f`"));
    match &e.outcome {
        Outcome::Unsupported(u) => {
            assert_eq!(u.construct.name(), "closure");
            assert_eq!(u.construct.stage(), "B9");
        }
        other => panic!("a closure is for stage B9: {other:?}"),
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
    // The closure literal is for plan stage B9: until then the body stops
    // there, at the trailing block.
    let b = golden_built("trailing_block");
    let e = b
        .entries
        .iter()
        .find(|e| e.name == "block")
        .unwrap_or_else(|| panic!("no `block`"));
    match &e.outcome {
        Outcome::Unsupported(u) => assert_eq!(u.construct.name(), "closure"),
        other => panic!("a trailing block is a closure: {other:?}"),
    }
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
fn sim_run_and_with_timeout_are_for_stage_b11() {
    let src = "fn f() -> u64 / async, fail {\n    with_timeout(1.s, g)\n}\nfn g() -> u64 { 1 }\ntest \"t\" {\n    sim.run(seed: 1) {\n        print(1)\n    }\n}\n";
    let (_, b) = build(src);
    for name in ["f", "test \"t\""] {
        let e = b
            .entries
            .iter()
            .find(|e| e.name == name)
            .unwrap_or_else(|| panic!("no `{name}`"));
        match &e.outcome {
            Outcome::Unsupported(u) => {
                assert_eq!(u.construct.name(), "intrinsic call", "{name}");
                assert_eq!(u.construct.stage(), "B11");
            }
            other => panic!("{name}: an intrinsic call is for stage B11: {other:?}"),
        }
    }
}
