//! The preview of group A with no call (plan stage F4).
//!
//! On each body of the corpus with no call, no `perform` and no `resume`,
//! the facts of the `ir` pipeline (`weft_sema::factgen::preview`) make the
//! production checker and the Datalog spec agree. The other bodies of a
//! program do not stop the preview: each body is checked alone.

use std::fs;
use std::path::Path;

use weft_check::{agreement, check_analysis};
use weft_sema::{analyze_source, factgen, irbuild, Options};

#[test]
fn the_checker_and_the_spec_agree_on_the_ir_facts_of_the_bodies_with_no_call() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut files: Vec<_> = fs::read_dir(&dir)
        .map(|d| {
            d.filter_map(Result::ok)
                .map(|e| e.path())
                .filter(|p| p.extension().is_some_and(|x| x == "wf"))
                .collect()
        })
        .unwrap_or_default();
    files.sort();
    let (mut agreed, mut programs) = (0usize, 0usize);
    let mut bad = Vec::new();
    for f in &files {
        let Ok(src) = fs::read_to_string(f) else {
            continue;
        };
        let Ok(a) = analyze_source(&src, Options::from_markers(&src)) else {
            continue;
        };
        let built = irbuild::build(&a);
        let mut bodies = Vec::new();
        for i in 0..built.entries.len() {
            if let (Ok(facts), Some(old)) = (factgen::preview(&a, &built, i), a.bodies.get(i)) {
                let mut b = old.clone();
                b.facts = facts;
                bodies.push(b);
            }
        }
        if bodies.is_empty() {
            continue;
        }
        programs += 1;
        let mut view = a.clone();
        view.bodies = bodies;
        view.diags = Vec::new();
        let checked = check_analysis(view, &[]);
        match agreement(&checked) {
            Ok(n) => agreed += n,
            Err(ds) => {
                for d in ds {
                    bad.push(format!(
                        "{}: `{}`: checker {:?}, spec {:?}, evidence {:?}",
                        f.display(),
                        d.function,
                        d.checker,
                        d.spec,
                        d.evidence
                    ));
                }
            }
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    eprintln!("the checker and the spec agree on {agreed} bodies of {programs} programs");
    assert!(agreed > 100, "only {agreed} bodies");
}

/// Returns the code and the start of each diagnostic of `a` with only body
/// `body` (and no diagnostic of the analysis).
fn body_diags(a: &weft_sema::Analysis, body: weft_sema::BodyFacts) -> Vec<(String, u32)> {
    let mut view = a.clone();
    view.bodies = vec![body];
    view.diags = Vec::new();
    check_analysis(view, &[])
        .diags
        .iter()
        .map(|d| (format!("{:?}", d.code), d.span.lo))
        .collect()
}

#[test]
fn the_preview_gives_the_old_diagnostics_on_the_bodies_of_the_temporaries_program() {
    // `docs/ir.md` 5.10: `let r = &1; print(r)` (`temp_copy`) has no
    // diagnostic in the old pipeline. A borrow of plain data borrows a
    // promoted temporary, so the facts of the IR agree.
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs/32_temporaries.wf");
    let src = fs::read_to_string(path).unwrap_or_default();
    let a = analyze_source(&src, Options::from_markers(&src))
        .unwrap_or_else(|d| panic!("the program does not parse: {}", d.message));
    let built = irbuild::build(&a);
    let mut seen = Vec::new();
    for (i, e) in built.entries.iter().enumerate() {
        let (Ok(facts), Some(old)) = (factgen::preview(&a, &built, i), a.bodies.get(i)) else {
            continue;
        };
        let mut b = old.clone();
        b.facts = facts;
        let ir = body_diags(&a, b);
        assert_eq!(ir, body_diags(&a, old.clone()), "`{}`", e.name);
        seen.push(e.name.clone());
    }
    assert!(seen.iter().any(|n| n == "temp_copy"), "{seen:?}");
}

/// The facts of the call nodes of a body: for each line, the places that
/// the calls on the line change (`mutates_at`), give (`call_arg`, with the
/// root), change as a callee root (`call_mut`), the variables of
/// `writes_via`, the effects that escape, and `may_abort`.
fn call_digest(
    src: &str,
    f: &weft_facts::FnFacts,
    is_call: &dyn Fn(&str) -> bool,
) -> std::collections::BTreeMap<usize, std::collections::BTreeSet<String>> {
    use std::collections::{BTreeMap, BTreeSet};
    let line = |n: weft_facts::NodeId| {
        let lo = f.node(n).span.lo as usize;
        src.get(..lo).map_or(0, |s| s.matches('\n').count() + 1)
    };
    let calls: BTreeSet<weft_facts::NodeId> = (0..f.nodes.len())
        .map(|i| weft_facts::NodeId(u32::try_from(i).unwrap_or(u32::MAX)))
        .filter(|&n| is_call(&f.node(n).label))
        .collect();
    let mut out: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
    let mut add = |n: weft_facts::NodeId, s: String| {
        if calls.contains(&n) {
            out.entry(line(n)).or_default().insert(s);
        }
    };
    let show = |p: weft_facts::PlaceId| f.place(p).display.clone();
    for &(n, p) in &f.mutates_at {
        add(n, format!("mutates_at {}", show(p)));
    }
    for &(n, p, r) in &f.call_mut {
        add(n, format!("call_mut {} {r}", show(p)));
    }
    for &(n, p, r) in &f.call_arg {
        add(n, format!("call_arg {} {r}", show(p)));
    }
    for &(n, v) in &f.writes_via {
        add(n, format!("writes_via {}", f.var(v).name));
    }
    for (n, e) in &f.escapes_at {
        add(*n, format!("escapes_at {e}"));
    }
    for &n in &f.may_abort {
        add(n, "may_abort".to_string());
    }
    out
}

#[test]
fn the_prelude_calls_give_the_call_facts_and_the_diagnostics_of_the_old_pipeline() {
    // `tests/programs/02_bad.wf` with a literal for `Entity.new()` (the
    // calls of the prelude only), and the calls `Vec.new`, `len` and
    // `clear`.
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs/02_bad.wf");
    let bad = fs::read_to_string(path).unwrap_or_default();
    assert!(bad.contains("Entity.new()"), "{bad}");
    let src = format!(
        "{}\nfn more(world: &World) / mut(world.entities) {{\n    let v = Vec.new()\n    v.push(1)\n    let n = v.len()\n    v.clear()\n    print(n + world.entities.len())\n    world.entities.clear()\n}}\n",
        bad.replace("Entity.new()", "Entity { hp: 10 }")
    );
    let a = analyze_source(&src, Options::from_markers(&src))
        .unwrap_or_else(|d| panic!("the program does not parse: {}", d.message));
    let built = irbuild::build(&a);
    let mut seen = Vec::new();
    for (i, e) in built.entries.iter().enumerate() {
        let (Ok(facts), Some(old)) = (factgen::preview(&a, &built, i), a.bodies.get(i)) else {
            continue;
        };
        let names = ["new", "push", "len", "clear"];
        let old_calls = call_digest(&src, &old.facts, &|l| names.contains(&l));
        let ir_calls = call_digest(&src, &facts, &|l| l == "call");
        assert_eq!(ir_calls, old_calls, "`{}`", e.name);
        let mut b = old.clone();
        b.facts = facts;
        assert_eq!(
            body_diags(&a, b),
            body_diags(&a, old.clone()),
            "`{}`",
            e.name
        );
        seen.push(e.name.clone());
    }
    assert!(seen.iter().any(|n| n == "bad"), "{seen:?}");
    assert!(seen.iter().any(|n| n == "more"), "{seen:?}");
}

#[test]
fn the_ir_pipeline_finds_the_references_that_a_match_through_a_reference_copies() {
    // R3RT2 and R3RT3 (`tests/gate/probes/r3/redteam/repro`): the part of
    // the repro before `mkw`, so that the `ir` pipeline checks it with
    // group A. Each `//~` marker is a
    // diagnostic of the `ir` pipeline; the old pipeline misses all but one.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/gate/probes/r3/redteam/repro/R3RT2_match_through_ref.wf");
    let full = fs::read_to_string(path).unwrap_or_default();
    let src = full.split("fn mkw").next().unwrap_or_default().to_string();
    let opts = Options {
        facts: weft_sema::FactGen::Ir,
        ir_groups: weft_sema::Groups::of(weft_sema::Group::A),
        ..Options::from_markers(&src)
    };
    let a = analyze_source(&src, opts)
        .unwrap_or_else(|d| panic!("the program does not parse: {}", d.message));
    assert!(
        a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope),
        "{:?}",
        a.ir_scope
    );
    let line = |lo: u32| {
        src.get(..lo as usize)
            .map_or(0, |s| s.matches('\n').count() + 1)
    };
    let mut got: Vec<(String, usize)> = check_analysis(a, &[])
        .diags
        .iter()
        .map(|d| (format!("{:?}", d.code), line(d.span.lo)))
        .collect();
    got.sort();
    let mut want: Vec<(String, usize)> = src
        .lines()
        .enumerate()
        .filter_map(|(i, l)| {
            l.split("//~ ")
                .nth(1)
                .map(|c| (c.trim().to_string(), i + 1))
        })
        .collect();
    want.sort();
    assert_eq!(got, want);
}

/// The codes and lines of the diagnostics of `src` with the `ir` pipeline
/// and group A on.
fn ir_codes(src: &str) -> Vec<(String, usize)> {
    let opts = Options {
        facts: weft_sema::FactGen::Ir,
        ir_groups: weft_sema::Groups::parse("A").unwrap_or(weft_sema::Groups::NONE),
        ..Options::from_markers(src)
    };
    let a = analyze_source(src, opts)
        .unwrap_or_else(|d| panic!("the program does not parse: {}", d.message));
    assert!(
        a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope),
        "{:?}",
        a.ir_scope.as_ref().and_then(|s| s.fallback.clone())
    );
    let line = |lo: u32| {
        src.get(..lo as usize)
            .map_or(0, |s| s.matches('\n').count() + 1)
    };
    check_analysis(a, &[])
        .diags
        .iter()
        .map(|d| (format!("{:?}", d.code), line(d.span.lo)))
        .collect()
}

#[test]
fn a_callee_that_keeps_a_linear_argument_makes_the_place_hold_a_linear_value() {
    // `let v = []` holds no linear value. `push` keeps its argument in `v`,
    // so `v` holds a `Tx` at its end (W0601, at the closing brace in the
    // `ir` pipeline): also through a function with no stated row, whose
    // summary comes from its body (plan stage F6).
    let direct = "linear struct Tx { id: u64 }
fn main() {
    let v: Vec<Tx> = []
    v.push(Tx { id: 1 })
    print(v.len())
}
";
    assert_eq!(ir_codes(direct), vec![("W0601".to_string(), 6)]);
    let callee = "linear struct Tx { id: u64 }
fn put(v: &Vec<Tx>) { v.push(Tx { id: 1 }) }
fn main() {
    let v: Vec<Tx> = []
    put(&v)
    print(v.len())
}
";
    assert_eq!(ir_codes(callee), vec![("W0601".to_string(), 7)]);
    // A second `push` is no overwrite: one diagnostic.
    let twice = "linear struct Tx { id: u64 }
fn main() {
    let v: Vec<Tx> = []
    v.push(Tx { id: 1 })
    v.push(Tx { id: 2 })
    print(v.len())
}
";
    assert_eq!(ir_codes(twice), vec![("W0601".to_string(), 7)]);
}

#[test]
fn the_result_of_an_operation_of_a_caller_points_into_its_argument() {
    // `ir/work/map/opres.wf` (map N1): the clause of a caller can give back
    // a reference into `v`, and `v.clear()` frees it. The old pipeline
    // accepts `body` (open-old); the facts of the IR give W0301 at the read.
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/gate/probes/ir/work/map/opres.wf");
    let src = fs::read_to_string(path).unwrap_or_default();
    let a = analyze_source(&src, Options::from_markers(&src))
        .unwrap_or_else(|d| panic!("the program does not parse: {}", d.message));
    let built = irbuild::build(&a);
    let i = built
        .entries
        .iter()
        .position(|e| e.name == "body")
        .expect("a function `body`");
    let facts = factgen::preview(&a, &built, i).unwrap_or_else(|u| panic!("{u}"));
    let mut b = a.bodies[i].clone();
    b.facts = facts;
    let line = |lo: u32| {
        src.get(..lo as usize)
            .map_or(0, |s| s.matches('\n').count() + 1)
    };
    let ir: Vec<(String, usize)> = body_diags(&a, b)
        .into_iter()
        .map(|(c, lo)| (c, line(lo)))
        .collect();
    assert_eq!(ir, vec![("W0301".to_string(), 8)]);
    assert!(body_diags(&a, a.bodies[i].clone()).is_empty());
}

#[test]
fn a_result_in_an_rc_group_depends_on_the_handle_of_the_argument() {
    // `verify/review_core/Core_S1/rt1/esc_rc_callee.wf`: the result of
    // `group_ret` is in the `rc` group, through the handle `a`. A new value
    // of `a` frees the object (W0301 at the read).
    let src = "struct Cell2 { items: Vec<u64> }
fn group_ret(h: &Rc<Cell2>) -> &Vec<u64> in Cell2.items { &h.items }
fn main() {
    let a = Rc.new(Cell2 { items: Vec.new() })
    let r = group_ret(&a)
    a = Rc.new(Cell2 { items: Vec.new() })
    print(r)
}
";
    assert_eq!(ir_codes(src), vec![("W0301".to_string(), 7)]);
}

#[test]
fn a_callee_holds_a_reference_argument_into_a_value_that_another_argument_moves() {
    // The callee gets `&v[0]` and `v`: it can free `v` and then read the
    // reference (the oracle faults). The move at the call frees `v`, and the
    // callee holds the reference until it returns (W0301 at the call).
    let src = "fn both(r: &u64, v: Vec<u64>) {
    let w = v
    w.clear()
    print(r)
}
fn main() {
    let v = Vec.new()
    v.push(1)
    both(&v[0], v)
}
";
    assert_eq!(ir_codes(src), vec![("W0301".to_string(), 9)]);
}

#[test]
fn an_assert_aborts_past_the_function_with_a_live_linear_value() {
    // `tests/gate/probes/ir/probes/p25_assert_abort.wf` and
    // `p27_assert_callee.wf` (sem-N4): W0602 at the `assert`, and at the
    // call of a function with an `assert` (plan stage F7).
    let p25 = "linear struct Lk { id: u64 }
fn done(l: Lk) { let Lk(i) = l; print(\"done\", i) }
fn main() {
    let l = Lk { id: 1 }
    let x = 3
    assert x == 4
    done(l)
}
";
    assert_eq!(ir_codes(p25), vec![("W0602".to_string(), 6)]);
    let p27 = "linear struct Lk { id: u64 }
fn done(l: Lk) { let Lk(i) = l; print(\"done\", i) }
fn check(x: u64) { assert x == 4 }
fn main() {
    let l = Lk { id: 1 }
    check(3)
    done(l)
}
";
    assert_eq!(ir_codes(p27), vec![("W0602".to_string(), 6)]);
}

#[test]
fn the_ir_pipeline_applies_the_on_abort_function_on_the_abort_path() {
    // F3-1: `undo` changes the vector through the reference in its value.
    // W0118 rejects it, and the change shows at the caller of `holder`.
    let src = "linear struct R { o: Option<&Vec<u64>> }
    on abort = undo
fn undo(r: R) {
    let R(o) = r
    match o {
        Some(v) => v.push(7),
        None => {},
    }
}
fn holder(v: &Vec<u64>) {
    let r = R { o: Some(v) }
    assert v.len() == 0
    let R(x) = r
}
fn main() {
    let v = Vec.new()
    v.push(1)
    let first = &v[0]
    holder(&v)
    print(first)
}
";
    let mut got = ir_codes(src);
    got.sort();
    assert_eq!(
        got,
        vec![("W0118".to_string(), 3), ("W0301".to_string(), 20)]
    );
    // QA2: `rollback` performs `Note`: W0118, as in the old pipeline.
    let qa2 = "effect Note { fn note(x: u64) }
linear struct Tx { id: u64 }
    on abort = rollback
fn rollback(t: Tx) { note(1); let Tx(i) = t }
fn commit(t: Tx) { let Tx(i) = t }
fn work() / fail { fail(\"x\") }
fn f() / fail {
    let t = Tx { id: 1 }
    work()
    commit(t)
}
fn main() / fail {
    f()
}
";
    assert_eq!(ir_codes(qa2), vec![("W0118".to_string(), 4)]);
    // A clean `on abort` function: no diagnostic.
    let clean = "linear struct H { items: Vec<u64> }
    on abort = undo_local
fn undo_local(h: H) {
    let H(items) = h
    items.push(1)
}
fn work() / fail { fail(\"x\") }
fn f() / fail {
    let h = H { items: Vec.new() }
    work()
    let H(x) = h
}
fn main() / fail {
    f()
}
";
    assert_eq!(ir_codes(clean), Vec::<(String, usize)>::new());
}

/// The code and the line of each diagnostic of the bodies `names` of the
/// corpus program `file`: with the facts of the old pipeline and with the
/// facts of the preview of the `ir` pipeline.
#[allow(clippy::type_complexity)]
fn corpus_bodies(
    file: &str,
    names: &[&str],
) -> Vec<(String, Vec<(String, usize)>, Vec<(String, usize)>)> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/programs")
        .join(file);
    let src = fs::read_to_string(path).unwrap_or_default();
    let a = analyze_source(&src, Options::from_markers(&src))
        .unwrap_or_else(|d| panic!("the program does not parse: {}", d.message));
    let built = irbuild::build(&a);
    let line = |lo: u32| {
        src.get(..lo as usize)
            .map_or(0, |s| s.matches('\n').count() + 1)
    };
    let lines = |ds: Vec<(String, u32)>| {
        let mut v: Vec<(String, usize)> = ds.into_iter().map(|(c, lo)| (c, line(lo))).collect();
        v.sort();
        v
    };
    let mut out = Vec::new();
    for (i, e) in built.entries.iter().enumerate() {
        if !names.contains(&e.name.as_str()) {
            continue;
        }
        let Some(old) = a.bodies.get(i) else {
            continue;
        };
        let facts = factgen::preview(&a, &built, i)
            .unwrap_or_else(|u| panic!("`{}`: no preview: {}", e.name, u.reason));
        let mut b = old.clone();
        b.facts = facts;
        out.push((
            e.name.clone(),
            lines(body_diags(&a, old.clone())),
            lines(body_diags(&a, b)),
        ));
    }
    assert_eq!(out.len(), names.len(), "{file}: {out:?}");
    out
}

#[test]
fn a_new_value_of_a_part_replaces_the_references_of_its_old_value() {
    // `docs/ir.md` 6.3: a new value of `w.x` replaces the places of `w.x`.
    // A reference in an old value of the part does not make a later use of
    // the part invalid (76 `reassign_*`, 87 `branch_stale`, the `Box`
    // shapes of 154), but a reference in a value that the part can hold
    // still does (76 `branch_keeps_part`, 87 `branch_live`). Not here: 154
    // `move_set`, where a place field reference into a boxed value moves
    // with the box (a relocation of place fields, ADR 0007; stage F20).
    let cases: [(&str, &[&str]); 3] = [
        (
            "76_ref_flow.wf",
            &[
                "reassign_part",
                "reassign_whole",
                "branch_keeps_part",
                "new_part_value",
            ],
        ),
        ("87_stored_refs.wf", &["branch_stale", "branch_live"]),
        (
            "154_unset_nested.wf",
            &["new_box", "store_unset", "new_box_set", "new_frame"],
        ),
    ];
    let mut bad = Vec::new();
    for (file, names) in cases {
        for (name, old, ir) in corpus_bodies(file, names) {
            if old != ir {
                bad.push(format!("{file} `{name}`: old {old:?}, ir {ir:?}"));
            }
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn a_part_that_is_stale_on_one_branch_is_valid_after_the_join() {
    let src = "struct E { hp: u64 }
struct World { entities: Vec<E> }
struct Wrap<T> { x: T }
fn moved_rest(a: &World, b: &World) / mut(a.entities) {
    let w = Wrap { x: (&b.entities[0], []) }
    w.x = (&a.entities[0], [&b.entities[0]])
    let m = w.x.1
    a.entities.clear()
    print(w.x.0.hp)
}
fn stale_then(a: &World, b: &World, c: bool) / mut(a.entities) {
    let w = Wrap { x: &b.entities[0] }
    if c {
        w.x = &a.entities[0]
        w.x = &b.entities[0]
        a.entities.clear()
    } else {
        w.x = &a.entities[0]
    }
    print(w.x.hp)
}
fn stale_then_live(a: &World, b: &World, c: bool) / mut(a.entities) {
    let w = Wrap { x: &b.entities[0] }
    if c {
        w.x = &a.entities[0]
        w.x = &b.entities[0]
    } else {
        w.x = &a.entities[0]
    }
    a.entities.clear()
    print(w.x.hp)
}
fn main() {}
";
    let mut got = ir_codes(src);
    got.sort();
    // The rest of a part after a move of another part keeps its references
    // (line 9: W0301 and the W0302 of the R3a encoding); the stale value of
    // the `then` branch is not a use at line 20; the value of the `else`
    // branch is (line 31). The old pipeline gives the same.
    let want: Vec<(String, usize)> = [("W0301", 9), ("W0301", 31), ("W0302", 9)]
        .iter()
        .map(|(c, l)| ((*c).to_string(), *l))
        .collect();
    assert_eq!(got, want);
}

/// The codes and lines of the diagnostics of `src` with the old pipeline.
fn old_codes(src: &str) -> Vec<(String, usize)> {
    let a = analyze_source(src, Options::from_markers(src))
        .unwrap_or_else(|d| panic!("the program does not parse: {}", d.message));
    let line = |lo: u32| {
        src.get(..lo as usize)
            .map_or(0, |s| s.matches('\n').count() + 1)
    };
    let mut v: Vec<(String, usize)> = check_analysis(a, &[])
        .diags
        .iter()
        .map(|d| (format!("{:?}", d.code), line(d.span.lo)))
        .collect();
    v.sort();
    v
}

#[test]
fn a_returned_reference_into_a_local_is_w0204_at_the_returned_expression() {
    // `docs/ir.md` 6.9: `error(_0, Return)` of a function is W0204 at the
    // span of the `Return` origin, as the old lowering. A by-value
    // parameter that the signature states has only the W0204 of the
    // signature check. `fn one() -> &u64 { &1 }`: the promoted temporary
    // ends at the frame end.
    let src = "struct E { hp: u64 }
struct Wrap<T> { x: T }
fn local_ref() -> Option<&u64> {
    let v: Vec<u64> = Vec.new()
    v.push(1)
    Some(&v[0])
}
fn wrapped_local() -> Wrap<&u64> {
    let v: Vec<u64> = Vec.new()
    v.push(1)
    Wrap { x: &v[0] }
}
fn ret_local(v: &Vec<u64>) -> &u64 in v[] {
    let w = Vec.new()
    w.push(1)
    &w[0]
}
fn ret_by_value(v: Vec<u64>) -> &u64 in v[] { &v[0] }
fn ret_in_by_value(v: Vec<u64>, r: &u64 in v[]) -> &u64 in v[] { r }
fn one() -> &u64 { &1 }
fn early(c: bool) -> &u64 {
    let w = [1, 2]
    if c { return &w[0] }
    &2
}
fn main() {}
";
    let mut got = ir_codes(src);
    got.sort();
    assert_eq!(got, old_codes(src));
    assert!(
        got.iter().filter(|(c, _)| c == "W0204").count() >= 7,
        "{got:?}"
    );
    assert!(!got.iter().any(|(c, _)| c == "W0301"), "{got:?}");
}

#[test]
fn a_linear_parameter_that_the_body_drops_is_w0601_at_the_function() {
    // The old lowering ends the parameters at a node with the span of the
    // function: W0601 of a parameter is at the line of the declaration
    // (70_type_props, 72 `match_payload_wild`). A local ends at the
    // closing brace in both pipelines.
    let src = "linear struct Tok { id: u64 }
linear struct Tx { id: u64 }
fn in_option(o: Option<Tok>) {
    let x = 1
}
fn match_payload_wild(o: Option<Tx>) {
    match o {
        Some(_) => {},
        None => {}
    }
}
fn loc() {
    let t = Tok { id: 1 }
    let y = 2
}
fn main() {}
";
    let mut got = ir_codes(src);
    got.sort();
    assert_eq!(got, old_codes(src));
}

#[test]
fn a_receiver_that_a_later_argument_moves_is_rejected() {
    // `docs/ir.md` 5.19: the receiver is read after the arguments. In
    // 33_rc_deps line 32 (`a.items.push(eat(a))`) `eat` moves `a` before the
    // receiver reads it: W0302 (the old pipeline says W0301). The IR engine
    // faults on it (weft-interp `compile_ir.rs`).
    let src = "struct Cell2 { items: Vec<u64>, n: u64 }
fn mk() -> Rc<Cell2> { Rc.new(Cell2 { items: Vec.new(), n: 4 }) }
fn eat(c: Rc<Cell2>) -> u64 { 0 }
fn receiver_moved() {
    let a = mk()
    a.items.push(eat(a))
}
fn main() {}
";
    assert_eq!(ir_codes(src), vec![("W0302".to_string(), 6)]);
    assert_eq!(old_codes(src), vec![("W0301".to_string(), 6)]);
}

#[test]
fn a_later_operand_of_one_call_that_reads_a_moved_local_is_w0302() {
    // Review of stage F8 (hole H1): two operands of one call or aggregate on
    // one local. The second operand reads the value that the first moves.
    let src = "\
struct S { items: Vec<u64>, n: u64 }
linear struct Tx { id: u64 }
fn two(a: Vec<u64>, b: Vec<u64>) {}
fn commit2(a: Tx, b: Tx) { let Tx(i) = a; let Tx(j) = b }
fn consume2(v: Vec<u64>, w: Vec<u64>) -> u64 { 1 }
fn consume_s(s: S, n: u64) -> u64 { n }
fn consume_z(v: Vec<u64>, n: usize) -> usize { n }
fn consume_r(v: Vec<u64>, w: &Vec<u64>) -> usize { w.len() }
fn consume(v: Vec<u64>, n: u64) -> u64 { n }
fn mk() -> S { S { items: Vec.new(), n: 3 } }
fn whole_twice() {
    let v = Vec.new()
    two(v, v)   //~ W0302
}
fn linear_twice() {
    let t = Tx { id: 1 }
    commit2(t, t)   //~ W0302
}
fn part_twice() {
    let s = mk()
    print(consume2(s.items, s.items))   //~ W0302
}
fn whole_then_part() {
    let s = mk()
    print(consume_s(s, s.n))   //~ W0302
}
fn len_after() {
    let s = mk()
    print(consume_z(s.items, s.items.len()))   //~ W0302
}
fn ref_after() {
    let s = mk()
    print(consume_r(s.items, &s.items))   //~ W0302
}
fn block_arg() {
    let s = mk()
    print(consume(s.items, { s.items.push(2); 3 }))   //~ W0302
}
fn tuple_twice() {
    let v = Vec.new()
    let t = (v, v)   //~ W0302
}
fn other_parts() {
    // A read of another part after a part move: W0302 in both pipelines
    // (the read uses `S(s)`; i12_partial_arg).
    let s = mk()
    print(consume(s.items, s.n))   //~ W0302
}
fn main() {}
";
    let mut want: Vec<(String, usize)> = src
        .lines()
        .enumerate()
        .filter(|(_, l)| l.contains("//~ W0302"))
        .map(|(i, _)| ("W0302".to_string(), i + 1))
        .collect();
    want.sort();
    let got: Vec<(String, usize)> = ir_codes(src)
        .into_iter()
        .filter(|(c, _)| c == "W0302")
        .collect();
    assert_eq!(got, want, "{:?}", ir_codes(src));
}

#[test]
fn the_tail_of_an_if_with_no_else_moves_its_place() {
    // Review of stage F8 (hole H2): ADR 0003 and docs/ir.md 5.1.3. The tail
    // of the branch of an `if` with no `else` moves into a temporary that
    // drops it (st2_if_semi, 127_place_statements `if_tail_moves`).
    let src = "\
linear struct Tx { id: u64 }
fn mk() -> Vec<u64> { Vec.new() }
fn commit(t: Tx) { let Tx(i) = t }
fn if_tail(c: bool) {
    let v = mk()
    if c { v }
    print(v.len())   //~ W0302
}
fn linear_tail() {
    let t = Tx { id: 1 }
    if true { t }   //~ W0601
    commit(t)   //~ W0302
}
fn plain_tail(c: bool) {
    let n = 1
    if c { n }
    print(n)
}
fn index_tail(c: bool) {
    let v = mk()
    if c { v[0] }
    print(v.len())
}
fn main() {}
";
    let mut want: Vec<(String, usize)> = src
        .lines()
        .enumerate()
        .filter_map(|(i, l)| {
            l.split("//~ ")
                .nth(1)
                .map(|c| (c.trim().to_string(), i + 1))
        })
        .collect();
    want.sort();
    let mut got = ir_codes(src);
    got.sort();
    assert_eq!(got, want);
}

#[test]
fn a_read_through_a_reference_to_a_part_that_holds_a_reference_uses_its_owner() {
    // Review of stage F8 (hole H3, x_refref_tuple): `r` points into `t.1`,
    // and `t.1` points into `b[]`. `print(r)` reads `**r`: the read uses
    // the variables of `t`, so the end of `b[]` makes it invalid. A
    // reference to a part of plain data stays valid.
    let src = "\
fn mkv() -> Vec<u64> { let v = Vec.new(); v.push(1); v }
fn show(r: &&u64) { print(r) }
fn tuple_part() {
    let b = mkv()
    let t = (5, &b[0])
    let r = &t.1
    b.clear()
    print(r)   //~ W0301
}
fn tuple_part_call() {
    let b = mkv()
    let t = (5, &b[0])
    let r = &t.1
    b.clear()
    show(r)   //~ W0301
}
fn plain_part() {
    let b = mkv()
    let t = (5, &b[0])
    let r = &t.0
    b.clear()
    print(r)
}
fn main() {}
";
    let mut want: Vec<(String, usize)> = src
        .lines()
        .enumerate()
        .filter_map(|(i, l)| {
            l.split("//~ ")
                .nth(1)
                .map(|c| (c.trim().to_string(), i + 1))
        })
        .collect();
    want.sort();
    let mut got = ir_codes(src);
    got.sort();
    assert_eq!(got, want);
}

/// The `//~ CODE` markers of `src` as (code, line), sorted.
fn markers(src: &str) -> Vec<(String, usize)> {
    let mut want: Vec<(String, usize)> = src
        .lines()
        .enumerate()
        .filter_map(|(i, l)| {
            l.split("//~ ")
                .nth(1)
                .map(|c| (c.trim().to_string(), i + 1))
        })
        .collect();
    want.sort();
    want
}

#[test]
fn a_read_through_a_chain_of_references_uses_the_owners_at_each_level() {
    // Second review of stage F8 (hole N1, f8/variants2/h3/h3_j*): the read
    // goes `r -> u.1 -> t -> t.1 -> b[]`. Only `t.1` is stale after the
    // clear. The read uses the owners of each place on the chain, to a
    // fixpoint, so the stale `t.1` makes it invalid. A clean read before
    // the clear, and a chain of new values after it, stay valid.
    let src = "\
fn mkv() -> Vec<u64> { let v = Vec.new(); v.push(1); v }
fn show3(x: &&(u64, &u64)) { print(x) }
fn sum3(x: &&(u64, &u64)) -> u64 { x.1 + 0 }
fn tuple_of_tuple_ref() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    let r = &u.1
    b.clear()
    print(r)   //~ W0301
}
fn ref_whole_outer() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    let r = &u
    b.clear()
    print(r)   //~ W0301
}
fn ref_of_ref_in_tuple() {
    let b = mkv()
    let t = (5, &b[0])
    let u = &t
    let w = (7, &u)
    let r = &w.1
    b.clear()
    print(r)   //~ W0301
}
fn four_levels() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    let w = (7, &u)
    let r = &w.1
    b.clear()
    print(r)   //~ W0301
}
fn call_arg() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    let r = &u.1
    b.clear()
    show3(r)   //~ W0301
}
fn call_arg_sum() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    let r = &u.1
    b.clear()
    print(sum3(r))   //~ W0301
}
fn option_nest() {
    let b = mkv()
    let o = Some(&b[0])
    let p = (1, &o)
    let r = &p.1
    b.clear()
    print(r)   //~ W0301
}
fn vec_nest() {
    let b = mkv()
    let vs = Vec.new()
    vs.push(&b[0])
    let t = (1, &vs)
    let r = &t.1
    b.clear()
    print(r)   //~ W0301
}
fn copy_then_print() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    let r = &u.1
    b.clear()
    let x = r
    print(x)   //~ W0301
}
fn clean_before_the_clear() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    let r = &u.1
    print(r)
    show3(r)
    b.clear()
}
fn clean_new_values() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    b.clear()
    b.push(3)
    let t2 = (5, &b[0])
    let u2 = (6, &t2)
    let r = &u2.1
    print(r)
}
fn main() {}
";
    let mut got = ir_codes(src);
    got.sort();
    assert_eq!(got, markers(src));
}

#[test]
fn an_interpolation_and_a_comparison_read_through_their_operands() {
    // Second review of stage F8 (hole N2, f8/variants2/h3/h3_k*): the parts
    // of an interpolation (`Concat`) and the operands of a comparison of
    // values that hold references read through the references, as `print`
    // does. `==` of a scalar through `r` stays W0301 (a deref place).
    let src = "\
fn mkv() -> Vec<u64> { let v = Vec.new(); v.push(1); v }
fn interp() {
    let b = mkv()
    let t = (5, &b[0])
    let r = &t.1
    b.clear()
    let s = \"{r}\"   //~ W0301
    print(s)
}
fn print_interp() {
    let b = mkv()
    let t = (5, &b[0])
    let r = &t.1
    b.clear()
    print(\"v={r}\")   //~ W0301
}
fn interp_ref_whole() {
    let b = mkv()
    let t = (5, &b[0])
    let r = &t
    b.clear()
    let s = \"{r}\"   //~ W0301
    print(s)
}
fn interp_deep() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    let w = (7, &u)
    let r = &w.1
    b.clear()
    let s = \"x {r} y\"   //~ W0301
    print(s)
}
fn interp_whole_tuple() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    b.clear()
    print(\"{u}\")   //~ W0301
}
fn eq_whole_tuple() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    b.clear()
    print(u == u)   //~ W0301
}
fn eq_deep() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    let r = &u.1
    b.clear()
    print(r == r)   //~ W0301
}
fn clean_interp() {
    let b = mkv()
    let t = (5, &b[0])
    let u = (6, &t)
    let r = &u.1
    print(\"{r} {u}\")
    print(u == u)
    b.clear()
}
fn main() {}
";
    let mut got = ir_codes(src);
    got.sort();
    assert_eq!(got, markers(src));
}

#[test]
fn a_perform_argument_reads_through_its_references() {
    // The handler of an operation can read through each argument, as a
    // callee does: the argument uses the owners of the chain.
    let src = "\
fn mkv() -> Vec<u64> { let v = Vec.new(); v.push(1); v }
effect Show { fn show(x: &&u64) }
fn f() / Show {
    let b = mkv()
    let t = (5, &b[0])
    let r = &t.1
    b.clear()
    show(r)   //~ W0301
}
fn g() / Show {
    let b = mkv()
    let t = (5, &b[0])
    let r = &t.1
    show(r)
    b.clear()
}
fn main() {}
";
    let mut got = ir_codes(src);
    got.sort();
    assert_eq!(got, markers(src));
}

#[test]
fn a_bind_after_the_consume_of_another_part_is_one_destructure() {
    // Tier 2 of stage F8 (verify/partb/S4/run/match_none.wf): the arm
    // `(None, Some(b))` consumes `p.0` (a variant with no payload) and then
    // moves the payload of `p.1`. Both are parts of one destructure: the
    // move does not read the moved `p` (no W0302).
    let src = "\
linear struct Tx { id: u64 }
fn rollback(tx: Tx) { let Tx(i) = tx }
fn m(p: (Option<Tx>, Option<Tx>)) {
    match p {
        (None, None) => {},
        (Some(a), Some(b)) => {
            rollback(a)
            rollback(b)
        },
        (None, Some(b)) => rollback(b),
        (Some(a), None) => rollback(a),
    }
}
fn pair(p: (Tx, Tx)) {
    // The move of `p.1` ends `p`: `p.0` moved before (a hole of the state),
    // so no other part is linear (no W0601).
    let (a, b) = p
    rollback(a)
    rollback(b)
}
fn main() {}
";
    assert_eq!(ir_codes(src), Vec::<(String, usize)>::new());
}

#[test]
fn a_move_of_an_element_leaves_the_other_linear_elements() {
    // r4_partmove (tier 1): the move of `a[0]` leaves `a[1]`: W0601 at the
    // end of the function, also with the holes of earlier part moves.
    let src = "\
linear struct Tx { id: u64 }
fn rollback(tx: Tx) { let Tx(i) = tx }
fn begin(n: u64) -> Tx { Tx { id: n } }
struct W { v: Vec<Tx>, t: Tx }
fn arr_part() {
    let a = [begin(1), begin(2)]
    rollback(a[0])
}
fn field_elem(w: W) {
    rollback(w.t)
    rollback(w.v[0])
}
fn main() {}
";
    // The same errors as the old pipeline: W0601 of `a` at its end and of
    // `w` at its declaration, and W0302 for the read of `w.v` after the move
    // of `w.t` (a read of another part after a part move).
    let mut got = ir_codes(src);
    got.sort();
    let want: Vec<(String, usize)> = [("W0302", 11), ("W0601", 8), ("W0601", 9)]
        .iter()
        .map(|(c, l)| ((*c).to_string(), *l))
        .collect();
    assert_eq!(got, want);
}

#[test]
fn a_variant_step_read_after_a_new_value_of_its_base_is_w0301() {
    // Third review of stage F8 (hole R1, f8/variants3/x*, y*, z*): the IR
    // tests the variant of a receiver place before the arguments and reads
    // the payload after them (`docs/ir.md` 5.19). An argument that gives the
    // base a new value (an assignment, a call that changes it) makes the
    // test stale: the IR engine would read the payload of another variant.
    // The value of an assignment runs before its target (5.6), but the
    // source names the target first: a value that gives the base of a
    // variant step of the target a new value is W0301 too. A write below
    // the payload, a write of another local and a write after the read stay
    // valid, and so do the binds of a pattern.
    let src = "\
struct Entity { hp: i32 }
impl Entity {
    fn plus(self, n: i32) -> i32 { self.hp + n }
    fn plusv(self: Entity, n: i32) -> i32 { self.hp + n }
    fn bump(self, n: i32) -> i32 / mut(self) { self.hp += n; self.hp }
}
struct Other { b: i32 }
enum Two { A(Entity), B(Other) }
enum Outer { X(Two), Y(i32) }
struct H { t: Two }
fn flip(h: &H) -> i32 / mut(h.t) { h.t = Two.B(Other { b: 1000 }); 5 }
fn recv_borrow() {
    let e = Two.A(Entity { hp: 1 })
    print(e.A.plus({ e = Two.B(Other { b: 1000 }); 0 }))   //~ W0301
}
fn recv_mut() {
    let e = Two.A(Entity { hp: 1 })
    print(e.A.bump({ e = Two.B(Other { b: 1000 }); 5 }))   //~ W0301
}
fn recv_value() {
    let e = Two.A(Entity { hp: 1 })
    print(e.A.plusv({ e = Two.B(Other { b: 1000 }); 0 }))   //~ W0301
}
fn recv_index() {
    let v = Vec.new()
    v.push(Two.A(Entity { hp: 1 }))
    print(v[0].A.plus({ v[0] = Two.B(Other { b: 1000 }); 0 }))   //~ W0301
}
fn recv_some() {
    let o = Some(Entity { hp: 1 })
    print(o.Some.plus({ o = None; 0 }))   //~ W0301
}
fn recv_some_index() {
    let v = Vec.new()
    v.push(Entity { hp: 1 })
    let o = Some(v)
    print(o.Some[0].plus({ o = None; 0 }))   //~ W0301
}
fn recv_field() {
    let h = H { t: Two.A(Entity { hp: 1 }) }
    print(h.t.A.plus({ h.t = Two.B(Other { b: 1000 }); 0 }))   //~ W0301
}
fn recv_call() {
    let h = H { t: Two.A(Entity { hp: 1 }) }
    print(h.t.A.plus(flip(&h)))   //~ W0301
}
fn recv_ref_param(h: &H) -> i32 / mut(h.t) {
    h.t.A.plus({ h.t = Two.B(Other { b: 1000 }); 0 })   //~ W0301
}
fn recv_inner() {
    let o = Outer.X(Two.A(Entity { hp: 1 }))
    print(o.X.A.plus({ o.X = Two.B(Other { b: 1000 }); 0 }))   //~ W0301
}
fn assign_target() {
    let e = Two.A(Entity { hp: 1 })
    e.A.hp = { e = Two.B(Other { b: 1000 }); 5 }   //~ W0301
}
fn compound_target() {
    let e = Two.A(Entity { hp: 1 })
    e.A.hp += { e = Two.B(Other { b: 1000 }); 5 }   //~ W0301
}
fn assign_call() {
    let h = H { t: Two.A(Entity { hp: 1 }) }
    h.t.A.hp = flip(&h)   //~ W0301
}
fn clean_payload_write() {
    let e = Two.A(Entity { hp: 1 })
    print(e.A.plus({ e.A.hp = 7; 0 }))
}
fn clean_other_local() {
    let e = Two.A(Entity { hp: 1 })
    let k = 3
    print(e.A.plus({ k = 4; k }))
    e.A.hp = { k = 5; k }
    e.A.hp += { let z = 4; z + 1 }
}
fn clean_write_after() {
    let e = Two.A(Entity { hp: 1 })
    print(e.A.plus(2))
    e = Two.B(Other { b: 1000 })
    let o = Some(Entity { hp: 1 })
    o.Some.hp = 4
    o = None
    o = Some(Entity { hp: 2 })
    print(o.Some.plus(1))
}
fn clean_match(e: Two, p: Option<(Vec<i32>, Vec<i32>)>) {
    match e {
        Two.A(x) => {
            e = Two.B(Other { b: 1000 })
            print(x.hp)
        },
        Two.B(o) => print(o.b),
    }
    match p {
        Some((a, b)) => {
            print(a.len())
            print(b.len())
        },
        None => {},
    }
}
fn main() {}
";
    let mut got = ir_codes(src);
    got.sort();
    assert_eq!(got, markers(src));
}

#[test]
fn a_value_stored_behind_a_reference_parameter_is_read_back_from_its_heap_slot() {
    // Stage F10a (tier 2 lost faults `W3_store_behind.wf`, `W3b`): a body
    // puts `&v[0]` into the vector behind `out`, reads it back, borrows
    // into it, and clears `v[0].kids`. The heap slot of `*out`
    // (`docs/ir.md` 6.6) keeps the places of the stored reference, so the
    // read gives `v[0]` and the borrow `k` is invalid. A store into one
    // parameter and a read of another, and a read before the change, are
    // valid.
    let src = "\
struct Entity { hp: i32, id: u64, kids: Vec<Entity> }
fn behind(v: &Vec<Entity>, out: &Vec<&Entity>) / mut(v.., out) {
    let e = &v[0]
    out.push(e)
    let c = out[out.len() - 1]
    let k = &c.kids[0]
    e.kids.clear()
    print(k.hp)   //~ W0301
}
fn other(v: &Vec<Entity>, out: &Vec<&Entity>, w: &Vec<&Entity>) / mut(v.., out) {
    let e = &v[0]
    out.push(e)
    let c = w[0]
    let k = &c.kids[0]
    e.kids.clear()
    print(k.hp)
}
fn before(v: &Vec<Entity>, out: &Vec<&Entity>) / mut(v.., out) {
    let e = &v[0]
    out.push(e)
    let c = out[out.len() - 1]
    let k = &c.kids[0]
    print(k.hp)
    e.kids.clear()
}
fn main() {}
";
    let mut got = ir_codes(src);
    got.sort();
    assert_eq!(got, markers(src));
}
