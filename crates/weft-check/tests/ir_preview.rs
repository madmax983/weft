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
    // `tests/programs/02_bad.wf` with a literal for `Entity.new()` (a
    // function with no stated signature gets its summary in stage F6), and
    // the calls `Vec.new`, `len` and `clear`.
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
    // R3RT2 and R3RT3 (`tests/gate/probes/r3/redteam/repro`): the repro with
    // no call of a function with no stated signature (stage F6), so that
    // the `ir` pipeline checks it with group A. Each `//~` marker is a
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
