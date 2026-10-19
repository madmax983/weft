//! Tests for semantic analysis.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use std::fmt::Write as _;

use weft_facts::{FnFacts, PlaceId, RootKind, VarId};
use weft_syntax::parse_file;

use crate::{
    analyze, analyze_source, prelude_unit, Analysis, Options, Unit, PRELUDE_UNIT, ROOT_UNIT,
};

/// The parsed prelude.
fn prelude() -> Unit {
    prelude_unit().expect("the prelude parses")
}

fn unit(name: &str, src: &str) -> Unit {
    Unit {
        name: name.into(),
        file: parse_file(src).unwrap_or_default(),
        is_std: false,
    }
}

/// Analyzes a root unit and dependency units `(name, source)`.
fn analyze_units(root: &str, deps: &[(&str, &str)]) -> Analysis {
    let mut units = vec![prelude(), unit("", root)];
    units.extend(deps.iter().map(|(n, s)| unit(n, s)));
    analyze(&units, Options::default())
}

fn codes(a: &Analysis) -> Vec<(usize, String)> {
    a.diags.iter().map(|d| (d.unit, d.code.clone())).collect()
}

#[test]
fn root_sees_dependency_modules() {
    let a = analyze_units(
        "fn main() { let n = json.parse(1)\n logger.note(n) }",
        &[
            ("json", "pub fn parse(n: u64) -> u64 { n }"),
            ("logger", "pub fn note(n: u64) { print(n) }"),
        ],
    );
    assert_eq!(codes(&a), Vec::new());
}

#[test]
fn dependency_name_cannot_hide_a_name_of_the_root() {
    // `log` is the alias of the standard effect `Log`.
    let a = analyze_units(
        "fn main() { log.info(\"x\") }",
        &[("log", "pub fn info(m: String) {}")],
    );
    assert_eq!(codes(&a), vec![(2, "W0107".to_string())]);
    assert!(
        a.diags[0].message.contains("`log`"),
        "{}",
        a.diags[0].message
    );
    // `Option` is a prelude item, and `Json` is a type of the root.
    for (root, dep) in [("fn main() {}", "Option"), ("struct Json {}", "Json")] {
        let a = analyze_units(root, &[(dep, "pub fn f() {}")]);
        assert_eq!(codes(&a), vec![(2, "W0107".to_string())], "{dep}");
    }
    // The root declares its functions after the dependency names, so the
    // error is at the function.
    let a = analyze_units("fn json() {}", &[("json", "pub fn f() {}")]);
    assert_eq!(codes(&a), vec![(1, "W0107".to_string())]);
    // Two items with one name are reported in their own unit.
    let a = analyze_units("fn main() {}", &[("dep", "fn f() {}\nfn f() {}")]);
    assert_eq!(codes(&a), vec![(2, "W0107".to_string())]);
}

#[test]
fn item_diagnostics_have_the_unit_of_the_item() {
    // Types are declared in the first pass, functions in the second pass.
    let dup = "struct S { v: u64 }\nstruct S { v: u64 }\neffect E { fn e() }\neffect E { fn e() }";
    let a = analyze_units(dup, &[("dep", dup)]);
    assert_eq!(
        codes(&a),
        vec![
            (1, "W0107".to_string()),
            (1, "W0107".to_string()),
            (2, "W0107".to_string()),
            (2, "W0107".to_string())
        ]
    );
}

#[test]
fn dependency_does_not_see_the_root() {
    let a = analyze_units(
        "fn helper() {}\nfn main() { dep.f() }",
        &[("dep", "pub fn f() { helper() }")],
    );
    assert_eq!(codes(&a), vec![(2, "W0101".to_string())]);
}

#[test]
fn dependency_rc_group_resolves_in_its_module() {
    let a = analyze_units(
        "fn main() {}",
        &[(
            "graph",
            "struct Node { v: u64 }\npub fn bump(a: Rc<Node>) / mut(Node) { a.v += 1 }",
        )],
    );
    assert_eq!(codes(&a), Vec::new());
}

#[test]
fn file_markers_set_options() {
    let none = Options::default();
    assert_eq!(Options::from_markers("fn f() {}"), none);
    let lib = Options::from_markers("// weft: library\nfn f() {}");
    assert!(lib.library && !lib.no_runtime);
    let both = Options::from_markers("// A comment.\n  // weft: no-runtime, library\n");
    assert!(both.library && both.no_runtime);
    // A marker must start a line comment; other text is not a marker.
    let text = Options::from_markers("fn f() { print(\"// weft: library\") }");
    assert_eq!(text, none);
    assert_eq!(Options::from_markers("// weft: libraries"), none);
    let src = "fn f() {}\n  // weft: lib,no-runtime  x\r\n// weft:\n";
    assert_eq!(
        crate::marker_words(src),
        vec![(21, "lib"), (25, "no-runtime"), (37, "x")]
    );
    assert_eq!(&src[25..35], "no-runtime");
}

/// Each function calls the next one; only the last one states `log`. The
/// callers come before their callees in the source.
fn call_chain(n: usize) -> String {
    let mut src = String::new();
    for i in 0..n {
        let _ = writeln!(src, "fn f{i}() {{ f{}() }}", i + 1);
    }
    let _ = writeln!(src, "fn f{n}() / log {{ log.info(\"x\") }}");
    src
}

/// `k` functions call each other in a cycle with `p` reference parameters. The
/// last one rotates the parameters and goes one level down. So each `mut`
/// place goes around the cycle once for each parameter and each level.
fn rotation(k: usize, p: usize) -> String {
    let params: Vec<String> = (0..p).map(|i| format!("x{i}: &N")).collect();
    let same: Vec<String> = (0..p).map(|i| format!("x{i}")).collect();
    let mut rotated: Vec<String> = (1..p).map(|i| format!("x{i}")).collect();
    rotated.push("&x0.a[0]".into());
    let mut src = String::from("struct N { v: u64, a: Vec<N> }\n");
    for i in 1..k {
        let _ = writeln!(
            src,
            "fn g{i}({}) {{ g{}({}) }}",
            params.join(", "),
            i + 1,
            same.join(", ")
        );
    }
    let _ = writeln!(
        src,
        "fn g{k}({}) {{ x0.v += 1\n g1({}) }}",
        params.join(", "),
        rotated.join(", ")
    );
    src
}

/// `walk` has `p` reference parameters. It lends `x0` to `f`, and then it calls
/// itself with the parameters turned by one and a place one level under `x0`.
/// So each lowering of `walk` adds a little to its `lent` part. `top` calls
/// `walk`, and `extra` more functions make the program larger.
fn lend_rotation(p: usize, extra: usize) -> String {
    let params: Vec<String> = (0..p).map(|i| format!("x{i}: &N")).collect();
    let mut rotated: Vec<String> = (1..p).map(|i| format!("x{i}")).collect();
    rotated.push("&x0.a[0]".into());
    let mut src = String::from("struct N { v: u64, a: Vec<N> }\n");
    let _ = writeln!(
        src,
        "fn walk(f: fn(&N), {}) {{ f(x0)\n walk(f, {}) }}",
        params.join(", "),
        rotated.join(", ")
    );
    let _ = writeln!(
        src,
        "fn top(n: &N) {{ walk(|y| y.v += 2, {}) }}",
        vec!["n"; p].join(", ")
    );
    for i in 0..extra {
        let _ = writeln!(src, "fn e{i}() {{}}");
    }
    src
}

fn sig_of<'a>(a: &'a Analysis, name: &str) -> &'a crate::FnSig {
    let i = a
        .program
        .fns
        .iter()
        .position(|f| f.name == name)
        .unwrap_or_else(|| panic!("no fn {name}"));
    &a.sigs[i]
}

#[test]
fn effect_inference_reaches_a_fixpoint() {
    let units = vec![prelude(), unit("", &call_chain(3))];
    let a = crate::analyze(&units, Options::default());
    assert_eq!(codes(&a), Vec::new());
    // Callees come first, so each function is lowered once. `f3` states its
    // effects, but it still infers the other parts of its signature.
    assert_eq!(a.lowerings, 4);
    for f in ["f0", "f1", "f2", "f3"] {
        assert!(sig_of(&a, f).effects.named.contains("Log"), "{f}");
    }
}

#[test]
fn effect_inference_time_is_linear_in_a_call_chain() {
    let n = 300;
    let units = vec![prelude(), unit("", &call_chain(n))];
    let a = crate::analyze(&units, Options::default());
    assert_eq!(codes(&a), Vec::new());
    assert_eq!(a.lowerings, n + 1);
    assert!(sig_of(&a, "f0").effects.named.contains("Log"));
}

#[test]
fn effect_inference_converges_when_places_go_around_a_cycle() {
    // The old bound of 10 rounds for each function stopped these too early.
    for (k, p) in [(1, 8), (4, 4), (8, 3)] {
        let units = vec![prelude(), unit("", &rotation(k, p))];
        let a = crate::analyze(&units, Options::default());
        assert_eq!(codes(&a), Vec::new(), "k={k} p={p}");
        // Each parameter gets the deepest place: 3 levels and `v`, or 4 levels.
        let muts = &sig_of(&a, "g1").effects.muts;
        for i in 0..p {
            assert!(
                muts.iter()
                    .any(|m| m.root == crate::program::SigRoot::Param(i) && m.steps.len() >= 7),
                "k={k} p={p} x{i}: {muts:?}"
            );
        }
    }
}

#[test]
fn effect_inference_that_does_not_converge_is_an_error() {
    let units = vec![prelude(), unit("", &rotation(1, 3))];
    // The row of `g1` grows more than twice.
    let a = crate::analyze_with_limit(&units, Options::default(), 2);
    assert_eq!(codes(&a), vec![(1, "W0706".to_string())]);
    assert!(
        a.diags[0].message.contains("`g1`"),
        "{}",
        a.diags[0].message
    );
    let a = crate::analyze_with_limit(&units, Options::default(), 100);
    assert_eq!(codes(&a), Vec::new());
}

#[test]
fn effect_inference_checks_the_fixpoint_at_the_end() {
    // The body of `a` reads the row of `c` but does not name `c`. The name graph
    // does not show the edge, so the last lowering finds the growth.
    let units = vec![prelude(), unit("", "fn a() {}\nfn c() { log.info(\"x\") }")];
    let (prog, _) = crate::program::Collector::collect(&units);
    let mut sigs: Vec<crate::FnSig> = prog.fns.iter().map(|f| f.sig.clone()).collect();
    let id = |name: &str| prog.fns.iter().position(|f| f.name == name).unwrap_or(0);
    let (a, c) = (id("a"), id("c"));
    let lower = |sigs: &[crate::FnSig], f: usize| {
        let mut l =
            crate::body::Lower::new(&prog, sigs, prog.fns[f].module, &prog.fns[f].path, false)
                .lower_fn(f);
        if f == a {
            l.effects = sigs[c].effects.clone();
        }
        l
    };
    let out = crate::infer::infer(&prog, &mut sigs, &[a, c], None, &lower);
    assert!(out.diags.is_empty());
    assert!(sigs[a].effects.named.contains("Log"));
    assert_eq!(out.lowered.len(), 2);
    // `a`, then `c`, then each again after the last lowering found `a` short.
    assert_eq!(out.lowerings, 4);
}

#[test]
fn a_function_that_states_its_effects_infers_its_other_parts() {
    // `apply` states its row, but its body still gives `w` to `f`.
    let src = "struct W { n: u64 }\nfn apply(f: fn(&W), w: &W) / mut(w) { f(w) }";
    let units = vec![prelude(), unit("", src)];
    let a = analyze(&units, Options::default());
    assert_eq!(codes(&a), Vec::new());
    let s = sig_of(&a, "apply");
    assert!(s.declared);
    assert_eq!(s.effects.muts.len(), 1);
    let lent = &s.effects.lent;
    assert_eq!(lent.len(), 1, "{lent:?}");
    assert_eq!((lent[0].param, lent[0].arg), (0, Some(0)));
}

#[test]
fn inferred_parts_that_do_not_become_stable_are_an_error() {
    // The lowering of `a` changes its `reaches` part each time, so the parts
    // never become stable. A row cannot do this, because a row only grows.
    let units = vec![prelude(), unit("", "fn a() {}")];
    let (prog, _) = crate::program::Collector::collect(&units);
    let mut sigs: Vec<crate::FnSig> = prog.fns.iter().map(|f| f.sig.clone()).collect();
    let a = prog.fns.iter().position(|f| f.name == "a").unwrap_or(0);
    let lower = |sigs: &[crate::FnSig], f: usize| {
        let mut l =
            crate::body::Lower::new(&prog, sigs, prog.fns[f].module, &prog.fns[f].path, false)
                .lower_fn(f);
        l.effects.reaches = !sigs[f].effects.reaches;
        l
    };
    let out = crate::infer::infer(&prog, &mut sigs, &[a], None, &lower);
    let found: Vec<&str> = out.diags.iter().map(|d| d.code.as_str()).collect();
    assert_eq!(found, vec!["W0704"]);
    assert!(
        out.diags[0].message.contains("`a`"),
        "{}",
        out.diags[0].message
    );
    // The bound stops the changes. The parts change at most once for each
    // lowering, and once more for each last lowering.
    assert!(
        out.lowerings <= crate::infer::parts_limit(1),
        "{}",
        out.lowerings
    );
}

#[test]
fn a_program_can_reach_the_parts_limit() {
    // In a program with two functions, the parts of `walk` can change 36
    // times. With 7 parameters, its `lent` part needs exactly 36 changes.
    assert_eq!(crate::infer::parts_limit(2), 36);
    let units = vec![prelude(), unit("", &lend_rotation(7, 0))];
    let a = analyze(&units, Options::default());
    assert_eq!(codes(&a), Vec::new());
    assert_eq!(sig_of(&a, "walk").effects.lent.len(), 36);
    // With 8 parameters, it needs 41 changes. So `walk` gets W0704.
    let units = vec![prelude(), unit("", &lend_rotation(8, 0))];
    let a = analyze(&units, Options::default());
    assert_eq!(codes(&a), vec![(1, "W0704".to_string())]);
    let m = &a.diags[0].message;
    assert!(
        m.contains("`walk`") && m.contains("after 36 changes"),
        "{m}"
    );
    // `walk` keeps the parts of its last change. `top` uses them and becomes
    // stable, so it does not get W0704. `walk` is lowered once for each
    // change and once for the change that the bound stops, then `top` once.
    assert_eq!(sig_of(&a, "walk").effects.lent.len(), 36);
    assert_eq!(a.lowerings, 37 + 1);
}

#[test]
fn the_parts_limit_grows_with_the_program() {
    // The same `walk` with 8 parameters, in a program with 102 functions. Its
    // `lent` part changes 41 times, so the bound of 236 changes does not stop it.
    let units = vec![prelude(), unit("", &lend_rotation(8, 100))];
    let a = analyze(&units, Options::default());
    assert_eq!(codes(&a), Vec::new());
    assert_eq!(sig_of(&a, "walk").effects.lent.len(), 41);
    // `walk` is lowered once for each change and once more. Each other
    // function is lowered once.
    assert_eq!(a.lowerings, 41 + 1 + 101);
}

#[test]
fn the_growth_limit_is_the_height_of_the_row_lattice() {
    let units = vec![prelude(), unit("", &rotation(1, 8))];
    let a = crate::analyze(&units, Options::default());
    let sig = sig_of(&a, "g1");
    let small = crate::infer::growth_limit(&a.program, sig, 2);
    // Each parameter and each `rc` group is a root of places of up to 8 steps.
    let roots = sig.params.len() + a.program.adts.len();
    assert!(small >= roots * 511, "{small}");
    assert!(crate::infer::growth_limit(&a.program, sig, 3) > small);
    // The limit does not overflow.
    assert!(crate::infer::growth_limit(&a.program, sig, usize::MAX) > small);
}

#[test]
fn a_row_only_grows() {
    use crate::infer::{covers, join};
    use crate::program::{EffectSig, SigPlace, SigRoot, SigStep};
    let field = |id| {
        SigStep::Step(
            weft_facts::Step {
                kind: weft_facts::StepKind::Field { id },
                unstable: false,
            },
            String::new(),
        )
    };
    let place = |root, steps: Vec<SigStep>| SigPlace {
        root: SigRoot::Param(root),
        steps,
        text: String::new(),
    };
    let a = EffectSig {
        muts: vec![place(0, vec![field(1)]), place(1, vec![field(0), field(0)])],
        named: ["Log".to_string()].into(),
        ..EffectSig::default()
    };
    let b = EffectSig {
        muts: vec![place(0, vec![field(1), field(0)]), place(1, vec![field(0)])],
        named: ["Net".to_string()].into(),
        ..EffectSig::default()
    };
    assert!(!covers(&a, &b) && !covers(&b, &a));
    let j = join(&a, &b);
    assert!(covers(&j, &a) && covers(&j, &b));
    // `x0.1` covers `x0.1.0`, and `x1.0` covers `x1.0.0`.
    assert_eq!(
        j.muts,
        vec![place(0, vec![field(1)]), place(1, vec![field(0)])]
    );
    assert_eq!(j.named.len(), 2);
}

fn root_diags(src: &str) -> Vec<(String, String)> {
    let units = vec![prelude(), unit("", src)];
    let a = analyze(&units, Options::default());
    a.diags
        .iter()
        .map(|d| (d.code.clone(), d.message.clone()))
        .collect()
}

const FFI: &str = "extern type Stmt\nextern fn open() -> *Stmt\nextern fn step(s: *Stmt) -> i32\n";

#[test]
fn raw_pointer_is_a_copy_value_of_its_own_type() {
    let ok = format!(
        "{FFI}fn f() -> i32 / blocking {{ let s = open()\n let t = s\n step(s) + step(t) }}"
    );
    assert_eq!(root_diags(&ok), Vec::new());
    let bad = format!("{FFI}fn g() -> i32 / blocking {{ open() }}");
    assert_eq!(
        root_diags(&bad),
        vec![(
            "W0102".to_string(),
            "type mismatch: expected `i32`, found `*Stmt`".to_string()
        )]
    );
    let units = vec![prelude(), unit("", FFI)];
    let a = analyze(&units, Options::default());
    let ptr = a.program.ptr.unwrap_or(usize::MAX);
    let def = &a.program.adts[ptr];
    assert!(def.copy && def.nonportable && !def.linear);
    assert!(a
        .program
        .lookup(a.program.root, crate::program::PTR_NAME)
        .is_none());
}

#[test]
fn raw_pointer_only_in_foreign_signatures_and_locals() {
    for item in [
        "fn f(s: *Stmt) {}",
        "fn f() -> (u32, *Stmt) { (1, open()) }",
        "struct S { p: Vec<*Stmt> }",
        "enum E { A(*Stmt) }",
        "effect E { fn op(p: *Stmt) }",
        "effect E { fn op() -> *Stmt }",
        "impl *Stmt { fn f(self) {} }",
        "fn f(g: fn(*Stmt)) {}",
    ] {
        let codes: Vec<String> = root_diags(&format!("{FFI}{item}"))
            .into_iter()
            .map(|(c, _)| c)
            .filter(|c| c == "W0116")
            .collect();
        assert_eq!(codes, vec!["W0116".to_string()], "{item}");
    }
    let local =
        format!("{FFI}fn f() / blocking {{ let v: Vec<*Stmt> = Vec.new()\n v.push(open()) }}");
    assert_eq!(root_diags(&local), Vec::new());
}

/// Returns the facts of the body of function `name`.
fn facts(src: &str, name: &str) -> FnFacts {
    let a = analyze_source(src, Options::default()).expect("the source parses");
    a.bodies
        .into_iter()
        .find(|b| b.facts.name == name)
        .map(|b| b.facts)
        .expect("the function exists")
}

fn var(f: &FnFacts, name: &str) -> VarId {
    let i = f
        .vars
        .iter()
        .position(|v| v.name == name)
        .expect("the variable exists");
    VarId(u32::try_from(i).unwrap())
}

fn place(f: &FnFacts, display: &str) -> PlaceId {
    let i = f
        .places
        .iter()
        .position(|p| p.display == display)
        .expect("the place exists");
    PlaceId(u32::try_from(i).unwrap())
}

#[test]
fn locals_and_by_value_parameters_own_their_roots() {
    let f = facts(
        "fn f(v: Vec<u64>, r: &Vec<u64>) { let w = Vec.new(); w.push(1) }",
        "f",
    );
    assert!(f.owner.contains(&(place(&f, "v"), var(&f, "v"))));
    assert!(f.owner.contains(&(place(&f, "w"), var(&f, "w"))));
    // The referent of a reference parameter has no owner in the function.
    let r = place(&f, "r");
    assert!(!f.owner.iter().any(|&(p, _)| p == r));
}

#[test]
fn a_reference_through_an_rc_handle_points_into_the_handle() {
    let f = facts(
        "struct C { items: Vec<u64> }
         fn f(a: Rc<C>) { let r = &a.items[0]; print(r) }",
        "f",
    );
    let r = var(&f, "r");
    assert!(f.points_into.contains(&(r, place(&f, "C.items[]"))));
    assert!(f.points_into.contains(&(r, place(&f, "a.*"))));
}

#[test]
fn a_block_value_into_a_block_local_is_held_across_the_end() {
    let f = facts(
        "fn f() { let r = { let v = Vec.new(); v.push(1); &v[0] }; print(r) }",
        "f",
    );
    let held = var(&f, "block value");
    let v = var(&f, "v");
    assert!(f.points_into.contains(&(held, place(&f, "v[]"))));
    let end = f
        .scope_end
        .iter()
        .find(|&&(x, _)| x == v)
        .map(|&(_, n)| n)
        .expect("v goes out of scope");
    let used = f
        .uses
        .iter()
        .find(|&&(x, _)| x == held)
        .map(|&(_, n)| n)
        .expect("the block value is used");
    assert!(f.cfg_edge.contains(&(end, used)));
}

#[test]
fn a_reference_used_as_a_value_reads_its_places() {
    let f = facts(
        "struct S { n: u64 } fn f(s: &S) -> u64 { let c = &s.n; c + 1 }",
        "f",
    );
    let n = place(&f, "s.n");
    assert!(f.reads_at.iter().any(|&(_, p)| p == n));
}

#[test]
fn a_compound_assignment_through_a_reference_mutates_its_places() {
    let f = facts(
        "struct S { n: u64 } fn f(s: &S) { let c = &s.n; c += 1 }",
        "f",
    );
    let n = place(&f, "s.n");
    assert!(f.mutates_at.iter().any(|&(_, p)| p == n));
    // `c` keeps its value: the assignment does not rebind it.
    let c = var(&f, "c");
    assert_eq!(f.rebound_at.iter().filter(|&&(v, _)| v == c).count(), 1);
}

#[test]
fn a_temporary_goes_out_of_scope_at_the_end_of_its_statement() {
    let f = facts(
        "fn mk() -> Vec<u64> { Vec.new() } fn f() { let r = &mk()[0]; print(r) }",
        "f",
    );
    let t = place(&f, "temporary");
    let (_, owner) = *f
        .owner
        .iter()
        .find(|&&(p, _)| p == t)
        .expect("the temporary has an owner");
    let end = f
        .scope_end
        .iter()
        .find(|&&(v, _)| v == owner)
        .map(|&(_, n)| n)
        .expect("the temporary goes out of scope");
    assert_eq!(f.node(end).label, "end of statement");
    let r = var(&f, "r");
    let used = f
        .uses
        .iter()
        .filter(|&&(v, _)| v == r)
        .map(|&(_, n)| n)
        .max()
        .expect("r is used");
    assert!(end < used);
}

#[test]
fn a_handler_clause_runs_at_each_operation_it_handles() {
    let f = facts(
        "effect Log { fn log(m: String) }
         fn take(v: Vec<u64>) {}
         fn f() {
             let v: Vec<u64> = Vec.new()
             handle Log { fn log(m) { let u = Vec.new(); take(v); resume(()) } } in log(\"x\")
         }",
        "f",
    );
    let log = f
        .nodes
        .iter()
        .position(|n| n.label == "log")
        .map(|i| weft_facts::NodeId(u32::try_from(i).unwrap()))
        .expect("the operation has a node");
    assert!(f.moved_at.contains(&(var(&f, "v"), log)));
    assert!(f.scope_end.contains(&(var(&f, "u"), log)));
}

#[test]
fn a_move_of_a_field_moves_a_part() {
    let f = facts(
        "struct P { a: Vec<u64>, b: Vec<u64> }
         fn take(v: Vec<u64>) {}
         fn f() { let p = P { a: Vec.new(), b: Vec.new() }; take(p.a); take(p) }",
        "f",
    );
    let a = place(&f, "p.a");
    let p = var(&f, "p");
    let (_, n) = *f
        .moved_part
        .iter()
        .find(|&&(m, _)| m == a)
        .expect("p.a moves");
    assert!(f.moved_at.contains(&(p, n)));
    // The move of the whole local is not a part move.
    assert_eq!(f.moved_part.len(), 1);
}

#[test]
fn a_loop_reads_the_elements_at_each_iteration() {
    let f = facts("fn f(v: &Vec<u64>) { for x in v[] { print(1) } }", "f");
    let elems = place(&f, "v[]");
    let header = f
        .nodes
        .iter()
        .position(|n| n.label == "for")
        .map(|i| weft_facts::NodeId(u32::try_from(i).unwrap()))
        .expect("the loop has a header");
    assert!(f.reads_at.contains(&(header, elems)));
}

#[test]
fn an_unknown_function_result_points_anywhere_inside_its_argument() {
    let f = facts(
        "struct E { hp: i32 } struct W { es: Vec<E> }
         fn f(g: fn(&W) -> &E, w: &W) { let r = g(w); print(r.hp) }",
        "f",
    );
    let any = place(&f, "w..");
    assert!(f.place(any).is_wildcard());
    assert!(f.points_into.contains(&(var(&f, "r"), any)));
}

#[test]
fn a_closure_refers_to_captured_values_that_are_not_plain_data() {
    let f = facts(
        "fn take(v: Vec<u64>) {}
         fn f() { let n: u64 = 1; let v: Vec<u64> = Vec.new(); let g = || { print(n); take(v) }; g() }",
        "f",
    );
    let g = var(&f, "{closure}");
    assert!(f.points_into.contains(&(g, place(&f, "v"))));
    assert!(!f.points_into.contains(&(g, place(&f, "n"))));
    // The move of `v` comes before the closure gets its value.
    let v = var(&f, "v");
    let (_, moved) = *f.moved_at.iter().find(|&&(x, _)| x == v).expect("v moves");
    let (_, bound) = *f
        .rebound_at
        .iter()
        .find(|&&(x, _)| x == g)
        .expect("g is bound");
    assert!(moved < bound);
}

#[test]
fn a_compound_assignment_to_a_reference_field_writes_its_place() {
    let f = facts(
        "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }
         fn f(fr: &Frame) / mut(fr.buf) { fr.cur += 1 }",
        "f",
    );
    let buf = place(&f, "fr.buf[]");
    assert!(f.mutates_at.iter().any(|&(_, p)| p == buf));
    let cur = place(&f, "fr.cur");
    assert!(!f.mutates_at.iter().any(|&(_, p)| p == cur));
}

/// Returns the node with label `label`.
fn node(f: &FnFacts, label: &str) -> weft_facts::NodeId {
    f.nodes
        .iter()
        .position(|n| n.label == label)
        .map(|i| weft_facts::NodeId(u32::try_from(i).unwrap()))
        .expect("the node exists")
}

/// Returns the signature of function `name`.
fn sig(src: &str, name: &str) -> crate::FnSig {
    let a = analyze_source(src, Options::default()).expect("the source parses");
    let i = a
        .program
        .fns
        .iter()
        .position(|f| f.name == name)
        .expect("the function exists");
    a.sigs[i].clone()
}

#[test]
fn a_perform_passes_its_reference_arguments_to_the_clause() {
    let f = facts(
        "effect Bump { fn bump(v: &Vec<u64>) }
         fn f() {
             let v: Vec<u64> = Vec.new()
             handle Bump { fn bump(x) { let e = &x[0]; x.push(1); print(e); resume(()) } } in bump(&v)
         }",
        "f",
    );
    let n = node(&f, "bump");
    let v = place(&f, "v");
    assert!(f.call_arg.contains(&(n, v, 0)));
    // The clause parameter has its own root. A mutation through it is a mutation
    // of the argument at the operation, and it needs no declaration.
    let x = place(&f, "x");
    assert_eq!(f.roots[f.place(x).root.index()].kind, RootKind::Arg);
    assert!(!f.param_rooted(x));
    assert!(f.points_into.contains(&(var(&f, "e"), place(&f, "x[]"))));
    assert!(f.mutates_at.contains(&(n, v)));
    assert!(f.call_mut.contains(&(n, v, 0)));
}

#[test]
fn an_operation_of_an_outer_handler_lends_its_arguments() {
    let f = facts(
        "effect Bump { fn bump(v: &Vec<u64>) }
         fn f(v: &Vec<u64>) / Bump { bump(v) }",
        "f",
    );
    assert!(f.lends_mut.contains(&(node(&f, "bump"), place(&f, "v"))));
    assert!(f.mutates_at.is_empty());
}

#[test]
fn a_closure_argument_passes_its_captures() {
    let f = facts(
        "struct E { hp: i32 } struct W { es: Vec<E> }
         fn run(g: fn(), w: &W) {}
         fn f(w: &W) { let r = &w.es[0]; run(|| print(r.hp), w) }",
        "f",
    );
    let n = node(&f, "run");
    assert!(f.call_arg.contains(&(n, place(&f, "w.es[]"), 800)));
    assert!(f.call_arg.contains(&(n, place(&f, "w"), 1)));
}

#[test]
fn a_call_of_a_function_parameter_lends_its_reference_arguments() {
    let f = facts("struct W { n: u64 } fn f(g: fn(&W), w: &W) { g(w) }", "f");
    assert!(f.lends_mut.contains(&(node(&f, "g"), place(&f, "w"))));
    assert!(f.may_abort.contains(&node(&f, "g")));
}

#[test]
fn a_closure_parameter_root_needs_no_declaration() {
    let f = facts(
        "struct W { n: u64 } fn f(w: &W) / mut(w.n) { let h = |x: &W| x.n += 1; h(w) }",
        "f",
    );
    let xn = place(&f, "x.n");
    assert!(!f.param_rooted(xn));
    // The call mutates the argument instead.
    assert!(f.mutates_at.contains(&(node(&f, "h"), place(&f, "w.n"))));
}

#[test]
fn a_signature_states_what_the_body_lends_to_its_function_parameters() {
    let s = sig(
        "struct W { n: u64 } fn apply(f: fn(&W), w: &W) { f(w) }",
        "apply",
    );
    let lp = &s.effects.lent;
    assert_eq!(lp.len(), 1, "{lp:?}");
    assert_eq!((lp[0].param, lp[0].arg), (0, Some(0)));
    let place = lp[0].place.as_ref().expect("the caller can name the place");
    assert_eq!(place.root, crate::program::SigRoot::Param(1));
    assert!(place.steps.is_empty());
}

#[test]
fn a_signature_states_what_a_returned_closure_does() {
    let s = sig(
        "struct W { n: u64 } fn mk(w: &W) -> fn() { || { w.n += 1; log.info(\"x\") } }",
        "mk",
    );
    // The maker has the effects of the closure.
    assert!(s.effects.named.contains("Log"));
    assert_eq!(s.effects.muts.len(), 1);
    let ret = s.effects.ret.expect("the returned closure has a summary");
    assert!(ret.named.contains("Log"));
    assert_eq!(ret.muts.len(), 1);
    assert_eq!(ret.muts[0].text, "w.n");
    assert!(ret.abort);
}

#[test]
fn a_signature_states_what_a_returned_closure_lends() {
    // The returned closure gives `w` to the function parameter `g`.
    let s = sig(
        "struct W { n: u64 } fn mk(g: fn(&W), w: &W) -> fn() { || g(w) }",
        "mk",
    );
    let ret = s.effects.ret.expect("the returned closure has a summary");
    assert_eq!(ret.lends.len(), 1);
    assert_eq!(ret.lends[0].text, "w");
    assert!(ret.passthrough.contains(&0));
    // The result of a call of a function parameter lends what the call gives.
    let s = sig(
        "struct W { n: u64 } fn call(m: fn(&W) -> fn(), w: &W) -> fn() { m(w) }",
        "call",
    );
    let ret = s.effects.ret.expect("the returned value has a summary");
    assert!(ret.unknown);
    assert_eq!(ret.lends.len(), 1);
    assert_eq!(ret.lends[0].text, "w");
}

#[test]
fn a_closure_has_the_effects_of_the_closure_that_it_returns() {
    let f = facts(
        "struct W { n: Vec<u64> }
         fn ap(f: fn() -> fn()) { let g = f(); g() }
         fn caller(w: &W) { ap(|| || w.n.clear()) }",
        "caller",
    );
    // The call of `ap` runs the inner closure.
    let n = place(&f, "w.n");
    assert!(f
        .mutates_at
        .iter()
        .any(|&(at, m)| m == n && f.node(at).label == "ap"));
}

#[test]
fn a_signature_states_what_a_body_gives_a_stored_value() {
    let src = "struct W { n: u64 } struct H { f: fn(&W) }
         fn dispatch(h: &H, w: &W) { let f = h.f; f(w) }
         fn count(h: &H, w: &W) -> u64 { w.n }";
    let s = sig(src, "dispatch");
    assert!(s.effects.reaches);
    assert_eq!(s.effects.reach_given.len(), 1);
    assert_eq!(s.effects.reach_given[0].arg, Some(0));
    let place = s.effects.reach_given[0]
        .place
        .as_ref()
        .expect("a named place");
    assert_eq!(place.text, "w");
    // A body that calls no unknown function value cannot run a stored one.
    assert!(!sig(src, "count").effects.reaches);
}

#[test]
fn effect_inference_runs_until_the_signatures_are_stable() {
    // A chain of 40 functions, each defined before the one that it calls.
    let mut src = String::from(
        "struct E { hp: i32 } struct W { es: Vec<E> }
         fn top(w: &W) { ap40(|x| x.es.clear(), w) }\n",
    );
    for i in (1..=40).rev() {
        let _ = writeln!(src, "fn ap{i}(f: fn(&W), w: &W) {{ ap{}(f, w) }}", i - 1);
    }
    src.push_str("fn ap0(f: fn(&W), w: &W) { f(w) }\n");
    let a = analyze_source(&src, Options::default()).expect("the source parses");
    // The old loop needed more than 32 rounds for this chain. The worklist puts
    // callees first, so it lowers each of the 42 functions once.
    assert_eq!(a.lowerings, 42);
    assert!(a
        .diags
        .iter()
        .all(|d| d.code != "W0704" && d.code != "W0706"));
    let f = facts(&src, "top");
    // The closure mutates what the chain gives it, at the call of `ap40`.
    let es = place(&f, "w.es");
    assert!(f
        .mutates_at
        .iter()
        .any(|&(at, m)| m == es && f.node(at).label == "ap40"));
}

#[test]
fn fip_use_counts_do_not_overflow_in_nested_loops() {
    // Each loop repeats the uses of `x`. 64 loops give 2^64 uses, which a
    // `usize` cannot hold. The count stops at two, so `x` is used more than
    // once.
    let mut src = String::from("fip fn g(x: Vec<u32>) -> Vec<u32> { ");
    src.push_str(&"while true { ".repeat(64));
    src.push_str("g(x) ");
    src.push_str(&"} ".repeat(64));
    src.push_str("\n x }");
    let a = analyze_source(&src, Options::default()).expect("the source parses");
    let d = a
        .diags
        .iter()
        .find(|d| d.code == "W1002")
        .unwrap_or_else(|| panic!("no W1002: {:?}", codes(&a)));
    assert!(d.message.contains("found 1 to 2 or more"), "{}", d.message);
}

#[test]
fn the_prelude_parses_and_has_no_diagnostics() {
    let p = prelude();
    assert!(p.is_std);
    assert!(!p.file.items.is_empty());
    let a = analyze_units("", &[]);
    assert_eq!(codes(&a), Vec::new());
    assert_eq!(a.program.mods[a.program.root].unit, ROOT_UNIT);
    assert_eq!(a.program.mods[crate::program::PRELUDE].unit, PRELUDE_UNIT);
}

/// The W1002 messages of a program.
fn w1002(src: &str) -> Vec<String> {
    root_diags(src)
        .into_iter()
        .filter(|(code, _)| code == "W1002")
        .map(|(_, message)| message)
        .collect()
}

#[test]
fn fip_use_counts_stop_at_two() {
    // A use in a loop body counts as two or more. Deep loops do not overflow.
    for depth in [1, 3, 64] {
        let src = format!(
            "fip fn g(x: Vec<u32>) -> Vec<u32> {{ {}let y = x{}\n x }}\n",
            "while true { ".repeat(depth),
            " }".repeat(depth)
        );
        assert_eq!(
            w1002(&src),
            ["`fip` needs `x` used exactly once on every path (found 1 to 2 or more)"],
            "{depth} loops"
        );
    }
    let src = "fip fn g(x: Vec<u32>) -> Vec<u32> { if true { x } else { Vec.new() } }\n";
    assert_eq!(
        w1002(src),
        ["`fip` needs `x` used exactly once on every path (found 0 to 1)"]
    );
    let src = "enum L { C(L), N }\nfip fn g(x: L) -> L { N }\n";
    assert_eq!(
        w1002(src),
        ["`fip` needs `x` used exactly once on every path (found 0)"]
    );
}

#[test]
fn fip_return_ends_a_path() {
    let src =
        "enum L { C(L), N }\nfip fn g(x: L, f: bool) -> L {\n    if f { return x }\n    x\n}\n";
    assert_eq!(w1002(src), Vec::<String>::new());
    // A use before the return counts on that path.
    let src = "enum L { C(L), N }\nfip fn g(x: L, f: bool) -> L {\n    if f { let y = x\n return x }\n    x\n}\n";
    assert_eq!(
        w1002(src),
        ["`fip` needs `x` used exactly once on every path (found 1 to 2 or more)"]
    );
    // A return in a match arm.
    let src = "enum L { C(L), N }\nfip fn g(x: L, y: L) -> L {\n    match y {\n        C(t) => { return C(t) }\n        N => {}\n    }\n    x\n}\n";
    assert_eq!(
        w1002(src),
        ["`fip` needs `x` used exactly once on every path (found 0 to 1)"]
    );
    // A loop body that returns runs at most once.
    let src =
        "enum L { C(L), N }\nfip fn g(x: L, f: bool) -> L {\n    while f { return x }\n    x\n}\n";
    assert_eq!(w1002(src), Vec::<String>::new());
}

#[test]
fn item_checks_report_in_the_unit_of_the_item() {
    let dep = "struct A { a: A }\nstruct D { x: u64, x: u64 }\nlinear struct L { id: u64 }\n    on abort = gone\nfn modes(x: &u64 @ once many) {}\n";
    let a = analyze_units("fn main() {}", &[("dep", dep)]);
    let mut got = codes(&a);
    got.sort();
    let want: Vec<(usize, String)> = ["W0101", "W0107", "W0117", "W0119"]
        .iter()
        .map(|c| (2, (*c).to_string()))
        .collect();
    assert_eq!(got, want);
}

/// `n` structs in a chain: `A0` holds `A1` inline, and so on. The last one
/// holds a number. `reverse` declares the last struct first.
fn struct_chain(n: usize, reverse: bool) -> String {
    let mut items: Vec<String> = (0..n)
        .map(|i| format!("struct A{i} {{ a: A{} }}\n", i + 1))
        .collect();
    items.push(format!("struct A{n} {{ x: u64 }}\n"));
    if reverse {
        items.reverse();
    }
    items.concat()
}

/// `n` generic structs in a chain that hold their parameter inline at the
/// end, and a struct `Top` that holds itself through the chain.
fn generic_chain(n: usize) -> String {
    let mut items = vec!["struct Top { g: G0<Top> }\n".to_string()];
    items.extend((0..n).map(|i| format!("struct G{i}<T> {{ g: G{}<T> }}\n", i + 1)));
    items.push(format!("struct G{n}<T> {{ t: T }}\n"));
    items.concat()
}

#[test]
fn the_size_check_is_fast_on_a_long_chain() {
    use std::time::{Duration, Instant};
    let n = 3000;
    for (src, want) in [
        (struct_chain(n, false), Vec::new()),
        (struct_chain(n, true), Vec::new()),
        (generic_chain(n), vec![(ROOT_UNIT, "W0117".to_string())]),
    ] {
        let start = Instant::now();
        let a = analyze_units(&src, &[]);
        let time = start.elapsed();
        assert_eq!(codes(&a), want);
        // About 0.06 s in a debug build. The first check took 150 s for
        // 800 structs.
        assert!(time < Duration::from_secs(2), "{time:?}");
    }
    let a = analyze_units(&generic_chain(3), &[]);
    let top = a.program.lookup(a.program.root, "Top");
    assert!(
        matches!(top, Some(crate::program::ItemRef::Adt(t)) if crate::program::infinite_structs(&a.program) == [t])
    );
}

#[test]
fn the_in_place_check_is_fast_on_a_long_chain() {
    use std::time::{Duration, Instant};
    let n = 3000;
    let params: Vec<String> = (0..n)
        .map(|i| format!("x{i}: &u32 in x{}", i + 1))
        .collect();
    let src = format!("fn f({}, x{n}: &u32) {{}}\n", params.join(", "));
    let start = Instant::now();
    let a = analyze_units(&src, &[]);
    let time = start.elapsed();
    assert_eq!(codes(&a), Vec::new());
    assert!(time < Duration::from_secs(2), "{time:?}");
    // The chain closes into a cycle: one error, at its first parameter.
    let src = format!("fn f({}, x{n}: &u32 in x0) {{}}\n", params.join(", "));
    assert_eq!(
        codes(&analyze_units(&src, &[])),
        vec![(ROOT_UNIT, "W0201".to_string())]
    );
}

#[test]
fn the_mode_check_is_fast_on_a_long_list() {
    use std::time::{Duration, Instant};
    let src = format!("fn f(x: &u32 @{}) {{}}\n", " uniq".repeat(100_000));
    let start = Instant::now();
    let a = analyze_units(&src, &[]);
    let time = start.elapsed();
    assert_eq!(codes(&a), Vec::new());
    assert!(time < Duration::from_secs(2), "{time:?}");
    let src = format!("fn f(x: &u32 @{} shared) {{}}\n", " uniq".repeat(100_000));
    assert_eq!(
        root_diags(&src),
        vec![(
            "W0119".to_string(),
            "modes `uniq` and `shared` contradict: other threads can read a `shared` value, so it is not `uniq`".to_string()
        )]
    );
}

#[test]
fn fip_counts_the_right_operand_of_and_and_or_on_one_path_only() {
    let h = "fip fn h(xs: Vec<u32>) -> bool { let n = xs\n true }\n";
    for op in ["&&", "||"] {
        let src = format!("{h}fip fn g(xs: Vec<u32>, c: bool) -> bool {{ c {op} h(xs) }}\n");
        assert_eq!(
            w1002(&src),
            ["`fip` needs `xs` used exactly once on every path (found 0 to 1)"],
            "{op}"
        );
    }
    let src = format!("{h}fip fn g(xs: Vec<u32>, c: bool) -> bool {{ h(xs) && c }}\n");
    assert_eq!(w1002(&src), Vec::<String>::new());
}

#[test]
fn fip_loop_paths_leave_only_by_break_or_return() {
    let ok = [
        // A `loop` with no `break` does not go on after it.
        "fip fn g(xs: Vec<u32>) -> Vec<u32> { loop { return xs } }\n",
        "fip fn g(xs: Vec<u32>, c: bool) -> Vec<u32> { loop { if c { return xs } } }\n",
        "fip fn g(xs: Vec<u32>, c: bool) -> Vec<u32> { loop { if c { break }\n return xs }\n xs }\n",
        // A `continue` skips the rest of the body.
        "fip fn g(xs: Vec<u32>, c: bool) -> Vec<u32> { while c { if c { continue }\n return xs }\n xs }\n",
    ];
    for src in ok {
        assert_eq!(w1002(src), Vec::<String>::new(), "{src}");
    }
    let src = "fip fn g(xs: Vec<u32>, c: bool) -> Vec<u32> { loop { let y = xs\n break }\n xs }\n";
    assert_eq!(
        w1002(src),
        ["`fip` needs `xs` used exactly once on every path (found 2 or more)"]
    );
    // A `break` in an inner loop leaves only the inner loop.
    let src = "fip fn g(xs: Vec<u32>) -> Vec<u32> { loop { loop { break }\n return xs } }\n";
    assert_eq!(w1002(src), Vec::<String>::new());
}

#[test]
fn a_match_too_large_to_check_is_an_error() {
    // Each of the 256 values has its own arm. The check needs more steps than
    // its budget (500 in a test build). So it cannot show that the arms cover
    // each value.
    let n = 8;
    let cols: Vec<String> = (0..n).map(|i| format!("b{i}: bool")).collect();
    let args: Vec<String> = (0..n).map(|i| format!("b{i}")).collect();
    let mut arms = String::new();
    for k in 0..(1u32 << n) {
        let pat: Vec<&str> = (0..n)
            .map(|i| if k >> i & 1 == 1 { "true" } else { "false" })
            .collect();
        let _ = writeln!(arms, "        ({}) => {k},", pat.join(", "));
    }
    let src = format!(
        "fn g({}) -> u32 {{\n    match ({}) {{\n{arms}    }}\n}}\n",
        cols.join(", "),
        args.join(", ")
    );
    let a = analyze_source(&src, Options::default()).unwrap();
    let w: Vec<&str> = a
        .diags
        .iter()
        .filter(|d| d.code == "W0120")
        .map(|d| d.message.as_str())
        .collect();
    assert_eq!(w.len(), 1, "{:?}", a.diags);
    assert!(w[0].contains("too large to check"), "{}", w[0]);
}

#[test]
fn a_small_match_is_checked_in_full() {
    let src = "fn g(a: bool, b: bool) -> u32 {\n    match (a, b) {\n        (true, _) => 0,\n        (_, true) => 1,\n        (false, false) => 2,\n    }\n}\n";
    let a = analyze_source(src, Options::default()).unwrap();
    assert!(a.diags.is_empty(), "{:?}", a.diags);
}

#[test]
fn many_locals_and_part_values_are_fast() {
    // A body with many locals, and many new values of one part of a local. The
    // lowering looks a local up by its variable, and each new value of the
    // part replaces the old one, so the cost grows linearly.
    let mut body = String::from("    let w = Wrap { x: &v[0] }\n");
    for i in 0..12_000 {
        let _ = writeln!(body, "    let x{i} = {i}");
    }
    for _ in 0..2_000 {
        body.push_str("    w.x = &v[0]\n    print(w.x)\n");
    }
    let src = format!("struct Wrap<T> {{ x: T }}\nfn f(v: &Vec<u64>) {{\n{body}}}\n");
    let start = std::time::Instant::now();
    let a = analyze_source(&src, Options::default()).unwrap();
    assert!(a.diags.is_empty(), "{:?}", a.diags);
    let f = a.bodies.iter().find(|b| b.facts.name == "f").unwrap();
    let holders = f
        .facts
        .vars
        .iter()
        .filter(|v| v.name.starts_with("value in"))
        .count();
    assert_eq!(holders, 1);
    assert!(start.elapsed().as_secs() < 10, "{:?}", start.elapsed());
}

/// A loop with a chain of `n` reference locals. The last one gets a place in
/// `w`, and each iteration moves the places one local down the chain.
fn ref_chain(n: usize) -> String {
    let mut s = String::from("struct E { hp: i32 }\nfn f(d: &Vec<i32>, w: &Vec<E>) {\n");
    for i in 0..n {
        let _ = writeln!(s, "    let r{i} = &d[0]");
    }
    s.push_str("    let m = 0\n    while m < 3 {\n");
    for i in 0..n - 1 {
        let _ = writeln!(s, "        r{i} = r{}", i + 1);
    }
    let _ = writeln!(
        s,
        "        r{} = &w[0].hp\n        m += 1\n    }}\n    print(r0)\n}}",
        n - 1
    );
    s
}

/// Returns the displays of the places that local `name` of `f` points into.
fn points_of(a: &Analysis, name: &str) -> Vec<String> {
    let f = a.bodies.iter().find(|b| b.facts.name == "f").unwrap();
    let mut out: Vec<String> = f
        .facts
        .points_into
        .iter()
        .filter(|(v, _)| f.facts.var(*v).name == name)
        .map(|&(_, p)| {
            let info = f.facts.place(p);
            let wild = if info.is_wildcard() {
                " (wildcard)"
            } else {
                ""
            };
            format!("{}{wild}", info.display)
        })
        .collect();
    out.sort();
    out.dedup();
    out
}

#[test]
fn a_loop_chain_iterates_until_the_values_are_stable() {
    // A chain of n locals needs one pass for each local, and one more pass that
    // shows that the values are stable. The old lowering stopped after 8 passes.
    for n in [3, 10, 30] {
        let a = analyze_units(&ref_chain(n), &[]);
        assert_eq!(codes(&a), Vec::new(), "n={n}");
        assert_eq!(a.work.loop_passes, n + 1, "n={n}");
        assert!(
            points_of(&a, "r0").contains(&"w[].hp".to_string()),
            "n={n}: {:?}",
            points_of(&a, "r0")
        );
    }
}

#[test]
fn a_reference_that_goes_deeper_becomes_a_wildcard_place() {
    // Each iteration goes one level deeper. After the widening, a new place
    // below a place at the head becomes the wildcard place of that place, so
    // the loop stops.
    let src = "struct Node { val: u64, next: Vec<Node> }
fn f(head: &Node, n: u64) -> u64 {
    let cur = head
    let i = 0
    while i < n {
        cur = &cur.next[0]
        i += 1
    }
    cur.val
}
";
    let a = analyze_units(src, &[]);
    assert_eq!(codes(&a), Vec::new());
    let widen = crate::body::loops::LOOP_WIDEN_AFTER;
    assert!(a.work.loop_passes <= widen + 2, "{}", a.work.loop_passes);
    let deep = format!("head{}.. (wildcard)", ".next[]".repeat(widen - 1));
    assert!(
        points_of(&a, "cur").contains(&deep),
        "{:?}",
        points_of(&a, "cur")
    );
}

#[test]
fn a_loop_that_is_not_stable_at_the_bound_is_an_error() {
    let units = vec![prelude(), unit("", &ref_chain(10))];
    let a = crate::analyze_with_loop_bound(&units, Options::default(), 4);
    assert_eq!(codes(&a), vec![(ROOT_UNIT, "W0707".to_string())]);
    assert!(
        a.diags[0].message.contains("4 passes"),
        "{}",
        a.diags[0].message
    );
    let a = crate::analyze_with_loop_bound(&units, Options::default(), 11);
    assert_eq!(codes(&a), Vec::new());
}

#[test]
fn task_handles_that_a_loop_swaps_join_each_task() {
    // After the loop each handle can hold each task, so each `join` joins both.
    let src = "fn f() / async {
    scope { s =>
        let t0 = s.spawn(|| print(1))
        let t1 = s.spawn(|| print(2))
        let m = 0
        while m < 3 {
            let x = t0
            t0 = t1
            t1 = x
            m += 1
        }
        t0.join()
        t1.join()
    }
}
";
    let a = analyze_units(src, &[]);
    assert_eq!(codes(&a), Vec::new());
    let f = a.bodies.iter().find(|b| b.facts.name == "f").unwrap();
    for t in 0..2 {
        let joins = f
            .facts
            .joined_at
            .iter()
            .filter(|(x, _)| x.index() == t)
            .count();
        assert!(joins >= 2, "task {t}: {:?}", f.facts.joined_at);
    }
}

/// `n` loops one after the other, each with a new local and a counter.
fn seq_loops(n: usize) -> String {
    let mut s = String::from("fn f(n: u64) {\n    let s: u64 = 0\n");
    for i in 0..n {
        let _ = writeln!(
            s,
            "    let i{i}: u64 = 0\n    while i{i} < n {{ s += 1\n        i{i} += 1 }}"
        );
    }
    s.push_str("    print(s)\n}\n");
    s
}

#[test]
fn loops_one_after_the_other_cost_linear_work() {
    // Each pass copied the whole lowering state, so a function with many loops
    // was quadratic (QA7: 2000 loops took 5.7 s). A pass now copies the state
    // of the head only, and a rewind puts back the locals that the pass changed.
    let small = analyze_units(&seq_loops(500), &[]);
    let large = analyze_units(&seq_loops(1000), &[]);
    assert_eq!(codes(&large), Vec::new());
    assert_eq!(small.work.loop_passes, 500);
    assert_eq!(large.work.loop_passes, 1000);
    let (a, b) = (small.work.loop_copies, large.work.loop_copies);
    assert!(b <= 2 * a + 100, "500 loops: {a}, 1000 loops: {b}");
    assert!(b <= 20 * 1000, "{b}");
}

#[test]
fn a_grow_set_cuts_back_to_a_mark() {
    let mut g: crate::body::Grow<u32> = [3, 1].into_iter().collect();
    let mark = g.mark();
    assert!(g.insert(2));
    assert!(!g.insert(1));
    g.extend([5, 4]);
    assert_eq!(g.iter().copied().collect::<Vec<_>>(), vec![1, 2, 3, 4, 5]);
    g.cut(mark);
    assert_eq!(g.iter().copied().collect::<Vec<_>>(), vec![1, 3]);
    assert!(!g.contains(&2) && g.contains(&3));
    let empty = crate::body::Grow::<u32>::default();
    assert!(empty.is_empty() && empty.mark() == 0 && empty == crate::body::Grow::default());
}

/// One untyped integer local, updated `n` times.
fn int_updates(n: usize) -> String {
    format!(
        "fn f() {{\n    let s = 0\n{}    print(s)\n}}\n",
        "    s += 1\n".repeat(n)
    )
}

#[test]
fn integer_variables_unify_in_linear_work() {
    // Each `s += 1` bound the end of the variable chain of `s` to the variable
    // of the new literal, and each lookup walked the whole chain (QA8: 16000
    // updates took 10.9 s). Union by rank keeps the chains short.
    let small = analyze_units(&int_updates(1000), &[]);
    let large = analyze_units(&int_updates(2000), &[]);
    assert_eq!(codes(&large), Vec::new());
    let (a, b) = (small.work.type_steps, large.work.type_steps);
    assert!(b <= 2 * a + 1000, "1000 updates: {a}, 2000 updates: {b}");
    assert!(b <= 40 * 2000, "{b}");
}
