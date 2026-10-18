//! Tests for semantic analysis.

use weft_syntax::parse_file;

use crate::{analyze, prelude_unit, Analysis, Options, Unit, PRELUDE_UNIT, ROOT_UNIT};

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
    use std::fmt::Write as _;
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
    use std::fmt::Write as _;
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
    // Callees come first, so each function is lowered once.
    assert_eq!(a.lowerings, 3);
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
    assert_eq!(a.lowerings, n);
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
