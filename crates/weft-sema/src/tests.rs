//! Tests for semantic analysis.

use weft_syntax::parse_file;

use crate::{analyze, prelude_unit, Analysis, Options, Unit};

fn unit(name: &str, src: &str) -> Unit {
    Unit {
        name: name.into(),
        file: parse_file(src).unwrap_or_default(),
        is_std: false,
    }
}

/// Analyzes a root unit and dependency units `(name, source)`.
fn analyze_units(root: &str, deps: &[(&str, &str)]) -> Analysis {
    let mut units = vec![prelude_unit(), unit("", root)];
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
    let or = lib.or(Options {
        library: false,
        no_runtime: true,
    });
    assert!(or.library && or.no_runtime);
}

/// Each function calls the next one; only the last one states `log`. In source
/// order, one round moves the effect one call back.
fn call_chain(n: usize) -> String {
    use std::fmt::Write as _;
    let mut src = String::new();
    for i in 0..n {
        let _ = writeln!(src, "fn f{i}() {{ f{}() }}", i + 1);
    }
    let _ = writeln!(src, "fn f{n}() / log {{ log.info(\"x\") }}");
    src
}

#[test]
fn effect_inference_reaches_a_fixpoint() {
    let units = vec![prelude_unit(), unit("", &call_chain(3))];
    let a = crate::analyze(&units, Options::default());
    assert_eq!(codes(&a), Vec::new());
    assert_eq!(a.rounds, 4);
    assert!(
        a.sigs
            .iter()
            .filter(|s| s.effects.named.contains("Log"))
            .count()
            >= 4
    );
}

#[test]
fn effect_inference_that_does_not_converge_is_an_error() {
    let units = vec![prelude_unit(), unit("", &call_chain(3))];
    let a = crate::analyze_with_limit(&units, Options::default(), 2);
    assert_eq!(a.rounds, 2);
    // After two rounds, `f0` does not have `log` yet.
    assert_eq!(codes(&a), vec![(1, "W0706".to_string())]);
    assert!(
        a.diags[0].message.contains("`f0`"),
        "{}",
        a.diags[0].message
    );
    // The last allowed round may be the one that finds no change.
    let a = crate::analyze_with_limit(&units, Options::default(), 4);
    assert_eq!(codes(&a), Vec::new());
}

#[test]
fn the_round_limit_grows_with_the_program() {
    assert!(crate::round_limit(0) >= 2);
    assert!(crate::round_limit(100) > crate::round_limit(10));
    // A long call chain converges: one round per call is in the limit.
    let n = 40;
    let units = vec![prelude_unit(), unit("", &call_chain(n))];
    let a = crate::analyze(&units, Options::default());
    assert_eq!(codes(&a), Vec::new());
    assert_eq!(a.rounds, n + 1);
}

fn root_diags(src: &str) -> Vec<(String, String)> {
    let units = vec![prelude_unit(), unit("", src)];
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
    let units = vec![prelude_unit(), unit("", FFI)];
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
