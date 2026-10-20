//! Tests of names and effects across the units of a package.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use weft_cli::run;

fn cmd(args: &[&str]) -> weft_cli::Output {
    let args: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
    run(&args).expect("command runs")
}

/// Writes `files` into a new directory for one test, and returns its path.
fn scratch(name: &str, files: &[(&str, &str)]) -> String {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("units")
        .join(name);
    let _ = std::fs::remove_dir_all(&dir);
    for (path, text) in files {
        let p = dir.join(path);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    }
    dir.display().to_string()
}

const MANIFEST: &str =
    "[package]\nname = \"app\"\n\n[dependencies.json]\npath = \"deps/json\"\nauthority = []\n";

const LIB: &str = "pub fn parse(text: String) -> u64 { size(text) }\n\
fn size(text: String) -> u64 { 3 }\n\
pub struct Doc { n: u64 }\n\
impl Doc {\n    pub fn len(self) -> u64 { self.n }\n    fn secret(self) -> u64 { self.n }\n}\n\
pub fn doc() -> Doc { Doc { n: 1 } }\n";

#[test]
fn the_project_cannot_name_a_private_function_of_a_dependency() {
    let pkg = scratch(
        "private_call",
        &[
            ("weft.toml", MANIFEST),
            (
                "src/main.wf",
                "fn main() {\n    print(json.size(\"x\"))\n    let f = json.size\n    let d = json.doc()\n    print(d.secret())\n}\n",
            ),
            ("deps/json/src/lib.wf", LIB),
        ],
    );
    let out = cmd(&["check", &pkg]);
    assert_eq!(out.code, 1, "{}", out.text);
    let private = out
        .text
        .lines()
        .filter(|l| l.starts_with("error[W0101]") && l.contains("is private"))
        .count();
    assert_eq!(private, 3, "{}", out.text);
    assert!(
        out.text
            .contains("error[W0101]: `size` is private: it is not `pub` in its package"),
        "{}",
        out.text
    );
}

#[test]
fn the_project_can_name_a_public_function_of_a_dependency() {
    let pkg = scratch(
        "public_call",
        &[
            ("weft.toml", MANIFEST),
            (
                "src/main.wf",
                "fn main() {\n    print(json.parse(\"x\"))\n    let f = json.parse\n    let d = json.doc()\n    print(d.len())\n}\n",
            ),
            ("deps/json/src/lib.wf", LIB),
        ],
    );
    let out = cmd(&["check", &pkg]);
    assert_eq!(out.code, 0, "{}", out.text);
}

#[test]
fn a_user_effect_of_a_dependency_needs_no_authority() {
    // The dependency defines its own `Log`. It is not the standard `log`.
    let pkg = scratch(
        "user_effect_authority",
        &[
            ("weft.toml", MANIFEST),
            ("src/main.wf", "fn main() {\n    print(1)\n}\n"),
            (
                "deps/json/src/lib.wf",
                "effect Log { fn log(msg: String) }\n\
pub fn quiet() / Log { log(\"x\") }\n\
pub fn loud() / log { log.info(\"x\") }\n",
            ),
        ],
    );
    let out = cmd(&["deps", &pkg]);
    assert_eq!(out.code, 1, "{}", out.text);
    assert!(
        out.text
            .contains("error[W0901]: dependency `json` function `loud` needs `log`"),
        "{}",
        out.text
    );
    assert!(!out.text.contains("function `quiet` needs"), "{}", out.text);
}

const NOTE_LIB: &str = "pub effect Note { fn note(x: u64) }\n\
effect Secret { fn secret(x: u64) }\n\
pub fn noting() / Note { note(1) }\n\
pub fn hiding() / Secret { secret(2) }\n";

#[test]
fn the_project_names_a_public_effect_of_a_dependency_with_a_path() {
    // ADR 0005: `handle util.Note` and the row `/ util.Note`.
    let pkg = scratch(
        "effect_path",
        &[
            ("weft.toml", MANIFEST),
            (
                "src/main.wf",
                "fn main() {\n    handle json.Note { fn note(x) {\n        print(x)\n        resume(())\n    } } in again()\n}\nfn again() / json.Note {\n    json.noting()\n    json.Note.note(3)\n}\n",
            ),
            ("deps/json/src/lib.wf", NOTE_LIB),
        ],
    );
    let out = cmd(&["check", &pkg]);
    assert_eq!(out.code, 0, "{}", out.text);
    let out = cmd(&["run", &pkg]);
    assert_eq!(out.code, 0, "{}", out.text);
    assert_eq!(out.text, "1\n3\n");
}

#[test]
fn the_hints_name_an_effect_of_a_dependency_as_the_project_writes_it() {
    let pkg = scratch(
        "effect_hints",
        &[
            ("weft.toml", MANIFEST),
            (
                "src/main.wf",
                "fn main() {\n    json.noting()\n}\nfn stated() / Note {\n    json.noting()\n}\n",
            ),
            ("deps/json/src/lib.wf", NOTE_LIB),
        ],
    );
    let out = cmd(&["check", &pkg]);
    assert_eq!(out.code, 1, "{}", out.text);
    for want in [
        "error[W0805]: `main` performs `json.Note`, and no handler handles it",
        "the runtime handles only the standard effects; handle `json.Note` in `main`",
        "error[W0101]: unknown effect `Note`",
        "the effect with this name is written `json.Note` here",
        "add `json.Note` to the effects after `/`, or handle it here",
    ] {
        assert!(out.text.contains(want), "missing `{want}`:\n{}", out.text);
    }
}

#[test]
fn the_project_cannot_name_a_private_effect_of_a_dependency() {
    let pkg = scratch(
        "private_effect",
        &[
            ("weft.toml", MANIFEST),
            (
                "src/main.wf",
                "fn main() {\n    handle json.Secret { fn secret(x) { resume(()) } } in json.hiding()\n}\nfn stated() / json.Secret { json.hiding() }\nfn direct() { json.Secret.secret(1) }\n",
            ),
            ("deps/json/src/lib.wf", NOTE_LIB),
        ],
    );
    let out = cmd(&["check", &pkg]);
    assert_eq!(out.code, 1, "{}", out.text);
    let private = out
        .text
        .lines()
        .filter(|l| l.starts_with("error[W0101]") && l.contains("is private"))
        .count();
    assert_eq!(private, 3, "{}", out.text);
    // The hints do not give a name that the project cannot write.
    assert!(
        out.text
            .contains("`json.Secret` is private in its package: code outside the package cannot state or handle it"),
        "{}",
        out.text
    );
}

#[test]
fn a_dependency_cannot_have_the_name_main() {
    // The effects of the root have `main` in their identity (`main.Note`). The
    // effects of a dependency `main` would get the same identities, so the
    // handler of the root would handle them (QA5).
    let manifest = |name: &str| {
        format!("[package]\nname = \"app\"\nkind = \"lib\"\n\n[dependencies.{name}]\npath = \"deps/{name}\"\nauthority = []\n")
    };
    let lib = "pub effect Note { fn note(x: u64) }\npub fn noisy() / Note { note(1) }\n";
    let root = |name: &str| {
        format!("effect Note {{ fn note(x: u64) }}\npub fn quiet() / {name}.Note {{\n    handle Note {{ fn note(x) {{ resume(()) }} }} in {name}.noisy()\n}}\n")
    };
    let bad = scratch(
        "dep_named_main",
        &[
            ("weft.toml", &manifest("main")),
            ("src/lib.wf", &root("main")),
            ("deps/main/src/lib.wf", lib),
        ],
    );
    let out = cmd(&["check", &bad]);
    assert_eq!(out.code, 1, "{}", out.text);
    assert!(
        out.text
            .contains("error[W0107]: a dependency cannot have the name `main`"),
        "{}",
        out.text
    );
    // With another name, the root states the effect of the dependency.
    let good = scratch(
        "dep_named_dep",
        &[
            ("weft.toml", &manifest("dep")),
            ("src/lib.wf", &root("dep")),
            ("deps/dep/src/lib.wf", lib),
        ],
    );
    let out = cmd(&["check", &good]);
    assert_eq!(out.code, 0, "{}", out.text);
}

/// Returns, for each task that `main` of the package at `pkg` spawns, true if
/// the scheduler may move it to another worker.
fn spawned_stealable(pkg: &str) -> Vec<bool> {
    let (_, c) = weft_cli::check_path(
        std::path::Path::new(pkg),
        weft_cli::package::Profile::default(),
    )
    .unwrap();
    assert!(c.ok(), "{:?}", c.codes());
    let opts = weft_interp::RunOptions {
        workers: 4,
        ..weft_interp::RunOptions::default()
    };
    let out = weft_interp::run_main(&c, &opts).unwrap();
    out.trace
        .iter()
        .filter_map(|e| match e {
            weft_interp::TraceEvent::Spawn { stealable, .. } => Some(*stealable),
            _ => None,
        })
        .collect()
}

#[test]
fn a_task_of_a_dependency_keeps_its_own_stealable_mark() {
    // The closure of the project and the closure of the dependency have the
    // same byte offsets in their files. The first task is stealable, the
    // second one captures an `Rc` and is pinned (ADR 0010).
    let main = "// a comment line!.\nfn main() / async, io {\n    scope { s => s.spawn(|| { let y = 123456789 }) }\n    json.bg()\n}\n";
    let lib = "pub fn bg() / async {\n    let r = Rc.new(0)\n    scope { s => s.spawn(|| { let y = r.clone() }) }\n}\n";
    let at = |src: &str, pat: &str| src.find(pat).unwrap();
    assert_eq!(at(main, "|| {"), at(lib, "|| {"));
    let manifest = "[package]\nname = \"app\"\n\n[dependencies.json]\npath = \"deps/json\"\nauthority = [\"async\"]\n";
    let pkg = scratch(
        "stealable_units",
        &[
            ("weft.toml", manifest),
            ("src/main.wf", main),
            ("deps/json/src/lib.wf", lib),
        ],
    );
    assert_eq!(spawned_stealable(&pkg), vec![true, false]);
}
