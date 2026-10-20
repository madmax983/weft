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
