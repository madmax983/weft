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
