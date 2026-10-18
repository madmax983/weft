//! Tests of the `weft` commands.

use weft_cli::run;

fn root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn cmd(args: &[&str]) -> weft_cli::Output {
    let args: Vec<String> = args
        .iter()
        .map(|a| {
            if a.contains('/') && !a.starts_with('/') {
                root().join(a).display().to_string()
            } else {
                (*a).to_string()
            }
        })
        .collect();
    run(&args).expect("command runs")
}

#[test]
fn check_reports_the_doc_diagnostic() {
    let out = cmd(&["check", "tests/programs/02_bad.wf"]);
    assert_eq!(out.code, 1);
    assert!(out
        .text
        .contains("error[W0301]: `first` used after it was invalidated"));
    assert!(out
        .text
        .contains("first : &Entity in world.entities[]  (line 7)"));
    assert!(out
        .text
        .contains("push : mut(world.entities)           (line 8)"));
    assert!(out.text.contains("invalidated at line 8"));
    assert!(out.text.contains("used at line 9"));
}

#[test]
fn check_accepts_the_doc_example() {
    let out = cmd(&["check", "tests/programs/01_places.wf"]);
    assert_eq!(out.code, 0, "{}", out.text);
}

#[test]
fn explain_prints_the_derivation_tree() {
    let out = cmd(&["check", "--explain", "tests/programs/02_bad.wf"]);
    assert!(out
        .text
        .contains("error(R, P) :- uses(R, P), invalid(R, P)."));
    assert!(out
        .text
        .contains("crosses_unstable(`world.entities`, `world.entities[]`)"));
    let json = cmd(&["check", "--explain", "--json", "tests/programs/02_bad.wf"]);
    assert!(json.text.contains("\"derivation\":{\"fact\":"));
    assert!(json.text.contains("\"code\":\"W0301\""));
}

#[test]
fn facts_are_datalog() {
    let out = cmd(&["facts", "tests/programs/02_bad.wf", "bad"]);
    assert!(out.text.contains("// facts of `bad`"));
    assert!(out.text.contains("cfg_edge(n"));
    assert!(out.text.contains("has_signature()."));
}

#[test]
fn agree_compares_checker_and_spec() {
    let out = cmd(&["agree", "tests/programs/08_ingest.wf"]);
    assert_eq!(out.code, 0, "{}", out.text);
    assert!(out.text.starts_with("agree:"));
}

#[test]
fn lint_runs_user_rules() {
    let out = cmd(&[
        "lint",
        "--rules",
        "examples/lints/ref_across_abort.dl",
        "tests/programs/18_polymorphism.wf",
    ]);
    assert!(out.text.contains("warning[L0001]"), "{}", out.text);
}

#[test]
fn deps_rejects_overreaching_dependency() {
    let out = cmd(&["deps", "examples/package"]);
    assert_eq!(out.code, 1);
    assert!(out
        .text
        .contains("error[W0901]: dependency `json` function `parse` needs"));
    assert!(out.text.contains("dependency `logger`: authority [log]"));
}

#[test]
fn library_cannot_enable_gc() {
    let out = cmd(&["check", "examples/gc-lib"]);
    assert!(out.text.contains("W0902"));
}

#[test]
fn explain_and_help() {
    assert!(cmd(&["explain", "w0301"])
        .text
        .contains("use of an invalidated reference"));
    assert_eq!(cmd(&["help"]).code, 0);
    assert!(cmd(&["spec"]).text.contains("invalidated_at(R, P)"));
    assert_eq!(run(&[]).expect("usage").code, 2);
    assert!(run(&["nope".to_string()]).is_err());
    assert!(run(&["explain".to_string(), "W9999".to_string()]).is_err());
    assert!(run(&["check".to_string(), "--bad".to_string()]).is_err());
}
