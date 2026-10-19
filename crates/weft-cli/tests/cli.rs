//! Tests of the `weft` commands.

#![allow(clippy::unwrap_used, clippy::expect_used)]

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

/// Writes `files` into a new directory for one test, and returns its path.
fn scratch(name: &str, files: &[(&str, &str)]) -> String {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("cli")
        .join(name);
    let _ = std::fs::remove_dir_all(&dir);
    for (path, text) in files {
        let p = dir.join(path);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    }
    dir.display().to_string()
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
fn authority_covers_private_dependency_functions() {
    // A private function of a dependency counts too: a public one can call it.
    let pkg = scratch(
        "private_authority",
        &[
            (
                "weft.toml",
                "[package]\nname = \"app\"\n\n[dependencies.json]\npath = \"deps/json\"\nauthority = []\n",
            ),
            (
                "src/main.wf",
                "fn main(env: Env) / io, net {\n    print(json.parse(\"[1]\"))\n}\n",
            ),
            (
                "deps/json/src/lib.wf",
                "pub fn parse(text: String) -> u64 { 3 }\n\nfn phone_home(text: String) / net {}\n",
            ),
        ],
    );
    for command in ["check", "deps"] {
        let out = cmd(&[command, &pkg]);
        assert_eq!(out.code, 1, "{command}: {}", out.text);
        assert!(
            out.text.contains(
                "error[W0901]: dependency `json` function `phone_home` needs `async, net`"
            ),
            "{command}: {}",
            out.text
        );
        assert!(
            !out.text.contains("`parse` needs"),
            "{command}: {}",
            out.text
        );
    }
    // A closure that a dependency returns runs the code of the dependency.
    let pkg = scratch(
        "closure_authority",
        &[
            (
                "weft.toml",
                "[package]\nname = \"app\"\n\n[dependencies.json]\npath = \"deps/json\"\nauthority = []\n",
            ),
            (
                "src/main.wf",
                "fn main(env: Env) / io, net {\n    let f = json.get()\n    f()\n}\n",
            ),
            (
                "deps/json/src/lib.wf",
                "pub fn get() -> fn() / net {\n    || net.net_poll()\n}\n",
            ),
        ],
    );
    let out = cmd(&["check", &pkg]);
    assert_eq!(out.code, 1, "{}", out.text);
    assert!(
        out.text
            .contains("error[W0901]: dependency `json` function `get` needs `async, net`"),
        "{}",
        out.text
    );
    // The closure belongs to `get`, so the public signature of `get` must state
    // `net` too (ADR 0005).
    assert!(
        out.text
            .contains("error[W0701]: public function `get` must state its effects: `/ net`"),
        "{}",
        out.text
    );
    assert!(out.text.contains("2 error(s)"), "{}", out.text);
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
    for code in ["W0108", "W0111", "W0115", "W0116", "W0706", "L0001"] {
        assert_eq!(cmd(&["explain", code]).code, 0, "{code}");
    }
    let help = cmd(&["help"]);
    assert_eq!(help.code, 0);
    for word in [
        "run     [PROFILE] [--seed N]",
        "test    [PROFILE] [--seed N]",
        "--unchecked",
        "--lib or --bin",
        "1 to 1024",
        "// weft: library",
    ] {
        assert!(help.text.contains(word), "{word}");
    }
    assert!(cmd(&["spec"]).text.contains("invalidated_at(R, P)"));
    assert_eq!(run(&[]).expect("usage").code, 2);
    assert!(run(&["nope".to_string()]).is_err());
    assert!(run(&["explain".to_string(), "W9999".to_string()]).is_err());
    assert!(run(&["check".to_string(), "--bad".to_string()]).is_err());
}

#[test]
fn check_sees_package_dependencies() {
    let out = cmd(&["check", "examples/package"]);
    assert!(!out.text.contains("W0101"), "{}", out.text);
    // The example grants `json` nothing, so its authority errors stay: one for
    // `parse` and one for the private `phone_home`.
    assert!(out.text.contains("error[W0901]"), "{}", out.text);
    assert!(out.text.contains("2 error(s)"), "{}", out.text);
}

#[test]
fn check_honors_file_markers() {
    let lib = cmd(&["check", "tests/programs/15_library.wf"]);
    assert_eq!(lib.code, 1);
    assert!(lib.text.contains("error[W0801]"), "{}", lib.text);
    assert!(lib.text.contains("error[W0802]"), "{}", lib.text);
    let embedded = cmd(&["check", "tests/programs/19b_no_runtime_bad.wf"]);
    assert_eq!(embedded.code, 1);
    assert!(embedded.text.contains("error[W0803]"), "{}", embedded.text);
    // A flag adds an option that the markers do not set.
    let embedded_ok = "tests/programs/19_no_runtime.wf";
    assert_eq!(cmd(&["check", embedded_ok]).code, 0);
    let flagged = cmd(&["check", "--lib", embedded_ok]);
    assert!(flagged.text.contains("error[W0801]"), "{}", flagged.text);
    assert!(!flagged.text.contains("W0803"), "{}", flagged.text);
    // `run` reads the markers too: the embedded profile has no root handlers.
    assert_eq!(cmd(&["run", embedded_ok]).code, 0);
    let refused = cmd(&["run", "tests/programs/19b_no_runtime_bad.wf"]);
    assert_eq!(refused.code, 1);
    assert!(
        refused.stderr.contains("error[W0803]"),
        "{}",
        refused.stderr
    );
}

const INTERP: &str = "crates/weft-interp/tests/programs";

#[test]
fn run_prints_the_output_of_main() {
    let out = cmd(&["run", &format!("{INTERP}/effects_log.wf")]);
    assert_eq!(out.code, 0, "{} {}", out.text, out.stderr);
    assert_eq!(out.text, "stepped 1 hp=9\nstepped 2 hp=19\n");
    assert_eq!(out.stderr, "");
}

#[test]
fn run_failure_exits_with_1() {
    let out = cmd(&["run", &format!("{INTERP}/root_handlers.wf")]);
    assert_eq!(out.code, 1);
    assert_eq!(out.text, "rollback 3\n");
    assert!(out.stderr.contains("starting"), "{}", out.stderr);
    assert!(out.stderr.contains("error: failed: boom"), "{}", out.stderr);
    assert!(
        out.stderr.contains("root_handlers.wf:12:"),
        "{}",
        out.stderr
    );
}

#[test]
fn run_refuses_a_program_with_errors() {
    let path = format!("{INTERP}/once_twice.wf");
    let out = cmd(&["run", &path]);
    assert_eq!(out.code, 1);
    assert_eq!(out.text, "");
    assert!(out.stderr.contains("error[W0501]"), "{}", out.stderr);
    assert!(out.stderr.contains("--unchecked"), "{}", out.stderr);
    assert!(!out.stderr.contains("was resumed twice"), "{}", out.stderr);
    let out = cmd(&["run", "--unchecked", &path]);
    assert_eq!(out.code, 1);
    assert!(
        out.stderr
            .contains("a `once` continuation was resumed twice"),
        "{}",
        out.stderr
    );
}

#[test]
fn run_takes_seed_and_workers() {
    let path = format!("{INTERP}/steal.wf");
    for args in [
        vec!["run", path.as_str()],
        vec!["run", "--seed", "7", "--workers", "1", path.as_str()],
        vec!["run", "--workers", "8", path.as_str()],
    ] {
        let out = cmd(&args);
        assert_eq!(out.code, 0, "{}", out.stderr);
        assert_eq!(out.text, "24856\n");
    }
    assert!(run(&["run".into(), "--seed".into(), "x".into(), path.clone()]).is_err());
    assert!(run(&["run".into(), "--workers".into(), "0".into(), path]).is_err());
    assert!(run(&["run".into(), "--seed".into()]).is_err());
}

#[test]
fn run_limits_the_workers() {
    let path = root().join(INTERP).join("steal.wf").display().to_string();
    let out = cmd(&["run", "--workers", "1024", &path]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    for n in ["1025", "100000000000", "18446744073709551615"] {
        let args: Vec<String> = ["run", "--workers", n, &path].map(String::from).to_vec();
        let e = run(&args).expect_err(n);
        assert!(e.to_string().contains("1 to 1024"), "{n}: {e}");
    }
}

#[test]
fn a_syntax_error_is_an_error_of_the_program() {
    let dir = scratch("syntax", &[("bad.wf", "fn main() {\n    let x = ;\n}\n")]);
    let file = format!("{dir}/bad.wf");
    let out = cmd(&["check", &file]);
    assert_eq!(out.code, 1, "{}", out.text);
    assert!(out.text.starts_with("error[W0001]: "), "{}", out.text);
    assert!(out.text.contains("bad.wf:2:13"), "{}", out.text);
    assert!(
        out.text.contains("1 error(s), 0 function(s)"),
        "{}",
        out.text
    );
    let json = cmd(&["check", "--json", &file]);
    assert_eq!(json.code, 1);
    assert!(
        json.text
            .starts_with("{\"code\":\"W0001\",\"severity\":\"error\""),
        "{}",
        json.text
    );
    assert!(
        json.text.contains("\"line\":2,\"column\":13"),
        "{}",
        json.text
    );
    for command in ["run", "test", "facts", "agree"] {
        let out = cmd(&[command, &file]);
        assert_eq!(out.code, 1, "{command}");
        assert_eq!(out.text, "", "{command}");
        assert!(
            out.stderr.starts_with("error[W0001]: "),
            "{command}: {}",
            out.stderr
        );
    }
    let out = cmd(&["run", "--unchecked", &file]);
    assert_eq!(out.code, 1);
    // A file that is not there is still a usage error.
    assert!(run(&["check".into(), format!("{dir}/none.wf")]).is_err());
}

#[test]
fn commands_reject_options_that_they_do_not_take() {
    let path = root()
        .join("tests/programs/01_places.wf")
        .display()
        .to_string();
    for args in [
        vec!["run", "--json", &path],
        vec!["test", "--explain", &path],
        vec!["run", "--rules", "x.dl", &path],
        vec!["check", "--seed", "1", &path],
        vec!["check", "--unchecked", &path],
        vec!["deps", "--lib", &path],
        vec!["explain", "--json", "W0301"],
    ] {
        let args: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
        let e = run(&args).expect_err(&args.join(" "));
        assert!(e.to_string().contains("does not take"), "{e}");
    }
}

#[test]
fn test_notes_a_file_with_no_tests() {
    let out = cmd(&["test", "tests/programs/01_places.wf"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert!(out.text.contains("0 passed, 0 failed"), "{}", out.text);
    assert!(out.stderr.contains("has no test blocks"), "{}", out.stderr);
}

#[test]
fn profile_flags_win_over_markers() {
    let lib = "tests/programs/15_library.wf";
    assert_eq!(cmd(&["check", lib]).code, 1);
    let bin = cmd(&["check", "--bin", lib]);
    assert!(!bin.text.contains("W0801"), "{}", bin.text);
    let embedded = "tests/programs/19b_no_runtime_bad.wf";
    let rt = cmd(&["check", "--runtime", embedded]);
    assert!(!rt.text.contains("W0803"), "{}", rt.text);
    assert_eq!(rt.code, 0, "{}", rt.text);
}

#[test]
fn check_warns_about_unknown_file_markers() {
    let dir = scratch(
        "markers",
        &[(
            "m.wf",
            "// weft: lib, no-runtime\n// weft: Library\nfn main() {}\n",
        )],
    );
    let out = cmd(&["check", &format!("{dir}/m.wf")]);
    assert_eq!(out.code, 0, "{}", out.text);
    assert!(
        out.text
            .contains("warning[W0804]: unknown file marker `lib`"),
        "{}",
        out.text
    );
    assert!(out.text.contains("m.wf:1:10"), "{}", out.text);
    assert!(
        out.text.contains("unknown file marker `Library`"),
        "{}",
        out.text
    );
    assert_eq!(out.text.matches("W0804").count(), 2, "{}", out.text);
}

#[test]
fn run_without_main_fails() {
    let out = cmd(&["run", "tests/programs/01_places.wf"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("no `fn main`"), "{}", out.stderr);
}

#[test]
fn test_runs_the_test_blocks() {
    let out = cmd(&["test", "tests/programs/10_sim.wf"]);
    assert_eq!(out.code, 0, "{} {}", out.text, out.stderr);
    assert!(out.text.contains("test election survives a partition: ok"));
    assert!(out.text.contains("1 passed, 0 failed"), "{}", out.text);
}

#[test]
fn test_reports_failing_tests() {
    let out = cmd(&["test", &format!("{INTERP}/sim.wf")]);
    assert_eq!(out.code, 1);
    assert!(
        out.text.contains("0s 35s\ntest virtual clock: ok\n"),
        "{}",
        out.text
    );
    assert!(out
        .text
        .contains("test a failing assertion: FAILED: assertion failed: the condition is false"));
    assert!(out
        .text
        .contains("test a failure inside a simulation: FAILED: failed: sim fail"));
    assert!(out.text.contains("3 passed, 2 failed"), "{}", out.text);
}

#[test]
fn test_refuses_a_program_with_errors() {
    let out = cmd(&["test", "tests/programs/02_bad.wf"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("error[W0301]"), "{}", out.stderr);
    assert!(out.stderr.contains("--unchecked"), "{}", out.stderr);
    let out = cmd(&["test", "--unchecked", "tests/programs/02_bad.wf"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert!(out.text.contains("0 passed, 0 failed"), "{}", out.text);
}

/// The binary prints the program output to stdout and the log and errors to
/// stderr, and its exit code is the command's code.
#[test]
fn binary_streams_output_and_sets_the_exit_code() {
    let bin = env!("CARGO_BIN_EXE_weft");
    let run_bin = |args: &[&str]| {
        let args: Vec<String> = args
            .iter()
            .map(|a| {
                if a.contains('/') {
                    root().join(a).display().to_string()
                } else {
                    (*a).to_string()
                }
            })
            .collect();
        std::process::Command::new(bin)
            .args(&args)
            .output()
            .expect("weft runs")
    };
    let ok = run_bin(&["run", &format!("{INTERP}/effects_log.wf")]);
    assert_eq!(ok.status.code(), Some(0));
    assert_eq!(
        String::from_utf8_lossy(&ok.stdout),
        "stepped 1 hp=9\nstepped 2 hp=19\n"
    );
    let bad = run_bin(&["run", &format!("{INTERP}/root_handlers.wf")]);
    assert_eq!(bad.status.code(), Some(1));
    assert_eq!(String::from_utf8_lossy(&bad.stdout), "rollback 3\n");
    let err = String::from_utf8_lossy(&bad.stderr);
    assert!(err.contains("starting"), "{err}");
    assert!(err.contains("error: failed: boom"), "{err}");
    let tests = run_bin(&["test", &format!("{INTERP}/sim.wf")]);
    assert_eq!(tests.status.code(), Some(1));
    let usage = run_bin(&["nope"]);
    assert_eq!(usage.status.code(), Some(2));
}

/// The binary writes the log of a test before the result line of the test.
#[cfg(unix)]
#[test]
fn binary_test_writes_each_log_before_its_result() {
    let dir = scratch(
        "test_log",
        &[(
            "t.wf",
            "test \"logs\" {\n    log.info(\"hello log\")\n    print(\"ok\")\n}\ntest \"after\" {\n    print(\"later\")\n}\n",
        )],
    );
    let bin = env!("CARGO_BIN_EXE_weft");
    let out = std::process::Command::new("sh")
        .arg("-c")
        .arg(format!("'{bin}' test '{dir}/t.wf' 2>&1"))
        .output()
        .expect("sh runs");
    assert_eq!(out.status.code(), Some(0));
    let text = String::from_utf8_lossy(&out.stdout);
    let at = |s: &str| text.find(s).unwrap_or_else(|| panic!("no {s:?} in {text}"));
    assert!(at("info: hello log") < at("test logs: ok"), "{text}");
    assert!(at("test logs: ok") < at("later"), "{text}");
}

#[test]
fn deps_sees_effects_that_signatures_hide() {
    let out = cmd(&["deps", "tests/packages/hidden"]);
    assert_eq!(out.code, 1, "{}", out.text);
    // A returned closure has the effects of its maker.
    assert!(
        out.text
            .contains("error[W0901]: dependency `json` function `parse` needs `async, net`"),
        "{}",
        out.text
    );
    // The body counts, not only the stated effects.
    assert!(
        out.text
            .contains("function `quiet` needs `async, log, net`"),
        "{}",
        out.text
    );
    // A private function counts: a public function can call it.
    assert!(out.text.contains("function `helper` needs"), "{}", out.text);
}
