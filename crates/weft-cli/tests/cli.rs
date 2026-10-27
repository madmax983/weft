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

/// Runs a command that must fail with a usage error, and returns the message.
fn usage_error(args: &[&str]) -> String {
    let args: Vec<String> = args.iter().map(|a| (*a).to_string()).collect();
    match run(&args) {
        Ok(out) => panic!("`{}` runs: {} {}", args.join(" "), out.text, out.stderr),
        Err(e) => format!("{e:#}"),
    }
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
fn json_notes_keep_their_lines() {
    let json = cmd(&["check", "--json", "tests/programs/02_bad.wf"]);
    let line = json.text.lines().next().unwrap_or_default();
    assert!(
        line.contains(
            "\"notes\":[{\"text\":\"first : &Entity in world.entities[]\",\"line\":7},{\"text\":\"push : mut(world.entities)\",\"line\":8},{\"text\":\"world.entities is a strict prefix of world.entities[], through an unstable step  →  invalidated at line 8\"},"
        ),
        "{line}"
    );
}

#[test]
fn explain_links_each_derivation_to_its_diagnostic() {
    let out = cmd(&["check", "--explain", "tests/programs/02_bad.wf"]);
    assert!(
        out.text.contains(
            "derivation of error(`first`, print@line9) in `bad`, for error[W0301] at line 9:\n"
        ),
        "{}",
        out.text
    );
    let json = cmd(&["check", "--explain", "--json", "tests/programs/02_bad.wf"]);
    let derivation = json
        .text
        .lines()
        .find(|l| l.starts_with("{\"derivation\":"))
        .unwrap_or_default();
    assert!(
        derivation.ends_with(
            ",\"function\":\"bad\",\"diagnostic\":{\"code\":\"W0301\",\"line\":9,\"column\":5}}"
        ),
        "{derivation}"
    );
}

#[test]
fn facts_are_datalog() {
    let out = cmd(&["facts", "tests/programs/02_bad.wf", "bad"]);
    assert!(out.text.contains("// facts of `bad`"));
    assert!(out.text.contains("cfg_edge(n"));
    assert!(out.text.contains("has_signature()."));
}

#[test]
fn ir_prints_the_core_ir() {
    let file = "crates/weft-sema/tests/ir_golden/ret_ref.wf";
    let all = cmd(&["ir", file]);
    assert_eq!(all.code, 0, "{}", all.stderr);
    assert!(all.text.contains("body b0: fn dangle"), "{}", all.text);
    assert!(
        all.text.contains("// typo: no IR: a type error"),
        "{}",
        all.text
    );
    let one = cmd(&["ir", file, "dangle"]);
    assert_eq!(one.code, 0, "{}", one.stderr);
    assert!(one.text.starts_with("body b0: fn dangle"), "{}", one.text);
    assert!(one
        .text
        .contains("    _0 = &_1\n    Dead(_1)\n    Return\n"));
    let none = cmd(&["ir", file, "typo"]);
    assert_eq!(none.code, 1);
    assert!(none.stderr.contains("has no IR"), "{}", none.stderr);
    let calls = cmd(&["ir", "tests/programs/01_places.wf", "tick"]);
    assert_eq!(calls.code, 0, "{}", calls.stderr);
    assert!(calls.text.contains("call step("), "{}", calls.text);
    let closures = cmd(&[
        "ir",
        "crates/weft-sema/tests/ir_golden/closure_move.wf",
        "main",
    ]);
    assert_eq!(closures.code, 0, "{}", closures.stderr);
    assert!(
        closures.text.starts_with("body b1: fn main"),
        "{}",
        closures.text
    );
    assert!(
        closures.text.contains("\nbody b2: closure c0; parent b1;"),
        "the closure bodies of `main` follow it: {}",
        closures.text
    );
    let handles = cmd(&["ir", "tests/programs/05_effects.wf", "main"]);
    assert_eq!(handles.code, 0, "{}", handles.stderr);
    assert!(
        handles.text.contains(" = handle h0 -> ["),
        "{}",
        handles.text
    );
    assert!(
        handles.text.contains(": handled h0; parent ") && handles.text.contains(": clause h0 log;"),
        "the handled body and the clause of `main` follow it: {}",
        handles.text
    );
    let scopes = cmd(&["ir", "tests/programs/07_scopes.wf", "profile_page"]);
    assert_eq!(scopes.code, 0, "{}", scopes.stderr);
    assert!(
        scopes.text.contains(" = scope s0 -> [") && scopes.text.contains(": scope s0; parent "),
        "the scope body of `profile_page` follows it: {}",
        scopes.text
    );
    assert!(scopes.text.contains("scope_wait _1"), "{}", scopes.text);
    // A move through a reference (W0303) gives the body no IR (ir 5.36).
    let moved = cmd(&["ir", "tests/programs/12_aliasing.wf", "steal"]);
    assert_eq!(moved.code, 1);
    assert!(
        moved.stderr.contains("`steal` has no IR: W0303"),
        "{}",
        moved.stderr
    );
    let missing = cmd(&["ir", file, "nope"]);
    assert_eq!(missing.code, 1);
    assert!(
        missing.stderr.contains("the bodies are `dangle`"),
        "{}",
        missing.stderr
    );
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
    assert_eq!(out.code, 1, "{}", out.text);
    let lines: Vec<&str> = out.text.lines().collect();
    assert_eq!(
        lines.first().copied(),
        Some("error[W0902]: a library cannot enable the GC tier; only a binary may"),
        "{}",
        out.text
    );
    assert!(
        lines
            .get(1)
            .is_some_and(|l| l.ends_with("examples/gc-lib/src/lib.wf:1:1")),
        "{}",
        out.text
    );
    assert!(
        out.text.contains("weft.toml sets `gc = true` in [package]"),
        "{}",
        out.text
    );
    assert_eq!(out.text.matches("error[").count(), 1, "{}", out.text);
}

#[test]
fn manifest_rejects_unknown_keys() {
    let main = ("src/main.wf", "fn main() {}\n");
    for (name, manifest, key) in [
        (
            "package_key",
            "[package]\nname = \"app\"\nruntim = \"none\"\n",
            "runtim",
        ),
        (
            "top_key",
            "[package]\nname = \"app\"\n[dependency.x]\npath = \"x\"\n",
            "dependency",
        ),
        (
            "dep_key",
            "[package]\nname = \"app\"\n[dependencies.x]\npath = \"x\"\nauthorty = []\n",
            "authorty",
        ),
    ] {
        let dir = scratch(
            &format!("manifest_{name}"),
            &[("weft.toml", manifest), main],
        );
        let e = usage_error(&["check", &dir]);
        assert!(
            e.starts_with(&format!("{dir}/weft.toml is not a valid manifest")),
            "{name}: {e}"
        );
        assert!(e.contains(&format!("unknown field `{key}`")), "{name}: {e}");
    }
}

#[test]
fn a_broken_dependency_manifest_is_an_error() {
    let dir = scratch(
        "broken_dep_manifest",
        &[
            (
                "weft.toml",
                "[package]\nname = \"app\"\n[dependencies.json]\npath = \"deps/json\"\n",
            ),
            ("src/main.wf", "fn main() {}\n"),
            (
                "deps/json/weft.toml",
                "[package]\nname = \"json\"\ngc = yes\n",
            ),
            ("deps/json/src/lib.wf", "pub fn parse() {}\n"),
        ],
    );
    let e = usage_error(&["check", &dir]);
    assert!(
        e.starts_with(&format!(
            "{dir}/deps/json/weft.toml is not a valid manifest"
        )),
        "{e}"
    );
    // A dependency with no manifest is a plain library.
    let dir = scratch(
        "no_dep_manifest",
        &[
            (
                "weft.toml",
                "[package]\nname = \"app\"\n[dependencies.json]\npath = \"deps/json\"\n",
            ),
            ("src/main.wf", "fn main() {}\n"),
            ("deps/json/src/lib.wf", "pub fn parse() {}\n"),
        ],
    );
    assert_eq!(cmd(&["check", &dir]).code, 0);
}

#[test]
fn a_user_effect_of_a_dependency_needs_no_authority() {
    // Authority grants standard effects only. The caller must handle a user
    // effect of the dependency, so the hint cannot name it.
    let dir = scratch(
        "user_effect_authority",
        &[
            (
                "weft.toml",
                "[package]\nname = \"app\"\n[dependencies.dep]\npath = \"deps/dep\"\nauthority = []\n",
            ),
            ("src/main.wf", "fn main() {}\n"),
            (
                "deps/dep/src/lib.wf",
                "pub effect Note2 { fn note2() }\npub fn f() / Note2 { note2() }\n",
            ),
        ],
    );
    let out = cmd(&["check", &dir]);
    assert!(!out.text.contains("W0901"), "{}", out.text);
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
        "run     [PROFILE] [FACTS] [RUN] PATH",
        "test    [PROFILE] [FACTS] [RUN] PATH",
        "FACTS is --facts=old|ir|both",
        "RUN is [--seed N] [--workers N] [--unchecked] [--oracle] [--fact-oracle]",
        "--ir-trace",
        "--unchecked",
        "--lib or --bin",
        "1 to 1024",
        "// weft: library",
    ] {
        assert!(help.text.contains(word), "{word}");
    }
    assert!(cmd(&["spec"]).text.contains("invalidated_at(R, P)"));
    assert_eq!(run(&[]).expect("usage").code, 2);
    assert!(usage_error(&["nope"]).starts_with("unknown command `nope`\nusage: weft"));
    assert_eq!(usage_error(&["explain", "W9999"]), "unknown code `W9999`");
    assert_eq!(usage_error(&["check", "--bad"]), "unknown option `--bad`");
}

#[test]
fn help_takes_a_command() {
    for args in [["help", "check"], ["--help", "run"], ["-h", "facts"]] {
        let out = cmd(&args);
        assert_eq!(out.code, 0, "{}", args.join(" "));
        assert!(out.text.starts_with("usage: weft"), "{}", out.text);
    }
    assert!(usage_error(&["help", "nope"]).starts_with("unknown command `nope`\nusage: weft"));
    assert_eq!(
        usage_error(&["help", "check", "x"]),
        "`help` takes at most 1 argument, found 2: `x` is extra; see `weft help`"
    );
}

#[test]
fn explain_needs_a_code() {
    let e = usage_error(&["explain"]);
    assert_eq!(e, "`explain` needs a CODE; see `weft help`");
}

#[test]
fn check_says_that_a_file_is_missing() {
    let dir = scratch("missing", &[("other.wf", "fn main() {}\n")]);
    let e = usage_error(&["check", &format!("{dir}/missing.wf")]);
    assert_eq!(
        e,
        format!("cannot read {dir}/missing.wf: no such file or directory")
    );
    // A directory needs a manifest.
    let e = usage_error(&["check", &dir]);
    assert!(
        e.starts_with(&format!("cannot read {dir}/weft.toml: ")),
        "{e}"
    );
}

#[test]
fn extra_positional_arguments_are_a_usage_error() {
    let path = root()
        .join("tests/programs/01_places.wf")
        .display()
        .to_string();
    for (args, want) in [
        (
            vec!["check", &path, "x"],
            "`check` takes 1 argument, found 2: `x` is extra; see `weft help`",
        ),
        (
            vec!["run", &path, "a", "b"],
            "`run` takes 1 argument, found 3: `a` is extra; see `weft help`",
        ),
        (
            vec!["facts", &path, "tick", "x"],
            "`facts` takes at most 2 arguments, found 3: `x` is extra; see `weft help`",
        ),
        (
            vec!["explain", "W0301", "W0302"],
            "`explain` takes 1 argument, found 2: `W0302` is extra; see `weft help`",
        ),
        (
            vec!["spec", "x"],
            "`spec` takes no arguments, found 1: `x` is extra; see `weft help`",
        ),
    ] {
        assert_eq!(usage_error(&args), want, "{}", args.join(" "));
    }
}

#[test]
fn facts_of_an_unknown_function_is_an_error() {
    let path = "tests/programs/02_bad.wf";
    let out = cmd(&["facts", path, "nosuchfn"]);
    assert_eq!(out.code, 1);
    assert_eq!(out.text, "");
    assert!(
        out.stderr
            .starts_with("error: no function or test `nosuchfn` in "),
        "{}",
        out.stderr
    );
    assert!(
        out.stderr
            .ends_with("; the bodies are `Entity.new`, `bad`\n"),
        "{}",
        out.stderr
    );
    assert_eq!(cmd(&["facts", path, "bad"]).code, 0);
    let dir = scratch("nobodies", &[("types.wf", "struct S { a: u64 }\n")]);
    let out = cmd(&["facts", &format!("{dir}/types.wf"), "f"]);
    assert_eq!(out.code, 1);
    assert!(
        out.stderr
            .ends_with("types.wf; it has no functions or tests\n"),
        "{}",
        out.stderr
    );
}

#[test]
fn lint_rejects_a_lint_relation_of_another_arity() {
    let path = root()
        .join("tests/programs/01_places.wf")
        .display()
        .to_string();
    for (name, rule, n) in [
        ("nullary", "lint() :- has_signature().\n", 0),
        ("unary", "lint(N) :- cfg_edge(N, _).\n", 1),
        ("ternary", "lint(\"x\", N, N) :- cfg_edge(N, _).\n", 3),
        ("fact", "lint(\"x\").\n", 1),
    ] {
        let dir = scratch(&format!("lint_{name}"), &[("rules.dl", rule)]);
        let rules = format!("{dir}/rules.dl");
        let e = usage_error(&["lint", "--rules", &rules, &path]);
        assert_eq!(
            e,
            format!("{rules}:1: `lint` must have 2 arguments (Name, Node), found {n}"),
            "{name}"
        );
    }
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
    assert_eq!(
        usage_error(&["run", "--seed", "x", &path]),
        "--seed needs a number, found `x`"
    );
    assert_eq!(
        usage_error(&["run", "--workers", "0", &path]),
        "--workers needs a number from 1 to 1024, found `0`"
    );
    assert_eq!(usage_error(&["run", "--seed"]), "--seed needs a number");
}

#[test]
fn run_and_test_take_an_engine() {
    // `root_handlers.wf` uses only the construct groups A and B: the IR
    // engine runs it.
    let path = format!("{INTERP}/root_handlers.wf");
    for engine in ["--engine=ir", "--engine=ast"] {
        let out = cmd(&["run", engine, &path]);
        assert_eq!(out.code, 1, "{engine}");
        assert_eq!(out.text, "rollback 3\n", "{engine}");
        assert!(!out.stderr.contains("note: --engine"), "{}", out.stderr);
    }
    let out = cmd(&["run", "--engine", "ir", &path]);
    assert_eq!(out.text, "rollback 3\n");
    // A program with a handler runs on the IR engine (plan stage I3).
    let out = cmd(&["run", "--engine=ir", &format!("{INTERP}/effects_log.wf")]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert_eq!(out.text, "stepped 1 hp=9\nstepped 2 hp=19\n");
    assert!(!out.stderr.contains("note: --engine"), "{}", out.stderr);
    // A program with a scope runs on the IR engine (plan stage I4).
    let out = cmd(&["run", "--engine=ir", &format!("{INTERP}/scope_join.wf")]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert_eq!(out.text, "a\nc\nb\n6\n");
    assert!(!out.stderr.contains("note: --engine"), "{}", out.stderr);
    // A program with a body that has no IR (W0303) falls back to the AST
    // compiler, and says so.
    let out = cmd(&[
        "run",
        "--engine=ir",
        "--unchecked",
        "tests/programs/12_aliasing.wf",
    ]);
    assert!(
        out.stderr
            .contains("\nnote: --engine=ir: the AST compiler runs the program: `steal` has no IR"),
        "{}",
        out.stderr
    );
    let out = cmd(&["test", "--engine=ir", &format!("{INTERP}/int_width.wf")]);
    assert_eq!(out.code, 1);
    assert!(
        out.text.contains("test values that fit: ok"),
        "{}",
        out.text
    );
    assert!(!out.stderr.contains("note: --engine"), "{}", out.stderr);
    assert_eq!(
        usage_error(&["run", "--engine=jit", &path]),
        "--engine needs `ast` or `ir`, found `jit`"
    );
    assert_eq!(
        usage_error(&["run", "--engine"]),
        "--engine needs `ast` or `ir`"
    );
    assert_eq!(
        usage_error(&["check", "--engine=ir", &path]),
        "`check` does not take --engine; see `weft help`"
    );
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
    assert_eq!(
        usage_error(&["check", &format!("{dir}/none.wf")]),
        format!("cannot read {dir}/none.wf: no such file or directory")
    );
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
        vec!["check", "--oracle", &path],
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
    let err = String::from_utf8_lossy(&usage.stderr);
    assert!(err.starts_with("error: unknown command `nope`"), "{err}");
    let help = run_bin(&[]);
    assert_eq!(help.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&help.stdout).starts_with("usage: weft"));
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

#[test]
fn oracle_turns_on_the_strict_run_time_checks() {
    // A reference into a cleared `Vec`: the checker rejects it (W0301). The
    // stock machine prints `<dangling>`; with --oracle the run fails (ADR 0010).
    let dir = scratch(
        "oracle",
        &[(
            "dangling.wf",
            "fn main() {\n    let v = Vec.new()\n    v.push(1)\n    let r = &v[0]\n    v.clear()\n    print(r)\n}\n",
        )],
    );
    let file = format!("{dir}/dangling.wf");
    let out = cmd(&["run", "--unchecked", &file]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert_eq!(out.text, "<dangling>\n");
    let out = cmd(&["run", "--unchecked", "--oracle", &file]);
    assert_eq!(out.code, 1, "{}", out.text);
    assert!(
        out.stderr.contains("oracle: a read of a freed cell"),
        "{}",
        out.stderr
    );
    // A correct program runs with the checks too.
    let path = root()
        .join("crates/weft-interp/tests/programs/places.wf")
        .display()
        .to_string();
    let out = cmd(&["run", "--oracle", &path]);
    assert_eq!(out.code, 0, "{}", out.stderr);
}

#[test]
fn facts_switch_falls_back_to_the_old_pipeline_with_a_note() {
    // Only the groups A, B and C are on by default (stages F8, F10 and F13,
    // plan §2.6): a program with a handler (group D) goes to the old
    // pipeline, and the command says why on standard error.
    let dir = scratch(
        "fallback",
        &[(
            "handler_bad.wf",
            "effect Log { fn log(msg: String) }\nfn bad() {\n    let v = [1]\n    let w = v\n    handle Log { fn log(msg) { resume(()) } } in log(\"a\")\n    print(v.len())\n}\nfn main() { bad() }\n",
        )],
    );
    let path = format!("{dir}/handler_bad.wf");
    let path = path.as_str();
    let old = cmd(&["check", path]);
    assert_eq!(old.code, 1, "{}", old.text);
    assert!(old.stderr.is_empty(), "{}", old.stderr);
    assert_eq!(cmd(&["check", "--facts=old", path]), old);
    for f in ["--facts=ir", "--facts=both"] {
        let out = cmd(&["check", f, path]);
        assert_eq!(out.text, old.text, "{f}");
        assert_eq!(out.code, old.code, "{f}");
        let note =
            format!("note: {f}: the old pipeline checks the program: the program uses group D");
        assert!(out.stderr.starts_with(&note), "{f}: {}", out.stderr);
        assert_eq!(out.stderr.lines().count(), 1, "{}", out.stderr);
    }
    let out = cmd(&["check", "--facts", "ir", "--json", path]);
    assert!(out.text.starts_with("{\"code\""), "{}", out.text);
    assert!(
        out.stderr.starts_with("note: --facts=ir: "),
        "{}",
        out.stderr
    );
    // Each command that checks takes the switch.
    // `sim.wf` uses groups B to E.
    let run = format!("{INTERP}/sim.wf");
    let rules = "examples/lints/ref_across_abort.dl";
    for args in [
        vec!["facts", "--facts=ir", path, "bad"],
        vec!["agree", "--facts=ir", path],
        vec!["lint", "--facts=ir", "--rules", rules, path],
        vec!["run", "--facts=ir", run.as_str()],
        vec!["test", "--facts=ir", run.as_str()],
    ] {
        let out = cmd(&args);
        assert!(
            out.stderr
                .contains("note: --facts=ir: the old pipeline checks the program"),
            "{args:?}: {}",
            out.stderr
        );
    }
    let out = cmd(&["facts", "--facts=both", path, "bad"]);
    assert_eq!(out.text, cmd(&["facts", path, "bad"]).text);
    assert_eq!(
        usage_error(&["check", "--facts=new", path]),
        "--facts needs `old`, `ir` or `both`, found `new`"
    );
    assert_eq!(
        usage_error(&["ir", "--facts=ir", path]),
        "`ir` does not take --facts; see `weft help`"
    );
}

#[test]
fn groups_put_a_program_in_scope_of_the_ir_pipeline() {
    // A program with no call: with group A on, the ir pipeline checks it.
    let dir = scratch(
        "groups",
        &[(
            "no_calls.wf",
            "fn f() -> u64 {\n    let x = 1\n    let r = &x\n    x = 2\n    print(r)\n    x\n}\n",
        )],
    );
    let path = format!("{dir}/no_calls.wf");
    let out = cmd(&["agree", "--facts=ir", "--groups=A", &path]);
    assert_eq!(out.code, 0, "{}{}", out.text, out.stderr);
    assert!(out.stderr.is_empty(), "{}", out.stderr);
    assert!(out.text.starts_with("agree: "), "{}", out.text);
    let out = cmd(&["agree", "--facts=both", "--groups", "A", &path]);
    assert!(out.text.contains("of the ir pipeline"), "{}", out.text);
    let out = cmd(&["check", "--facts=both", "--groups=A", &path]);
    assert!(out.stderr.is_empty(), "{}", out.stderr);
    let facts = cmd(&["facts", "--facts=ir", "--groups=A", &path, "f"]);
    assert!(facts.text.contains("rebound_at("), "{}", facts.text);
    // Group A is on by default (stage F8): the ir pipeline checks the
    // program with no `--groups`. With `--groups=B` group A is off.
    let out = cmd(&["agree", "--facts=ir", &path]);
    assert!(out.stderr.is_empty(), "{}", out.stderr);
    assert_eq!(
        out.text,
        cmd(&["agree", "--facts=ir", "--groups=A", &path]).text
    );
    let out = cmd(&["agree", "--facts=ir", "--groups=B", &path]);
    assert!(
        out.stderr.contains("the program uses group A"),
        "{}",
        out.stderr
    );
    // A call of a function with no stated row is in scope (stage F6), and
    // so is a cleanup chain with an `on abort` function (stage F7).
    let out = cmd(&[
        "agree",
        "--facts=ir",
        "--groups=A",
        "tests/programs/02_bad.wf",
    ]);
    assert!(out.stderr.is_empty(), "{}", out.stderr);
    let dir = scratch(
        "groups_on_abort",
        &[(
            "on_abort.wf",
            "linear struct Tx { id: u64 }\n    on abort = undo\nfn undo(t: Tx) { let Tx(i) = t }\nfn g() { print(1) }\nfn f() {\n    let t = Tx { id: 1 }\n    g()\n    let Tx(i) = t\n}\n",
        )],
    );
    let out = cmd(&[
        "agree",
        "--facts=ir",
        "--groups=A",
        &format!("{dir}/on_abort.wf"),
    ]);
    assert!(out.stderr.is_empty(), "{}", out.stderr);
    assert!(out.text.starts_with("agree: "), "{}", out.text);
    assert_eq!(
        usage_error(&["check", "--groups=G", &path]),
        "--groups needs construct groups from A to F, found `G`: `G` is not a construct group (A to F)"
    );
}

#[test]
fn a_borrow_of_plain_data_gives_the_old_diagnostics_in_the_ir_pipeline() {
    // `docs/ir.md` 5.10: `temp_copy` of `tests/programs/32_temporaries.wf`
    // and other borrows of plain data, in a program with no call (group A).
    let src = "struct P { x: u64, y: u64 }\n\
        fn temp_copy() {\n    let r = &1\n    print(r)\n}\n\
        fn forms(c: bool) {\n\
        \x20   let a = &\"s\"\n    let b = &true\n    let u = &()\n    let d = &2.s\n\
        \x20   let t = &(1, 2)\n    let p = &P { x: 1, y: 2 }\n    let f = &(3, 4).0\n\
        \x20   let k = 0\n    let r = &k\n    if c { r = &5 }\n\
        \x20   print(a)\n    print(b)\n    print(u)\n    print(d)\n\
        \x20   print(t.0)\n    print(p.x)\n    print(f)\n    print(r)\n}\n";
    let dir = scratch("promoted", &[("plain.wf", src)]);
    let path = format!("{dir}/plain.wf");
    let old = cmd(&["check", "--facts=old", &path]);
    let ir = cmd(&["check", "--facts=ir", "--groups=A", &path]);
    assert!(
        ir.stderr.is_empty(),
        "the program is not in scope: {}",
        ir.stderr
    );
    assert_eq!(old.code, 0, "{}", old.text);
    assert_eq!((ir.code, ir.text), (old.code, old.text));
}

/// `--fact-oracle` runs the fact oracle on the IR engine and writes what it
/// checked; `--ir-trace` writes each step of the IR trace (stage F9).
#[test]
fn the_fact_oracle_and_the_ir_trace_write_notes() {
    let path = format!("{INTERP}/rc_cycle.wf");
    let out = cmd(&["run", "--fact-oracle", "--ir-trace", &path]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert!(
        out.stderr.contains("note: --fact-oracle: 1 frame(s)"),
        "{}",
        out.stderr
    );
    assert!(out.stderr.contains("ir-trace: frame 1 b"), "{}", out.stderr);
    // A local handler (plan stage F14): the oracle checks the handled body
    // and the clause in the component of the site.
    let handled = format!("{INTERP}/effects_log.wf");
    let checked = cmd(&["run", "--fact-oracle", &handled]);
    assert_eq!(checked.code, 0, "{}", checked.stderr);
    assert!(
        checked.stderr.contains("note: --fact-oracle: 7 frame(s)"),
        "{}",
        checked.stderr
    );
    // A program that is not in scope (a `multi` handler, stage F16): the
    // oracle checks nothing.
    let multi = format!("{INTERP}/multi_choose.wf");
    let looped = cmd(&["run", "--fact-oracle", &multi]);
    assert!(
        looped.stderr.contains("the oracle checks nothing"),
        "{}",
        looped.stderr
    );
}
