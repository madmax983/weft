//! The run-time program corpus.
//!
//! Each `tests/programs/NAME.wf` runs and its output must equal `NAME.out`.
//! A program with `test` blocks prints each test's output, then one result line
//! per test. Comment lines at the top give options:
//!
//! - `// unchecked`: the checker may report errors.
//! - `// expect-error: TEXT`: `main` must fail with a message that contains TEXT.
//! - `// seed: N`: the scheduler seed.
//! - `// leaked: N`, `// blocking: N`: the expected counters.
//! - `// weft: no-runtime`: the embedded profile.
//!
//! Set `WEFT_BLESS=1` to write the `.out` files from the current output.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use weft_interp::{run_main, run_tests, RunOptions};
use weft_sema::Options;
use weft_syntax::SourceFile;

fn directive<'s>(src: &'s str, key: &str) -> Option<&'s str> {
    src.lines()
        .take_while(|l| l.starts_with("//"))
        .find_map(|l| l.strip_prefix("// ")?.strip_prefix(key))
        .map(str::trim)
}

fn programs(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "wf"))
        .collect();
    v.sort();
    v
}

/// Runs one program and returns its output text.
fn run_program(path: &Path) -> Result<String, String> {
    let src = fs::read_to_string(path).unwrap();
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    let no_runtime = src.contains("// weft: no-runtime");
    let checked = weft_check::check_source(
        &name,
        &src,
        Options {
            library: src.contains("// weft: library"),
            no_runtime,
        },
    );
    let file = SourceFile::new(&name, src.as_str());
    if directive(&src, "unchecked").is_none() && !checked.ok() {
        let mut msg = format!("{name}: the checker rejects the program\n");
        for d in &checked.diags {
            msg.push_str(&d.render(&file));
        }
        return Err(msg);
    }
    let opts = RunOptions {
        seed: directive(&src, "seed:").map_or(0, |s| s.parse().unwrap()),
        max_steps: Some(5_000_000),
        no_runtime,
        ..RunOptions::default()
    };
    let mut out = String::new();
    if checked.analysis.program.tests.is_empty() {
        let (outcome, err) = match run_main(&checked, &opts) {
            Ok(o) => (o, None),
            Err(e) => (*e.outcome.clone(), Some(e)),
        };
        out.push_str(&outcome.stdout);
        match (directive(&src, "expect-error:"), err) {
            (None, None) => {}
            (Some(want), Some(e)) => {
                if !e.to_string().contains(want) {
                    return Err(format!("{name}: expected error `{want}`, found `{e}`"));
                }
            }
            (Some(want), None) => return Err(format!("{name}: expected error `{want}`")),
            (None, Some(e)) => {
                let line = e.span.map_or(0, |s| file.line(s));
                return Err(format!("{name}:{line}: unexpected error: {e}\n{out}"));
            }
        }
        if let Some(n) = directive(&src, "leaked:") {
            let n: usize = n.parse().unwrap();
            if outcome.leaked_rc != n {
                return Err(format!(
                    "{name}: leaked {} rc cells, expected {n}",
                    outcome.leaked_rc
                ));
            }
        }
        if let Some(n) = directive(&src, "blocking:") {
            let n: usize = n.parse().unwrap();
            if outcome.blocking_calls != n {
                return Err(format!(
                    "{name}: {} blocking calls, expected {n}",
                    outcome.blocking_calls
                ));
            }
        }
    } else {
        for t in run_tests(&checked, &opts) {
            out.push_str(&t.outcome.stdout);
            match t.message {
                None => writeln!(out, "test {}: ok", t.name).unwrap(),
                Some(m) => writeln!(out, "test {}: FAILED: {m}", t.name).unwrap(),
            }
        }
    }
    Ok(out)
}

#[test]
fn runtime_corpus() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let bless = std::env::var("WEFT_BLESS").is_ok();
    let mut failures = String::new();
    let mut count = 0;
    for path in programs(&dir) {
        count += 1;
        let expected_path = path.with_extension("out");
        match run_program(&path) {
            Err(e) => failures.push_str(&e),
            Ok(out) => {
                if bless {
                    fs::write(&expected_path, &out).unwrap();
                    continue;
                }
                let want = fs::read_to_string(&expected_path).unwrap_or_default();
                if out != want {
                    let _ = write!(
                        failures,
                        "{}: output differs\n--- expected\n{want}--- found\n{out}",
                        path.display()
                    );
                }
            }
        }
    }
    assert!(count >= 15, "the corpus is too small");
    assert!(failures.is_empty(), "{failures}");
}

/// The static corpus: every program with `main` or `test` blocks runs, or only
/// the static checker rejects it.
#[test]
fn static_corpus_runs() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut ran = 0;
    for path in programs(&dir) {
        let src = fs::read_to_string(&path).unwrap();
        let has_main = src.contains("fn main(");
        let has_tests = src.lines().any(|l| l.starts_with("test "));
        if !has_main && !has_tests {
            continue;
        }
        let no_runtime = src.contains("// weft: no-runtime");
        let checked = weft_check::check_source(
            "corpus",
            &src,
            Options {
                library: src.contains("// weft: library"),
                no_runtime,
            },
        );
        let opts = RunOptions {
            max_steps: Some(1_000_000),
            max_requests: Some(0),
            no_runtime,
            ..RunOptions::default()
        };
        if has_tests {
            for t in run_tests(&checked, &opts) {
                assert!(
                    t.passed,
                    "{}: test {} failed: {:?}",
                    path.display(),
                    t.name,
                    t.message
                );
            }
        }
        if has_main {
            let main_rejected = checked
                .diags
                .iter()
                .any(|d| d.severity == weft_syntax::diag::Severity::Error && d.code == "W0803");
            match run_main(&checked, &opts) {
                Ok(_) => assert!(
                    !main_rejected,
                    "{}: the checker rejects main",
                    path.display()
                ),
                Err(e) => assert!(
                    main_rejected,
                    "{}: main failed at run time: {e}",
                    path.display()
                ),
            }
        }
        ran += 1;
    }
    assert!(ran >= 5);
}
