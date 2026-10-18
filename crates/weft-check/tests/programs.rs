//! The program corpus: every design doc example and one negative program per rule.

#![allow(clippy::unwrap_used, clippy::expect_used)]
//!
//! A line that ends with `//~ CODE ...` expects those error codes on that line.
//! A file that contains `// weft: library` is checked as a library.
//! For every body, the production checker must agree with the Datalog spec.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use weft_check::{agreement, check_source};
use weft_sema::Options;
use weft_syntax::diag::Severity;
use weft_syntax::SourceFile;

fn expected(src: &str) -> BTreeSet<(usize, String)> {
    let mut out = BTreeSet::new();
    for (i, line) in src.lines().enumerate() {
        if let Some(pos) = line.find("//~") {
            for code in line[pos + 3..].split_whitespace() {
                out.insert((i + 1, code.to_string()));
            }
        }
    }
    out
}

fn run(path: &Path) -> Result<(), String> {
    let src = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let name = path
        .file_name()
        .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
    let opts = Options {
        library: src.contains("// weft: library"),
        no_runtime: src.contains("// weft: no-runtime"),
    };
    let checked = check_source(&name, &src, opts);
    let file = SourceFile::new(&name, src.as_str());
    let actual: BTreeSet<(usize, String)> = checked
        .diags
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| (file.line(d.span), d.code.clone()))
        .collect();
    let want = expected(&src);
    let mut msg = String::new();
    if actual != want {
        let _ = writeln!(msg, "{name}: expected {want:?}\n  found {actual:?}");
        for d in &checked.diags {
            msg.push_str(&d.render(&file));
        }
    }
    if let Err(bad) = agreement(&checked) {
        for b in bad {
            let _ = writeln!(
                msg,
                "{name}: checker and spec disagree in `{}`\n  checker: {:?}\n  spec:    {:?}",
                b.function, b.checker, b.spec
            );
        }
    }
    if msg.is_empty() {
        Ok(())
    } else {
        Err(msg)
    }
}

#[test]
fn corpus() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut paths: Vec<_> = fs::read_dir(&dir)
        .expect("tests/programs exists")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    paths.sort();
    assert!(paths.len() >= 10, "the corpus is missing");
    let failures: Vec<String> = paths.iter().filter_map(|p| run(p).err()).collect();
    assert!(
        failures.is_empty(),
        "{} of {} programs failed:\n{}",
        failures.len(),
        paths.len(),
        failures.join("\n")
    );
}
