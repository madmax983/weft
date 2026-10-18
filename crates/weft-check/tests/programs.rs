//! The program corpus: every design doc example and one negative program per rule.

#![allow(clippy::unwrap_used, clippy::expect_used)]
//!
//! A line that ends with `//~ CODE ...` expects those error codes on that line.
//! The words `stealable` and `pinned` after `//~` expect each task closure on
//! that line to be stealable, or not. A file that uses one of these words must
//! mark every line with a task closure.
//! The file markers `// weft: library` and `// weft: no-runtime` set the options,
//! as in `weft check`. For every body, the production checker must agree with
//! the Datalog spec. Each violation relation of the spec, and `stealable`, must
//! hold for some body of the corpus.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use weft_check::{agreement, bridge, check_source, Checked};
use weft_sema::Options;
use weft_syntax::diag::Severity;
use weft_syntax::SourceFile;

/// The words after `//~` that name a task property, not an error code.
const TASK_WORDS: [&str; 2] = ["stealable", "pinned"];

/// A set of `(line, word)` pairs.
type Marks = BTreeSet<(usize, String)>;

/// Returns the expected `(line, word)` pairs: error codes, and task words.
fn expected(src: &str) -> (Marks, Marks) {
    let (mut codes, mut tasks) = (BTreeSet::new(), BTreeSet::new());
    for (i, line) in src.lines().enumerate() {
        if let Some(pos) = line.find("//~") {
            for word in line[pos + 3..].split_whitespace() {
                let set = if TASK_WORDS.contains(&word) {
                    &mut tasks
                } else {
                    &mut codes
                };
                set.insert((i + 1, word.to_string()));
            }
        }
    }
    (codes, tasks)
}

/// Returns `(line, stealable or pinned)` for each task closure of the root unit.
fn task_lines(checked: &Checked, file: &SourceFile) -> Marks {
    let mut out = BTreeSet::new();
    for (b, r) in checked.analysis.bodies.iter().zip(&checked.reports) {
        if b.unit != 1 {
            continue;
        }
        for (i, t) in b.facts.tasks.iter().enumerate() {
            let stealable = r.violations.stealable.iter().any(|s| s.index() == i);
            let word = TASK_WORDS[usize::from(!stealable)];
            out.insert((file.line(t.span), word.to_string()));
        }
    }
    out
}

fn run(path: &Path) -> Result<(), String> {
    let src = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let name = path
        .file_name()
        .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
    let unknown: Vec<&str> = weft_sema::marker_words(&src)
        .into_iter()
        .map(|(_, w)| w)
        .filter(|w| !weft_sema::MARKERS.contains(w))
        .collect();
    if !unknown.is_empty() {
        return Err(format!("unknown file markers {unknown:?}"));
    }
    let opts = Options::from_markers(&src);
    let checked = check_source(&name, &src, opts);
    let file = SourceFile::new(&name, src.as_str());
    let actual: BTreeSet<(usize, String)> = checked
        .diags
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| (file.line(d.span), d.code.clone()))
        .collect();
    let (want, want_tasks) = expected(&src);
    let mut msg = String::new();
    if actual != want {
        let _ = writeln!(msg, "{name}: expected {want:?}\n  found {actual:?}");
        for d in &checked.diags {
            msg.push_str(&d.render(&file));
        }
    }
    if !want_tasks.is_empty() {
        let tasks = task_lines(&checked, &file);
        if tasks != want_tasks {
            let _ = writeln!(
                msg,
                "{name}: expected tasks {want_tasks:?}\n  found {tasks:?}"
            );
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

fn corpus_paths() -> Vec<std::path::PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut paths: Vec<_> = fs::read_dir(&dir)
        .expect("tests/programs exists")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    paths.sort();
    paths
}

/// Each violation relation of the spec, and `stealable`, holds for at least one
/// body of the corpus. So each rule has a corpus program that exercises it.
#[test]
fn corpus_exercises_every_rule() {
    let mut want: BTreeSet<&str> = bridge::VIOLATION_RELATIONS.into_iter().collect();
    want.insert("stealable");
    let mut seen = BTreeSet::new();
    for path in corpus_paths() {
        let src = fs::read_to_string(&path).expect("the program is readable");
        let checked = check_source("corpus.wf", &src, Options::from_markers(&src));
        for b in &checked.analysis.bodies {
            let out = bridge::evaluate_spec(&b.facts, false).expect("the spec runs");
            for rel in &want {
                if !out.tuples(rel).is_empty() {
                    seen.insert(*rel);
                }
            }
        }
    }
    let missing: Vec<&&str> = want.iter().filter(|r| !seen.contains(*r)).collect();
    assert!(missing.is_empty(), "no corpus program derives {missing:?}");
}

#[test]
fn corpus() {
    let paths = corpus_paths();
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
