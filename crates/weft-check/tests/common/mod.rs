//! The parts that the corpus test (`programs.rs`) and the core IR target test
//! (`ir_targets.rs`) share: the `//~` markers of a program, the errors of the
//! checker by line, and the agreement of the checker with the spec.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use weft_check::{agreement, Checked};
use weft_syntax::diag::Severity;
use weft_syntax::SourceFile;

/// The words after `//~` that name a task property, not an error code.
pub const TASK_WORDS: [&str; 2] = ["stealable", "pinned"];

/// A set of `(line, word)` pairs.
pub type Marks = BTreeSet<(usize, String)>;

/// A sorted list of `(line, code)` pairs. A pair can occur more than one time.
pub type Codes = Vec<(usize, String)>;

/// The fact pipeline that a marker expects an error of (`--facts`, plan
/// §2.6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
pub enum Pipeline {
    /// The facts of the old lowering.
    Old,
    /// The facts of the core IR.
    Ir,
}

/// The words after `//~` that make the codes after them apply to one
/// pipeline only: `old:` and `ir:`.
pub const PIPELINE_WORDS: [&str; 2] = ["old:", "ir:"];

/// Returns the expected `(line, word)` pairs of the old pipeline: error
/// codes, and task words (see [`expected_for`]).
#[allow(dead_code)]
pub fn expected(src: &str) -> (Codes, Marks) {
    expected_for(src, Pipeline::Old)
}

/// Returns the expected `(line, word)` pairs of the pipeline `pipe`: error
/// codes, and task words.
///
/// A line that ends with `//~ CODE ...` expects those error codes on that
/// line. A code that occurs two times expects two errors with that code.
/// The word `old:` or `ir:` makes the codes after it apply to that pipeline
/// only, until the next such word: `//~ old: W0301 ir: W0302` expects W0301
/// from the old pipeline and W0302 from the ir pipeline.
pub fn expected_for(src: &str, pipe: Pipeline) -> (Codes, Marks) {
    let (mut codes, mut tasks) = (Vec::new(), BTreeSet::new());
    for (i, line) in src.lines().enumerate() {
        if let Some(pos) = line.find("//~") {
            let mut on = true;
            for word in line[pos + 3..].split_whitespace() {
                match word {
                    "old:" => on = pipe == Pipeline::Old,
                    "ir:" => on = pipe == Pipeline::Ir,
                    _ if !on => {}
                    w if TASK_WORDS.contains(&w) => {
                        tasks.insert((i + 1, w.to_string()));
                    }
                    w => codes.push((i + 1, w.to_string())),
                }
            }
        }
    }
    codes.sort();
    (codes, tasks)
}

/// True if a marker of `src` has an expectation for one pipeline only
/// (`old:` or `ir:`).
#[allow(dead_code)]
pub fn has_pipeline_markers(src: &str) -> bool {
    src.lines().any(|line| {
        line.find("//~").is_some_and(|pos| {
            line[pos + 3..]
                .split_whitespace()
                .any(|w| PIPELINE_WORDS.contains(&w))
        })
    })
}

/// Returns the sorted `(line, code)` pairs of the errors of a checked file.
pub fn actual(checked: &Checked, file: &SourceFile) -> Codes {
    let mut codes: Codes = checked
        .diags
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| (file.line(d.span), d.code.to_string()))
        .collect();
    codes.sort();
    codes
}

/// Writes one message to `msg` for each body where the production checker and
/// the Datalog spec disagree.
pub fn write_disagreements(name: &str, checked: &Checked, msg: &mut String) {
    if let Err(bad) = agreement(checked) {
        for b in bad {
            let _ = writeln!(
                msg,
                "{name}: checker and spec disagree in `{}`\n  checker: {:?}\n  spec:    {:?}",
                b.function, b.checker, b.spec
            );
        }
    }
}
