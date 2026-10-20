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

/// Returns the expected `(line, word)` pairs: error codes, and task words.
///
/// A line that ends with `//~ CODE ...` expects those error codes on that
/// line. A code that occurs two times expects two errors with that code.
pub fn expected(src: &str) -> (Codes, Marks) {
    let (mut codes, mut tasks) = (Vec::new(), BTreeSet::new());
    for (i, line) in src.lines().enumerate() {
        if let Some(pos) = line.find("//~") {
            for word in line[pos + 3..].split_whitespace() {
                if TASK_WORDS.contains(&word) {
                    tasks.insert((i + 1, word.to_string()));
                } else {
                    codes.push((i + 1, word.to_string()));
                }
            }
        }
    }
    codes.sort();
    (codes, tasks)
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
