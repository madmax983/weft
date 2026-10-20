//! The checker and the spec on mutated corpus programs (QR22).
//!
//! Each case takes a program of `tests/programs` and changes a few of its
//! lines: it deletes, duplicates or swaps statements, changes `&` to `&mut`,
//! or puts a statement into a closure, a loop or a handler. Each mutated
//! program goes through `check_source` on a 2 MiB thread. No stage may panic,
//! and the checker and the spec must agree on each body of a program that
//! parses, also on the evidence of W0301 and W0405.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use std::path::Path;

use proptest::prelude::*;
use weft_sema::Options;

/// The stack of the thread that checks a mutated program.
const STACK: usize = 2 * 1024 * 1024;

/// The sources of the corpus programs at the top of `tests/programs`, sorted
/// by name. The first call reads them.
fn corpus() -> &'static [(String, String)] {
    static CORPUS: std::sync::OnceLock<Vec<(String, String)>> = std::sync::OnceLock::new();
    CORPUS.get_or_init(read_corpus)
}

fn read_corpus() -> Vec<(String, String)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut out: Vec<(String, String)> = std::fs::read_dir(&dir)
        .expect("the corpus directory exists")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .map(|p| {
            let name = p.display().to_string();
            let src = std::fs::read_to_string(&p).expect("the program is readable");
            (name, src)
        })
        .collect();
    out.sort();
    out
}

/// One change of a program: the kind, a line and a second number.
type Mutation = (u8, usize, usize);

/// The number of kinds of change in [`mutate`].
const KINDS: u8 = 9;

/// Returns true if `line` looks like one whole statement of a body: it is
/// indented, and it does not open or close a block.
fn is_statement(line: &str) -> bool {
    let t = line.trim();
    line.starts_with(' ')
        && !t.is_empty()
        && !t.starts_with("//")
        && !t.starts_with('}')
        && !t.ends_with('{')
        && !t.starts_with("fn ")
        && t.matches('{').count() == t.matches('}').count()
}

/// Applies the changes to the lines of `src`, one after the other. A change
/// takes a line that holds a whole statement, if the program has one.
fn mutate(src: &str, changes: &[Mutation]) -> String {
    let mut lines: Vec<String> = src.lines().map(String::from).collect();
    for &(kind, at, other) in changes {
        if lines.is_empty() {
            break;
        }
        let stmts: Vec<usize> = (0..lines.len())
            .filter(|&k| is_statement(&lines[k]))
            .collect();
        let i = if stmts.is_empty() {
            at % lines.len()
        } else {
            stmts[at % stmts.len()]
        };
        let line = lines[i].clone();
        let stmt = line.trim();
        match kind % KINDS {
            // Delete a statement.
            0 => {
                lines.remove(i);
            }
            // Duplicate a statement.
            1 => lines.insert(i, line),
            // Swap a statement with the one after it.
            2 => {
                let j = (i + 1 + other % 3) % lines.len();
                lines.swap(i, j);
            }
            // Change a `&` to `&mut`, on the first line from `i` with one.
            3 => {
                let n = lines.len();
                let Some(j) = (0..n)
                    .map(|d| (i + d) % n)
                    .find(|&j| lines[j].contains('&'))
                else {
                    continue;
                };
                let line = lines[j].clone();
                let amps: Vec<usize> = line.match_indices('&').map(|(k, _)| k).collect();
                let k = amps[other % amps.len()];
                lines[j] = format!("{}&mut {}", &line[..k], &line[k + 1..]);
            }
            // Put a statement into a closure that runs at once, or later.
            4 => lines[i] = format!("let mut_k{i} = || {{ {stmt} }}\n mut_k{i}()"),
            5 => lines[i] = format!("let mut_c{i} = || {{ {stmt} }}"),
            // Put a statement into a loop.
            6 => {
                lines[i] = match other % 3 {
                    0 => format!("loop {{ {stmt}\n break }}"),
                    1 => format!("for mut_i in [1, 2] {{ {stmt} }}"),
                    _ => format!("while false {{ {stmt} }}"),
                };
            }
            // Put a statement into a handler of `Log` or `Fail`.
            7 => {
                lines[i] = if other % 2 == 0 {
                    format!("handle Log {{ fn info(m) {{ resume(()) }} fn warn(m) {{ resume(()) }} }} in {{ {stmt} }}")
                } else {
                    format!("handle Fail {{ fn fail(m) {{ () }} }} in {{ {stmt} }}")
                };
            }
            // Move a statement to another line.
            _ => {
                let s = lines.remove(i);
                let j = other % (lines.len() + 1);
                lines.insert(j, s);
            }
        }
    }
    lines.join("\n") + "\n"
}

/// Checks `src` on a 2 MiB thread and compares the checker with the spec.
/// Returns an error text if a stage panics or if they disagree.
fn check_on_small_stack(name: &str, src: &str) -> Result<(), String> {
    let file = name.to_string();
    let text = src.to_string();
    let result = std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let checked = weft_check::check_source(&file, &text, Options::default());
            if checked.analysis.bodies.is_empty() {
                return Ok(0);
            }
            weft_check::agreement(&checked).map_err(|bad| {
                let first = bad.first().map(|d| {
                    format!(
                        "{}: checker {:?}, spec {:?}, evidence {:?}",
                        d.function, d.checker, d.spec, d.evidence
                    )
                });
                format!("{} disagreements: {first:?}", bad.len())
            })
        })
        .expect("the thread starts")
        .join();
    match result {
        Ok(Ok(_)) => Ok(()),
        Ok(Err(e)) => Err(format!("{name}: {e}\n{src}")),
        Err(_) => Err(format!("{name}: a stage panics\n{src}")),
    }
}

/// The mutations of a few programs. Each kind changes the program: a
/// statement goes away, comes twice, moves, or goes into a closure, a loop or
/// a handler.
#[test]
fn each_kind_of_mutation_changes_the_program() {
    let src = "fn f(v: &Vec<u64>) / mut(v) {\n    let r = &v[0]\n    v.push(1)\n    print(r)\n}\n";
    for kind in 0..KINDS {
        let out = mutate(src, &[(kind, 1, 1)]);
        assert_ne!(out, src, "kind {kind}");
        assert!(check_on_small_stack("m.wf", &out).is_ok(), "{out}");
    }
    assert!(mutate(src, &[(3, 0, 0)]).contains("&mut v[0]"));
    assert!(mutate(src, &[(7, 1, 0)]).contains("handle Log"));
    assert!(is_statement("    v.push(1)"));
    assert!(!is_statement("fn f() {"));
    assert!(!is_statement("    if a {"));
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("PROPTEST_CASES").ok().and_then(|v| v.parse().ok()).unwrap_or(64),
        ..ProptestConfig::default()
    })]

    /// A mutated corpus program never panics a stage, and the checker agrees
    /// with the spec on it.
    #[test]
    fn mutated_programs_check_and_agree(
        pick in any::<usize>(),
        changes in prop::collection::vec((0..KINDS, any::<usize>(), any::<usize>()), 1..4),
    ) {
        let programs = corpus();
        prop_assume!(!programs.is_empty());
        let (name, src) = &programs[pick % programs.len()];
        let out = mutate(src, &changes);
        if let Err(e) = check_on_small_stack(name, &out) {
            prop_assert!(false, "{}", e);
        }
    }
}
