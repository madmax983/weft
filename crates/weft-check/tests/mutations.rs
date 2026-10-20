//! The checker and the spec on mutated corpus programs (QR22).
//!
//! Each case takes a program of `tests/programs` and changes a few of its
//! lines: it deletes, duplicates or swaps statements, changes a mode of a
//! function (its effect row, a `mut` place, `@ uniq` or `@ shared` on a
//! reference parameter), or puts a statement into a closure, a loop or a
//! handler. Weft has no `&mut`: the modes state what a reference can do. Each
//! mutated program goes through `check_source` on a 2 MiB thread
//! (`weft_sema::on_current_stack`). No stage may panic, and the checker and
//! the spec must agree on each body of a program that parses, also on the
//! evidence of W0301 and W0405.

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
            // Change a mode of the first function from `i` with a reference
            // parameter.
            3 => {
                let n = lines.len();
                let Some(j) = (0..n).map(|d| (i + d) % n).find(|&j| {
                    lines[j].trim_start().starts_with("fn ") && lines[j].contains(": &")
                }) else {
                    continue;
                };
                if let Some(changed) = change_mode(&lines[j], other) {
                    lines[j] = changed;
                }
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

/// Changes a mode of the function line `line`, by `how`: it drops the effect
/// row, states `mut` of the first reference parameter, or gives that
/// parameter `@ uniq` or `@ shared`. Returns `None` if the line has no place
/// for the change.
fn change_mode(line: &str, how: usize) -> Option<String> {
    // The first reference parameter: its name, and the end of its type.
    let at = line.find(": &")?;
    let start = line[..at].rfind(['(', ','])? + 1;
    let name = line[start..at].trim();
    let mut depth = 0i32;
    let mut end = None;
    for (k, c) in line[at..].char_indices() {
        match c {
            ')' | ',' if depth == 0 => {
                end = Some(at + k);
                break;
            }
            '<' | '(' | '[' => depth += 1,
            '>' | ']' | ')' => depth -= 1,
            _ => {}
        }
    }
    let end = end?;
    // The text after the parameters: the result type, the row and the body.
    let close = line[end..].find(')')? + end;
    let row = line[close..].find(" / ").map(|k| k + close);
    let body = line[close..].find(" {").map(|k| k + close)?;
    match how % 4 {
        0 => row.map(|r| format!("{}{}", &line[..r], &line[body..])),
        1 => Some(match row {
            Some(r) => format!("{} / mut({name}), {}", &line[..r], &line[r + 3..]),
            None => format!("{} / mut({name}){}", &line[..body], &line[body..]),
        }),
        m => {
            if line[at..end].contains('@') {
                return None;
            }
            let mode = if m == 2 { "uniq" } else { "shared" };
            Some(format!("{} @ {mode}{}", &line[..end], &line[end..]))
        }
    }
}

/// Checks `src` on a 2 MiB thread and compares the checker with the spec.
/// Returns the number of bodies, or an error text if a stage panics or if
/// they disagree.
fn check_on_small_stack(name: &str, src: &str) -> Result<usize, String> {
    let file = name.to_string();
    let text = src.to_string();
    let result = std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            weft_sema::on_current_stack(|| {
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
        })
        .expect("the thread starts")
        .join();
    match result {
        Ok(Ok(n)) => Ok(n),
        Ok(Err(e)) => Err(format!("{name}: {e}\n{src}")),
        Err(_) => Err(format!("{name}: a stage panics\n{src}")),
    }
}

/// The mutations of a few programs. Each kind changes the program: a
/// statement goes away, comes twice, moves, or goes into a closure, a loop or
/// a handler, or a mode of a function changes. Each kind gives a program that
/// parses for some second number, so the checker and the spec compare its
/// bodies.
#[test]
fn each_kind_of_mutation_changes_the_program() {
    let src = "fn f(v: &Vec<u64>) / mut(v) {\n    let r = &v[0]\n    v.push(1)\n    print(r)\n}\n";
    for kind in 0..KINDS {
        let (mut changed, mut bodies) = (false, 0);
        for other in 0..4 {
            let out = mutate(src, &[(kind, 1, other)]);
            changed |= out != src;
            let checked = check_on_small_stack("m.wf", &out);
            assert!(checked.is_ok(), "{out}");
            bodies += checked.unwrap_or(0);
        }
        assert!(changed, "kind {kind}: no change");
        assert!(bodies > 0, "kind {kind}: no program parses");
    }
    let modes: Vec<String> = (0..4).map(|k| mutate(src, &[(3, 0, k)])).collect();
    assert!(modes[0].starts_with("fn f(v: &Vec<u64>) {"), "{}", modes[0]);
    assert!(modes[1].contains("/ mut(v), mut(v)"), "{}", modes[1]);
    assert!(modes[2].contains("v: &Vec<u64> @ uniq)"), "{}", modes[2]);
    assert!(modes[3].contains("v: &Vec<u64> @ shared)"), "{}", modes[3]);
    let plain = "fn g(a: u64, w: &Map<u64, u64>) -> u64 { 0 }\n";
    assert_eq!(
        change_mode(plain.trim_end(), 1).as_deref(),
        Some("fn g(a: u64, w: &Map<u64, u64>) -> u64 / mut(w) { 0 }")
    );
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
