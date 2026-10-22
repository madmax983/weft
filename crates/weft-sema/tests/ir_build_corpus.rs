//! The IR of each program of the corpus (plan stage B12).
//!
//! Each program in `tests/programs/` has the text of its IR in
//! `tests/ir_corpus/<name>.ir`. The test builds the IR of each program, runs the
//! verifier on it, and compares the text. Set `UPDATE_IR=1` to write the `.ir`
//! files again; then read each changed file against `docs/ir.md` section 5
//! before you commit it.
//!
//! The gate test `crates/weft-gate/tests/thir.rs` builds and verifies the IR of
//! each program of tier 1 (the corpus is a part of it); `weft-gate ir-build`
//! does the same with a release build, on tier 1 or tier 2.

use std::path::{Path, PathBuf};

use weft_sema::irbuild::{self, Outcome};
use weft_sema::{analyze_source, Options};

/// The programs of the corpus.
fn corpus() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut v: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    v.sort();
    v
}

/// The directory of the `.ir` files.
fn ir_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/ir_corpus")
}

/// Returns the line and the column of byte `at` of `src`.
fn line_col(src: &str, at: u32) -> String {
    let at = usize::try_from(at).unwrap_or(usize::MAX).min(src.len());
    let before = &src[..at];
    let line = before.matches('\n').count() + 1;
    let col = at - before.rfind('\n').map_or(0, |i| i + 1) + 1;
    format!("{line}:{col}")
}

/// Returns the text of the IR of program `p`, after a check that the IR breaks
/// no rule and that the builder lowers each body or gives a reason for no IR.
fn ir_text(p: &Path) -> String {
    let src = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
    let Ok(a) = analyze_source(&src, Options::from_markers(&src)) else {
        return "// the program does not parse\n".to_string();
    };
    let b = irbuild::build(&a);
    assert!(
        b.broken.is_empty(),
        "{}: the IR breaks rules:\n{}",
        p.display(),
        b.broken
            .iter()
            .map(|x| format!("  {x}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    for e in &b.entries {
        assert!(
            !matches!(e.outcome, Outcome::Unsupported(_)),
            "{}: {} is unsupported",
            p.display(),
            e.name
        );
    }
    irbuild::text(&b, &|_, s| line_col(&src, s.lo))
}

#[test]
fn the_ir_of_each_corpus_program_is_its_golden_text() {
    let programs = corpus();
    assert!(
        programs.len() > 100,
        "the corpus has {} programs",
        programs.len()
    );
    let dir = ir_dir();
    let update = std::env::var_os("UPDATE_IR").is_some_and(|v| v == "1");
    if update {
        std::fs::create_dir_all(&dir).unwrap_or_else(|e| panic!("make {}: {e}", dir.display()));
    }
    let mut differ = Vec::new();
    let mut names = Vec::new();
    for p in &programs {
        let name = p
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or_else(|| panic!("a bad name: {}", p.display()))
            .to_string();
        let text = ir_text(p);
        let ir = dir.join(format!("{name}.ir"));
        names.push(format!("{name}.ir"));
        if update {
            std::fs::write(&ir, &text).unwrap_or_else(|e| panic!("write {}: {e}", ir.display()));
            continue;
        }
        let want = std::fs::read_to_string(&ir).unwrap_or_default();
        if want != text {
            differ.push(name);
        }
    }
    assert!(
        differ.is_empty(),
        "the IR of {} corpus programs differs from tests/ir_corpus (set UPDATE_IR=1 to write it, then review the diff): {}",
        differ.len(),
        differ.join(", ")
    );
    // Each `.ir` file belongs to a program of the corpus.
    let mut stale: Vec<String> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .filter_map(|e| e.ok().map(|e| e.file_name().to_string_lossy().into_owned()))
        .filter(|f| !names.contains(f))
        .collect();
    stale.sort();
    assert!(
        stale.is_empty(),
        "files of tests/ir_corpus with no program: {stale:?}"
    );
}
