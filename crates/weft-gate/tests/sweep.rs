//! Tests of the fresh sweep (plan `docs/plan/core-ir.md`, stage C2).
//!
//! The end-to-end test runs `weft-gate sweep --n 20 --seed-base 1` with the
//! generators of `tools/gate/gen`. It needs `python3`.

use std::path::{Path, PathBuf};
use std::process::Command;

use weft_gate::sweep::{self, GENERATORS};

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn gate() -> Command {
    Command::new(env!("CARGO_BIN_EXE_weft-gate"))
}

#[test]
fn shares_divide_the_programs_among_the_generators() {
    let gens: Vec<String> = GENERATORS.iter().map(ToString::to_string).collect();
    let s = sweep::shares(22, &gens);
    let counts: Vec<usize> = s.iter().map(|x| x.1).collect();
    assert_eq!(counts, vec![5, 5, 4, 4, 4]);
    assert_eq!(s.iter().map(|x| x.1).sum::<usize>(), 22);
    // A generator with no program is not in the list.
    assert_eq!(sweep::shares(2, &gens).len(), 2);
}

#[test]
fn only_the_known_generators_are_accepted() {
    let g = sweep::parse_generators("gen4, gen3,gen4").expect("known names");
    assert_eq!(g, vec!["gen4".to_string(), "gen3".to_string()]);
    assert!(sweep::parse_generators("gen3,../../x").is_err());
    assert!(sweep::parse_generators("").is_err());
}

#[test]
fn a_signal_is_a_text_of_the_review_scripts() {
    assert!(sweep::is_signal(
        "seed 1, workers 1: fault: a value is used after it was moved at p.wf:3:5"
    ));
    assert!(sweep::is_signal(
        "seed 2, workers 4: fault: oracle: read of a freed cell"
    ));
    assert!(!sweep::is_signal(
        "seed 1, workers 1: fault: no `match` arm matches the value"
    ));
}

#[test]
fn each_generator_gives_the_same_program_for_the_same_seed() {
    let dir = tempfile::tempdir().expect("temporary directory");
    for g in GENERATORS {
        let a = dir.path().join(format!("{g}-a"));
        let b = dir.path().join(format!("{g}-b"));
        let one = sweep::generate(&repo(), Path::new("python3"), g, 7, 3, &a).expect("generate");
        let two = sweep::generate(&repo(), Path::new("python3"), g, 7, 3, &b).expect("generate");
        assert_eq!(one.len(), 3, "{g}: {one:?}");
        assert_eq!(one, two, "{g}");
        assert_eq!(one.iter().map(|x| x.0).collect::<Vec<_>>(), vec![7, 8, 9]);
        for (_, file) in &one {
            let x = std::fs::read_to_string(a.join(file)).expect("read");
            let y = std::fs::read_to_string(b.join(file)).expect("read");
            assert_eq!(x, y, "{g}: {file}");
            assert!(x.contains("fn "), "{g}: {file}");
        }
    }
}

#[test]
fn oracle_run_stops_after_the_runs_of_the_flag() {
    let data = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
    let out = gate()
        .args([
            "oracle-run",
            "--path",
            "clean.wf",
            "--runs",
            "2",
            "--engine",
            "ir",
        ])
        .arg("--base")
        .arg(&data)
        .output()
        .expect("run weft-gate");
    let text = String::from_utf8_lossy(&out.stdout);
    let steps = text.lines().filter(|l| l.starts_with("@oracle")).count();
    assert_eq!(steps, 2, "{text}");
}

#[test]
fn sweep_of_20_programs_runs_end_to_end() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let out_dir = dir.path().join("sweep");
    let out = gate()
        .args(["sweep", "--n", "20", "--seed-base", "1", "--workers", "2"])
        .arg("--out")
        .arg(&out_dir)
        .arg("--repo")
        .arg(repo())
        .output()
        .expect("run weft-gate");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    // 0: nothing kept; 1: a program kept. 2 is an error of the tool.
    assert!(
        matches!(out.status.code(), Some(0 | 1)),
        "{}\n{stdout}\n{stderr}",
        out.status
    );
    let rows = std::fs::read_to_string(out_dir.join("programs.tsv")).expect("seed list");
    let mut lines = rows.lines();
    assert_eq!(lines.next(), Some(sweep::ROWS_HEADER));
    let rows: Vec<Vec<&str>> = lines.map(|l| l.split('\t').collect()).collect();
    assert_eq!(rows.len(), 20, "{rows:?}");
    for g in GENERATORS {
        let seeds: Vec<&str> = rows
            .iter()
            .filter(|r| r.first() == Some(&g))
            .filter_map(|r| r.get(1).copied())
            .collect();
        assert_eq!(seeds, vec!["1", "2", "3", "4"], "{g}");
    }
    // Each row has a result, and the oracle ran on each accepted program.
    for r in &rows {
        assert_eq!(r.len(), 8, "{r:?}");
        let ir = r.get(4).copied().unwrap_or_default();
        let verdict = r.get(6).copied().unwrap_or_default();
        assert!(!ir.is_empty(), "{r:?}");
        if ir == "accept" {
            assert_ne!(verdict, "-", "{r:?}");
        }
    }
    let report = std::fs::read_to_string(out_dir.join("report.md")).expect("report");
    assert!(report.contains("| all |"), "{report}");
    assert!(report.contains("| gen3 | 1 to 4 | 4 |"), "{report}");
    // The temporary programs are gone; the kept programs are there.
    assert!(!out_dir.join("tmp").exists());
    let kept = std::fs::read_dir(out_dir.join("kept"))
        .expect("kept")
        .count();
    assert_eq!(kept > 0, out.status.code() == Some(1), "{report}");
}
