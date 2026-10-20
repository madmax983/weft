//! Tests of the copy of the hand probes and of the default tier-2 root (plan
//! `docs/plan/core-ir.md`, stage G2).

use std::fs;
use std::path::Path;

use weft_gate::archive;
use weft_gate::copy;
use weft_gate::manifest::{self, Options};

/// Writes `text` to `base/rel` and makes the parent directories.
fn put(base: &Path, rel: &str, text: &str) {
    let path = base.join(rel);
    if let Some(dir) = path.parent() {
        fs::create_dir_all(dir).expect("make the directories");
    }
    fs::write(path, text).expect("write the file");
}

/// A small scratch tree with one example of each rule of plan §2.2.
fn scratch(base: &Path) {
    // Whole directories.
    put(base, "redteam/a01.wf", "fn a01() {}\n");
    put(base, "redteam/pkg/weft.toml", "[package]\nname = \"p\"\n");
    put(base, "redteam/pkg/src/main.wf", "fn main() {}\n");
    put(base, "redteam/pkg/notes.txt", "not a program\n");
    put(base, "redteam/notes.md", "not a program\n");
    put(base, "specreview/progs/s1.wf", "fn s1() {}\n");
    put(base, "specreview/other/s2.wf", "fn s2() {}\n");
    // Named directories below r2 and r3, at any depth.
    put(base, "r2/oracle/repro/OR1.wf", "fn or1() {}\n");
    put(base, "r2/oracle/fp3/fp.wf", "fn fp() {}\n");
    put(base, "r2/oracle/other/x.wf", "fn other() {}\n");
    put(base, "r2/oracle/runs/p/gen.wf", "fn generated() {}\n");
    put(base, "r2/oracle/seeds/s.wf", "fn seed() {}\n");
    put(base, "r2/oracle/weft-inst/Cargo.toml", "[package]\n");
    put(base, "r2/oracle/weft-inst/p/copy.wf", "fn copy() {}\n");
    put(base, "r3/triage/t.wf", "fn t() {}\n");
    put(base, "r3/interp/probe/b6/deep.wf", "fn deep() {}\n");
    put(base, "r3/interp/probe/fuzzout/f.wf", "fn fuzz() {}\n");
    put(
        base,
        "r3/redteam/pkgA/weft.toml",
        "[package]\nname = \"a\"\n",
    );
    put(base, "r3/redteam/pkgA/src/lib.wf", "pub fn a() {}\n");
    put(base, "r3/fidelity/x.wf", "fn not_named() {}\n");
    // The IR design: the judge traces come too.
    put(base, "ir/probes/p2.wf", "fn p2() {}\n");
    put(base, "ir/judge_sound/j1.wf", "fn j1() {}\n");
    put(base, "ir/judge_sound/j1.dl", "edge(1, 2).\n");
    put(base, "ir/judge_sound/run_all.sh", "#!/bin/sh\n");
    put(base, "ir/judge_sound/notes.md", "no\n");
    put(base, "ir/work/other/o.wf", "fn o() {}\n");
    // Stage roots.
    put(base, "verify/partb/S3/p/v1.wf", "fn v1() {}\n");
    put(base, "verify/review/rt1/v2.wf", "fn v2() {}\n");
    put(base, "verify/review/b6/v3.wf", "fn v3() {}\n");
    put(base, "verify/quality/gen/p/v4.wf", "fn v4() {}\n");
    put(base, "fix/f1.wf", "fn f1() {}\n");
    put(base, "fix/base/Cargo.toml", "[package]\n");
    put(base, "fix/base/tests/programs/x.wf", "fn x() {}\n");
    put(base, "s2/a/tests/t.wf", "fn tests_copy() {}\n");
    put(base, "core/big.wf", &"// x\n".repeat(70_000));
    put(base, "core/dup.wf", "fn same_as_the_corpus() {}\n");
    put(base, "top.wf", "fn top() {}\n");
    put(base, "backup/b.wf", "fn backup() {}\n");
}

/// A small repository with one corpus program.
fn repo(base: &Path) {
    put(base, "tests/programs/01.wf", "fn same_as_the_corpus() {}\n");
    put(
        base,
        "docs/plan/core-ir-inputs/reviews/round1a_results.json",
        "{\"S3: verify probe\": \"see SCRATCH/verify/partb/S3/p/v1.wf\", \
         \"Other\": \"SCRATCH/verify/partbx/no.wf\"}\n",
    );
}

#[test]
fn select_follows_the_rules_of_the_plan() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    scratch(base);
    let sel = copy::select(base).expect("select the probes");
    assert_eq!(
        sel.files,
        [
            "core/dup.wf",
            "fix/f1.wf",
            "ir/judge_sound/j1.dl",
            "ir/judge_sound/j1.wf",
            "ir/judge_sound/run_all.sh",
            "ir/probes/p2.wf",
            "r2/oracle/fp3/fp.wf",
            "r2/oracle/repro/OR1.wf",
            "r3/interp/probe/b6/deep.wf",
            "r3/triage/t.wf",
            "redteam/a01.wf",
            "specreview/progs/s1.wf",
            "verify/partb/S3/p/v1.wf",
            "verify/review/rt1/v2.wf",
        ]
    );
    assert_eq!(sel.packages, ["r3/redteam/pkgA", "redteam/pkg"]);
    assert_eq!(sel.large, ["core/big.wf"]);
    assert!(sel.dirs.contains(&"r2/oracle/repro".to_string()));
    assert!(sel.dirs.contains(&"verify/review/rt1".to_string()));
    assert!(!sel.dirs.iter().any(|d| d.contains("runs")));
}

#[test]
fn copy_keeps_the_paths_dedupes_and_writes_the_sources() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path().join("scratch");
    let repo_dir = dir.path().join("repo");
    scratch(&base);
    repo(&repo_dir);
    let report = copy::copy_probes(&base, &repo_dir).expect("copy the probes");
    let out = repo_dir.join(copy::PROBES_DIR);
    assert!(out.join("r2/oracle/repro/OR1.wf").is_file());
    assert!(out.join("ir/judge_sound/j1.dl").is_file());
    assert!(out.join("redteam/pkg/weft.toml").is_file());
    assert!(out.join("redteam/pkg/src/main.wf").is_file());
    assert!(!out.join("redteam/pkg/notes.txt").exists());
    assert!(!out.join("core/big.wf").exists());
    // The corpus has the same text.
    assert!(!out.join("core/dup.wf").exists());
    assert_eq!(
        report.deduped,
        [(
            "core/dup.wf".to_string(),
            "tests/programs/01.wf".to_string()
        )]
    );
    assert_eq!(report.files, 13);
    assert_eq!(report.packages, 2);

    let sources = fs::read_to_string(out.join(copy::SOURCES_NAME)).expect("read SOURCES.md");
    assert!(sources.contains("| `verify/partb/S3/p` |"));
    assert!(sources.contains("S3: verify probe"));
    assert!(!sources.contains("Other"));
    assert!(sources.contains("`core/dup.wf`"));
    assert!(sources.contains("`core/big.wf`"));

    // A second run gives the same tree.
    let again = copy::copy_probes(&base, &repo_dir).expect("copy the probes again");
    assert_eq!(again, report);
    let text = fs::read_to_string(out.join(copy::SOURCES_NAME)).expect("read SOURCES.md");
    assert_eq!(text, sources);
}

/// Writes a small archive and its hash into the repository `repo`, as stage G1 did.
fn committed_archive(repo: &Path) -> String {
    let probes = repo.join("src-probes");
    put(&probes, "r2/a.wf", "fn main() {}\n");
    put(&probes, "top.wf", "fn top() {}\n");
    let tier: Vec<_> = manifest::tier2_roots()
        .into_iter()
        .map(|t| t.root)
        .collect();
    let m = manifest::build(
        &probes,
        &tier,
        Options {
            exclude_copies: true,
        },
    )
    .expect("build the manifest");
    let file = repo.join(archive::COMMITTED_ARCHIVE);
    let hash = archive::write(&probes, &m, &file).expect("write the archive");
    put(
        repo,
        archive::COMMITTED_HASH,
        &format!("{hash}  probes-tier2.tar.zst\n"),
    );
    hash
}

#[test]
fn the_default_tier2_root_is_the_unpacked_committed_archive() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let repo_dir = dir.path();
    committed_archive(repo_dir);
    let root = archive::default_probes(repo_dir).expect("unpack the archive");
    assert_eq!(root, repo_dir.join(archive::UNPACKED_DIR));
    assert!(root.join("r2/a.wf").is_file());
    assert!(root.join("top.wf").is_file());

    // A second call does not unpack again: a change in the tree stays.
    put(&root, "r2/a.wf", "changed\n");
    let again = archive::default_probes(repo_dir).expect("use the unpacked archive");
    assert_eq!(again, root);
    assert_eq!(
        fs::read_to_string(root.join("r2/a.wf")).expect("read"),
        "changed\n"
    );

    // A new committed hash unpacks again, after the hash check.
    put(
        repo_dir,
        archive::COMMITTED_HASH,
        &format!("{}  probes-tier2.tar.zst\n", "0".repeat(64)),
    );
    let err = archive::default_probes(repo_dir).expect_err("the hash is wrong");
    assert!(err.to_string().contains("SHA-256"), "{err}");
}

#[test]
fn a_flag_or_the_environment_names_another_tier2_root() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let repo_dir = dir.path();
    let flag = repo_dir.join("flag");
    let env = repo_dir.join("env");
    let got = archive::probes_root(repo_dir, Some(flag.clone()), Some(env.clone().into()))
        .expect("the flag");
    assert_eq!(got, flag);
    let got = archive::probes_root(repo_dir, None, Some(env.clone().into())).expect("the env");
    assert_eq!(got, env);
    // With neither, the root is the committed archive, which this repository does
    // not have.
    assert!(archive::probes_root(repo_dir, None, None).is_err());
    committed_archive(repo_dir);
    let got = archive::probes_root(repo_dir, None, None).expect("the archive");
    assert_eq!(got, repo_dir.join(archive::UNPACKED_DIR));
}
