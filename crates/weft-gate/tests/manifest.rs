//! Tests of the gate manifest (plan `docs/plan/core-ir.md`, stage G1).

use std::fs;
use std::path::Path;

use weft_gate::manifest::{self, Entry, Manifest, Mode, Options, Root, Scope};

/// Writes `text` to `base/rel` and makes the parent directories.
fn put(base: &Path, rel: &str, text: &str) {
    let path = base.join(rel);
    if let Some(dir) = path.parent() {
        fs::create_dir_all(dir).expect("make the directories");
    }
    fs::write(path, text).expect("write the file");
}

fn tree(set: &str, dir: &str) -> Root {
    Root {
        set: set.to_string(),
        dir: dir.into(),
        scope: Scope::Tree,
    }
}

fn build(base: &Path, roots: &[Root], exclude_copies: bool) -> Manifest {
    manifest::build(base, roots, Options { exclude_copies }).expect("build the manifest")
}

fn paths(m: &Manifest) -> Vec<&str> {
    m.entries.iter().map(|e| e.path.as_str()).collect()
}

fn entry<'a>(m: &'a Manifest, path: &str) -> &'a Entry {
    m.entries
        .iter()
        .find(|e| e.path == path)
        .unwrap_or_else(|| panic!("no entry for {path}"))
}

#[test]
fn finds_wf_files_in_a_tree() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(base, "r/a.wf", "fn a() {}\n");
    put(base, "r/sub/deep/b.wf", "fn b() {}\n");
    put(base, "r/notes.md", "not a program\n");
    put(base, "r/c.wf.bak", "fn c() {}\n");
    put(base, "other/d.wf", "fn d() {}\n");
    let m = build(base, &[tree("r", "r")], false);
    assert_eq!(paths(&m), ["r/a.wf", "r/sub/deep/b.wf"]);
    assert_eq!(m.path_count(), 2);
    assert!(m
        .entries
        .iter()
        .all(|e| e.mode == Mode::File && e.set == "r"));
}

#[test]
fn files_scope_reads_only_the_top_of_a_directory() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(base, "top.wf", "fn t() {}\n");
    put(base, "r/below.wf", "fn b() {}\n");
    let roots = [Root {
        set: "top".to_string(),
        dir: "".into(),
        scope: Scope::Files,
    }];
    let m = build(base, &roots, true);
    assert_eq!(paths(&m), ["top.wf"]);
}

#[test]
fn a_missing_root_is_recorded_and_gives_no_entries() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let m = build(dir.path(), &[tree("probes", "tests/gate/probes")], false);
    assert!(m.entries.is_empty());
    assert_eq!(m.missing, ["tests/gate/probes"]);
}

#[test]
fn skips_copies_of_the_source_tree() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(base, "r/keep.wf", "fn keep() {}\n");
    put(base, "r/copy/Cargo.toml", "[package]\n");
    put(base, "r/copy/x.wf", "fn x() {}\n");
    put(base, "r/copy/deep/y.wf", "fn y() {}\n");
    for part in ["target", "crates", "tests", "std", "examples"] {
        put(
            base,
            &format!("r/a/{part}/z.wf"),
            &format!("fn {part}() {{}}\n"),
        );
    }
    // A name that only contains an excluded word stays.
    put(base, "r/my_tests/w.wf", "fn w() {}\n");
    let m = build(base, &[tree("r", "r")], true);
    assert_eq!(paths(&m), ["r/keep.wf", "r/my_tests/w.wf"]);

    // Without the exclusion rule (tier 1), each file stays.
    let m = build(base, &[tree("r", "r")], false);
    assert_eq!(m.entries.len(), 9);
}

#[test]
fn dedupes_by_sha256_and_keeps_the_first_path_in_sorted_order() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(base, "r/z/same.wf", "abc");
    put(base, "r/a/same.wf", "abc");
    put(base, "r/m.wf", "abc");
    put(base, "r/other.wf", "abd");
    let m = build(base, &[tree("r", "r")], false);
    assert_eq!(paths(&m), ["r/a/same.wf", "r/other.wf"]);
    let e = entry(&m, "r/a/same.wf");
    // SHA-256 of "abc" (FIPS 180-2, appendix B.1).
    assert_eq!(
        e.hash,
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    assert_eq!(e.others, ["r/m.wf", "r/z/same.wf"]);
    assert_eq!(m.path_count(), 4);
}

#[test]
fn an_earlier_root_keeps_its_path_over_a_later_root() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(base, "b/x.wf", "fn x() {}\n");
    put(base, "a/x.wf", "fn x() {}\n");
    // The root `b` comes first in the list, so its path stays.
    let m = build(base, &[tree("b", "b"), tree("a", "a")], false);
    assert_eq!(paths(&m), ["b/x.wf"]);
    assert_eq!(entry(&m, "b/x.wf").others, ["a/x.wf"]);
    assert_eq!(entry(&m, "b/x.wf").set, "b");
}

#[test]
fn marks_main_and_tests() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(
        base,
        "r/main.wf",
        "fn helper() {}\n\nfn main() {\n    helper()\n}\n",
    );
    put(
        base,
        "r/tests.wf",
        "fn f() -> Int { 1 }\n\ntest \"one\" {\n    assert(f() == 1)\n}\n",
    );
    put(base, "r/both.wf", "pub fn main() {}\ntest \"t\" {}\n");
    put(base, "r/none.wf", "fn mainly() {}\n// fn main() {}\n");
    put(
        base,
        "r/nested.wf",
        "mod m {\n    fn main() {}\n    test \"inner\" {}\n}\n",
    );
    put(base, "r/string.wf", "fn f() { print(\"fn main() {}\") }\n");
    let m = build(base, &[tree("r", "r")], false);
    let flags = |p: &str| {
        let e = entry(&m, p);
        (e.has_main, e.has_tests)
    };
    assert_eq!(flags("r/main.wf"), (true, false));
    assert_eq!(flags("r/tests.wf"), (false, true));
    assert_eq!(flags("r/both.wf"), (true, true));
    assert_eq!(flags("r/none.wf"), (false, false));
    // `main` must be in the root module; a test can be in any module.
    assert_eq!(flags("r/nested.wf"), (false, true));
    assert_eq!(flags("r/string.wf"), (false, false));
}

#[test]
fn a_directory_with_weft_toml_is_one_package_entry() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(
        base,
        "r/pkg/weft.toml",
        "[package]\nname = \"app\"\nkind = \"bin\"\n",
    );
    put(base, "r/pkg/src/main.wf", "fn main() {}\n");
    put(
        base,
        "r/pkg/deps/json/weft.toml",
        "[package]\nname = \"json\"\n",
    );
    put(base, "r/pkg/deps/json/src/lib.wf", "pub fn parse() {}\n");
    put(base, "r/loose.wf", "fn loose() {}\n");
    let m = build(base, &[tree("r", "r")], false);
    assert_eq!(paths(&m), ["r/loose.wf", "r/pkg"]);
    let p = entry(&m, "r/pkg");
    assert_eq!(p.mode, Mode::Package);
    assert!(p.has_main);
    assert!(!p.has_tests);
    assert_eq!(p.hash.len(), 64);

    // A change in a dependency changes the hash of the package.
    let before = p.hash.clone();
    put(base, "r/pkg/deps/json/src/lib.wf", "pub fn parse() { }\n");
    let m = build(base, &[tree("r", "r")], false);
    assert_ne!(entry(&m, "r/pkg").hash, before);

    // The files of a package entry.
    let files = manifest::package_files(&base.join("r/pkg")).expect("list the package");
    assert_eq!(
        files,
        [
            "deps/json/src/lib.wf",
            "deps/json/weft.toml",
            "src/main.wf",
            "weft.toml"
        ]
    );
}

#[test]
fn a_root_that_is_a_package_is_one_entry() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(
        base,
        "lib/weft.toml",
        "[package]\nname = \"lib\"\nkind = \"lib\"\n",
    );
    put(base, "lib/src/lib.wf", "pub fn f() {}\ntest \"f\" {}\n");
    let m = build(base, &[tree("examples", "lib")], false);
    assert_eq!(paths(&m), ["lib"]);
    let p = entry(&m, "lib");
    assert_eq!(
        (p.mode, p.has_main, p.has_tests),
        (Mode::Package, false, true)
    );
}

#[test]
fn identical_packages_dedupe() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    for d in ["r/p1", "r/p2"] {
        put(base, &format!("{d}/weft.toml"), "[package]\nname = \"p\"\n");
        put(base, &format!("{d}/src/main.wf"), "fn main() {}\n");
    }
    let m = build(base, &[tree("r", "r")], false);
    assert_eq!(paths(&m), ["r/p1"]);
    assert_eq!(entry(&m, "r/p1").others, ["r/p2"]);
}

#[test]
fn the_tsv_text_reads_back() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(base, "r/a b;c.wf", "fn main() {}\n");
    put(base, "r/x\\y.wf", "fn main() {}\n");
    put(base, "r/t.wf", "test \"t\" {}\n");
    put(base, "r/pkg/weft.toml", "[package]\nname = \"p\"\n");
    put(base, "r/pkg/src/main.wf", "fn main() {}\ntest \"t\" {}\n");
    let m = build(base, &[tree("r", "r")], false);
    let text = m.to_tsv();
    assert!(text.starts_with("hash\tpath\tset\tmode\thas_main\thas_tests\tother_paths\n"));
    let back = Manifest::from_tsv(&text).expect("read the manifest");
    assert_eq!(back.entries, m.entries);
    assert!(Manifest::from_tsv("hash\tpath\n").is_err());
}

#[test]
fn skips_symbolic_links() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(base, "r/real/a.wf", "fn a() {}\n");
    #[cfg(unix)]
    std::os::unix::fs::symlink(base.join("r/real"), base.join("r/link")).expect("make the link");
    let m = build(base, &[tree("r", "r")], false);
    assert_eq!(paths(&m), ["r/real/a.wf"]);
    assert!(entry(&m, "r/real/a.wf").others.is_empty());
}

#[test]
fn the_tier_roots_follow_the_plan() {
    let t1: Vec<_> = manifest::tier1_roots().into_iter().map(|r| r.set).collect();
    assert_eq!(
        t1,
        [
            "corpus",
            "interp",
            "examples",
            "packages",
            "ir_targets",
            "probes"
        ]
    );
    let t2 = manifest::tier2_roots();
    let report: Vec<_> = t2
        .iter()
        .filter(|r| r.group == manifest::Group::Report)
        .map(|r| r.root.set.as_str())
        .collect();
    assert_eq!(report, ["redteam", "specreview", "r2", "r3", "ir"]);
    let stage: Vec<_> = t2
        .iter()
        .filter(|r| r.group == manifest::Group::Stage)
        .map(|r| r.root.set.as_str())
        .collect();
    assert_eq!(
        stage,
        [
            "verify", "fix", "s2", "s2fix", "edge", "edgefix", "partb", "s5", "s5r", "s1fix", "p",
            "core", "backup", "top"
        ]
    );
}

#[test]
fn the_archive_is_reproducible_and_holds_every_path() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(base, "r/a.wf", "fn main() {}\n");
    put(base, "r/b.wf", "fn main() {}\n");
    put(base, "r/pkg/weft.toml", "[package]\nname = \"p\"\n");
    put(base, "r/pkg/src/main.wf", "fn main() {}\n");
    let m = build(base, &[tree("r", "r")], false);
    let out = tempfile::tempdir().expect("temporary directory");
    let one = out.path().join("one.tar.zst");
    let two = out.path().join("two.tar.zst");
    let h1 = weft_gate::archive::write(base, &m, &one).expect("write the archive");
    let h2 = weft_gate::archive::write(base, &m, &two).expect("write the archive");
    assert_eq!(h1, h2);
    assert_eq!(h1.len(), 64);
    let names = weft_gate::archive::list(&one).expect("read the archive");
    assert_eq!(
        names,
        [
            "manifest.tsv",
            "r/a.wf",
            "r/b.wf",
            "r/pkg/src/main.wf",
            "r/pkg/weft.toml"
        ]
    );
}

#[test]
fn the_unpacked_archive_gives_the_same_manifest() {
    let dir = tempfile::tempdir().expect("temporary directory");
    let base = dir.path();
    put(base, "r/a.wf", "fn main() {}\n");
    put(base, "r/sub/b.wf", "fn main() {}\n");
    put(base, "r/t.wf", "test \"t\" {}\n");
    put(base, "r/copy/Cargo.toml", "[package]\n");
    put(base, "r/copy/c.wf", "fn c() {}\n");
    put(base, "r/pkg/weft.toml", "[package]\nname = \"p\"\n");
    put(base, "r/pkg/src/main.wf", "fn main() {}\n");
    put(base, "top.wf", "fn top() {}\n");
    let roots = [
        tree("r", "r"),
        Root {
            set: "top".to_string(),
            dir: "".into(),
            scope: Scope::Files,
        },
    ];
    let m = build(base, &roots, true);
    let out = tempfile::tempdir().expect("temporary directory");
    let file = out.path().join("a.tar.zst");
    weft_gate::archive::write(base, &m, &file).expect("write the archive");
    let dest = out.path().join("unpacked");
    weft_gate::archive::unpack(&file, &dest).expect("unpack the archive");
    let again = build(&dest, &roots, true);
    assert_eq!(again.to_tsv(), m.to_tsv());
    let text = fs::read_to_string(dest.join("manifest.tsv")).expect("read the manifest");
    assert_eq!(text, m.to_tsv());
}

/// The repository of this crate.
fn repo() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The committed tier-1 manifest.
fn tier1() -> Manifest {
    let text = fs::read_to_string(repo().join("tests/gate/manifest-tier1.tsv"))
        .expect("read the tier-1 manifest");
    Manifest::from_tsv(&text).expect("parse the tier-1 manifest")
}

#[test]
fn the_tier1_manifest_holds_the_probes_and_controls_of_ir_10_2() {
    let m = tier1();
    let all: Vec<&str> = m.all_paths().map(|(_, p)| p).collect();
    let probes = [
        // M1 to M4.
        "work/machine/m1_post_resume.wf",
        "work/mir/postres.wf",
        "work/machine/m6b_resume_result_ref.wf",
        "work/machine/m8_abort_value_into_body.wf",
        "work/machine/m10_abort_value_callee_local.wf",
        // J1 to J6.
        "judge_sound/j1_post_resume_keep.wf",
        "judge_sound/j2_post_resume_closure.wf",
        "judge_sound/j3_resuming_clause_value.wf",
        "judge_sound/j4_multi_outer_ref.wf",
        "judge_sound/j5_kept_borrow.wf",
        "judge_sound/j5d_maker_borrow.wf",
        "judge_sound/j6_resume_temp_keep.wf",
        // map N1, N2.
        "work/map/opres.wf",
        "work/map/fnres2.wf",
        // sem N1 to N4.
        "probes/p2_late_operand_ref.wf",
        "probes/p9_print_late.wf",
        "probes/p10_index_late.wf",
        "probes/p25_assert_abort.wf",
        "probes/p27_assert_callee.wf",
        // The controls.
        "judge_sound/j5b_kept_write.wf",
        "judge_sound/j5c_kept_borrow_task.wf",
        "work/judge/p/d5_count.wf",
        "work/machine/m6_resume_result_body_local.wf",
        "work/machine/m9_resume_twice_tail.wf",
    ];
    let missing: Vec<String> = probes
        .iter()
        .map(|p| format!("tests/gate/probes/ir/{p}"))
        .filter(|p| !all.contains(&p.as_str()))
        .collect();
    assert!(
        missing.is_empty(),
        "not in the tier-1 manifest: {missing:?}"
    );
}

/// The repro paths of the tables of `docs/ir.md` §10.4. A name without `/` is in the
/// directory of the path before it in the same cell.
fn repros_of_ir_10_4() -> Vec<String> {
    let text = fs::read_to_string(repo().join("docs/ir.md")).expect("read docs/ir.md");
    let start = text.find("### 10.4 ").expect("docs/ir.md has section 10.4");
    let rest = text.get(start..).unwrap_or_default();
    let end = rest.find("\n## ").unwrap_or(rest.len());
    let mut out = Vec::new();
    for line in rest.get(..end).unwrap_or_default().lines() {
        let cells: Vec<&str> = line.split('|').map(str::trim).collect();
        // `| Id | Class | Verdict | Mechanism | Repro | Group | Claim |`: the repro is
        // cell 5 (cell 0 is the empty text before the first `|`).
        let Some(cell) = cells.get(5).filter(|_| cells.len() == 9) else {
            continue;
        };
        let mut dir = String::new();
        for (i, span) in cell.split('`').enumerate() {
            if i % 2 == 0 || Path::new(span).extension().is_none_or(|e| e != "wf") {
                continue;
            }
            let path = match span.rsplit_once('/') {
                Some((d, _)) => {
                    dir = d.to_string();
                    span.to_string()
                }
                None => format!("{dir}/{span}"),
            };
            out.push(path);
        }
    }
    out
}

/// True if the file name `name` matches `pattern`, where `*` matches any text.
fn glob(pattern: &str, name: &str) -> bool {
    match pattern.split_once('*') {
        None => pattern == name,
        Some((head, tail)) => {
            let Some(rest) = name.strip_prefix(head) else {
                return false;
            };
            (0..=rest.len()).any(|i| rest.is_char_boundary(i) && glob(tail, &rest[i..]))
        }
    }
}

#[test]
fn each_repro_of_ir_10_4_is_in_the_copy() {
    let repros = repros_of_ir_10_4();
    // 26 rows of round 2, 20 of round 3 and 14 items; some rows have two paths.
    assert!(repros.len() >= 60, "only {} repro paths", repros.len());
    let probes = repo().join("tests/gate/probes");
    let mut missing = Vec::new();
    for r in &repros {
        let (dir, name) = r.rsplit_once('/').unwrap_or(("", r));
        let found = fs::read_dir(probes.join(dir)).is_ok_and(|rd| {
            rd.filter_map(Result::ok)
                .any(|e| glob(name, &e.file_name().to_string_lossy()))
        });
        if !found {
            missing.push(r.clone());
        }
    }
    assert!(missing.is_empty(), "not in tests/gate/probes: {missing:?}");
}

#[test]
fn the_committed_tier1_manifest_is_current() {
    let fresh = manifest::build(
        &repo(),
        &manifest::tier1_roots(),
        Options {
            exclude_copies: false,
        },
    )
    .expect("build the tier-1 manifest");
    assert!(
        fresh.missing.is_empty(),
        "missing roots: {:?}",
        fresh.missing
    );
    assert_eq!(
        fresh.to_tsv(),
        tier1().to_tsv(),
        "run `cargo run -p weft-gate -- manifest --tier 1`"
    );
    let sets = |s: &str| fresh.entries.iter().filter(|e| e.set == s).count();
    assert_eq!(sets("ir_targets"), 6);
    assert!(sets("probes") > 3000, "{} probes", sets("probes"));
}
