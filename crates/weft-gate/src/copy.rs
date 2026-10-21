//! The copy of the hand probes into the repository (plan §2.2, stage G2).
//!
//! [`select`] finds the hand probes below the scratch root: the directories of plan
//! §2.2, without the generated sets, the copies of the repository and the files
//! larger than [`MAX_PROBE_BYTES`]. [`copy_probes`] copies them into [`PROBES_DIR`]
//! with the same relative paths, skips each program whose text is in a repository
//! set, and writes [`SOURCES_NAME`].

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use sha2::{Digest, Sha256};

use crate::manifest::{
    self, hex, is_real_dir, is_wf, join_rel, package_files, package_hash, read_dir_sorted,
    root_is_excluded, Kind, Options, EXCLUDED_COMPONENTS,
};
use crate::Error;

/// The directory of the hand probes, relative to the repository.
pub const PROBES_DIR: &str = "tests/gate/probes";

/// The name of the file that gives the origin of each directory of the copy.
pub const SOURCES_NAME: &str = "SOURCES.md";

/// A file larger than this number of bytes stays in tier 2 only.
pub const MAX_PROBE_BYTES: u64 = 256 * 1024;

/// The names of the hand directories below `r2/` and `r3/`.
const ROUND_NAMES: [&str; 18] = [
    "p", "probe", "probes", "repro", "r2probes", "fp", "fp2", "fp3", "min", "sanity", "b6",
    "crash", "cli", "big", "lib", "pkgA", "pkgB", "triage",
];

/// The names of the hand directories below `verify/`.
const VERIFY_NAMES: [&str; 4] = ["p", "probes", "repro", "rt1"];

/// The patterns of the generated sets. A `*` matches any text.
const GENERATED: [&str; 11] = [
    "runs", "seeds*", "sweep*", "t0", "gen*", "fuzz*", "fz*", "mut*", "effmut_*", "genout",
    "fuzzout",
];

/// Generated directories that the patterns do not name, relative to the scratch root.
const GENERATED_DIRS: [&str; 1] = ["verify/quality/gen"];

/// The directories of the IR design. The second item gives the patterns of the other
/// files to copy from the top of the directory (the judge traces).
const IR_DIRS: [(&str, &[&str]); 6] = [
    ("ir/probes", &[]),
    ("ir/work/map", &[]),
    ("ir/work/machine", &[]),
    ("ir/work/mir", &[]),
    ("ir/judge_sound", &["*.dl", "run_all.sh"]),
    ("ir/work/judge/p", &[]),
];

/// The stage roots that the copy takes as a whole.
const STAGE_DIRS: [&str; 11] = [
    "fix", "s2", "s2fix", "edge", "edgefix", "partb", "s5", "s5r", "s1fix", "p", "core",
];

/// The stage results that name the verifier repros, in
/// `docs/plan/core-ir-inputs/reviews/`.
const RESULTS: [&str; 3] = [
    "round1a_results.json",
    "round1b_results.json",
    "round2_results.json",
];

/// The directory of the review records, relative to the repository.
const REVIEWS_DIR: &str = "docs/plan/core-ir-inputs/reviews";

/// The hand probes below a scratch root.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Selection {
    /// The selected directories, in the order of plan §2.2.
    pub dirs: Vec<String>,
    /// The files outside packages: the `.wf` files and the judge traces, in sorted
    /// order.
    pub files: Vec<String>,
    /// The package directories, in sorted order.
    pub packages: Vec<String>,
    /// The `.wf` files larger than [`MAX_PROBE_BYTES`], in sorted order.
    pub large: Vec<String>,
}

/// The result of [`copy_probes`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Report {
    /// The selection.
    pub selection: Selection,
    /// The number of files that the copy wrote outside packages.
    pub files: usize,
    /// The number of packages that the copy wrote.
    pub packages: usize,
    /// The number of bytes that the copy wrote (also the package files).
    pub bytes: u64,
    /// The probes that the copy skipped because a repository set has the same text:
    /// the probe path and the repository path.
    pub deduped: Vec<(String, String)>,
}

/// True if `name` matches `pattern`. A `*` in the pattern matches any text.
fn glob(pattern: &str, name: &str) -> bool {
    match pattern.split_once('*') {
        None => pattern == name,
        Some((head, tail)) => name.strip_prefix(head).is_some_and(|rest| {
            rest.char_indices()
                .map(|(i, _)| i)
                .chain(std::iter::once(rest.len()))
                .any(|i| rest.get(i..).is_some_and(|r| glob(tail, r)))
        }),
    }
}

/// True if the walk must not go into the directory `rel` (with the last component
/// `name`): a generated set or a copy of the repository.
fn skipped_dir(rel: &str, name: &str) -> bool {
    EXCLUDED_COMPONENTS.contains(&name)
        || GENERATED.iter().any(|g| glob(g, name))
        || GENERATED_DIRS.contains(&rel)
}

/// Finds the hand probes below the scratch root `base` (plan §2.2).
pub fn select(base: &Path) -> Result<Selection, Error> {
    let mut sel = Selection::default();
    let mut tops: Vec<(String, &[&str])> = vec![
        ("redteam".to_string(), &[]),
        ("specreview/progs".to_string(), &[]),
    ];
    for round in ["r2", "r3"] {
        for d in find_named(base, round, &ROUND_NAMES)? {
            tops.push((d, &[]));
        }
    }
    for (d, extras) in IR_DIRS {
        tops.push((d.to_string(), extras));
    }
    for d in find_named(base, "verify", &VERIFY_NAMES)? {
        tops.push((d, &[]));
    }
    for d in STAGE_DIRS {
        tops.push((d.to_string(), &[]));
    }
    for (dir, extras) in tops {
        let full = base.join(&dir);
        if !is_real_dir(&full) || root_is_excluded(base, Path::new(&dir)) {
            continue;
        }
        take(&full, &dir, extras, true, &mut sel)?;
        sel.dirs.push(dir);
    }
    sel.files.sort();
    sel.files.dedup();
    sel.packages.sort();
    sel.packages.dedup();
    sel.large.sort();
    sel.large.dedup();
    Ok(sel)
}

/// Finds each directory below `base/rel` whose name is in `names`. The search does
/// not go into a found directory, a package, a copy of the repository or a
/// generated set.
fn find_named(base: &Path, rel: &str, names: &[&str]) -> Result<Vec<String>, Error> {
    fn go(full: &Path, rel: &str, names: &[&str], out: &mut Vec<String>) -> Result<(), Error> {
        if full.join("Cargo.toml").is_file() || full.join("weft.toml").is_file() {
            return Ok(());
        }
        for (name, kind) in read_dir_sorted(full)? {
            let child = join_rel(rel, &name);
            if kind != Kind::Dir || skipped_dir(&child, &name) {
                continue;
            }
            if names.contains(&name.as_str()) {
                out.push(child);
            } else {
                go(&full.join(&name), &child, names, out)?;
            }
        }
        Ok(())
    }
    let mut out = Vec::new();
    let full = base.join(rel);
    if is_real_dir(&full) {
        go(&full, rel, names, &mut out)?;
    }
    Ok(out)
}

/// Adds the programs below the directory `full` (the path `rel`) to `sel`. At the
/// top of the directory, a file that matches a pattern of `extras` comes too.
fn take(
    full: &Path,
    rel: &str,
    extras: &[&str],
    top: bool,
    sel: &mut Selection,
) -> Result<(), Error> {
    if full.join("weft.toml").is_file() {
        sel.packages.push(rel.to_string());
        return Ok(());
    }
    if full.join("Cargo.toml").is_file() {
        return Ok(());
    }
    for (name, kind) in read_dir_sorted(full)? {
        let child = join_rel(rel, &name);
        let path = full.join(&name);
        match kind {
            Kind::Dir if !skipped_dir(&child, &name) => take(&path, &child, extras, false, sel)?,
            Kind::File if is_wf(&name) => {
                let len = fs::metadata(&path).map_err(|e| Error::io(&path, e))?.len();
                if len > MAX_PROBE_BYTES {
                    sel.large.push(child);
                } else {
                    sel.files.push(child);
                }
            }
            Kind::File if top && extras.iter().any(|g| glob(g, &name)) => sel.files.push(child),
            _ => {}
        }
    }
    Ok(())
}

/// Copies the hand probes from the scratch root `base` into [`PROBES_DIR`] of the
/// repository `repo`, and writes [`SOURCES_NAME`].
///
/// The copy keeps the relative paths. It skips a `.wf` file or a package whose text
/// is in a repository set of tier 1. It does not remove other files of
/// [`PROBES_DIR`] (for example the repros of the fixes, plan rule 6).
pub fn copy_probes(base: &Path, repo: &Path) -> Result<Report, Error> {
    let selection = select(base)?;
    let in_repo = repository_hashes(repo)?;
    let out = repo.join(PROBES_DIR);
    let mut report = Report::default();
    for rel in &selection.files {
        let from = base.join(rel);
        let bytes = fs::read(&from).map_err(|e| Error::io(&from, e))?;
        if is_wf(rel) {
            if let Some(path) = in_repo.get(&hex(&Sha256::digest(&bytes))) {
                report.deduped.push((rel.clone(), path.clone()));
                continue;
            }
        }
        write(&out.join(rel), &bytes)?;
        report.files += 1;
        report.bytes += bytes.len() as u64;
    }
    for rel in &selection.packages {
        let from = base.join(rel);
        if let Some(path) = in_repo.get(&package_hash(&from)?) {
            report.deduped.push((rel.clone(), path.clone()));
            continue;
        }
        for file in package_files(&from)? {
            let src = from.join(&file);
            let bytes = fs::read(&src).map_err(|e| Error::io(&src, e))?;
            write(&out.join(rel).join(&file), &bytes)?;
            report.bytes += bytes.len() as u64;
        }
        report.packages += 1;
    }
    report.deduped.sort();
    let mentions = mentions(&repo.join(REVIEWS_DIR), &selection.dirs)?;
    let sources = out.join(SOURCES_NAME);
    let text = sources_text(&selection, &report, &mentions);
    write(&sources, text.as_bytes())?;
    report.selection = selection;
    Ok(report)
}

/// The hashes of the programs of the repository sets of tier 1 (not the probes),
/// with the path of each.
fn repository_hashes(repo: &Path) -> Result<HashMap<String, String>, Error> {
    let roots: Vec<_> = manifest::tier1_roots()
        .into_iter()
        .filter(|r| r.dir != Path::new(PROBES_DIR))
        .collect();
    let m = manifest::build(
        repo,
        &roots,
        Options {
            exclude_copies: false,
        },
    )?;
    Ok(m.entries
        .into_iter()
        .map(|e| (e.hash, e.path))
        .collect::<HashMap<_, _>>())
}

fn write(path: &Path, bytes: &[u8]) -> Result<(), Error> {
    if let Some(dir) = path.parent() {
        fs::create_dir_all(dir).map_err(|e| Error::io(dir, e))?;
    }
    fs::write(path, bytes).map_err(|e| Error::io(path, e))
}

/// For each directory of `dirs`, the stage results and their keys that name a path
/// in the directory (`SCRATCH/<dir>` and then a character that is not part of a
/// name). A missing results file names nothing.
fn mentions(
    reviews: &Path,
    dirs: &[String],
) -> Result<BTreeMap<String, Vec<(String, String)>>, Error> {
    let mut out: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
    for name in RESULTS {
        let path = reviews.join(name);
        let Ok(text) = fs::read_to_string(&path) else {
            continue;
        };
        let value: serde_json::Value = serde_json::from_str(&text).map_err(|e| Error::Syntax {
            line: e.line(),
            message: format!("{}: {e}", path.display()),
        })?;
        let Some(map) = value.as_object() else {
            continue;
        };
        for (key, v) in map {
            let body = v.to_string();
            for dir in dirs {
                if names_dir(&body, dir) {
                    out.entry(dir.clone())
                        .or_default()
                        .push((name.to_string(), key.clone()));
                }
            }
        }
    }
    Ok(out)
}

/// True if `text` has `SCRATCH/<dir>` and then a character that cannot continue a
/// directory name, or the end of the text. A `.` continues the name only if a letter
/// or a digit comes after it (`p.wf` is a file, but `p.` ends a sentence).
fn names_dir(text: &str, dir: &str) -> bool {
    let needle = format!("SCRATCH/{dir}");
    let name_char = |c: char| c.is_alphanumeric() || matches!(c, '_' | '-');
    text.match_indices(&needle).any(|(i, _)| {
        let mut rest = text.get(i + needle.len()..).unwrap_or_default().chars();
        match rest.next() {
            None => true,
            Some('.') => !rest.next().is_some_and(char::is_alphanumeric),
            Some(c) => !name_char(c),
        }
    })
}

/// The origin of the directory `dir` of the copy.
fn origin(dir: &str) -> String {
    let mut parts = dir.split('/');
    let first = parts.next().unwrap_or_default();
    let second = parts.next().unwrap_or_default();
    match first {
        "redteam" => "round 1 red team (`reviews/redteam_review.md`)".to_string(),
        "specreview" => "round 1 spec review (`reviews/spec_review.md`)".to_string(),
        "r2" | "r3" => {
            let n = if first == "r2" { 2 } else { 3 };
            match second {
                "fidelity" | "interp" | "oracle" | "quality" | "redteam" | "issues" => {
                    format!("round {n} report (`reviews/{first}/{second}.md`)")
                }
                _ => format!("round {n} ({second})"),
            }
        }
        "ir" => "IR design (`docs/ir.md`)".to_string(),
        "verify" => "stage verifier (rounds 1 and 2)".to_string(),
        _ => format!("stage root `{first}` (rounds 1 and 2)"),
    }
}

/// The text of [`SOURCES_NAME`].
fn sources_text(
    sel: &Selection,
    report: &Report,
    mentions: &BTreeMap<String, Vec<(String, String)>>,
) -> String {
    let deduped: Vec<&str> = report.deduped.iter().map(|(p, _)| p.as_str()).collect();
    let mut t = String::new();
    t.push_str("# Sources of the hand probes\n\n");
    t.push_str(
        "Stage G2 of `docs/plan/core-ir.md` copied these probes from `SCRATCH`, the scratch\n\
         directory of the session that made the plan (plan §2.2). The command\n\
         `cargo run -p weft-gate -- copy-probes --probes DIR` makes the copy again and\n\
         writes this file. Each path below is relative to `SCRATCH`, and the copy has the\n\
         same path below `tests/gate/probes/`. `reviews/` is\n\
         `docs/plan/core-ir-inputs/reviews/`.\n\n\
         The copy has the `.wf` files, the packages (a directory with `weft.toml`, with its\n\
         `.wf` files) and the judge traces (`ir/judge_sound/*.dl`, `run_all.sh`). It does not\n\
         have the generated sets, the copies of the repository, the files larger than\n\
         256 KB, and the programs whose text is in a repository set. Tier 2 has all of them.\n\n",
    );
    let _ = writeln!(
        t,
        "Totals: {} directories, {} files, {} packages.\n",
        sel.dirs.len(),
        report.files,
        report.packages
    );
    t.push_str("## Directories\n\n");
    t.push_str("| Directory | Files | Packages | Origin | Named in the stage results |\n");
    t.push_str("| --- | --- | --- | --- | --- |\n");
    for dir in &sel.dirs {
        let below = |p: &&String| {
            p.starts_with(dir.as_str()) && p.get(dir.len()..dir.len() + 1) == Some("/")
        };
        let files = sel
            .files
            .iter()
            .filter(below)
            .filter(|p| !deduped.contains(&p.as_str()))
            .count();
        let packages = sel
            .packages
            .iter()
            .filter(|p| *p == dir || below(p))
            .filter(|p| !deduped.contains(&p.as_str()))
            .count();
        let named = mentions.get(dir).map_or_else(String::new, |list| {
            let mut by_file: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
            for (file, key) in list {
                by_file.entry(file).or_default().push(key);
            }
            by_file
                .iter()
                .map(|(file, keys)| format!("`{file}`: {}", keys.join("; ")))
                .collect::<Vec<_>>()
                .join("<br>")
        });
        let _ = writeln!(
            t,
            "| `{dir}` | {files} | {packages} | {} | {} |",
            origin(dir),
            named.replace('|', "\\|")
        );
    }
    t.push_str("\n## Same text as a repository program\n\n");
    if report.deduped.is_empty() {
        t.push_str("None.\n");
    } else {
        t.push_str("| Probe | Repository program |\n| --- | --- |\n");
        for (p, r) in &report.deduped {
            let _ = writeln!(t, "| `{p}` | `{r}` |");
        }
    }
    t.push_str("\n## Larger than 256 KB (tier 2 only)\n\n");
    if sel.large.is_empty() {
        t.push_str("None.\n");
    } else {
        for p in &sel.large {
            let _ = writeln!(t, "- `{p}`");
        }
    }
    t
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn glob_matches_a_star() {
        assert!(glob("gen*", "gen"));
        assert!(glob("gen*", "genout"));
        assert!(!glob("gen*", "agen"));
        assert!(glob("*.dl", "j1.dl"));
        assert!(!glob("*.dl", "j1.wf"));
        assert!(glob("runs", "runs"));
        assert!(!glob("runs", "runs2"));
    }

    #[test]
    fn names_dir_needs_the_end_of_a_name() {
        assert!(names_dir("see SCRATCH/verify/p/x.wf", "verify/p"));
        assert!(names_dir("in SCRATCH/verify/p.", "verify/p"));
        assert!(!names_dir("SCRATCH/verify/partb/x.wf", "verify/p"));
        assert!(!names_dir("SCRATCH/verify/p_x", "verify/p"));
        assert!(!names_dir("SCRATCH/verify/p.wf", "verify/p"));
        assert!(names_dir("SCRATCH/verify/p", "verify/p"));
    }
}
