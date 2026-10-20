//! The `weft-gate` command: the diff gate of the core IR migration.
//!
//! ```text
//! weft-gate manifest --tier 1|2 [--repo DIR] [--probes DIR] [--out FILE]
//! weft-gate archive --tier 2 [--repo DIR] [--probes DIR] [--out FILE]
//! weft-gate unpack --archive FILE --out DIR [--repo DIR]
//! ```
//!
//! `--repo` is the repository (default: the workspace of this crate). `--probes` is
//! the tier-2 root (default: `WEFT_GATE_PROBES`, else the scratch directory of the
//! plan).

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::{bail, Context, Result};
use weft_gate::archive;
use weft_gate::manifest::{self, Group, Manifest, Options, Root};

/// The tier-1 manifest, relative to the repository.
const TIER1_OUT: &str = "tests/gate/manifest-tier1.tsv";
/// The tier-2 manifest, relative to the repository (not committed).
const TIER2_OUT: &str = "target/gate/manifest-tier2.tsv";
/// The tier-2 archive, relative to the repository (not committed).
const ARCHIVE_OUT: &str = "target/gate/probes-tier2.tar.zst";
/// The committed hash of the tier-2 archive, relative to the repository.
const ARCHIVE_HASH: &str = "tests/gate/probes-tier2.sha256";

const USAGE: &str = "usage:
  weft-gate manifest --tier 1|2 [--repo DIR] [--probes DIR] [--out FILE]
  weft-gate archive --tier 2 [--repo DIR] [--probes DIR] [--out FILE]
  weft-gate unpack --archive FILE --out DIR [--repo DIR]";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(2)
        }
    }
}

/// The parsed flags.
struct Flags {
    tier: Option<u8>,
    archive: Option<PathBuf>,
    repo: PathBuf,
    probes: PathBuf,
    out: Option<PathBuf>,
}

fn parse_flags(args: &[String]) -> Result<Flags> {
    let mut tier = None;
    let mut repo = None;
    let mut probes = None;
    let mut out = None;
    let mut archive = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut value = || it.next().with_context(|| format!("{a} needs a value"));
        match a.as_str() {
            "--tier" => {
                tier = Some(match value()?.as_str() {
                    "1" => 1,
                    "2" => 2,
                    t => bail!("unknown tier `{t}`"),
                });
            }
            "--repo" => repo = Some(PathBuf::from(value()?)),
            "--probes" => probes = Some(PathBuf::from(value()?)),
            "--out" => out = Some(PathBuf::from(value()?)),
            "--archive" => archive = Some(PathBuf::from(value()?)),
            _ => bail!("unknown flag `{a}`\n{USAGE}"),
        }
    }
    let repo = repo.unwrap_or_else(|| {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        std::fs::canonicalize(&dir).unwrap_or(dir)
    });
    let probes = probes
        .or_else(|| std::env::var_os("WEFT_GATE_PROBES").map(PathBuf::from))
        .unwrap_or_else(|| PathBuf::from(manifest::DEFAULT_PROBES));
    Ok(Flags {
        tier,
        archive,
        repo,
        probes,
        out,
    })
}

fn run(args: &[String]) -> Result<()> {
    let Some((cmd, rest)) = args.split_first() else {
        bail!("{USAGE}");
    };
    let flags = parse_flags(rest)?;
    match cmd.as_str() {
        "manifest" => {
            let tier = flags.tier.context("--tier is necessary")?;
            let (m, out) = if tier == 1 {
                let m = tier1(&flags)?;
                (m, flags.out.unwrap_or_else(|| flags.repo.join(TIER1_OUT)))
            } else {
                let m = tier2(&flags)?;
                (m, flags.out.unwrap_or_else(|| flags.repo.join(TIER2_OUT)))
            };
            write_text(&out, &m.to_tsv())?;
            println!("wrote {}", out.display());
            Ok(())
        }
        "archive" => {
            if flags.tier != Some(2) {
                bail!("only tier 2 has an archive: use --tier 2");
            }
            let m = tier2(&flags)?;
            write_text(&flags.repo.join(TIER2_OUT), &m.to_tsv())?;
            let out = flags.out.unwrap_or_else(|| flags.repo.join(ARCHIVE_OUT));
            let hash = archive::write(&flags.probes, &m, &out)
                .with_context(|| format!("write {}", out.display()))?;
            let name = out
                .file_name()
                .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
            write_text(&flags.repo.join(ARCHIVE_HASH), &format!("{hash}  {name}\n"))?;
            println!("wrote {} (sha256 {hash})", out.display());
            Ok(())
        }
        "unpack" => {
            let file = flags.archive.context("--archive is necessary")?;
            let dest = flags.out.context("--out is necessary")?;
            let hash = archive::sha256_file(&file)?;
            let committed =
                std::fs::read_to_string(flags.repo.join(ARCHIVE_HASH)).unwrap_or_default();
            if committed.split_whitespace().next() != Some(hash.as_str()) {
                eprintln!("warning: the sha256 {hash} is not the hash in {ARCHIVE_HASH}");
            }
            archive::unpack(&file, &dest)?;
            println!(
                "unpacked into {}; set WEFT_GATE_PROBES to it",
                dest.display()
            );
            Ok(())
        }
        _ => bail!("unknown command `{cmd}`\n{USAGE}"),
    }
}

fn tier1(flags: &Flags) -> Result<Manifest> {
    let roots = manifest::tier1_roots();
    let m = manifest::build(
        &flags.repo,
        &roots,
        Options {
            exclude_copies: false,
        },
    )?;
    report(&m, &roots);
    Ok(m)
}

fn tier2(flags: &Flags) -> Result<Manifest> {
    let tier = manifest::tier2_roots();
    let roots: Vec<Root> = tier.iter().map(|t| t.root.clone()).collect();
    let m = manifest::build(
        &flags.probes,
        &roots,
        Options {
            exclude_copies: true,
        },
    )
    .with_context(|| format!("read {}", flags.probes.display()))?;
    report(&m, &roots);
    for (group, name) in [
        (Group::Report, "report roots"),
        (Group::Stage, "stage roots"),
    ] {
        let sets: Vec<&str> = tier
            .iter()
            .filter(|t| t.group == group)
            .map(|t| t.root.set.as_str())
            .collect();
        let (distinct, paths) = counts(&m, &roots, |s| sets.contains(&s));
        println!("{name}: {distinct} distinct, {paths} paths");
    }
    Ok(m)
}

/// Counts the entries whose set passes `keep`, and the paths in the roots whose set
/// passes `keep`.
fn counts(m: &Manifest, roots: &[Root], keep: impl Fn(&str) -> bool) -> (usize, usize) {
    let distinct = m.entries.iter().filter(|e| keep(&e.set)).count();
    let paths = m
        .all_paths()
        .filter(|(_, p)| {
            roots
                .iter()
                .find(|r| r.holds(p))
                .is_some_and(|r| keep(&r.set))
        })
        .count();
    (distinct, paths)
}

/// Prints the counts of each set and the missing roots.
fn report(m: &Manifest, roots: &[Root]) {
    for dir in &m.missing {
        eprintln!("warning: the root `{dir}` does not exist");
    }
    for r in roots {
        let (distinct, paths) = counts(m, roots, |s| s == r.set);
        let packages = m
            .entries
            .iter()
            .filter(|e| e.set == r.set && e.mode == manifest::Mode::Package)
            .count();
        println!(
            "{:<10} {distinct:>6} distinct ({packages} packages), {paths:>6} paths",
            r.set
        );
    }
    let mains = m.entries.iter().filter(|e| e.has_main).count();
    let tests = m.entries.iter().filter(|e| e.has_tests).count();
    println!(
        "total: {} distinct, {} paths; {mains} with main, {tests} with tests",
        m.entries.len(),
        m.path_count()
    );
}

fn write_text(path: &Path, text: &str) -> Result<()> {
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir).with_context(|| format!("make {}", dir.display()))?;
    }
    std::fs::write(path, text).with_context(|| format!("write {}", path.display()))
}
