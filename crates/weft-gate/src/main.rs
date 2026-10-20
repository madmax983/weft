//! The `weft-gate` command: the diff gate of the core IR migration.
//!
//! ```text
//! weft-gate manifest --tier 1|2 [--repo DIR] [--probes DIR] [--out FILE]
//! weft-gate archive --tier 2 [--repo DIR] [--probes DIR] [--out FILE]
//! weft-gate unpack --archive FILE --out DIR [--repo DIR]
//! weft-gate copy-probes [--repo DIR] [--probes DIR]
//! weft-gate snapshot --tier 1|2 [--facts old] [--out FILE.jsonl] [--full-digest DIR]
//!                    [--workers N] [--limit SECONDS] [--repo DIR] [--probes DIR]
//! ```
//!
//! `--repo` is the repository (default: the workspace of this crate). `--probes` is
//! the tier-2 root. Its default is `WEFT_GATE_PROBES`, else the committed archive
//! (`tests/gate/probes-tier2.tar.zst`), unpacked into `target/gate/probes-tier2`
//! after a check of its hash. The scratch directory of the plan (`SCRATCH`) is a
//! root only through `--probes` or `WEFT_GATE_PROBES`.
//!
//! `copy-probes` copies the hand probes (plan §2.2) from the tier-2 root into
//! `tests/gate/probes`. Run it with `SCRATCH`: the archive does not have the judge
//! traces (`ir/judge_sound/*.dl`, `run_all.sh`).
//!
//! `snapshot` checks each program of the manifest and writes one JSON record for
//! each program (plan §2.3). The default output is
//! `target/gate/snapshot-tier<N>-<pipeline>.jsonl`. `--full-digest DIR` also writes
//! the canonical fact digest of each program to `DIR/<hash>.<pipeline>.digest`.
//! The default number of workers is the number of CPUs, and the default time limit
//! is 60 s for each program.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use weft_gate::manifest::{self, Group, Manifest, Options, Root};
use weft_gate::snapshot::{self, Kind, Pipeline, Settings};
use weft_gate::{archive, copy};

/// The tier-1 manifest, relative to the repository.
const TIER1_OUT: &str = "tests/gate/manifest-tier1.tsv";
/// The tier-2 manifest, relative to the repository (not committed).
const TIER2_OUT: &str = "target/gate/manifest-tier2.tsv";
/// The tier-2 archive, relative to the repository (not committed).
const ARCHIVE_OUT: &str = "target/gate/probes-tier2.tar.zst";

const USAGE: &str = "usage:
  weft-gate manifest --tier 1|2 [--repo DIR] [--probes DIR] [--out FILE]
  weft-gate archive --tier 2 [--repo DIR] [--probes DIR] [--out FILE]
  weft-gate unpack --archive FILE --out DIR [--repo DIR]
  weft-gate copy-probes [--repo DIR] [--probes DIR]
  weft-gate snapshot --tier 1|2 [--facts old] [--out FILE.jsonl] [--full-digest DIR]
                     [--workers N] [--limit SECONDS] [--repo DIR] [--probes DIR]";

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
    probes: Option<PathBuf>,
    out: Option<PathBuf>,
    facts: Option<String>,
    full_digest: Option<PathBuf>,
    workers: Option<usize>,
    limit: Option<u64>,
}

impl Flags {
    /// The tier-2 root: `--probes`, else `WEFT_GATE_PROBES`, else the unpacked
    /// committed archive.
    fn probes(&self) -> Result<PathBuf> {
        let root = archive::probes_root(
            &self.repo,
            self.probes.clone(),
            std::env::var_os("WEFT_GATE_PROBES"),
        )?;
        Ok(root)
    }
}

fn parse_flags(args: &[String]) -> Result<Flags> {
    let mut tier = None;
    let mut repo = None;
    let mut probes = None;
    let mut out = None;
    let mut archive = None;
    let mut facts = None;
    let mut full_digest = None;
    let mut workers = None;
    let mut limit = None;
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
            "--facts" => facts = Some(value()?.clone()),
            "--full-digest" => full_digest = Some(PathBuf::from(value()?)),
            "--workers" => {
                let v = value()?;
                match v.parse::<usize>() {
                    Ok(n) if n > 0 => workers = Some(n),
                    _ => bail!("--workers needs a number larger than 0, found `{v}`"),
                }
            }
            "--limit" => {
                let v = value()?;
                match v.parse::<u64>() {
                    Ok(n) if n > 0 => limit = Some(n),
                    _ => bail!("--limit needs a number of seconds larger than 0, found `{v}`"),
                }
            }
            _ => bail!("unknown flag `{a}`\n{USAGE}"),
        }
    }
    let repo = repo.unwrap_or_else(|| {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        std::fs::canonicalize(&dir).unwrap_or(dir)
    });
    Ok(Flags {
        tier,
        archive,
        repo,
        probes,
        out,
        facts,
        full_digest,
        workers,
        limit,
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
                let m = tier2(&flags.probes()?)?;
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
            let probes = flags.probes()?;
            let m = tier2(&probes)?;
            write_text(&flags.repo.join(TIER2_OUT), &m.to_tsv())?;
            let out = flags.out.unwrap_or_else(|| flags.repo.join(ARCHIVE_OUT));
            let hash = archive::write(&probes, &m, &out)
                .with_context(|| format!("write {}", out.display()))?;
            let name = out
                .file_name()
                .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
            write_text(
                &flags.repo.join(archive::COMMITTED_HASH),
                &format!("{hash}  {name}\n"),
            )?;
            println!("wrote {} (sha256 {hash})", out.display());
            Ok(())
        }
        "unpack" => {
            let file = flags.archive.context("--archive is necessary")?;
            let dest = flags.out.context("--out is necessary")?;
            let committed = archive::committed_hash(&flags.repo).unwrap_or_default();
            if let Err(e) = archive::check_hash(&file, &committed) {
                eprintln!("warning: {e}");
            }
            archive::unpack(&file, &dest)?;
            println!(
                "unpacked into {}; set WEFT_GATE_PROBES to it",
                dest.display()
            );
            Ok(())
        }
        "copy-probes" => {
            let probes = flags.probes()?;
            let r = copy::copy_probes(&probes, &flags.repo)
                .with_context(|| format!("copy the probes from {}", probes.display()))?;
            println!(
                "copied {} files and {} packages ({} bytes) from {} directories into {}",
                r.files,
                r.packages,
                r.bytes,
                r.selection.dirs.len(),
                copy::PROBES_DIR
            );
            println!(
                "skipped {} programs of the repository sets and {} files larger than {} bytes",
                r.deduped.len(),
                r.selection.large.len(),
                copy::MAX_PROBE_BYTES
            );
            Ok(())
        }
        "snapshot" => run_snapshot(&flags),
        _ => bail!("unknown command `{cmd}`\n{USAGE}"),
    }
}

/// `snapshot`: checks each program of the manifest of the tier and writes the
/// records in the order of the manifest.
fn run_snapshot(flags: &Flags) -> Result<()> {
    let tier = flags.tier.context("--tier is necessary")?;
    let name = flags.facts.as_deref().unwrap_or("old");
    let pipeline = match Pipeline::parse(name) {
        Some(p) => p,
        None if name == "ir" => bail!("the `ir` pipeline does not exist before stage F1"),
        None => bail!("unknown pipeline `{name}`: use --facts old"),
    };
    let (m, base) = if tier == 1 {
        (tier1(flags)?, flags.repo.clone())
    } else {
        let probes = flags.probes()?;
        (tier2(&probes)?, probes)
    };
    let settings = Settings {
        pipeline,
        workers: flags.workers.unwrap_or_else(|| {
            std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get)
        }),
        limit: flags.limit.map_or(snapshot::LIMIT, Duration::from_secs),
    };
    let out = flags.out.clone().unwrap_or_else(|| {
        flags.repo.join(format!(
            "target/gate/snapshot-tier{tier}-{}.jsonl",
            pipeline.name()
        ))
    });
    if let Some(dir) = &flags.full_digest {
        std::fs::create_dir_all(dir).with_context(|| format!("make {}", dir.display()))?;
    }
    snapshot::install_panic_hook();
    let total = m.entries.len();
    println!(
        "snapshot of {total} programs with the `{}` pipeline on {} workers",
        pipeline.name(),
        settings.workers
    );
    let start = Instant::now();
    let mut records = vec![None; total];
    let mut failed = Vec::new();
    let mut ended = 0;
    snapshot::snapshot(&base, m.entries, &settings, |i, o| {
        if let Some(dir) = &flags.full_digest {
            if o.record.kind == Kind::Ok {
                let file = dir.join(format!("{}.{}.digest", o.record.hash, pipeline.name()));
                if let Err(e) = std::fs::write(&file, &o.digest) {
                    failed.push(format!("write {}: {e}", file.display()));
                }
            }
        }
        if let Some(slot) = records.get_mut(i) {
            *slot = Some(o.record);
        }
        ended += 1;
        if ended % 500 == 0 {
            println!(
                "{ended} of {total} programs in {:.1} s",
                start.elapsed().as_secs_f64()
            );
        }
    })?;
    if let Some(e) = failed.first() {
        bail!("{e}");
    }
    let mut text = String::new();
    let mut kinds: BTreeMap<Kind, usize> = BTreeMap::new();
    for r in records.iter().flatten() {
        text.push_str(&r.to_json()?);
        text.push('\n');
        *kinds.entry(r.kind).or_default() += 1;
    }
    write_text(&out, &text)?;
    let counts: Vec<String> = Kind::ALL
        .iter()
        .map(|k| format!("{} {}", kinds.get(k).copied().unwrap_or(0), k.name()))
        .collect();
    println!(
        "wrote {} records to {} in {:.1} s: {}",
        records.iter().flatten().count(),
        out.display(),
        start.elapsed().as_secs_f64(),
        counts.join(", ")
    );
    Ok(())
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

fn tier2(probes: &Path) -> Result<Manifest> {
    let tier = manifest::tier2_roots();
    let roots: Vec<Root> = tier.iter().map(|t| t.root.clone()).collect();
    let m = manifest::build(
        probes,
        &roots,
        Options {
            exclude_copies: true,
        },
    )
    .with_context(|| format!("read {}", probes.display()))?;
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
