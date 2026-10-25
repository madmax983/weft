//! The `weft-gate` command: the diff gate of the core IR migration.
//!
//! ```text
//! weft-gate manifest --tier 1|2 [--repo DIR] [--probes DIR] [--out FILE]
//! weft-gate archive --tier 2 [--repo DIR] [--probes DIR] [--out FILE]
//! weft-gate unpack --archive FILE --out DIR [--repo DIR]
//! weft-gate copy-probes [--repo DIR] [--probes DIR]
//! weft-gate snapshot --tier 1|2 [--facts old|ir] [--groups ABCDEF] [--out FILE.jsonl] [--full-digest DIR]
//!                    [--workers N] [--limit SECONDS] [--repo DIR] [--probes DIR]
//! weft-gate oracle --tier 1|2 [--engine ast|ir] [--out FILE] [--workers N]
//!                  [--limit SECONDS] [--max-steps N] [--max-memory MB]
//!                  [--repo DIR] [--probes DIR]
//! weft-gate oracle-run --base DIR --path PATH [--from K] [--limit-ms MS]
//!                      [--max-steps N] [--max-memory MB] [--engine ast|ir] [--observe]
//! weft-gate run --tier 1|2 [--groups ABCDEF] [--report FILE] [--workers N]
//!               [--limit SECONDS] [--repo DIR] [--probes DIR] [--write-baseline]
//! weft-gate thir --tier 1|2 [--report FILE] [--workers N] [--limit SECONDS]
//!                [--repo DIR] [--probes DIR]
//! weft-gate ir-build --tier 1|2 [--report FILE] [--workers N] [--limit SECONDS]
//!                    [--repo DIR] [--probes DIR]
//! weft-gate engines --tier 1|2 [--report FILE] [--workers N] [--limit SECONDS]
//!                   [--max-steps N] [--max-memory MB] [--sample PERCENT] [--seed N]
//!                   [--repo DIR] [--probes DIR]
//! weft-gate sigdiff --tier 1|2 [--groups ABCDEF] [--report FILE] [--workers N]
//!                   [--limit SECONDS] [--repo DIR] [--probes DIR]
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
//! `--facts ir` checks with the `ir` pipeline (plan §2.6): a program out of
//! scope gets the result of the old pipeline. `--groups` puts more construct
//! groups on. The default number of workers is the number of CPUs, and the default time limit
//! is 60 s for each program.
//!
//! `oracle` gives the oracle verdict of each program of the manifest (plan §2.4,
//! `weft_gate::oracle`). A row of the cache with the same key skips the run. The
//! cache of tier 1 is `tests/gate/oracle-<engine>.tsv`. The cache of tier 2 is the
//! same name in `WEFT_GATE_CACHE` (default `target/gate/`); tier 2 also takes
//! the rows of the tier-1 cache. The command adds each new row to the end of the
//! file when its run ends, so a stopped command continues at the next start. At
//! the end it writes the file again with only the rows of the manifest. The time
//! limit (default 10 s) and the step limit (default 50 000 000) are for each of
//! the six runs of a program. Each program runs in child processes
//! (`oracle-run`): the parent stops a child at the time limit, and a child
//! stops itself when it uses more than the memory limit (default 2048 MB).
//!
//! `oracle` takes `--engine ast` (the default) or `--engine ir`. From stage I5
//! on, the gate classifies the programs with the verdicts of the `ir` engine
//! (`tests/gate/oracle-ir.tsv`); the `ast` cache stays for the engine
//! differential and for a comparison.
//!
//! `oracle-run` is the child process of `oracle` and `engines`: it runs the
//! program `PATH` below `DIR` with the engine `--engine` in the configurations
//! from index `K` and writes one line for each run (`weft_gate::oracle::Step`).
//! With `--observe` it also writes the observation of each run
//! (`weft_gate::oracle::Observation`).
//!
//! `run` is the gate (plan §2.5): it checks each program of the tier, reads
//! the oracle verdicts from the cache, classifies each program with the
//! ledger `tests/gate/ledger.toml`, and writes the report (default
//! `target/gate/report.md`). The exit code is 1 if the gate has a blocker. A
//! cache with no verdict for a program (a stale key) is an error: run
//! `oracle` first. One analysis of each program gives both records
//! (`--facts=both`). `--groups` puts more construct groups on, for a preview
//! report (plan §2.6); the report gives the coverage of each set.
//!
//! `run` also compares the old records with the baseline of the tier
//! (`weft_gate::baseline`): `tests/gate/baseline-tier1.jsonl` (committed; it
//! must exist) or `target/gate/baseline-tier2.jsonl` (if it exists). A
//! difference is a blocker. `--write-baseline` writes the old records to that
//! file and does not compare them. Write a baseline with a release build: a
//! debug build can give timeouts. In tier 2 an `open` program with no ledger
//! entry does not block (`weft_gate::report::Policy::for_tier`).
//!
//! `thir` runs test D0 (plan stage T3, `weft_gate::thir`) on each program of
//! the tier: the THIR tables that the old lowering records, against the syntax
//! tree, the facts and the final types. It writes the summary (default
//! `target/gate/thir-tier<N>.md`). The exit code is 1 if D0 fails on a program.
//! Run it with a release build.
//!
//! `ir-build` builds and verifies the IR of each program of the tier (plan
//! stage B12, `weft_gate::ir_build`). It counts the bodies that the builder
//! lowers, the bodies with no IR for each reason, the unsupported bodies, the
//! broken rules, the panics and the timeouts, and lists the slowest builds. It
//! writes the summary (default `target/gate/ir-build-tier<N>.md`). The exit
//! code is 1 if a program panics, breaks a rule or has an unsupported body. A
//! timeout does not fail; the summary lists it. Run it with a release build.
//!
//! `engines` is the engine differential (plan stage I5, `weft_gate::engines`):
//! it runs each program of the tier that has `main` or test blocks with the
//! `ast` and the `ir` engine, with the oracle, in the six configurations, and
//! compares the output, the status, and the message and line of each error.
//! Each difference needs a ledger entry of class `engine`. The checker results
//! come from the baseline of the tier. A program with a time limit on one side
//! runs again, alone. `--sample PERCENT` keeps that share of the programs that
//! the checker rejects (a fixed choice for `--seed`, default 1) and each program
//! that it accepts. It writes the report (default
//! `target/gate/engines-tier<N>.md`) and the differences as JSON lines next to
//! it. The exit code is 1 if a difference has no entry. Run it with a release
//! build.
//!
//! `sigdiff` is the signature diff (plan stage F6, `weft_gate::sigdiff`): for
//! each program of the tier in scope of the `ir` pipeline with the groups of
//! `--groups`, it compares the `EffectSig` of each function that the `ir`
//! pipeline infers with the one of the old inference. Each difference needs a
//! ledger entry of class `sig`. It writes the report (default
//! `target/gate/sigdiff-tier<N>.md`). The exit code is 1 if a difference has
//! no entry or a program panics. Run it with a release build.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use weft_gate::ledger::{self, Ledger};
use weft_gate::manifest::{self, Group, Manifest, Options, Root};
use weft_gate::oracle::{self, Cache, Engine, Step, Verdict};
use weft_gate::snapshot::{self, Kind, Pipeline, Settings};
use weft_gate::{archive, baseline, copy, engines, report};

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
  weft-gate snapshot --tier 1|2 [--facts old|ir] [--groups ABCDEF] [--out FILE.jsonl] [--full-digest DIR]
                     [--workers N] [--limit SECONDS] [--repo DIR] [--probes DIR]
  weft-gate oracle --tier 1|2 [--engine ast|ir] [--out FILE] [--workers N]
                   [--limit SECONDS] [--max-steps N] [--max-memory MB]
                   [--repo DIR] [--probes DIR]
  weft-gate oracle-run --base DIR --path PATH [--from K] [--limit-ms MS]
                       [--max-steps N] [--max-memory MB] [--engine ast|ir] [--observe]
                       [--fact-oracle]
  weft-gate fact-oracle --tier 1|2 [--report FILE] [--workers N] [--limit SECONDS]
                        [--max-steps N] [--max-memory MB] [--repo DIR] [--probes DIR]
  weft-gate run --tier 1|2 [--groups ABCDEF] [--report FILE] [--workers N]
                [--limit SECONDS] [--repo DIR] [--probes DIR] [--write-baseline]
  weft-gate thir --tier 1|2 [--report FILE] [--workers N] [--limit SECONDS]
                 [--repo DIR] [--probes DIR]
  weft-gate ir-build --tier 1|2 [--report FILE] [--workers N] [--limit SECONDS]
                     [--repo DIR] [--probes DIR]
  weft-gate engines --tier 1|2 [--report FILE] [--workers N] [--limit SECONDS]
                    [--max-steps N] [--max-memory MB] [--sample PERCENT] [--seed N]
                    [--repo DIR] [--probes DIR]
  weft-gate sigdiff --tier 1|2 [--groups ABCDEF] [--report FILE] [--workers N]
                    [--limit SECONDS] [--repo DIR] [--probes DIR]";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
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
    engine: Option<String>,
    max_steps: Option<u64>,
    max_memory: Option<u64>,
    base: Option<PathBuf>,
    path: Option<String>,
    from: Option<usize>,
    limit_ms: Option<u64>,
    groups: Option<String>,
    report: Option<PathBuf>,
    write_baseline: bool,
    observe: bool,
    fact_oracle: bool,
    rejudge: bool,
    sample: Option<u64>,
    seed: Option<u64>,
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
    let mut engine = None;
    let mut max_steps = None;
    let mut max_memory = None;
    let mut base = None;
    let mut path = None;
    let mut from = None;
    let mut limit_ms = None;
    let mut groups = None;
    let mut report = None;
    let mut write_baseline = false;
    let mut observe = false;
    let mut fact_oracle = false;
    let mut rejudge = false;
    let mut sample = None;
    let mut seed = None;
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
            "--engine" => engine = Some(value()?.clone()),
            "--max-steps" => max_steps = Some(positive(a, value()?)?),
            "--max-memory" => max_memory = Some(positive(a, value()?)?),
            "--limit-ms" => limit_ms = Some(positive(a, value()?)?),
            "--base" => base = Some(PathBuf::from(value()?)),
            "--path" => path = Some(value()?.clone()),
            "--groups" => groups = Some(value()?.clone()),
            "--report" => report = Some(PathBuf::from(value()?)),
            "--write-baseline" => write_baseline = true,
            "--observe" => observe = true,
            "--fact-oracle" => fact_oracle = true,
            "--rejudge" => rejudge = true,
            "--sample" => {
                let v = value()?;
                match v.parse::<u64>() {
                    Ok(n) if (1..=100).contains(&n) => sample = Some(n),
                    _ => bail!("--sample needs a percent from 1 to 100, found `{v}`"),
                }
            }
            "--seed" => {
                let v = value()?;
                seed = Some(
                    v.parse::<u64>()
                        .with_context(|| format!("--seed needs a number, found `{v}`"))?,
                );
            }
            "--from" => {
                let v = value()?;
                match v.parse::<usize>() {
                    Ok(n) if n < oracle::CONFIGS.len() => from = Some(n),
                    _ => bail!("--from needs an index of a configuration, found `{v}`"),
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
        engine,
        max_steps,
        max_memory,
        base,
        path,
        from,
        limit_ms,
        groups,
        report,
        write_baseline,
        observe,
        fact_oracle,
        rejudge,
        sample,
        seed,
    })
}

/// The value of the flag `flag` as a number larger than 0.
fn positive(flag: &str, v: &str) -> Result<u64> {
    match v.parse::<u64>() {
        Ok(n) if n > 0 => Ok(n),
        _ => bail!("{flag} needs a number larger than 0, found `{v}`"),
    }
}

/// Runs the command. Returns false if the gate has a blocker.
fn run(args: &[String]) -> Result<bool> {
    let Some((cmd, rest)) = args.split_first() else {
        bail!("{USAGE}");
    };
    let flags = parse_flags(rest)?;
    if cmd == "run" {
        return run_gate(&flags);
    }
    if cmd == "thir" {
        return run_thir(&flags);
    }
    if cmd == "ir-build" {
        return run_ir_build(&flags);
    }
    if cmd == "engines" {
        return run_engines(&flags);
    }
    if cmd == "sigdiff" {
        return run_sigdiff(&flags);
    }
    if cmd == "fact-oracle" {
        return run_fact_oracle(&flags);
    }
    run_tool(cmd, flags).map(|()| true)
}

/// Runs a command that is not `run`.
fn run_tool(cmd: &str, flags: Flags) -> Result<()> {
    match cmd {
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
        "oracle" => run_oracle(&flags),
        "oracle-run" => run_oracle_child(&flags),
        _ => bail!("unknown command `{cmd}`\n{USAGE}"),
    }
}

/// The construct groups that are on: the default groups of the analysis and
/// the groups of `--groups`.
fn groups_on(flags: &Flags) -> Result<weft_sema::Groups> {
    let on = weft_sema::Options::default().ir_groups;
    match flags.groups.as_deref().filter(|g| !g.is_empty()) {
        None => Ok(on),
        Some(g) => weft_sema::Groups::parse(g)
            .map(|g| on.union(g))
            .map_err(|e| anyhow::anyhow!("--groups {g}: {e}")),
    }
}

/// `run`: the gate on the programs of the tier. Returns false if the gate has
/// a blocker.
fn run_gate(flags: &Flags) -> Result<bool> {
    let tier = flags.tier.context("--tier is necessary")?;
    let settings = report::RunSettings {
        groups: groups_on(flags)?,
        workers: flags.workers.unwrap_or_else(|| {
            std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get)
        }),
        limit: flags.limit.map_or(snapshot::LIMIT, Duration::from_secs),
        policy: report::Policy::for_tier(tier),
        baseline: !flags.write_baseline,
    };
    let out = flags
        .report
        .clone()
        .unwrap_or_else(|| flags.repo.join("target/gate/report.md"));
    let start = Instant::now();
    let r = if tier == 1 {
        println!("the gate on tier 1 with {} workers", settings.workers);
        report::run_tier1(&flags.repo, &settings)?
    } else {
        let probes = flags.probes()?;
        let m = tier2(&probes)?;
        let name = oracle::cache_name(report::ORACLE_ENGINE);
        let dir = std::env::var_os("WEFT_GATE_CACHE")
            .map_or_else(|| flags.repo.join("target/gate"), PathBuf::from);
        let mut cache = read_cache(&dir.join(&name))?;
        cache.extend(read_cache(&flags.repo.join("tests/gate").join(&name))?);
        let interp = oracle::interp_hash(&flags.repo)?;
        let ledger = Ledger::read(&flags.repo.join(ledger::LEDGER))?;
        println!("the gate on tier 2 with {} workers", settings.workers);
        let mut r = report::run(
            &probes,
            m,
            &cache,
            &interp,
            &ledger,
            &settings,
            Some(copy::PROBES_DIR),
        )?;
        r.notes.insert(0, format!("tier 2 ({})", probes.display()));
        if settings.baseline {
            match baseline::read(&flags.repo.join(baseline::TIER2))? {
                Some(base) => r.compare_baseline(Some(base), baseline::TIER2),
                None => r.notes.push(format!(
                    "no baseline `{}`: the old records are not compared",
                    baseline::TIER2
                )),
            }
        }
        r
    };
    if flags.write_baseline {
        write_baseline(&flags.repo, tier, &r.records)?;
    }
    write_text(&out, &r.to_markdown())?;
    let counts: Vec<String> = r
        .class_counts()
        .iter()
        .map(|(c, n)| format!("{n} {}", c.name()))
        .collect();
    println!(
        "{} programs in {:.1} s: {}",
        r.rows.len(),
        start.elapsed().as_secs_f64(),
        counts.join(", ")
    );
    for w in &r.warnings {
        eprintln!("warning: {w}");
    }
    for b in r.blockers.iter().take(20) {
        eprintln!("blocker: {b}");
    }
    println!(
        "wrote {}; {} blockers, {} warnings",
        out.display(),
        r.blockers.len(),
        r.warnings.len()
    );
    Ok(r.passes())
}

/// `thir`: test D0 on the programs of the tier. Returns false if D0 fails.
fn run_thir(flags: &Flags) -> Result<bool> {
    let tier = flags.tier.context("--tier is necessary")?;
    let (m, base) = if tier == 1 {
        (tier1(flags)?, flags.repo.clone())
    } else {
        let probes = flags.probes()?;
        (tier2(&probes)?, probes)
    };
    let workers = flags.workers.unwrap_or_else(|| {
        std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get)
    });
    let limit = flags.limit.map_or(snapshot::LIMIT, Duration::from_secs);
    let out = flags
        .report
        .clone()
        .unwrap_or_else(|| flags.repo.join(format!("target/gate/thir-tier{tier}.md")));
    snapshot::install_panic_hook();
    let total = m.entries.len();
    println!("D0 on {total} programs of tier {tier} with {workers} workers");
    let start = Instant::now();
    let sum = weft_gate::thir::run(&base, m.entries, workers, limit, |ended| {
        if ended % 2000 == 0 {
            println!(
                "{ended} of {total} programs in {:.1} s",
                start.elapsed().as_secs_f64()
            );
        }
    })?;
    let text = sum.to_markdown(&format!("tier {tier}"));
    write_text(&out, &text)?;
    print!("{text}");
    println!(
        "{} programs in {:.1} s; wrote {}",
        sum.programs,
        start.elapsed().as_secs_f64(),
        out.display()
    );
    Ok(sum.holds())
}

/// `ir-build`: builds and verifies the IR of the programs of the tier. Returns
/// false if a program panics, breaks a rule or has an unsupported body.
fn run_ir_build(flags: &Flags) -> Result<bool> {
    let tier = flags.tier.context("--tier is necessary")?;
    let (m, base) = if tier == 1 {
        (tier1(flags)?, flags.repo.clone())
    } else {
        let probes = flags.probes()?;
        (tier2(&probes)?, probes)
    };
    let workers = flags.workers.unwrap_or_else(|| {
        std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get)
    });
    let limit = flags.limit.map_or(snapshot::LIMIT, Duration::from_secs);
    let out = flags.report.clone().unwrap_or_else(|| {
        flags
            .repo
            .join(format!("target/gate/ir-build-tier{tier}.md"))
    });
    snapshot::install_panic_hook();
    let total = m.entries.len();
    println!("ir-build on {total} programs of tier {tier} with {workers} workers");
    let start = Instant::now();
    let sum = weft_gate::ir_build::run(&base, m.entries, workers, limit, |ended| {
        if ended % 2000 == 0 {
            println!(
                "{ended} of {total} programs in {:.1} s",
                start.elapsed().as_secs_f64()
            );
        }
    })?;
    let text = sum.to_markdown(&format!("tier {tier}"));
    write_text(&out, &text)?;
    print!("{text}");
    println!(
        "{} programs in {:.1} s; wrote {}",
        sum.programs,
        start.elapsed().as_secs_f64(),
        out.display()
    );
    Ok(sum.holds())
}

/// `sigdiff`: the signature diff on the programs of the tier. Returns false
/// if a difference has no ledger entry or a program panics.
fn run_sigdiff(flags: &Flags) -> Result<bool> {
    let tier = flags.tier.context("--tier is necessary")?;
    let (m, base) = if tier == 1 {
        (tier1(flags)?, flags.repo.clone())
    } else {
        let probes = flags.probes()?;
        (tier2(&probes)?, probes)
    };
    let groups = groups_on(flags)?;
    let workers = flags.workers.unwrap_or_else(|| {
        std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get)
    });
    let limit = flags.limit.map_or(snapshot::LIMIT, Duration::from_secs);
    let out = flags.report.clone().unwrap_or_else(|| {
        flags
            .repo
            .join(format!("target/gate/sigdiff-tier{tier}.md"))
    });
    let ledger = Ledger::read(&flags.repo.join(ledger::LEDGER))?;
    snapshot::install_panic_hook();
    let total = m.entries.len();
    println!("sigdiff on {total} programs of tier {tier} with {workers} workers, groups {groups}");
    let start = Instant::now();
    let sum =
        weft_gate::sigdiff::run(&base, m.entries, workers, limit, groups, &ledger, |ended| {
            if ended % 2000 == 0 {
                println!(
                    "{ended} of {total} programs in {:.1} s",
                    start.elapsed().as_secs_f64()
                );
            }
        })?;
    let text = sum.to_markdown(&format!("tier {tier}, groups {groups}"));
    write_text(&out, &text)?;
    println!(
        "{} programs in {:.1} s: {} in scope, {} functions, {} same, {} differ, {} with no entry; wrote {}",
        sum.programs,
        start.elapsed().as_secs_f64(),
        sum.in_scope,
        sum.fns,
        sum.same,
        sum.fns.saturating_sub(sum.same),
        sum.unledgered,
        out.display()
    );
    Ok(sum.holds())
}

/// `engines`: the engine differential on the runnable programs of the tier.
/// Returns false if a difference has no ledger entry.
fn run_engines(flags: &Flags) -> Result<bool> {
    let tier = flags.tier.context("--tier is necessary")?;
    let (m, base, alias) = if tier == 1 {
        (tier1(flags)?, flags.repo.clone(), None)
    } else {
        let probes = flags.probes()?;
        (tier2(&probes)?, probes, Some(copy::PROBES_DIR))
    };
    let file = baseline::file(tier);
    let Some(records) = baseline::read(&flags.repo.join(file))? else {
        bail!(
            "the baseline `{file}` does not exist: the differential reads the checker results from it. Run `cargo run -p weft-gate --release -- run --tier {tier} --write-baseline` first"
        );
    };
    let rejected = engines::rejected_hashes(&records);
    if flags.rejudge {
        return rejudge_engines(flags, tier, &m, alias);
    }
    let mut entries: Vec<manifest::Entry> = m
        .entries
        .into_iter()
        .filter(|e| e.has_main || e.has_tests)
        .collect();
    let runnable = entries.len();
    let mut notes = vec![
        format!("tier {tier}: {runnable} programs with `main` or test blocks"),
        format!(
            "the checker results come from `{file}`: {} of the programs that it lists are rejected",
            rejected.len()
        ),
    ];
    if let Some(percent) = flags.sample {
        let seed = flags.seed.unwrap_or(1);
        entries
            .retain(|e| !rejected.contains(&e.hash) || engines::in_sample(&e.hash, percent, seed));
        notes.push(format!(
            "sample: {percent} % of the programs that the checker rejects (seed {seed}), and each program that it accepts: {} programs",
            entries.len()
        ));
    }
    let settings = oracle::Settings {
        workers: flags.workers.unwrap_or_else(|| {
            std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get)
        }),
        limit: flags.limit.map_or(oracle::LIMIT, Duration::from_secs),
        max_steps: Some(flags.max_steps.unwrap_or(oracle::MAX_STEPS)),
        max_memory_mb: flags.max_memory.unwrap_or(oracle::MAX_MEMORY_MB),
        exe: Some(std::env::current_exe().context("find the weft-gate program")?),
        engine: Engine::Ast,
        fact_oracle: false,
    };
    notes.push(format!(
        "{} workers; time limit of a run {} s, step limit {}, memory limit {} MB",
        settings.workers,
        settings.limit.as_secs(),
        settings.max_steps.unwrap_or(0),
        settings.max_memory_mb
    ));
    let ledger = Ledger::read(&flags.repo.join(ledger::LEDGER))?;
    let rules = engines::Rules::from_ledger(&ledger);
    snapshot::install_panic_hook();
    let total = entries.len();
    println!(
        "engine differential on {total} programs of tier {tier} with {} workers",
        settings.workers
    );
    let start = Instant::now();
    let mut runs: Vec<Option<engines::Runs>> = vec![None; total];
    let mut ended = 0;
    engines::run_all(&base, entries.clone(), &settings, |i, r| {
        if let Some(slot) = runs.get_mut(i) {
            *slot = Some(r);
        }
        ended += 1;
        if ended % 500 == 0 {
            println!(
                "{ended} of {total} programs in {:.1} s",
                start.elapsed().as_secs_f64()
            );
        }
    })?;
    // A time limit on one side only: run the program again, alone.
    let again: Vec<usize> = runs
        .iter()
        .enumerate()
        .filter(|(_, r)| r.as_ref().is_some_and(engines::Runs::one_sided_timeout))
        .map(|(i, _)| i)
        .collect();
    let mut rerun = BTreeSet::new();
    if !again.is_empty() {
        println!(
            "{} programs with a time limit on one side run again, alone",
            again.len()
        );
        let alone = oracle::Settings {
            workers: 1,
            ..settings
        };
        let list: Vec<manifest::Entry> = again
            .iter()
            .filter_map(|&i| entries.get(i).cloned())
            .collect();
        engines::run_all(&base, list, &alone, |k, r| {
            if let Some(&i) = again.get(k) {
                if let Some(slot) = runs.get_mut(i) {
                    *slot = Some(r);
                }
                rerun.insert(i);
            }
        })?;
        notes.push(format!(
            "{} programs with a time limit on one side ran again with one worker",
            again.len()
        ));
    }
    let mut report = engines::Report {
        notes,
        problems: rules.problems.clone(),
        ..engines::Report::default()
    };
    for &(k, kind) in &rules.entries {
        if let Some(e) = ledger.entries.get(k) {
            report.entries.insert(k, (e.label(), kind));
        }
    }
    for (i, (e, r)) in entries.iter().zip(runs).enumerate() {
        let Some(r) = r else { continue };
        let paths = engines::entry_paths(e, alias);
        let is_rejected = rejected.contains(&e.hash);
        report.rows.push(engines::Row {
            path: e.path.clone(),
            rejected: is_rejected,
            rerun: rerun.contains(&i),
            result: engines::judge(&r, &paths, is_rejected, &ledger, &rules),
        });
    }
    let out = flags.report.clone().unwrap_or_else(|| {
        flags
            .repo
            .join(format!("target/gate/engines-tier{tier}.md"))
    });
    write_text(&out, &report.to_markdown())?;
    let jsonl = out.with_extension("jsonl");
    write_text(&jsonl, &report.differences_jsonl())?;
    let (same, fallback, differ) = report.counts();
    println!(
        "{} programs in {:.1} s: same {same}, fallback {fallback}, differ {differ}",
        report.rows.len(),
        start.elapsed().as_secs_f64()
    );
    for (c, n) in report.class_counts() {
        println!("  {c}: {n}");
    }
    for p in &report.problems {
        eprintln!("problem: {p}");
    }
    for r in report.unledgered().iter().take(20) {
        eprintln!("unledgered: {}", r.path);
    }
    println!(
        "wrote {} and {}; {} unledgered differences",
        out.display(),
        jsonl.display(),
        report.unledgered().len()
    );
    Ok(report.passes())
}

/// `engines --rejudge`: classifies the differences of the last run again
/// (the JSON lines next to the report) with the ledger of today. Only the
/// differences are in the file, so the report has no `same` program.
fn rejudge_engines(flags: &Flags, tier: u8, m: &Manifest, alias: Option<&str>) -> Result<bool> {
    let out = flags.report.clone().unwrap_or_else(|| {
        flags
            .repo
            .join(format!("target/gate/engines-tier{tier}.md"))
    });
    let jsonl = out.with_extension("jsonl");
    let text =
        std::fs::read_to_string(&jsonl).with_context(|| format!("read {}", jsonl.display()))?;
    let saved = engines::read_differences(&text)
        .map_err(|e| anyhow::anyhow!("{}: {e}", jsonl.display()))?;
    let ledger = Ledger::read(&flags.repo.join(ledger::LEDGER))?;
    let rules = engines::Rules::from_ledger(&ledger);
    let by_path: BTreeMap<&str, &manifest::Entry> =
        m.entries.iter().map(|e| (e.path.as_str(), e)).collect();
    let mut report = engines::Report {
        notes: vec![format!(
            "tier {tier}: the differences of `{}`, classified again with the ledger of today",
            jsonl.display()
        )],
        problems: rules.problems.clone(),
        ..engines::Report::default()
    };
    for &(k, kind) in &rules.entries {
        if let Some(e) = ledger.entries.get(k) {
            report.entries.insert(k, (e.label(), kind));
        }
    }
    for s in saved {
        let paths = by_path
            .get(s.path.as_str())
            .map_or_else(|| vec![s.path.clone()], |e| engines::entry_paths(e, alias));
        report.rows.push(engines::Row {
            path: s.path.clone(),
            rejected: s.rejected,
            rerun: s.rerun,
            result: engines::judge_difference(s.diff, &paths, s.rejected, &ledger, &rules),
        });
    }
    let new = out.with_file_name(format!("engines-tier{tier}-rejudged.md"));
    write_text(&new, &report.to_markdown())?;
    for (c, n) in report.class_counts() {
        println!("  {c}: {n}");
    }
    for p in &report.problems {
        eprintln!("problem: {p}");
    }
    for r in report.unledgered().iter().take(40) {
        eprintln!("unledgered: {}", r.path);
    }
    println!(
        "wrote {}; {} differences, {} unledgered",
        new.display(),
        report.rows.len(),
        report.unledgered().len()
    );
    Ok(report.passes())
}

/// Writes `records` in the committed form to the baseline file of the tier.
/// Warns if the build is a debug build or a record is a timeout.
fn write_baseline(repo: &Path, tier: u8, records: &[snapshot::Record]) -> Result<()> {
    if cfg!(debug_assertions) {
        eprintln!(
            "warning: a debug build writes the baseline; a release build gives fewer timeouts"
        );
    }
    let timeouts: Vec<&str> = records
        .iter()
        .filter(|r| r.kind == Kind::Timeout)
        .map(|r| r.path.as_str())
        .collect();
    if !timeouts.is_empty() {
        eprintln!(
            "warning: the baseline has {} timeout records (the comparison skips them): {}",
            timeouts.len(),
            timeouts.join(", ")
        );
    }
    let out = repo.join(baseline::file(tier));
    write_text(&out, &baseline::to_jsonl(records)?)?;
    println!("wrote {} records to {}", records.len(), out.display());
    Ok(())
}

/// `snapshot`: checks each program of the manifest of the tier and writes the
/// records in the order of the manifest.
fn run_snapshot(flags: &Flags) -> Result<()> {
    let tier = flags.tier.context("--tier is necessary")?;
    let name = flags.facts.as_deref().unwrap_or("old");
    let Some(pipeline) = Pipeline::parse(name) else {
        bail!("unknown pipeline `{name}`: use --facts old or --facts ir");
    };
    let (m, base) = if tier == 1 {
        (tier1(flags)?, flags.repo.clone())
    } else {
        let probes = flags.probes()?;
        (tier2(&probes)?, probes)
    };
    let settings = Settings {
        pipeline,
        groups: groups_on(flags)?,
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

/// Reads the oracle cache `file`. A file that does not exist gives an empty cache.
fn read_cache(file: &Path) -> Result<Cache> {
    match std::fs::read_to_string(file) {
        Ok(text) => Cache::from_tsv(&text).with_context(|| format!("read {}", file.display())),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(Cache::default()),
        Err(e) => Err(e).with_context(|| format!("read {}", file.display())),
    }
}

/// Opens the oracle cache `file` to add rows at its end. Writes the header
/// first if the file does not exist.
fn open_journal(file: &Path) -> Result<std::fs::File> {
    if let Some(dir) = file.parent() {
        std::fs::create_dir_all(dir).with_context(|| format!("make {}", dir.display()))?;
    }
    let new = !file.exists();
    let mut f = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(file)
        .with_context(|| format!("open {}", file.display()))?;
    if new {
        writeln!(f, "{}", oracle::HEADER).with_context(|| format!("write {}", file.display()))?;
    }
    Ok(f)
}

/// `oracle`: gives the oracle verdict of each program of the manifest of the
/// tier, from the cache or from a run, and writes the cache.
fn run_oracle(flags: &Flags) -> Result<()> {
    let tier = flags.tier.context("--tier is necessary")?;
    let name = flags.engine.as_deref().unwrap_or("ast");
    let engine = Engine::parse(name)
        .with_context(|| format!("unknown engine `{name}`: use --engine ast or --engine ir"))?;
    let (m, base) = if tier == 1 {
        (tier1(flags)?, flags.repo.clone())
    } else {
        let probes = flags.probes()?;
        (tier2(&probes)?, probes)
    };
    let tier1_file = flags
        .repo
        .join("tests/gate")
        .join(oracle::cache_name(engine));
    let out = flags.out.clone().unwrap_or_else(|| {
        if tier == 1 {
            tier1_file.clone()
        } else {
            let dir = std::env::var_os("WEFT_GATE_CACHE")
                .map_or_else(|| flags.repo.join("target/gate"), PathBuf::from);
            dir.join(oracle::cache_name(engine))
        }
    });
    let interp = oracle::interp_hash(&flags.repo)?;
    let mut cache = read_cache(&out)?;
    if tier == 2 {
        cache.extend(read_cache(&tier1_file)?);
    }
    let settings = oracle::Settings {
        workers: flags.workers.unwrap_or_else(|| {
            std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get)
        }),
        limit: flags.limit.map_or(oracle::LIMIT, Duration::from_secs),
        max_steps: Some(flags.max_steps.unwrap_or(oracle::MAX_STEPS)),
        max_memory_mb: flags.max_memory.unwrap_or(oracle::MAX_MEMORY_MB),
        exe: Some(std::env::current_exe().context("find the weft-gate program")?),
        engine,
        fact_oracle: false,
    };
    let mut journal = open_journal(&out)?;
    snapshot::install_panic_hook();
    let total = m.entries.len();
    println!(
        "oracle of {total} programs with the `{}` engine on {} workers (interpreter {interp})",
        engine.name(),
        settings.workers
    );
    let start = Instant::now();
    let mut rows = Cache::default();
    let mut failed: Option<String> = None;
    let mut ended = 0;
    let summary = oracle::oracle(
        &base,
        m.entries,
        &cache,
        engine,
        &interp,
        &settings,
        |row, hit| {
            if !hit && failed.is_none() {
                let line = row.to_line();
                if let Err(e) = writeln!(journal, "{line}").and_then(|()| journal.flush()) {
                    failed = Some(format!("write {}: {e}", out.display()));
                }
            }
            rows.insert(row);
            ended += 1;
            if ended % 1000 == 0 {
                println!(
                    "{ended} of {total} programs in {:.1} s",
                    start.elapsed().as_secs_f64()
                );
            }
        },
    )?;
    if let Some(e) = failed {
        bail!("{e}");
    }
    write_text(&out, &rows.to_tsv())?;
    let counts: Vec<String> = Verdict::ALL
        .iter()
        .map(|v| {
            format!(
                "{} {}",
                summary.counts.get(v).copied().unwrap_or(0),
                v.name()
            )
        })
        .collect();
    println!(
        "wrote {} rows to {} in {:.1} s ({} from the cache, {} runs): {}",
        rows.len(),
        out.display(),
        start.elapsed().as_secs_f64(),
        summary.hits,
        summary.runs,
        counts.join(", ")
    );
    Ok(())
}

/// Writes one step of `oracle-run` and flushes the output.
fn write_step(step: &Step) {
    let mut out = std::io::stdout().lock();
    let _ = writeln!(out, "{}", step.to_line());
    let _ = out.flush();
}

/// `oracle-run`: the child process of `oracle`. Runs one program in the
/// configurations from `--from` and writes one step for each run.
///
/// A thread stops the process with the exit code [`oracle::MEMORY_EXIT`] when
/// it uses more than `--max-memory` MB, after it writes a step
/// [`Verdict::Timeout`] for the run. It also stops the process after a time
/// that is longer than the limits of all its runs, so a child does not stay
/// after its parent stops.
fn run_oracle_child(flags: &Flags) -> Result<()> {
    let base = flags.base.clone().context("--base is necessary")?;
    let path = flags.path.clone().context("--path is necessary")?;
    let from = flags.from.unwrap_or(0);
    let limit = Duration::from_millis(flags.limit_ms.unwrap_or(10_000));
    let max_memory = flags.max_memory.unwrap_or(oracle::MAX_MEMORY_MB);
    let current = Arc::new(AtomicUsize::new(from));
    let watched = Arc::clone(&current);
    let runs = u32::try_from(oracle::CONFIGS.len() + 1).unwrap_or(u32::MAX);
    let deadline = limit.saturating_mul(runs) + Duration::from_secs(60);
    let start = Instant::now();
    std::thread::spawn(move || loop {
        std::thread::sleep(Duration::from_millis(20));
        if oracle::resident_bytes().is_some_and(|b| b > max_memory.saturating_mul(1 << 20)) {
            let config = watched.load(Ordering::SeqCst);
            write_step(&Step::Run {
                config,
                verdict: Verdict::Timeout,
                detail: format!(
                    "{}: the run uses more than {max_memory} MB of memory",
                    oracle::config_text(config)
                ),
            });
            std::process::exit(oracle::MEMORY_EXIT);
        }
        if start.elapsed() > deadline {
            std::process::exit(oracle::MEMORY_EXIT + 1);
        }
    });
    let engine = match flags.engine.as_deref() {
        None => Engine::Ast,
        Some(name) => Engine::parse(name).with_context(|| format!("unknown engine `{name}`"))?,
    };
    let observe = flags.observe;
    let fact = flags.fact_oracle;
    let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        if fact {
            oracle::run_fact_configs(
                &base,
                &path,
                from,
                flags.max_steps,
                |k| current.store(k, Ordering::SeqCst),
                |step| write_step(&step),
            );
            return;
        }
        oracle::run_configs(
            &base,
            &path,
            from,
            flags.max_steps,
            engine,
            |k| current.store(k, Ordering::SeqCst),
            |step, o| {
                if let Some(line) = o.filter(|_| observe).and_then(|o| o.to_line().ok()) {
                    let mut out = std::io::stdout().lock();
                    let _ = writeln!(out, "{line}");
                }
                write_step(&step);
            },
        );
    }));
    if let Err(payload) = run {
        let text = payload
            .downcast_ref::<&str>()
            .map(ToString::to_string)
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "a panic with no text".to_string());
        let config = current.load(Ordering::SeqCst);
        write_step(&Step::Run {
            config,
            verdict: Verdict::Fault,
            detail: format!(
                "{}: the interpreter panicked: {text}",
                oracle::config_text(config)
            ),
        });
    }
    Ok(())
}

/// `fact-oracle`: the fact oracle and trace conformance (`docs/ir.md` 8.5)
/// on each program of the tier with `main` or test blocks that the `ir`
/// pipeline checks and accepts. Writes the report (default
/// `target/gate/fact-oracle-tier<N>.md`). Returns false if a run fails the
/// fact oracle or trace conformance.
fn run_fact_oracle(flags: &Flags) -> Result<bool> {
    let tier = flags.tier.context("--tier is necessary")?;
    let (m, base) = if tier == 1 {
        (tier1(flags)?, flags.repo.clone())
    } else {
        let probes = flags.probes()?;
        (tier2(&probes)?, probes)
    };
    let entries: Vec<manifest::Entry> = m
        .entries
        .into_iter()
        .filter(|e| e.has_main || e.has_tests)
        .collect();
    let settings = oracle::Settings {
        workers: flags.workers.unwrap_or_else(|| {
            std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get)
        }),
        limit: flags.limit.map_or(oracle::LIMIT, Duration::from_secs),
        max_steps: Some(flags.max_steps.unwrap_or(oracle::MAX_STEPS)),
        max_memory_mb: flags.max_memory.unwrap_or(oracle::MAX_MEMORY_MB),
        exe: Some(std::env::current_exe().context("find the weft-gate program")?),
        engine: Engine::Ir,
        fact_oracle: true,
    };
    snapshot::install_panic_hook();
    let total = entries.len();
    println!(
        "fact oracle of {total} programs on {} workers",
        settings.workers
    );
    let start = Instant::now();
    let paths: Vec<String> = entries.iter().map(|e| e.path.clone()).collect();
    let mut rows: Vec<(String, oracle::FactClass, String)> = Vec::new();
    oracle::run_all(&base, entries, &settings, |i, o| {
        let path = paths.get(i).cloned().unwrap_or_default();
        rows.push((path, oracle::fact_class(&o), o.detail));
        if rows.len() % 1000 == 0 {
            println!(
                "{} of {total} programs in {:.1} s",
                rows.len(),
                start.elapsed().as_secs_f64()
            );
        }
    })?;
    rows.sort();
    let text = oracle::fact_report(tier, &rows, start.elapsed());
    let out = flags.report.clone().unwrap_or_else(|| {
        flags
            .repo
            .join(format!("target/gate/fact-oracle-tier{tier}.md"))
    });
    write_text(&out, &text)?;
    let failed = rows.iter().filter(|r| r.1.is_failure()).count();
    println!(
        "wrote {} in {:.1} s: {failed} failures of the fact oracle",
        out.display(),
        start.elapsed().as_secs_f64()
    );
    Ok(failed == 0)
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
