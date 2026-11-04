//! The fresh sweep (plan stage C2): new generated programs, checked with the
//! `ir` pipeline, and the oracle on each program that the checker accepts.
//!
//! The generators are the Python scripts of `tools/gate/gen` ([`GENERATORS`]).
//! Each one takes its seed as an argument (`genmain.py`), so the same seed
//! gives the same program. The sweep divides `n` programs among the
//! generators ([`shares`]). Generator `g` gets the seeds `seed_base` to
//! `seed_base + n_g - 1`.
//!
//! The sweep works in chunks. For each chunk it:
//!
//! 1. runs the generator into a temporary directory;
//! 2. checks each new program with both pipelines in one analysis
//!    ([`snapshot::check_both`]): the `ir` record is the result of
//!    `weft check --facts=ir`, and the `old` record is for the report;
//! 3. runs the oracle with the `ir` engine on each program that the `ir`
//!    pipeline accepts (with [`Settings::oracle_all`], on each program), in
//!    the first `runs` configurations of [`oracle::CONFIGS`] ([`oracle::Settings::runs`]);
//! 4. keeps each program that the checker accepts and that faults, and each
//!    program on which the `ir` pipeline panics or does not end, in
//!    `OUT/kept/`;
//! 5. removes the temporary directory.
//!
//! The sweep writes one line for each program to `OUT/programs.tsv`
//! ([`ROWS_HEADER`]): the seed list. It does not keep the other programs: the
//! generator and the seed make each one again.
//!
//! A program with the same text as an earlier program of the sweep is a
//! duplicate: the sweep counts it and does not check it again.

use std::collections::{BTreeMap, HashSet};
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use weft_sema::Groups;

use crate::classify;
use crate::digest;
use crate::manifest::{self, Entry, Mode};
use crate::oracle::{self, Engine, Verdict};
use crate::snapshot::{self, Both, Kind, Pipeline};
use crate::Error;

/// The generators, in the order of the sweep. Each is the script
/// `tools/gate/gen/<name>.py`.
pub const GENERATORS: [&str; 5] = ["gen3", "gen4", "mutate3", "gen", "sweep4"];

/// The directory of the generators, relative to the repository.
pub const GEN_DIR: &str = "tools/gate/gen";

/// The default number of programs in one chunk of one generator.
pub const CHUNK: usize = 500;

/// The default number of configurations of the oracle: the seeds 1, 2 and 3.
pub const RUNS: usize = 3;

/// The texts of a fault that are a soundness signal.
///
/// These are the texts of the function `isfault` of the review scripts, and
/// a stop of the interpreter. An accepted fault with no such text is also reported, with the mark
/// `other`.
pub const SIGNAL: [&str; 17] = [
    "oracle:",
    "used after",
    "moved",
    "freed",
    "dangling",
    "leak",
    "linear",
    "once",
    "twice",
    "called",
    "another variant",
    "does not exist",
    "no handler",
    "changed shape",
    "the output holds",
    "panicked",
    "the interpreter stopped",
];

/// The first line of `programs.tsv`.
pub const ROWS_HEADER: &str = "generator\tseed\thash\tscope\tir\told\tverdict\tdetail";

/// The settings of a sweep.
#[derive(Clone, Debug)]
pub struct Settings {
    /// The number of programs of all the generators.
    pub n: usize,
    /// The first seed of each generator.
    pub seed_base: u64,
    /// The generators, a subset of [`GENERATORS`].
    pub generators: Vec<String>,
    /// The number of worker threads of the check and of the oracle.
    pub workers: usize,
    /// The number of programs in one chunk.
    pub chunk: usize,
    /// The Python program.
    pub python: PathBuf,
    /// The output directory.
    pub out: PathBuf,
    /// The construct groups of the `ir` pipeline.
    pub groups: Groups,
    /// The time limit of the check of one program.
    pub check_limit: Duration,
    /// The settings of the oracle (the engine is always [`Engine::Ir`]).
    pub oracle: oracle::Settings,
    /// Runs the oracle on each program, not only on the programs that the
    /// checker accepts. The counts then show how many faults the checker
    /// rejects.
    pub oracle_all: bool,
}

/// The counts of one generator.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    /// The programs that the generator wrote.
    pub generated: usize,
    /// The programs with the text of an earlier program of the sweep.
    pub duplicates: usize,
    /// The programs in scope of the `ir` pipeline.
    pub in_scope: usize,
    /// The programs that `--facts=ir` accepts.
    pub ir_accepted: usize,
    /// The programs that `--facts=old` accepts.
    pub old_accepted: usize,
    /// The programs that ran in the oracle.
    pub oracle_runs: usize,
    /// The programs that ran in the oracle and faulted.
    pub faulted: usize,
    /// The programs that `--facts=ir` accepts and that fault.
    pub accepted_faults: usize,
    /// The accepted faults with a text of [`SIGNAL`].
    pub signal_faults: usize,
    /// The programs on which the `ir` pipeline panics or does not end.
    pub crashes: usize,
}

impl Counts {
    const fn add(&mut self, o: &Self) {
        self.generated += o.generated;
        self.duplicates += o.duplicates;
        self.in_scope += o.in_scope;
        self.ir_accepted += o.ir_accepted;
        self.old_accepted += o.old_accepted;
        self.oracle_runs += o.oracle_runs;
        self.faulted += o.faulted;
        self.accepted_faults += o.accepted_faults;
        self.signal_faults += o.signal_faults;
        self.crashes += o.crashes;
    }
}

/// The kind of a finding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FindingKind {
    /// `--facts=ir` accepts the program, and the oracle faults.
    AcceptedFault,
    /// The `ir` pipeline panics or does not end.
    Crash,
}

impl FindingKind {
    /// The name in the report.
    pub const fn name(self) -> &'static str {
        match self {
            Self::AcceptedFault => "accepted-fault",
            Self::Crash => "crash",
        }
    }
}

/// A program that the sweep keeps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Finding {
    /// The kind.
    pub kind: FindingKind,
    /// The generator.
    pub generator: String,
    /// The seed.
    pub seed: u64,
    /// The file in the output directory, relative to it.
    pub file: String,
    /// True if the program is in scope of the `ir` pipeline.
    pub in_scope: bool,
    /// True if `--facts=old` accepts the program.
    pub old_accepts: bool,
    /// True if the fault has a text of [`SIGNAL`].
    pub signal: bool,
    /// The verdict detail of the oracle, or the message of the crash.
    pub detail: String,
}

/// The result of a sweep.
#[derive(Clone, Debug, Default)]
pub struct Sweep {
    /// The counts of each generator, in the order of the sweep.
    pub counts: Vec<(String, Counts)>,
    /// The seeds of each generator: the first and the last.
    pub seeds: Vec<(String, u64, u64)>,
    /// The kept programs.
    pub findings: Vec<Finding>,
    /// The time of the sweep.
    pub elapsed: Duration,
}

impl Sweep {
    /// The sum of the counts of all generators.
    pub fn total(&self) -> Counts {
        let mut t = Counts::default();
        for (_, c) in &self.counts {
            t.add(c);
        }
        t
    }

    /// True if the sweep found no accepted fault and no crash.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }
}

/// True if the detail of a fault has a text of [`SIGNAL`].
pub fn is_signal(detail: &str) -> bool {
    SIGNAL.iter().any(|s| detail.contains(s))
}

/// Divides `n` programs among `generators`: each gets `n / k`, and the
/// first `n % k` get one more.
pub fn shares(n: usize, generators: &[String]) -> Vec<(String, usize)> {
    let k = generators.len().max(1);
    generators
        .iter()
        .enumerate()
        .map(|(i, g)| (g.clone(), n / k + usize::from(i < n % k)))
        .filter(|(_, c)| *c > 0)
        .collect()
}

/// Reads a list of generators (`gen3,gen4`). Each name must be one of
/// [`GENERATORS`].
pub fn parse_generators(text: &str) -> Result<Vec<String>, Error> {
    let mut out = Vec::new();
    for name in text.split(',').map(str::trim).filter(|s| !s.is_empty()) {
        if !GENERATORS.contains(&name) {
            return Err(Error::Sweep(format!(
                "unknown generator `{name}`: use one of {}",
                GENERATORS.join(", ")
            )));
        }
        if !out.iter().any(|g| g == name) {
            out.push(name.to_string());
        }
    }
    if out.is_empty() {
        return Err(Error::Sweep("no generator".to_string()));
    }
    Ok(out)
}

/// Runs the generator `name` for the seeds `from` to `from + n - 1` into
/// `dir`. Returns the seed and the file name of each program, in the order of
/// the seeds.
pub fn generate(
    repo: &Path,
    python: &Path,
    name: &str,
    from: u64,
    n: usize,
    dir: &Path,
) -> Result<Vec<(u64, String)>, Error> {
    let script = repo.join(GEN_DIR).join(format!("{name}.py"));
    // `-I`: no path or setting of the environment; `-B`: no `__pycache__`.
    let out = Command::new(python)
        .arg("-I")
        .arg("-B")
        .arg(&script)
        .arg("--seed-base")
        .arg(from.to_string())
        .arg("--n")
        .arg(n.to_string())
        .arg("--out")
        .arg(dir)
        .env_remove("GEN_OFF")
        .output()
        .map_err(|e| Error::io(python, e))?;
    if !out.status.success() {
        return Err(Error::Sweep(format!(
            "{} {} --seed-base {from} --n {n}: {}: {}",
            python.display(),
            script.display(),
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        )));
    }
    let prefix = format!("{name}_");
    let mut files = Vec::new();
    let read = std::fs::read_dir(dir).map_err(|e| Error::io(dir, e))?;
    for item in read {
        let item = item.map_err(|e| Error::io(dir, e))?;
        let file = item.file_name().to_string_lossy().into_owned();
        let seed = file
            .strip_prefix(&prefix)
            .and_then(|s| s.strip_suffix(".wf"))
            .and_then(|s| s.parse::<u64>().ok());
        if let Some(seed) = seed {
            files.push((seed, file));
        }
    }
    files.sort_unstable();
    Ok(files)
}

/// The errors of a record as one column: `accept`, or the codes.
fn column(r: &snapshot::Record) -> String {
    let errors = classify::errors(r);
    if errors.is_empty() {
        return "accept".to_string();
    }
    let mut codes: Vec<&str> = errors.iter().map(|d| d.0.as_str()).collect();
    codes.dedup();
    codes.join(",")
}

/// The text on one line for a TSV column.
fn cell(text: &str) -> String {
    text.replace(['\t', '\n', '\r'], " ")
}

/// The result of the check and the oracle for one program of a chunk.
struct Program {
    seed: u64,
    file: String,
    entry: Entry,
    both: Option<Both>,
    outcome: Option<oracle::Outcome>,
}

/// Runs a sweep. Calls `progress` with a line of text after each chunk.
///
/// # Errors
///
/// Returns an error if a generator fails, a file cannot be read or written,
/// or the system cannot start a worker thread.
pub fn run(
    repo: &Path,
    settings: &Settings,
    mut progress: impl FnMut(&str),
) -> Result<Sweep, Error> {
    let start = Instant::now();
    let kept = settings.out.join("kept");
    let tmp = settings.out.join("tmp");
    std::fs::create_dir_all(&kept).map_err(|e| Error::io(&kept, e))?;
    let rows_file = settings.out.join("programs.tsv");
    let mut rows = std::fs::File::create(&rows_file).map_err(|e| Error::io(&rows_file, e))?;
    writeln!(rows, "{ROWS_HEADER}").map_err(|e| Error::io(&rows_file, e))?;
    let oracle_settings = oracle::Settings {
        engine: Engine::Ir,
        workers: settings.workers,
        ..settings.oracle.clone()
    };
    let check_settings = snapshot::Settings {
        pipeline: Pipeline::Ir,
        groups: settings.groups,
        workers: settings.workers,
        limit: settings.check_limit,
    };
    let mut seen: HashSet<String> = HashSet::new();
    let mut sweep = Sweep::default();
    for (name, count) in shares(settings.n, &settings.generators) {
        let mut counts = Counts::default();
        let last = settings
            .seed_base
            .saturating_add(u64::try_from(count).unwrap_or(u64::MAX))
            .saturating_sub(1);
        sweep.seeds.push((name.clone(), settings.seed_base, last));
        let mut done = 0;
        while done < count {
            let size = settings.chunk.max(1).min(count - done);
            let from = settings
                .seed_base
                .saturating_add(u64::try_from(done).unwrap_or(u64::MAX));
            if tmp.exists() {
                std::fs::remove_dir_all(&tmp).map_err(|e| Error::io(&tmp, e))?;
            }
            std::fs::create_dir_all(&tmp).map_err(|e| Error::io(&tmp, e))?;
            let files = generate(repo, &settings.python, &name, from, size, &tmp)?;
            let chunk = sweep_chunk(
                &tmp,
                &name,
                files,
                &mut seen,
                &check_settings,
                &oracle_settings,
                settings.oracle_all,
            )?;
            for p in &chunk {
                record(&name, p, &mut counts, &mut rows, &rows_file)?;
                if let Some(f) = finding(&name, p, &tmp, &kept)? {
                    sweep.findings.push(f);
                }
            }
            std::fs::remove_dir_all(&tmp).map_err(|e| Error::io(&tmp, e))?;
            done += size;
            progress(&format!(
                "{name}: {done} of {count} programs, {} accepted, {} accepted faults, {} crashes, {:.1} s",
                counts.ir_accepted,
                counts.accepted_faults,
                counts.crashes,
                start.elapsed().as_secs_f64()
            ));
        }
        sweep.counts.push((name, counts));
    }
    sweep.elapsed = start.elapsed();
    Ok(sweep)
}

/// Checks the programs `files` in `dir` and runs the oracle on them.
fn sweep_chunk(
    dir: &Path,
    name: &str,
    files: Vec<(u64, String)>,
    seen: &mut HashSet<String>,
    check: &snapshot::Settings,
    oracle_settings: &oracle::Settings,
    oracle_all: bool,
) -> Result<Vec<Program>, Error> {
    let mut programs = Vec::new();
    for (seed, file) in files {
        let path = dir.join(&file);
        let text = std::fs::read_to_string(&path).map_err(|e| Error::io(&path, e))?;
        let hash = digest::sha256(&text);
        let fresh = seen.insert(hash.clone());
        let (has_main, has_tests) = manifest::scan(&text);
        let entry = Entry {
            hash,
            path: file.clone(),
            set: name.to_string(),
            mode: Mode::File,
            has_main,
            has_tests,
            others: Vec::new(),
        };
        programs.push((
            fresh,
            Program {
                seed,
                file,
                entry,
                both: None,
                outcome: None,
            },
        ));
    }
    let todo: Vec<usize> = (0..programs.len())
        .filter(|&i| programs.get(i).is_some_and(|p| p.0))
        .collect();
    let entries: Vec<Entry> = todo
        .iter()
        .filter_map(|&i| programs.get(i).map(|p| p.1.entry.clone()))
        .collect();
    let mut checked: Vec<Option<Both>> = vec![None; entries.len()];
    snapshot::run_both(dir, entries, check, |i, both| {
        if let Some(slot) = checked.get_mut(i) {
            *slot = Some(both);
        }
    })?;
    for (k, both) in checked.into_iter().enumerate() {
        if let Some(p) = todo.get(k).and_then(|&i| programs.get_mut(i)) {
            p.1.both = both;
        }
    }
    let run: Vec<usize> = todo
        .iter()
        .copied()
        .filter(|&i| {
            programs.get(i).is_some_and(|p| {
                p.1.both.as_ref().is_some_and(|b| {
                    accepts(&b.ir.record) || (oracle_all && b.ir.record.kind == Kind::Ok)
                })
            })
        })
        .collect();
    let entries: Vec<Entry> = run
        .iter()
        .filter_map(|&i| programs.get(i).map(|p| p.1.entry.clone()))
        .collect();
    let mut outcomes: Vec<Option<oracle::Outcome>> = vec![None; entries.len()];
    oracle::run_all(dir, entries, oracle_settings, |i, o| {
        if let Some(slot) = outcomes.get_mut(i) {
            *slot = Some(o);
        }
    })?;
    for (k, o) in outcomes.into_iter().enumerate() {
        if let Some(p) = run.get(k).and_then(|&i| programs.get_mut(i)) {
            p.1.outcome = o;
        }
    }
    Ok(programs
        .into_iter()
        .map(|(fresh, mut p)| {
            if !fresh {
                p.both = None;
                p.outcome = None;
            }
            p
        })
        .collect())
}

/// True if the record has no error and is [`Kind::Ok`].
fn accepts(r: &snapshot::Record) -> bool {
    r.kind == Kind::Ok && classify::errors(r).is_empty()
}

/// True if the `ir` pipeline panics or does not end on the program.
fn crashed(b: &Both) -> bool {
    matches!(b.ir.record.kind, Kind::Crash | Kind::Timeout) || !b.ir.record.problems.is_empty()
}

/// Adds the program to the counts and writes its row.
fn record(
    name: &str,
    p: &Program,
    counts: &mut Counts,
    rows: &mut std::fs::File,
    rows_file: &Path,
) -> Result<(), Error> {
    counts.generated += 1;
    let Some(b) = &p.both else {
        counts.duplicates += 1;
        return writeln!(
            rows,
            "{name}\t{}\t{}\t-\tduplicate\t-\t-\t",
            p.seed, p.entry.hash
        )
        .map_err(|e| Error::io(rows_file, e));
    };
    let ir_ok = accepts(&b.ir.record);
    counts.in_scope += usize::from(b.in_scope);
    counts.ir_accepted += usize::from(ir_ok);
    counts.old_accepted += usize::from(accepts(&b.old.record));
    counts.crashes += usize::from(crashed(b));
    let (verdict, detail) = match &p.outcome {
        Some(o) => {
            counts.oracle_runs += 1;
            let fault = o.verdict == Verdict::Fault;
            counts.faulted += usize::from(fault);
            if fault && ir_ok {
                counts.accepted_faults += 1;
                counts.signal_faults += usize::from(is_signal(&o.detail));
            }
            (o.verdict.name(), o.detail.as_str())
        }
        None => ("-", ""),
    };
    writeln!(
        rows,
        "{name}\t{}\t{}\t{}\t{}\t{}\t{verdict}\t{}",
        p.seed,
        p.entry.hash,
        if b.in_scope { "in" } else { "out" },
        cell(&column(&b.ir.record)),
        cell(&column(&b.old.record)),
        cell(detail)
    )
    .map_err(|e| Error::io(rows_file, e))
}

/// The finding of the program, if the sweep keeps it. Copies the program
/// into `kept`.
fn finding(name: &str, p: &Program, dir: &Path, kept: &Path) -> Result<Option<Finding>, Error> {
    let Some(b) = &p.both else {
        return Ok(None);
    };
    let (kind, detail, signal) = if crashed(b) {
        let text = b.ir.record.message.clone().unwrap_or_default();
        (FindingKind::Crash, text, true)
    } else {
        match &p.outcome {
            Some(o) if o.verdict == Verdict::Fault && accepts(&b.ir.record) => (
                FindingKind::AcceptedFault,
                o.detail.clone(),
                is_signal(&o.detail),
            ),
            _ => return Ok(None),
        }
    };
    let from = dir.join(&p.file);
    let to = kept.join(&p.file);
    std::fs::copy(&from, &to).map_err(|e| Error::io(&to, e))?;
    Ok(Some(Finding {
        kind,
        generator: name.to_string(),
        seed: p.seed,
        file: format!("kept/{}", p.file),
        in_scope: b.in_scope,
        old_accepts: accepts(&b.old.record),
        signal,
        detail,
    }))
}

/// The report of a sweep, in Markdown.
pub fn report(sweep: &Sweep, settings: &Settings) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "# Fresh sweep (plan stage C2)\n");
    let secs = sweep.elapsed.as_secs_f64();
    let total = sweep.total();
    let rate = if secs > 0.0 {
        f64::from(u32::try_from(total.generated).unwrap_or(u32::MAX)) / secs
    } else {
        0.0
    };
    let _ = writeln!(
        s,
        "{} programs in {secs:.1} s ({rate:.1} programs/s) on {} workers. Seed base {}. \
         The oracle runs the `ir` engine in the first {} configurations{}.\n",
        total.generated,
        settings.workers,
        settings.seed_base,
        settings.oracle.runs,
        if settings.oracle_all {
            " on each program"
        } else {
            " on each program that the checker accepts"
        }
    );
    let _ = writeln!(s, "## Counts\n");
    let _ = writeln!(
        s,
        "| generator | seeds | generated | duplicates | in scope | ir accepts | old accepts | oracle runs | faulted | accepted faults | signal | crashes |"
    );
    let _ = writeln!(
        s,
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"
    );
    let seeds: BTreeMap<&str, (u64, u64)> = sweep
        .seeds
        .iter()
        .map(|(g, a, b)| (g.as_str(), (*a, *b)))
        .collect();
    let row = |s: &mut String, name: &str, range: String, c: &Counts| {
        let _ = writeln!(
            s,
            "| {name} | {range} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
            c.generated,
            c.duplicates,
            c.in_scope,
            c.ir_accepted,
            c.old_accepted,
            c.oracle_runs,
            c.faulted,
            c.accepted_faults,
            c.signal_faults,
            c.crashes
        );
    };
    for (g, c) in &sweep.counts {
        let range = seeds
            .get(g.as_str())
            .map_or_else(String::new, |(a, b)| format!("{a} to {b}"));
        row(&mut s, g, range, c);
    }
    row(&mut s, "all", String::new(), &total);
    let _ = writeln!(s, "\n## Kept programs\n");
    if sweep.findings.is_empty() {
        let _ = writeln!(s, "None: no accepted fault and no crash.");
        return s;
    }
    let _ = writeln!(
        s,
        "Make a program again with `python3 -I {GEN_DIR}/GENERATOR.py SEED`.\n"
    );
    let _ = writeln!(
        s,
        "| kind | generator | seed | file | scope | old | signal | detail |"
    );
    let _ = writeln!(s, "| --- | --- | ---: | --- | --- | --- | --- | --- |");
    for f in &sweep.findings {
        let _ = writeln!(
            s,
            "| {} | {} | {} | `{}` | {} | {} | {} | {} |",
            f.kind.name(),
            f.generator,
            f.seed,
            f.file,
            if f.in_scope { "in" } else { "out" },
            if f.old_accepts { "accepts" } else { "rejects" },
            if f.signal { "yes" } else { "other" },
            cell(&f.detail).replace('|', "\\|")
        );
    }
    s
}
