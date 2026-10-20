//! The oracle cache (plan §2.4): the verdict of the interpreter oracle for
//! each program, computed once for each interpreter version.
//!
//! The oracle runs the program with no check (`--unchecked`), with the oracle
//! checks on (`RunOptions::oracle`), in the six configurations of the round-3
//! harness ([`CONFIGS`]). It runs `fn main`. A program with no `main` runs its
//! test blocks. The verdict of one run is one of [`Verdict`]. The verdict of
//! the program is the first verdict in the order of [`Verdict::ALL`] that a run
//! gives. A run that faults stops the runs of its program, because no other
//! verdict comes before `fault`.
//!
//! The runs use [`weft_interp::run_analysis_main`] and
//! [`weft_interp::run_analysis_tests`]: the checker does not see the program,
//! so no task is stealable. The verdict does not depend on the fact generator
//! or the checker.
//!
//! The key of a verdict is the hash of the program text (the hash of the
//! manifest entry), the engine ([`Engine`]) and the hash of the interpreter
//! sources ([`interp_hash`]). The cache is a TSV file ([`Cache`]): for tier 1
//! `tests/gate/oracle-ast.tsv` (committed), for tier 2 the same name in
//! `$WEFT_GATE_CACHE` (default `target/gate/`).
//!
//! Each program runs in child processes (`weft-gate oracle-run`,
//! [`run_isolated`]), because a run that does not end, or that uses too much
//! memory, cannot be stopped in this process. Three limits stop such a run, and
//! each gives [`Verdict::Timeout`]: the step limit ([`MAX_STEPS`]), the time
//! limit of one run ([`LIMIT`]: the parent stops the child, and a new child
//! runs the next configurations), and the memory limit ([`MAX_MEMORY_MB`]: the
//! child stops itself). A child that stops with no verdict, for example at a
//! stack overflow, gives [`Verdict::Fault`] (the harness calls it a panic).

use std::collections::BTreeMap;
use std::io::{BufRead as _, BufReader, Read as _};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::sync::Arc;
use std::time::{Duration, Instant};

use sha2::{Digest as _, Sha256};
use weft_cli::package::{self, Package, Profile};
use weft_interp::{ErrorKind, RunOptions, RunOutcome, RuntimeError, TestOutcome};

use crate::manifest::{hex, Entry};
use crate::pool::{self, Ended};
use crate::Error;

/// The texts of a run-time error that stops the run and is not a soundness
/// signal. The same texts as the list `BENIGN` of the round-3 harness
/// (`tools/gate/gen/harness.py`).
pub const BENIGN: [&str; 9] = [
    "out of bounds",
    "integer overflow",
    "unsigned underflow",
    "integer underflow",
    "does not fit in",
    "cannot listen on",
    "division by zero",
    "duration underflow",
    "split point is out of bounds",
];

/// The six configurations of the round-3 harness: the seed and the number of
/// virtual workers.
pub const CONFIGS: [(u64, usize); 6] = [(1, 1), (2, 4), (3, 2), (7, 4), (11, 1), (42, 3)];

/// The default time limit for one run. The pool gives the runs of one program
/// six times this limit (one time for each of [`CONFIGS`]).
pub const LIMIT: Duration = Duration::from_secs(10);

/// The default step limit for one run. The release build runs about 25
/// million steps in a second, so a run that ends at this limit takes about 2 s.
pub const MAX_STEPS: u64 = 50_000_000;

/// The default memory limit of a child process, in MB.
pub const MAX_MEMORY_MB: u64 = 2048;

/// The interpreter sources, relative to the repository. The key of a verdict
/// holds their hash ([`interp_hash`]).
pub const INTERP_SRC: &str = "crates/weft-interp/src";

/// The first line of a cache file.
pub const HEADER: &str = "hash\tengine\tinterp\tverdict\tdetail\tpath";

/// The most bytes of the detail of a verdict.
pub const MAX_DETAIL: usize = 300;

/// The texts in the output of a run that show a fault (the round-3 harness).
pub const FAULT_MARKERS: [&str; 3] = ["<moved>", "<freed>", "<dangling>"];

/// The interpreter that runs the program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Engine {
    /// The interpreter that compiles the AST (`--engine=ast`).
    Ast,
}

impl Engine {
    /// Returns the engine with the name `name`, or `None`.
    pub fn parse(name: &str) -> Option<Self> {
        match name {
            "ast" => Some(Self::Ast),
            _ => None,
        }
    }

    /// The name, as `--engine` takes it.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Ast => "ast",
        }
    }
}

/// The name of the cache file of `engine`.
pub fn cache_name(engine: Engine) -> String {
    format!("oracle-{}.tsv", engine.name())
}

/// The verdict of the oracle. The order of the variants is the order of
/// precedence: the verdict of a program is the first that one of its runs
/// gives.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Verdict {
    /// An oracle fault, another run-time error that is not [`BENIGN`], a fault
    /// marker in the output, or a panic of the interpreter.
    Fault,
    /// The run does not end: the time limit, the step limit, or a deadlock.
    Timeout,
    /// The program fails through `fail`, or an `assert` is false.
    Fail,
    /// A run-time error of the [`BENIGN`] list.
    Benign,
    /// The run ends with no error.
    Clean,
    /// No `main` and no test block, or the program does not load (for example,
    /// it does not parse).
    NotRunnable,
}

impl Verdict {
    /// All the verdicts, in the order of precedence.
    pub const ALL: [Self; 6] = [
        Self::Fault,
        Self::Timeout,
        Self::Fail,
        Self::Benign,
        Self::Clean,
        Self::NotRunnable,
    ];

    /// The name in the cache.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Fault => "fault",
            Self::Timeout => "timeout",
            Self::Fail => "fail",
            Self::Benign => "benign",
            Self::Clean => "clean",
            Self::NotRunnable => "not-runnable",
        }
    }

    /// Returns the verdict with the name `name`, or `None`.
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|v| v.name() == name)
    }
}

/// The verdict of a program, and what gave it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outcome {
    /// The verdict.
    pub verdict: Verdict,
    /// The configuration and the error that gave the verdict, on one line.
    pub detail: String,
}

impl Outcome {
    fn new(verdict: Verdict, detail: impl Into<String>) -> Self {
        Self {
            verdict,
            detail: one_line(&detail.into()),
        }
    }
}

/// The settings of the oracle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Settings {
    /// The number of worker threads (at least 1).
    pub workers: usize,
    /// The time limit for one run.
    pub limit: Duration,
    /// The step limit for one run.
    pub max_steps: Option<u64>,
    /// The memory limit of a child process in MB ([`run_isolated`]).
    pub max_memory_mb: u64,
    /// The `weft-gate` program. With it, each program runs in child processes
    /// ([`run_isolated`]). With no program, each program runs on a worker
    /// thread of this process ([`run_entry`]): then a run that does not end
    /// keeps its worker thread busy, a run that uses too much memory can stop
    /// this process, and a relative path that a program reads starts at the
    /// working directory of this process. Use it only for tests.
    pub exe: Option<PathBuf>,
}

impl Default for Settings {
    fn default() -> Self {
        Self {
            workers: 1,
            limit: LIMIT,
            max_steps: Some(MAX_STEPS),
            max_memory_mb: MAX_MEMORY_MB,
            exe: None,
        }
    }
}

/// True if the message of a run-time error holds a text of [`BENIGN`].
pub fn is_benign(message: &str) -> bool {
    BENIGN.iter().any(|b| message.contains(b))
}

/// The text on one line: each tab, carriage return and line feed becomes a
/// space, and the text has at most [`MAX_DETAIL`] bytes.
fn one_line(text: &str) -> String {
    let mut s: String = text
        .trim()
        .chars()
        .map(|c| {
            if matches!(c, '\t' | '\n' | '\r') {
                ' '
            } else {
                c
            }
        })
        .collect();
    if s.len() > MAX_DETAIL {
        let mut end = MAX_DETAIL;
        while !s.is_char_boundary(end) {
            end -= 1;
        }
        s.truncate(end);
    }
    s
}

/// The verdict of a run-time error of this kind and message.
fn error_verdict(kind: ErrorKind, message: &str) -> Verdict {
    match kind {
        ErrorKind::Fault if is_benign(message) => Verdict::Benign,
        ErrorKind::Fault => Verdict::Fault,
        ErrorKind::StepLimit | ErrorKind::Deadlock => Verdict::Timeout,
        ErrorKind::Failed | ErrorKind::Assertion => Verdict::Fail,
        ErrorKind::NoMain => Verdict::NotRunnable,
    }
}

/// The verdict of the output of a run with no run-time error, or with an
/// error that is not a fault: a fault marker gives [`Verdict::Fault`].
fn marker(out: &RunOutcome) -> Option<&'static str> {
    FAULT_MARKERS.into_iter().find(|m| out.stdout.contains(m))
}

/// The location of a run-time error, for a program of one file.
fn location(pkg: &Package, base: &Path, e: &RuntimeError) -> String {
    match (e.span, pkg.files.as_slice()) {
        (Some(span), [_, file]) => {
            let (line, col) = file.line_col(span.lo);
            let name = crate::digest::relative_name(base, &file.name);
            format!(" at {name}:{line}:{col}")
        }
        _ => String::new(),
    }
}

/// The verdict of one run of `main`, in the order of the round-3 harness: a
/// run-time error that is a fault, a fault marker in the output, a run that
/// does not end, then another error.
fn main_verdict(
    pkg: &Package,
    base: &Path,
    run: &Result<RunOutcome, RuntimeError>,
) -> (Verdict, String) {
    match run {
        Ok(out) => match marker(out) {
            Some(m) => (Verdict::Fault, format!("the output holds `{m}`")),
            None => (Verdict::Clean, String::new()),
        },
        Err(e) => {
            let text = format!("{e}{}", location(pkg, base, e));
            let v = error_verdict(e.kind, &e.message);
            if e.kind != ErrorKind::Fault {
                if let Some(m) = marker(&e.outcome) {
                    return (Verdict::Fault, format!("the output holds `{m}`; {text}"));
                }
            }
            (v, text)
        }
    }
}

/// The kind of the error in the message of a failed test: the message starts
/// with the display text of the kind (`RuntimeError` shows `KIND: MESSAGE`).
fn test_error_kind(message: &str) -> Option<(ErrorKind, &str)> {
    [
        ErrorKind::Failed,
        ErrorKind::Assertion,
        ErrorKind::Fault,
        ErrorKind::StepLimit,
        ErrorKind::Deadlock,
        ErrorKind::NoMain,
    ]
    .into_iter()
    .find_map(|k| {
        message
            .strip_prefix(&format!("{k}: "))
            .map(|rest| (k, rest))
    })
}

/// The verdict of one test block.
fn test_verdict(t: &TestOutcome) -> (Verdict, String) {
    let name = format!("test `{}`", t.name);
    match &t.message {
        None => match marker(&t.outcome) {
            Some(m) => (Verdict::Fault, format!("{name}: the output holds `{m}`")),
            None => (Verdict::Clean, String::new()),
        },
        Some(message) => {
            let (kind, rest) = test_error_kind(message).unwrap_or((ErrorKind::Fault, message));
            let v = error_verdict(kind, rest);
            if kind != ErrorKind::Fault {
                if let Some(m) = marker(&t.outcome) {
                    return (
                        Verdict::Fault,
                        format!("{name}: the output holds `{m}`; {message}"),
                    );
                }
            }
            (v, format!("{name}: {message}"))
        }
    }
}

/// Keeps in `best` the first verdict in the order of precedence. Of two equal
/// verdicts, it keeps the earlier one.
fn keep_first(best: &mut Option<(Verdict, String)>, next: (Verdict, String)) {
    if best.as_ref().is_none_or(|(v, _)| next.0 < *v) {
        *best = Some(next);
    }
}

/// One step of the runs of a program: the verdict of one configuration, or a
/// program that cannot run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    /// The program does not load, or it has no `main` and no test block.
    NotRunnable(String),
    /// The verdict of the run in configuration `config` (an index of
    /// [`CONFIGS`]).
    Run {
        /// The index of the configuration.
        config: usize,
        /// The verdict of the run.
        verdict: Verdict,
        /// The configuration and the error, on one line.
        detail: String,
    },
}

/// Each line of a step in the output of `weft-gate oracle-run` starts with
/// this text. The parent ignores other lines.
pub const STEP_PREFIX: &str = "@oracle";

impl Step {
    /// The step as one line of the output of `weft-gate oracle-run`.
    pub fn to_line(&self) -> String {
        match self {
            Self::NotRunnable(detail) => {
                format!("{STEP_PREFIX}\t-\tnot-runnable\t{}", one_line(detail))
            }
            Self::Run {
                config,
                verdict,
                detail,
            } => format!(
                "{STEP_PREFIX}\t{config}\t{}\t{}",
                verdict.name(),
                one_line(detail)
            ),
        }
    }

    /// Reads a line of [`Step::to_line`]. Another line gives `None`.
    pub fn parse_line(line: &str) -> Option<Self> {
        let mut cols = line.splitn(4, '\t');
        if cols.next() != Some(STEP_PREFIX) {
            return None;
        }
        let config = cols.next()?;
        let verdict = Verdict::parse(cols.next()?)?;
        let detail = cols.next().unwrap_or_default().to_string();
        if config == "-" {
            return (verdict == Verdict::NotRunnable).then_some(Self::NotRunnable(detail));
        }
        let config = config
            .parse::<usize>()
            .ok()
            .filter(|&c| c < CONFIGS.len())?;
        Some(Self::Run {
            config,
            verdict,
            detail,
        })
    }
}

/// The text of configuration `config` for a detail.
pub fn config_text(config: usize) -> String {
    CONFIGS.get(config).map_or_else(
        || format!("configuration {config}"),
        |(seed, workers)| format!("seed {seed}, workers {workers}"),
    )
}

/// Runs the program at `path` below `base` in the configurations of
/// [`CONFIGS`] from index `from`, on this thread.
///
/// Calls `start` with the index of each configuration before its run, and
/// `emit` with each step. The runs stop after a run that faults, because no
/// other verdict comes before `fault`.
///
/// A panic of the interpreter continues in the caller.
pub fn run_configs(
    base: &Path,
    path: &str,
    from: usize,
    max_steps: Option<u64>,
    mut start: impl FnMut(usize),
    mut emit: impl FnMut(Step),
) {
    let pkg = match package::load(&base.join(path)) {
        Ok(pkg) => pkg,
        Err(e) => {
            let dir = format!("{}/", base.display());
            let text = format!("the program does not load: {e:#}").replace(&dir, "");
            emit(Step::NotRunnable(text));
            return;
        }
    };
    let opts = pkg.options(Profile::default());
    let analysis = weft_sema::analyze(&pkg.units, opts);
    for (config, &(seed, workers)) in CONFIGS.iter().enumerate().skip(from) {
        start(config);
        let run_opts = RunOptions {
            seed,
            workers,
            max_steps,
            capture_output: true,
            no_runtime: opts.no_runtime,
            oracle: true,
            ..RunOptions::default()
        };
        let mut best: Option<(Verdict, String)> = None;
        let run = weft_interp::run_analysis_main(&analysis, &run_opts);
        if matches!(&run, Err(e) if e.kind == ErrorKind::NoMain) {
            let tests = weft_interp::run_analysis_tests(&analysis, &run_opts);
            if tests.is_empty() {
                emit(Step::NotRunnable("no `main` and no test block".to_string()));
                return;
            }
            for t in &tests {
                keep_first(&mut best, test_verdict(t));
            }
        } else {
            keep_first(&mut best, main_verdict(&pkg, base, &run));
        }
        let (verdict, text) = best.unwrap_or((Verdict::Clean, String::new()));
        let detail = if verdict == Verdict::Clean {
            String::new()
        } else {
            format!("{}: {text}", config_text(config))
        };
        emit(Step::Run {
            config,
            verdict,
            detail,
        });
        if verdict == Verdict::Fault {
            return;
        }
    }
}

/// Combines the steps of the runs of a program into its outcome.
#[derive(Clone, Debug, Default)]
struct Combine {
    best: Option<(Verdict, String)>,
    not_runnable: Option<String>,
}

impl Combine {
    fn add(&mut self, step: Step) {
        match step {
            Step::NotRunnable(detail) => self.not_runnable = Some(detail),
            Step::Run {
                verdict, detail, ..
            } => keep_first(&mut self.best, (verdict, detail)),
        }
    }

    const fn is_final(&self) -> bool {
        self.not_runnable.is_some() || matches!(self.best, Some((Verdict::Fault, _)))
    }

    fn outcome(self) -> Outcome {
        match (self.not_runnable, self.best) {
            (Some(detail), _) => Outcome::new(Verdict::NotRunnable, detail),
            (None, Some((verdict, detail))) => Outcome::new(verdict, detail),
            (None, None) => Outcome::new(Verdict::NotRunnable, "no run"),
        }
    }
}

/// Runs the program `entry` below `base` in the six configurations, on this
/// thread, and gives its verdict. Only the step limit stops a run that does
/// not end.
///
/// A panic of the interpreter continues in the caller.
pub fn run_entry(base: &Path, entry: &Entry, settings: &Settings) -> Outcome {
    let mut c = Combine::default();
    run_configs(
        base,
        &entry.path,
        0,
        settings.max_steps,
        |_| {},
        |s| c.add(s),
    );
    c.outcome()
}

/// What a reader thread of a child process sends.
enum ChildMsg {
    /// A step.
    Step(Step),
    /// The child closed its standard output.
    End,
}

/// Starts `exe oracle-run` for the configurations from `from`, and a thread
/// that sends each step of its output to `tx`.
fn spawn_child(
    exe: &Path,
    base: &Path,
    entry: &Entry,
    from: usize,
    settings: &Settings,
    tx: mpsc::Sender<ChildMsg>,
) -> std::io::Result<(Child, std::thread::JoinHandle<String>)> {
    let base = std::path::absolute(base).unwrap_or_else(|_| base.to_path_buf());
    let mut cmd = Command::new(exe);
    cmd.current_dir(&base)
        .arg("oracle-run")
        .arg("--base")
        .arg(&base)
        .arg("--path")
        .arg(&entry.path)
        .arg("--from")
        .arg(from.to_string())
        .arg("--limit-ms")
        .arg(settings.limit.as_millis().to_string())
        .arg("--max-memory")
        .arg(settings.max_memory_mb.to_string())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(n) = settings.max_steps {
        cmd.arg("--max-steps").arg(n.to_string());
    }
    let mut child = cmd.spawn()?;
    if let Some(out) = child.stdout.take() {
        std::thread::spawn(move || {
            for line in BufReader::new(out).lines() {
                let Ok(line) = line else { break };
                if let Some(step) = Step::parse_line(&line) {
                    if tx.send(ChildMsg::Step(step)).is_err() {
                        return;
                    }
                }
            }
            let _ = tx.send(ChildMsg::End);
        });
    } else {
        let _ = tx.send(ChildMsg::End);
    }
    let err = child.stderr.take();
    let errors = std::thread::spawn(move || {
        let Some(mut err) = err else {
            return String::new();
        };
        let mut buf = Vec::new();
        let _ = err.read_to_end(&mut buf);
        let tail = buf.len().saturating_sub(2000);
        String::from_utf8_lossy(buf.get(tail..).unwrap_or_default()).into_owned()
    });
    Ok((child, errors))
}

/// Stops a child process and waits for it.
fn stop_child(child: &mut Child) {
    let _ = child.kill();
    let _ = child.wait();
}

/// Runs the program `entry` below `base` in the six configurations, each in a
/// child process `exe oracle-run`, and gives its verdict.
///
/// The working directory of the child is `base`, so a relative path that the
/// program reads does not depend on the working directory of the gate.
///
/// The parent stops the child after `settings.limit` for one run: the run
/// gives [`Verdict::Timeout`], and a new child runs the next configurations.
/// The child stops itself when it uses more than `settings.max_memory_mb`
/// (the run gives [`Verdict::Timeout`]). A child that stops with no verdict
/// for its run (for example, a stack overflow of the interpreter) gives
/// [`Verdict::Fault`].
pub fn run_isolated(exe: &Path, base: &Path, entry: &Entry, settings: &Settings) -> Outcome {
    let mut c = Combine::default();
    let mut next = 0;
    while next < CONFIGS.len() && !c.is_final() {
        let (tx, rx) = mpsc::channel();
        let (mut child, errors) = match spawn_child(exe, base, entry, next, settings, tx) {
            Ok(x) => x,
            Err(e) => {
                return Outcome::new(
                    Verdict::NotRunnable,
                    format!("cannot start {}: {e}", exe.display()),
                );
            }
        };
        let mut at = Instant::now();
        loop {
            let wait = settings.limit.saturating_sub(at.elapsed());
            match rx.recv_timeout(wait) {
                Ok(ChildMsg::Step(step)) => {
                    if let Step::Run { config, .. } = step {
                        next = config + 1;
                    }
                    c.add(step);
                    at = Instant::now();
                    if c.is_final() {
                        stop_child(&mut child);
                        break;
                    }
                }
                Ok(ChildMsg::End) | Err(RecvTimeoutError::Disconnected) => {
                    let status = child.wait();
                    let memory = status.as_ref().is_ok_and(|s| s.code() == Some(MEMORY_EXIT));
                    if next < CONFIGS.len() && !memory && !c.is_final() {
                        let how = status.map_or_else(|e| e.to_string(), |s| s.to_string());
                        let text = errors.join().unwrap_or_default();
                        c.add(Step::Run {
                            config: next,
                            verdict: Verdict::Fault,
                            detail: format!(
                                "{}: the interpreter stopped ({how}): {}",
                                config_text(next),
                                text.trim()
                            ),
                        });
                    }
                    break;
                }
                Err(RecvTimeoutError::Timeout) => {
                    stop_child(&mut child);
                    c.add(Step::Run {
                        config: next,
                        verdict: Verdict::Timeout,
                        detail: format!(
                            "{}: the run takes more than {} ms",
                            config_text(next),
                            settings.limit.as_millis()
                        ),
                    });
                    next += 1;
                    break;
                }
            }
        }
    }
    c.outcome()
}

/// The exit code of `weft-gate oracle-run` when it stops itself at the memory
/// limit. It writes the step of the run first.
pub const MEMORY_EXIT: i32 = 3;

/// The resident memory of this process in bytes, from `/proc/self/statm`
/// (pages of 4096 bytes). `None` if the file cannot be read (a system that is
/// not Linux).
pub fn resident_bytes() -> Option<u64> {
    let text = std::fs::read_to_string("/proc/self/statm").ok()?;
    let pages: u64 = text.split_whitespace().nth(1)?.parse().ok()?;
    Some(pages.saturating_mul(4096))
}

/// The time limit of the pool for the runs of one program: the parent of a
/// child stops it after `settings.limit` for one run, so this limit is only a
/// guard.
fn program_limit(settings: &Settings) -> Duration {
    let runs = u32::try_from(CONFIGS.len() + 1).unwrap_or(u32::MAX);
    settings
        .limit
        .saturating_mul(runs)
        .saturating_add(Duration::from_secs(60))
}

/// Gives the verdict of each entry below `base` on a pool ([`pool::run`]).
///
/// Calls `emit` once for each entry with its index and its outcome, in the
/// order in which the entries end. With `settings.exe`, each program runs in
/// child processes ([`run_isolated`]); else on the worker thread
/// ([`run_entry`]).
///
/// A panic of the interpreter gives [`Verdict::Fault`]. The command must call
/// [`pool::install_panic_hook`] first.
///
/// # Errors
///
/// Returns [`Error::Thread`] if the system cannot start a worker thread.
pub fn run_all(
    base: &Path,
    entries: Vec<Entry>,
    settings: &Settings,
    mut emit: impl FnMut(usize, Outcome),
) -> Result<(), Error> {
    let dir: PathBuf = base.to_path_buf();
    let s = settings.clone();
    let limit = match settings.exe {
        Some(_) => program_limit(settings),
        None => settings
            .limit
            .saturating_mul(u32::try_from(CONFIGS.len()).unwrap_or(u32::MAX)),
    };
    let work: pool::Work<Outcome> = Arc::new(move |e: &Entry| match &s.exe {
        Some(exe) => run_isolated(exe, &dir, e, &s),
        None => run_entry(&dir, e, &s),
    });
    pool::run(entries, settings.workers, limit, work, |i, _, ended| {
        let outcome = match ended {
            Ended::Done(o) => o,
            Ended::Panic { text, .. } => {
                Outcome::new(Verdict::Fault, format!("the interpreter panicked: {text}"))
            }
            Ended::Timeout => Outcome::new(
                Verdict::Timeout,
                format!("the runs take more than {} ms", limit.as_millis()),
            ),
        };
        emit(i, outcome);
    })
}

/// One line of the cache: the key, the verdict and the path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    /// The hash of the program text (the hash of the manifest entry).
    pub hash: String,
    /// The engine.
    pub engine: Engine,
    /// The hash of the interpreter sources ([`interp_hash`]).
    pub interp: String,
    /// The verdict.
    pub verdict: Verdict,
    /// The detail of the verdict ([`Outcome::detail`]).
    pub detail: String,
    /// The path of the manifest entry, for the reader. It is not part of the key.
    pub path: String,
}

impl Row {
    /// The row as one line of the cache, with no line feed. A tab or a line
    /// feed in the detail or the path becomes a space.
    pub fn to_line(&self) -> String {
        format!(
            "{}\t{}\t{}\t{}\t{}\t{}",
            self.hash,
            self.engine.name(),
            self.interp,
            self.verdict.name(),
            one_line(&self.detail),
            self.path.replace(['\t', '\n', '\r'], " ")
        )
    }
}

/// The key of a row.
type Key = (String, Engine, String);

/// The oracle cache: one row for each key.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Cache {
    rows: BTreeMap<Key, Row>,
}

impl Cache {
    /// Reads a cache file. Empty lines and the header are skipped. Of two rows
    /// with the same key, the later row wins.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Cache`] for a line that does not have six columns, or
    /// whose engine or verdict is not known.
    pub fn from_tsv(text: &str) -> Result<Self, Error> {
        let mut cache = Self::default();
        for (i, line) in text.lines().enumerate() {
            if line.is_empty() || line == HEADER {
                continue;
            }
            let bad = |message: String| Error::Cache {
                line: i + 1,
                message,
            };
            let cols: Vec<&str> = line.split('\t').collect();
            let [hash, engine, interp, verdict, detail, path] = cols.as_slice() else {
                return Err(bad(format!("{} columns, not 6", cols.len())));
            };
            let engine = Engine::parse(engine).ok_or_else(|| bad(format!("engine `{engine}`")))?;
            let verdict =
                Verdict::parse(verdict).ok_or_else(|| bad(format!("verdict `{verdict}`")))?;
            cache.insert(Row {
                hash: (*hash).to_string(),
                engine,
                interp: (*interp).to_string(),
                verdict,
                detail: (*detail).to_string(),
                path: (*path).to_string(),
            });
        }
        Ok(cache)
    }

    /// The cache as a file: the header, then one line for each row, in the
    /// order of the paths.
    pub fn to_tsv(&self) -> String {
        let mut rows: Vec<&Row> = self.rows.values().collect();
        rows.sort_by(|a, b| {
            (&a.path, &a.hash, a.engine, &a.interp).cmp(&(&b.path, &b.hash, b.engine, &b.interp))
        });
        let mut text = String::from(HEADER);
        text.push('\n');
        for r in rows {
            text.push_str(&r.to_line());
            text.push('\n');
        }
        text
    }

    /// Adds a row, or replaces the row with the same key. The detail and the
    /// path are put on one line.
    pub fn insert(&mut self, mut row: Row) {
        row.detail = one_line(&row.detail);
        row.path = row.path.replace(['\t', '\n', '\r'], " ");
        let key = (row.hash.clone(), row.engine, row.interp.clone());
        self.rows.insert(key, row);
    }

    /// The row with this key, if any.
    pub fn get(&self, hash: &str, engine: Engine, interp: &str) -> Option<&Row> {
        self.rows
            .get(&(hash.to_string(), engine, interp.to_string()))
    }

    /// Adds the rows of `other`. A row of `other` replaces a row with the same
    /// key.
    pub fn extend(&mut self, other: Self) {
        self.rows.extend(other.rows);
    }

    /// Keeps only the rows for which `keep` is true.
    pub fn retain(&mut self, mut keep: impl FnMut(&Row) -> bool) {
        self.rows.retain(|_, r| keep(r));
    }

    /// The number of rows.
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    /// True if the cache has no row.
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }
}

/// The counts of an oracle command.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// The programs whose verdict came from the cache.
    pub hits: usize,
    /// The programs that ran.
    pub runs: usize,
    /// The number of programs with each verdict.
    pub counts: BTreeMap<Verdict, usize>,
}

/// Gives the verdict of each entry below `base` with `engine`.
///
/// The verdict comes from `cache` if it has the key, else from a run
/// ([`run_all`]). Calls `emit` once for each entry with its row and true for a
/// cache hit. The rows of the hits come first.
///
/// # Errors
///
/// Returns [`Error::Thread`] if the system cannot start a worker thread.
pub fn oracle(
    base: &Path,
    entries: Vec<Entry>,
    cache: &Cache,
    engine: Engine,
    interp: &str,
    settings: &Settings,
    mut emit: impl FnMut(Row, bool),
) -> Result<Summary, Error> {
    let mut summary = Summary::default();
    let mut todo = Vec::new();
    for e in entries {
        if let Some(row) = cache.get(&e.hash, engine, interp) {
            let mut row = row.clone();
            row.path.clone_from(&e.path);
            summary.hits += 1;
            *summary.counts.entry(row.verdict).or_default() += 1;
            emit(row, true);
        } else {
            todo.push(e);
        }
    }
    let keys: Vec<(String, String)> = todo
        .iter()
        .map(|e| (e.hash.clone(), e.path.clone()))
        .collect();
    run_all(base, todo, settings, |i, o| {
        let Some((hash, path)) = keys.get(i) else {
            return;
        };
        summary.runs += 1;
        *summary.counts.entry(o.verdict).or_default() += 1;
        emit(
            Row {
                hash: hash.clone(),
                engine,
                interp: interp.to_string(),
                verdict: o.verdict,
                detail: o.detail,
                path: path.clone(),
            },
            false,
        );
    })?;
    Ok(summary)
}

/// Adds each file below `dir` to `files`, with its path relative to `root`
/// (with `/` between the components).
fn source_files(root: &Path, dir: &Path, files: &mut Vec<(String, PathBuf)>) -> Result<(), Error> {
    let read = std::fs::read_dir(dir).map_err(|e| Error::io(dir, e))?;
    for item in read {
        let item = item.map_err(|e| Error::io(dir, e))?;
        let path = item.path();
        let kind = item.file_type().map_err(|e| Error::io(&path, e))?;
        if kind.is_dir() {
            source_files(root, &path, files)?;
        } else if kind.is_file() {
            let rel = path.strip_prefix(root).unwrap_or(&path);
            let name: Vec<String> = rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect();
            files.push((name.join("/"), path));
        }
    }
    Ok(())
}

/// The SHA-256 of the interpreter sources ([`INTERP_SRC`] below `repo`): of
/// each file in the order of its relative path, the path, the length and the
/// bytes.
///
/// # Errors
///
/// Returns [`Error::Io`] if a directory or a file cannot be read.
pub fn interp_hash(repo: &Path) -> Result<String, Error> {
    let root = repo.join(INTERP_SRC);
    let mut files = Vec::new();
    source_files(&root, &root, &mut files)?;
    files.sort();
    let mut h = Sha256::new();
    for (name, path) in &files {
        let bytes = std::fs::read(path).map_err(|e| Error::io(path, e))?;
        h.update(name.as_bytes());
        h.update([0]);
        h.update(u64::try_from(bytes.len()).unwrap_or(u64::MAX).to_le_bytes());
        h.update(&bytes);
    }
    Ok(hex(&h.finalize()))
}
