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
//! sources ([`interp_hash`]). The cache is a TSV file ([`Cache`]) for each
//! engine: for tier 1 `tests/gate/oracle-ast.tsv` and `tests/gate/oracle-ir.tsv`
//! (committed), for tier 2 the same names in `$WEFT_GATE_CACHE` (default
//! `target/gate/`). From stage I5 the gate classifies the programs with the
//! verdicts of the IR engine.
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
use std::fmt::Write as _;
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
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Engine {
    /// The interpreter that compiles the AST (`--engine=ast`).
    #[default]
    Ast,
    /// The interpreter that compiles the core IR (`--engine=ir`). A program
    /// with a body that has no IR runs on the AST compiler
    /// ([`Observation::fallback`]).
    Ir,
}

impl Engine {
    /// The engines, in the order of the engine differential.
    pub const ALL: [Self; 2] = [Self::Ast, Self::Ir];

    /// Returns the engine with the name `name`, or `None`.
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|e| e.name() == name)
    }

    /// The name, as `--engine` takes it.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Ast => "ast",
            Self::Ir => "ir",
        }
    }

    /// The engine of the interpreter.
    pub const fn interp(self) -> weft_interp::Engine {
        match self {
            Self::Ast => weft_interp::Engine::Ast,
            Self::Ir => weft_interp::Engine::Ir,
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
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "kebab-case")]
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
    /// The engine that runs the programs.
    pub engine: Engine,
    /// Runs the fact oracle and trace conformance (`docs/ir.md` 8.5) on each
    /// program in scope that the `ir` pipeline accepts ([`run_fact_configs`]),
    /// in place of the oracle verdict.
    pub fact_oracle: bool,
    /// The construct groups of the `ir` pipeline for the fact oracle, or
    /// `None` for the default groups (`--groups`, a preview of a stage).
    pub groups: Option<weft_sema::Groups>,
}

impl Default for Settings {
    fn default() -> Self {
        Self {
            workers: 1,
            limit: LIMIT,
            max_steps: Some(MAX_STEPS),
            max_memory_mb: MAX_MEMORY_MB,
            exe: None,
            engine: Engine::Ast,
            fact_oracle: false,
            groups: None,
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

/// The line of a run-time error, for a program of one file.
fn error_line(pkg: &Package, e: &RuntimeError) -> Option<usize> {
    match (e.span, pkg.files.as_slice()) {
        (Some(span), [_, file]) => Some(file.line_col(span.lo).0),
        _ => None,
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

/// The most bytes of the output that an [`Observation`] keeps. The hash of
/// the output covers all of it.
pub const MAX_OUTPUT: usize = 4000;

/// Each line of an observation in the output of `weft-gate oracle-run
/// --observe` starts with this text.
pub const OBSERVE_PREFIX: &str = "@observe";

/// What one run of a program shows: the engine differential
/// (`crate::engines`) compares the observations of the two engines.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Observation {
    /// The index of the configuration ([`CONFIGS`]).
    pub config: usize,
    /// The verdict of the run.
    pub verdict: Verdict,
    /// How the run ends: `ok`, the kind of the run-time error (`fault`,
    /// `failed`, `assertion`, `step-limit`, `deadlock`, `no-main`), or, from
    /// the parent process, `timeout` (the time or the memory limit) and
    /// `stopped` (the interpreter stops with no result). A program that does
    /// not load, or that has no `main` and no test block, is `not-runnable`.
    /// For test blocks: the kind of the first test that fails, else `ok`.
    pub status: String,
    /// The message of the run-time error. For test blocks: the result of each
    /// test, one per line.
    pub message: String,
    /// The line of the run-time error (a program of one file).
    pub line: Option<usize>,
    /// The start of the output: the standard output, then the `Log` output
    /// after a line `[stderr]`. For test blocks: the output of each test after
    /// a line with its name. At most [`MAX_OUTPUT`] bytes.
    pub output: String,
    /// The SHA-256 of all the output.
    pub output_hash: String,
    /// Why the AST compiler ran the program when the IR engine was asked
    /// (`RunOutcome::fallback`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fallback: Option<String>,
}

impl Observation {
    /// An observation with no output.
    pub fn bare(config: usize, verdict: Verdict, status: &str, message: impl Into<String>) -> Self {
        Self::with_output(config, verdict, status, message, String::new())
    }

    /// An observation with the output `output` (all of it).
    fn with_output(
        config: usize,
        verdict: Verdict,
        status: &str,
        message: impl Into<String>,
        output: String,
    ) -> Self {
        let output_hash = hex(&Sha256::digest(output.as_bytes()));
        let mut keep = output;
        if keep.len() > MAX_OUTPUT {
            let mut end = MAX_OUTPUT;
            while !keep.is_char_boundary(end) {
                end -= 1;
            }
            keep.truncate(end);
        }
        Self {
            config,
            verdict,
            status: status.to_string(),
            message: message.into(),
            line: None,
            output: keep,
            output_hash,
            fallback: None,
        }
    }

    /// The observation as one line of the output of `oracle-run --observe`.
    ///
    /// # Errors
    ///
    /// Returns the error of `serde_json`.
    pub fn to_line(&self) -> Result<String, serde_json::Error> {
        Ok(format!(
            "{OBSERVE_PREFIX}\t{}",
            serde_json::to_string(self)?
        ))
    }

    /// Reads a line of [`Observation::to_line`]. Another line gives `None`.
    pub fn parse_line(line: &str) -> Option<Self> {
        let json = line.strip_prefix(OBSERVE_PREFIX)?.strip_prefix('\t')?;
        serde_json::from_str(json).ok()
    }

    /// True if the run does not end: the time, the memory or the step limit.
    /// The output of such a run depends on the limit, not on the program.
    pub fn is_timeout(&self) -> bool {
        matches!(self.status.as_str(), "timeout" | "step-limit")
    }
}

/// The name of an error kind in [`Observation::status`].
const fn status_name(kind: ErrorKind) -> &'static str {
    match kind {
        ErrorKind::Failed => "failed",
        ErrorKind::Assertion => "assertion",
        ErrorKind::Fault => "fault",
        ErrorKind::StepLimit => "step-limit",
        ErrorKind::Deadlock => "deadlock",
        ErrorKind::NoMain => "no-main",
    }
}

/// The output of a run: the standard output, then the `Log` output.
fn output_text(out: &RunOutcome) -> String {
    if out.stderr.is_empty() {
        out.stdout.clone()
    } else {
        format!("{}\n[stderr]\n{}", out.stdout, out.stderr)
    }
}

/// The observation of one run of `main`.
fn main_observation(
    pkg: &Package,
    config: usize,
    verdict: Verdict,
    run: &Result<RunOutcome, RuntimeError>,
) -> Observation {
    match run {
        Ok(out) => {
            let mut o = Observation::with_output(config, verdict, "ok", "", output_text(out));
            o.fallback.clone_from(&out.fallback);
            o
        }
        Err(e) => {
            let mut o = Observation::with_output(
                config,
                verdict,
                status_name(e.kind),
                e.message.clone(),
                output_text(&e.outcome),
            );
            o.line = error_line(pkg, e);
            o.fallback.clone_from(&e.outcome.fallback);
            o
        }
    }
}

/// The observation of one run of the test blocks.
fn tests_observation(config: usize, verdict: Verdict, tests: &[TestOutcome]) -> Observation {
    let mut status = "ok";
    let mut message = String::new();
    let mut output = String::new();
    for t in tests {
        let result = t.message.as_deref().unwrap_or("ok");
        if status == "ok" {
            if let Some(m) = &t.message {
                status = test_error_kind(m).map_or("fault", |(k, _)| status_name(k));
            }
        }
        let _ = writeln!(message, "test `{}`: {result}", t.name);
        let _ = writeln!(output, "[test `{}`]\n{}", t.name, output_text(&t.outcome));
    }
    let mut o = Observation::with_output(config, verdict, status, message, output);
    o.fallback = tests.iter().find_map(|t| t.outcome.fallback.clone());
    o
}

/// The text of configuration `config` for a detail.
pub fn config_text(config: usize) -> String {
    CONFIGS.get(config).map_or_else(
        || format!("configuration {config}"),
        |(seed, workers)| format!("seed {seed}, workers {workers}"),
    )
}

/// Runs the program at `path` below `base` with `engine` in the
/// configurations of [`CONFIGS`] from index `from`, on this thread.
///
/// Calls `start` with the index of each configuration before its run, and
/// `emit` with each step and the observation of its run (`None` for a
/// program that does not load). The runs stop after a run that faults,
/// because no other verdict comes before `fault`.
///
/// A panic of the interpreter continues in the caller.
pub fn run_configs(
    base: &Path,
    path: &str,
    from: usize,
    max_steps: Option<u64>,
    engine: Engine,
    mut start: impl FnMut(usize),
    mut emit: impl FnMut(Step, Option<Observation>),
) {
    let pkg = match package::load(&base.join(path)) {
        Ok(pkg) => pkg,
        Err(e) => {
            let dir = format!("{}/", base.display());
            let text = format!("the program does not load: {e:#}").replace(&dir, "");
            emit(Step::NotRunnable(text), None);
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
            engine: engine.interp(),
            ..RunOptions::default()
        };
        let mut best: Option<(Verdict, String)> = None;
        let run = weft_interp::run_analysis_main(&analysis, &run_opts);
        let observed = if matches!(&run, Err(e) if e.kind == ErrorKind::NoMain) {
            let tests = weft_interp::run_analysis_tests(&analysis, &run_opts);
            if tests.is_empty() {
                let text = "no `main` and no test block";
                let o = Observation::bare(config, Verdict::NotRunnable, "not-runnable", text);
                emit(Step::NotRunnable(text.to_string()), Some(o));
                return;
            }
            for t in &tests {
                keep_first(&mut best, test_verdict(t));
            }
            Err(tests)
        } else {
            keep_first(&mut best, main_verdict(&pkg, base, &run));
            Ok(run)
        };
        let (verdict, text) = best.unwrap_or((Verdict::Clean, String::new()));
        let detail = if verdict == Verdict::Clean {
            String::new()
        } else {
            format!("{}: {text}", config_text(config))
        };
        let o = match &observed {
            Ok(run) => main_observation(&pkg, config, verdict, run),
            Err(tests) => tests_observation(config, verdict, tests),
        };
        emit(
            Step::Run {
                config,
                verdict,
                detail,
            },
            Some(o),
        );
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
    run_entry_observed(base, entry, settings).0
}

/// Runs the program `entry` below `base` as [`run_entry`] does, and also gives
/// the observation of each run, in the order of the configurations.
///
/// A panic of the interpreter continues in the caller.
pub fn run_entry_observed(
    base: &Path,
    entry: &Entry,
    settings: &Settings,
) -> (Outcome, Vec<Observation>) {
    let mut c = Combine::default();
    let mut seen = Vec::new();
    if settings.fact_oracle {
        run_fact_configs(
            base,
            &entry.path,
            0,
            settings.max_steps,
            settings.groups,
            |_| {},
            |s| c.add(s),
        );
        return (c.outcome(), seen);
    }
    run_configs(
        base,
        &entry.path,
        0,
        settings.max_steps,
        settings.engine,
        |_| {},
        |s, o| {
            c.add(s);
            seen.extend(o);
        },
    );
    (c.outcome(), seen)
}

/// The class of the outcome of the fact oracle on one program
/// ([`run_fact_configs`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FactClass {
    /// A failure of trace conformance.
    Trace,
    /// A failure of the fact oracle (C1, C4, C5, D1, D4).
    Fact,
    /// Another fault: the memory oracle, a panic, a fault marker.
    Fault,
    /// The run does not end in the limits.
    Timeout,
    /// The runs end with no failure of the fact oracle (also a `fail`, an
    /// `assert` or a benign error).
    Pass,
    /// The program is not in scope of the `ir` pipeline.
    OutOfScope,
    /// The `ir` pipeline rejects the program.
    Rejected,
    /// The program does not load, or has no `main` and no test block.
    NotRunnable,
}

impl FactClass {
    /// The classes, in the order of the report.
    pub const ALL: [Self; 8] = [
        Self::Trace,
        Self::Fact,
        Self::Fault,
        Self::Timeout,
        Self::Pass,
        Self::OutOfScope,
        Self::Rejected,
        Self::NotRunnable,
    ];

    /// The name in the report.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Trace => "trace",
            Self::Fact => "fact-oracle",
            Self::Fault => "fault",
            Self::Timeout => "timeout",
            Self::Pass => "pass",
            Self::OutOfScope => "out-of-scope",
            Self::Rejected => "rejected",
            Self::NotRunnable => "not-runnable",
        }
    }

    /// True for a failure of the fact oracle or of trace conformance.
    pub const fn is_failure(self) -> bool {
        matches!(self, Self::Trace | Self::Fact)
    }
}

/// The class of outcome `o` of [`run_fact_configs`].
pub fn fact_class(o: &Outcome) -> FactClass {
    let d = &o.detail;
    match o.verdict {
        Verdict::Fault if d.contains("trace conformance:") => FactClass::Trace,
        Verdict::Fault if d.contains("fact oracle (") => FactClass::Fact,
        Verdict::Fault => FactClass::Fault,
        Verdict::Timeout => FactClass::Timeout,
        Verdict::NotRunnable if d.contains(&format!("{FACT_SKIP}out of scope")) => {
            FactClass::OutOfScope
        }
        Verdict::NotRunnable if d.contains(FACT_SKIP) => FactClass::Rejected,
        Verdict::NotRunnable => FactClass::NotRunnable,
        Verdict::Fail | Verdict::Benign | Verdict::Clean => FactClass::Pass,
    }
}

/// The report of `weft-gate fact-oracle`: the count of each class, and the
/// path and the detail of each program of the classes before `pass`.
pub fn fact_report(tier: u8, rows: &[(String, FactClass, String)], took: Duration) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "# Fact oracle and trace conformance, tier {tier}\n");
    let _ = writeln!(
        s,
        "The runs of `weft-gate fact-oracle` (`docs/ir.md` 8.5): each program with `main` or test blocks that the `ir` pipeline checks and accepts runs on the IR engine with the fact oracle and the memory oracle, in the six configurations. {} programs, {:.1} s.\n",
        rows.len(),
        took.as_secs_f64()
    );
    let _ = writeln!(s, "| Class | Programs |\n| --- | --- |");
    for c in FactClass::ALL {
        let n = rows.iter().filter(|r| r.1 == c).count();
        let _ = writeln!(s, "| {} | {n} |", c.name());
    }
    for c in [
        FactClass::Trace,
        FactClass::Fact,
        FactClass::Fault,
        FactClass::Timeout,
    ] {
        let list: Vec<&(String, FactClass, String)> = rows.iter().filter(|r| r.1 == c).collect();
        if list.is_empty() {
            continue;
        }
        let _ = writeln!(s, "\n## {}\n", c.name());
        for (p, _, d) in list {
            let _ = writeln!(s, "- `{p}`: {d}");
        }
    }
    s
}

/// The start of the detail of a program that the fact oracle does not run:
/// a program that is not in scope of the `ir` pipeline, or that it rejects.
pub const FACT_SKIP: &str = "fact oracle: no run: ";

/// Runs the program at `path` below `base` with the fact oracle (`docs/ir.md`
/// 8.5).
///
/// The runs use the memory oracle and the IR engine, in the configurations
/// of [`CONFIGS`] from index `from`, on this thread. A program that is not
/// in scope of the `ir` pipeline (the default groups), or that the `ir`
/// pipeline rejects, gives [`Step::NotRunnable`] with a detail that starts
/// with [`FACT_SKIP`]. A failure of the fact oracle or of trace conformance
/// is a [`Verdict::Fault`] whose detail holds `fact oracle (` or `trace
/// conformance:`.
///
/// A panic of the interpreter continues in the caller.
pub fn run_fact_configs(
    base: &Path,
    path: &str,
    from: usize,
    max_steps: Option<u64>,
    groups: Option<weft_sema::Groups>,
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
    let mut opts = weft_sema::Options {
        facts: weft_sema::FactGen::Both,
        ..pkg.options(Profile::default())
    };
    if let Some(g) = groups {
        opts.ir_groups = g;
    }
    let analysis = weft_sema::analyze(&pkg.units, opts);
    let fallback = analysis.ir_scope.as_ref().and_then(|s| s.fallback.clone());
    let checked = weft_check::check_analysis(analysis, &pkg.files);
    let Some(ir) = &checked.ir else {
        let why = fallback.unwrap_or_else(|| "no scope".to_string());
        emit(Step::NotRunnable(format!("{FACT_SKIP}out of scope: {why}")));
        return;
    };
    if !ir.ok() {
        emit(Step::NotRunnable(format!(
            "{FACT_SKIP}the ir pipeline rejects it"
        )));
        return;
    }
    for (config, &(seed, workers)) in CONFIGS.iter().enumerate().skip(from) {
        start(config);
        let run_opts = RunOptions {
            seed,
            workers,
            max_steps,
            capture_output: true,
            no_runtime: opts.no_runtime,
            oracle: true,
            engine: weft_interp::Engine::Ir,
            fact_oracle: true,
            ..RunOptions::default()
        };
        let mut best: Option<(Verdict, String)> = None;
        let run = weft_interp::run_main(&checked, &run_opts);
        if matches!(&run, Err(e) if e.kind == ErrorKind::NoMain) {
            let tests = weft_interp::run_tests(&checked, &run_opts);
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

/// What a reader thread of a child process sends.
enum ChildMsg {
    /// A step.
    Step(Step),
    /// An observation of a run.
    Observe(Box<Observation>),
    /// The child closed its standard output.
    End,
}

/// The coverage profile file of a child, when the parent writes a profile.
///
/// The pool kills a child at its time limit. A killed child can leave a part
/// of a profile, and a coverage run then cannot merge its profiles. So each
/// child writes its own profile in the temporary directory, away from the
/// profiles of the coverage run.
fn child_profile_file(parent_has_profile: bool) -> Option<PathBuf> {
    parent_has_profile.then(|| std::env::temp_dir().join("weft-gate-child-%p.profraw"))
}

/// Starts `exe oracle-run` for the configurations from `from`, and a thread
/// that sends each step of its output to `tx`.
fn spawn_child(
    exe: &Path,
    base: &Path,
    entry: &Entry,
    from: usize,
    settings: &Settings,
    observe: bool,
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
        .arg("--engine")
        .arg(settings.engine.name())
        .args(settings.fact_oracle.then_some("--fact-oracle"))
        .args(
            settings
                .groups
                .iter()
                .flat_map(|g| ["--groups".to_string(), g.to_string()]),
        )
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(n) = settings.max_steps {
        cmd.arg("--max-steps").arg(n.to_string());
    }
    if observe {
        cmd.arg("--observe");
    }
    if let Some(file) = child_profile_file(std::env::var_os("LLVM_PROFILE_FILE").is_some()) {
        cmd.env("LLVM_PROFILE_FILE", file);
    }
    let mut child = cmd.spawn()?;
    if let Some(out) = child.stdout.take() {
        std::thread::spawn(move || {
            for line in BufReader::new(out).lines() {
                let Ok(line) = line else { break };
                let msg = Step::parse_line(&line).map(ChildMsg::Step).or_else(|| {
                    Observation::parse_line(&line).map(|o| ChildMsg::Observe(Box::new(o)))
                });
                if let Some(msg) = msg {
                    if tx.send(msg).is_err() {
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
    isolated(exe, base, entry, settings, false).0
}

/// Runs the program `entry` below `base` as [`run_isolated`] does, and also
/// gives the observation of each run.
///
/// The observations are in the order of the configurations. A run that the
/// parent stops at the time limit has the status `timeout`; a child that stops
/// with no result gives the status `stopped`.
pub fn run_isolated_observed(
    exe: &Path,
    base: &Path,
    entry: &Entry,
    settings: &Settings,
) -> (Outcome, Vec<Observation>) {
    isolated(exe, base, entry, settings, true)
}

/// Adds the observation of a run that has no observation from the child.
fn observe_step(seen: &mut Vec<Observation>, step: &Step, status: &str) {
    match step {
        Step::Run {
            config,
            verdict,
            detail,
        } if !seen.iter().any(|o| o.config == *config) => {
            seen.push(Observation::bare(*config, *verdict, status, detail.clone()));
        }
        Step::NotRunnable(detail) if seen.is_empty() => {
            seen.push(Observation::bare(
                0,
                Verdict::NotRunnable,
                "not-runnable",
                detail.clone(),
            ));
        }
        _ => {}
    }
}

/// The runs of [`run_isolated`]; with `observe`, also the observations.
fn isolated(
    exe: &Path,
    base: &Path,
    entry: &Entry,
    settings: &Settings,
    observe: bool,
) -> (Outcome, Vec<Observation>) {
    let mut c = Combine::default();
    let mut seen: Vec<Observation> = Vec::new();
    let mut next = 0;
    while next < CONFIGS.len() && !c.is_final() {
        let (tx, rx) = mpsc::channel();
        let (mut child, errors) = match spawn_child(exe, base, entry, next, settings, observe, tx) {
            Ok(x) => x,
            Err(e) => {
                let text = format!("cannot start {}: {e}", exe.display());
                if observe {
                    seen.push(Observation::bare(
                        next,
                        Verdict::NotRunnable,
                        "not-runnable",
                        text.clone(),
                    ));
                }
                return (Outcome::new(Verdict::NotRunnable, text), seen);
            }
        };
        let mut at = Instant::now();
        loop {
            let wait = settings.limit.saturating_sub(at.elapsed());
            match rx.recv_timeout(wait) {
                Ok(ChildMsg::Observe(o)) => seen.push(*o),
                Ok(ChildMsg::Step(step)) => {
                    if let Step::Run { config, .. } = step {
                        next = config + 1;
                    }
                    if observe {
                        // A step with no observation: the memory limit.
                        observe_step(&mut seen, &step, "timeout");
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
                        let step = Step::Run {
                            config: next,
                            verdict: Verdict::Fault,
                            detail: format!(
                                "{}: the interpreter stopped ({how}): {}",
                                config_text(next),
                                text.trim()
                            ),
                        };
                        if observe {
                            observe_step(&mut seen, &step, "stopped");
                        }
                        c.add(step);
                    }
                    break;
                }
                Err(RecvTimeoutError::Timeout) => {
                    stop_child(&mut child);
                    let step = Step::Run {
                        config: next,
                        verdict: Verdict::Timeout,
                        detail: format!(
                            "{}: the run takes more than {} ms",
                            config_text(next),
                            settings.limit.as_millis()
                        ),
                    };
                    if observe {
                        observe_step(&mut seen, &step, "timeout");
                    }
                    c.add(step);
                    next += 1;
                    break;
                }
            }
        }
    }
    seen.sort_by_key(|o| o.config);
    (c.outcome(), seen)
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
    let settings = Settings {
        engine,
        ..settings.clone()
    };
    run_all(base, todo, &settings, |i, o| {
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

#[cfg(test)]
mod tests {
    use super::child_profile_file;

    #[test]
    fn a_child_profile_goes_to_the_temporary_directory_in_a_coverage_run() {
        assert_eq!(child_profile_file(false), None);
        let file = child_profile_file(true).unwrap_or_default();
        assert!(file.starts_with(std::env::temp_dir()));
        assert!(file
            .to_string_lossy()
            .ends_with("weft-gate-child-%p.profraw"));
    }
}
