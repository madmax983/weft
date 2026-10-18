//! The Weft reference interpreter.
//!
//! The interpreter gives the dynamic semantics of the design: algebraic effects
//! with lexical handlers, one-shot and multi-shot continuations, `on abort`,
//! structured tasks with cancellation, and deterministic simulation.
//!
//! The machine compiles each body to a small stack code (see [`code`]) and runs
//! it with an explicit frame stack per task. A perform captures the frames up to
//! its handler as a delimited continuation. The verified state machines in
//! `weft_verified::lifecycle` guard each continuation (`once` resumes at most
//! once) and each linear value (it finishes at most once). The state machines
//! do not make sure that each linear value finishes. The checker (W0601,
//! W0602) and the unwinder do that.
//!
//! The scheduler is deterministic: one OS thread, `N` virtual workers and a
//! seeded random choice among ready tasks. An idle worker steals only a task that
//! the checker marked `stealable`.
//!
//! Entry points: [`run_main`] and [`run_tests`].

pub mod code;
pub mod compile;
pub mod error;
pub mod heap;
mod machine;
pub mod rng;
pub mod runtime;
pub mod trace;
pub mod value;

use std::collections::BTreeSet;

use weft_check::Checked;
use weft_sema::Analysis;

pub use error::{ErrorKind, RuntimeError};
pub use trace::{SuspendReason, TaskEnd, TraceEvent};

use crate::machine::{Machine, TaskResult};
use crate::runtime::Runtime;
use crate::value::{Cap, Obj, Value};

/// Options for one run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunOptions {
    /// The seed of the scheduler and of the `Rand` root handler.
    pub seed: u64,
    /// The number of virtual workers.
    pub workers: usize,
    /// Stops the run with an error after this many steps.
    pub max_steps: Option<u64>,
    /// Keeps output only in the outcome. If false, output also goes to the
    /// process standard output and standard error.
    pub capture_output: bool,
    /// Stops `http.serve` after this many requests.
    pub max_requests: Option<usize>,
    /// The number of steps before a loop back-edge yields to the scheduler.
    pub quantum: u64,
    /// The embedded profile: no root handlers for the standard effects.
    pub no_runtime: bool,
}

impl Default for RunOptions {
    fn default() -> Self {
        Self {
            seed: 0,
            workers: 4,
            max_steps: None,
            capture_output: true,
            max_requests: None,
            quantum: 1000,
            no_runtime: false,
        }
    }
}

/// What a run produced.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RunOutcome {
    /// The standard output.
    pub stdout: String,
    /// The standard error (`Log` output).
    pub stderr: String,
    /// The scheduler trace.
    pub trace: Vec<TraceEvent>,
    /// The number of `Rc` cells that are still alive at the end (cycles leak).
    pub leaked_rc: usize,
    /// The number of calls that ran on the blocking pool.
    pub blocking_calls: usize,
}

/// The result of one test block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestOutcome {
    /// The test name.
    pub name: String,
    /// True if the test body finished normally.
    pub passed: bool,
    /// The failure message, if the test failed.
    pub message: Option<String>,
    /// The output and trace of the test.
    pub outcome: RunOutcome,
}

/// Returns the spans of the task closures that the checker marked stealable.
pub fn stealable_spans(checked: &Checked) -> BTreeSet<(u32, u32)> {
    let mut out = BTreeSet::new();
    for (b, r) in checked.analysis.bodies.iter().zip(&checked.reports) {
        if b.unit != weft_sema::ROOT_UNIT {
            continue;
        }
        for t in &r.violations.stealable {
            if let Some(info) = b.facts.tasks.get(t.index()) {
                out.insert((info.span.lo, info.span.hi));
            }
        }
    }
    out
}

/// Runs `fn main` of a checked program.
///
/// The interpreter does not refuse a program with diagnostics. Run-time guards
/// catch some errors that the checker rejects, for example a second resume of a
/// `once` continuation.
pub fn run_main(checked: &Checked, opts: &RunOptions) -> Result<RunOutcome, RuntimeError> {
    let rt = Runtime::new(
        &checked.analysis.program,
        &checked.analysis.sigs,
        stealable_spans(checked),
    );
    run_main_with(&rt, opts)
}

/// Runs `fn main` of an analysis that the checker did not see. No task is
/// stealable.
pub fn run_analysis_main(
    analysis: &Analysis,
    opts: &RunOptions,
) -> Result<RunOutcome, RuntimeError> {
    let rt = Runtime::new(&analysis.program, &analysis.sigs, BTreeSet::new());
    run_main_with(&rt, opts)
}

/// Runs every test block of a checked program, in source order.
pub fn run_tests(checked: &Checked, opts: &RunOptions) -> Vec<TestOutcome> {
    let rt = Runtime::new(
        &checked.analysis.program,
        &checked.analysis.sigs,
        stealable_spans(checked),
    );
    run_tests_with(&rt, opts)
}

/// Runs every test block of an analysis that the checker did not see.
pub fn run_analysis_tests(analysis: &Analysis, opts: &RunOptions) -> Vec<TestOutcome> {
    let rt = Runtime::new(&analysis.program, &analysis.sigs, BTreeSet::new());
    run_tests_with(&rt, opts)
}

fn env_value(rt: &Runtime<'_>) -> Value {
    let Some(adt) = rt.b.env else {
        return Value::Unit;
    };
    let fields = rt.adts[adt]
        .fields
        .iter()
        .map(|f| match &**f {
            "fs" => Value::Cap(Cap::Fs),
            "net" => Value::Cap(Cap::Net),
            "stdout" => Value::Cap(Cap::Stdout),
            _ => Value::Unit,
        })
        .collect();
    Value::Struct(Box::new(Obj {
        adt,
        fields,
        lin: None,
    }))
}

fn with_outcome(mut e: RuntimeError, m: &Machine<'_, '_>) -> RuntimeError {
    e.outcome = Box::new(m.outcome());
    e
}

fn finish_run(m: &mut Machine<'_, '_>, root: usize) -> Result<RunOutcome, RuntimeError> {
    if let Err(e) = m.run_until_done(root) {
        return Err(with_outcome(e, m));
    }
    match m.result(root).cloned() {
        Some(TaskResult::Ok(v)) => {
            m.drop_value(v);
            Ok(m.outcome())
        }
        Some(TaskResult::Failed { msg, kind, span }) => {
            Err(with_outcome(RuntimeError::new(kind, msg, span), m))
        }
        Some(TaskResult::Cancelled) => Err(with_outcome(
            RuntimeError::new(ErrorKind::Fault, "the root task was cancelled", None),
            m,
        )),
        None => Err(with_outcome(
            RuntimeError::new(ErrorKind::Fault, "the root task has no result", None),
            m,
        )),
    }
}

fn run_main_with(rt: &Runtime<'_>, opts: &RunOptions) -> Result<RunOutcome, RuntimeError> {
    let Some(f) = rt.main_fn() else {
        return Err(RuntimeError::new(
            ErrorKind::NoMain,
            "the program has no `fn main`",
            None,
        ));
    };
    let Some(code) = rt.compiled.fn_code.get(f).copied().flatten() else {
        return Err(RuntimeError::new(
            ErrorKind::NoMain,
            "`main` has no body",
            None,
        ));
    };
    let mut m = Machine::new(rt, opts);
    let n = rt.prog.fns[f].decl.params.len();
    let args = if n == 0 {
        Vec::new()
    } else {
        vec![env_value(rt)]
    };
    let root = match m.start(code, args) {
        Ok(r) => r,
        Err(e) => return Err(with_outcome(e, &m)),
    };
    finish_run(&mut m, root)
}

fn run_tests_with(rt: &Runtime<'_>, opts: &RunOptions) -> Vec<TestOutcome> {
    let mut out = Vec::new();
    for (name, code) in &rt.compiled.tests {
        let mut m = Machine::new(rt, opts);
        let r = m
            .start(*code, Vec::new())
            .and_then(|root| finish_run(&mut m, root));
        out.push(match r {
            Ok(outcome) => TestOutcome {
                name: name.clone(),
                passed: true,
                message: None,
                outcome,
            },
            Err(e) => TestOutcome {
                name: name.clone(),
                passed: false,
                message: Some(e.to_string()),
                outcome: *e.outcome,
            },
        });
    }
    out
}
