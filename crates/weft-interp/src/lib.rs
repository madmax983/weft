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
//! W0602) and the unwinder do that. On an abort path the unwinder finishes the
//! linear values of the frames that it leaves: their locals, temporaries and
//! operands, the cells of a closure that took a value by move (also a block
//! that a call consumes, such as the block of `with_timeout`), the captures of
//! a task that a cancel stops (also before it starts), and the results of tasks
//! and fork branches that are done and that no `join` can take (ADR 0010). Some
//! shapes stay open until the core IR (ADR 0007): a spawn whose handle is not
//! kept drops the result of the task; a `fork` that can abort needs `on abort`
//! for each linear type of a branch value, which the checker does not ask for
//! yet; and a generic body that holds a `Task<T>` handle across an abort, or
//! whose task closure takes a value of a type parameter, does not tell its
//! caller.
//!
//! The scheduler is deterministic: one OS thread, `N` virtual workers and a
//! seeded random choice among ready tasks. An idle worker steals only a task that
//! the checker marked `stealable`.
//!
//! Entry points: [`run_main`] and [`run_tests`].

pub mod code;
pub mod compile;
pub mod compile_ir;
pub mod error;
pub mod heap;
mod machine;
pub mod oracle;
pub mod rng;
pub mod runtime;
pub mod trace;
pub mod value;

use std::collections::BTreeSet;

use weft_check::Checked;
use weft_sema::Analysis;

pub use error::{ErrorKind, RuntimeError};
pub use oracle::facts::{FactReport, IrStep};
pub use trace::{SuspendReason, TaskEnd, TraceEvent};

use crate::compile::{ArgOrder, ByValue, Exports, IntOps};
use crate::machine::{Machine, TaskResult};
use crate::runtime::Runtime;
use crate::value::{Cap, Obj, Value};

/// The compiler that makes the code of a run.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Engine {
    /// The AST compiler ([`compile`]). It is the default.
    #[default]
    Ast,
    /// The IR compiler ([`compile_ir`]): it compiles the core IR of the
    /// program (`docs/ir.md` 8.1). For a program with a body that has no
    /// IR (a type error, an error in a declaration, W0303), the AST compiler
    /// runs the program, and [`RunOutcome::fallback`] tells why. The checker
    /// rejects these programs.
    Ir,
}

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
    /// Turns on the oracle checks (see [`oracle`]): a dangling reference, a
    /// buffer that a `Vec` moves, a linear leak, a data race and a stealable
    /// task that reaches a nonportable value are faults. Off by default.
    pub oracle: bool,
    /// The compiler that makes the code.
    pub engine: Engine,
    /// Turns on the fact oracle and trace conformance
    /// ([`oracle::facts`], `docs/ir.md` 8.5): the run checks the facts of
    /// the `ir` pipeline against what it does. The IR engine runs the
    /// program, whatever [`RunOptions::engine`] says. A failure is a fault
    /// whose message starts with `fact oracle` or `trace conformance`.
    /// Off by default.
    pub fact_oracle: bool,
    /// Records the IR location of each step of each frame of the IR engine
    /// ([`RunOutcome::ir_trace`]). Off by default.
    pub ir_trace: bool,
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
            oracle: false,
            engine: Engine::Ast,
            fact_oracle: false,
            ir_trace: false,
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
    /// With [`Engine::Ir`]: the reason why the AST compiler ran the program,
    /// if it did.
    pub fallback: Option<String>,
    /// With [`RunOptions::ir_trace`]: each step of the IR trace.
    pub ir_trace: Vec<IrStep>,
    /// With [`RunOptions::fact_oracle`]: what the fact oracle saw.
    pub fact_oracle: Option<FactReport>,
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

/// Returns the tasks that the checker marked stealable: the source unit and
/// the span of each. Two units can have the same byte offsets, so the unit is
/// part of the key.
pub fn stealable_spans(checked: &Checked) -> BTreeSet<(usize, u32, u32)> {
    let mut out = BTreeSet::new();
    for (b, r) in checked.analysis.bodies.iter().zip(&checked.reports) {
        for t in &r.violations.stealable {
            if let Some(info) = b.facts.tasks.get(t.index()) {
                out.insert((b.unit, info.span.lo, info.span.hi));
            }
        }
    }
    out
}

/// Returns the captures that each closure takes by value when it is made.
///
/// These are the captures that the closure moves, as semantic analysis gives
/// them (`FnFacts::by_value`). The checker sees each of these moves where the
/// closure is made, so the interpreter moves the value there too.
pub fn by_value_captures(analysis: &Analysis) -> ByValue {
    let mut out = ByValue::new();
    for b in &analysis.bodies {
        for &(span, v) in &b.facts.by_value {
            let name = b.facts.var(v).name.clone();
            out.entry((b.unit, span.lo, span.hi))
                .or_default()
                .insert(name);
        }
    }
    out
}

/// Returns the order of the arguments of the calls with named arguments whose
/// callee the compiler does not know (see [`ArgOrder`]), as semantic analysis
/// gives it (`FnFacts::arg_order`).
pub fn arg_orders(analysis: &Analysis) -> ArgOrder {
    let mut out = ArgOrder::new();
    for b in &analysis.bodies {
        for (span, order) in &b.facts.arg_order {
            out.insert((b.unit, span.lo, span.hi), order.clone());
        }
    }
    out
}

/// Returns the integer type of each arithmetic result (see [`IntOps`]), as
/// semantic analysis gives it (`FnFacts::int_ops`).
pub fn int_ops(analysis: &Analysis) -> IntOps {
    let mut out = IntOps::new();
    for b in &analysis.bodies {
        for (span, name) in &b.facts.int_ops {
            if let Some(it) = weft_sema::types::IntTy::from_name(name) {
                out.insert((b.unit, span.lo, span.hi), it);
            }
        }
    }
    out
}

/// Returns what the compiler needs from semantic analysis.
pub fn exports(analysis: &Analysis) -> Exports {
    Exports {
        by_value: by_value_captures(analysis),
        arg_order: arg_orders(analysis),
        int_ops: int_ops(analysis),
    }
}

/// Runs `fn main` of a checked program.
///
/// The interpreter does not refuse a program with diagnostics. Run-time guards
/// catch some errors that the checker rejects, for example a second resume of a
/// `once` continuation. The run is on a large stack ([`weft_sema::on_large_stack`]).
pub fn run_main(checked: &Checked, opts: &RunOptions) -> Result<RunOutcome, RuntimeError> {
    weft_sema::on_large_stack(|| {
        let (rt, fallback) = runtime(&checked.analysis, stealable_spans(checked), opts, None);
        with_fallback(run_main_with(&rt, opts), fallback)
    })
}

/// Runs `fn main` of an analysis that the checker did not see. No task is
/// stealable. The run is on a large stack ([`weft_sema::on_large_stack`]).
pub fn run_analysis_main(
    analysis: &Analysis,
    opts: &RunOptions,
) -> Result<RunOutcome, RuntimeError> {
    weft_sema::on_large_stack(|| {
        let (rt, fallback) = runtime(analysis, BTreeSet::new(), opts, None);
        with_fallback(run_main_with(&rt, opts), fallback)
    })
}

/// Runs every test block of a checked program, in source order, on a large
/// stack ([`weft_sema::on_large_stack`]).
pub fn run_tests(checked: &Checked, opts: &RunOptions) -> Vec<TestOutcome> {
    weft_sema::on_large_stack(|| {
        let (rt, fallback) = runtime(&checked.analysis, stealable_spans(checked), opts, None);
        tests_with_fallback(run_tests_with(&rt, opts), fallback.as_deref())
    })
}

/// Runs every test block of an analysis that the checker did not see, on a
/// large stack ([`weft_sema::on_large_stack`]).
pub fn run_analysis_tests(analysis: &Analysis, opts: &RunOptions) -> Vec<TestOutcome> {
    weft_sema::on_large_stack(|| {
        let (rt, fallback) = runtime(analysis, BTreeSet::new(), opts, None);
        tests_with_fallback(run_tests_with(&rt, opts), fallback.as_deref())
    })
}

/// A change of the facts of each component, for a test of the fact oracle.
pub type FactEdit<'e> = &'e (dyn Fn(&mut weft_facts::FnFacts) + Sync);

/// Makes the tables and the code of a run with the engine of `opts`. With
/// [`Engine::Ir`], the second value is the reason why the AST compiler
/// compiled the program, if it did. With the fact oracle, the IR engine
/// runs the program, and the runtime gets the components of its facts
/// (changed by `edit`, for a test).
fn runtime<'a>(
    analysis: &'a Analysis,
    stealable: BTreeSet<(usize, u32, u32)>,
    opts: &RunOptions,
    edit: Option<FactEdit<'_>>,
) -> (Runtime<'a>, Option<String>) {
    let (prog, sigs) = (&analysis.program, analysis.sigs.as_slice());
    if opts.engine == Engine::Ir || opts.fact_oracle {
        let built = weft_sema::irbuild::build(analysis);
        match compile_ir::compile_ir(prog, &built) {
            Ok(code) => {
                let mut rt = Runtime::with_code(prog, sigs, stealable, code);
                if opts.fact_oracle {
                    let mut comps = weft_sema::factgen::components(analysis, &built)
                        .map_err(|u| format!("the program is not in scope: {u}"));
                    if let (Ok(cs), Some(edit)) = (&mut comps, edit) {
                        for c in cs {
                            edit(&mut c.facts);
                        }
                    }
                    rt.facts = Some(std::rc::Rc::new(oracle::facts::FactInput { built, comps }));
                }
                return (rt, None);
            }
            Err(f) => {
                let rt = Runtime::new(prog, sigs, stealable, &exports(analysis));
                return (rt, Some(f.to_string()));
            }
        }
    }
    (
        Runtime::new(prog, sigs, stealable, &exports(analysis)),
        None,
    )
}

/// Runs `fn main` of a checked program with the fact oracle, as
/// [`run_main`] does, after `edit` changes the facts of each component.
/// A test breaks the facts by hand and sees the fact oracle fail.
pub fn run_main_with_facts(
    checked: &Checked,
    opts: &RunOptions,
    edit: impl Fn(&mut weft_facts::FnFacts) + Sync,
) -> Result<RunOutcome, RuntimeError> {
    weft_sema::on_large_stack(|| {
        let (rt, fallback) = runtime(
            &checked.analysis,
            stealable_spans(checked),
            opts,
            Some(&edit),
        );
        with_fallback(run_main_with(&rt, opts), fallback)
    })
}

/// Writes the reason of a fallback into the outcome of a run.
fn with_fallback(
    r: Result<RunOutcome, RuntimeError>,
    fallback: Option<String>,
) -> Result<RunOutcome, RuntimeError> {
    match r {
        Ok(mut o) => {
            o.fallback = fallback;
            Ok(o)
        }
        Err(mut e) => {
            e.outcome.fallback = fallback;
            Err(e)
        }
    }
}

/// Writes the reason of a fallback into the outcome of each test.
fn tests_with_fallback(mut ts: Vec<TestOutcome>, fallback: Option<&str>) -> Vec<TestOutcome> {
    for t in &mut ts {
        t.outcome.fallback = fallback.map(str::to_string);
    }
    ts
}

fn env_value(rt: &Runtime<'_>) -> Value {
    let Some(adt) = rt.b.env else {
        return Value::Unit;
    };
    let fields = rt.adts[adt.index()]
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
            if let Err(e) = m.oracle_end() {
                return Err(with_outcome(e, m));
            }
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

/// Runs `fn main` of a program whose tables and code are ready, on the
/// current stack. A test can give it hand-made code.
pub fn run_runtime_main(rt: &Runtime<'_>, opts: &RunOptions) -> Result<RunOutcome, RuntimeError> {
    run_main_with(rt, opts)
}

fn run_main_with(rt: &Runtime<'_>, opts: &RunOptions) -> Result<RunOutcome, RuntimeError> {
    let Some(f) = rt.main_fn() else {
        return Err(RuntimeError::new(
            ErrorKind::NoMain,
            "the program has no `fn main`",
            None,
        ));
    };
    let Some(code) = rt.compiled.fn_code.get(f.index()).copied().flatten() else {
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

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

    use super::*;

    /// Runs `main` of `src` with each task stealable, as if the checker had
    /// marked them so (the checker pins a task that reaches an `Rc`).
    fn run_stealable(src: &str, oracle: bool) -> Result<RunOutcome, RuntimeError> {
        let a = weft_sema::analyze_source(src, weft_sema::Options::default()).unwrap();
        let mut all = BTreeSet::new();
        for b in &a.bodies {
            for t in &b.facts.tasks {
                all.insert((b.unit, t.span.lo, t.span.hi));
            }
        }
        assert!(!all.is_empty(), "the program has no task");
        let rt = Runtime::new(&a.program, &a.sigs, all, &exports(&a));
        let opts = RunOptions {
            max_steps: Some(100_000),
            workers: 4,
            oracle,
            ..RunOptions::default()
        };
        run_main_with(&rt, &opts)
    }

    #[test]
    fn a_stealable_task_that_reaches_an_rc_faults() {
        let src = "struct W { score: u64, rc: Rc<u64> }\n\
            fn main() / par, async {\n let w = W { score: 7, rc: Rc.new(1) }\n\
            scope { s => s.spawn(|| print(w.rc)) }\n}";
        assert!(run_stealable(src, false).is_ok());
        let e = run_stealable(src, true).expect_err("the oracle stops the run");
        assert!(
            e.message
                .contains("a stealable task reaches a nonportable value (`Rc`)"),
            "{}",
            e.message
        );
    }

    #[test]
    fn a_reference_reaches_only_its_place() {
        // `&w.score` is portable. The `Rc` in the other field of `w`, and the
        // other elements of a slice, are not reached.
        let src = "struct W { score: u64, rc: Rc<u64> }\n\
            fn show(r: &u64) / par, async { scope { s => s.spawn(|| print(r)) } }\n\
            fn main() / par, async {\n let w = W { score: 7, rc: Rc.new(1) }\n\
            let r = &w.score\n scope { s => s.spawn(|| print(r)) }\n show(&w.score)\n\
            let t = (5, Rc.new(1))\n let q = &t.0\n scope { s => s.spawn(|| print(q)) }\n}";
        let out = run_stealable(src, true).expect("the oracle accepts the program");
        assert_eq!(out.stdout, "7\n7\n5\n");
    }
}
