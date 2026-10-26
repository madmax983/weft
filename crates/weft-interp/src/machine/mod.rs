//! The abstract machine: tasks with explicit frame stacks, and the scheduler.
//!
//! Each task has a stack of [`Frame`]s. A code frame runs one code unit. Mark
//! frames delimit handlers, clauses, scopes, timeouts and simulations. A perform
//! moves the frames above its handler mark into a continuation. Unwinding is a
//! frame too, so `on abort` functions run as normal code.

mod effects;
mod exec;
mod http;
mod natives;
mod show;

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::rc::Rc;

use weft_syntax::ast::Span;
use weft_verified::lifecycle::{Continuation, Linear};

use crate::code::Code;
use crate::error::{ErrorKind, RuntimeError};
use crate::heap::{Heap, SlotKind};
use crate::oracle::facts::{FactOracle, FactReport, IrStep};
use crate::rng::Rng;
use crate::runtime::Runtime;
use crate::trace::{SuspendReason, TaskEnd, TraceEvent};
use crate::value::{CellId, CodeId, ContId, HEnv, ScopeId, TaskId, Value};
use crate::{RunOptions, RunOutcome};

/// The result type of machine operations.
pub type R<T> = Result<T, RuntimeError>;

/// A frame that runs one code unit.
#[derive(Clone, Debug)]
pub struct CodeFrame {
    /// The code.
    pub code: Rc<Code>,
    /// The next instruction.
    pub pc: usize,
    /// The cell of each slot, while the slot is live.
    pub slots: Vec<Option<CellId>>,
    /// The captured cells.
    pub caps: Rc<[CellId]>,
    /// The cells of `caps` that the frame owns: the first frame of a task
    /// owns the captures that its closure moved. The unwinder finishes the
    /// linear values in them (ADR 0010).
    pub owned: Vec<CellId>,
    /// The operand stack.
    pub stack: Vec<Value>,
    /// Temporary cells of the current statements.
    pub temps: Vec<CellId>,
    /// The temporary count at the start of each open statement.
    pub marks: Vec<usize>,
    /// Stack and mark heights at the start of each open loop.
    pub loops: Vec<(usize, usize)>,
    /// The lexical handlers.
    pub henv: HEnv,
    /// In unwind mode (`docs/ir.md` 8.2): the cells that the frame had when
    /// its cleanup chain started. `None` on a normal path.
    pub chain: Option<Vec<CellId>>,
    /// With `--ir-trace` or the fact oracle: the number of the frame in
    /// the run (from 1). 0 for a frame that nothing follows.
    pub uid: u64,
}

/// One clause of a handler mark: operation, code and captured cells.
pub type Clause = (usize, CodeId, Rc<[CellId]>);

/// A `handle` mark: the delimiter of a continuation.
#[derive(Clone, Debug)]
pub struct HandleMark {
    /// The handler instance.
    pub id: u64,
    /// The clauses: operation, code and captured cells.
    pub clauses: Rc<[Clause]>,
    /// The handlers outside this one. Clauses run with them.
    pub outer: HEnv,
}

/// What happens when unwinding ends.
#[derive(Clone, Debug)]
pub enum After {
    /// Gives a value to the frame below (a handler aborted the computation).
    Deliver(Value),
    /// Ends the task.
    Finish(TaskResult),
    /// Performs `fail(msg)` from the frame below (a timeout).
    Fail {
        /// The message.
        msg: String,
        /// The handlers at the `with_timeout` call.
        henv: HEnv,
    },
}

/// An unwinding in progress.
#[derive(Clone, Debug)]
pub struct Unwind {
    /// The frames that remain, innermost last.
    pub frames: Vec<Frame>,
    /// Linear values that wait for `on abort`, innermost first.
    pub aborts: VecDeque<Value>,
    /// What happens at the end.
    pub then: After,
    /// The children of exited scopes were cancelled.
    pub prepass: bool,
    /// Tasks that must finish before unwinding goes on.
    pub children: Vec<TaskId>,
}

/// One frame of a task stack.
#[derive(Clone, Debug)]
pub enum Frame {
    /// A code unit.
    Code(CodeFrame),
    /// A handler.
    Handle(HandleMark),
    /// A running handler clause and its continuation.
    Clause {
        /// The continuation.
        cont: ContId,
    },
    /// A `scope`.
    Scope {
        /// The scope.
        scope: ScopeId,
    },
    /// A `fork` that waits for its branches.
    Fork {
        /// The implicit scope.
        scope: ScopeId,
        /// The branches, in order.
        tasks: Vec<TaskId>,
        /// The handlers at the `fork`.
        henv: HEnv,
    },
    /// A `with_timeout` block.
    Timeout {
        /// The timeout.
        id: u64,
        /// The handlers at the call.
        henv: HEnv,
    },
    /// A `sim.run` body. The code above it runs in the simulation.
    Sim {
        /// The simulation.
        sim: SimId,
        /// The simulated worker of the task before it entered the simulation.
        /// The end of the simulation gives it back.
        outer: usize,
    },
    /// An unwinding.
    Unwind(Box<Unwind>),
}

/// An index into the simulations of a run.
pub type SimId = usize;

/// The number of simulated workers of `sim.run` when the call gives none.
pub const SIM_WORKERS: usize = 4;

/// A simulation: the root handlers that `sim.run` gives its body (ADR 0010).
///
/// A task is in the simulation of the nearest `Sim` frame on its stack, else
/// in the simulation of its spawn site (`Task::sim`). The simulation has its
/// own scheduler and simulated workers, so its order of tasks does not depend
/// on `--workers` or on the tasks outside it.
#[derive(Clone, Debug)]
pub struct SimState {
    /// The virtual time when the simulation started.
    pub start: u64,
    /// The current partition. Phase 1 does not simulate the network: nothing
    /// reads it.
    pub partition: Option<(Vec<u64>, Vec<u64>)>,
    /// The scheduler of the simulation.
    sched: Rng,
    /// The randomness of the simulation.
    pub(crate) rand: Rng,
    /// The run queues of the simulated workers.
    queues: Vec<VecDeque<TaskId>>,
}

/// How a task ended.
#[derive(Clone, Debug)]
pub enum TaskResult {
    /// It returned a value.
    Ok(Value),
    /// It failed.
    Failed {
        /// The message.
        msg: String,
        /// The kind of failure.
        kind: ErrorKind,
        /// Where it failed.
        span: Option<Span>,
    },
    /// It was cancelled.
    Cancelled,
}

/// The state of a task.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TState {
    /// In a run queue.
    Ready,
    /// Running now.
    Running,
    /// Waiting.
    Blocked,
    /// Finished.
    Done,
}

/// What a blocked task waits for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Wait {
    /// A timer.
    Sleep,
    /// A task.
    Join(TaskId),
    /// All children of a scope.
    Scope(ScopeId),
    /// A set of tasks.
    Children(Vec<TaskId>),
    /// The blocking pool.
    Pool,
    /// A network connection.
    Accept,
}

/// A task.
#[derive(Clone, Debug)]
pub struct Task {
    /// The frames.
    pub frames: Vec<Frame>,
    /// The state.
    pub state: TState,
    /// The worker of the machine that owns the task.
    pub worker: usize,
    /// The simulated worker that owns the task while it runs in a simulation.
    /// The simulation chooses it, so it does not depend on `worker`
    /// (ADR 0010).
    pub sim_worker: usize,
    /// The checker allows other workers to steal the task.
    pub stealable: bool,
    /// The scope of the task.
    pub scope: Option<ScopeId>,
    /// The result.
    pub result: Option<TaskResult>,
    /// The linear state of the task handle.
    pub handle: Linear,
    /// A cancellation was requested.
    pub cancel: bool,
    /// The value that the task gets when it wakes.
    pub wake: Option<Value>,
    /// What the task waits for.
    pub wait: Option<Wait>,
    /// The number of the current wait, to ignore old timers.
    pub wait_seq: u64,
    /// The task stopped at a suspension point and has not run since.
    pub suspended: bool,
    /// The simulation of the spawn site of the task, if any.
    pub sim: Option<SimId>,
}

/// A scope record.
#[derive(Clone, Debug)]
pub struct ScopeRec {
    /// The task that runs the scope body.
    pub owner: TaskId,
    /// The children.
    pub children: Vec<TaskId>,
    /// The first failure of a child.
    pub failure: Option<String>,
    /// The failure was raised in the owner, or a joiner took it.
    pub propagated: bool,
    /// The handlers at the `scope` or the `fork`. A failure of a child goes to
    /// them, not to the handlers where the owner is when the child fails.
    pub henv: HEnv,
}

/// A captured continuation.
#[derive(Clone, Debug)]
pub struct ContRec {
    /// The verified state machine.
    pub k: Continuation,
    /// The captured frames, the handler mark first.
    pub frames: Vec<Frame>,
}

/// A linear value record.
#[derive(Clone, Debug)]
pub struct LinRec {
    /// The verified state machine.
    pub l: Linear,
}

/// A timer.
#[derive(Clone, Debug)]
pub enum Timer {
    /// Wakes a sleeping task.
    Wake {
        /// The task.
        task: TaskId,
        /// The wait number.
        seq: u64,
        /// The value it gets.
        value: Value,
    },
    /// A `with_timeout` deadline.
    Timeout {
        /// The task.
        task: TaskId,
        /// The timeout.
        id: u64,
    },
}

/// What a step did.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Flow {
    /// The task can go on.
    Continue,
    /// The task yields at a suspension point and stays ready.
    Yield,
    /// The quantum expired at a back-edge.
    Preempt,
    /// The task waits.
    Block,
    /// The task finished.
    Done,
}

/// The machine.
pub struct Machine<'r, 'a> {
    pub(crate) rt: &'r Runtime<'a>,
    pub(crate) opts: RunOptions,
    pub(crate) heap: Heap,
    pub(crate) tasks: Vec<Task>,
    queues: Vec<VecDeque<TaskId>>,
    pub(crate) scopes: Vec<ScopeRec>,
    pub(crate) conts: Vec<ContRec>,
    pub(crate) lins: Vec<LinRec>,
    timers: BTreeMap<(u64, u64), Timer>,
    timer_seq: u64,
    /// The `with_timeout` blocks whose deadline passed, by the id of the
    /// timeout. Each id belongs to the task of its block. The block times out
    /// at the next check of its task while its frame is on the task stack
    /// (`check_interrupt`): at once, after a resume that puts the frame back,
    /// or after the unwinding above the frame that defers it (`live_base`,
    /// ADR 0010). A set, not one slot, so two deadlines at one instant both
    /// hold.
    expired: BTreeSet<u64>,
    pub(crate) now: u64,
    sched_rng: Rng,
    pub(crate) rand_rng: Rng,
    pub(crate) sims: Vec<SimState>,
    next_id: u64,
    pub(crate) trace: Vec<TraceEvent>,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
    steps: u64,
    pub(crate) blocking_calls: usize,
    pub(crate) cur: TaskId,
    quantum_used: u64,
    pub(crate) listeners: Vec<String>,
    http: Option<http::HttpState>,
    /// The fact oracle (`crate::oracle::facts`), if it is on and the IR
    /// engine runs the program.
    pub(crate) facts: Option<Box<FactOracle>>,
    /// What the fact oracle saw, when it is on but checks nothing.
    fact_skip: Option<String>,
    /// With `--ir-trace`: the steps of the IR trace.
    pub(crate) ir_trace: Vec<IrStep>,
    /// With `--ir-trace`: the last IR location of each frame.
    pub(crate) trace_at: std::collections::HashMap<u64, (u32, u32, u32)>,
    /// The number of the last frame that the run numbered.
    next_uid: u64,
}

const RAND_SALT: u64 = 0x5EED_F00D_7A4D_C0DE;

impl<'r, 'a> Machine<'r, 'a> {
    /// Makes a machine for one run.
    pub fn new(rt: &'r Runtime<'a>, opts: &RunOptions) -> Self {
        let workers = opts.workers.max(1);
        let mut heap = Heap::new(Rc::clone(&rt.move_only));
        if opts.oracle {
            heap.enable_oracle();
        }
        let (facts, fact_skip) = match (&rt.facts, opts.fact_oracle) {
            (Some(input), true) => {
                heap.enable_facts_log();
                (
                    Some(Box::new(FactOracle::new(
                        Rc::clone(input),
                        &rt.compiled.codes,
                    ))),
                    None,
                )
            }
            (None, true) => (None, Some("the AST compiler runs the program".to_string())),
            _ => (None, None),
        };
        Self {
            rt,
            opts: opts.clone(),
            heap,
            tasks: Vec::new(),
            queues: (0..workers).map(|_| VecDeque::new()).collect(),
            scopes: Vec::new(),
            conts: Vec::new(),
            lins: Vec::new(),
            timers: BTreeMap::new(),
            timer_seq: 0,
            expired: BTreeSet::new(),
            now: 0,
            sched_rng: Rng::new(opts.seed),
            rand_rng: Rng::new(opts.seed ^ RAND_SALT),
            sims: Vec::new(),
            next_id: 1,
            trace: Vec::new(),
            stdout: String::new(),
            stderr: String::new(),
            steps: 0,
            blocking_calls: 0,
            cur: 0,
            quantum_used: 0,
            listeners: Vec::new(),
            http: None,
            facts,
            fact_skip,
            ir_trace: Vec::new(),
            trace_at: std::collections::HashMap::new(),
            next_uid: 0,
        }
    }

    /// Returns a fresh identifier for handlers and timeouts.
    pub(crate) const fn fresh_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Returns what the program wrote, the trace and the counters.
    pub fn outcome(&self) -> RunOutcome {
        RunOutcome {
            stdout: self.stdout.clone(),
            stderr: self.stderr.clone(),
            trace: self.trace.clone(),
            leaked_rc: self.heap.leaked_rc(),
            blocking_calls: self.blocking_calls,
            fallback: None,
            ir_trace: self.ir_trace.clone(),
            fact_oracle: self.opts.fact_oracle.then(|| {
                self.facts.as_ref().map_or_else(
                    || FactReport {
                        skipped: self.fact_skip.clone(),
                        ..FactReport::default()
                    },
                    |f| f.report.clone(),
                )
            }),
        }
    }

    /// Makes an error at the current instruction.
    pub(crate) fn err(&self, kind: ErrorKind, msg: impl Into<String>) -> RuntimeError {
        RuntimeError::new(kind, msg, self.span())
    }

    /// Makes a fault at the current instruction.
    pub(crate) fn fault(&self, msg: impl Into<String>) -> RuntimeError {
        self.err(ErrorKind::Fault, msg)
    }

    /// Returns the span of the current instruction of the current task.
    fn span(&self) -> Option<Span> {
        let t = self.tasks.get(self.cur)?;
        t.frames.iter().rev().find_map(|f| match f {
            Frame::Code(cf) => cf.code.spans.get(cf.pc.saturating_sub(1)).copied(),
            _ => None,
        })
    }

    /// Writes a line to standard output.
    pub(crate) fn out_line(&mut self, s: &str) {
        self.stdout.push_str(s);
        self.stdout.push('\n');
        if !self.opts.capture_output {
            println!("{s}");
        }
    }

    /// Writes a line to standard error.
    pub(crate) fn err_line(&mut self, s: &str) {
        self.stderr.push_str(s);
        self.stderr.push('\n');
        if !self.opts.capture_output {
            eprintln!("{s}");
        }
    }

    // -----------------------------------------------------------------------
    // Tasks
    // -----------------------------------------------------------------------

    /// Makes a code frame for a code unit with arguments.
    pub(crate) fn code_frame(
        &mut self,
        code: CodeId,
        args: Vec<Value>,
        caps: Rc<[CellId]>,
        henv: HEnv,
    ) -> R<CodeFrame> {
        let Some(code) = self.rt.compiled.codes.get(code).cloned() else {
            return Err(self.fault("bad code unit"));
        };
        if args.len() != code.n_params as usize {
            let msg = format!(
                "`{}` takes {} arguments, found {}",
                code.name,
                code.n_params,
                args.len()
            );
            for a in args {
                self.heap.drop_value(a);
            }
            return Err(self.fault(msg));
        }
        let mut slots = vec![None; code.n_slots as usize];
        for (i, a) in args.into_iter().enumerate() {
            slots[i] = Some(self.heap.alloc(SlotKind::Local, a));
        }
        let follow = self.facts.as_ref().is_some_and(|f| f.follows(&code));
        let uid = if follow || (self.opts.ir_trace && !code.locs.is_empty()) {
            self.next_uid += 1;
            self.next_uid
        } else {
            0
        };
        if follow {
            if let Some(f) = self.facts.as_mut() {
                f.enter(uid, &code, &slots, &caps, &self.heap);
            }
        }
        Ok(CodeFrame {
            code,
            pc: 0,
            slots,
            caps,
            owned: Vec::new(),
            stack: Vec::new(),
            temps: Vec::new(),
            marks: Vec::new(),
            loops: Vec::new(),
            henv,
            chain: None,
            uid,
        })
    }

    /// Adds a task with one frame and puts it in a run queue.
    /// `sim` is the simulation of the spawn site.
    pub(crate) fn add_task(
        &mut self,
        frame: CodeFrame,
        parent: Option<TaskId>,
        stealable: bool,
        scope: Option<ScopeId>,
        sim: Option<SimId>,
    ) -> TaskId {
        let id = self.tasks.len();
        // A task starts on the worker of its parent, in the machine and in the
        // simulation.
        let (worker, sim_worker) = parent
            .and_then(|p| self.tasks.get(p))
            .map_or((0, 0), |p| (p.worker, p.sim_worker));
        self.tasks.push(Task {
            frames: vec![Frame::Code(frame)],
            state: TState::Ready,
            worker,
            sim_worker,
            stealable,
            scope,
            result: None,
            // The runtime cancels the task: that is the `on abort` of a handle.
            handle: Linear::new(true),
            cancel: false,
            wake: None,
            wait: None,
            wait_seq: 0,
            suspended: true,
            sim,
        });
        if let (Some(p), Some(o)) = (parent, self.heap.oracle()) {
            o.borrow_mut().spawn(p, id);
        }
        self.enqueue(id);
        id
    }

    /// Returns the simulation that task `t` runs in: the one of the nearest
    /// `Sim` frame on its stack, also in an unwinding, else the one of its
    /// spawn site. A clause of a handler outside a `sim.run` runs below the
    /// `Sim` frame, so it is outside the simulation.
    pub(crate) fn sim_of(&self, t: TaskId) -> Option<SimId> {
        fn find(frames: &[Frame]) -> Option<SimId> {
            frames.iter().rev().find_map(|f| match f {
                Frame::Sim { sim, .. } => Some(*sim),
                Frame::Unwind(u) => find(&u.frames),
                _ => None,
            })
        }
        let task = self.tasks.get(t)?;
        find(&task.frames).or(task.sim)
    }

    /// Puts ready task `t` in the run queue of its worker: a queue of the
    /// machine, or of a simulated worker of its simulation.
    pub(crate) fn enqueue(&mut self, t: TaskId) {
        let sim = self.sim_of(t);
        let task = &self.tasks[t];
        let (queues, w) = match sim {
            Some(s) => (&mut self.sims[s].queues, task.sim_worker),
            None => (&mut self.queues, task.worker),
        };
        let n = queues.len().max(1);
        if let Some(q) = queues.get_mut(w % n) {
            q.push_back(t);
        }
        self.set_worker(t, sim.is_some(), w % n);
    }

    /// Sets the worker of task `t`: a simulated worker if `in_sim`, else a
    /// worker of the machine.
    fn set_worker(&mut self, t: TaskId, in_sim: bool, w: usize) {
        if in_sim {
            self.tasks[t].sim_worker = w;
        } else {
            self.tasks[t].worker = w;
        }
    }

    /// Returns the worker whose queue has task `t`: a simulated worker in a
    /// simulation, else a worker of the machine.
    pub(crate) fn queue_worker(&self, t: TaskId) -> usize {
        match (self.sim_of(t), self.tasks.get(t)) {
            (Some(_), Some(task)) => task.sim_worker,
            (None, Some(task)) => task.worker,
            (_, None) => 0,
        }
    }

    /// Returns the current task.
    pub(crate) fn task(&mut self) -> &mut Task {
        let c = self.cur;
        &mut self.tasks[c]
    }

    /// Returns true if a task finished.
    pub(crate) fn is_done(&self, t: TaskId) -> bool {
        self.tasks.get(t).is_none_or(|t| t.state == TState::Done)
    }

    /// Makes a ready task of a blocked one.
    pub(crate) fn wake(&mut self, t: TaskId, value: Option<Value>) {
        let Some(task) = self.tasks.get_mut(t) else {
            return;
        };
        if task.state != TState::Blocked {
            return;
        }
        task.state = TState::Ready;
        task.wait = None;
        task.wait_seq += 1;
        if let Some(v) = value {
            task.wake = Some(v);
        }
        self.enqueue(t);
        self.trace.push(TraceEvent::Resume { task: t });
    }

    /// Blocks the current task.
    pub(crate) fn block(&mut self, wait: Wait, reason: SuspendReason) -> Flow {
        let cur = self.cur;
        let t = self.task();
        t.state = TState::Blocked;
        t.wait = Some(wait);
        t.suspended = true;
        self.trace.push(TraceEvent::Suspend { task: cur, reason });
        Flow::Block
    }

    /// Returns the wait number of the current task. A timer with this number wakes
    /// the task only if the task did not wake since.
    pub(crate) fn wait_seq(&mut self) -> u64 {
        self.task().wait_seq
    }

    /// Requests cancellation of a task. It aborts at its next suspension point.
    pub(crate) fn cancel(&mut self, t: TaskId) {
        let Some(task) = self.tasks.get_mut(t) else {
            return;
        };
        if task.state == TState::Done || task.cancel {
            return;
        }
        task.cancel = true;
        self.trace.push(TraceEvent::Cancel { task: t });
        if self.tasks[t].state == TState::Blocked && !self.defers(t) {
            self.wake(t, None);
        }
    }

    /// Records the end of a task and wakes the tasks that wait for it.
    pub(crate) fn finish_task(&mut self, t: TaskId, result: TaskResult) {
        let end = match &result {
            TaskResult::Ok(_) => TaskEnd::Ok,
            TaskResult::Failed { msg, .. } => TaskEnd::Failed(msg.clone()),
            TaskResult::Cancelled => TaskEnd::Cancelled,
        };
        self.trace.push(TraceEvent::Finish { task: t, end });
        let failed = match &result {
            TaskResult::Failed { msg, .. } => Some(msg.clone()),
            _ => None,
        };
        let scope = self.tasks[t].scope;
        self.tasks[t].state = TState::Done;
        self.tasks[t].result = Some(result);
        self.tasks[t].frames.clear();
        if let (Some(sid), Some(msg)) = (scope, failed) {
            self.child_failed(sid, t, &msg);
        }
        self.wake_waiters();
    }

    /// A child of a scope failed: cancel its siblings and tell the owner.
    fn child_failed(&mut self, sid: ScopeId, child: TaskId, msg: &str) {
        let Some(s) = self.scopes.get_mut(sid) else {
            return;
        };
        if s.failure.is_none() {
            s.failure = Some(msg.to_string());
        }
        let siblings: Vec<TaskId> = s.children.iter().copied().filter(|&c| c != child).collect();
        let owner = s.owner;
        for c in siblings {
            self.cancel(c);
        }
        // The owner raises the failure at its next suspension point. A wait on this
        // scope raises it itself when the children are done.
        let waits_here = match &self.tasks[owner].wait {
            Some(Wait::Scope(x)) => *x == sid,
            Some(Wait::Join(j)) => self.scopes[sid].children.contains(j),
            Some(Wait::Children(_)) => true,
            _ => false,
        };
        if self.tasks[owner].state == TState::Done || waits_here {
            return;
        }
        // The owner raises the failure at its next suspension point while the
        // frame of the scope is on its stack (`check_interrupt`). The frame can
        // be away, in the continuation of a clause outside the scope. Then the
        // owner goes on, and it raises the failure when the frame is back, or at
        // the end of the scope (`raise_scope_failure`). Wake the owner only if
        // its check finds the failure.
        let t = &self.tasks[owner];
        let base = self.live_base(owner);
        let wake = t.state == TState::Blocked
            && !self.scopes[sid].propagated
            && Self::scope_frame(&t.frames, sid).is_some_and(|i| i >= base);
        if wake {
            self.wake(owner, None);
        }
    }

    /// Returns the index of the frame of scope `sid` (a `scope` or a `fork`) in
    /// `frames`.
    pub(crate) fn scope_frame(frames: &[Frame], sid: ScopeId) -> Option<usize> {
        frames.iter().rposition(
            |f| matches!(f, Frame::Scope { scope } | Frame::Fork { scope, .. } if *scope == sid),
        )
    }

    /// Returns the outermost scope on the stack of the current task, above
    /// its innermost unwinding (`live_base`), whose child failed, if the owner
    /// has not raised that failure yet. The unwind to that scope ends the
    /// scopes inside it too.
    fn failed_scope(&self) -> Option<ScopeId> {
        let base = self.live_base(self.cur);
        let frames = self.tasks[self.cur].frames.get(base..).unwrap_or_default();
        frames.iter().find_map(|f| match f {
            Frame::Scope { scope } | Frame::Fork { scope, .. } => self
                .scopes
                .get(*scope)
                .filter(|s| !s.propagated && s.failure.is_some() && s.owner == self.cur)
                .map(|_| *scope),
            _ => None,
        })
    }

    /// Wakes every task whose wait condition now holds.
    fn wake_waiters(&mut self) {
        let mut ready = Vec::new();
        for (i, t) in self.tasks.iter().enumerate() {
            if t.state != TState::Blocked {
                continue;
            }
            let ok = match &t.wait {
                Some(Wait::Join(j)) => self.is_done(*j),
                Some(Wait::Scope(s)) => self
                    .scopes
                    .get(*s)
                    .is_none_or(|s| s.children.iter().all(|&c| self.is_done(c))),
                Some(Wait::Children(cs)) => cs.iter().all(|&c| self.is_done(c)),
                _ => false,
            };
            if ok {
                ready.push(i);
            }
        }
        for t in ready {
            self.wake(t, None);
        }
    }

    // -----------------------------------------------------------------------
    // Timers
    // -----------------------------------------------------------------------

    /// Adds a timer.
    pub(crate) fn add_timer(&mut self, at: u64, t: Timer) {
        self.timer_seq += 1;
        self.timers.insert((at, self.timer_seq), t);
    }

    /// Removes the timer of a timeout.
    pub(crate) fn remove_timeout(&mut self, id: u64) {
        self.timers
            .retain(|_, t| !matches!(t, Timer::Timeout { id: x, .. } if *x == id));
        self.expired.remove(&id);
    }

    /// Gives a copy of a `with_timeout` block (a `multi` resume) timeout `new`
    /// with the deadline of timeout `old`. Each copy times out on its own.
    pub(crate) fn copy_timeout(&mut self, old: u64, new: u64) {
        let deadline = self.timers.iter().find_map(|(&(at, _), t)| match t {
            Timer::Timeout { task, id } if *id == old => Some((at, *task)),
            _ => None,
        });
        if let Some((at, task)) = deadline {
            self.add_timer(at, Timer::Timeout { task, id: new });
        }
        if self.expired.contains(&old) {
            self.expired.insert(new);
        }
    }

    /// Fires every timer that is due.
    pub(crate) fn fire_timers(&mut self) {
        loop {
            let Some((&key, _)) = self.timers.iter().next() else {
                return;
            };
            if key.0 > self.now {
                return;
            }
            let Some(timer) = self.timers.remove(&key) else {
                return;
            };
            match timer {
                Timer::Wake { task, seq, value } => {
                    let ok = self
                        .tasks
                        .get(task)
                        .is_some_and(|t| t.state == TState::Blocked && t.wait_seq == seq);
                    if ok {
                        self.wake(task, Some(value));
                    }
                }
                Timer::Timeout { task, id } => {
                    if self.is_done(task) {
                        continue;
                    }
                    // The deadline holds at the next check of the task while
                    // the frame is on its stack. A frame in a continuation
                    // waits for the resume that puts it back, and a frame
                    // below an unwinding waits for its end (`live_base`).
                    self.expired.insert(id);
                    let base = self.live_base(task);
                    let has = self.tasks[task]
                        .frames
                        .iter()
                        .rposition(|f| matches!(f, Frame::Timeout { id: x, .. } if *x == id))
                        .is_some_and(|i| i >= base);
                    if has && self.tasks[task].state == TState::Blocked {
                        self.wake(task, None);
                    }
                }
            }
        }
    }

    /// Moves the virtual clock to the next timer. Returns false if there is none.
    fn advance_to_next_timer(&mut self) -> bool {
        let Some((&(at, _), _)) = self.timers.iter().next() else {
            return false;
        };
        if at > self.now {
            self.now = at;
            self.trace.push(TraceEvent::Advance { now: at });
        }
        self.fire_timers();
        true
    }

    // -----------------------------------------------------------------------
    // The scheduler
    // -----------------------------------------------------------------------

    /// Returns the choices of a set of run queues: a worker and a task. An
    /// idle worker may steal only a stealable task.
    fn candidates(
        queues: &[VecDeque<TaskId>],
        tasks: &[Task],
    ) -> Vec<(usize, TaskId, Option<usize>)> {
        let n = queues.len();
        let mut cands = Vec::new();
        for w in 0..n {
            if let Some(&t) = queues[w].front() {
                cands.push((w, t, None));
                continue;
            }
            for (v, q) in queues.iter().enumerate() {
                if v == w {
                    continue;
                }
                if let Some(&t) = q.iter().rev().find(|&&t| tasks[t].stealable) {
                    cands.push((w, t, Some(v)));
                }
            }
        }
        cands
    }

    /// Picks a worker and a task. A simulation with a ready task is one choice
    /// of the machine; its own scheduler then picks its task, so that its
    /// order does not depend on `--workers` (ADR 0010).
    fn pick(&mut self) -> Option<(Option<SimId>, usize, TaskId, Option<usize>)> {
        let cands = Self::candidates(&self.queues, &self.tasks);
        let sims: Vec<SimId> = (0..self.sims.len())
            .filter(|&s| !Self::candidates(&self.sims[s].queues, &self.tasks).is_empty())
            .collect();
        let total = cands.len() + sims.len();
        if total == 0 {
            return None;
        }
        let i = self.sched_rng.below(total);
        if let Some(&(w, t, from)) = cands.get(i) {
            return Some((None, w, t, from));
        }
        let s = sims[i - cands.len()];
        let inner = Self::candidates(&self.sims[s].queues, &self.tasks);
        let j = self.sims[s].sched.below(inner.len());
        let (w, t, from) = inner[j];
        Some((Some(s), w, t, from))
    }

    /// Runs tasks until the root task finishes.
    pub fn run_until_done(&mut self, root: TaskId) -> R<()> {
        while !self.is_done(root) {
            let Some((sim, w, t, from)) = self.pick() else {
                if self.advance_to_next_timer() {
                    continue;
                }
                if self.http_pending() {
                    self.http_poll()?;
                    continue;
                }
                return Err(RuntimeError::new(
                    ErrorKind::Deadlock,
                    "every task waits and no timer can wake one",
                    None,
                ));
            };
            let queues = match sim {
                Some(s) => &mut self.sims[s].queues,
                None => &mut self.queues,
            };
            match from {
                Some(v) => {
                    queues[v].retain(|&x| x != t);
                    self.set_worker(t, sim.is_some(), w);
                    self.trace.push(TraceEvent::Steal {
                        task: t,
                        from: v,
                        to: w,
                    });
                }
                None => {
                    queues[w].pop_front();
                }
            }
            self.trace.push(TraceEvent::Run { task: t, worker: w });
            self.run_quantum(t)?;
        }
        Ok(())
    }

    fn run_quantum(&mut self, t: TaskId) -> R<()> {
        self.cur = t;
        if let Some(o) = self.heap.oracle() {
            o.borrow_mut().set_task(t);
        }
        self.quantum_used = 0;
        self.tasks[t].state = TState::Running;
        let mut flow = Flow::Continue;
        if self.tasks[t].suspended {
            self.tasks[t].suspended = false;
            if let Some(f) = self.check_interrupt() {
                flow = f;
            } else if let Some(v) = self.tasks[t].wake.take() {
                flow = self.deliver(v)?;
            }
        }
        loop {
            match flow {
                Flow::Continue => {}
                Flow::Yield | Flow::Preempt => {
                    if flow == Flow::Preempt {
                        self.trace.push(TraceEvent::Preempt { task: t });
                    }
                    if self.tasks[t].state == TState::Running {
                        self.tasks[t].state = TState::Ready;
                        self.enqueue(t);
                    }
                    return Ok(());
                }
                Flow::Block | Flow::Done => return Ok(()),
            }
            self.steps += 1;
            self.quantum_used += 1;
            if let Some(max) = self.opts.max_steps {
                if self.steps > max {
                    return Err(self.err(
                        ErrorKind::StepLimit,
                        format!("the program ran more than {max} steps"),
                    ));
                }
            }
            flow = self.step()?;
            self.oracle_check()?;
        }
    }

    /// With the oracle checks on, reports the first violation that a check
    /// found, and a live linear value that the heap dropped with no consume
    /// and no `on abort`.
    pub(crate) fn oracle_check(&self) -> R<()> {
        let Some(o) = self.heap.oracle() else {
            return Ok(());
        };
        let (violation, lins) = {
            let mut o = o.borrow_mut();
            (o.take_violation(), o.take_dropped_lins())
        };
        if let Some(v) = violation {
            return Err(self.fault(v));
        }
        let live = |id: usize| {
            self.lins
                .get(id)
                .is_some_and(|l| l.l.state == weft_verified::lifecycle::LinState::Live)
        };
        if lins.into_iter().any(live) {
            return Err(self.fault(
                "oracle: linear leak: a live linear value goes away with no consume and no `on abort`",
            ));
        }
        Ok(())
    }

    /// With the oracle checks on, reports a violation at the end of a normal
    /// run, and a linear value that is still live.
    pub(crate) fn oracle_end(&self) -> R<()> {
        if self.heap.oracle().is_none() {
            return Ok(());
        }
        self.oracle_check()?;
        if self
            .lins
            .iter()
            .any(|l| l.l.state == weft_verified::lifecycle::LinState::Live)
        {
            return Err(RuntimeError::new(
                ErrorKind::Fault,
                "oracle: linear leak: a linear value is still live at the end of the run",
                None,
            ));
        }
        Ok(())
    }

    /// With the oracle checks on, the running task sees that task `u` is done.
    pub(crate) fn oracle_join(&self, u: TaskId) {
        if let Some(o) = self.heap.oracle() {
            o.borrow_mut().join(u);
        }
    }

    /// Returns true if the quantum of the current task expired.
    pub(crate) const fn quantum_expired(&self) -> bool {
        self.quantum_used >= self.opts.quantum
    }

    /// Returns true if task `t` defers a cancel: an unwinding runs on its
    /// stack, also an `on abort` function above it. The effects proof models
    /// `on abort` as atomic, so a cancel does not cut it. The cancel stays in
    /// `Task::cancel`, and the task handles it when the unwinding ends (ADR
    /// 0010).
    pub(crate) fn defers(&self, t: TaskId) -> bool {
        self.tasks
            .get(t)
            .is_some_and(|x| x.frames.iter().any(|f| matches!(f, Frame::Unwind(_))))
    }

    /// Returns the index of the first frame of task `t` above its innermost
    /// unwinding, or 0 if no unwinding runs. A deadline of a `with_timeout`
    /// block and a failure of a child of a scope hold at once only for a frame
    /// at this index or above it: a frame of the `on abort` function that runs
    /// above the unwinding. Their unwinding does not cut that function. For a
    /// frame below the unwinding they stay pending: a deadline in
    /// `Machine::expired`, a failure in the record of its scope. The task
    /// handles them when the unwinding ends (ADR 0010).
    pub(crate) fn live_base(&self, t: TaskId) -> usize {
        self.tasks
            .get(t)
            .and_then(|x| x.frames.iter().rposition(|f| matches!(f, Frame::Unwind(_))))
            .map_or(0, |i| i + 1)
    }

    /// Handles a pending cancellation, deadline or failure of a child at a
    /// suspension point, and at the end of an unwinding.
    pub(crate) fn check_interrupt(&mut self) -> Option<Flow> {
        let cur = self.cur;
        if self.tasks[cur].cancel && !self.defers(cur) {
            return Some(self.abort_task(TaskResult::Cancelled));
        }
        if let Some(f) = self.late_timeout() {
            return Some(f);
        }
        let sid = self.failed_scope()?;
        self.scope_fail_unwind(sid)
    }

    /// Times out the outermost `with_timeout` block on the stack of the
    /// current task, above its innermost unwinding (`live_base`), whose
    /// deadline passed. Its unwinding ends the blocks inside it too, also one
    /// with the same deadline.
    pub(crate) fn late_timeout(&mut self) -> Option<Flow> {
        if self.expired.is_empty() {
            return None;
        }
        let base = self.live_base(self.cur);
        let frames = self.tasks[self.cur].frames.get(base..).unwrap_or_default();
        let id = frames.iter().find_map(|f| match f {
            Frame::Timeout { id, .. } if self.expired.contains(id) => Some(*id),
            _ => None,
        })?;
        self.expired.remove(&id);
        self.timeout_unwind(id)
    }

    /// Returns the handlers of the innermost code frame.
    pub(crate) fn top_henv(&mut self) -> HEnv {
        self.task()
            .frames
            .iter()
            .rev()
            .find_map(|f| match f {
                Frame::Code(cf) => Some(cf.henv.clone()),
                _ => None,
            })
            .unwrap_or_default()
    }

    /// Starts a root task for a code unit.
    pub fn start(&mut self, code: CodeId, args: Vec<Value>) -> R<TaskId> {
        let f = self.code_frame(code, args, Rc::from(Vec::new()), HEnv::default())?;
        Ok(self.add_task(f, None, false, None, None))
    }

    /// Returns the result of a finished task.
    pub fn result(&self, t: TaskId) -> Option<&TaskResult> {
        self.tasks.get(t).and_then(|t| t.result.as_ref())
    }

    /// Drops a value.
    pub fn drop_value(&mut self, v: Value) {
        self.heap.drop_value(v);
    }
}
