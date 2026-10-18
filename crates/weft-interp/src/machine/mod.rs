//! The abstract machine: tasks with explicit frame stacks, and the scheduler.
//!
//! Each task has a stack of [`Frame`]s. A code frame runs one code unit. Mark
//! frames delimit handlers, clauses, scopes, timeouts and simulations. A perform
//! moves the frames above its handler mark into a continuation. Unwinding is a
//! frame too, so `on abort` functions run as normal code.

mod effects;
mod exec;
mod natives;
mod show;

use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;

use weft_syntax::ast::Span;
use weft_verified::lifecycle::{Continuation, Linear};

use crate::code::Code;
use crate::error::{ErrorKind, RuntimeError};
use crate::heap::{Heap, SlotKind};
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
}

/// A `handle` mark: the delimiter of a continuation.
#[derive(Clone, Debug)]
pub struct HandleMark {
    /// The handler instance.
    pub id: u64,
    /// The clauses: operation, code and captured cells.
    pub clauses: Rc<[(usize, CodeId, Rc<[CellId]>)]>,
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
    /// A `sim.run` body.
    Sim {
        /// The state outside the simulation.
        saved: Box<SimSaved>,
    },
    /// An unwinding.
    Unwind(Box<Unwind>),
}

/// The state that `sim.run` replaces.
#[derive(Clone, Debug)]
pub struct SimSaved {
    sim: Option<SimState>,
    sched: Rng,
    rand: Rng,
}

/// The simulation state.
#[derive(Clone, Debug)]
pub struct SimState {
    /// The seed.
    pub seed: u64,
    /// The virtual time when the simulation started.
    pub start: u64,
    /// The current partition.
    pub partition: Option<(Vec<u64>, Vec<u64>)>,
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

/// A request that a task handles at its next suspension point.
#[derive(Clone, Debug)]
pub enum Interrupt {
    /// A `with_timeout` deadline passed.
    Timeout(u64),
    /// A child failed: perform `fail(msg)`.
    Fail(String),
}

/// A task.
#[derive(Clone, Debug)]
pub struct Task {
    /// The frames.
    pub frames: Vec<Frame>,
    /// The state.
    pub state: TState,
    /// The worker that owns the task.
    pub worker: usize,
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
    /// The task unwinds because of a failure or a cancellation.
    pub aborting: bool,
    /// A pending interrupt.
    pub interrupt: Option<Interrupt>,
    /// The value that the task gets when it wakes.
    pub wake: Option<Value>,
    /// What the task waits for.
    pub wait: Option<Wait>,
    /// The number of the current wait, to ignore old timers.
    pub wait_seq: u64,
    /// The task stopped at a suspension point and has not run since.
    pub suspended: bool,
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
    /// The failure was raised in the owner.
    pub propagated: bool,
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
    /// The type.
    pub adt: usize,
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
    pub(crate) now: u64,
    sched_rng: Rng,
    pub(crate) rand_rng: Rng,
    pub(crate) sim: Option<SimState>,
    next_id: u64,
    pub(crate) trace: Vec<TraceEvent>,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
    steps: u64,
    pub(crate) blocking_calls: usize,
    pub(crate) cur: TaskId,
    quantum_used: u64,
    pub(crate) requests: usize,
    pub(crate) listeners: Vec<String>,
}

const RAND_SALT: u64 = 0x5EED_0F_7A4D;

impl<'r, 'a> Machine<'r, 'a> {
    /// Makes a machine for one run.
    pub fn new(rt: &'r Runtime<'a>, opts: &RunOptions) -> Self {
        let workers = opts.workers.max(1);
        Self {
            rt,
            opts: opts.clone(),
            heap: Heap::new(Rc::clone(&rt.move_only)),
            tasks: Vec::new(),
            queues: (0..workers).map(|_| VecDeque::new()).collect(),
            scopes: Vec::new(),
            conts: Vec::new(),
            lins: Vec::new(),
            timers: BTreeMap::new(),
            timer_seq: 0,
            now: 0,
            sched_rng: Rng::new(opts.seed),
            rand_rng: Rng::new(opts.seed ^ RAND_SALT),
            sim: None,
            next_id: 1,
            trace: Vec::new(),
            stdout: String::new(),
            stderr: String::new(),
            steps: 0,
            blocking_calls: 0,
            cur: 0,
            quantum_used: 0,
            requests: 0,
            listeners: Vec::new(),
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
            Frame::Code(cf) => cf
                .code
                .spans
                .get(cf.pc.saturating_sub(1))
                .copied(),
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
        Ok(CodeFrame {
            code,
            pc: 0,
            slots,
            caps,
            stack: Vec::new(),
            temps: Vec::new(),
            marks: Vec::new(),
            loops: Vec::new(),
            henv,
        })
    }

    /// Adds a task with one frame and puts it in a run queue.
    pub(crate) fn add_task(
        &mut self,
        frame: CodeFrame,
        worker: usize,
        stealable: bool,
        scope: Option<ScopeId>,
    ) -> TaskId {
        let id = self.tasks.len();
        self.tasks.push(Task {
            frames: vec![Frame::Code(frame)],
            state: TState::Ready,
            worker,
            stealable,
            scope,
            result: None,
            handle: Linear::new(),
            cancel: false,
            aborting: false,
            interrupt: None,
            wake: None,
            wait: None,
            wait_seq: 0,
            suspended: true,
        });
        if let Some(q) = self.queues.get_mut(worker) {
            q.push_back(id);
        }
        id
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
        let w = task.worker;
        if let Some(q) = self.queues.get_mut(w) {
            q.push_back(t);
        }
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
        if self.tasks[t].state == TState::Blocked && !self.tasks[t].aborting {
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
        if self.tasks[owner].interrupt.is_none() {
            self.scopes[sid].propagated = true;
            self.tasks[owner].interrupt = Some(Interrupt::Fail(msg.to_string()));
        }
        if self.tasks[owner].state == TState::Blocked {
            self.wake(owner, None);
        }
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
                    let has = self.tasks[task]
                        .frames
                        .iter()
                        .any(|f| matches!(f, Frame::Timeout { id: x, .. } if *x == id));
                    if !has {
                        continue;
                    }
                    self.tasks[task].interrupt = Some(Interrupt::Timeout(id));
                    if self.tasks[task].state == TState::Blocked && !self.tasks[task].aborting {
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

    /// Picks a worker and a task. An idle worker may steal only a stealable task.
    fn pick(&mut self) -> Option<(usize, TaskId, Option<usize>)> {
        let n = self.queues.len();
        let mut cands = Vec::new();
        for w in 0..n {
            if let Some(&t) = self.queues[w].front() {
                cands.push((w, t, None));
                continue;
            }
            for v in 0..n {
                if v == w {
                    continue;
                }
                if let Some(&t) = self.queues[v]
                    .iter()
                    .rev()
                    .find(|&&t| self.tasks[t].stealable)
                {
                    cands.push((w, t, Some(v)));
                }
            }
        }
        if cands.is_empty() {
            return None;
        }
        let i = self.sched_rng.below(cands.len());
        Some(cands[i])
    }

    /// Runs tasks until the root task finishes.
    pub fn run_until_done(&mut self, root: TaskId) -> R<()> {
        while !self.is_done(root) {
            let Some((w, t, from)) = self.pick() else {
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
            match from {
                Some(v) => {
                    self.queues[v].retain(|&x| x != t);
                    self.tasks[t].worker = w;
                    self.trace.push(TraceEvent::Steal {
                        task: t,
                        from: v,
                        to: w,
                    });
                }
                None => {
                    self.queues[w].pop_front();
                }
            }
            self.trace.push(TraceEvent::Run { task: t, worker: w });
            self.run_quantum(t)?;
        }
        Ok(())
    }

    fn run_quantum(&mut self, t: TaskId) -> R<()> {
        self.cur = t;
        self.quantum_used = 0;
        self.tasks[t].state = TState::Running;
        let mut flow = Flow::Continue;
        if self.tasks[t].suspended {
            self.tasks[t].suspended = false;
            if let Some(f) = self.check_interrupt()? {
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
                        let w = self.tasks[t].worker;
                        self.queues[w].push_back(t);
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
        }
    }

    /// Returns true if the quantum of the current task expired.
    pub(crate) const fn quantum_expired(&self) -> bool {
        self.quantum_used >= self.opts.quantum
    }

    /// Handles a pending cancellation or interrupt at a suspension point.
    pub(crate) fn check_interrupt(&mut self) -> R<Option<Flow>> {
        let t = self.task();
        if t.aborting {
            t.interrupt = None;
            return Ok(None);
        }
        if t.cancel {
            return self.abort_task(TaskResult::Cancelled).map(Some);
        }
        match t.interrupt.take() {
            None => Ok(None),
            Some(Interrupt::Timeout(id)) => self.timeout_unwind(id),
            Some(Interrupt::Fail(msg)) => {
                let henv = self.top_henv();
                self.fail(msg, henv).map(Some)
            }
        }
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
        Ok(self.add_task(f, 0, false, None))
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
