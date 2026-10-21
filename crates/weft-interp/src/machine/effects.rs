//! Effects: perform, resume, abort and unwinding.
//!
//! A perform finds the innermost lexical handler of its effect whose mark is on
//! the current task's stack. It moves the frames from that mark to the top into a
//! continuation, and runs the clause below them. `resume(v)` puts the frames back.
//! A clause that returns without a resume aborts the continuation: its frames
//! unwind and every live linear value in them gets `on abort`, innermost first.

use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;

use weft_sema::program::EffectId;
use weft_verified::lifecycle::{ContError, Continuation, LinState};

use super::{
    After, CodeFrame, ContRec, Flow, Frame, HandleMark, SimId, TaskResult, Timer, Unwind, Wait, R,
};
use crate::error::ErrorKind;
use crate::heap::{take_moved, SlotKind};
use crate::trace::{SuspendReason, TraceEvent};
use crate::value::{CellId, CodeId, ContId, HEnv, Place, TaskId, Value};

impl super::Machine<'_, '_> {
    /// Performs an effect operation with the lexical handlers `henv`.
    pub(crate) fn perform(
        &mut self,
        effect: EffectId,
        op: usize,
        args: Vec<Value>,
        henv: &HEnv,
    ) -> R<Flow> {
        let Some((idx, code, cells, outer)) = self.find_handler(effect, op, henv) else {
            return self.root_op(effect, op, args);
        };
        let multi = self
            .rt
            .prog
            .effects
            .get(effect.index())
            .and_then(|e| e.ops.get(op))
            .is_some_and(|o| o.multi);
        let frames = self.task().frames.split_off(idx);
        let k = self.conts.len();
        self.conts.push(ContRec {
            k: Continuation::new(multi),
            frames,
        });
        self.task().frames.push(Frame::Clause { cont: k });
        let mut args = args;
        args.push(Value::Cont(k));
        let f = self.code_frame(code, args, cells, outer)?;
        self.task().frames.push(Frame::Code(f));
        Ok(Flow::Continue)
    }

    /// Finds the handler mark and the clause for an operation.
    fn find_handler(
        &self,
        effect: EffectId,
        op: usize,
        henv: &HEnv,
    ) -> Option<(usize, CodeId, Rc<[CellId]>, HEnv)> {
        let frames = &self.tasks.get(self.cur)?.frames;
        for h in henv.handlers_for(effect) {
            let Some(idx) = frames
                .iter()
                .rposition(|f| matches!(f, Frame::Handle(m) if m.id == h))
            else {
                continue;
            };
            if let Some(Frame::Handle(m)) = frames.get(idx) {
                if let Some((_, code, cells)) = m.clauses.iter().find(|(o, _, _)| *o == op) {
                    return Some((idx, *code, Rc::clone(cells), m.outer.clone()));
                }
            }
        }
        None
    }

    /// Returns true if a perform of `op` of `effect` with the lexical
    /// handlers `henv` goes to handler `id`, the handler of the capability of
    /// the perform (`docs/ir.md` 8.1). It is also true if the mark of handler
    /// `id` is not on the stack of the task (the capability left its
    /// handler, W0313), or if the handler has no clause for `op` (the
    /// operation goes to an outer handler): then the machine finds a handler
    /// as for a perform through the row.
    pub(crate) fn finds_handler_of_cap(
        &self,
        effect: EffectId,
        op: usize,
        id: u64,
        henv: &HEnv,
    ) -> bool {
        let Some(frames) = self.tasks.get(self.cur).map(|t| &t.frames) else {
            return true;
        };
        let takes = frames.iter().any(
            |f| matches!(f, Frame::Handle(m) if m.id == id && m.clauses.iter().any(|c| c.0 == op)),
        );
        if !takes {
            return true;
        }
        match self.find_handler(effect, op, henv) {
            Some((idx, ..)) => matches!(frames.get(idx), Some(Frame::Handle(m)) if m.id == id),
            None => false,
        }
    }

    /// Performs `fail(msg)`.
    pub(crate) fn fail(&mut self, msg: String, henv: &HEnv) -> R<Flow> {
        let Some(e) = self.rt.b.fail else {
            let span = self.span_now();
            return Ok(self.abort_task(TaskResult::Failed {
                msg,
                kind: ErrorKind::Failed,
                span,
            }));
        };
        let op = self.rt.prog.effects[e]
            .ops
            .iter()
            .position(|o| o.name == "fail")
            .unwrap_or(0);
        self.perform(e, op, vec![Value::str(&msg)], henv)
    }

    /// Resumes a continuation with a value.
    pub(crate) fn resume(&mut self, k: ContId, args: Vec<Value>) -> R<Flow> {
        let v = args.into_iter().next().unwrap_or_default();
        let Some(rec) = self.conts.get_mut(k) else {
            return Err(self.fault("internal: bad continuation"));
        };
        match rec.k.resume() {
            Ok(()) => {}
            Err(ContError::AlreadyResumed) => {
                return Err(self.fault("a `once` continuation was resumed twice"));
            }
            Err(ContError::AlreadyDropped) => {
                return Err(self.fault("a continuation was resumed after it was dropped"));
            }
        }
        let frames = if rec.k.multi {
            let tmpl = std::mem::take(&mut rec.frames);
            let copy = self.copy_frames(&tmpl);
            self.conts[k].frames = tmpl;
            copy
        } else {
            std::mem::take(&mut rec.frames)
        };
        self.task().frames.extend(frames);
        let flow = self.deliver(v)?;
        // A `with_timeout` deadline that passed while the block was in the
        // continuation holds now: the block times out (ADR 0010).
        if let Some(f) = self.late_timeout() {
            return Ok(f);
        }
        Ok(flow)
    }

    /// Gives a value to the frame on top. Marks pass it down.
    pub(crate) fn deliver(&mut self, v: Value) -> R<Flow> {
        let cur = self.cur;
        loop {
            let Some(top) = self.tasks[cur].frames.last_mut() else {
                return self.end_task(v);
            };
            match top {
                Frame::Code(cf) => {
                    cf.stack.push(v);
                    return Ok(Flow::Continue);
                }
                Frame::Unwind(_) => {
                    // The result of an `on abort` function.
                    self.heap.drop_value(v);
                    return Ok(Flow::Continue);
                }
                Frame::Handle(_) | Frame::Scope { .. } => {
                    self.tasks[cur].frames.pop();
                }
                Frame::Timeout { id, .. } => {
                    let id = *id;
                    self.tasks[cur].frames.pop();
                    self.remove_timeout(id);
                }
                Frame::Sim { outer, .. } => {
                    let outer = *outer;
                    self.tasks[cur].frames.pop();
                    self.tasks[cur].sim_worker = outer;
                    self.trace.push(TraceEvent::SimEnd);
                }
                Frame::Clause { cont } => {
                    let k = *cont;
                    self.tasks[cur].frames.pop();
                    let frames = std::mem::take(&mut self.conts[k].frames);
                    if self.conts[k].k.drop_now() {
                        // The clause returned without a resume: abort the computation.
                        self.tasks[cur].frames.push(Frame::Unwind(Box::new(Unwind {
                            frames,
                            aborts: VecDeque::new(),
                            then: After::Deliver(v),
                            prepass: false,
                            children: Vec::new(),
                        })));
                        return Ok(Flow::Continue);
                    }
                    // The clause ends: a closure that it gave away cannot
                    // resume the continuation later.
                    self.conts[k].k.end();
                    self.drop_frames(frames);
                }
                Frame::Fork { .. } => {
                    return Err(self.fault("internal: a value reached a fork mark"));
                }
            }
        }
    }

    /// Ends the current task with the value `v`. If the unwinder already
    /// finished the handle of the task (its `on abort` cancelled the task),
    /// no `join` can take the value. Then the task finishes the live linear
    /// parts of the value itself before it ends (ADR 0010).
    fn end_task(&mut self, v: Value) -> R<Flow> {
        let cur = self.cur;
        if self.tasks[cur].handle.state != LinState::Aborted {
            self.finish_task(cur, TaskResult::Ok(v));
            return Ok(Flow::Done);
        }
        let mut found = Vec::new();
        let rest = self.extract_linear(v, &mut found);
        let mut live = VecDeque::new();
        for x in found {
            if self.unwind_lin(&x)? {
                live.push_back(x);
            } else {
                self.heap.drop_value(x);
            }
        }
        if live.is_empty() {
            self.finish_task(cur, TaskResult::Ok(rest));
            return Ok(Flow::Done);
        }
        self.tasks[cur].frames.push(Frame::Unwind(Box::new(Unwind {
            frames: Vec::new(),
            aborts: live,
            then: After::Finish(TaskResult::Ok(rest)),
            prepass: true,
            children: Vec::new(),
        })));
        Ok(Flow::Continue)
    }

    /// Starts a simulation with `workers` simulated workers: it replaces the
    /// root handlers for the code above its `Sim` frame and for the tasks that
    /// this code spawns.
    pub(crate) fn enter_sim(&mut self, seed: u64, workers: usize) -> SimId {
        self.sims.push(super::SimState {
            start: self.now,
            partition: None,
            sched: crate::rng::Rng::new(seed),
            rand: crate::rng::Rng::new(seed ^ super::RAND_SALT),
            queues: (0..workers.max(1)).map(|_| VecDeque::new()).collect(),
        });
        self.trace.push(TraceEvent::SimStart { seed });
        self.sims.len() - 1
    }

    /// Aborts the whole current task: unwinds every frame, then ends the task.
    pub(crate) fn abort_task(&mut self, result: TaskResult) -> Flow {
        let cur = self.cur;
        let frames = std::mem::take(&mut self.tasks[cur].frames);
        self.tasks[cur].frames.push(Frame::Unwind(Box::new(Unwind {
            frames,
            aborts: VecDeque::new(),
            then: After::Finish(result),
            prepass: false,
            children: Vec::new(),
        })));
        Flow::Continue
    }

    /// Aborts the block of a `with_timeout` whose deadline passed.
    pub(crate) fn timeout_unwind(&mut self, id: u64) -> Option<Flow> {
        let cur = self.cur;
        let idx = self.tasks[cur]
            .frames
            .iter()
            .rposition(|f| matches!(f, Frame::Timeout { id: x, .. } if *x == id))?;
        let henv = match &self.tasks[cur].frames[idx] {
            Frame::Timeout { henv, .. } => henv.clone(),
            _ => HEnv::default(),
        };
        let frames = self.tasks[cur].frames.split_off(idx);
        self.trace.push(TraceEvent::Timeout { task: cur });
        self.tasks[cur].frames.push(Frame::Unwind(Box::new(Unwind {
            frames,
            aborts: VecDeque::new(),
            then: After::Fail {
                msg: "timeout".into(),
                henv,
            },
            prepass: false,
            children: Vec::new(),
        })));
        Some(Flow::Continue)
    }

    /// A child of scope `sid` failed. Unwinds the frames of the scope, which
    /// cancels the other children, and then performs `fail(msg)` with the
    /// handlers of the scope, as `timeout_unwind` does for a `with_timeout`
    /// block. Handlers are lexical: a handler that the owner installed inside
    /// the scope does not get the failure (ADR 0010). `check_interrupt` calls
    /// this only while the frame of the scope is on the task stack.
    pub(crate) fn scope_fail_unwind(&mut self, sid: crate::value::ScopeId) -> Option<Flow> {
        let cur = self.cur;
        let idx = Self::scope_frame(&self.tasks[cur].frames, sid)?;
        let s = self.scopes.get_mut(sid)?;
        let msg = s.failure.clone()?;
        s.propagated = true;
        let henv = s.henv.clone();
        let frames = self.tasks[cur].frames.split_off(idx);
        self.tasks[cur].frames.push(Frame::Unwind(Box::new(Unwind {
            frames,
            aborts: VecDeque::new(),
            then: After::Fail { msg, henv },
            prepass: false,
            children: Vec::new(),
        })));
        Some(Flow::Continue)
    }

    /// Returns the tasks of every scope in a set of frames.
    fn children_in(&self, frames: &[Frame], out: &mut Vec<TaskId>) {
        for f in frames {
            match f {
                Frame::Scope { scope } | Frame::Fork { scope, .. } => {
                    if let Some(s) = self.scopes.get(*scope) {
                        out.extend(s.children.iter().copied());
                    }
                }
                Frame::Clause { cont } => {
                    if let Some(c) = self.conts.get(*cont) {
                        self.children_in(&c.frames, out);
                    }
                }
                Frame::Unwind(u) => self.children_in(&u.frames, out),
                _ => {}
            }
        }
    }

    fn unwind_top(&mut self) -> R<&mut Unwind> {
        let cur = self.cur;
        match self.tasks[cur].frames.last_mut() {
            Some(Frame::Unwind(u)) => Ok(u),
            _ => Err(crate::error::RuntimeError::new(
                ErrorKind::Fault,
                "internal: no unwinding",
                None,
            )),
        }
    }

    /// One step of an unwinding.
    pub(crate) fn unwind_step(&mut self) -> R<Flow> {
        let u = self.unwind_top()?;
        if !u.prepass {
            u.prepass = true;
            let frames = std::mem::take(&mut u.frames);
            let mut kids = Vec::new();
            self.children_in(&frames, &mut kids);
            for &k in &kids {
                if self.is_done(k) {
                    self.oracle_join(k);
                }
            }
            kids.retain(|&t| !self.is_done(t));
            for &t in &kids {
                self.cancel(t);
            }
            let u = self.unwind_top()?;
            u.frames = frames;
            u.children = kids;
        }
        let kids = self.unwind_top()?.children.clone();
        let pending: Vec<TaskId> = kids.iter().copied().filter(|&t| !self.is_done(t)).collect();
        if !pending.is_empty() {
            return Ok(self.block(Wait::Children(pending), SuspendReason::Children));
        }
        for k in kids {
            self.oracle_join(k);
        }
        let u = self.unwind_top()?;
        if let Some(v) = u.aborts.pop_front() {
            return self.run_on_abort(v);
        }
        if let Some(f) = u.frames.pop() {
            return self.unwind_frame(f);
        }
        let cur = self.cur;
        let Some(Frame::Unwind(u)) = self.tasks[cur].frames.pop() else {
            return Err(self.fault("internal: no unwinding"));
        };
        let flow = match u.then {
            After::Deliver(v) => self.deliver(v)?,
            After::Finish(r) => {
                self.finish_task(cur, r);
                return Ok(Flow::Done);
            }
            After::Fail { msg, henv } => self.fail(msg, &henv)?,
        };
        // The unwinding deferred the interrupts of the task for the frames
        // below it (`defers`, `live_base`): a cancel, a deadline that passed,
        // a failure of a child. The task handles them now (ADR 0010).
        if flow == Flow::Done {
            return Ok(flow);
        }
        if let Some(f) = self.check_interrupt() {
            return Ok(f);
        }
        Ok(flow)
    }

    /// Unwinds one frame: finds live linear values and drops the rest.
    fn unwind_frame(&mut self, f: Frame) -> R<Flow> {
        match f {
            Frame::Code(cf) => {
                let mut found = Vec::new();
                for v in self.frame_values(cf) {
                    let rest = self.extract_linear(v, &mut found);
                    self.heap.drop_value(rest);
                }
                let mut live = Vec::new();
                for v in found {
                    if self.unwind_lin(&v)? {
                        live.push(v);
                    } else {
                        self.heap.drop_value(v);
                    }
                }
                self.unwind_top()?.aborts.extend(live);
            }
            Frame::Clause { cont } => {
                let frames = std::mem::take(&mut self.conts[cont].frames);
                if self.conts[cont].k.drop_now() {
                    self.unwind_top()?.frames.extend(frames);
                } else {
                    self.conts[cont].k.end();
                    self.drop_frames(frames);
                }
            }
            Frame::Scope { scope } | Frame::Fork { scope, .. } => {
                let all: Vec<TaskId> = self
                    .scopes
                    .get(scope)
                    .map(|s| s.children.clone())
                    .unwrap_or_default();
                for &k in &all {
                    if self.is_done(k) {
                        self.oracle_join(k);
                    }
                }
                let kids: Vec<TaskId> = all.iter().copied().filter(|&t| !self.is_done(t)).collect();
                if !kids.is_empty() {
                    for &t in &kids {
                        self.cancel(t);
                    }
                    let u = self.unwind_top()?;
                    u.frames.push(f);
                    u.children.clone_from(&kids);
                    return Ok(self.block(Wait::Children(kids), SuspendReason::Children));
                }
                // The results of the children that are done and that no
                // `join` can take: the value of a fork branch, and the result
                // of a task whose handle went to the scope (`done_results`).
                let live = self.done_results(&all)?;
                self.unwind_top()?.aborts.extend(live);
            }
            Frame::Timeout { id, .. } => self.remove_timeout(id),
            Frame::Sim { outer, .. } => {
                let cur = self.cur;
                self.tasks[cur].sim_worker = outer;
                self.trace.push(TraceEvent::SimEnd);
            }
            Frame::Handle(_) => {}
            Frame::Unwind(inner) => {
                let inner = *inner;
                // The value that the inner unwinding gives at its end, such as
                // the value of a clause that did not resume, goes away: the
                // unwinder finishes its linear parts.
                let mut found = Vec::new();
                match inner.then {
                    After::Deliver(v) | After::Finish(TaskResult::Ok(v)) => {
                        let rest = self.extract_linear(v, &mut found);
                        self.heap.drop_value(rest);
                    }
                    After::Finish(_) | After::Fail { .. } => {}
                }
                let mut live = Vec::new();
                for v in found {
                    if self.unwind_lin(&v)? {
                        live.push(v);
                    } else {
                        self.heap.drop_value(v);
                    }
                }
                let u = self.unwind_top()?;
                u.frames.extend(inner.frames);
                u.aborts.extend(inner.aborts);
                u.aborts.extend(live);
            }
        }
        Ok(Flow::Continue)
    }

    /// Returns the values of a code frame, innermost first: the operand stack from
    /// the top, then temporaries, then slots in reverse order, then the captures
    /// that the frame owns (the first frame of a task).
    ///
    /// A closure is a copy value, so it stays in its cell. A closure that owns
    /// cells is in the result too: the unwinder finishes the linear values in
    /// its cells (`extract_linear`).
    fn frame_values(&mut self, cf: CodeFrame) -> Vec<Value> {
        let mut vals: Vec<Value> = cf.stack.into_iter().rev().collect();
        let mut cells: Vec<CellId> = cf.temps.into_iter().rev().collect();
        // A slot of a temporary cell is on the temporary list too.
        let n = cf.code.local_slots();
        cells.extend(cf.slots.into_iter().take(n).rev().flatten());
        cells.extend(cf.owned.into_iter().rev());
        // The scope of each local and temporary ends here, as at a normal end
        // (`end_cells`): the oracle sees a later read through a reference
        // into the cell.
        for c in cells {
            if let Some(v) = self.heap.end_cell_value(c) {
                vals.push(v);
            } else if let Ok(s) = self.heap.slot(c) {
                owning_closures(&s.val, &mut vals);
            }
        }
        vals
    }

    /// Drops the frames of a continuation that will not run.
    pub(crate) fn drop_frames(&mut self, frames: Vec<Frame>) {
        for f in frames.into_iter().rev() {
            match f {
                Frame::Code(cf) => self.cleanup_frame(cf),
                Frame::Clause { cont } => {
                    let fs = std::mem::take(&mut self.conts[cont].frames);
                    let _ = self.conts[cont].k.drop_now();
                    self.conts[cont].k.end();
                    self.drop_frames(fs);
                }
                Frame::Timeout { id, .. } => self.remove_timeout(id),
                Frame::Unwind(u) => self.drop_frames(u.frames),
                _ => {}
            }
        }
    }

    /// Takes the live linear values out of a value.
    fn extract_linear(&mut self, v: Value, out: &mut Vec<Value>) -> Value {
        match v {
            Value::Struct(o)
                if o.lin.is_some_and(|id| {
                    self.lins
                        .get(id)
                        .is_some_and(|l| l.l.state == LinState::Live)
                }) =>
            {
                out.push(Value::Struct(o));
                Value::Moved
            }
            Value::Task(t)
                if self
                    .tasks
                    .get(t)
                    .is_some_and(|x| x.handle.state == LinState::Live) =>
            {
                out.push(Value::Task(t));
                Value::Moved
            }
            Value::Struct(mut o) => {
                let fields = std::mem::take(&mut o.fields);
                o.fields = fields
                    .into_iter()
                    .map(|f| self.extract_linear(f, out))
                    .collect();
                Value::Struct(o)
            }
            Value::Enum(mut e) => {
                let fields = std::mem::take(&mut e.fields);
                e.fields = fields
                    .into_iter()
                    .map(|f| self.extract_linear(f, out))
                    .collect();
                Value::Enum(e)
            }
            Value::Tuple(vs) => Value::Tuple(
                vs.into_iter()
                    .map(|f| self.extract_linear(f, out))
                    .collect(),
            ),
            Value::List(vs) => Value::List(
                vs.into_iter()
                    .map(|f| self.extract_linear(f, out))
                    .collect(),
            ),
            Value::Vec(c) | Value::Boxed(c) => {
                let owned = self
                    .heap
                    .slot(c)
                    .is_ok_and(|s| matches!(s.kind, SlotKind::Buf | SlotKind::Boxed));
                if owned {
                    if let Ok(inner) = self.heap.take(&Place::root(c)) {
                        let rest = self.extract_linear(inner, out);
                        if let Ok(s) = self.heap.slot_mut(c) {
                            s.val = rest;
                        }
                    }
                }
                v
            }
            // A closure holds the captures that it moved in cells of its own.
            Value::Closure(c) => {
                for &cell in &c.owned {
                    let inner = match self.heap.slot_mut(cell) {
                        Ok(s) => take_moved(&mut s.val),
                        Err(_) => continue,
                    };
                    let rest = self.extract_linear(inner, out);
                    if let Ok(s) = self.heap.slot_mut(cell) {
                        s.val = rest;
                    }
                }
                Value::Closure(c)
            }
            other => other,
        }
    }

    /// Marks a linear value as aborted. Returns true if `on abort` must run.
    /// A live value whose type has no `on abort` is a fault: the checker
    /// rejects it (W0602), and the unwinder cannot finish it.
    fn unwind_lin(&mut self, v: &Value) -> R<bool> {
        let r = match v {
            Value::Struct(o) => o
                .lin
                .and_then(|id| self.lins.get_mut(id))
                .map_or(Ok(false), |l| l.l.unwind()),
            Value::Task(t) => self
                .tasks
                .get_mut(*t)
                .map_or(Ok(false), |x| x.handle.unwind()),
            _ => Ok(false),
        };
        r.map_err(|_| {
            let ty = match v {
                Value::Struct(o) => self.rt.adts.get(o.adt.index()).map_or("?", |a| &*a.name),
                _ => "Task",
            };
            self.fault(format!(
                "a linear value of type `{ty}` has no `on abort`, so the unwinder cannot finish it"
            ))
        })
    }

    /// Runs `on abort` for one linear value. The record of the value is
    /// finished (`Aborted`), so the `on abort` function gets the value
    /// without its record.
    fn run_on_abort(&mut self, v: Value) -> R<Flow> {
        let cur = self.cur;
        match v {
            Value::Struct(mut o) => {
                o.lin = None;
                let info = &self.rt.adts[o.adt.index()];
                let ty = info.name.to_string();
                let f = info.on_abort;
                let code =
                    f.and_then(|f| self.rt.compiled.fn_code.get(f.index()).copied().flatten());
                let Some(code) = code else {
                    self.heap.drop_value(Value::Struct(o));
                    return Ok(Flow::Continue);
                };
                self.trace.push(TraceEvent::OnAbort { task: cur, ty });
                let f = self.code_frame(
                    code,
                    vec![Value::Struct(o)],
                    Rc::from(Vec::new()),
                    HEnv::default(),
                )?;
                self.task().frames.push(Frame::Code(f));
            }
            Value::Task(t) => {
                self.trace.push(TraceEvent::OnAbort {
                    task: cur,
                    ty: "Task".into(),
                });
                // A cancel does not finish the result of a task that is done:
                // the unwinder finishes its linear parts now. A task that is
                // not done finishes them itself when it ends (`end_task`).
                if self.is_done(t) {
                    let live = self.done_results(&[t])?;
                    self.unwind_top()?.aborts.extend(live);
                } else {
                    self.cancel(t);
                }
            }
            other => self.heap.drop_value(other),
        }
        Ok(Flow::Continue)
    }

    /// Performs `fail(msg)` with the handlers `henv` after the unwinder
    /// finishes the live linear parts of the results of `tasks` that are done:
    /// a `fork` with a failed branch does not give the values of the others.
    pub(crate) fn fail_after_results(
        &mut self,
        tasks: &[TaskId],
        msg: String,
        henv: HEnv,
    ) -> R<Flow> {
        let cur = self.cur;
        self.tasks[cur].frames.push(Frame::Unwind(Box::new(Unwind {
            frames: Vec::new(),
            aborts: VecDeque::new(),
            then: After::Fail { msg, henv },
            prepass: true,
            children: Vec::new(),
        })));
        let live = self.done_results(tasks)?;
        self.unwind_top()?.aborts.extend(live);
        Ok(Flow::Continue)
    }

    /// Takes the results of the tasks `tasks` that are done and that no
    /// `join` took, and returns their live linear parts, each marked as
    /// aborted (`unwind_lin`). The other parts are dropped. The unwinder runs
    /// `on abort` for the returned values.
    ///
    /// A handle that is live and that a value still holds keeps the result:
    /// the handle can leave the frames that unwind, for example in the value
    /// of a clause that does not resume. Its owner takes the result with a
    /// `join`, or the `on abort` of the handle finishes it (`run_on_abort`).
    /// So this takes only the result of a task whose handle was dropped, used
    /// or finished: a branch of a `fork`, a task whose handle went to the
    /// scope, a detached task, or a task whose handle the unwinder finished.
    fn done_results(&mut self, tasks: &[TaskId]) -> R<Vec<Value>> {
        let mut found = Vec::new();
        for &t in tasks {
            let ok = matches!(
                self.tasks.get(t).and_then(|x| x.result.as_ref()),
                Some(TaskResult::Ok(_))
            );
            let held = self
                .tasks
                .get(t)
                .is_some_and(|x| x.handle.state == LinState::Live)
                && !self.heap.handle_dropped(t);
            if !ok || held {
                continue;
            }
            if let Some(TaskResult::Ok(v)) = self.tasks[t].result.take() {
                let rest = self.extract_linear(v, &mut found);
                self.heap.drop_value(rest);
            }
        }
        let mut live = Vec::new();
        for v in found {
            if self.unwind_lin(&v)? {
                live.push(v);
            } else {
                self.heap.drop_value(v);
            }
        }
        Ok(live)
    }

    /// Copies the frames of a `multi` continuation. Cells that the frames own get
    /// fresh copies, so each resume starts from the captured state. A clause
    /// frame in them gets a copy of its continuation, with a copy of its frames:
    /// each copy resumes or drops its own continuation. The clauses of a handler
    /// mark in them capture the copied cells.
    fn copy_frames(&mut self, frames: &[Frame]) -> Vec<Frame> {
        // The continuations of the clause frames, also inside those continuations.
        let mut nested: Vec<(ContId, Vec<Frame>)> = Vec::new();
        let mut work = clause_conts(frames);
        while let Some(k) = work.pop() {
            if nested.iter().any(|(j, _)| *j == k) {
                continue;
            }
            let fs = self
                .conts
                .get(k)
                .map(|c| c.frames.clone())
                .unwrap_or_default();
            work.extend(clause_conts(&fs));
            nested.push((k, fs));
        }
        let lists: Vec<&[Frame]> = std::iter::once(frames)
            .chain(nested.iter().map(|(_, fs)| fs.as_slice()))
            .collect();
        let mut owned: Vec<CellId> = Vec::new();
        for f in lists.iter().copied().flatten() {
            if let Frame::Code(cf) = f {
                owned.extend(cf.slots.iter().flatten().copied());
                owned.extend(cf.temps.iter().copied());
                owned.extend(cf.owned.iter().copied());
            }
        }
        let mut extra = Vec::new();
        for &c in &owned {
            if let Ok(s) = self.heap.slot(c) {
                self.heap.owned_cells(&s.val, &mut extra);
            }
        }
        for f in lists.iter().copied().flatten() {
            if let Frame::Code(cf) = f {
                for v in &cf.stack {
                    self.heap.owned_cells(v, &mut extra);
                }
            }
        }
        owned.extend(extra);
        // Each nested continuation gets a record of its own, in the same state.
        let mut kmap: BTreeMap<ContId, ContId> = BTreeMap::new();
        for (k, _) in &nested {
            let Some(state) = self.conts.get(*k).map(|c| c.k) else {
                continue;
            };
            kmap.insert(*k, self.conts.len());
            self.conts.push(ContRec {
                k: state,
                frames: Vec::new(),
            });
        }
        let mut map: BTreeMap<CellId, CellId> = BTreeMap::new();
        for c in owned {
            if map.contains_key(&c) {
                continue;
            }
            let kind = self.heap.slot(c).map_or(SlotKind::Local, |s| s.kind);
            let n = self.heap.alloc(kind, Value::Moved);
            map.insert(c, n);
        }
        let pairs: Vec<(CellId, CellId)> = map.iter().map(|(a, b)| (*a, *b)).collect();
        for (old, new) in pairs {
            let v = self
                .heap
                .slot(old)
                .map(|s| s.val.clone())
                .unwrap_or_default();
            let nv = remap_conts(self.heap.remap(&v, &map), &kmap);
            if let Ok(s) = self.heap.slot_mut(new) {
                s.val = nv;
            }
        }
        for (k, fs) in &nested {
            let copy = self.copy_list(fs, &map, &kmap);
            if let Some(rec) = kmap.get(k).and_then(|&n| self.conts.get_mut(n)) {
                rec.frames = copy;
            }
        }
        self.copy_list(frames, &map, &kmap)
    }

    /// Copies a list of frames with the cell map `map` and the continuation map
    /// `kmap` of `copy_frames`.
    fn copy_list(
        &mut self,
        frames: &[Frame],
        map: &BTreeMap<CellId, CellId>,
        kmap: &BTreeMap<ContId, ContId>,
    ) -> Vec<Frame> {
        let m = |c: &CellId| map.get(c).copied().unwrap_or(*c);
        let mut out = Vec::new();
        for f in frames {
            out.push(match f {
                Frame::Code(cf) => {
                    let stack = cf
                        .stack
                        .iter()
                        .map(|v| remap_conts(self.heap.remap(v, map), kmap))
                        .collect();
                    Frame::Code(CodeFrame {
                        code: Rc::clone(&cf.code),
                        pc: cf.pc,
                        slots: cf.slots.iter().map(|s| s.as_ref().map(m)).collect(),
                        caps: cf.caps.iter().map(m).collect(),
                        owned: cf.owned.iter().map(m).collect(),
                        stack,
                        temps: cf.temps.iter().map(m).collect(),
                        marks: cf.marks.clone(),
                        loops: cf.loops.clone(),
                        henv: cf.henv.clone(),
                    })
                }
                Frame::Handle(h) => Frame::Handle(HandleMark {
                    id: h.id,
                    clauses: h
                        .clauses
                        .iter()
                        .map(|(op, code, cells)| (*op, *code, cells.iter().map(m).collect()))
                        .collect(),
                    outer: h.outer.clone(),
                }),
                Frame::Clause { cont } => Frame::Clause {
                    cont: kmap.get(cont).copied().unwrap_or(*cont),
                },
                // Each copy of a `with_timeout` block has a timeout of its own.
                Frame::Timeout { id, henv } => {
                    let new = self.fresh_id();
                    self.copy_timeout(*id, new);
                    Frame::Timeout {
                        id: new,
                        henv: henv.clone(),
                    }
                }
                other => other.clone(),
            });
        }
        out
    }

    // -----------------------------------------------------------------------
    // Root handlers
    // -----------------------------------------------------------------------

    /// Handles an operation that no user handler takes: the `std.rt` root
    /// handlers, or the simulation when `sim.run` is active.
    fn root_op(&mut self, effect: EffectId, op: usize, args: Vec<Value>) -> R<Flow> {
        let Some(e) = self.rt.prog.effects.get(effect.index()) else {
            return Err(self.fault("internal: bad effect"));
        };
        let opname = e.ops.get(op).map_or("", |o| o.name.as_str()).to_string();
        let ename = e.name.clone();
        if !e.is_std {
            return Err(self.fault(format!("no handler for `{ename}.{opname}` on this task")));
        }
        // A failure of a task goes to the task that joins it, also with no runtime.
        let child = self.tasks.get(self.cur).is_some_and(|t| t.scope.is_some());
        let to_joiner = ename == "Fail" && child;
        let sim = self.sim_of(self.cur);
        if self.opts.no_runtime && sim.is_none() && !to_joiner {
            return Err(self.fault(format!("no runtime: nothing handles `{ename}.{opname}`")));
        }
        let arg = args.into_iter().next();
        match (ename.as_str(), opname.as_str()) {
            ("Log", level) => {
                let msg = arg.map(|v| self.show(&v)).unwrap_or_default();
                self.err_line(&format!("{level}: {msg}"));
                self.deliver(Value::Unit)
            }
            ("Fail", _) => {
                let msg = arg.map(|v| self.show(&v)).unwrap_or_default();
                let span = self.span_now();
                Ok(self.abort_task(TaskResult::Failed {
                    msg,
                    kind: ErrorKind::Failed,
                    span,
                }))
            }
            ("Clock", "now") => {
                let start = sim.and_then(|s| self.sims.get(s)).map_or(0, |s| s.start);
                let now = self.now.saturating_sub(start);
                self.deliver(Value::Dur(now))
            }
            ("Clock", "sleep") => {
                let d = match arg.map(|v| self.deref_value(v)).transpose()? {
                    Some(Value::Dur(d)) => d,
                    Some(Value::Int(i)) => u64::try_from(i).unwrap_or(0),
                    _ => 0,
                };
                Ok(self.sleep_for(d))
            }
            ("Rand", _) => {
                let rng = match sim.and_then(|s| self.sims.get_mut(s)) {
                    Some(s) => &mut s.rand,
                    None => &mut self.rand_rng,
                };
                let r = rng.next_u64() >> 1;
                self.deliver(Value::Int(i64::try_from(r).unwrap_or(0)))
            }
            _ => Ok(self.yield_now()),
        }
    }

    /// Suspends the current task for `d` milliseconds of virtual time.
    pub(crate) fn sleep_for(&mut self, d: u64) -> Flow {
        if let Some(f) = self.check_interrupt() {
            return f;
        }
        let task = self.cur;
        let seq = self.wait_seq();
        let at = self.now.saturating_add(d);
        self.add_timer(
            at,
            Timer::Wake {
                task,
                seq,
                value: Value::Unit,
            },
        );
        self.block(Wait::Sleep, SuspendReason::Sleep)
    }

    /// Yields at a suspension point. The task stays ready.
    pub(crate) fn yield_now(&mut self) -> Flow {
        if let Some(f) = self.check_interrupt() {
            return f;
        }
        let cur = self.cur;
        let t = self.task();
        t.suspended = true;
        t.wake = Some(Value::Unit);
        self.trace.push(TraceEvent::Suspend {
            task: cur,
            reason: SuspendReason::Yield,
        });
        Flow::Yield
    }
}

/// Returns the continuations of the clause frames in `frames`.
fn clause_conts(frames: &[Frame]) -> Vec<ContId> {
    frames
        .iter()
        .filter_map(|f| match f {
            Frame::Clause { cont } => Some(*cont),
            _ => None,
        })
        .collect()
}

/// Returns `v` with each continuation of `kmap` replaced by its copy.
fn remap_conts(v: Value, kmap: &BTreeMap<ContId, ContId>) -> Value {
    if kmap.is_empty() {
        return v;
    }
    match v {
        Value::Cont(k) => Value::Cont(kmap.get(&k).copied().unwrap_or(k)),
        Value::Tuple(vs) => Value::Tuple(vs.into_iter().map(|x| remap_conts(x, kmap)).collect()),
        Value::List(vs) => Value::List(vs.into_iter().map(|x| remap_conts(x, kmap)).collect()),
        Value::Struct(mut o) => {
            let fields = std::mem::take(&mut o.fields);
            o.fields = fields.into_iter().map(|x| remap_conts(x, kmap)).collect();
            Value::Struct(o)
        }
        Value::Enum(mut e) => {
            let fields = std::mem::take(&mut e.fields);
            e.fields = fields.into_iter().map(|x| remap_conts(x, kmap)).collect();
            Value::Enum(e)
        }
        other => other,
    }
}

/// Puts each closure in the copy value `v` that owns cells into `out`. A
/// copy value stays in its cell at the end of its scope, so the unwinder
/// looks into it for these closures.
fn owning_closures(v: &Value, out: &mut Vec<Value>) {
    let mut work = vec![v];
    while let Some(v) = work.pop() {
        match v {
            Value::Closure(c) if !c.owned.is_empty() => out.push(Value::Closure(Rc::clone(c))),
            Value::Tuple(vs) => work.extend(vs.iter()),
            Value::Struct(o) => work.extend(o.fields.iter()),
            Value::Enum(e) => work.extend(e.fields.iter()),
            _ => {}
        }
    }
}
