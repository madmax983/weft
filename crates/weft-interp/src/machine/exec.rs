//! Instruction execution.

use std::rc::Rc;

use weft_sema::program::FnId;
use weft_sema::types::{IntTy, Ty};
use weft_syntax::ast::Span;
use weft_verified::lifecycle::LinState;

use super::{CodeFrame, Flow, Frame, HandleMark, LinRec, ScopeRec, TaskResult, Wait, R};
use crate::code::{CPat, LitPat, Op, VarRef};
use crate::error::{ErrorKind, RuntimeError};
use crate::heap::SlotKind;
use crate::runtime::Native;
use crate::trace::{SuspendReason, TraceEvent};
use crate::value::{Cap, CellId, ClosureVal, EnumVal, HEnv, IterState, Obj, Place, ScopeId, Value};
use weft_verified::lifecycle::Linear;

/// Returns true for values that `for` and `match` bind by value.
const fn is_scalar(v: &Value) -> bool {
    matches!(
        v,
        Value::Int(_) | Value::Bool(_) | Value::Unit | Value::Str(_) | Value::Dur(_)
    )
}

fn u32_of(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}

impl super::Machine<'_, '_> {
    // -----------------------------------------------------------------------
    // Frame access
    // -----------------------------------------------------------------------

    pub(crate) fn fr(&mut self) -> R<&mut CodeFrame> {
        let cur = self.cur;
        match self.tasks[cur].frames.last_mut() {
            Some(Frame::Code(cf)) => Ok(cf),
            _ => Err(RuntimeError::new(
                ErrorKind::Fault,
                "internal: no code frame on top",
                None,
            )),
        }
    }

    pub(crate) fn push(&mut self, v: Value) -> R<()> {
        self.fr()?.stack.push(v);
        Ok(())
    }

    pub(crate) fn pop(&mut self) -> R<Value> {
        match self.fr()?.stack.pop() {
            Some(v) => Ok(v),
            None => Err(self.fault("internal: the operand stack is empty")),
        }
    }

    pub(crate) fn pop_n(&mut self, n: usize) -> R<Vec<Value>> {
        let fr = self.fr()?;
        if fr.stack.len() < n {
            return Err(self.fault("internal: the operand stack is too short"));
        }
        let at = fr.stack.len() - n;
        Ok(fr.stack.split_off(at))
    }

    pub(crate) fn pop_loc(&mut self) -> R<(Place, bool)> {
        match self.pop()? {
            Value::Loc(p, t) => Ok((p, t)),
            Value::Ref(p) => {
                self.heap.check_ref(&p);
                Ok((p, true))
            }
            v => {
                // A value where a place is needed: keep it in a temporary.
                let c = self.heap.alloc(SlotKind::Temp, v);
                self.fr()?.temps.push(c);
                Ok((Place::root(c), false))
            }
        }
    }

    fn cell_of(&mut self, v: VarRef) -> R<CellId> {
        let fr = self.fr()?;
        let c = match v {
            VarRef::Local(s) => fr.slots.get(s as usize).copied().flatten(),
            VarRef::Cap(i) => fr.caps.get(i as usize).copied(),
        };
        c.ok_or_else(|| self.fault("a variable is used before it has a value"))
    }

    fn set_pc(&mut self, pc: usize) -> R<()> {
        self.fr()?.pc = pc;
        Ok(())
    }

    /// Moves the current frame back to the instruction that is running, so it
    /// runs again when the task wakes.
    pub(crate) fn retry(&mut self) -> R<()> {
        let fr = self.fr()?;
        fr.pc = fr.pc.saturating_sub(1);
        Ok(())
    }

    pub(crate) fn hget(&self, p: &Place) -> R<&Value> {
        self.heap.get(p).map_err(|e| self.fault(e))
    }

    pub(crate) fn hget_mut(&mut self, p: &Place) -> R<&mut Value> {
        match self.heap.get_mut(p) {
            Ok(v) => Ok(v),
            Err(e) => Err(RuntimeError::new(ErrorKind::Fault, e, None)),
        }
    }

    /// Follows references, boxes and `Rc` handles to the place of a value.
    pub(crate) fn resolve(&self, p: Place, through: bool) -> R<(Place, bool)> {
        let (mut p, mut tr) = (p, through);
        for _ in 0..256 {
            match self.hget(&p)? {
                Value::Ref(q) => {
                    self.heap.log_read(&p);
                    self.heap.check_ref(q);
                    p = q.clone();
                    tr = true;
                }
                Value::Boxed(c) => {
                    self.heap.log_read(&p);
                    p = Place::root(*c);
                }
                Value::Rc(c) => {
                    self.heap.log_read(&p);
                    p = Place::root(*c);
                    tr = true;
                }
                _ => return Ok((p, tr)),
            }
        }
        Err(self.fault("a reference chain is too long"))
    }

    /// Follows references only.
    pub(crate) fn follow_refs(&self, p: Place) -> R<Place> {
        let mut p = p;
        for _ in 0..256 {
            match self.hget(&p)? {
                Value::Ref(q) => {
                    self.heap.check_ref(q);
                    p = q.clone();
                }
                _ => return Ok(p),
            }
        }
        Err(self.fault("a reference chain is too long"))
    }

    /// Reads through references. Each read is a read for the race detector of
    /// the oracle: an operand and a callee read through a reference here.
    pub(crate) fn deref_value(&self, v: Value) -> R<Value> {
        let mut v = v;
        for _ in 0..256 {
            match v {
                Value::Ref(p) => {
                    self.heap.check_ref(&p);
                    self.heap.log_read(&p);
                    v = self.hget(&p)?.clone();
                }
                Value::Loc(p, _) => {
                    self.heap.log_read(&p);
                    v = self.hget(&p)?.clone();
                }
                other => return Ok(other),
            }
        }
        Err(self.fault("a reference chain is too long"))
    }

    /// Copies a copy value at a place, or moves any other value out of it.
    pub(crate) fn use_place(&mut self, p: &Place) -> R<Value> {
        self.heap.log_read(p);
        let v = self.hget(p)?;
        if matches!(v, Value::Moved) {
            return Err(self.fault("a value is used after it was moved"));
        }
        if self.heap.is_copy(v) {
            Ok(v.clone())
        } else {
            let p = p.clone();
            self.heap.take(&p).map_err(|e| self.fault(e))
        }
    }

    pub(crate) fn end_cells(&mut self, cells: Vec<CellId>) {
        for c in cells {
            self.heap.end_cell(c);
        }
    }

    /// Drops everything that a finished code frame holds.
    pub(crate) fn cleanup_frame(&mut self, cf: CodeFrame) {
        for v in cf.stack {
            self.heap.drop_value(v);
        }
        self.end_cells(cf.temps);
        let slots: Vec<CellId> = cf.slots.into_iter().flatten().collect();
        self.end_cells(slots);
    }

    // -----------------------------------------------------------------------
    // Stepping
    // -----------------------------------------------------------------------

    /// Runs one step of the current task.
    pub(crate) fn step(&mut self) -> R<Flow> {
        let cur = self.cur;
        let (code, pc) = match self.tasks[cur].frames.last_mut() {
            None => return Ok(Flow::Done),
            Some(Frame::Code(cf)) => {
                let pc = cf.pc;
                cf.pc += 1;
                (Rc::clone(&cf.code), pc)
            }
            Some(Frame::Unwind(_)) => return self.unwind_step(),
            Some(Frame::Fork { .. }) => return self.fork_step(),
            Some(_) => return Err(self.fault("internal: a mark frame is on top")),
        };
        let Some(op) = code.ops.get(pc) else {
            return Err(self.fault("internal: the code has no instruction here"));
        };
        self.exec(op)
    }

    #[allow(clippy::too_many_lines)]
    fn exec(&mut self, op: &Op) -> R<Flow> {
        match op {
            Op::Unit => self.push(Value::Unit)?,
            Op::Int(i) => self.push(Value::Int(*i))?,
            Op::Bool(b) => self.push(Value::Bool(*b))?,
            Op::Str(s) => self.push(Value::Str(Rc::clone(s)))?,
            Op::Dur(d) => self.push(Value::Dur(*d))?,
            Op::Var(v) => {
                let c = self.cell_of(*v)?;
                self.push(Value::Loc(Place::root(c), false))?;
            }
            Op::Bind(s) => {
                let v = self.pop()?;
                self.bind_slot(*s, v)?;
            }
            Op::BindEmpty(s) => self.bind_slot(*s, Value::Moved)?,
            Op::DropSlots(slots) => {
                let fr = self.fr()?;
                let mut cells = Vec::new();
                for &s in slots {
                    if let Some(c) = fr.slots.get_mut(s as usize).and_then(Option::take) {
                        cells.push(c);
                    }
                }
                self.end_cells(cells);
            }
            Op::Field(name) => {
                let (p, tr) = self.pop_loc()?;
                let (p, tr) = self.resolve(p, tr)?;
                let idx = match self.hget(&p)? {
                    Value::Struct(o) => self.rt.adts[o.adt.index()]
                        .fields
                        .iter()
                        .position(|f| f == name),
                    Value::Tuple(vs) => name.parse::<usize>().ok().filter(|&i| i < vs.len()),
                    Value::Moved => return Err(self.fault("a value is used after it was moved")),
                    _ => None,
                };
                let Some(i) = idx else {
                    return Err(self.fault(format!("this value has no field `{name}`")));
                };
                self.push(Value::Loc(p.child(u32_of(i)), tr))?;
            }
            Op::Index => {
                let i = self.pop()?;
                let i = self.int_of(i)?;
                let (p, tr) = self.pop_loc()?;
                let (p, tr) = self.resolve(p, tr)?;
                let (buf, lo, hi, tr) = self.elems_of(&p, tr)?;
                let i = u32::try_from(i)
                    .ok()
                    .filter(|&i| lo.saturating_add(i) < hi)
                    .ok_or_else(|| {
                        self.fault(format!("index {i} is out of bounds (length {})", hi - lo))
                    })?;
                self.push(Value::Loc(Place::root(buf).child(lo + i), tr))?;
            }
            Op::ToTemp => {
                let v = self.pop()?;
                let c = self.heap.alloc(SlotKind::Temp, v);
                self.fr()?.temps.push(c);
                self.push(Value::Loc(Place::root(c), false))?;
            }
            Op::Read => {
                let (p, _) = self.pop_loc()?;
                let v = self.use_place(&p)?;
                self.push(v)?;
            }
            Op::Borrow => {
                let (p, _) = self.pop_loc()?;
                self.push(Value::Ref(p))?;
            }
            Op::BorrowAll => {
                let (p, tr) = self.pop_loc()?;
                let (p, tr) = self.resolve(p, tr)?;
                let (buf, lo, hi, _) = self.elems_of(&p, tr)?;
                self.push(Value::Slice { buf, lo, hi })?;
            }
            Op::Store => {
                let (p, _) = self.pop_loc()?;
                let v = self.pop()?;
                self.check_unsigned(&p, &v)?;
                let old = std::mem::replace(self.hget_mut(&p)?, v);
                self.heap.drop_value(old);
            }
            Op::CompoundStore(op, int) => {
                let (p, _) = self.pop_loc()?;
                let v = self.pop()?;
                let p = self.follow_refs(p)?;
                let cur = self.hget(&p)?.clone();
                let new = self.binop(*op, cur, v)?;
                // The check of a field names the field, so it comes first.
                self.check_unsigned(&p, &new)?;
                if let Some(it) = int {
                    self.check_int(*it, &new)?;
                }
                *self.hget_mut(&p)? = new;
            }
            Op::Pop => {
                let v = self.pop()?;
                self.heap.drop_value(v);
            }
            Op::Nip => {
                let top = self.pop()?;
                let under = self.pop()?;
                self.heap.drop_value(under);
                self.push(top)?;
            }
            Op::Bin(op) => {
                let b = self.pop()?;
                let a = self.pop()?;
                let v = self.binop(*op, a, b)?;
                self.push(v)?;
            }
            Op::Neg => {
                let v = self.pop()?;
                let v = match self.deref_value(v)? {
                    Value::Int(i) => Value::Int(
                        i.checked_neg()
                            .ok_or_else(|| self.fault("integer overflow"))?,
                    ),
                    _ => return Err(self.fault("`-` needs an integer")),
                };
                self.push(v)?;
            }
            Op::CheckInt(it) => {
                let v = self.pop()?;
                self.check_int(*it, &v)?;
                self.push(v)?;
            }
            Op::Not => {
                let v = self.pop()?;
                let b = self.bool_of(v)?;
                self.push(Value::Bool(!b))?;
            }
            Op::Jump(t) => self.set_pc(*t)?,
            Op::JumpIfFalse(t) => {
                let v = self.pop()?;
                if !self.bool_of(v)? {
                    self.set_pc(*t)?;
                }
            }
            Op::JumpIfTrue(t) => {
                let v = self.pop()?;
                if self.bool_of(v)? {
                    self.set_pc(*t)?;
                }
            }
            Op::BackEdge => {
                if self.quantum_expired() {
                    return Ok(Flow::Preempt);
                }
            }
            Op::LoopEnter => {
                let fr = self.fr()?;
                let h = (fr.stack.len(), fr.marks.len());
                fr.loops.push(h);
            }
            Op::LoopExit => {
                self.fr()?.loops.pop();
            }
            Op::Break(t) => {
                let fr = self.fr()?;
                let (sl, ml) = fr.loops.last().copied().unwrap_or((0, 0));
                let vals: Vec<Value> = fr.stack.drain(sl.min(fr.stack.len())..).collect();
                let mut cells = Vec::new();
                while fr.marks.len() > ml {
                    let m = fr.marks.pop().unwrap_or(0).min(fr.temps.len());
                    cells.extend(fr.temps.drain(m..));
                }
                fr.pc = *t;
                for v in vals {
                    self.heap.drop_value(v);
                }
                self.end_cells(cells);
            }
            Op::StmtBegin => {
                let fr = self.fr()?;
                let n = fr.temps.len();
                fr.marks.push(n);
            }
            Op::StmtEnd => {
                let fr = self.fr()?;
                let m = fr.marks.pop().unwrap_or(fr.temps.len()).min(fr.temps.len());
                let cells: Vec<CellId> = fr.temps.drain(m..).collect();
                self.end_cells(cells);
            }
            Op::Return => {
                let v = self.pop()?;
                let cur = self.cur;
                if let Some(Frame::Code(cf)) = self.tasks[cur].frames.pop() {
                    self.cleanup_frame(cf);
                }
                return self.deliver(v);
            }
            Op::Tuple(n) => {
                let vs = self.pop_n(*n as usize)?;
                self.push(Value::Tuple(vs))?;
            }
            Op::MakeVec(n) => {
                let vs = self.pop_n(*n as usize)?;
                let buf = self.heap.alloc(SlotKind::Buf, Value::List(vs));
                self.push(Value::Vec(buf))?;
            }
            Op::MakeStruct { adt, fields, total } => {
                let vs = self.pop_n(fields.len())?;
                let mut fs = vec![Value::Moved; *total as usize];
                for (&i, v) in fields.iter().zip(vs) {
                    if let Some(slot) = fs.get_mut(i as usize) {
                        *slot = v;
                    }
                }
                let lin = match self.rt.adts.get(adt.index()) {
                    Some(a) if a.linear => {
                        self.lins.push(LinRec {
                            l: Linear::new(a.on_abort.is_some()),
                        });
                        Some(self.lins.len() - 1)
                    }
                    _ => None,
                };
                self.push(Value::Struct(Box::new(Obj {
                    adt: *adt,
                    fields: fs,
                    lin,
                })))?;
            }
            Op::MakeEnum { adt, variant, n } => {
                let vs = self.pop_n(*n as usize)?;
                self.push(Value::Enum(Box::new(EnumVal {
                    adt: *adt,
                    variant: *variant,
                    fields: vs,
                })))?;
            }
            Op::Untuple(n) => self.untuple(*n as usize)?,
            Op::Unstruct(n) => self.unstruct(*n as usize)?,
            Op::Concat(n) => {
                let vs = self.pop_n(*n as usize)?;
                let mut s = String::new();
                for v in &vs {
                    s.push_str(&self.show(v));
                }
                self.push(Value::str(&s))?;
            }
            Op::ToStr => {
                let v = self.pop()?;
                let s = self.show(&v);
                self.heap.drop_value(v);
                self.push(Value::str(&s))?;
            }
            Op::Match { pat, fail } => {
                let (p, tr) = match self.fr()?.stack.last() {
                    Some(Value::Loc(p, tr)) => (p.clone(), *tr),
                    _ => return Err(self.fault("internal: `match` needs a place")),
                };
                if self.pat_test(pat, &p)? {
                    self.pat_bind(pat, &p, tr)?;
                } else {
                    self.set_pc(*fail)?;
                }
            }
            Op::Call { f, n } => {
                let args = self.pop_n(*n as usize)?;
                let henv = self.fr()?.henv.clone();
                return self.call_fn(*f, args, henv);
            }
            Op::CallValue(n) => {
                let args = self.pop_n(*n as usize)?;
                let callee = self.pop()?;
                return self.call_value(callee, args);
            }
            Op::CallMethod { name, n, arg_span } => {
                return self.call_method(name, *n as usize, *arg_span);
            }
            Op::Perform { effect, op, n } => {
                let args = self.pop_n(*n as usize)?;
                let henv = self.fr()?.henv.clone();
                return self.perform(*effect, *op, args, &henv);
            }
            Op::MakeClosure {
                code,
                caps,
                owned,
                span,
            } => {
                let mut cells = Vec::new();
                let mut own = Vec::new();
                for (i, c) in caps.iter().enumerate() {
                    let cell = self.cell_of(*c)?;
                    if owned.contains(&u32_of(i)) {
                        // A capture that the closure moves: the closure takes the
                        // value now, into a cell of its own.
                        let p = Place::root(cell);
                        if matches!(self.hget(&p)?, Value::Moved) {
                            return Err(self.fault("a value is used after it was moved"));
                        }
                        let v = self.heap.take(&p).map_err(|e| self.fault(e))?;
                        let cell = self.heap.alloc(SlotKind::Local, v);
                        cells.push(cell);
                        own.push(cell);
                    } else {
                        cells.push(cell);
                    }
                }
                let henv = self.fr()?.henv.clone();
                self.push(Value::Closure(Rc::new(ClosureVal {
                    code: *code,
                    cells,
                    owned: own,
                    henv,
                    span: *span,
                })))?;
            }
            Op::FnValue(f) => self.push(Value::FnItem(*f))?,
            Op::Handle(spec) => {
                let henv = self.fr()?.henv.clone();
                let id = self.fresh_id();
                let mut clauses = Vec::new();
                for c in &spec.clauses {
                    let mut cells = Vec::new();
                    for v in &c.caps {
                        cells.push(self.cell_of(*v)?);
                    }
                    clauses.push((c.op, c.code, Rc::from(cells)));
                }
                let mut cells = Vec::new();
                for v in &spec.body_caps {
                    cells.push(self.cell_of(*v)?);
                }
                let inner = henv.with(spec.effect, id);
                self.task().frames.push(Frame::Handle(HandleMark {
                    id,
                    clauses: Rc::from(clauses),
                    outer: henv,
                }));
                let f = self.code_frame(spec.body, Vec::new(), Rc::from(cells), inner)?;
                self.task().frames.push(Frame::Code(f));
            }
            Op::Scope { code, caps } => {
                let henv = self.fr()?.henv.clone();
                let sid = self.new_scope(henv.clone());
                let mut cells = Vec::new();
                for v in caps {
                    cells.push(self.cell_of(*v)?);
                }
                self.task().frames.push(Frame::Scope { scope: sid });
                let f = self.code_frame(*code, vec![Value::Scope(sid)], Rc::from(cells), henv)?;
                self.task().frames.push(Frame::Code(f));
            }
            Op::ScopeWait(s) => return self.scope_wait(*s),
            Op::Fork { n, spans } => return self.fork(*n as usize, spans),
            Op::Print(n) => {
                let vs = self.pop_n(*n as usize)?;
                let parts: Vec<String> = vs.iter().map(|v| self.show(v)).collect();
                self.out_line(&parts.join(" "));
                for v in vs {
                    self.heap.drop_value(v);
                }
                self.push(Value::Unit)?;
            }
            Op::Assert => {
                let v = self.pop()?;
                if !self.bool_of(v)? {
                    let span = self.span_now();
                    return Ok(self.abort_task(TaskResult::Failed {
                        msg: "the condition is false".into(),
                        kind: ErrorKind::Assertion,
                        span,
                    }));
                }
            }
            Op::RangeIter => {
                let hi = self.pop()?;
                let lo = self.pop()?;
                let (lo, hi) = (self.int_of(lo)?, self.int_of(hi)?);
                self.push(Value::Iter(Box::new(IterState::Range {
                    next: lo,
                    end: hi,
                })))?;
            }
            Op::ElemIter => {
                let (p, tr) = self.pop_loc()?;
                let (p, tr) = self.resolve(p, tr)?;
                let (buf, lo, hi, _) = self.elems_of(&p, tr)?;
                self.push(Value::Iter(Box::new(IterState::Elems {
                    buf,
                    next: lo,
                    end: hi,
                })))?;
            }
            Op::IterNext { slot, exit } => {
                let c = self.cell_of(VarRef::Local(*slot))?;
                let p = Place::root(c);
                let state = match self.hget(&p)? {
                    Value::Iter(it) => (**it).clone(),
                    _ => return Err(self.fault("internal: no iterator")),
                };
                let (item, next) = match state {
                    IterState::Range { next, end } => {
                        if next < end {
                            (
                                Some(Value::Int(next)),
                                IterState::Range {
                                    next: next + 1,
                                    end,
                                },
                            )
                        } else {
                            (None, IterState::Range { next, end })
                        }
                    }
                    IterState::Elems { buf, next, end } => {
                        // The oracle checks report an iteration over a freed
                        // buffer. The stock machine ends the loop.
                        let len = match self.heap.list(buf) {
                            Ok(l) => u32_of(l.len()),
                            Err(e) if self.heap.oracle().is_some() => {
                                return Err(self.fault(e));
                            }
                            Err(_) => 0,
                        };
                        if next < end.min(len) {
                            let ep = Place::root(buf).child(next);
                            self.heap.log_read(&ep);
                            let v = self.hget(&ep)?;
                            let item = if is_scalar(v) {
                                v.clone()
                            } else {
                                Value::Ref(ep)
                            };
                            (
                                Some(item),
                                IterState::Elems {
                                    buf,
                                    next: next + 1,
                                    end,
                                },
                            )
                        } else {
                            (None, IterState::Elems { buf, next, end })
                        }
                    }
                };
                *self.hget_mut(&p)? = Value::Iter(Box::new(next));
                match item {
                    Some(v) => self.push(v)?,
                    None => self.set_pc(*exit)?,
                }
            }
            Op::Fault(msg) => return Err(self.fault(msg.to_string())),
        }
        Ok(Flow::Continue)
    }

    pub(crate) fn span_now(&self) -> Option<Span> {
        let t = self.tasks.get(self.cur)?;
        t.frames.iter().rev().find_map(|f| match f {
            Frame::Code(cf) => cf.code.spans.get(cf.pc.saturating_sub(1)).copied(),
            _ => None,
        })
    }

    /// Faults if integer `v` does not fit in type `it`. A `u64` or a `usize`
    /// holds at most `i64::MAX` here: a larger value faults as an overflow of
    /// the arithmetic before.
    fn check_int(&self, it: IntTy, v: &Value) -> R<()> {
        let Value::Int(i) = v else {
            return Ok(());
        };
        let (min, max) = it.range();
        let i = i128::from(*i);
        if i < min {
            return Err(self.fault(format!(
                "integer underflow: {i} does not fit in `{}`",
                it.name()
            )));
        }
        if i > max {
            return Err(self.fault(format!(
                "integer overflow: {i} does not fit in `{}`",
                it.name()
            )));
        }
        Ok(())
    }

    /// An unsigned struct field cannot hold a negative integer.
    fn check_unsigned(&self, p: &Place, v: &Value) -> R<()> {
        let Value::Int(i) = v else {
            return Ok(());
        };
        let Some((&last, parent)) = p.path.split_last() else {
            return Ok(());
        };
        if *i >= 0 {
            return Ok(());
        }
        let parent = Place {
            cell: p.cell,
            path: parent.to_vec(),
        };
        if let Ok(Value::Struct(o)) = self.heap.get(&parent) {
            let info = &self.rt.adts[o.adt.index()];
            if info.unsigned.get(last as usize).copied().unwrap_or(false) {
                let name = info.fields.get(last as usize).map_or("", |n| &**n);
                return Err(self.fault(format!("unsigned underflow: field `{name}` would be {i}")));
            }
        }
        Ok(())
    }

    fn bind_slot(&mut self, s: u32, v: Value) -> R<()> {
        let c = self.heap.alloc(SlotKind::Local, v);
        let fr = self.fr()?;
        let old = fr.slots.get_mut(s as usize).and_then(|x| x.replace(c));
        if let Some(old) = old {
            self.heap.end_cell(old);
        }
        Ok(())
    }

    /// Returns the buffer and the index range of a `Vec` or a slice at a place.
    fn elems_of(&self, p: &Place, tr: bool) -> R<(CellId, u32, u32, bool)> {
        self.heap.log_read(p);
        match self.hget(p)? {
            Value::Vec(buf) => {
                let len = self.heap.list(*buf).map_err(|e| self.fault(e))?.len();
                Ok((*buf, 0, u32_of(len), tr))
            }
            Value::Slice { buf, lo, hi } => Ok((*buf, *lo, *hi, true)),
            Value::Moved => Err(self.fault("a value is used after it was moved")),
            _ => Err(self.fault("this value has no elements")),
        }
    }

    pub(crate) fn int_of(&self, v: Value) -> R<i64> {
        match self.deref_value(v)? {
            Value::Int(i) => Ok(i),
            _ => Err(self.fault("an integer is needed here")),
        }
    }

    pub(crate) fn bool_of(&self, v: Value) -> R<bool> {
        match self.deref_value(v)? {
            Value::Bool(b) => Ok(b),
            _ => Err(self.fault("a boolean is needed here")),
        }
    }

    fn untuple(&mut self, n: usize) -> R<()> {
        let v = self.pop()?;
        match v {
            Value::Tuple(vs) if vs.len() == n => {
                for v in vs.into_iter().rev() {
                    self.push(v)?;
                }
            }
            Value::Ref(p) | Value::Loc(p, _) => {
                self.heap.check_ref(&p);
                let (p, _) = self.resolve(p, true)?;
                let len = match self.hget(&p)? {
                    Value::Tuple(vs) => vs.len(),
                    _ => return Err(self.fault("this value is not a tuple")),
                };
                if len != n {
                    return Err(self.fault("this tuple has another size"));
                }
                for i in (0..n).rev() {
                    let q = p.child(u32_of(i));
                    let x = self.hget(&q)?;
                    // A scalar part behind the reference is copied: a read.
                    let item = if is_scalar(x) {
                        let x = x.clone();
                        self.heap.log_read(&q);
                        x
                    } else {
                        Value::Ref(q)
                    };
                    self.push(item)?;
                }
            }
            _ => return Err(self.fault("this value is not a tuple of that size")),
        }
        Ok(())
    }

    fn unstruct(&mut self, n: usize) -> R<()> {
        let v = self.pop()?;
        match v {
            Value::Struct(o) if o.fields.len() == n => {
                if let Some(id) = o.lin {
                    self.consume_lin(id)?;
                }
                for f in o.fields.into_iter().rev() {
                    self.push(f)?;
                }
            }
            Value::Ref(p) | Value::Loc(p, _) => {
                self.heap.check_ref(&p);
                let (p, _) = self.resolve(p, true)?;
                if !matches!(self.hget(&p)?, Value::Struct(o) if o.fields.len() == n) {
                    return Err(self.fault("this value is not a struct of that size"));
                }
                for i in (0..n).rev() {
                    let q = p.child(u32_of(i));
                    let x = self.hget(&q)?;
                    // A scalar part behind the reference is copied: a read.
                    let item = if is_scalar(x) {
                        let x = x.clone();
                        self.heap.log_read(&q);
                        x
                    } else {
                        Value::Ref(q)
                    };
                    self.push(item)?;
                }
            }
            Value::Moved => return Err(self.fault("a value is used after it was moved")),
            _ => return Err(self.fault("this value is not a struct of that size")),
        }
        Ok(())
    }

    /// Consumes a linear value on the normal path. A value that is already
    /// finished is a fault: the verified record refuses the consume.
    pub(crate) fn consume_lin(&mut self, id: usize) -> R<()> {
        let Some(rec) = self.lins.get_mut(id) else {
            return Err(self.fault("internal: bad linear record"));
        };
        if rec.l.consume().is_ok() {
            return Ok(());
        }
        let aborted = rec.l.state == LinState::Aborted;
        Err(self.fault(if aborted {
            "a linear value was consumed after `on abort` finished it"
        } else {
            "a linear value was consumed twice"
        }))
    }

    // -----------------------------------------------------------------------
    // Patterns
    // -----------------------------------------------------------------------

    fn pat_test(&self, pat: &CPat, p: &Place) -> R<bool> {
        Ok(match pat {
            CPat::Wild | CPat::Bind(_) => true,
            CPat::Lit(l) => {
                let (p, _) = self.resolve(p.clone(), false)?;
                self.heap.log_read(&p);
                match (l, self.hget(&p)?) {
                    (LitPat::Int(a), Value::Int(b)) => a == b,
                    (LitPat::Bool(a), Value::Bool(b)) => a == b,
                    (LitPat::Str(a), Value::Str(b)) => a == b,
                    (LitPat::Unit, Value::Unit) => true,
                    _ => false,
                }
            }
            CPat::Tuple(ps) => {
                let (p, _) = self.resolve(p.clone(), false)?;
                match self.hget(&p)? {
                    Value::Tuple(vs) if vs.len() == ps.len() => {
                        for (i, q) in ps.iter().enumerate() {
                            if !self.pat_test(q, &p.child(u32_of(i)))? {
                                return Ok(false);
                            }
                        }
                        true
                    }
                    _ => false,
                }
            }
            CPat::Variant { name, fields } => {
                let (p, _) = self.resolve(p.clone(), false)?;
                self.heap.log_read(&p);
                let ok = match self.hget(&p)? {
                    Value::Enum(e) => {
                        self.rt.adts[e.adt.index()]
                            .variants
                            .get(e.variant as usize)
                            .is_some_and(|(n, _)| n == name)
                            && e.fields.len() == fields.len()
                    }
                    Value::Struct(o) => {
                        self.rt.adts[o.adt.index()].name == *name && o.fields.len() == fields.len()
                    }
                    _ => false,
                };
                if !ok {
                    return Ok(false);
                }
                for (i, q) in fields.iter().enumerate() {
                    if !self.pat_test(q, &p.child(u32_of(i)))? {
                        return Ok(false);
                    }
                }
                true
            }
        })
    }

    fn pat_bind(&mut self, pat: &CPat, p: &Place, tr: bool) -> R<()> {
        match pat {
            CPat::Wild | CPat::Lit(_) => {}
            CPat::Bind(s) => {
                let v = if tr {
                    let x = self.hget(p)?;
                    if is_scalar(x) {
                        // A part behind a reference is copied: a read.
                        self.heap.log_read(p);
                        x.clone()
                    } else {
                        Value::Ref(p.clone())
                    }
                } else {
                    self.use_place(p)?
                };
                self.bind_slot(*s, v)?;
            }
            CPat::Tuple(ps) | CPat::Variant { fields: ps, .. } => {
                let (q, tr) = self.resolve(p.clone(), tr)?;
                if let Some(id) = match self.hget(&q)? {
                    Value::Struct(o) if !tr => o.lin,
                    _ => None,
                } {
                    self.consume_lin(id)?;
                }
                for (i, x) in ps.iter().enumerate() {
                    self.pat_bind(x, &q.child(u32_of(i)), tr)?;
                }
            }
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Calls
    // -----------------------------------------------------------------------

    /// Calls a function item. `henv` holds the caller's handlers.
    pub(crate) fn call_fn(&mut self, f: FnId, args: Vec<Value>, henv: HEnv) -> R<Flow> {
        let mut args = args;
        if let Some(n) = self.rt.natives.get(f.index()).copied().flatten() {
            return self.native(n, f, args, henv);
        }
        self.coerce_args(f, &mut args)?;
        let Some(code) = self.rt.compiled.fn_code.get(f.index()).copied().flatten() else {
            return Err(self.fault(format!("`{}` has no body", self.rt.prog.fns[f].path)));
        };
        let frame = self.code_frame(code, args, Rc::from(Vec::new()), henv)?;
        self.task().frames.push(Frame::Code(frame));
        Ok(Flow::Continue)
    }

    /// A reference to a copy value, passed to a parameter that is not a
    /// reference, passes the value.
    fn coerce_args(&self, f: FnId, args: &mut [Value]) -> R<()> {
        let Some(sig) = self.rt.sigs.get(f.index()) else {
            return Ok(());
        };
        for (p, a) in sig.params.iter().zip(args.iter_mut()) {
            if let (true, Value::Int(i)) = (crate::runtime::is_unsigned(&p.ty), &*a) {
                if *i < 0 {
                    return Err(self.fault(format!(
                        "unsigned underflow: parameter `{}` would be {i}",
                        p.name
                    )));
                }
            }
            if p.ty.is_ref() || matches!(p.ty, Ty::Param(_) | Ty::Fn(_) | Ty::Error) {
                continue;
            }
            if let Value::Ref(q) = a {
                let v = self.deref_value(Value::Ref(q.clone()))?;
                if self.heap.is_copy(&v) {
                    *a = v;
                }
            }
        }
        Ok(())
    }

    /// Calls a closure, a function item or a continuation.
    ///
    /// A closure that moved its captures runs only once (W0502), so the call
    /// consumes it: the frame takes the captures (`take_captures`). The
    /// unwinder of the frame finishes their linear values, also when no local
    /// holds the closure, as for the block of a `with_timeout` (ADR 0010).
    pub(crate) fn call_value(&mut self, callee: Value, args: Vec<Value>) -> R<Flow> {
        match callee {
            Value::Closure(c) => {
                let (caps, owned) = self.take_captures(&c);
                let mut f = self.code_frame(c.code, args, caps, c.henv.clone())?;
                f.owned = owned;
                self.task().frames.push(Frame::Code(f));
                Ok(Flow::Continue)
            }
            Value::FnItem(f) => {
                let henv = self.top_henv();
                self.call_fn(f, args, henv)
            }
            Value::Cont(k) => self.resume(k, args),
            Value::Ref(_) | Value::Loc(..) => {
                let v = self.deref_value(callee)?;
                self.call_value(v, args)
            }
            Value::Moved => Err(self.fault("a value is used after it was moved")),
            _ => Err(self.fault("this value cannot be called")),
        }
    }

    /// Returns the type whose methods a value has.
    fn owner_adt(&self, v: &Value) -> Option<weft_sema::AdtId> {
        let b = &self.rt.b;
        match v {
            Value::Struct(o) => Some(o.adt),
            Value::Enum(e) => Some(e.adt),
            Value::Vec(_) | Value::Slice { .. } | Value::List(_) => b.vec,
            Value::Str(_) => b.string,
            Value::Rc(_) => b.rc,
            Value::Weak(_) => b.weak,
            Value::Boxed(_) => b.boxed,
            Value::Task(_) => b.task,
            Value::Dur(_) => b.duration,
            Value::Cap(Cap::Fs) => b.fscap,
            Value::Cap(Cap::Net) => b.netcap,
            Value::Cap(Cap::Stdout) => b.stdout,
            Value::Cap(Cap::Listener(_)) => b.listener,
            Value::Request(_) => b.request,
            Value::Response(_) => b.response,
            _ => None,
        }
    }

    fn call_method(&mut self, name: &str, n: usize, arg_span: Span) -> R<Flow> {
        let mut args = self.pop_n(n)?;
        let (p0, tr0) = self.pop_loc()?;
        let mut p = p0.clone();
        let found = loop {
            let v = self.hget(&p)?;
            if let Value::Scope(sid) = v {
                if name == "spawn" {
                    let sid = *sid;
                    let f = args.pop().unwrap_or_default();
                    return self.spawn_into(sid, f, arg_span);
                }
            }
            if let Some(adt) = self.owner_adt(v) {
                if let Some(&f) = self.rt.prog.methods.get(&(adt, name.to_string())) {
                    break f;
                }
            }
            match v {
                Value::Ref(q) => {
                    self.heap.check_ref(q);
                    p = q.clone();
                }
                Value::Boxed(c) | Value::Rc(c) => p = Place::root(*c),
                Value::Moved => return Err(self.fault("a value is used after it was moved")),
                _ => return Err(self.fault(format!("this value has no method `{name}`"))),
            }
        };
        if self.rt.natives.get(found.index()).copied().flatten() == Some(Native::TaskJoin) {
            if let Value::Task(t) = self.hget(&p)? {
                let t = *t;
                if !self.is_done(t) {
                    self.push(Value::Loc(p0, tr0))?;
                    for a in args {
                        self.push(a)?;
                    }
                    self.retry()?;
                    if let Some(f) = self.check_interrupt() {
                        return Ok(f);
                    }
                    return Ok(self.block(Wait::Join(t), SuspendReason::Join(t)));
                }
            }
        }
        let by_ref = self
            .rt
            .sigs
            .get(found.index())
            .and_then(|s| s.params.first())
            .is_some_and(|p| p.ty.is_ref());
        let recv = if by_ref {
            Value::Ref(p)
        } else {
            self.use_place(&p)?
        };
        args.insert(0, recv);
        let henv = self.fr()?.henv.clone();
        self.call_fn(found, args, henv)
    }

    // -----------------------------------------------------------------------
    // Tasks and scopes
    // -----------------------------------------------------------------------

    /// Makes a scope whose owner is the current task. `henv` has the handlers
    /// at the `scope` or the `fork`: a failure of a child goes to them.
    pub(crate) fn new_scope(&mut self, henv: HEnv) -> ScopeId {
        let owner = self.cur;
        self.scopes.push(ScopeRec {
            owner,
            children: Vec::new(),
            failure: None,
            propagated: false,
            henv,
        });
        self.scopes.len() - 1
    }

    /// With the oracle checks on, notes a violation if task value `f`, which
    /// the checker marks stealable, reaches an `Rc`, a `Weak` or a `Scope`.
    /// Those stay on one thread. A reference reaches only the value at its
    /// place, not the other fields of its cell: `&w.score` is portable even if
    /// `w.rc` is an `Rc`. A slice reaches only its elements.
    fn oracle_portable(&self, f: &Value) {
        let Some(o) = self.heap.oracle() else {
            return;
        };
        let mut work: Vec<Value> = vec![f.clone()];
        let mut seen: std::collections::BTreeSet<Place> = std::collections::BTreeSet::new();
        let found = loop {
            let Some(v) = work.pop() else {
                break None;
            };
            let places: Vec<Place> = match v {
                Value::Rc(_) => break Some("Rc"),
                Value::Weak(_) => break Some("Weak"),
                Value::Scope(_) => break Some("Scope"),
                Value::Closure(c) => c.cells.iter().map(|&cell| Place::root(cell)).collect(),
                Value::Ref(p) | Value::Loc(p, _) => vec![p],
                Value::Vec(c) | Value::Boxed(c) => vec![Place::root(c)],
                Value::Slice { buf, lo, hi } => {
                    (lo..hi).map(|i| Place::root(buf).child(i)).collect()
                }
                Value::Tuple(vs) | Value::List(vs) => {
                    work.extend(vs);
                    Vec::new()
                }
                Value::Struct(o) => {
                    work.extend(o.fields);
                    Vec::new()
                }
                Value::Enum(e) => {
                    work.extend(e.fields);
                    Vec::new()
                }
                _ => Vec::new(),
            };
            for p in places {
                if let Some(v) = self.value_at(&p) {
                    if seen.insert(p) {
                        work.push(v.clone());
                    }
                }
            }
        };
        if let Some(what) = found {
            o.borrow_mut().flag(format!(
                "oracle: a stealable task reaches a nonportable value (`{what}`)"
            ));
        }
    }

    /// Returns the value at place `p`, or `None` if it does not exist. This is
    /// not an access of the program: the oracle does not log it.
    fn value_at(&self, p: &Place) -> Option<&Value> {
        let mut v = &self.heap.slot(p.cell).ok()?.val;
        for &i in &p.path {
            v = match v {
                Value::Tuple(vs) | Value::List(vs) => vs.get(i as usize),
                Value::Struct(o) => o.fields.get(i as usize),
                Value::Enum(e) => e.fields.get(i as usize),
                _ => None,
            }?;
        }
        Some(v)
    }

    /// Returns the captured cells of a frame that runs closure `c`, and the
    /// cells of them that the frame owns. The frame takes each capture that
    /// the closure moved into a new cell of its own. A copy of the closure
    /// that stays in a local then holds no value there, so no unwinder
    /// finishes a value twice (ADR 0010).
    fn take_captures(&mut self, c: &ClosureVal) -> (Rc<[CellId]>, Vec<CellId>) {
        if c.owned.is_empty() {
            return (Rc::from(c.cells.as_slice()), Vec::new());
        }
        let mut caps = c.cells.clone();
        let mut owned = Vec::new();
        for cap in &mut caps {
            if !c.owned.contains(cap) {
                continue;
            }
            let v = match self.heap.slot_mut(*cap) {
                Ok(s) => crate::heap::take_moved(&mut s.val),
                Err(_) => Value::Moved,
            };
            *cap = self.heap.alloc(SlotKind::Local, v);
            owned.push(*cap);
        }
        (Rc::from(caps), owned)
    }

    /// Makes the first frame of a task for a closure or a function item.
    ///
    /// The closure moves into the task. So the first frame takes the captures
    /// that the closure moved (`take_captures`): the unwinder of the task
    /// finishes their linear values, also when the task is cancelled before
    /// it starts (ADR 0010).
    fn task_frame(&mut self, f: Value) -> R<CodeFrame> {
        match f {
            Value::Closure(c) => {
                let (caps, owned) = self.take_captures(&c);
                let mut frame = self.code_frame(c.code, Vec::new(), caps, c.henv.clone())?;
                frame.owned = owned;
                Ok(frame)
            }
            Value::FnItem(f) => {
                let Some(code) = self.rt.compiled.fn_code.get(f.index()).copied().flatten() else {
                    return Err(self.fault("a task needs a function with a body"));
                };
                let henv = self.top_henv();
                self.code_frame(code, Vec::new(), Rc::from(Vec::new()), henv)
            }
            Value::Ref(_) | Value::Loc(..) => {
                let v = self.deref_value(f)?;
                self.task_frame(v)
            }
            _ => Err(self.fault("a task needs a closure")),
        }
    }

    /// Spawns a closure as a child of a scope.
    pub(crate) fn spawn_task(&mut self, sid: ScopeId, f: Value, span: Span) -> R<usize> {
        // The span is in the code that spawns the task.
        let unit = self.fr().map_or(usize::MAX, |cf| cf.code.unit);
        let stealable = self.rt.is_stealable(unit, span);
        if stealable {
            self.oracle_portable(&f);
        }
        let frame = self.task_frame(f)?;
        let parent = self.cur;
        // The task runs in the simulation of its spawn site.
        let sim = self.sim_of(parent);
        let t = self.add_task(frame, Some(parent), stealable, Some(sid), sim);
        if let Some(s) = self.scopes.get_mut(sid) {
            s.children.push(t);
        }
        let worker = self.queue_worker(t);
        self.trace.push(TraceEvent::Spawn {
            task: t,
            parent,
            worker,
            stealable,
        });
        Ok(t)
    }

    fn spawn_into(&mut self, sid: ScopeId, f: Value, span: Span) -> R<Flow> {
        let t = self.spawn_task(sid, f, span)?;
        self.push(Value::Task(t))?;
        Ok(Flow::Continue)
    }

    fn scope_wait(&mut self, slot: u32) -> R<Flow> {
        let c = self.cell_of(VarRef::Local(slot))?;
        let Value::Scope(sid) = *self.hget(&Place::root(c))? else {
            return Err(self.fault("internal: no scope"));
        };
        let done = self
            .scopes
            .get(sid)
            .is_none_or(|s| s.children.iter().all(|&t| self.is_done(t)));
        if !done {
            self.retry()?;
            if let Some(f) = self.check_interrupt() {
                return Ok(f);
            }
            return Ok(self.block(Wait::Scope(sid), SuspendReason::Scope));
        }
        let kids = self
            .scopes
            .get(sid)
            .map(|s| s.children.clone())
            .unwrap_or_default();
        for k in kids {
            self.oracle_join(k);
        }
        self.raise_scope_failure(sid)
    }

    /// Raises the failure of a child in the scope owner, once.
    pub(crate) fn raise_scope_failure(&mut self, sid: ScopeId) -> R<Flow> {
        let Some(s) = self.scopes.get_mut(sid) else {
            return Ok(Flow::Continue);
        };
        if s.propagated {
            return Ok(Flow::Continue);
        }
        let Some(msg) = s.failure.clone() else {
            return Ok(Flow::Continue);
        };
        s.propagated = true;
        let henv = s.henv.clone();
        self.fail(msg, &henv)
    }

    fn fork(&mut self, n: usize, spans: &[Span]) -> R<Flow> {
        let fs = self.pop_n(n)?;
        let henv = self.fr()?.henv.clone();
        let sid = self.new_scope(henv.clone());
        let mut tasks = Vec::new();
        for (i, f) in fs.into_iter().enumerate() {
            let span = spans.get(i).copied().unwrap_or_default();
            let t = self.spawn_task(sid, f, span)?;
            let _ = self.tasks[t].handle.consume();
            tasks.push(t);
        }
        self.task().frames.push(Frame::Fork {
            scope: sid,
            tasks,
            henv,
        });
        Ok(Flow::Continue)
    }

    fn fork_step(&mut self) -> R<Flow> {
        let cur = self.cur;
        let Some(Frame::Fork { scope, tasks, .. }) = self.tasks[cur].frames.last() else {
            return Err(self.fault("internal: no fork"));
        };
        let (sid, tasks) = (*scope, tasks.clone());
        if !tasks.iter().all(|&t| self.is_done(t)) {
            if let Some(f) = self.check_interrupt() {
                return Ok(f);
            }
            return Ok(self.block(Wait::Scope(sid), SuspendReason::Fork));
        }
        let Some(Frame::Fork { henv, .. }) = self.tasks[cur].frames.pop() else {
            return Err(self.fault("internal: no fork"));
        };
        for &k in &tasks {
            self.oracle_join(k);
        }
        let failed = self.scopes.get(sid).and_then(|s| {
            if s.propagated {
                None
            } else {
                s.failure.clone()
            }
        });
        if let Some(msg) = failed {
            if let Some(s) = self.scopes.get_mut(sid) {
                s.propagated = true;
            }
            // The values of the branches that are done go away: the unwinder
            // finishes their linear parts before the failure (ADR 0010).
            return self.fail_after_results(&tasks, msg, henv);
        }
        let mut vals = Vec::new();
        for t in tasks {
            match self.tasks[t].result.take() {
                Some(TaskResult::Ok(v)) => vals.push(v),
                _ => vals.push(Value::Unit),
            }
        }
        // A `fork` gives a tuple of the branch values, also when each one is
        // `()`: a generic caller takes the tuple apart (ADR 0010).
        self.deliver(Value::Tuple(vals))
    }
}
