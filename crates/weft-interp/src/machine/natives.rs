//! Native functions: the `extern` items of the prelude and foreign functions.

use std::rc::Rc;

use weft_sema::program::FnId;
use weft_sema::types::Ty;

use super::{Flow, Frame, TaskResult, Timer, Wait, R};
use crate::heap::SlotKind;
use crate::runtime::Native;
use crate::trace::{SuspendReason, TraceEvent};
use crate::value::{Cap, CellId, EnumVal, HEnv, HttpResponse, Place, Value};

/// The number of threads of the blocking pool.
const POOL_THREADS: usize = 2;

impl super::Machine<'_, '_> {
    /// Makes an `Option` value.
    pub(crate) fn option(&self, v: Option<Value>) -> R<Value> {
        let Some(adt) = self.rt.b.option else {
            return Err(self.fault("the prelude has no `Option`"));
        };
        let name = if v.is_some() { "Some" } else { "None" };
        let variant = self
            .rt
            .variant_index(adt, name)
            .ok_or_else(|| self.fault("`Option` has no such variant"))?;
        Ok(Value::Enum(Box::new(EnumVal {
            adt,
            variant: u32::try_from(variant).unwrap_or(0),
            fields: v.into_iter().collect(),
        })))
    }

    /// Returns the buffer and range of a `Vec` receiver (a reference to a `Vec`
    /// or a slice).
    fn vec_of(&self, recv: &Value) -> R<(CellId, u32, u32, bool)> {
        let p = match recv {
            Value::Ref(p) | Value::Loc(p, _) => {
                if let Value::Ref(p) = recv {
                    self.heap.check_ref(p);
                }
                self.follow_refs(p.clone())?
            }
            Value::Vec(buf) => {
                let len = self.heap.list(*buf).map_err(|e| self.fault(e))?.len();
                return Ok((*buf, 0, u32::try_from(len).unwrap_or(u32::MAX), true));
            }
            Value::Slice { buf, lo, hi } => return Ok((*buf, *lo, *hi, false)),
            _ => return Err(self.fault("a `Vec` is needed here")),
        };
        let (p, _) = self.resolve(p, false)?;
        self.heap.log_read(&p);
        match self.hget(&p)? {
            Value::Vec(buf) => {
                let len = self.heap.list(*buf).map_err(|e| self.fault(e))?.len();
                Ok((*buf, 0, u32::try_from(len).unwrap_or(u32::MAX), true))
            }
            Value::Slice { buf, lo, hi } => Ok((*buf, *lo, *hi, false)),
            _ => Err(self.fault("a `Vec` is needed here")),
        }
    }

    /// With the oracle checks on, a change of the length of a `Vec` moves its
    /// buffer, as a real `Vec` can when it grows or shrinks. The old buffer is
    /// freed, so a reference into it dangles.
    fn oracle_move_buffer(&mut self, recv: &Value) -> R<()> {
        if self.heap.oracle().is_none() {
            return Ok(());
        }
        let p = match recv {
            Value::Ref(p) | Value::Loc(p, _) => self.follow_refs(p.clone())?,
            _ => return Ok(()),
        };
        let (p, _) = self.resolve(p, false)?;
        let Value::Vec(old) = self.hget(&p)?.clone() else {
            return Ok(());
        };
        let list = self
            .heap
            .take(&Place::root(old))
            .map_err(|e| self.fault(e))?;
        let new = self.heap.alloc(SlotKind::Buf, list);
        *self.hget_mut(&p)? = Value::Vec(new);
        if let Ok(s) = self.heap.slot_mut(old) {
            s.kind = SlotKind::Free;
        }
        Ok(())
    }

    fn list_mut(&mut self, buf: CellId) -> R<&mut Vec<Value>> {
        self.heap
            .list_mut(buf)
            .map_err(|e| crate::error::RuntimeError::new(crate::error::ErrorKind::Fault, e, None))
    }

    /// Returns the value behind a reference receiver, without following `Rc`.
    fn recv_value(&self, recv: &Value) -> R<Value> {
        match recv {
            Value::Ref(p) | Value::Loc(p, _) => {
                let p = self.follow_refs(p.clone())?;
                Ok(self.hget(&p)?.clone())
            }
            other => Ok(other.clone()),
        }
    }

    fn str_arg(&self, v: &Value) -> String {
        self.show(v)
    }

    fn dur_arg(&self, v: Value) -> R<u64> {
        match self.deref_value(v)? {
            Value::Dur(d) => Ok(d),
            Value::Int(i) => Ok(u64::try_from(i).unwrap_or(0)),
            _ => Err(self.fault("a `Duration` is needed here")),
        }
    }

    /// Returns a default value of a type, for foreign functions.
    fn default_of(&self, t: &Ty) -> Value {
        match t {
            Ty::Int(_) => Value::Int(0),
            Ty::Bool => Value::Bool(false),
            Ty::Tuple(ts) => Value::Tuple(ts.iter().map(|t| self.default_of(t)).collect()),
            Ty::Adt(a, _) if Some(*a) == self.rt.b.string => Value::str(""),
            Ty::Adt(a, _) if Some(*a) == self.rt.b.duration => Value::Dur(0),
            _ => Value::Unit,
        }
    }

    /// Calls a closure from native code.
    fn call_closure(&mut self, f: Value, args: Vec<Value>) -> R<Flow> {
        self.call_value(f, args)
    }

    /// Runs a native function.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn native(&mut self, n: Native, f: FnId, args: Vec<Value>, henv: HEnv) -> R<Flow> {
        let mut it = args.into_iter();
        let mut next = || it.next().unwrap_or_default();
        let v = match n {
            Native::VecNew => {
                let buf = self.heap.alloc(SlotKind::Buf, Value::List(Vec::new()));
                Value::Vec(buf)
            }
            Native::VecPush => {
                let recv = next();
                let x = next();
                self.oracle_move_buffer(&recv)?;
                let (buf, _, _, whole) = self.vec_of(&recv)?;
                if !whole {
                    return Err(self.fault("cannot push to a slice"));
                }
                self.list_mut(buf)?.push(x);
                Value::Unit
            }
            Native::VecPop => {
                let recv = next();
                self.oracle_move_buffer(&recv)?;
                let (buf, _, _, _) = self.vec_of(&recv)?;
                let x = self.list_mut(buf)?.pop();
                self.option(x)?
            }
            Native::VecClear => {
                let recv = next();
                self.oracle_move_buffer(&recv)?;
                let (buf, _, _, _) = self.vec_of(&recv)?;
                let xs = std::mem::take(self.list_mut(buf)?);
                for x in xs {
                    self.heap.drop_value(x);
                }
                Value::Unit
            }
            Native::VecLen => {
                let recv = next();
                let (_, lo, hi, _) = self.vec_of(&recv)?;
                Value::Int(i64::from(hi.saturating_sub(lo)))
            }
            Native::VecGet => {
                let recv = next();
                let i = self.int_of(next())?;
                let (buf, lo, hi, _) = self.vec_of(&recv)?;
                let i = u32::try_from(i)
                    .ok()
                    .filter(|&i| lo.saturating_add(i) < hi)
                    .ok_or_else(|| self.fault(format!("index {i} is out of bounds")))?;
                Value::Ref(Place::root(buf).child(lo + i))
            }
            Native::VecSplitAt | Native::VecSplitMut => {
                let recv = next();
                let mid = self.int_of(next())?;
                let (buf, lo, hi, _) = self.vec_of(&recv)?;
                let mid = u32::try_from(mid)
                    .ok()
                    .filter(|&m| lo.saturating_add(m) <= hi)
                    .ok_or_else(|| self.fault("the split point is out of bounds"))?;
                Value::Tuple(vec![
                    Value::Slice {
                        buf,
                        lo,
                        hi: lo + mid,
                    },
                    Value::Slice {
                        buf,
                        lo: lo + mid,
                        hi,
                    },
                ])
            }
            Native::BoxNew => {
                let x = next();
                Value::Boxed(self.heap.alloc(SlotKind::Boxed, x))
            }
            Native::RcNew => {
                let x = next();
                Value::Rc(self.heap.alloc(SlotKind::Rc { strong: 1, weak: 0 }, x))
            }
            Native::RcClone => match self.recv_value(&next())? {
                Value::Rc(c) => {
                    self.heap.rc_inc(c).map_err(|e| self.fault(e))?;
                    Value::Rc(c)
                }
                _ => return Err(self.fault("`clone` needs an `Rc`")),
            },
            Native::RcDowngrade => match self.recv_value(&next())? {
                Value::Rc(c) => {
                    self.heap.weak_inc(c).map_err(|e| self.fault(e))?;
                    Value::Weak(c)
                }
                _ => return Err(self.fault("`downgrade` needs an `Rc`")),
            },
            Native::WeakUpgrade => match self.recv_value(&next())? {
                Value::Weak(c) => {
                    if self.heap.strong(c) > 0 {
                        self.heap.rc_inc(c).map_err(|e| self.fault(e))?;
                        self.option(Some(Value::Rc(c)))?
                    } else {
                        self.option(None)?
                    }
                }
                _ => return Err(self.fault("`upgrade` needs a `Weak`")),
            },
            Native::StrLen => match self.recv_value(&next())? {
                Value::Str(s) => Value::Int(i64::try_from(s.len()).unwrap_or(i64::MAX)),
                _ => return Err(self.fault("`len` needs a `String`")),
            },
            Native::TaskJoin => return self.join(next(), &henv),
            Native::TaskDetach => {
                if let Value::Task(t) = self.deref_value(next())? {
                    if self.tasks[t].handle.consume().is_err() {
                        return Err(self.fault("a task handle was used twice"));
                    }
                }
                Value::Unit
            }
            Native::FsRead => {
                let _cap = next();
                let path = self.str_arg(&next());
                match std::fs::read_to_string(&path) {
                    Ok(s) => Value::str(&s),
                    Err(e) => return self.fail(format!("cannot read {path}: {e}"), &henv),
                }
            }
            Native::NetListen => {
                let _cap = next();
                let addr = self.str_arg(&next());
                self.listeners.push(addr);
                Value::Cap(Cap::Listener(self.listeners.len() - 1))
            }
            Native::StdoutWrite => {
                let _cap = next();
                let s = self.str_arg(&next());
                self.out_line(&s);
                Value::Unit
            }
            Native::StdoutWriteAll => {
                let _cap = next();
                let lines = next();
                let (buf, lo, hi, _) = self.vec_of(&lines)?;
                let items: Vec<String> = self
                    .heap
                    .list(buf)
                    .map_err(|e| self.fault(e))?
                    .iter()
                    .skip(lo as usize)
                    .take(hi.saturating_sub(lo) as usize)
                    .map(|v| self.show(v))
                    .collect();
                for s in items {
                    self.out_line(&s);
                }
                self.heap.drop_value(lines);
                Value::Unit
            }
            Native::ReqParam => {
                let req = self.recv_value(&next())?;
                let key = self.str_arg(&next());
                match req {
                    Value::Request(r) => Value::str(r.params.get(&key).map_or("", String::as_str)),
                    _ => return Err(self.fault("`param` needs a `Request`")),
                }
            }
            Native::RespJson => {
                let x = next();
                let body = self.json(&x);
                self.heap.drop_value(x);
                Value::Response(Rc::new(HttpResponse {
                    status: 200,
                    content_type: "application/json".into(),
                    body,
                }))
            }
            Native::RespText => {
                let s = self.str_arg(&next());
                Value::Response(Rc::new(HttpResponse {
                    status: 200,
                    content_type: "text/plain".into(),
                    body: s,
                }))
            }
            Native::HttpServe => {
                let l = self.deref_value(next())?;
                let h = next();
                return self.http_serve(&l, h, &henv);
            }
            Native::WithTimeout => {
                let d = self.dur_arg(next())?;
                let body = next();
                let id = self.fresh_id();
                let task = self.cur;
                let at = self.now.saturating_add(d);
                self.add_timer(at, Timer::Timeout { task, id });
                self.task().frames.push(Frame::Timeout { id, henv });
                return self.call_closure(body, Vec::new());
            }
            Native::Sleep => {
                let d = next();
                let Some(clock) = self.rt.b.clock else {
                    let d = self.dur_arg(d)?;
                    return Ok(self.sleep_for(d));
                };
                let op = self.rt.prog.effects[clock]
                    .ops
                    .iter()
                    .position(|o| o.name == "sleep")
                    .unwrap_or(0);
                return self.perform(clock, op, vec![d], &henv);
            }
            Native::SimRun => {
                let seed = self.int_of(next())?;
                let workers = self.int_of(next())?;
                let body = next();
                let workers = usize::try_from(workers).unwrap_or(1).clamp(1, 1024);
                let sim = self.enter_sim(u64::try_from(seed).unwrap_or(0), workers);
                // The task enters the simulation on its first simulated worker,
                // whatever worker of the machine runs it (ADR 0010).
                let t = self.task();
                let outer = std::mem::replace(&mut t.sim_worker, 0);
                t.frames.push(Frame::Sim { sim, outer });
                return self.call_closure(body, Vec::new());
            }
            // Phase 1 does not simulate the network: the partition is only
            // recorded (ADR 0010).
            Native::SimPartition => {
                let a = next();
                let b = next();
                let (la, lb) = (self.int_list(&a), self.int_list(&b));
                self.heap.drop_value(a);
                self.heap.drop_value(b);
                if let Some(s) = self.sim_of(self.cur).and_then(|s| self.sims.get_mut(s)) {
                    s.partition = Some((la.clone(), lb.clone()));
                }
                self.trace.push(TraceEvent::Partition { a: la, b: lb });
                Value::Unit
            }
            Native::SimHeal => {
                if let Some(s) = self.sim_of(self.cur).and_then(|s| self.sims.get_mut(s)) {
                    s.partition = None;
                }
                self.trace.push(TraceEvent::Heal);
                Value::Unit
            }
            Native::SimAdvance => {
                let d = self.dur_arg(next())?;
                self.now = self.now.saturating_add(d);
                self.trace.push(TraceEvent::Advance { now: self.now });
                self.fire_timers();
                Value::Unit
            }
            Native::UserExtern { blocking } => {
                let ret = self
                    .rt
                    .sigs
                    .get(f.index())
                    .map_or(Value::Unit, |s| self.default_of(&s.ret));
                for a in it {
                    self.heap.drop_value(a);
                }
                if !blocking {
                    return self.deliver(ret);
                }
                return Ok(self.blocking_call(f, ret));
            }
            Native::Unknown => {
                return Err(self.fault(format!(
                    "the interpreter has no implementation of `{}`",
                    self.rt.prog.fns[f].path
                )));
            }
        };
        self.deliver(v)
    }

    /// Runs a foreign call on the blocking pool. The task waits for the pool.
    fn blocking_call(&mut self, f: FnId, ret: Value) -> Flow {
        if let Some(fl) = self.check_interrupt() {
            return fl;
        }
        let thread = self.blocking_calls % POOL_THREADS;
        self.blocking_calls += 1;
        let task = self.cur;
        self.trace.push(TraceEvent::BlockingCall {
            task,
            name: self.rt.prog.fns[f].path.clone(),
            thread,
        });
        let seq = self.wait_seq();
        let at = self.now.saturating_add(1);
        self.add_timer(
            at,
            Timer::Wake {
                task,
                seq,
                value: ret,
            },
        );
        self.block(Wait::Pool, SuspendReason::Blocking)
    }

    /// `t.join()` on a finished task.
    fn join(&mut self, t: Value, henv: &HEnv) -> R<Flow> {
        let Value::Task(t) = self.deref_value(t)? else {
            return Err(self.fault("`join` needs a task"));
        };
        if self.tasks[t].handle.consume().is_err() {
            return Err(self.fault("a task handle was used twice"));
        }
        self.oracle_join(t);
        let scope = self.tasks[t].scope;
        match self.tasks[t].result.take() {
            Some(TaskResult::Ok(v)) => self.deliver(v),
            Some(TaskResult::Failed { msg, .. }) => {
                if let Some(s) = scope.and_then(|s| self.scopes.get_mut(s)) {
                    s.propagated = true;
                }
                self.fail(msg, henv)
            }
            Some(TaskResult::Cancelled) => {
                let msg = scope.and_then(|s| self.scopes.get_mut(s)).map_or_else(
                    || "task was cancelled".to_string(),
                    |s| {
                        s.propagated = true;
                        s.failure
                            .clone()
                            .unwrap_or_else(|| "task was cancelled".to_string())
                    },
                );
                self.fail(msg, henv)
            }
            None => Err(self.fault("the task result was already taken")),
        }
    }
}
