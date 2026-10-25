//! The heap: cells for locals, temporaries, buffers, boxes and counted cells.
//!
//! A cell never moves. A reference is a cell and a path, so a reference to a
//! field of a `!Move` struct keeps its address while the struct stays in its cell.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::oracle::facts::HeapEvent;
use crate::oracle::Oracle;
use crate::value::{CellId, ClosureVal, EnumMark, Place, TaskId, Value};

/// What a cell holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SlotKind {
    /// A local variable or a parameter.
    Local,
    /// A temporary value that a statement borrows.
    Temp,
    /// The buffer of a `Vec`. The value is a [`Value::List`].
    Buf,
    /// The target of a `Box`.
    Boxed,
    /// The target of an `Rc`, with its counts.
    Rc {
        /// The strong count.
        strong: u32,
        /// The weak count.
        weak: u32,
    },
    /// A freed cell.
    Free,
}

/// One heap cell.
#[derive(Clone, Debug)]
pub struct Slot {
    /// The value.
    pub val: Value,
    /// The kind.
    pub kind: SlotKind,
}

/// The heap.
#[derive(Clone, Debug, Default)]
pub struct Heap {
    slots: Vec<Slot>,
    /// For each type definition: true if its values never copy (linear or `!Move`).
    move_only: Rc<[bool]>,
    /// The state of the oracle checks, if they are on (see [`crate::oracle`]).
    oracle: Option<RefCell<Oracle>>,
    /// The tasks whose handle was dropped, for example by a `spawn` in
    /// statement position: the scope keeps the task, and no `join` takes its
    /// result.
    dropped_tasks: BTreeSet<TaskId>,
    /// With the fact oracle on: the accesses since the last
    /// [`Heap::take_facts_log`] (`crate::oracle::facts`).
    facts_log: Option<RefCell<Vec<HeapEvent>>>,
}

impl Heap {
    /// Makes an empty heap. `move_only[a]` tells whether type `a` never copies.
    pub const fn new(move_only: Rc<[bool]>) -> Self {
        Self {
            slots: Vec::new(),
            move_only,
            oracle: None,
            dropped_tasks: BTreeSet::new(),
            facts_log: None,
        }
    }

    /// Turns the log of the fact oracle on.
    pub fn enable_facts_log(&mut self) {
        self.facts_log = Some(RefCell::new(Vec::new()));
    }

    /// Takes the accesses that the log of the fact oracle has.
    pub fn take_facts_log(&self) -> Vec<HeapEvent> {
        self.facts_log
            .as_ref()
            .map(|l| std::mem::take(&mut *l.borrow_mut()))
            .unwrap_or_default()
    }

    /// Adds an access to the log of the fact oracle, if it is on.
    fn log_fact(&self, e: impl FnOnce() -> HeapEvent) {
        if let Some(l) = &self.facts_log {
            l.borrow_mut().push(e());
        }
    }

    /// Returns true if the handle of task `t` was dropped: no value holds it.
    pub fn handle_dropped(&self, t: TaskId) -> bool {
        self.dropped_tasks.contains(&t)
    }

    /// Turns the oracle checks on.
    pub fn enable_oracle(&mut self) {
        self.oracle = Some(RefCell::new(Oracle::default()));
    }

    /// Returns the state of the oracle checks, if they are on.
    pub const fn oracle(&self) -> Option<&RefCell<Oracle>> {
        self.oracle.as_ref()
    }

    /// With the oracle checks on, notes a violation and returns it as an error
    /// if cell `c` is freed.
    fn oracle_freed(&self, c: CellId, what: &str) -> Result<(), String> {
        let Some(o) = &self.oracle else {
            return Ok(());
        };
        if self.slots.get(c).is_some_and(|s| s.kind == SlotKind::Free) {
            let msg = format!("oracle: {what} of a freed cell (a dangling reference)");
            o.borrow_mut().flag(msg.clone());
            return Err(msg);
        }
        Ok(())
    }

    /// With the oracle checks on, records an access to place `p` for the race
    /// detector.
    fn oracle_access(&self, cell: CellId, path: &[u32], write: bool) {
        if let Some(o) = &self.oracle {
            let what = match self.slots.get(cell).map(|s| s.kind) {
                Some(SlotKind::Local) => "local",
                Some(SlotKind::Temp) => "temporary",
                Some(SlotKind::Buf) => "buffer",
                Some(SlotKind::Boxed) => "box",
                Some(SlotKind::Rc { .. }) => "counted cell",
                Some(SlotKind::Free) | None => "freed cell",
            };
            o.borrow_mut().access(cell, path, write, what);
        }
    }

    /// With the oracle checks on, records a read of the value at `p`.
    pub fn log_read(&self, p: &Place) {
        self.oracle_access(p.cell, &p.path, false);
        self.log_fact(|| HeapEvent::Read(Place::new(p.cell, p.path.clone())));
    }

    /// With the fact oracle on, records that the run follows the reference
    /// at `p`.
    pub fn log_deref(&self, p: &Place) {
        self.log_fact(|| HeapEvent::Deref(Place::new(p.cell, p.path.clone())));
    }

    /// With the oracle checks on, notes a violation if a reference to `p` is
    /// followed after the scope of its local ended.
    pub fn check_ref(&self, p: &Place) {
        if let Some(o) = &self.oracle {
            let ended = o.borrow().ended(p.cell);
            if ended {
                o.borrow_mut()
                    .flag("oracle: a reference into a local whose scope ended is used (a dangling reference)");
            }
        }
    }

    /// Returns the identity of a new enum value ([`crate::value::EnumVal::id`]):
    /// a new number with the oracle checks on, else 0.
    pub fn new_enum_id(&self) -> u64 {
        self.oracle
            .as_ref()
            .map_or(0, |o| o.borrow_mut().next_enum_id())
    }

    /// With the oracle checks on, returns `p` with a mark for each enum
    /// value that the path of `p` goes into (see [`EnumMark`]). A step that
    /// has a mark keeps it: a reference made from an old reference keeps
    /// the enum values of the old one. Use it for each new reference.
    pub fn mark(&self, p: Place) -> Place {
        if self.oracle.is_none() || p.path.is_empty() {
            return p;
        }
        let mut p = p;
        let Ok(slot) = self.slot(p.cell) else {
            return p;
        };
        let mut v = &slot.val;
        let mut marks = Vec::new();
        for (d, &i) in p.path.iter().enumerate() {
            let depth = u32::try_from(d).unwrap_or(u32::MAX);
            if let Some(m) = p.marks.iter().find(|m| m.depth == depth) {
                marks.push(*m);
            } else if let Value::Enum(e) = v {
                marks.push(EnumMark { depth, id: e.id });
            }
            let Some(next) = part(v, i) else {
                // The rest of the path does not exist now: keep the old
                // marks below this step.
                marks.extend(p.marks.iter().filter(|m| m.depth > depth).copied());
                break;
            };
            v = next;
        }
        p.marks = marks;
        p
    }

    /// With the oracle checks on, notes a violation and returns it as an
    /// error if an enum value that a mark of `p` names got a new value.
    fn check_marks(&self, p: &Place, what: &str) -> Result<(), String> {
        let (Some(o), Ok(slot)) = (&self.oracle, self.slot(p.cell)) else {
            return Ok(());
        };
        let mut v = &slot.val;
        let mut marks = p.marks.iter().peekable();
        for (d, &i) in p.path.iter().enumerate() {
            let depth = u32::try_from(d).unwrap_or(u32::MAX);
            if let Some(m) = marks.next_if(|m| m.depth == depth) {
                if !matches!(v, Value::Enum(e) if e.id == m.id) {
                    let msg = format!(
                        "oracle: {what} of a part of an enum value that got a new value (a dangling reference)"
                    );
                    o.borrow_mut().flag(msg.clone());
                    return Err(msg);
                }
            }
            if marks.peek().is_none() {
                return Ok(());
            }
            let Some(next) = part(v, i) else {
                return Ok(());
            };
            v = next;
        }
        Ok(())
    }

    /// Allocates a cell.
    pub fn alloc(&mut self, kind: SlotKind, val: Value) -> CellId {
        self.slots.push(Slot { val, kind });
        self.slots.len() - 1
    }

    /// Returns the number of cells ever allocated.
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    /// Returns true if no cell was allocated.
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    /// Returns a cell.
    pub fn slot(&self, c: CellId) -> Result<&Slot, String> {
        self.slots.get(c).ok_or_else(|| format!("bad cell {c}"))
    }

    /// Returns a cell for writing.
    pub fn slot_mut(&mut self, c: CellId) -> Result<&mut Slot, String> {
        self.slots.get_mut(c).ok_or_else(|| format!("bad cell {c}"))
    }

    /// Returns the value at a place.
    pub fn get(&self, p: &Place) -> Result<&Value, String> {
        self.oracle_freed(p.cell, "a read")?;
        if !p.marks.is_empty() {
            self.check_marks(p, "a read")?;
        }
        let mut v = &self.slot(p.cell)?.val;
        for &i in &p.path {
            let i = i as usize;
            v = match v {
                Value::Tuple(vs) | Value::List(vs) => vs.get(i),
                Value::Struct(o) => o.fields.get(i),
                Value::Enum(e) => e.fields.get(i),
                _ => None,
            }
            .ok_or_else(|| "a place does not exist (the value changed shape)".to_string())?;
        }
        Ok(v)
    }

    /// Returns the value at a place for writing.
    pub fn get_mut(&mut self, p: &Place) -> Result<&mut Value, String> {
        if self.facts_log.is_some() {
            let fresh = matches!(self.get_quiet(p), Ok(Value::Moved));
            self.log_fact(|| HeapEvent::Write(Place::new(p.cell, p.path.clone()), fresh));
        }
        self.get_mut_quiet(p)
    }

    /// The value at a place, with no check and no log.
    fn get_quiet(&self, p: &Place) -> Result<&Value, String> {
        let mut v = &self.slot(p.cell)?.val;
        for &i in &p.path {
            v = part(v, i).ok_or_else(|| "a place does not exist".to_string())?;
        }
        Ok(v)
    }

    /// [`Heap::get_mut`] with no log of the fact oracle.
    fn get_mut_quiet(&mut self, p: &Place) -> Result<&mut Value, String> {
        self.oracle_freed(p.cell, "a write")?;
        if !p.marks.is_empty() {
            self.check_marks(p, "a write")?;
        }
        self.oracle_access(p.cell, &p.path, true);
        let mut v = &mut self.slot_mut(p.cell)?.val;
        for &i in &p.path {
            let i = i as usize;
            v = match v {
                Value::Tuple(vs) | Value::List(vs) => vs.get_mut(i),
                Value::Struct(o) => o.fields.get_mut(i),
                Value::Enum(e) => e.fields.get_mut(i),
                _ => None,
            }
            .ok_or_else(|| "a place does not exist (the value changed shape)".to_string())?;
        }
        Ok(v)
    }

    /// Takes the value out of a place and leaves [`Value::Moved`].
    pub fn take(&mut self, p: &Place) -> Result<Value, String> {
        if self.facts_log.is_some() {
            self.log_fact(|| HeapEvent::Take(Place::new(p.cell, p.path.clone())));
        }
        Ok(take_moved(self.get_mut_quiet(p)?))
    }

    /// Returns the elements of a buffer cell.
    pub fn list(&self, buf: CellId) -> Result<&Vec<Value>, String> {
        self.oracle_freed(buf, "a read")?;
        match &self.slot(buf)?.val {
            Value::List(vs) => Ok(vs),
            _ => Err("a buffer was freed".into()),
        }
    }

    /// Returns the elements of a buffer cell for writing.
    pub fn list_mut(&mut self, buf: CellId) -> Result<&mut Vec<Value>, String> {
        self.oracle_freed(buf, "a write")?;
        self.oracle_access(buf, &[], true);
        self.log_fact(|| HeapEvent::Write(Place::root(buf), false));
        match &mut self.slot_mut(buf)?.val {
            Value::List(vs) => Ok(vs),
            _ => Err("a buffer was freed".into()),
        }
    }

    /// Returns true if using the value copies it. Other values move.
    pub fn is_copy(&self, v: &Value) -> bool {
        match v {
            Value::Unit
            | Value::Bool(_)
            | Value::Int(_)
            | Value::Str(_)
            | Value::Dur(_)
            | Value::Ref(_)
            | Value::Slice { .. }
            | Value::Closure(_)
            | Value::FnItem(_)
            | Value::Cont(_)
            | Value::Scope(_)
            | Value::Cap(_)
            | Value::Request(_)
            | Value::Response(_)
            | Value::Loc(..)
            | Value::Moved => true,
            Value::Tuple(vs) => vs.iter().all(|v| self.is_copy(v)),
            Value::Struct(o) => {
                o.lin.is_none()
                    && !self.move_only.get(o.adt.index()).copied().unwrap_or(false)
                    && o.fields.iter().all(|v| self.is_copy(v))
            }
            Value::Enum(e) => e.fields.iter().all(|v| self.is_copy(v)),
            Value::Vec(_)
            | Value::List(_)
            | Value::Boxed(_)
            | Value::Rc(_)
            | Value::Weak(_)
            | Value::Task(_)
            | Value::Iter(_) => false,
        }
    }

    /// Increments the strong count of a counted cell.
    pub fn rc_inc(&mut self, c: CellId) -> Result<(), String> {
        match &mut self.slot_mut(c)?.kind {
            SlotKind::Rc { strong, .. } => {
                *strong += 1;
                Ok(())
            }
            _ => Err("`Rc` handle to a cell that is not counted".into()),
        }
    }

    /// Increments the weak count of a counted cell.
    pub fn weak_inc(&mut self, c: CellId) -> Result<(), String> {
        match &mut self.slot_mut(c)?.kind {
            SlotKind::Rc { weak, .. } => {
                *weak += 1;
                Ok(())
            }
            _ => Err("`Weak` handle to a cell that is not counted".into()),
        }
    }

    /// Returns the strong count of a counted cell, or 0.
    pub fn strong(&self, c: CellId) -> u32 {
        match self.slots.get(c).map(|s| s.kind) {
            Some(SlotKind::Rc { strong, .. }) => strong,
            _ => 0,
        }
    }

    /// Drops a value: frees buffers and boxes, and decrements counts.
    pub fn drop_value(&mut self, v: Value) {
        let mut work = vec![v];
        while let Some(v) = work.pop() {
            match v {
                Value::Tuple(vs) | Value::List(vs) => work.extend(vs),
                Value::Struct(o) => {
                    if let (Some(id), Some(oracle)) = (o.lin, &self.oracle) {
                        oracle.borrow_mut().drop_lin(id);
                    }
                    work.extend(o.fields);
                }
                Value::Enum(e) => work.extend(e.fields),
                Value::Task(t) => {
                    self.dropped_tasks.insert(t);
                }
                Value::Vec(c) | Value::Boxed(c) => {
                    if let Some(s) = self.slots.get_mut(c) {
                        if matches!(s.kind, SlotKind::Buf | SlotKind::Boxed) {
                            s.kind = SlotKind::Free;
                            work.push(take_moved(&mut s.val));
                        }
                    }
                }
                Value::Rc(c) => {
                    if let Some(s) = self.slots.get_mut(c) {
                        if let SlotKind::Rc { strong, weak } = &mut s.kind {
                            *strong = strong.saturating_sub(1);
                            if *strong == 0 {
                                let w = *weak;
                                if w == 0 {
                                    s.kind = SlotKind::Free;
                                }
                                work.push(take_moved(&mut s.val));
                            }
                        }
                    }
                }
                Value::Weak(c) => {
                    if let Some(s) = self.slots.get_mut(c) {
                        if let SlotKind::Rc { strong, weak } = &mut s.kind {
                            *weak = weak.saturating_sub(1);
                            if *strong == 0 && *weak == 0 {
                                s.kind = SlotKind::Free;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Ends the life of a local or temporary cell. Copy values stay readable, so a
    /// closure that outlives the scope of a captured integer still sees it.
    pub fn end_cell(&mut self, c: CellId) {
        if let Some(v) = self.end_cell_value(c) {
            self.drop_value(v);
        }
    }

    /// Ends the life of a local or temporary cell, as [`Heap::end_cell`] does,
    /// and returns its value if it is not a copy value. The unwinder finds the
    /// linear values in it. A copy value stays in the cell.
    pub fn end_cell_value(&mut self, c: CellId) -> Option<Value> {
        let s = self.slots.get(c)?;
        let copy = self.is_copy(&s.val);
        if let Some(o) = &self.oracle {
            // A reference into the cell dangles now, also for a copy value.
            if s.kind == SlotKind::Local || !copy {
                o.borrow_mut().end_cell(c);
            }
        }
        if copy {
            return None;
        }
        Some(take_moved(&mut self.slots.get_mut(c)?.val))
    }

    /// Returns the number of counted cells that are still alive.
    pub fn leaked_rc(&self) -> usize {
        self.slots
            .iter()
            .filter(|s| matches!(s.kind, SlotKind::Rc { strong, .. } if strong > 0))
            .count()
    }

    /// Copies a value for a copied continuation frame. `map` gives the new cell of
    /// each copied cell. Owned buffers and boxes in `map` are copied by the caller.
    pub fn remap(&mut self, v: &Value, map: &BTreeMap<CellId, CellId>) -> Value {
        let m = |c: &CellId| map.get(c).copied().unwrap_or(*c);
        match v {
            Value::Tuple(vs) => Value::Tuple(vs.iter().map(|v| self.remap(v, map)).collect()),
            Value::List(vs) => Value::List(vs.iter().map(|v| self.remap(v, map)).collect()),
            Value::Struct(o) => {
                let mut o2 = (**o).clone();
                o2.fields = o.fields.iter().map(|v| self.remap(v, map)).collect();
                Value::Struct(Box::new(o2))
            }
            Value::Enum(e) => {
                let mut e2 = (**e).clone();
                e2.fields = e.fields.iter().map(|v| self.remap(v, map)).collect();
                Value::Enum(Box::new(e2))
            }
            Value::Vec(c) => Value::Vec(m(c)),
            Value::Boxed(c) => Value::Boxed(m(c)),
            Value::Rc(c) => {
                let _ = self.rc_inc(*c);
                Value::Rc(*c)
            }
            Value::Weak(c) => {
                let _ = self.weak_inc(*c);
                Value::Weak(*c)
            }
            Value::Ref(p) => Value::Ref(Place {
                cell: m(&p.cell),
                ..p.clone()
            }),
            Value::Loc(p, t) => Value::Loc(
                Place {
                    cell: m(&p.cell),
                    ..p.clone()
                },
                *t,
            ),
            Value::Slice { buf, lo, hi } => Value::Slice {
                buf: m(buf),
                lo: *lo,
                hi: *hi,
            },
            Value::Closure(c) => {
                if c.cells.iter().any(|x| map.contains_key(x)) {
                    Value::Closure(Rc::new(ClosureVal {
                        code: c.code,
                        cells: c.cells.iter().map(m).collect(),
                        owned: c.owned.iter().map(m).collect(),
                        henv: c.henv.clone(),
                        span: c.span,
                    }))
                } else {
                    Value::Closure(Rc::clone(c))
                }
            }
            Value::Iter(it) => {
                let mut it2 = (**it).clone();
                if let crate::value::IterState::Elems { buf, .. } = &mut it2 {
                    *buf = m(buf);
                }
                Value::Iter(Box::new(it2))
            }
            other => other.clone(),
        }
    }

    /// Collects the buffers and boxes that a value owns, recursively.
    pub fn owned_cells(&self, v: &Value, out: &mut Vec<CellId>) {
        let mut work = vec![v];
        while let Some(v) = work.pop() {
            match v {
                Value::Tuple(vs) | Value::List(vs) => work.extend(vs.iter()),
                Value::Struct(o) => work.extend(o.fields.iter()),
                Value::Enum(e) => work.extend(e.fields.iter()),
                Value::Vec(c) | Value::Boxed(c) => {
                    if let Some(s) = self.slots.get(*c) {
                        if matches!(s.kind, SlotKind::Buf | SlotKind::Boxed) && !out.contains(c) {
                            out.push(*c);
                            work.push(&s.val);
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

/// Returns part `i` of a value: a field, a payload part, a tuple part or an
/// element of a buffer.
fn part(v: &Value, i: u32) -> Option<&Value> {
    let i = i as usize;
    match v {
        Value::Tuple(vs) | Value::List(vs) => vs.get(i),
        Value::Struct(o) => o.fields.get(i),
        Value::Enum(e) => e.fields.get(i),
        _ => None,
    }
}

/// Replaces a value with [`Value::Moved`] and returns the old value.
pub const fn take_moved(v: &mut Value) -> Value {
    std::mem::replace(v, Value::Moved)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{Obj, Value};

    fn heap() -> Heap {
        Heap::new(Rc::from(vec![false, true]))
    }

    #[test]
    fn rc_counts_and_leaks() {
        let mut h = heap();
        let c = h.alloc(SlotKind::Rc { strong: 1, weak: 0 }, Value::Int(1));
        h.rc_inc(c).ok();
        assert_eq!(h.strong(c), 2);
        h.drop_value(Value::Rc(c));
        assert_eq!(h.leaked_rc(), 1);
        h.weak_inc(c).ok();
        h.drop_value(Value::Rc(c));
        assert_eq!(h.leaked_rc(), 0);
        assert!(matches!(
            h.slot(c).map(|s| s.kind),
            Ok(SlotKind::Rc { strong: 0, weak: 1 })
        ));
        h.drop_value(Value::Weak(c));
        assert!(matches!(h.slot(c).map(|s| s.kind), Ok(SlotKind::Free)));
        assert!(h.rc_inc(c).is_err());
        assert!(h.weak_inc(c).is_err());
        assert_eq!(h.strong(999), 0);
    }

    #[test]
    fn places_and_copies() {
        let mut h = heap();
        assert!(h.is_empty());
        let buf = h.alloc(
            SlotKind::Buf,
            Value::List(vec![Value::Int(1), Value::Int(2)]),
        );
        let local = h.alloc(
            SlotKind::Local,
            Value::Tuple(vec![Value::Vec(buf), Value::Int(3)]),
        );
        assert_eq!(h.len(), 2);
        let p = Place::root(local).child(1);
        assert!(matches!(h.get(&p), Ok(Value::Int(3))));
        *h.get_mut(&p).unwrap_or(&mut Value::Unit) = Value::Int(4);
        assert!(matches!(h.take(&p), Ok(Value::Int(4))));
        assert!(matches!(h.get(&p), Ok(Value::Moved)));
        assert!(h.get(&Place::root(local).child(9)).is_err());
        assert!(h.get_mut(&Place::root(local).child(0).child(0)).is_err());
        assert_eq!(h.list(buf).map(Vec::len), Ok(2));
        h.list_mut(buf).map(|l| l.push(Value::Int(5))).ok();
        let mut owned = Vec::new();
        h.owned_cells(
            h.get(&Place::root(local)).unwrap_or(&Value::Unit),
            &mut owned,
        );
        assert_eq!(owned, vec![buf]);
        let lin = Value::Struct(Box::new(Obj {
            adt: weft_sema::AdtId(0),
            fields: vec![],
            lin: Some(0),
        }));
        assert!(!h.is_copy(&lin));
        let immovable = Value::Struct(Box::new(Obj {
            adt: weft_sema::AdtId(1),
            fields: vec![],
            lin: None,
        }));
        assert!(!h.is_copy(&immovable));
        assert!(h.is_copy(&Value::Tuple(vec![Value::Int(1)])));
        assert!(!h.is_copy(&Value::Vec(buf)));
        h.end_cell(local);
        assert!(h.list(buf).is_err());
        assert!(h.slot(1000).is_err());
    }
}
