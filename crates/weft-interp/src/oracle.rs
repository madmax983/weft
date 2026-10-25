//! The oracle: checks that make the interpreter a strict test oracle (OR11).
//!
//! The checks are off by default. [`RunOptions::oracle`](crate::RunOptions)
//! turns them on. With them, the machine reports a fault where a real machine
//! can do something that the design forbids, and the stock machine goes on:
//!
//! - an access to a freed cell or buffer (a dangling reference);
//! - a `Vec` moves its buffer on each `push`, `pop` and `clear`, as a real
//!   `Vec` can, so a reference into the old buffer dangles;
//! - a reference into a local whose scope ended is used, also after an abort
//!   path unwound the frame of the local;
//! - a reference into the payload of an enum value is used after the enum
//!   got a new value (a write of the enum or of a place above it), also of
//!   the same variant: the payload of a real enum is in place, so the old
//!   parts are gone (`docs/ir.md` 8.5). A write inside the payload keeps
//!   the value, as a write of a field of a struct does;
//! - a display (`print`) of a moved value, or of a value through a dangling
//!   reference;
//! - a live linear value goes away with no consume and no `on abort`, or is
//!   still live at the end of the run;
//! - a live linear value is in a cell of a frame after the cleanup chain of
//!   the frame ran (the frame scan of `docs/ir.md` 8.2): the chain must
//!   finish each value of the frame;
//! - two tasks access overlapping places, one of them writes, and no join
//!   orders them (a vector-clock race detector). Spawn, join, the end of a
//!   scope or a `fork` and unwinding are the points that order tasks;
//! - a task that the checker marks stealable reaches an `Rc`, a `Weak` or a
//!   `Scope`.
//!
//! An accepted program must not fault with these checks. The interpreter
//! program tests and the runs of the corpus turn them on.

pub mod facts;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::value::CellId;

/// The accesses of one task to one cell. For each path and each kind (a read
/// or a write), the log keeps the clock of the task at the last access. An
/// earlier access of the same task, path and kind has a smaller clock, so it
/// cannot find a race that the last one does not find. There is no limit on
/// the number of paths (I3-12).
#[derive(Clone, Debug, Default)]
struct TaskLog {
    /// The largest clock of an access in the log.
    last: u32,
    /// The clock of the last read of each path.
    reads: BTreeMap<Vec<u32>, u32>,
    /// The clock of the last write of each path.
    writes: BTreeMap<Vec<u32>, u32>,
}

/// Returns a path of `m` that overlaps `path` (one is a prefix of the other)
/// and whose clock is larger than `known`.
fn unordered(m: &BTreeMap<Vec<u32>, u32>, path: &[u32], known: u32) -> Option<Vec<u32>> {
    // The paths above `path`, and `path` itself.
    for k in 0..=path.len() {
        if m.get(&path[..k]).is_some_and(|&e| e > known) {
            return Some(path[..k].to_vec());
        }
    }
    // The paths below `path`: they follow it in the order of the map.
    m.range(path.to_vec()..)
        .take_while(|(p, _)| p.starts_with(path))
        .find(|(_, &e)| e > known)
        .map(|(p, _)| p.clone())
}

/// The state of the oracle checks.
#[derive(Clone, Debug, Default)]
pub struct Oracle {
    /// The first violation that a check found and the machine did not report yet.
    violation: Option<String>,
    /// The local and temporary cells whose scope ended.
    ended: BTreeSet<CellId>,
    /// The linear records of the struct values that the heap dropped.
    dropped_lins: Vec<usize>,
    /// The running task.
    cur: usize,
    /// The vector clock of each task.
    clocks: Vec<Vec<u32>>,
    /// The accesses of each cell, for each task.
    log: HashMap<CellId, BTreeMap<usize, TaskLog>>,
    /// The tasks that no task joined yet. A joined task is done: it makes no
    /// more accesses.
    live: BTreeSet<usize>,
    /// The last identity of an enum value.
    enum_ids: u64,
}

impl Oracle {
    /// Makes the clocks of tasks up to `t`. A new task starts at 1 in its own
    /// entry.
    fn ensure(&mut self, t: usize) {
        while self.clocks.len() <= t {
            let n = self.clocks.len();
            let mut v = vec![0; n + 1];
            v[n] = 1;
            self.clocks.push(v);
            self.live.insert(n);
        }
    }

    /// Returns what task `t` knows of the clock of task `u`.
    fn at(&self, t: usize, u: usize) -> u32 {
        self.clocks
            .get(t)
            .and_then(|v| v.get(u))
            .copied()
            .unwrap_or(0)
    }

    /// Joins the clock of task `from` into the clock of task `into`.
    fn merge(&mut self, into: usize, from: usize) {
        self.ensure(into.max(from));
        let src = self.clocks[from].clone();
        let dst = &mut self.clocks[into];
        if dst.len() < src.len() {
            dst.resize(src.len(), 0);
        }
        for (d, s) in dst.iter_mut().zip(&src) {
            *d = (*d).max(*s);
        }
    }

    /// Sets the running task.
    pub const fn set_task(&mut self, t: usize) {
        self.cur = t;
    }

    /// Task `parent` starts task `child`: the child sees each access of the
    /// parent before the start.
    pub fn spawn(&mut self, parent: usize, child: usize) {
        self.merge(child, parent);
        let own = &mut self.clocks[child];
        if own.len() <= child {
            own.resize(child + 1, 0);
        }
        own[child] = own[child].max(1);
        let p = &mut self.clocks[parent];
        if p.len() <= parent {
            p.resize(parent + 1, 0);
        }
        p[parent] += 1;
    }

    /// The running task sees that task `u` is done: it sees each access of `u`.
    pub fn join(&mut self, u: usize) {
        let t = self.cur;
        self.merge(t, u);
        if u != t {
            self.live.remove(&u);
        }
    }

    /// Returns true if the log of task `u` on a cell, with largest clock
    /// `last`, cannot find a race any more: `u` is done, and each task that
    /// can still make an access sees each access of `u` in the log. A task
    /// that starts later gets the clock of its parent, so it sees them too.
    fn forgotten(&self, u: usize, last: u32) -> bool {
        !self.live.contains(&u) && self.live.iter().all(|&w| self.at(w, u) >= last)
    }

    /// Records an access of the running task to `path` in `cell`, and finds a
    /// race with an access of another task that no join orders before it.
    pub fn access(&mut self, cell: CellId, path: &[u32], write: bool, what: &str) {
        let t = self.cur;
        self.ensure(t);
        // When the running task is the only task that no task joined, each
        // other task is done, and its accesses are ordered before this one
        // (a join merges the clocks, and the clocks of the joins chain to
        // this task). A task that starts later sees this access too. So the
        // access cannot be part of a race, and the log does not need it. A
        // deep recursion of one task then makes no log at all.
        if self.live.len() == 1 && self.live.contains(&t) {
            return;
        }
        let epoch = self.at(t, t);
        // The logs of done tasks that each task sees: they are dropped, so
        // the cost of an access does not grow with the number of done tasks.
        let mut stale = Vec::new();
        let race = self.log.get(&cell).and_then(|logs| {
            logs.iter().filter(|(&u, _)| u != t).find_map(|(&u, l)| {
                let known = self.at(t, u);
                if l.last <= known {
                    if self.forgotten(u, l.last) {
                        stale.push(u);
                    }
                    return None;
                }
                // A write overlaps each access; a read overlaps a write only.
                if let Some(p) = unordered(&l.writes, path, known) {
                    return Some((u, p, true));
                }
                let p = if write {
                    unordered(&l.reads, path, known)
                } else {
                    None
                };
                p.map(|p| (u, p, false))
            })
        });
        if let Some((u, p, wrote)) = race {
            let msg = format!(
                "oracle: data race: task {t} {} a {what} at {path:?}, and task {u} {} it at {p:?} with no join between",
                if write { "writes" } else { "reads" },
                if wrote { "wrote" } else { "read" },
            );
            self.flag(msg);
        }
        let logs = self.log.entry(cell).or_default();
        for u in stale {
            logs.remove(&u);
        }
        let l = logs.entry(t).or_default();
        l.last = l.last.max(epoch);
        let m = if write { &mut l.writes } else { &mut l.reads };
        m.insert(path.to_vec(), epoch);
    }

    /// Returns the identity of a new enum value (from 1).
    pub const fn next_enum_id(&mut self) -> u64 {
        self.enum_ids += 1;
        self.enum_ids
    }

    /// Notes a violation. The machine reports the first one.
    pub fn flag(&mut self, msg: impl Into<String>) {
        if self.violation.is_none() {
            self.violation = Some(msg.into());
        }
    }

    /// Notes that the scan of a frame found a live linear value after the
    /// cleanup chain of the frame ended (`docs/ir.md` 8.2): the chain does
    /// not finish each value of the frame.
    pub fn left_after_chain(&mut self, frame: &str) {
        self.flag(format!(
            "oracle: a live linear value is left after the cleanup chain of `{frame}`"
        ));
    }

    /// Takes the violation that the machine did not report yet.
    pub const fn take_violation(&mut self) -> Option<String> {
        self.violation.take()
    }

    /// Notes that the scope of local or temporary cell `c` ended.
    pub fn end_cell(&mut self, c: CellId) {
        self.ended.insert(c);
    }

    /// Returns true if the scope of cell `c` ended.
    pub fn ended(&self, c: CellId) -> bool {
        self.ended.contains(&c)
    }

    /// Notes that the heap dropped a struct value with linear record `id`.
    pub fn drop_lin(&mut self, id: usize) {
        self.dropped_lins.push(id);
    }

    /// Takes the linear records of the struct values that the heap dropped.
    pub fn take_dropped_lins(&mut self) -> Vec<usize> {
        std::mem::take(&mut self.dropped_lins)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_join_orders_the_accesses_of_two_tasks() {
        let mut o = Oracle::default();
        o.set_task(0);
        o.access(7, &[], true, "local");
        o.spawn(0, 1);
        o.set_task(1);
        // The child sees the write of its parent before the spawn.
        o.access(7, &[0], true, "local");
        assert!(o.take_violation().is_none());
        o.set_task(0);
        // The parent reads while the child can still run: a race.
        o.access(7, &[0], false, "local");
        assert!(o.take_violation().is_some());
        o.join(1);
        o.access(7, &[0], false, "local");
        assert!(o.take_violation().is_none());
        // Disjoint paths do not race.
        o.spawn(0, 2);
        o.set_task(2);
        o.access(7, &[1], true, "local");
        o.set_task(0);
        o.access(7, &[2], true, "local");
        assert!(o.take_violation().is_none());
    }

    #[test]
    fn a_race_after_many_accesses_is_found() {
        // Task 1 writes 300 paths of one cell. Task 2 then writes the last
        // path with no join between: a race also after more than 256 records
        // (I3-12).
        let mut o = Oracle::default();
        o.set_task(0);
        o.spawn(0, 1);
        o.spawn(0, 2);
        o.set_task(1);
        for i in 0..300 {
            o.access(9, &[i, 0], true, "buffer");
        }
        assert!(o.take_violation().is_none());
        o.set_task(2);
        o.access(9, &[299, 0], true, "buffer");
        let v = o.take_violation();
        assert!(
            v.as_deref().is_some_and(|m| m.contains("[299, 0]")),
            "{v:?}"
        );
        // A read of the whole cell overlaps each path.
        o.access(9, &[], false, "buffer");
        assert!(o.take_violation().is_some());
        // Each task keeps one record for each path and kind.
        let logs = &o.log[&9];
        assert_eq!(logs[&1].writes.len(), 300);
        assert_eq!(logs[&2].reads.len(), 1);
        // A read of another path of the parent after a join does not race.
        o.set_task(0);
        o.join(1);
        o.join(2);
        o.access(9, &[5], false, "buffer");
        o.access(9, &[], true, "buffer");
        assert!(o.take_violation().is_none());
    }

    #[test]
    fn the_log_forgets_a_joined_task_that_each_task_sees() {
        // Task 0 starts and joins one task after the other. Each task reads
        // the cell. After the join, task 0 is the only task that can make an
        // access, and it sees the reads: the log drops them.
        let mut o = Oracle::default();
        o.set_task(0);
        o.access(3, &[0], true, "buffer");
        for u in 1..100 {
            o.spawn(0, u);
            o.set_task(u);
            o.access(3, &[0], false, "buffer");
            o.set_task(0);
            o.join(u);
            o.access(3, &[0], true, "buffer");
        }
        assert!(o.take_violation().is_none());
        assert_eq!(o.log[&3].len(), 1, "{:?}", o.log[&3].keys());
        // A task that can still run and does not see a done task keeps its
        // log: task 101 races with the write of task 100.
        o.spawn(0, 100);
        o.spawn(0, 101);
        o.set_task(100);
        o.access(3, &[1], true, "buffer");
        o.set_task(0);
        o.join(100);
        o.access(3, &[2], false, "buffer");
        o.set_task(101);
        o.access(3, &[1], false, "buffer");
        assert!(o.take_violation().is_some());
    }

    #[test]
    fn the_only_live_task_makes_no_log() {
        // Before a spawn and after the join of each task, no access can race:
        // the log stays empty. A race between two live tasks is found.
        let mut o = Oracle::default();
        o.set_task(0);
        o.access(4, &[], true, "local");
        assert!(o.log.is_empty());
        o.spawn(0, 1);
        o.set_task(1);
        o.access(4, &[], true, "local");
        o.set_task(0);
        o.access(4, &[], false, "local");
        assert!(o.take_violation().is_some());
        o.join(1);
        let n = o.log.len();
        o.access(5, &[], true, "local");
        assert_eq!(o.log.len(), n);
        assert!(o.take_violation().is_none());
    }

    #[test]
    fn records_ended_cells_and_dropped_linear_values() {
        let mut o = Oracle::default();
        o.end_cell(3);
        assert!(o.ended(3) && !o.ended(4));
        o.drop_lin(5);
        assert_eq!(o.take_dropped_lins(), vec![5]);
        assert!(o.take_dropped_lins().is_empty());
        o.flag("first");
        o.flag("second");
        assert_eq!(o.take_violation().as_deref(), Some("first"));
    }
}
