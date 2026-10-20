//! The oracle: checks that make the interpreter a strict test oracle (OR11).
//!
//! The checks are off by default. [`RunOptions::oracle`](crate::RunOptions)
//! turns them on. With them, the machine reports a fault where a real machine
//! can do something that the design forbids, and the stock machine goes on:
//!
//! - an access to a freed cell or buffer (a dangling reference);
//! - a `Vec` moves its buffer on each `push`, `pop` and `clear`, as a real
//!   `Vec` can, so a reference into the old buffer dangles;
//! - a reference into a local whose scope ended is used;
//! - a live linear value goes away with no consume and no `on abort`, or is
//!   still live at the end of the run;
//! - two tasks access overlapping places, one of them writes, and no join
//!   orders them (a vector-clock race detector). Spawn, join, the end of a
//!   scope or a `fork` and unwinding are the points that order tasks;
//! - a task that the checker marks stealable reaches an `Rc`, a `Weak` or a
//!   `Scope`.
//!
//! An accepted program must not fault with these checks. The interpreter
//! program tests and the runs of the corpus turn them on.

use std::collections::{BTreeSet, HashMap};

use crate::value::CellId;

/// The most accesses that the race detector keeps for one cell.
const LOG_LIMIT: usize = 256;

/// One access of a task to a place of a cell.
#[derive(Clone, Debug)]
struct Access {
    /// The path in the cell.
    path: Vec<u32>,
    /// The task.
    task: usize,
    /// The clock of the task at the access.
    epoch: u32,
    /// True for a write.
    write: bool,
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
    /// The accesses of each cell.
    log: HashMap<CellId, Vec<Access>>,
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
    }

    /// Records an access of the running task to `path` in `cell`, and finds a
    /// race with an access of another task that no join orders before it.
    pub fn access(&mut self, cell: CellId, path: &[u32], write: bool, what: &str) {
        let t = self.cur;
        self.ensure(t);
        let epoch = self.at(t, t);
        let race = self.log.get(&cell).and_then(|recs| {
            recs.iter().find(|r| {
                let n = r.path.len().min(path.len());
                r.task != t
                    && (write || r.write)
                    && r.path[..n] == path[..n]
                    && r.epoch > self.at(t, r.task)
            })
        });
        if let Some(r) = race {
            let msg = format!(
                "oracle: data race: task {t} {} a {what} at {path:?}, and task {} {} it at {:?} with no join between",
                if write { "writes" } else { "reads" },
                r.task,
                if r.write { "wrote" } else { "read" },
                r.path
            );
            self.flag(msg);
        }
        let recs = self.log.entry(cell).or_default();
        if let Some(r) = recs
            .iter_mut()
            .find(|r| r.path == path && r.task == t && r.write == write)
        {
            r.epoch = epoch;
        } else if recs.len() < LOG_LIMIT {
            recs.push(Access {
                path: path.to_vec(),
                task: t,
                epoch,
                write,
            });
        }
    }

    /// Notes a violation. The machine reports the first one.
    pub fn flag(&mut self, msg: impl Into<String>) {
        if self.violation.is_none() {
            self.violation = Some(msg.into());
        }
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
