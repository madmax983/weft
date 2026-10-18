//! Scheduler trace events.
//!
//! The machine records one event for each scheduling decision and each change of
//! task state. Tests compare traces to check determinism and scheduling rules.

use std::fmt;

/// Why a task stopped running before it finished.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SuspendReason {
    /// `sleep(d)` or `Clock.sleep(d)`.
    Sleep,
    /// `t.join()` on a task that is not finished.
    Join(usize),
    /// The end of a `scope` waits for its children.
    Scope,
    /// `fork` waits for its branches.
    Fork,
    /// A blocking call runs on the blocking pool.
    Blocking,
    /// A yield: `Async.suspend()` or a poll operation of a standard effect.
    Yield,
    /// Unwinding waits for cancelled children.
    Children,
    /// `http.serve` waits for a connection.
    Accept,
}

/// How a task finished.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TaskEnd {
    /// The task returned a value.
    Ok,
    /// The task failed with a message.
    Failed(String),
    /// The task was cancelled.
    Cancelled,
}

/// One trace event.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TraceEvent {
    /// A task was spawned. Task 0 is the root task.
    Spawn {
        /// The new task.
        task: usize,
        /// The task that spawned it.
        parent: usize,
        /// The worker queue that got the task.
        worker: usize,
        /// The checker marked the task stealable.
        stealable: bool,
    },
    /// A worker runs a task for one quantum.
    Run {
        /// The task.
        task: usize,
        /// The worker.
        worker: usize,
    },
    /// An idle worker took a task from another worker.
    Steal {
        /// The task.
        task: usize,
        /// The worker that had the task.
        from: usize,
        /// The idle worker.
        to: usize,
    },
    /// A task stopped at a suspension point.
    Suspend {
        /// The task.
        task: usize,
        /// The reason.
        reason: SuspendReason,
    },
    /// A suspended task became ready again.
    Resume {
        /// The task.
        task: usize,
    },
    /// The quantum of a task expired at a loop back-edge.
    Preempt {
        /// The task.
        task: usize,
    },
    /// A task got a cancellation request.
    Cancel {
        /// The task.
        task: usize,
    },
    /// Unwinding ran `on abort` for a live linear value.
    OnAbort {
        /// The task that unwinds.
        task: usize,
        /// The type of the linear value.
        ty: String,
    },
    /// A blocking call ran on the blocking pool.
    BlockingCall {
        /// The task.
        task: usize,
        /// The function.
        name: String,
        /// The pool thread.
        thread: usize,
    },
    /// A `with_timeout` deadline passed.
    Timeout {
        /// The task.
        task: usize,
    },
    /// `sim.run` started a simulation.
    SimStart {
        /// The seed.
        seed: u64,
    },
    /// The simulation ended.
    SimEnd,
    /// The simulated network was partitioned.
    Partition {
        /// One side.
        a: Vec<u64>,
        /// The other side.
        b: Vec<u64>,
    },
    /// The simulated network was healed.
    Heal,
    /// The virtual clock moved forward.
    Advance {
        /// The new time in milliseconds.
        now: u64,
    },
    /// A task finished.
    Finish {
        /// The task.
        task: usize,
        /// How it finished.
        end: TaskEnd,
    },
}

impl fmt::Display for TraceEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Spawn {
                task,
                parent,
                worker,
                stealable,
            } => write!(
                f,
                "spawn t{task} from t{parent} on w{worker}{}",
                if *stealable {
                    " (stealable)"
                } else {
                    " (pinned)"
                }
            ),
            Self::Run { task, worker } => write!(f, "run t{task} on w{worker}"),
            Self::Steal { task, from, to } => write!(f, "steal t{task} w{from} -> w{to}"),
            Self::Suspend { task, reason } => write!(f, "suspend t{task}: {reason:?}"),
            Self::Resume { task } => write!(f, "resume t{task}"),
            Self::Preempt { task } => write!(f, "preempt t{task}"),
            Self::Cancel { task } => write!(f, "cancel t{task}"),
            Self::OnAbort { task, ty } => write!(f, "on abort t{task}: {ty}"),
            Self::BlockingCall { task, name, thread } => {
                write!(f, "blocking t{task}: {name} on pool thread {thread}")
            }
            Self::Timeout { task } => write!(f, "timeout t{task}"),
            Self::SimStart { seed } => write!(f, "sim start seed {seed}"),
            Self::SimEnd => write!(f, "sim end"),
            Self::Partition { a, b } => write!(f, "partition {a:?} | {b:?}"),
            Self::Heal => write!(f, "heal"),
            Self::Advance { now } => write!(f, "clock {now}ms"),
            Self::Finish { task, end } => write!(f, "finish t{task}: {end:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn events_display() {
        let evs = [
            TraceEvent::Spawn {
                task: 1,
                parent: 0,
                worker: 0,
                stealable: true,
            },
            TraceEvent::Spawn {
                task: 2,
                parent: 0,
                worker: 0,
                stealable: false,
            },
            TraceEvent::Run { task: 1, worker: 2 },
            TraceEvent::Steal {
                task: 1,
                from: 0,
                to: 2,
            },
            TraceEvent::Suspend {
                task: 1,
                reason: SuspendReason::Sleep,
            },
            TraceEvent::Resume { task: 1 },
            TraceEvent::Preempt { task: 1 },
            TraceEvent::Cancel { task: 1 },
            TraceEvent::OnAbort {
                task: 1,
                ty: "Tx".into(),
            },
            TraceEvent::BlockingCall {
                task: 1,
                name: "f".into(),
                thread: 0,
            },
            TraceEvent::Timeout { task: 1 },
            TraceEvent::SimStart { seed: 4 },
            TraceEvent::SimEnd,
            TraceEvent::Partition {
                a: vec![0],
                b: vec![1],
            },
            TraceEvent::Heal,
            TraceEvent::Advance { now: 5 },
            TraceEvent::Finish {
                task: 1,
                end: TaskEnd::Ok,
            },
        ];
        let text: Vec<String> = evs.iter().map(ToString::to_string).collect();
        assert_eq!(text[0], "spawn t1 from t0 on w0 (stealable)");
        assert_eq!(text[1], "spawn t2 from t0 on w0 (pinned)");
        assert_eq!(text[3], "steal t1 w0 -> w2");
        assert!(text.iter().all(|t| !t.is_empty()));
    }
}
