//! One test (or more) for each point of the dynamic semantics.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use weft_check::Checked;
use weft_interp::{
    run_analysis_main, run_main, run_tests, ErrorKind, RunOptions, RunOutcome, RuntimeError,
    SuspendReason, TaskEnd, TraceEvent,
};
use weft_sema::Options;

fn program(name: &str) -> String {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/programs")
        .join(format!("{name}.wf"));
    fs::read_to_string(p).unwrap()
}

fn check(src: &str) -> Checked {
    weft_check::check_source("t.wf", src, Options::default())
}

fn checked_ok(src: &str) -> Checked {
    let c = check(src);
    assert!(c.ok(), "the checker rejects the program: {:?}", c.codes());
    c
}

fn opts(seed: u64) -> RunOptions {
    RunOptions {
        seed,
        max_steps: Some(2_000_000),
        ..RunOptions::default()
    }
}

fn run(src: &str, o: &RunOptions) -> Result<RunOutcome, RuntimeError> {
    run_main(&checked_ok(src), o)
}

fn ok(src: &str, seed: u64) -> RunOutcome {
    match run(src, &opts(seed)) {
        Ok(o) => o,
        Err(e) => panic!("run failed: {e}\n{}", e.outcome.stdout),
    }
}

fn count<F: Fn(&TraceEvent) -> bool>(o: &RunOutcome, f: F) -> usize {
    o.trace.iter().filter(|e| f(e)).count()
}

// ---------------------------------------------------------------------------
// 1. Programs
// ---------------------------------------------------------------------------

#[test]
fn main_gets_env_capabilities() {
    let o = ok(
        "fn main(env: Env) / io {\n env.stdout.write(\"hi\")\n let v = Vec.new()\n v.push(\"a\")\n v.push(\"b\")\n env.stdout.write_all(v)\n}",
        0,
    );
    assert_eq!(o.stdout, "hi\na\nb\n");
}

#[test]
fn test_blocks_run_and_report() {
    let c = checked_ok("test \"one\" { print(1) }\ntest \"two\" { assert 1 == 2 }\n");
    let ts = run_tests(&c, &opts(0));
    assert_eq!(ts.len(), 2);
    assert!(ts[0].passed);
    assert_eq!(ts[0].outcome.stdout, "1\n");
    assert!(!ts[1].passed);
    assert!(ts[1]
        .message
        .as_deref()
        .unwrap()
        .contains("assertion failed"));
}

#[test]
fn missing_main_is_an_error() {
    let e = run("fn helper() {}", &opts(0)).unwrap_err();
    assert_eq!(e.kind, ErrorKind::NoMain);
}

// ---------------------------------------------------------------------------
// 2. Values and places
// ---------------------------------------------------------------------------

#[test]
fn element_references_mutate_in_place() {
    let o = ok(&program("places"), 0);
    assert_eq!(
        o.stdout,
        "10\nDied(1)\nentity 1 hp 0 unarmed\nentity 2 hp 40 weapon 3\n"
    );
}

#[test]
fn immovable_field_keeps_its_address() {
    let src = "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }\n\
        fn main() {\n let f = Frame { buf: [1, 2, 3, 4] }\n f.cur = &f.buf[2]\n f.buf[0] = 9\n print(f.cur)\n print(f.buf)\n}";
    assert_eq!(ok(src, 0).stdout, "3\n[9, 2, 3, 4]\n");
}

#[test]
fn closures_capture_by_reference() {
    let src = "fn main() {\n let n = 1\n let add = |x: u64| n + x\n n = 10\n print(add(5))\n}";
    assert_eq!(ok(src, 0).stdout, "15\n");
}

#[test]
fn moved_capture_moves_the_value() {
    let src = "struct Bag { items: Vec<u64> }\n\
        fn take(b: Bag) -> usize { b.items.len() }\n\
        fn main() {\n let b = Bag { items: [1, 2] }\n let f = || take(b)\n print(f())\n}";
    assert_eq!(ok(src, 0).stdout, "2\n");
}

#[test]
fn values_of_every_kind() {
    let o = ok(&program("values"), 0);
    assert!(o
        .stdout
        .starts_with("1 two\n(1, \"two\")\n12\n3\n2s 500ms 1500ms\n2\n"));
}

#[test]
fn integer_overflow_and_division_by_zero_are_errors() {
    let e = run(
        "fn main() { let x = 9223372036854775807\n print(x + 1) }",
        &opts(0),
    )
    .unwrap_err();
    assert!(e.message.contains("overflow"));
    let e = run("fn main() { let z = 0\n print(1 / z) }", &opts(0)).unwrap_err();
    assert!(e.message.contains("division by zero"));
    let e = run("fn main() { let v = [1]\n print(v[3]) }", &opts(0)).unwrap_err();
    assert!(e.message.contains("out of bounds"));
}

#[test]
fn unsigned_underflow_is_an_error() {
    let src = "struct C { n: u64 }\nfn main() {\n let c = C { n: 1 }\n c.n -= 1\n print(c.n)\n c.n -= 1\n}";
    let e = run(src, &opts(0)).unwrap_err();
    assert!(
        e.message
            .contains("unsigned underflow: field `n` would be -1"),
        "{e}"
    );
    assert_eq!(e.outcome.stdout, "0\n");
    let src = "fn f(x: u64) -> u64 { x }\nfn main() {\n let a = 2\n print(f(a - 3))\n}";
    let e = run(src, &opts(0)).unwrap_err();
    assert!(e.message.contains("parameter `x` would be -1"), "{e}");
    let src = "struct S { x: i64 }\nfn main() {\n let s = S { x: 0 }\n s.x = 0 - 5\n print(s.x)\n}";
    assert_eq!(ok(src, 0).stdout, "-5\n");
}

// ---------------------------------------------------------------------------
// 3. Effects and handlers
// ---------------------------------------------------------------------------

#[test]
fn handler_collects_log_lines() {
    assert_eq!(
        ok(&program("effects_log"), 0).stdout,
        "stepped 1 hp=9\nstepped 2 hp=19\n"
    );
}

#[test]
fn perform_reaches_the_lexical_handler() {
    // A closure uses the handlers where it was made. A call passes the caller's.
    let src = "effect Note { fn note(x: u64) }\n\
        fn emit() / Note { note(3) }\n\
        fn run(f: fn() / Note) / Note {\n\
            handle Note { fn note(x) { print(\"inner {x}\"); resume(()) } } in {\n f()\n note(2)\n emit()\n }\n}\n\
        fn main() {\n handle Note { fn note(x) { print(\"outer {x}\"); resume(()) } } in {\n let f = || note(1)\n run(f)\n }\n}";
    assert_eq!(ok(src, 0).stdout, "outer 1\ninner 2\ninner 3\n");
}

#[test]
fn multi_shot_choose_explores_both_branches() {
    assert_eq!(ok(&program("multi_choose"), 0).stdout, "[1, 2]\n23\n");
}

#[test]
fn once_resume_twice_is_a_runtime_error() {
    let src = program("once_twice");
    let c = check(&src);
    assert!(c.codes().contains(&"W0501".to_string()));
    let e = run_main(&c, &opts(0)).unwrap_err();
    assert_eq!(e.kind, ErrorKind::Fault);
    assert!(e.message.contains("`once` continuation was resumed twice"));
    // The same guard, on an analysis that the checker never saw.
    let a = weft_sema::analyze_source(&src, Options::default()).unwrap();
    let e = run_analysis_main(&a, &opts(0)).unwrap_err();
    assert!(e.message.contains("resumed twice"));
}

#[test]
fn unhandled_user_effect_is_an_error() {
    let c = check("effect Note { fn note(x: u64) }\nfn main() { note(1) }");
    let e = run_main(&c, &opts(0)).unwrap_err();
    assert!(e.message.contains("no handler for `Note.note`"));
}

#[test]
fn partial_handler_forwards_other_operations() {
    let src = "fn main() / io {\n handle Log { fn info(m) { print(\"caught {m}\"); resume(()) } } in {\n log.info(\"a\")\n log.warn(\"b\")\n }\n}";
    let o = ok(src, 0);
    assert_eq!(o.stdout, "caught a\n");
    assert_eq!(o.stderr, "warn: b\n");
}

// ---------------------------------------------------------------------------
// 4. Abort and `on abort`
// ---------------------------------------------------------------------------

#[test]
fn abort_runs_on_abort_once() {
    let o = ok(&program("abort_on_abort"), 0);
    assert_eq!(o.stdout, "commit 1\nfailed: too much\nrollback 2\ndone\n");
    assert_eq!(o.stdout.matches("rollback").count(), 1);
    assert_eq!(
        count(
            &o,
            |e| matches!(e, TraceEvent::OnAbort { ty, .. } if ty == "Tx")
        ),
        1
    );
}

#[test]
fn normal_path_runs_no_on_abort() {
    let src = program("abort_on_abort").replace("transfer(2, 500)", "transfer(2, 5)");
    let o = ok(&src, 0);
    assert_eq!(o.stdout, "commit 1\ncommit 2\nnot reached\ndone\n");
    assert_eq!(count(&o, |e| matches!(e, TraceEvent::OnAbort { .. })), 0);
}

#[test]
fn linear_value_moved_into_a_call_is_aborted_by_the_callee() {
    // `keep` owns the value when it fails: its frame runs `on abort`, once.
    let src = "linear struct Tx { id: u64 }\n on abort = undo\n\
        fn undo(t: Tx) { let Tx(id) = t\n print(\"undo {id}\") }\n\
        fn keep(t: Tx) / fail { fail(\"no\")\n let Tx(i) = t }\n\
        fn main() {\n handle Fail { fn fail(m) { print(m) } } in {\n let t = Tx { id: 4 }\n keep(t)\n }\n}";
    assert_eq!(ok(src, 0).stdout, "no\nundo 4\n");
}

// ---------------------------------------------------------------------------
// 5. Root handlers
// ---------------------------------------------------------------------------

#[test]
fn root_log_writes_stderr_and_root_fail_fails_main() {
    let e = run(&program("root_handlers"), &opts(0)).unwrap_err();
    assert_eq!(e.kind, ErrorKind::Failed);
    assert_eq!(e.message, "boom");
    assert!(e.span.is_some());
    assert_eq!(e.outcome.stdout, "rollback 3\n");
    assert_eq!(e.outcome.stderr, "info: starting\nwarn: careful\n");
}

#[test]
fn clock_sleep_suspends_on_virtual_time() {
    let src = "fn main() / io {\n let t0 = Clock.now()\n sleep(3.s)\n Clock.sleep(500.ms)\n print(t0, Clock.now())\n}";
    let o = ok(src, 0);
    assert_eq!(o.stdout, "0s 3500ms\n");
    assert_eq!(
        count(&o, |e| matches!(
            e,
            TraceEvent::Suspend {
                reason: SuspendReason::Sleep,
                ..
            }
        )),
        2
    );
}

#[test]
fn blocking_pool_counts_calls() {
    let o = ok(&program("blocking"), 0);
    assert_eq!(o.blocking_calls, 2);
    assert_eq!(
        count(
            &o,
            |e| matches!(e, TraceEvent::BlockingCall { name, .. } if name == "db_step")
        ),
        2
    );
}

#[test]
fn yields_of_standard_effects_suspend() {
    let src = "fn main() / io {\n Async.suspend()\n Net.net_poll()\n print(\"after\")\n}";
    let o = ok(src, 0);
    assert_eq!(o.stdout, "after\n");
    assert_eq!(
        count(&o, |e| matches!(
            e,
            TraceEvent::Suspend {
                reason: SuspendReason::Yield,
                ..
            }
        )),
        2
    );
}

#[test]
fn no_runtime_has_no_root_handlers() {
    let src = "// weft: no-runtime\nfn main() / clock { sleep(1.s) }";
    let c = weft_check::check_source(
        "t.wf",
        src,
        Options {
            library: false,
            no_runtime: true,
        },
    );
    let o = RunOptions {
        no_runtime: true,
        ..opts(0)
    };
    let e = run_main(&c, &o).unwrap_err();
    assert!(e.message.contains("no runtime"));
}

// ---------------------------------------------------------------------------
// 6. Tasks, scopes, cancellation and timeouts
// ---------------------------------------------------------------------------

#[test]
fn scope_join_order_with_a_fixed_seed() {
    let src = program("scope_join");
    let a = ok(&src, 0);
    assert_eq!(a.stdout, "a\nc\nb\n6\n");
    assert_eq!(a, ok(&src, 0));
    // Other seeds may interleave differently; the result is the same.
    let mut orders = BTreeSet::new();
    for seed in 0..32 {
        let o = ok(&src, seed);
        assert!(o.stdout.ends_with("6\n"));
        orders.insert(o.stdout);
    }
    assert!(orders.len() > 1, "every seed gave the same order");
}

#[test]
fn failing_child_cancels_its_sleeping_sibling() {
    let o = ok(&program("cancel_sibling"), 0);
    assert_eq!(o.stdout, "release 7\ncaught: boom\nafter\n");
    // Task 1 sleeps with a live `Lease`; task 2 fails.
    assert!(o.trace.contains(&TraceEvent::Cancel { task: 1 }));
    assert!(o.trace.contains(&TraceEvent::OnAbort {
        task: 1,
        ty: "Lease".into()
    }));
    assert!(o.trace.contains(&TraceEvent::Finish {
        task: 1,
        end: TaskEnd::Cancelled
    }));
    assert!(o.trace.contains(&TraceEvent::Finish {
        task: 2,
        end: TaskEnd::Failed("boom".into())
    }));
    let cancel = o
        .trace
        .iter()
        .position(|e| *e == TraceEvent::Cancel { task: 1 });
    let fail = o.trace.iter().position(|e| {
        *e == TraceEvent::Finish {
            task: 2,
            end: TaskEnd::Failed("boom".into()),
        }
    });
    assert!(fail < cancel);
}

#[test]
fn failure_propagates_to_the_scope_owner() {
    let src = "fn main() / io, fail {\n scope { s =>\n let a = s.spawn(|| fail(\"child\"))\n let b = s.spawn(|| sleep(5.s))\n b.join()\n a.join()\n }\n print(\"no\")\n}";
    let e = run(src, &opts(0)).unwrap_err();
    assert_eq!(e.kind, ErrorKind::Failed);
    assert_eq!(e.message, "child");
    assert!(e.outcome.stdout.is_empty());
}

#[test]
fn handler_abort_cancels_a_running_scope() {
    let o = ok(&program("scope_abort"), 0);
    assert_eq!(o.stdout, "caught abort scope\nend\n");
    assert!(o.trace.contains(&TraceEvent::Cancel { task: 1 }));
    assert!(o.trace.contains(&TraceEvent::Finish {
        task: 1,
        end: TaskEnd::Cancelled
    }));
    assert!(o.trace.contains(&TraceEvent::OnAbort {
        task: 0,
        ty: "Task".into()
    }));
}

#[test]
fn task_abort_unwinds_an_unresumed_continuation() {
    let e = run(&program("clause_abort"), &opts(0)).unwrap_err();
    assert_eq!(e.message, "in clause");
    assert_eq!(e.outcome.stdout, "undo 9\n");
}

#[test]
fn failing_fork_branch_cancels_the_other() {
    let e = run(&program("fork_fail"), &opts(0)).unwrap_err();
    assert_eq!(e.message, "left");
}

#[test]
fn multi_shot_copies_owned_heap_data() {
    let o = ok(&program("multi_heap"), 0);
    assert_eq!(o.stdout, "252\n[63, 32, 42, 11, 52, 21, 31, 0]\n");
    assert_eq!(o.leaked_rc, 0);
}

#[test]
fn fork_returns_a_tuple_of_results() {
    assert_eq!(ok(&program("fork"), 0).stdout, "150\n156\n");
}

#[test]
fn with_timeout_aborts_a_slow_block() {
    let o = ok(&program("timeout"), 0);
    assert_eq!(o.stdout, "fast: 7\nguard 1 aborted\nfailed: timeout\nend\n");
    assert_eq!(count(&o, |e| matches!(e, TraceEvent::Timeout { .. })), 1);
    assert_eq!(
        count(
            &o,
            |e| matches!(e, TraceEvent::OnAbort { ty, .. } if ty == "Guard")
        ),
        1
    );
}

#[test]
fn timeout_without_handler_fails_main() {
    let src = "fn main() / io, fail {\n with_timeout(1.ms) { sleep(1.s) }\n}";
    let e = run(src, &opts(0)).unwrap_err();
    assert_eq!(e.message, "timeout");
}

#[test]
fn join_of_a_spawned_value() {
    let src = "fn main() / io {\n let r = scope { s =>\n let t = s.spawn(|| 40)\n t.join() + 2\n }\n print(r)\n}";
    assert_eq!(ok(src, 0).stdout, "42\n");
}

#[test]
fn detached_task_still_finishes_in_its_scope() {
    let src = "fn main() / io {\n scope { s =>\n let t = s.spawn(|| { sleep(1.s); print(\"bg\") })\n t.detach()\n print(\"fg\")\n }\n print(\"end\")\n}";
    assert_eq!(ok(src, 0).stdout, "fg\nbg\nend\n");
}

// ---------------------------------------------------------------------------
// 7. The scheduler
// ---------------------------------------------------------------------------

#[test]
fn preemption_lets_a_second_task_run() {
    let src = program("preempt");
    // One worker: the spinner runs first. Its quantum expires at a back-edge.
    let one = RunOptions {
        workers: 1,
        ..opts(0)
    };
    let o = run(&src, &one).unwrap();
    assert_eq!(o.stdout, "second ran\nspinner done\n");
    assert!(o.trace.contains(&TraceEvent::Preempt { task: 1 }));
    // With no preemption, the spinner finishes first.
    let never = RunOptions {
        quantum: u64::MAX,
        ..one
    };
    let o = run(&src, &never).unwrap();
    assert_eq!(o.stdout, "spinner done\nsecond ran\n");
    assert_eq!(count(&o, |e| matches!(e, TraceEvent::Preempt { .. })), 0);
}

#[test]
fn only_stealable_tasks_move_between_workers() {
    let src = program("steal");
    let mut steals = 0;
    for seed in 0..16 {
        let o = ok(&src, seed);
        assert_eq!(o.stdout, "24856\n");
        assert!(o.trace.contains(&TraceEvent::Spawn {
            task: 1,
            parent: 0,
            worker: 0,
            stealable: true
        }));
        assert!(o.trace.contains(&TraceEvent::Spawn {
            task: 2,
            parent: 0,
            worker: 0,
            stealable: false
        }));
        for e in &o.trace {
            match e {
                TraceEvent::Steal { task, .. } => {
                    assert_ne!(*task, 2, "the pinned task was stolen");
                    steals += 1;
                }
                TraceEvent::Run { task: 2, worker } => assert_eq!(*worker, 0),
                _ => {}
            }
        }
    }
    assert!(steals > 0, "no task was ever stolen");
}

#[test]
fn same_seed_gives_the_same_trace() {
    for name in ["cancel_sibling", "steal", "scope_join", "timeout", "fork"] {
        let src = program(name);
        for seed in [1, 9, 77] {
            assert_eq!(ok(&src, seed), ok(&src, seed), "{name} with seed {seed}");
        }
    }
}

#[test]
fn step_limit_stops_a_loop() {
    let o = RunOptions {
        max_steps: Some(1000),
        ..opts(0)
    };
    let e = run("fn main() { loop { } }", &o).unwrap_err();
    assert_eq!(e.kind, ErrorKind::StepLimit);
}

// ---------------------------------------------------------------------------
// 8. Deterministic simulation
// ---------------------------------------------------------------------------

#[test]
fn design_doc_simulation_test_passes() {
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs/10_sim.wf");
    let c = checked_ok(&fs::read_to_string(p).unwrap());
    let ts = run_tests(&c, &opts(0));
    assert_eq!(ts.len(), 1);
    assert!(ts[0].passed, "{:?}", ts[0].message);
    let t = &ts[0].outcome.trace;
    assert!(t.contains(&TraceEvent::SimStart { seed: 42 }));
    assert!(t.contains(&TraceEvent::Partition {
        a: vec![0, 1],
        b: vec![2, 3, 4]
    }));
    assert!(t.contains(&TraceEvent::Advance { now: 30_000 }));
    assert!(t.contains(&TraceEvent::SimEnd));
}

#[test]
fn simulation_replaces_root_handlers() {
    let src = "test \"r\" {\n sim.run(seed: 5) {\n let a = random()\n sleep(2.s)\n print(a % 1000, Clock.now())\n }\n}";
    let c = checked_ok(src);
    let first = run_tests(&c, &opts(0));
    let other = run_tests(&c, &opts(123));
    assert!(first[0].passed);
    // The simulation seed, not the run seed, gives the random values.
    assert_eq!(first[0].outcome.stdout, other[0].outcome.stdout);
    assert!(first[0].outcome.stdout.ends_with(" 2s\n"));
    let five = src.to_string();
    let six = five.replace("seed: 5", "seed: 6");
    let c6 = checked_ok(&six);
    assert_ne!(
        run_tests(&c6, &opts(0))[0].outcome.stdout,
        first[0].outcome.stdout
    );
}

#[test]
fn simulation_runs_tasks_on_virtual_time() {
    let c = checked_ok(&program("sim"));
    let ts = run_tests(&c, &opts(0));
    let t = ts
        .iter()
        .find(|t| t.name == "tasks in a simulation")
        .unwrap();
    assert_eq!(t.outcome.stdout, "early\nlate\n");
}

// ---------------------------------------------------------------------------
// 9. Rc, Weak and leaks
// ---------------------------------------------------------------------------

#[test]
fn rc_cycle_leaks_and_is_counted() {
    let o = ok(&program("rc_cycle"), 0);
    assert_eq!(o.stdout, "gone\nalive 1\n");
    assert_eq!(o.leaked_rc, 2);
}

#[test]
fn rc_without_cycle_frees_everything() {
    let src = "struct Node { v: u64 }\nfn main() {\n let a = Rc.new(Node { v: 1 })\n let b = a.clone()\n print(b.v)\n}";
    assert_eq!(ok(src, 0).leaked_rc, 0);
}
