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
    // The result of `a - 3` has the type `u64` of the parameter: the check of
    // the result stops the run before the call (RR14).
    let src = "fn f(x: u64) -> u64 { x }\nfn main() {\n let a = 2\n print(f(a - 3))\n}";
    let e = run(src, &opts(0)).unwrap_err();
    assert!(
        e.message
            .contains("integer underflow: -1 does not fit in `u64`"),
        "{e}"
    );
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
    assert!(c.codes().iter().any(|x| *x == "W0501"));
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
            ..Options::default()
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
fn child_failure_goes_to_the_handlers_of_the_scope() {
    // On each seed and worker count: a handler inside the scope body does not
    // get the failure of a child, and the scope does not return normally.
    let src = program("child_fail_lexical");
    let c = checked_ok(&src);
    let want = "main handler: child failed\nmain handler: child failed\nouter handler: child failed\nclause done\nscope handler: child failed\nend\n";
    for seed in 0..6 {
        for workers in [1, 2, 4] {
            let o = run_main(
                &c,
                &RunOptions {
                    workers,
                    ..opts(seed)
                },
            )
            .unwrap();
            assert_eq!(o.stdout, want, "seed {seed}, workers {workers}");
        }
    }
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

// ---------------------------------------------------------------------------
// 10. The ops of the IR compiler (`docs/ir.md` 8.4)
// ---------------------------------------------------------------------------

mod ir_ops {
    use std::collections::BTreeSet;
    use std::rc::Rc;

    use weft_interp::code::{
        CapHold, ClauseSpec, Code, CodeKind, HandleSpec, Op, UnwindStep, VarRef,
    };
    use weft_interp::compile::{Compiler, Exports};
    use weft_interp::runtime::Runtime;
    use weft_interp::{run_runtime_main, RunOptions, RunOutcome, RuntimeError};
    use weft_sema::program::ItemRef;
    use weft_sema::{AdtId, Options};
    use weft_syntax::ast::Span;

    const SRC: &str = "enum E { A, B(u64) }\nlinear struct T { x: u64 }\n\
        linear struct U { x: u64 }\n    on abort = undo\n\
        fn undo(u: U) { let U(x) = u\n print(\"undo\", x) }\n\
        effect Ask { fn ask() -> u64 }\nfn main() {}";

    /// Runs `main` with hand-made code: `ops`, with `slots` slots, of which
    /// the last `temps` hold temporary cells.
    fn run_ops(ops: Vec<Op>, slots: u32, temps: u32) -> Result<RunOutcome, RuntimeError> {
        run_units(ops, slots, temps, Vec::new())
    }

    /// The id of the first code unit that `run_units` adds.
    fn first_extra_unit() -> usize {
        let a = weft_sema::analyze_source(SRC, Options::default()).unwrap();
        Compiler::compile(&a.program, &a.sigs, &Exports::default())
            .codes
            .len()
    }

    /// A closure code unit with hand-made code and `params` parameters.
    fn closure_unit(ops: Vec<Op>, slots: u32, params: u32) -> Code {
        unit(CodeKind::Closure, ops, slots, params)
    }

    /// A code unit of `kind` with hand-made code and `params` parameters.
    fn unit(kind: CodeKind, ops: Vec<Op>, slots: u32, params: u32) -> Code {
        let n = ops.len();
        Code {
            name: "closure".into(),
            kind,
            ops,
            spans: vec![Span::default(); n],
            n_slots: slots,
            n_params: params,
            unit: 0,
            temp_slots: 0,
            locs: Vec::new(),
            pads: Vec::new(),
        }
    }

    /// Runs `main` as `run_ops` does, with the code units `extra` after the
    /// code units of the program.
    fn run_units(
        ops: Vec<Op>,
        slots: u32,
        temps: u32,
        extra: Vec<Code>,
    ) -> Result<RunOutcome, RuntimeError> {
        run_code(ops, slots, temps, Vec::new(), extra)
    }

    /// Runs `main` as `run_units` does. `pads` is the landing-pad table of
    /// `main` (`Code::pads`).
    fn run_code(
        ops: Vec<Op>,
        slots: u32,
        temps: u32,
        pads: Vec<(usize, usize)>,
        extra: Vec<Code>,
    ) -> Result<RunOutcome, RuntimeError> {
        let a = weft_sema::analyze_source(SRC, Options::default()).unwrap();
        let mut compiled = Compiler::compile(&a.program, &a.sigs, &Exports::default());
        let Some(ItemRef::Fn(f)) = a.program.mods[a.program.root].items.get("main").copied() else {
            panic!("no main");
        };
        let id = compiled.fn_code[f.index()].unwrap();
        let n = ops.len();
        compiled.codes[id] = Rc::new(Code {
            name: "main".into(),
            kind: CodeKind::Fn(f),
            ops,
            spans: vec![Span::default(); n],
            n_slots: slots,
            n_params: 0,
            unit: 0,
            temp_slots: temps,
            locs: Vec::new(),
            pads,
        });
        compiled.codes.extend(extra.into_iter().map(Rc::new));
        let rt = Runtime::with_code(&a.program, &a.sigs, BTreeSet::new(), compiled);
        let opts = RunOptions {
            max_steps: Some(10_000),
            oracle: true,
            ..RunOptions::default()
        };
        run_runtime_main(&rt, &opts)
    }

    fn adt(name: &str) -> AdtId {
        let a = weft_sema::analyze_source(SRC, Options::default()).unwrap();
        AdtId(a.program.adts.iter().position(|d| d.name == name).unwrap())
    }

    const fn var(s: u32) -> Op {
        Op::Var(VarRef::Local(s))
    }

    /// The ops that print the value of the place on top, then return `()`.
    fn print_end() -> Vec<Op> {
        vec![Op::Read, Op::Print(1), Op::Pop, Op::Unit, Op::Return]
    }

    fn out(ops: Vec<Op>, slots: u32, temps: u32) -> String {
        match run_ops(ops, slots, temps) {
            Ok(o) => o.stdout,
            Err(e) => panic!("run failed: {e}"),
        }
    }

    fn fault(ops: Vec<Op>, slots: u32, temps: u32) -> String {
        run_ops(ops, slots, temps).unwrap_err().message
    }

    #[test]
    fn part_names_a_part_of_a_value() {
        let mut ops = vec![
            Op::Int(1),
            Op::Int(2),
            Op::Tuple(2),
            Op::Bind(0),
            var(0),
            Op::Part(1),
        ];
        ops.extend(print_end());
        assert_eq!(out(ops, 1, 0), "2\n");
        let ops = vec![Op::Int(1), Op::Tuple(1), Op::Bind(0), var(0), Op::Part(3)];
        assert!(fault(ops, 1, 0).contains("no part 3"));
    }

    #[test]
    fn deref_follows_a_reference_and_keeps_a_slice() {
        let mut ops = vec![Op::Int(7), Op::Bind(0), var(0), Op::Borrow, Op::Bind(1)];
        ops.extend([var(1), Op::Deref]);
        ops.extend(print_end());
        assert_eq!(out(ops, 2, 0), "7\n");
        // `(*s)` of a slice `s` is the slice: `Len` reads its range there.
        let mut ops = vec![
            Op::Int(1),
            Op::Int(2),
            Op::Int(3),
            Op::MakeVec(3),
            Op::Bind(0),
        ];
        ops.extend([
            var(0),
            Op::BorrowAll,
            Op::Bind(1),
            var(1),
            Op::Deref,
            Op::Len,
        ]);
        ops.extend([Op::Print(1), Op::Pop, Op::Unit, Op::Return]);
        assert_eq!(out(ops, 2, 0), "3\n");
        let ops = vec![Op::Int(7), Op::Bind(0), var(0), Op::Deref];
        assert!(fault(ops, 1, 0).contains("a pointer is needed"));
    }

    #[test]
    fn len_counts_the_elements() {
        let mut ops = vec![
            Op::Int(1),
            Op::Int(2),
            Op::MakeVec(2),
            Op::Bind(0),
            var(0),
            Op::Len,
        ];
        ops.extend([Op::Print(1), Op::Pop, Op::Unit, Op::Return]);
        assert_eq!(out(ops, 1, 0), "2\n");
    }

    #[test]
    fn tag_reads_the_variant() {
        let e = adt("E");
        let mut ops = vec![
            Op::Int(5),
            Op::MakeEnum {
                adt: e,
                variant: 1,
                n: 1,
            },
            Op::Bind(0),
            var(0),
            Op::Tag,
        ];
        ops.extend([Op::Print(1), Op::Pop, Op::Unit, Op::Return]);
        assert_eq!(out(ops, 1, 0), "1\n");
    }

    #[test]
    fn jump_table_jumps_to_the_arm_of_the_value() {
        for (v, want) in [
            (Op::Int(2), "two\n"),
            (Op::Int(9), "other\n"),
            (Op::Bool(true), "one\n"),
        ] {
            let ops = vec![
                v,
                Op::JumpTable {
                    arms: vec![(1, 2), (2, 6)],
                    otherwise: 10,
                },
                Op::Str("one".into()),
                Op::Print(1),
                Op::Pop,
                Op::Jump(13),
                Op::Str("two".into()),
                Op::Print(1),
                Op::Pop,
                Op::Jump(13),
                Op::Str("other".into()),
                Op::Print(1),
                Op::Pop,
                Op::Unit,
                Op::Return,
            ];
            assert_eq!(out(ops, 0, 0), want);
        }
    }

    #[test]
    fn bounds_faults_at_an_index_past_the_end() {
        let base = vec![Op::Int(4), Op::MakeVec(1), Op::Bind(0)];
        let mut ops = base.clone();
        ops.extend([var(0), Op::Int(0), Op::Bounds, Op::Unit, Op::Return]);
        assert_eq!(out(ops, 1, 0), "");
        let mut ops = base;
        ops.extend([var(0), Op::Int(1), Op::Bounds, Op::Unit, Op::Return]);
        assert!(fault(ops, 1, 0).contains("index 1 is out of bounds (length 1)"));
    }

    #[test]
    fn take_moves_the_value_out_also_a_copy_value() {
        // `Read` copies a copy value; `Take` (a `move` of the IR) leaves no
        // value.
        let mut ops = vec![
            Op::Int(4),
            Op::Bind(0),
            var(0),
            Op::Take,
            Op::Print(1),
            Op::Pop,
        ];
        ops.push(var(0));
        ops.extend(print_end());
        let e = run_ops(ops, 1, 0).unwrap_err();
        assert_eq!(e.outcome.stdout, "4\n");
        assert!(
            e.message.contains("used after it was moved"),
            "{}",
            e.message
        );
    }

    #[test]
    fn drop_place_drops_the_value_and_leaves_no_value() {
        let mut ops = vec![
            Op::Int(4),
            Op::MakeVec(1),
            Op::Bind(0),
            var(0),
            Op::DropPlace,
        ];
        ops.push(var(0));
        ops.extend(print_end());
        assert!(fault(ops, 1, 0).contains("used after it was moved"));
    }

    #[test]
    fn consume_finishes_the_linear_record() {
        let t = adt("T");
        let base = vec![
            Op::Int(1),
            Op::MakeStruct {
                adt: t,
                fields: vec![0],
                total: 1,
            },
            Op::Bind(0),
            var(0),
            Op::Consume,
        ];
        let mut ops = base.clone();
        ops.extend([Op::Unit, Op::Return]);
        // The oracle finds no live linear value at the end.
        assert_eq!(out(ops, 1, 0), "");
        let mut ops = base;
        ops.extend([var(0), Op::Consume, Op::Unit, Op::Return]);
        assert!(fault(ops, 1, 0).contains("consumed twice"));
    }

    #[test]
    fn end_temp_ends_the_temporary_cell() {
        // Slot 1 is a temporary cell: `Live`, a value, a borrow into it,
        // then `Dead`. A read through the reference after it dangles.
        let mut ops = vec![
            Op::LiveTemp(1),
            Op::Int(4),
            Op::MakeVec(1),
            var(1),
            Op::Store,
        ];
        ops.extend([var(1), Op::Borrow, Op::Bind(0), var(0), Op::Deref, Op::Len]);
        ops.extend([
            Op::Print(1),
            Op::Pop,
            Op::EndTemp(1),
            var(0),
            Op::Deref,
            Op::Len,
        ]);
        ops.extend([Op::Print(1), Op::Pop, Op::Unit, Op::Return]);
        let e = run_ops(ops, 2, 1).unwrap_err();
        assert_eq!(e.outcome.stdout, "1\n");
        assert!(e.message.contains("dangling"), "{}", e.message);
        // After `Dead` the slot has no cell.
        let ops = vec![Op::LiveTemp(0), Op::EndTemp(0), var(0), Op::Read];
        assert!(fault(ops, 1, 1).contains("before it has a value"));
    }

    #[test]
    fn make_closure_ir_shares_kept_cells_and_owns_the_other_captures() {
        // Slot 0 is `x`, slot 1 is a `Vec` `v`, slot 2 is the closure. The
        // closure shares the cell of `x` (`Kept`), takes `v` (`ByMove`) and
        // holds `&x` (`ByRef`). After a write of `x`, the closure reads 5
        // through the shared cell and through the reference, and the `Vec`
        // that it took.
        let code = first_extra_unit();
        let body = vec![
            Op::Var(VarRef::Cap(0)),
            Op::Read,
            Op::Var(VarRef::Cap(1)),
            Op::Len,
            Op::Var(VarRef::Cap(2)),
            Op::Deref,
            Op::Read,
            Op::Print(3),
            Op::Pop,
            Op::Unit,
            Op::Return,
        ];
        let mut ops = vec![Op::Int(1), Op::Bind(0), Op::Int(4), Op::MakeVec(1)];
        ops.extend([Op::Bind(1), var(0), var(1), Op::Take, var(0), Op::Borrow]);
        ops.extend([
            Op::MakeClosureIr {
                code,
                holds: vec![CapHold::Shared, CapHold::Moved, CapHold::Ref],
                span: Span::default(),
            },
            Op::Bind(2),
            Op::Int(5),
            var(0),
            Op::Store,
        ]);
        ops.extend([var(2), Op::Read, Op::CallValue(0), Op::Pop, var(1)]);
        ops.extend(print_end());
        let e = run_units(ops, 3, 0, vec![closure_unit(body, 0, 0)]).unwrap_err();
        assert_eq!(e.outcome.stdout, "5 1 5\n");
        // The closure moved `v` when it was made.
        assert!(
            e.message.contains("used after it was moved"),
            "{}",
            e.message
        );
    }

    fn effect(name: &str) -> weft_sema::EffectId {
        let a = weft_sema::analyze_source(SRC, Options::default()).unwrap();
        weft_sema::EffectId(
            a.program
                .effects
                .iter()
                .position(|d| d.name == name)
                .unwrap(),
        )
    }

    /// A `Handle` of `Ask` whose handled body is code unit `body` and whose
    /// clause is code unit `clause`. The handled body takes the capability.
    fn handle_ask(body: usize, clause: usize, body_caps: Vec<VarRef>) -> Op {
        Op::Handle(Rc::new(HandleSpec {
            effect: effect("Ask"),
            clauses: vec![ClauseSpec {
                op: 0,
                code: clause,
                caps: Vec::new(),
            }],
            body,
            body_caps,
            cap: true,
        }))
    }

    /// The clause of `ask`: `resume(41)`. Its parameter is the continuation.
    fn ask_clause() -> Code {
        let ops = vec![var(0), Op::Read, Op::Int(41), Op::CallValue(1), Op::Return];
        unit(CodeKind::Clause, ops, 1, 1)
    }

    #[test]
    fn perform_cap_performs_through_the_capability_of_a_handled_body() {
        // The handled body (unit `first`) gets the capability of the handler
        // in slot 0. `PerformCap` reads the effect from it: `ask()` gives 41.
        let first = first_extra_unit();
        let body = vec![
            var(0),
            Op::Read,
            Op::PerformCap { op: 0, n: 0 },
            Op::Int(1),
            Op::Bin(weft_syntax::ast::BinOp::Add),
            Op::Return,
        ];
        let ops = vec![
            handle_ask(first, first + 1, Vec::new()),
            Op::Print(1),
            Op::Pop,
            Op::Unit,
            Op::Return,
        ];
        let units = vec![unit(CodeKind::HandleBody, body, 1, 1), ask_clause()];
        let o = run_units(ops, 0, 0, units).unwrap();
        assert_eq!(o.stdout, "42\n");
        // A capability that is not a capability of a handler is a fault.
        let ops = vec![Op::Int(1), Op::PerformCap { op: 0, n: 0 }];
        assert!(fault(ops, 0, 0).contains("capability"));
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "the handler of the capability")]
    fn perform_cap_asserts_that_the_machine_finds_the_handler_of_the_capability() {
        // The outer handled body (unit `first`) gives its capability to the
        // inner handled body (unit `first + 1`), which performs through it.
        // The machine finds the inner handler (lexical): the IR never does
        // this, and the debug assertion stops it.
        let first = first_extra_unit();
        let outer = vec![
            handle_ask(first + 1, first + 2, vec![VarRef::Local(0)]),
            Op::Return,
        ];
        let inner = vec![
            Op::Var(VarRef::Cap(0)),
            Op::Read,
            Op::PerformCap { op: 0, n: 0 },
            Op::Return,
        ];
        let ops = vec![
            handle_ask(first, first + 2, Vec::new()),
            Op::Print(1),
            Op::Pop,
            Op::Unit,
            Op::Return,
        ];
        let units = vec![
            unit(CodeKind::HandleBody, outer, 1, 1),
            unit(CodeKind::HandleBody, inner, 1, 1),
            ask_clause(),
        ];
        let _ = run_units(ops, 0, 0, units);
    }

    #[test]
    fn make_closure_ir_copies_a_copied_capture_into_a_cell_of_its_own() {
        // A `Cap` or a `multi` `Kont` capture (`CapHold::Copied`): the closure
        // holds a copy of the value in a cell of its own, and a call does not
        // take it. A later write of the variable does not change the copy.
        let code = first_extra_unit();
        let body = vec![
            Op::Var(VarRef::Cap(0)),
            Op::Read,
            Op::Print(1),
            Op::Pop,
            Op::Unit,
            Op::Return,
        ];
        let mut ops = vec![Op::Int(1), Op::Bind(0), var(0), Op::Read];
        ops.extend([
            Op::MakeClosureIr {
                code,
                holds: vec![CapHold::Copied],
                span: Span::default(),
            },
            Op::Bind(1),
            Op::Int(5),
            var(0),
            Op::Store,
        ]);
        ops.extend([var(1), Op::Read, Op::CallValue(0), Op::Pop]);
        ops.extend([
            var(1),
            Op::Read,
            Op::CallValue(0),
            Op::Pop,
            Op::Unit,
            Op::Return,
        ]);
        let o = run_units(ops, 2, 0, vec![closure_unit(body, 0, 0)]).unwrap();
        assert_eq!(o.stdout, "1\n1\n");
    }

    /// The ops that put a struct `name { x: x }` into slot `slot`.
    fn make(name: &str, x: i64, slot: u32) -> Vec<Op> {
        vec![
            Op::Int(x),
            Op::MakeStruct {
                adt: adt(name),
                fields: vec![0],
                total: 1,
            },
            Op::Bind(slot),
        ]
    }

    /// Runs `main`: `setup`, then an `Assert` that fails, with a landing
    /// pad into the cleanup code `chain`. Returns the output and the
    /// error message.
    fn abort_with(setup: Vec<Op>, slots: u32, chain: Vec<Op>) -> (String, String) {
        let mut ops = setup;
        ops.extend([Op::Bool(false), Op::Assert]);
        let at = ops.len() - 1;
        ops.extend([Op::Unit, Op::Return]);
        let pad = ops.len();
        ops.extend(chain);
        let e = run_code(ops, slots, 0, vec![(at, pad)], Vec::new()).unwrap_err();
        (e.outcome.stdout.clone(), e.message)
    }

    #[test]
    fn unwind_value_runs_the_on_abort_of_the_value_at_its_place() {
        // The chain decides the order: the unwinder runs the `on abort` of
        // each value when the chain gets to it.
        let mut setup = make("U", 1, 0);
        setup.extend(make("U", 2, 1));
        let finish = |s: u32| {
            [
                Op::UnwindValue {
                    var: VarRef::Local(s),
                    path: Vec::new(),
                },
                Op::DropSlots(vec![s]),
            ]
        };
        let mut chain: Vec<Op> = finish(1).into_iter().chain(finish(0)).collect();
        chain.push(Op::UnwindExit);
        let (out, e) = abort_with(setup.clone(), 2, chain);
        assert_eq!(out, "undo 2\nundo 1\n");
        assert!(e.contains("the condition is false"), "{e}");
        let mut chain: Vec<Op> = finish(0).into_iter().chain(finish(1)).collect();
        chain.push(Op::UnwindExit);
        assert_eq!(abort_with(setup, 2, chain).0, "undo 1\nundo 2\n");
    }

    #[test]
    fn unwind_value_follows_the_path_and_skips_another_variant() {
        // `(_0 as B).0` of the value `E::A` names no value: the unwinder
        // does nothing (`docs/ir.md` 5.1.6). A part of a tuple is a part.
        let setup = vec![
            Op::MakeEnum {
                adt: adt("E"),
                variant: 0,
                n: 0,
            },
            Op::Bind(0),
        ];
        let chain = vec![
            Op::UnwindValue {
                var: VarRef::Local(0),
                path: vec![UnwindStep::Variant(1), UnwindStep::Part(0)],
            },
            Op::DropSlots(vec![0]),
            Op::UnwindExit,
        ];
        let (out, e) = abort_with(setup, 1, chain);
        assert_eq!(out, "");
        assert!(e.contains("the condition is false"), "{e}");
        let mut setup = vec![Op::Int(0)];
        setup.extend(make("U", 3, 0));
        setup.extend([var(0), Op::Read, Op::Tuple(2), Op::Bind(0)]);
        let chain = vec![
            Op::UnwindValue {
                var: VarRef::Local(0),
                path: vec![UnwindStep::Part(1)],
            },
            Op::DropSlots(vec![0]),
            Op::UnwindExit,
        ];
        assert_eq!(abort_with(setup, 1, chain).0, "undo 3\n");
    }

    #[test]
    fn the_oracle_finds_a_value_that_a_cleanup_chain_misses() {
        // `docs/ir.md` 8.2: after the chain of a frame, the scan of its
        // cells finds no live linear value. A hand-made chain that misses
        // the value of slot 0 fails the check.
        let (_, e) = abort_with(make("U", 1, 0), 1, vec![Op::UnwindExit]);
        assert!(e.contains("left after the cleanup chain of `main`"), "{e}");
        // A chain that ends the cell with no `UnwindValue` drops the value:
        // a linear leak.
        let chain = vec![Op::DropSlots(vec![0]), Op::UnwindExit];
        let (_, e) = abort_with(make("U", 1, 0), 1, chain);
        assert!(e.contains("linear leak"), "{e}");
        // A linear value with no `on abort` is a fault at its `UnwindValue`.
        let chain = vec![
            Op::UnwindValue {
                var: VarRef::Local(0),
                path: Vec::new(),
            },
            Op::DropSlots(vec![0]),
            Op::UnwindExit,
        ];
        let (_, e) = abort_with(make("T", 1, 0), 1, chain);
        assert!(e.contains("has no `on abort`"), "{e}");
    }
}

// ---------------------------------------------------------------------------
// 11. Variant steps on the IR engine (`docs/ir.md` 5.8, 8.1)
// ---------------------------------------------------------------------------

/// Runs the unchecked program `src` on the IR engine with the oracle checks.
/// Returns the output and the error message, if any.
fn run_ir_unchecked(src: &str) -> (String, Option<String>) {
    run_unchecked(src, weft_interp::Engine::Ir)
}

/// Runs the unchecked program `src` on `engine` with the oracle checks.
/// Returns the output and the error message, if any.
fn run_unchecked(src: &str, engine: weft_interp::Engine) -> (String, Option<String>) {
    let a = weft_sema::analyze_source(src, Options::default()).unwrap();
    let o = RunOptions {
        max_steps: Some(1_000_000),
        oracle: true,
        engine,
        ..RunOptions::default()
    };
    match run_analysis_main(&a, &o) {
        Ok(out) => {
            assert_eq!(out.fallback, None);
            (out.stdout, None)
        }
        Err(e) => {
            assert_eq!(e.outcome.fallback, None);
            (e.outcome.stdout.clone(), Some(e.message))
        }
    }
}

#[test]
fn a_variant_step_checks_the_tag_at_each_read_and_write() {
    // Third review of stage F8 (hole R1). The IR tests the variant of a
    // receiver place before the arguments and reads the payload after
    // them. An argument that gives the base another variant must not let
    // the engine read or write the payload of the other variant as the
    // wrong type: each place step `(p as V)` checks the tag again, and
    // another variant stops the run with the text of the `o.Some` test.
    let head = "struct Entity { hp: i32 }
impl Entity {
    fn plus(self, n: i32) -> i32 { self.hp + n }
    fn bump(self, n: i32) -> i32 / mut(self) { self.hp += n; self.hp }
}
struct Other { b: i32, a: Vec<i32> }
enum Two { A(Entity), B(Other) }
";
    let bad = [
        // A read through the receiver (y01: the run printed 1000).
        "fn main() { let e = Two.A(Entity { hp: 1 }); print(e.A.plus({ e = Two.B(Other { b: 1000, a: Vec.new() }); 0 })) }",
        // A write through the receiver (y02: the run printed 1005 1005).
        "fn main() { let e = Two.A(Entity { hp: 1 }); print(e.A.bump({ e = Two.B(Other { b: 1000, a: Vec.new() }); 5 })) }",
        // An element of a `Vec` (y08).
        "fn main() { let v = Vec.new(); v.push(Two.A(Entity { hp: 1 })); print(v[0].A.plus({ v[0] = Two.B(Other { b: 1000, a: Vec.new() }); 0 })) }",
        // `Option` (x02).
        "fn main() { let o = Some(Entity { hp: 1 }); print(o.Some.plus({ o = None; 0 })) }",
    ];
    for b in bad {
        let src = format!("{head}{b}");
        let (out, err) = run_ir_unchecked(&src);
        assert_eq!(out, "", "{b}");
        let err = err.unwrap_or_default();
        assert!(
            err.contains("this value is another variant: it has no such field"),
            "{b}: {err}"
        );
    }
    // The same variant: the steps read and write the payload.
    let good = "fn main() { let e = Two.A(Entity { hp: 1 }); print(e.A.plus(2)); print(e.A.bump({ e = Two.A(Entity { hp: 4 }); 5 })) }";
    let (out, err) = run_ir_unchecked(&format!("{head}{good}"));
    assert_eq!((out.as_str(), err), ("3\n9\n", None));
}

// ---------------------------------------------------------------------------
// 12. References into the payload of an enum value (oracle)
// ---------------------------------------------------------------------------

#[test]
fn a_reference_into_an_enum_payload_ends_when_the_enum_gets_a_new_value() {
    // Third review of stage F8, addendum (a15, b07): a reference into the
    // payload of an enum value stayed valid when the enum got another
    // variant, and the run read the payload of the new variant as the old
    // type (it printed 1000). The checker rejects these programs (W0301:
    // the variant step is unstable). With the oracle on, a new value of the
    // enum (a whole write of it or of a place above it) ends each reference
    // into its parts, and a read through one is a dangling read. `Entity`
    // is not plain data, so a pattern binds it by reference.
    let head = "struct Entity { hp: i32, v: Vec<i32> }
impl Entity {
    fn plus(self, n: i32) -> i32 { self.hp + n }
    fn me(self, n: i32) -> &Entity in self { self }
}
fn ent(hp: i32) -> Entity { Entity { hp: hp, v: Vec.new() } }
struct Other { b: i32 }
enum Two { A(Entity), B(Other) }
struct H { t: Two }
fn flip(h: &H) -> i32 / mut(h.t) { h.t = Two.B(Other { b: 1000 }); 0 }
fn mkh() -> H { H { t: Two.A(ent(1)) } }
";
    let ir_only = [
        // a15: a match binds `x` into the payload, an argument flips it.
        "fn main() { let h = mkh(); let r = &h.t; match r { Two.A(x) => print(x.plus(flip(&h))), Two.B(o) => {} } }",
        // b07: a returned reference into the payload, then a flip.
        "fn main() { let h = mkh(); let x = h.t.A.me(0); let n = flip(&h); print(x.hp + n) }",
        // A new value of the same variant is a new value too.
        "fn main() { let h = mkh(); let x = h.t.A.me(0); h.t = Two.A(ent(7)); print(x.hp) }",
        // A new value of a place above the enum.
        "fn main() { let h = mkh(); let x = h.t.A.me(0); h = mkh(); print(x.hp) }",
        // An enum in an element of a `Vec`.
        "fn main() { let v = Vec.new(); v.push(Two.A(ent(1))); let x = v[0].A.me(0); v[0] = Two.B(Other { b: 1000 }); print(x.hp) }",
    ];
    // A match through a reference binds by reference on both engines.
    let both = [
        "fn main() { let h = mkh(); let r = &h.t; match r { Two.A(x) => { let n = flip(&h); print(x.hp + n) }, Two.B(o) => {} } }",
        "fn main() { let o = Some(ent(1)); let r = &o; match r { Some(x) => { o = None; print(x.hp) }, None => {} } }",
    ];
    let engines = [weft_interp::Engine::Ast, weft_interp::Engine::Ir];
    let runs = ir_only
        .iter()
        .map(|b| (*b, weft_interp::Engine::Ir))
        .chain(both.iter().flat_map(|b| engines.map(|e| (*b, e))));
    for (b, e) in runs {
        let (out, err) = run_unchecked(&format!("{head}{b}"), e);
        assert_eq!(out, "", "{e:?} {b}");
        let err = err.unwrap_or_default();
        assert!(
            err.contains("oracle:")
                && err.contains("an enum value")
                && err.contains("(a dangling reference)"),
            "{e:?} {b}: {err}"
        );
    }
}

#[test]
fn a_write_inside_the_payload_keeps_the_references_into_the_enum_value() {
    // Controls of the test above. A write to a field of the payload does
    // not give the enum a new value: a reference to another field stays
    // valid (as for a struct). A reference to the enum value itself (not
    // into its payload) stays valid when the enum gets a new value. A
    // reference made after the new value is valid.
    let head = "struct P2 { a: i32, b: i32 }
enum E2 { P(P2), Q(i32) }
fn setb(p: &P2) -> i32 / mut(p.b) { p.b = 5; 0 }
struct Other { b: i32 }
struct Entity { hp: i32 }
enum Two { A(Entity), B(Other) }
struct H { t: Two }
fn flip(h: &H) -> i32 / mut(h.t) { h.t = Two.B(Other { b: 1000 }); 0 }
fn mkh() -> H { H { t: Two.A(Entity { hp: 1 }) } }
";
    let good = [
        (
            "fn main() { let e = E2.P(P2 { a: 1, b: 2 }); match &e { E2.P(p) => { let ra = &p.a; let n = setb(&p); print(ra); print(p.b + n) }, E2.Q(_) => {} } }",
            "1\n5\n",
        ),
        (
            "fn main() { let h = mkh(); let r = &h.t; let n = flip(&h); match r { Two.A(x) => print(x.hp), Two.B(o) => print(o.b + n) } }",
            "1000\n",
        ),
        (
            "fn main() { let h = mkh(); match &h.t { Two.A(x) => print(x.hp), Two.B(_) => {} }; let n = flip(&h); match &h.t { Two.B(o) => print(o.b + n), Two.A(_) => {} } }",
            "1\n1000\n",
        ),
    ];
    for (g, want) in good {
        for e in [weft_interp::Engine::Ast, weft_interp::Engine::Ir] {
            let (out, err) = run_unchecked(&format!("{head}{g}"), e);
            assert_eq!((out.as_str(), err), (want, None), "{e:?} {g}");
        }
    }
}
