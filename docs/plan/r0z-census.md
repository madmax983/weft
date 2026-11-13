# R0z census: the fallbacks after R0k-b2

This file is the per-row list of the plan section "R0z plan (census after R0k-b2)" in
`docs/plan/core-ir.md`. Read that section first: it has the stage names, the rules and
the counts.

## Source

- Binary: the release build of main at c414c69 (R0k-b2 and its fix 1; scratchpad
  `r0k/b2f1/bin/weft-r0kb2f1`).
- Census: `weft check` on each file of the manifests; a row is a fallback if the note
  "--facts=ir: the old pipeline checks the program: ..." is there (scratchpad
  `r0k/b2f1/p-t1.tsv`, `p-t2.tsv`). Tier 1: 5373 files, 105 fallbacks. Tier 2: 57393
  files (`target/gate/probes-tier2`), 60 fallbacks.
- Verdicts: `ereview/ev.sh` on each of the 165 rows (scratchpad `r0z/ev-all.tsv`): the old
  codes, and a run of the `ir` engine with the oracle (seeds 1 to 3) and of the AST engine.
- The note names the reason of the first body that fails. A program can have more
  reasons. Stage Z0 lists all of them.

## Columns

- Reason: the reason of the note. `C2` a function value that an operation gives to a
  handler (`OP_KEPT`); `D1` a `resume` of a captured continuation (`KONT_CAPTURED`); `D3`
  a call that runs a clause of a local handler whose operation gives a value back
  (`GIVES_BACK`); `RC` a reference into an `rc` group in a copied frame across a `multi`
  operation (`RC_ACROSS_ROW`); `NESTED` a function value that a function value of a callee
  runs as a task (R0e fix 2); `VT` a function value that runs a value of its arguments as
  a task (`VALUE_TASKS`); `F18` a function value that changes places or holds a
  nonportable value, and that code of a caller can run on another thread (`TASK_RUN`);
  `E2` a task that runs a callback more than once (`TASK_AGAIN`); `E4` a task that runs a
  function variable that gets a new value (`TASK_LATE`); `TC` a task that runs code of a
  caller (`TASK_CODE`); `esc` a capability that leaves its handler; `A` a perform whose
  rest of the handled body the facts do not find (`REST_NOT_FOUND`); `D5` a `multi`
  operation of a handler of a caller in a clause (a row that only the analysis finds);
  `chain` a chain of function values deeper than 64. `X>Y`: the reason is X; with the
  copies of the callees the reason is Y.
- Old pipeline: `clean`, or the codes of `--facts=old`.
- Run: `fault` if a run of the program faults (a fault of the oracle or of the runtime);
  `no fault`; `no main` (not runnable); `timeout`.
- Class: `rejected` (the old pipeline rejects it), `clean` (the old pipeline accepts it
  and it does not fault), `oldmiss` (the old pipeline accepts it and it faults).
- Refusal probe: `yes` if the probe was written to show a refusal or a pending reason
  (its comment says that the program keeps the fallback, or keeps the fallback or is
  rejected).
- Stage: the stage of the R0z plan that closes the row. `Z1-A` to `Z1-G` are the rules
  of stage Z1.

## Tier 1 (105 rows)

| # | Path | Reason | Form | Old pipeline | Run | Class | Refusal probe | Stage |
|---|---|---|---|---|---|---|---|---|
| 1 | `fixes/r0k2/u04_task_reassigns.wf` | C2 | a scope task gives `k` a closure with a capability of a local handler | W0314 | fault | rejected | yes | Z1-A |
| 2 | `fixes/r0k2/u08_task_join.wf` | C2 | a joined task gives `k` a closure with a capability of a local handler | W0314 | fault | rejected | yes | Z1-A |
| 3 | `fixes/r0k2/u09_fork.wf` | C2 | a fork branch gives `k` a closure with a capability of a local handler | W0314, W0403 | fault | rejected | yes | Z1-A |
| 4 | `fixes/r0kb2/u14_task_bad.wf` | C2 | a second write by a task; the task holds a capability of a local handler | W0314 | fault | rejected | yes | Z1-A |
| 5 | `fixes/r0kb2/u14_task_ok.wf` | C2 | a second write by a task (old W0314 on both twins) | W0314 | no fault | rejected | yes | Z1-A |
| 6 | `r2/oracle/min/or_resume_in_task.wf` | D1 | task resume: `resume` in a spawn closure | 2xW0314 | fault | rejected | no | Z1-A |
| 7 | `r2/oracle/probes/i3_resume_task.wf` | D1 | task resume: `resume` in a spawn closure | W0314 | fault | rejected | no | Z1-A |
| 8 | `r2/oracle/probes/i3b_resume_task.wf` | D1 | task resume: `resume` in a spawn closure | W0314 | fault | rejected | no | Z1-A |
| 9 | `r2/oracle/repro/OR9_resume_in_task.wf` | D1 | task resume: `resume` in a spawn closure | 2xW0314 | fault | rejected | no | Z1-A |
| 10 | `verify/s5/R2c/p/c2.wf` | D1 | task resume: through a field, a callee in the task, a named closure, a fork branch (no `main` body) | 4xW0314 | no fault | rejected | no | Z1-A |
| 11 | `verify/s5/R2c: .../p/rr3_v15_spawn_nested_closure.wf` | D1 | task resume: a task runs a closure that runs the resuming closure | W0314 | no fault | rejected | no | Z1-A |
| 12 | `verify/s5/R2c: .../p/rr3_v16_spawn_via_callee.wf` | D1 | task resume: a callee runs the resuming closure as a task | W0314 | no fault | rejected | no | Z1-A |
| 13 | `verify/s5/R2c: .../p/rr3_v17_fork.wf` | D1 | task resume: a fork branch resumes | W0314 | no fault | rejected | no | Z1-A |
| 14 | `fixes/r0h/d3f_task.wf` | D3>TC | the callee runs the closure of the clause on a task (the copy brings in a task that runs code of a caller) | W0314 | no fault | rejected | no | Z1-B |
| 15 | `fixes/r0j/j05_code_old.wf` | TC | a task runs a value of an operation (code of a caller) | W0314 | no fault | rejected | yes | Z1-B |
| 16 | `fixes/r0e/a13_sim_param_task.wf` | F18 | a parameter spawned inside `sim.run`; the value holds the capability of a local handler | W0314 | fault | rejected | no | Z1-C |
| 17 | `fixes/r0e/a13b_callee_param_task.wf` | F18 | a parameter spawned in a closure that a callee runs; the value holds a capability | W0314 | fault | rejected | no | Z1-C |
| 18 | `fixes/r0e/a13c_callee_bg_param.wf` | F18 | as a13b, through a second callee | W0314 | fault | rejected | no | Z1-C |
| 19 | `fixes/r0j/j07_run_bad.wf` | F18 | as a13 (a task of `sim.run` performs through a handler of the spawning task) | W0314 | fault | rejected | yes | Z1-C |
| 20 | `verify/partb/S3/p/sim1.wf` | F18 | `sim.run` and tasks with capability values, no `main` | 4xW0314, 2xW0702 | no `main` | rejected | no | Z1-C |
| 21 | `fixes/r0kb1/c11_c2_loop_instance_bad.wf` | C2 | extent rule: a new handler instance in a loop; the value goes through a local outside the handled body | W0301, W0313 | fault | rejected | yes | Z1-D |
| 22 | `fixes/r0kb1/c11_c2_loop_instance_ok.wf` | C2 | extent rule (clean twin; the old W0313 is the language rule "not through a local outside it") | W0313 | no fault | rejected | yes | Z1-D |
| 23 | `fixes/r0kb1/n04_loop_instance_bad.wf` | C2 | extent rule: as c11, a closure of the same function | W0301, W0313 | fault | rejected | yes | Z1-D |
| 24 | `fixes/r0kb1/n04_loop_instance_ok.wf` | C2 | extent rule (clean twin; old W0313) | W0313 | no fault | rejected | yes | Z1-D |
| 25 | `fixes/r0kb2/q01_85_after_resume_bad.wf` | C2>esc | the clause of `Run` runs a capability closure of `Note` after its `resume` (outside `Note`) | W0313 | fault | rejected | no | Z1-D |
| 26 | `verify/partb/p/a4_get_own.wf` | C2 | a closure that performs through `Get` goes to an operation of `Get` itself | W0313 | fault | rejected | no | Z1-D |
| 27 | `verify/s5/S5a/x/p/e2b_e_job.wf` | C2>VT | forms 2 to 4 with a clause that spawns its argument (capability of `Note` to `Run`, `RunJ`) | 2xW0313, 5xW0314 | fault | rejected | no | Z1-D |
| 28 | `verify/s5/S5a/x/p/e2b_e_mk_job.wf` | C2>VT | as e2b_e_job | 2xW0313, 5xW0314 | fault | rejected | no | Z1-D |
| 29 | `verify/s5/S5a/x/p/e2b_e_struct.wf` | C2>VT | as e2b_e_job | 2xW0313, 5xW0314 | fault | rejected | no | Z1-D |
| 30 | `verify/s5/S5a/x/p/e2b_variants.wf` | C2>VT | as e2b_e_job | 2xW0313, 5xW0314 | fault | rejected | no | Z1-D |
| 31 | `verify/s5/diff/p/v1c_stored.wf` | C2 | form 3: a closure in a field run by `run_it`; the clause keeps the value in a local outside | W0313 | fault | rejected | no | Z1-D |
| 32 | `fixes/r0e/rv1_b2_h10.wf` | NESTED | a closure that a callee runs spawns a `once` value two times | W0502 | fault | rejected | yes | Z1-E |
| 33 | `fixes/r0e/rv1_b2_h18.wf` | NESTED | a callee runs the closure that spawns a `once` value two times | W0502 | fault | rejected | yes | Z1-E |
| 34 | `verify/partb/p/a2_escapes.wf` | C2 | a capability closure as the value of a handled body (via `id`, `wrap`, `pair`, `pop`, ...), no `main` | W0301, 9xW0313 | no `main` | rejected | no | Z1-G |
| 35 | `fixes/r0kc2b/b03_rc_between_ok.wf` | RC | rc-across-multi: an `rc` object shared between the copies | clean | no fault | clean | no | Z2 |
| 36 | `fixes/r0kc2b/b07_abort_in_copy_ok.wf` | RC | rc-across-multi: an abort in a copy | clean | no fault | clean | no | Z2 |
| 37 | `fixes/r0kc2b/b08_handled_after_ok.wf` | RC | rc-across-multi: the rest of the handled body runs again | clean | no fault | clean | no | Z2 |
| 38 | `fixes/r0kc2b/b09_post_row_ok.wf` | RC | rc-across-multi: a row after the `resume` | clean | no fault | clean | no | Z2 |
| 39 | `fixes/r0kc2b/b10_post_row_after_ok.wf` | RC | rc-across-multi: a row after the `resume`, a read after the handler | clean | no fault | clean | no | Z2 |
| 40 | `fixes/r0kc2c/n18_rc_handled_frame_bad.wf` | RC | rc-across-multi: the handled body of `run` holds a reference into the `rc` across `pick` | clean | fault | oldmiss | no | Z2 |
| 41 | `fixes/r0kc2c/n19_rc_param_arg_bad.wf` | RC | rc-across-multi: a reference into the `rc` as the argument of `pick` | clean | fault | oldmiss | no | Z2 |
| 42 | `fixes/r0kc2c/p08_rc_between_param_bad.wf` | RC | rc-across-multi: a reference into the `rc` through a parameter of `run` | clean | fault | oldmiss | no | Z2 |
| 43 | `fixes/r0k2/a05_by_value_bad.wf` | D3 | a `ByMove` capture (static copy refused) | W0301 | fault | rejected | yes | Z3 |
| 44 | `fixes/r0k2/a05_by_value_ok.wf` | D3 | a `ByMove` capture (clean twin) | clean | no fault | clean | yes | Z3 |
| 45 | `fixes/r0k2/g26_weak_run_in_callee_bad.wf` | C2 | weak guard order: the weak value goes to `apply`, which the analysis runs before the maker | W0301, W0403, W0405 | fault | rejected | yes | Z3 |
| 46 | `fixes/r0kb1/n03_clause_runs_ok.wf` | A | form 4 (a clause runs its parameter): the copy region exists, but copies apply only to C2 and D3 | clean | no fault | clean | yes | Z3 |
| 47 | `fixes/r0kb2/a02_vec_same_id_bad.wf` | C2 | heap slot: one closure id two times in a `Vec`, other captures | clean | fault | oldmiss | yes | Z3 |
| 48 | `fixes/r0kb2/a02_vec_same_id_ok.wf` | C2 | heap slot (clean twin) | clean | no fault | clean | yes | Z3 |
| 49 | `fixes/r0kb2/e04b_field_read_bad.wf` | C2>A | form 3 with a read of another part: no `sole`, so the copy needs the rest of the handled body | clean | fault | oldmiss | yes | Z3 |
| 50 | `fixes/r0kb2/o01_once_two_runs_bad.wf` | C2 | once: a copy of a `once` closure is refused; two runs | W0502 | fault | rejected | yes | Z3 |
| 51 | `fixes/r0kb2/o01_once_two_runs_ok.wf` | C2 | once: one run (clean twin) | clean | no fault | clean | yes | Z3 |
| 52 | `fixes/r0kb2/u12_scope_body_bad.wf` | C2 | a second write of the local of the way by a scope body (the same closure id) | clean | fault | oldmiss | yes | Z3 |
| 53 | `fixes/r0kb2/u12_scope_body_ok.wf` | C2 | a second write by a scope body (clean twin) | clean | no fault | clean | yes | Z3 |
| 54 | `fixes/r0kb2/u13_clause_bad.wf` | C2 | a second write of the local of the way by a clause (the same closure id) | clean | fault | oldmiss | yes | Z3 |
| 55 | `fixes/r0kb2/u13_clause_ok.wf` | C2 | a second write by a clause (clean twin) | clean | no fault | clean | yes | Z3 |
| 56 | `fixes/r0h/c2_task.wf` | D1 | D1b: the clause spawns the value, then resumes in the scope body; the rest of the handled body writes what the task reads | clean | fault | oldmiss | no | Z5 |
| 57 | `fixes/r0k/k04_c2_race_ok.wf` | D1 | D1b (clean twin) | clean | no fault | clean | no | Z5 |
| 58 | `fixes/r0k/rv_p12_c2_task_after_perform.wf` | D1 | D1b: as c2_task; the callee spawns a writer after the perform | clean | fault | oldmiss | no | Z5 |
| 59 | `fixes/r0k/rv_p12_c2_task_after_perform_ok.wf` | D1 | D1b (clean twin) | clean | no fault | clean | no | Z5 |
| 60 | `fixes/r0k/rv_p04_c2_multi.wf` | C2>D5 | a `multi` clause runs the value between two `resume`s; the copy brings in a row that only the analysis finds | clean | fault | oldmiss | no | Z7 |
| 61 | `fixes/r0k/rv_p04_c2_multi_ok.wf` | C2>D5 | as rv_p04 (clean twin) | clean | no fault | clean | no | Z7 |
| 62 | `fixes/r0k2/a04_two_closures_bad.wf` | D3 | two closures can reach the local (static copy refused) | W0301 | fault | rejected | yes | Z6 |
| 63 | `fixes/r0k2/a04_two_closures_ok.wf` | D3 | two closures (clean twin) | clean | no fault | clean | yes | Z6 |
| 64 | `fixes/r0k2/u03_callee_reassigns_via_clause.wf` | C2 | two values at the run node: a clause of another handler gives `k` a second closure | clean | fault | oldmiss | yes | Z6 |
| 65 | `fixes/r0k2/u05_scope_body.wf` | C2 | two values at the run node: a scope body gives `k` a second closure | clean | fault | oldmiss | yes | Z6 |
| 66 | `fixes/r0k2/u06_handled_body.wf` | C2 | two values at the run node: a nested handled body gives `k` a second closure | clean | fault | oldmiss | yes | Z6 |
| 67 | `fixes/r0k2/u07_if_branch.wf` | C2 | two values at the run node: an `if` branch gives `k` a second closure | clean | fault | oldmiss | yes | Z6 |
| 68 | `fixes/r0k2/u10_clause_of_inner.wf` | C2 | two values at the run node: a clause that a perform of a callee runs gives `k` a second closure | clean | fault | oldmiss | yes | Z6 |
| 69 | `fixes/r0k2/u11_clause_harmless_then.wf` | C2 | two values at the run node: a clause gives `k` a harmless closure (clean twin of the u family) | clean | no fault | clean | yes | Z6 |
| 70 | `fixes/r0kb2/a01_two_paths_bad.wf` | C2 | form 2 with two values: `mk` gives back one of two closures | W0301 | fault | rejected | yes | Z6 |
| 71 | `fixes/r0kb2/a01_two_paths_ok.wf` | C2 | form 2 with two values (clean twin) | clean | no fault | clean | yes | Z6 |
| 72 | `fixes/r0kb2/a03_put_fns_bad.wf` | C2 | a borrow of the local of the way: `put_fns` writes the field before the run | W0301 | fault | rejected | yes | Z6 |
| 73 | `fixes/r0kb2/a03_put_fns_ok.wf` | C2 | a borrow of the local of the way (clean twin) | clean | no fault | clean | yes | Z6 |
| 74 | `fixes/r0kc/c03_two_runs_bad.wf` | D1 | D1a refusal: two runs | W0301 | fault | rejected | yes | Z4 |
| 75 | `fixes/r0kc/c03_two_runs_ok.wf` | D1 | D1a refusal: two runs (clean twin) | clean | no fault | clean | yes | Z4 |
| 76 | `fixes/r0kc/c05_perform_between_bad.wf` | D1 | D1a refusal: a perform between the make and the run | W0301 | fault | rejected | yes | Z4 |
| 77 | `fixes/r0kc/c05_perform_between_ok.wf` | D1 | D1a refusal: a perform between (clean twin) | clean | no fault | clean | yes | Z4 |
| 78 | `fixes/r0kc/c06_call_between_bad.wf` | D1 | D1a refusal: a call between the make and the run | W0301 | fault | rejected | yes | Z4 |
| 79 | `fixes/r0kc/c06_call_between_ok.wf` | D1 | D1a refusal: a call between (clean twin) | clean | no fault | clean | yes | Z4 |
| 80 | `fixes/r0kc/c07_use_after_bad.wf` | D1 | D1a refusal: a borrow of the closure value | W0301 | fault | rejected | yes | Z4 |
| 81 | `fixes/r0kc/c07_use_after_ok.wf` | D1 | D1a refusal: a borrow (clean twin) | clean | no fault | clean | yes | Z4 |
| 82 | `fixes/r0kc/c08_nested_bad.wf` | D1 | D1a refusal: a body inside the clause makes and runs the closure | W0301 | fault | rejected | yes | Z4 |
| 83 | `fixes/r0kc/c08_nested_ok.wf` | D1 | D1a refusal: a body inside the clause (clean twin) | clean | no fault | clean | yes | Z4 |
| 84 | `fixes/r0kc/c09_field_bad.wf` | D1 | D1a refusal: the closure goes through a field | W0301 | fault | rejected | yes | Z4 |
| 85 | `fixes/r0kc/c09_field_ok.wf` | D1 | D1a refusal: a field (clean twin) | clean | no fault | clean | yes | Z4 |
| 86 | `verify/s5/R2c: .../p/fd2_v2_closure_resume.wf` | D1 | D1a in a `multi` clause: a perform between, two runs | clean | no fault | clean | no | Z4 |
| 87 | `verify/s5/R2c: .../p/fd2_v3_vec_of_closures.wf` | D1 | D1a through a `Vec` (heap slot), a perform between | clean | no fault | clean | no | Z4 |
| 88 | `verify/s5/R2c: .../p/rr3_v19_sim_run_closure.wf` | D1 | runtime run: `resume` in the block of `sim.run` | clean | no fault | clean | no | Z4b |
| 89 | `verify/s5/R2c: .../p/rr3_v20_with_timeout.wf` | D1 | runtime run: `resume` in the block of `with_timeout` | clean | no fault | clean | no | Z4b |
| 90 | `fixes/r0kd1/d02_multi_weak.wf` | esc | D4 multi: the update after a `multi` resume stays weak, so a closure seems to run outside its handler | clean | no fault | clean | yes | Z8 |
| 91 | `verify/partb/p/g2_lexical.wf` | D3 | a value through a `resume`: the inner clause gives back a closure that performs to the outer handler | clean | no fault | clean | no | Z8 |
| 92 | `fixes/r0kd2/s4_spawn_in_closure_ok.wf` | E4 | a spawn in a closure on the scope of the outer body; two writes of `f` | clean | no fault | clean | yes | Z9b |
| 93 | `fixes/r0f/c09_cc_during_ok.wf` | E2 | two values: code of a caller runs `f` once on the task (the c09 subset of R0k-d3) | clean | no fault | clean | no | Z9a |
| 94 | `fixes/r0j/j01_again_ok.wf` | E2 | code of a caller runs `f` two times on the task | clean | no fault | clean | yes | Z9a |
| 95 | `r3/oracle/probes/i9_kept_write.wf` | E2 | a task runs a kept callback more than once | W0405 | no fault | rejected | no | Z9a |
| 96 | `r3/oracle/probes/s8_steal_fnparam.wf` | E2 | a task runs a function parameter more than once | clean | no fault | clean | no | Z9a |
| 97 | `r3/oracle/probes/s9_steal_stored.wf` | E2 | a task runs a stored callback more than once | W0302 | fault (AST engine only) | rejected | no | Z9a |
| 98 | `fixes/r0e/a13_ok.wf` | NESTED | a spawn of a parameter inside `sim.run` of a callee (task of a callee, no `TaskHow`) | clean | no fault | clean | no | Z9c |
| 99 | `fixes/r0j/j03_nested_ok.wf` | NESTED | a closure spawns a parameter and a task; the closure runs in a callee (two levels of runs) | clean | no fault | clean | yes | Z9c |
| 100 | `fixes/r0j/j04_value_ok.wf` | VT | a closure spawns a captured closure two times (tasks of a value of the interface) | clean | no fault | clean | yes | Z9c |
| 101 | `fixes/r0j/j07_run_ok.wf` | F18 | a parameter spawned inside `sim.run`; the value changes a local of its maker (task of a callee, no `TaskHow`) | clean | no fault | clean | yes | Z9c |
| 102 | `fixes/r0kb1/c16_c2_nested_bad.wf` | C2>VT | a nested closure in the closure of the maker `mk_cap` (VALUE_TASKS in the facts of the maker) | W0301 | fault | rejected | yes | Z9c |
| 103 | `fixes/r0kb1/c16_c2_nested_ok.wf` | C2>VT | a nested closure in the maker (clean twin) | clean | no fault | clean | yes | Z9c |
| 104 | `fixes/r0kd2/s3_nested_closure_ok.wf` | VT | a task closure runs a value from the environment of the closure that makes the scope | clean | no fault | clean | no | Z9c |
| 105 | `verify/review_core/Core_S2/probes/crash/c10.wf` | NESTED | a recursive higher-order function `y(f)`, no `main` (the worst case of a recursive callee: a task run) | clean | no `main` | clean | no | Z9c |

## Tier 2 (60 rows)

25 rows of tier 2 are the same files as rows of tier 1 (the same bytes, the same reason,
the same old codes and the same verdict). They close in the same stage:

- `r2/oracle/min/or_resume_in_task.wf`
- `r2/oracle/probes/i3_resume_task.wf`
- `r2/oracle/probes/i3b_resume_task.wf`
- `r2/oracle/repro/OR9_resume_in_task.wf`
- `r3/oracle/probes/i9_kept_write.wf`
- `r3/oracle/probes/s8_steal_fnparam.wf`
- `r3/oracle/probes/s9_steal_stored.wf`
- `verify/partb/S3/p/sim1.wf`
- `verify/partb/p/a2_escapes.wf`
- `verify/partb/p/a4_get_own.wf`
- `verify/partb/p/g2_lexical.wf`
- `verify/review_core/Core_S2/probes/crash/c10.wf`
- `verify/s5/R2c/p/c2.wf`
- `verify/s5/R2c: effects, continuations, on abort and drops/p/fd2_v2_closure_resume.wf`
- `verify/s5/R2c: effects, continuations, on abort and drops/p/fd2_v3_vec_of_closures.wf`
- `verify/s5/R2c: effects, continuations, on abort and drops/p/rr3_v15_spawn_nested_closure.wf`
- `verify/s5/R2c: effects, continuations, on abort and drops/p/rr3_v16_spawn_via_callee.wf`
- `verify/s5/R2c: effects, continuations, on abort and drops/p/rr3_v17_fork.wf`
- `verify/s5/R2c: effects, continuations, on abort and drops/p/rr3_v19_sim_run_closure.wf`
- `verify/s5/R2c: effects, continuations, on abort and drops/p/rr3_v20_with_timeout.wf`
- `verify/s5/S5a/x/p/e2b_e_job.wf`
- `verify/s5/S5a/x/p/e2b_e_mk_job.wf`
- `verify/s5/S5a/x/p/e2b_e_struct.wf`
- `verify/s5/S5a/x/p/e2b_variants.wf`
- `verify/s5/diff/p/v1c_stored.wf`
The other 35 rows of tier 2:

| # | Path | Reason | Form | Old pipeline | Run | Class | Refusal probe | Stage |
|---|---|---|---|---|---|---|---|---|
| 1 | `r3/oracle/runs/m3a/p1414.wf` | D1 | task resume: `fork(|| resume(()), ..)` | W0314 | no fault | rejected | no | Z1-A |
| 2 | `r3/oracle/runs/m3a/p316.wf` | D1 | task resume: `s.spawn(|| resume(1))` | W0314 | no fault | rejected | no | Z1-A |
| 3 | `r3/oracle/runs/m3a/p4859.wf` | D1 | task resume: `fork(|| resume(()), ..)` | W0314 | no fault | rejected | no | Z1-A |
| 4 | `r3/oracle/runs/m3a/p5452.wf` | D1 | task resume: `s.spawn(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A |
| 5 | `r3/oracle/runs/m3a/p5483.wf` | D1 | task resume: `spawn_m(|| resume(()))` (a callee spawns its parameter) | W0314 | no fault | rejected | no | Z1-A |
| 6 | `r3/oracle/runs/m3a/p6530.wf` | D1 | task resume: `spawn_m(|| resume(()))` | W0301, W0314 | no fault | rejected | no | Z1-A |
| 7 | `r3/oracle/runs/m3a/p7888.wf` | D1 | task resume: `spawn_m(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A |
| 8 | `r3/oracle/runs/m3b/p21941.wf` | D1 | task resume: `spawn_m(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A |
| 9 | `r3/oracle/runs/m3b/p22442.wf` | D1 | task resume: `spawn_m(|| print(k))` holds the resuming closure | W0301, W0314 | no fault | rejected | no | Z1-A |
| 10 | `r3/oracle/runs/m3b/p25672.wf` | D1 | task resume: `s.spawn(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A |
| 11 | `r3/oracle/runs/m3b/p26278.wf` | D1 | task resume: `spawn_m(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A |
| 12 | `r3/oracle/runs/m3b/p27232.wf` | D1 | task resume: `s.spawn(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A |
| 13 | `r3/oracle/runs/m3b/p21376.wf` | D1 | D1b: two `resume`s of a `once` continuation in a scope body | W0501 | no fault | rejected | no | Z1-F |
| 14 | `r3/oracle/runs/m3a/p6152.wf` | C2 | a body with a `typeck` error (W0102) and a C2 body | W0102, W0401, W0405, 4xW0503 | no fault | rejected | no | Z1-G |
| 15 | `r3/oracle/runs/m3b/p26666.wf` | C2 | errors (W0314, W0403, W0405) in bodies that do not call the C2 body | W0314, W0403, 3xW0405 | no fault | rejected | no | Z1-G |
| 16 | `r3/quality/big/all.wf` | C2>E2 | a concatenation of the corpus: W01xx errors of `typeck` | 50 codes (W01xx to W1004) | no fault | rejected | no | Z1-G |
| 17 | `r3/quality/big/all_2.wf` | C2>E2 | as all.wf (two copies) | 50 codes (W01xx to W1004) | timeout | rejected | no | Z1-G |
| 18 | `verify/s5/S5c/mut/progs/m00982_85_op_args.wf` | C2>D1 | a mutant of 85, no `main`: errors in other bodies (W0313, W0314) | W0313, 10xW0314, W0501 | no `main` | rejected | no | Z1-G |
| 19 | `verify/s5/S5c/mut/progs/m01268_85_op_args.wf` | C2>D1 | as m00982 | W0313, 11xW0314 | no `main` | rejected | no | Z1-G |
| 20 | `verify/s5/S5c/mut/progs/m01766_85_op_args.wf` | C2>D1 | as m00982 | W0313, 12xW0314 | no `main` | rejected | no | Z1-G |
| 21 | `verify/s5/S5c/mut/progs/m02309_85_op_args.wf` | C2>D1 | as m00982 | W0313, 9xW0314 | no `main` | rejected | no | Z1-G |
| 22 | `r2/oracle/runs/m1/p1669.wf` | D5 | a `multi` clause runs its parameter: a row that only the analysis finds | clean | no fault | clean | no | Z7 |
| 23 | `r3/oracle/runs/m3a/p5750.wf` | D1 | D1a refusal: a call (`print(r)`) between the make and the run | W0301 | no fault | rejected | no | Z4 |
| 24 | `r3/oracle/runs/m3a/p7154.wf` | D1 | D1a refusal: a call (`Box.new`) between, a `resume` in a nested handled body | W0301 | no fault | rejected | no | Z4 |
| 25 | `r2/oracle/runs/g2/p2515.wf` | esc | closures that capture a capability in a block of a closure body that no node runs | clean | no fault | clean | no | Z8 |
| 26 | `r2/oracle/runs/m2/p7046.wf` | E2 | a task runs `run_both(f1, f1)` | clean | no fault | clean | no | Z9a |
| 27 | `r3/oracle/runs/g3b/p18574.wf` | VT | a function value runs a value of its arguments as a task | W0312 | no fault | rejected | no | Z9c |
| 28 | `r3/oracle/runs/g4p/p25005.wf` | NESTED | a value of a callee runs a value as a task | W0405 | no fault | rejected | no | Z9c |
| 29 | `r3/oracle/runs/t3/p148.wf` | NESTED | a value of a callee runs a value as a task | W0312 | no fault | rejected | no | Z9c |
| 30 | `r3/oracle/seeds3/gen3_15687.wf` | VT | a function value runs a value of its arguments as a task | clean | no fault | clean | no | Z9c |
| 31 | `r3/oracle/seeds3/gen3_18180.wf` | NESTED | a value of a callee runs a value as a task | clean | no fault | clean | no | Z9c |
| 32 | `r3/quality/gen3/closure_chain_100.wf` | chain | a chain of function values deeper than 64, no `main` | clean | no `main` | clean | no | Z10 |
| 33 | `r3/quality/gen3/closure_chain_200.wf` | chain | as closure_chain_100 | clean | no `main` | clean | no | Z10 |
| 34 | `r3/quality/gen3/closure_chain_400.wf` | chain | as closure_chain_100 | clean | no `main` | clean | no | Z10 |
| 35 | `r3/quality/gen3/closure_chain_800.wf` | chain | as closure_chain_100 | clean | no `main` | clean | no | Z10 |
