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

## Z0 and Z1 (as built)

- Z0: `weft check --reasons` lists each reason of a row: each body whose analysis stops
  (the fact generator goes on after it), each construct with no full facts (`pending`),
  and the same with the copies of the callees (`cp:`). The note of the census names only
  the first one. 27 of the 165 rows have more than one reason (scratchpad
  `r0z/z0/reasons-a3.tsv`). The second reasons that a later stage must close too:
  - D1 and TC (a task that runs code of a caller): `c2_task`, `k04_c2_race_ok`, `rv_p12`
    and its twin (Z5; closed, "Z5 (as built)");
  - F18 and NESTED: `a13`, `a13b`, `a13c`, `j07_run_bad`, `j07_run_ok`, `sim1` (Z9c;
    Z9c-C closes the NESTED reason of all but `sim1`: "Z9c-C (as built)");
  - C2 and D5: `rv_p04` and its twin (Z7; closed, "Z7 (as built)");
  - D3 and TC: `d3f_task`;
  - three bodies with C2 and TC (with the copies VT): the four `e2b` rows;
  - C2, D1 and TC: the four tier-2 mutants of 85;
  - five bodies that stop and five pending reasons: `r3/quality/big/all.wf`.
- Z1 closed 33 rows of tier 1 and 37 rows of tier 2 (the column Stage says
  "(closed)"). Each one is a row that the old pipeline rejects; no clean row and no
  oldmiss row changed. Rule G closed the four `e2b` rows (the plan named rule D: the
  error is the W0314 of a body that does not reach the bodies that stop). `q01` stays
  open: the closure of `Note` goes to the clause of `Run` through a call of a function
  value (`c(|| note(2))`), and no structural form of rule D follows that value. Of the
  25 tier-2 rows that are tier-1 files, 16 closed, as in tier 1. Fixes 1 and 2 (the
  reviews of Z1) do not change these rows: the errors of Z1 close a fallback only if the
  old pipeline rejects the program, and each closed row is such a row. No program that
  is in scope without Z1 changes.

## Z2 (as built)

- Z2 closed the 8 RC rows of tier 1 (rows 35 to 42; 72 to 64 fallbacks of the census
  rows; tier 1 85 to 77 fallbacks of 5471 files with the new probes, also with fixes 1
  to 3 of the reviews of Z2). The five clean twins
  `b03`, `b07` to `b10` are in scope with no error (their record before R0k-c2 fix 1). The
  three oldmiss rows `n18`, `n19`, `p08` are rejected in scope (W0301 at the call of `run`
  in `main`: the copy of the frame of the call points into the group of the object).
  Tier 2 has no RC row. No other row of the census changes.

## Z3 (as built)

- Z3 closed 11 rows of tier 1 (rows 43 to 46 and 49 to 55; 64 to 53 fallbacks of the
  census rows; tier 1 77 to 74 fallbacks of 5502 files with the 31 new files, of which 8
  keep the fallback: refusal probes). Each bad twin is rejected in scope: `a05_bad`,
  `g26` and `e04b_bad` W0301; `o01_bad` W0502; `u12_bad`, `u13_bad` W0301 at the read of
  `h.f` (the three oldmiss rows of the stage). Each clean twin is in scope with no error.
- Rows 47 and 48 (`a02`, a value in a `Vec`) stay: part b is not built. With a design of
  part b, the clean twin `a02_vec_same_id_ok` gets a false W0301 of the parameter of a
  clause that runs at two nodes; main has the same false W0301 for that form with no
  `Vec` (`docs/plan/core-ir.md`, "Z3 as built"). The open-old entry `R0kB2-STAYS` goes;
  `R0z3-HEAP-SLOT` names `a02_vec_same_id_bad`.
- Tier 2 has no row of the stage.
- Fix 1 (the review of Z3): a `once` closure outside the handled body of a local
  `multi` handler is spared by its resume (`spared_at`). The first build gave a false
  W0503 for it on the review probe `e10_ok_twoRun` (main falls back and accepts it); main
  gives the same false W0503 on the forms in scope (`e08`, `e14`). No row of the census
  changes; the 7 new files of the fix are in scope (74 fallbacks of 5509 files).
- Fix 3 (the review of Z3, round 3): a write of the local of the way in a clause is a
  value of the way only in the form of `u13`. Rows 54 and 55 (`u13`) stay closed.
  Tier 1: 85 fallbacks of 5520 files (the 4 new refusal probes `w1`, `w2` keep the fallback); no other row changes.
- Fix 2 (the review of Z3, round 2): a region with two closures is refused if its clause
  can run at more than one node (the join of issue #79, in the one-local form), and the
  value of a capture joins only the closures that the state can have. The rows 52 to 55
  (`u12`, `u13`, one run) stay closed. Tier 1: 81 fallbacks of 5516 files (main 77 of 5471): the 11 census rows stay closed; of the files of the stage, the probes `a3` and `a5` (two runs of the local) and the refusal probes `n1`, `n2` keep the fallback.

## Z5 (as built)

- Z5 closed the 4 D1b rows of tier 1 (rows 56 to 59; 53 to 49 fallbacks of the census
  rows). A `resume` in a scope body of the clause through scope bodies only is a resume
  point; the task of the scope that is active at the `resume` conflicts at the `resume`
  with what the rest of the handled body reads, changes and frees. TC, the second reason
  of these rows, goes with the copies of R0k-a: the copy of the callee makes the perform
  a perform of the local handler, so the task runs the closure of the copy.
  `c2_task` and `rv_p12_c2_task_after_perform` (oldmiss) are rejected in scope (W0405 at
  the `resume`); `k04_c2_race_ok` and `rv_p12_c2_task_after_perform_ok` are in scope with
  no error.
- Tier 1: 85 fallbacks of 5562 files (main: 85 of 5520, and 125 of 5562 with the 42 new
  files of the stage: 41 probes `fixes/r0z5/` and the corpus program
  `202_scope_resume.wf`). Out of the census rows, `fixes/r0z/f1_scope_resumes_ok` (the
  clean twin of rule F) leaves the fallback too. Of the new files, five keep the
  fallback: `x1_runs_again_ok`, `y1_callee_twice_bad`, `y1_callee_twice_ok`,
  `y2_local_twice_bad`, `y2_local_twice_ok` (the clause runs again in the region of its
  `resume`, `SCOPE_RESUME_AGAIN`); `x1_runs_again_bad` is rejected by the pending rule.
- Tier 2 has no D1b row of the census (row 13, `m3b/p21376`, closed in Z1): 23
  fallbacks of 57393 files, as main, and no row changes its reason
  (`r3/quality/big/all_2.wf` was a time-out of 150 s in the census of main on a loaded
  machine).
- The open-old entry `R0h-STAYS` keeps only `rv_p04_c2_multi` (Z7).

## Z7 (as built)

- Z7 closed the 2 D5 rows of tier 1 (rows 60 and 61; 49 to 47 fallbacks of the census
  rows) and the D5 row of tier 2 (row 22; 23 to 22). In each of them the clause runs its
  parameter, and the value that the perform gives cannot resume more than once: the run of
  the function runs the clause with that value and finds no row, so the run of the
  parameter is no row and no `multi` point (`analysis::code_row`). `rv_p04_c2_multi`
  (oldmiss) is rejected in scope with the copy of the callee (W0301 at lines 5, 11 and 12:
  the run of `g` after the first `resume` reads `r`, which points into the cleared `v`);
  `rv_p04_c2_multi_ok` and `p1669` are in scope with no error. Before Z7 the weak form
  gave `rv_p04_c2_multi_ok` a false W0301 (the `multi_at` of the run of `g` at `Post` put
  the rest of `main` into the region of the `resume`).
- A row that the run of the function finds (a value that performs a `multi` operation of a
  handler of a caller) gets the re-entry of R0k-c2: the analysis of the program runs again
  with the node as a row of its clause (`frames::ClauseDynRows`). No census row has this
  form; the probes `fixes/r0z7/` have it (the test programs
  `crates/weft-check/tests/data/handlers/c15/clause_m.wf` and `clause_after_m.wf` have it
  too, but the refusal of the reviews keeps their row pending, as with main).
- Tier 1: 106 fallbacks of 5607 files (main: 85 of 5562, and 122 of 5607 with the 45 new
  files of the stage: 44 probes `fixes/r0z7/` and the corpus program
  `203_clause_value_rows.wf`). Of the new files, `o1_other_clause_ok` keeps the fallback
  (a refusal probe: the clause of `Run` gives the value to the clause of `Go`, whose row
  is not in the chain of the clause of `Run`), and so do the `r1_repeats` pair and the 20
  probes `z1`, `z3`, `g1`, `g3`, `c4`, `t3`, `s5`, `m1`, `m2`, `m3` of the reviews of Z7
  (the refusals `factgen::arg_shadow_gap` and `analysis::env_can_hold_refs`: a reference
  goes into the run); `o1_other_clause_bad` is rejected by the pending rule. No other
  fallback changes its reason. 12 files in scope lose the pending reason D5 (the `ir`
  pipeline rejected each of them with the weak form; with the full facts it rejects each
  but three, which lose a false error: `r2/oracle/fp3/W0503_p345`, a signed `lost-clean`
  entry, and the new probes `a1_between_ok`, `p1_param_ok`): `p345`, `e2_spared`,
  `or4_v1`, `f1_multi`, the corpus program and 7 new probes.
- Tier 2: 22 fallbacks of 57393 files (main 23); only `p1669` leaves the fallback, and no
  row comes in. `r3/quality/big/all_2.wf` (in scope, rule G) was a time-out of 150 s in
  the census of Z7 on a loaded machine (182 s with main, 263 s with Z7).
- The open-old entry `R0h-STAYS` goes.

## Z6 (as built)

- Z6 closed 10 rows of tier 1 (rows 62 to 71; 47 to 37 fallbacks of the census rows):
  the run of the local gets a dispatch (a test of the closure for each group, and a copy
  of the closure body in each arm, `docs/plan/core-ir.md`, "Z6 as built"). `u03`, `u05`,
  `u06`, `u07` and `u10` (oldmiss) are rejected in scope (W0301 at the read and at the
  run of the kept value); `u11`, `a01_two_paths_ok` and `a04_two_closures_ok` are in scope
  with no error; `a01_two_paths_bad` and `a04_two_closures_bad` are rejected in scope
  (W0301, as the old pipeline). `u10` needs Part B: the pre-scan gives the call of
  `do_sw` a copy, so the clause of `Sw` has one direct perform (the form of `u13`).
- Rows 72 and 73 (`a03_put_fns`) stay: Part C (a write through a reference into a local
  of the way, the field that `put_fns` writes) is cut. `a03_put_fns_bad` keeps the
  fallback, which rejects it (W0301); `a03_put_fns_ok` keeps the fallback, clean.
- Tier 1: 128 fallbacks of 5708 files (main 106 of 5607). Also `fixes/r0z3/a1_other_maker`
  (both twins) leaves the fallback; of the 101 new files the refusal probes keep it (the
  forms of R-JOIN, R-ROW, R-LOOP and the walk), and the probes of the review for the root
  fix of round 3 are in scope.
- The root fix of round 3 (`analysis::clause::call_landings` takes the handlers of
  `run_handlers`): a run of a function value that runs no clause gives nothing to the
  parameters of a clause. It removes a false W0301 of main in scope (the forms with one
  value of the review); no row of the census and no other row of the tiers changes.
- Tier 2 has no row of the stage: 22 fallbacks, as main.

## Z4 (as built)

- Z4 closed 10 rows of tier 1 (rows 74 to 81, 84 and 85; 37 to 27 fallbacks of the census
  rows): the run of the closure gets a kont region (a copy region that reads the
  continuation of the clause through its environment local, so the `resume` of the closure
  is a resume point of the clause; `docs/plan/core-ir.md`, "Z4 as built"). The bad twins of
  `c03`, `c05`, `c06`, `c07` and `c09` are rejected in scope (W0301, as the old pipeline);
  the clean twins are in scope with no error.
- Tier 2: row 23 (`m3a/p5750`) is rejected in scope (W0301 at line 81, as the old pipeline);
  22 to 21 fallbacks.
- The rows that stay: 82 and 83 (`c08_nested`) and tier 2 row 24 (`m3a/p7154`): a resume
  point in a handled body inside the clause (Part B) is not built; 86 and 87 (`fd2_v2`,
  `fd2_v3`, both tiers): a `multi` operation of another handler (R-ROW-K, the IR engine
  keeps the old continuation record in a copied frame, issue #94) and a value in a `Vec`
  (Z3 part b); 88 and 89 (`rr3_v19`, `rr3_v20`, both tiers): the runtime runs of Z4b are
  not built. Each keeps the fallback: the old pipeline rejects the bad ones, so no hole.
- Tier 1: 173 fallbacks of 5822 files (main 128 of 5708): the 10 rows above leave it, and
  55 of the 114 new files keep it (the refusal probes of `fixes/r0z4`, and its probes of
  Part B and Z4b). Tier 2: 21 fallbacks (main 22).

## Z8 (as built)

- Z8 closed 2 rows of tier 1 (rows 90 and 91; 27 to 25 fallbacks of the census rows) and 2
  rows of tier 2 (row 25, `g2/p2515`, and the copy of row 91, `verify/partb/p/g2_lexical`; 21
  to 19): `docs/plan/core-ir.md`, "Z8 as built". Each one is in scope with no error, as the
  old pipeline.
- Row 91 (`g2_lexical`, part a): the run of the closure that the inner clause gives back runs
  no clause of the inner handler (the closure performs through its capture of the outer
  capability), so the given-back rule of R0h does not apply there.
- Row 90 (`d02_multi_weak`, part b): the strong update of R0k-d1 after a `resume` of a
  `multi` continuation.
- Tier 2 row 25 (`p2515`, part c): the cause is not a closure body that no node runs. The
  closure `g2` runs `twice(f1)`, and `f1` performs through the capability of the handled
  body, which `g2` captures too. The run in the closure body is a perform through that
  capture of `g2` (as R0d for a capture of a capture).
- Row 25 (`q01_85_after_resume_bad`) stays: the closure of `Note` goes into the clause of
  `Run` through a call of a function value (`c(|| note(2))`), not through the result of a
  perform; the old pipeline rejects it (W0313), so no hole.
- Tier 1: 180 fallbacks of 5895 files (main 211 of 5895): the 2 rows above leave it, and 29
  of the 73 new files (`fixes/r0z8`, the corpus program `206_handler_env_leftovers`); 9 new
  files keep it (the refusal probes of the stage, R-DEAD among them, and three bad probes
  that the old pipeline checks, as with main). Tier 2: 19 fallbacks (main 21).
- Review round 2 (R-DEAD): a closure that no node runs and that runs a closure of its maker
  keeps the pending escape of main, so no row in scope on main leaves the scope; the census
  rows are as above.

## Z9b (as built)

- Z9b closed 1 row of tier 1 (row 92, `fixes/r0kd2/s4_spawn_in_closure_ok`; 25 to 24
  fallbacks of the census rows) and no row of tier 2 (19 stay: no row of tier 2 has the
  form): `docs/plan/core-ir.md`, "Z9b as built". The row is in scope with no error, as the
  old pipeline.
- Row 92: the cause of the plan is the real cause (`TASK_LATE`: a spawn in a closure on the
  scope of the scope body gets the rule of R0j, two whole writes of `f`). The spawn now has
  a window up to the end of the scope (`templates::outer_window`): the function around the
  scope waits at the scope, so its two writes of `f` before the scope do not count.
- Tier 1: 185 fallbacks of 5929 files (main 196 of 5929). The new files are the 33 probes
  of `fixes/r0z9b` and the corpus program `207_spawn_window`; main sends 16 of them to the
  old pipeline. The row above leaves the fallback, and so do 10 of these 16; the other 6
  keep it (the refusal probes of the stage: a write of the scope body before the closure, a
  `join` in the scope body, a scope in a clause, in a task or in a closure, a write after
  the scope in a loop). Tier 2: 19 fallbacks (main 19); no row of tier 2 has the form.
- No row in scope on main leaves the scope, and no row changes its codes.
- Review round 2 (R-ESCAPE): a function value that can leave the function around the
  scope (its result, a parameter, an operation of a user effect) keeps the rule of R0j.
  Without it, four review probes (a closure that spawns on the scope is returned, put in a
  returned struct, stored through a reference parameter or pushed into a `Vec`
  parameter) came into scope with no error and faulted (the task runs in the caller):
  lost faults. Row 92 and the clean probes of the stage have no such way out, so the
  census rows are as above. The probes `x01_return_escape_bad`, `x02_struct_return_bad`,
  `x03_vec_param_bad` and `x01_return_fn_ok` keep the fallback, as on main.


## Z9a (as built)

- Z9a closed 3 rows of tier 1 (rows 95 to 97: `i9_kept_write`, `s8_steal_fnparam`,
  `s9_steal_stored`; 24 to 21 fallbacks of the census rows; rows 93 and 94,
  `c09_cc_during_ok` and `j01_again_ok`, closed in the first build and went back to the
  fallback in review round 3, by R-CODE: code of a caller `g(f)` runs a value of the body
  again on the task) and 4 rows of tier 2 (row 26, `m2/p7046`, and the copies of `i9`, `s8`, `s9`; 19 to
  15): `docs/plan/core-ir.md`, "Z9a as built". Each row is in scope with no error. `i9`
  (old W0405) and `s9` (old W0302) are `lost-clean` (ledger entries, signed by the builder
  only; `s9` is a point for the review: the old analysis moves `fs` into the task closure,
  the IR copies the function value).
- The cause of the plan is the real cause (`TASK_AGAIN`: a run with `again` and not
  `order`). A spawn whose task runs a value more than once has a second node of the run
  (`Task(1)` after `Main`); the run happens at both nodes, and the task starts at the
  second one.
- Tier 1: 187 fallbacks of 5970 files (main 208 of 5970). The new files are the 36 probes
  of `fixes/r0z9a` and the corpus program `208_task_runs_again`; main sends 19 of them to
  the old pipeline. The rows above leave the fallback, and so do 16 of these 19; the other
  3 keep it (`e09_closure_body_ok`: `VALUE_TASKS`, Z9c; the refusal probes `r01_fork_ok`,
  R-FORK, and `r02_inner_task_ok`, R-INNER). Tier 2: 15 fallbacks (main 19).
- Review round 1: the 14 new probes of B1 and R-ONCE (`g01` to `g08`). Tier 1: 189
  fallbacks of 5984 files (main 220 of 5984); the 10 probes `g01` to `g05` that main sends
  to the old pipeline leave it; `g07_stored_once_bad` and `g08_stored_once_twice_bad` keep
  it (R-ONCE), as on main. The census rows stay 24 to 19 and 19 to 15.
- Review round 2: the 8 new probes `h01` to `h04`. Tier 1: 190 fallbacks of 5992 files
  (main 223 of 5992); `h04_reassign_loop_ok` keeps it (R-REBIND), as on main. The census
  rows stay 24 to 19 and 19 to 15.
- Review round 3: the 7 new probes `i01` to `i04`. R-CODE puts rows 93 and 94 back, so the
  census rows are 24 to 21 in tier 1 (19 to 15 in tier 2: no row of tier 2 has the form).
- No row in scope on main leaves the scope. Three rejected rows of main get one more W0301
  at the spawn, the code of the old pipeline (`tests/programs/114_repeated_callbacks`,
  `verify/s5/p/or3c`, `verify/s5/repro/V4_or3_containers`).
## Z9c-A (as built)

- Z9c-A (part A of Z9c: the `with` of a task of a call slot, C1 of the design review)
  closes no row and opens none: `docs/plan/core-ir.md`, "Z9c-A as built". It only adds
  rejections: the summary of a body keeps the values of the interface that a callee runs
  with a task of a call slot, so eight old holes of main close (`fixes/r0z9c`; two of them
  are review probes of the design).
- Tier 1: 199 fallbacks of 6038 files with main and with Z9c-A, the same rows and the
  same reasons (`check --reasons`, `weft-work/z9c/census/`). The new files are the 38
  probes of `fixes/r0z9c` and the corpus program `209_slot_task_with`; each one is in
  scope with both. The census rows stay 21. Tier 2 (the rows of the Z8 list): 15
  fallbacks and 6 time-outs with both, the same rows.

## Z9c-B (as built)

- Z9c-B (part B of Z9c: the late slots of a call, the capture slots, proof P2) closes
  rows 100 (`j04_value_ok`) and 104 (`s3_nested_closure_ok`) of tier 1, and rows 27
  (`g3b/p18574`) and 30 (`gen3_15687`) of tier 2: `docs/plan/core-ir.md`, "Z9c-B as
  built". The probe `fixes/r0z9a/e09_closure_body_ok` leaves the fallback too. Rows 102
  and 103 (`c16`) stay: the copy of `mk_cap` gives the capture to a perform whose clause
  is code of a caller that can run it more than once (R-VCODE).
- Tier 1: 239 fallbacks of 6107 files with main, 229 with Z9c-B (`check --reasons`,
  `weft-work/z9cb/census/`, after review round 4). Of the 6038 files of Z9c-A, 199 to
  196; the census rows go from 21 to 19. The new files are the probes of `fixes/r0z9cb`
  and the corpus program `210_capture_slots`; seven clean twins come into scope, and the
  refusal probes keep `VALUE_TASKS`. Tier 2 (the rows of the Z8 list): 15 fallbacks and 5
  time-outs with main, 13 and 5 with Z9c-B (6 and 6 in the run of review round 4: large
  files at the time limit). Row 27 (`p18574`) becomes `lost-clean` (old
  W0312, no fault): a ledger entry, signed by the reviewer of round 1 of the stage.

## Z9c-C (as built)

- Z9c-C (part C of Z9c: the nested slots of a call, part 2) closes rows 98 (`a13_ok`) and
  101 (`j07_run_ok`) of tier 1: `docs/plan/core-ir.md`, "Z9c-C as built". The probes
  `fixes/r0z/c1_sim_param_task_ok` and `rv2_n06_collide_e_ok` leave the fallback too. Part
  4 (row 105, `c10`, and its copy in tier 2) is out after review round 1 (a lost race and a
  lost W0502 of that path): the row stays open for a later stage. Row 99 (`j03_nested_ok`)
  and rows 28, 29 and 31 of tier 2 stay: a value that the run node knows (part 3, stage
  Z9d: row 99 closes there, rows 28, 29 and 31 stay, "Z9d (as built)").
- Tier 1: 311 fallbacks of 6205 files with main, 293 with Z9c-C (`check --reasons`,
  `weft-work/z9cc/census/`, after review round 2). Of the 6107 files of Z9c-B, 229 to 225;
  the census rows go from 19 to 17. The new files are the 97 probes of `fixes/r0z9cc` and
  the corpus program `211_nested_slots`; 14 come into scope, 16 bad twins are in scope
  with main too (the pending rule rejects them), and the refusal probes and the probes of
  review rounds 1 and 2 keep `NESTED_TASK_RUN`.
- Tier 2 (the rows of the Z8 list): 13 fallbacks and 5 time-outs with main and with
  Z9c-C. No row becomes `lost-clean`.

## Z9d (as built)

- Z9d (part 3 of Z9c: the nested slot of a value that the run node knows, and of a value
  that the callee gives to the closure) closes row 99 (`j03_nested_ok`) of tier 1:
  `docs/plan/core-ir.md`, "Z9d as built". Rows 28 (`p25005`), 29 (`p148`) and 31
  (`gen3_18180`) of tier 2 stay: R-NREF of the locals (`transfer::plain_bodies`, a
  refusal of Z9c-C) refuses them, as each one has a local that can hold a reference or an
  `rc` handle (the reference temporaries of method calls, a struct with a function field,
  a reference result, an `rc` handle from a call). No row becomes `lost-clean`.
- Tier 1: 315 fallbacks of 6246 files with main, 305 with Z9d (`check --reasons`,
  `weft-work/z9d/census/`). Of the 6205 files of Z9c-C, 293 to 292; the census rows go
  from 17 to 16. The new files are the 40 probes of `fixes/r0z9d` and the corpus program
  `212_nested_known`; the 9 clean probes `p01` to `p09` come into scope, and the refusal
  probes keep `NESTED_TASK_RUN`.
- Tier 2 (the rows of the Z8 list): 13 fallbacks and 6 time-outs with main and with Z9d.

## Z10 (as built)

- Z10 (the chain: a memo of the walk of a run node) closes rows 32 to 35 of tier 2
  (`closure_chain_100`, `_200`, `_400`, `_800`): `docs/plan/core-ir.md`, "Z10 as built". Each
  one has full facts of the `ir` pipeline and no error, as the old pipeline gives
  (`closure_chain_800`: 18 s with `weft check`). The depth bound stays only as a limit of the
  resources (1024 levels, and 4096 values at a run node of a chain deeper than 64). No
  W0706, no `new-fp` entry and no `lost-clean` entry.
- Tier 1: 368 fallbacks of 6346 files with main, 324 with Z10 (`check --reasons`,
  `weft-work/z10/census/`). Of the 6246 files of Z9d, 305 with both; the census rows stay
  16. The new files are the 100 probes of `fixes/r0z10`: 63 fallbacks with main, 19 with Z10.
- Tier 2 (the rows of the Z8 list): 13 fallbacks and 6 time-outs with main, 9 fallbacks and
  6 time-outs with Z10.

## Columns

- Reason: the reason of the note. `C2` a function value that an operation gives to a
  handler (`OP_KEPT`); `D1` a `resume` of a captured continuation (`KONT_CAPTURED`); `D3`
  a call that runs a clause of a local handler whose operation gives a value back
  (`GIVES_BACK`); `RC` a reference into an `rc` group in a copied frame across a `multi`
  operation (`RC_ACROSS_ROW`; stage Z2 removes the rule); `NESTED` a function value that a function value of a callee
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
| 1 | `fixes/r0k2/u04_task_reassigns.wf` | C2 | a scope task gives `k` a closure with a capability of a local handler | W0314 | fault | rejected | yes | Z1-A (closed) |
| 2 | `fixes/r0k2/u08_task_join.wf` | C2 | a joined task gives `k` a closure with a capability of a local handler | W0314 | fault | rejected | yes | Z1-A (closed) |
| 3 | `fixes/r0k2/u09_fork.wf` | C2 | a fork branch gives `k` a closure with a capability of a local handler | W0314, W0403 | fault | rejected | yes | Z1-A (closed) |
| 4 | `fixes/r0kb2/u14_task_bad.wf` | C2 | a second write by a task; the task holds a capability of a local handler | W0314 | fault | rejected | yes | Z1-A (closed) |
| 5 | `fixes/r0kb2/u14_task_ok.wf` | C2 | a second write by a task (old W0314 on both twins) | W0314 | no fault | rejected | yes | Z1-A (closed) |
| 6 | `r2/oracle/min/or_resume_in_task.wf` | D1 | task resume: `resume` in a spawn closure | 2xW0314 | fault | rejected | no | Z1-A (closed) |
| 7 | `r2/oracle/probes/i3_resume_task.wf` | D1 | task resume: `resume` in a spawn closure | W0314 | fault | rejected | no | Z1-A (closed) |
| 8 | `r2/oracle/probes/i3b_resume_task.wf` | D1 | task resume: `resume` in a spawn closure | W0314 | fault | rejected | no | Z1-A (closed) |
| 9 | `r2/oracle/repro/OR9_resume_in_task.wf` | D1 | task resume: `resume` in a spawn closure | 2xW0314 | fault | rejected | no | Z1-A (closed) |
| 10 | `verify/s5/R2c/p/c2.wf` | D1 | task resume: through a field, a callee in the task, a named closure, a fork branch (no `main` body) | 4xW0314 | no fault | rejected | no | Z1-A (closed) |
| 11 | `verify/s5/R2c: .../p/rr3_v15_spawn_nested_closure.wf` | D1 | task resume: a task runs a closure that runs the resuming closure | W0314 | no fault | rejected | no | Z1-A (closed) |
| 12 | `verify/s5/R2c: .../p/rr3_v16_spawn_via_callee.wf` | D1 | task resume: a callee runs the resuming closure as a task | W0314 | no fault | rejected | no | Z1-A (closed) |
| 13 | `verify/s5/R2c: .../p/rr3_v17_fork.wf` | D1 | task resume: a fork branch resumes | W0314 | no fault | rejected | no | Z1-A (closed) |
| 14 | `fixes/r0h/d3f_task.wf` | D3>TC | the callee runs the closure of the clause on a task (the copy brings in a task that runs code of a caller) | W0314 | no fault | rejected | no | Z1-B (closed) |
| 15 | `fixes/r0j/j05_code_old.wf` | TC | a task runs a value of an operation (code of a caller) | W0314 | no fault | rejected | yes | Z1-B (closed) |
| 16 | `fixes/r0e/a13_sim_param_task.wf` | F18 | a parameter spawned inside `sim.run`; the value holds the capability of a local handler | W0314 | fault | rejected | no | Z1-C (closed) |
| 17 | `fixes/r0e/a13b_callee_param_task.wf` | F18 | a parameter spawned in a closure that a callee runs; the value holds a capability | W0314 | fault | rejected | no | Z1-C (closed) |
| 18 | `fixes/r0e/a13c_callee_bg_param.wf` | F18 | as a13b, through a second callee | W0314 | fault | rejected | no | Z1-C (closed) |
| 19 | `fixes/r0j/j07_run_bad.wf` | F18 | as a13 (a task of `sim.run` performs through a handler of the spawning task) | W0314 | fault | rejected | yes | Z1-C (closed) |
| 20 | `verify/partb/S3/p/sim1.wf` | F18 | `sim.run` and tasks with capability values, no `main` | 4xW0314, 2xW0702 | no `main` | rejected | no | Z1-C (closed) |
| 21 | `fixes/r0kb1/c11_c2_loop_instance_bad.wf` | C2 | extent rule: a new handler instance in a loop; the value goes through a local outside the handled body | W0301, W0313 | fault | rejected | yes | Z1-D (closed) |
| 22 | `fixes/r0kb1/c11_c2_loop_instance_ok.wf` | C2 | extent rule (clean twin; the old W0313 is the language rule "not through a local outside it") | W0313 | no fault | rejected | yes | Z1-D (closed) |
| 23 | `fixes/r0kb1/n04_loop_instance_bad.wf` | C2 | extent rule: as c11, a closure of the same function | W0301, W0313 | fault | rejected | yes | Z1-D (closed) |
| 24 | `fixes/r0kb1/n04_loop_instance_ok.wf` | C2 | extent rule (clean twin; old W0313) | W0313 | no fault | rejected | yes | Z1-D (closed) |
| 25 | `fixes/r0kb2/q01_85_after_resume_bad.wf` | C2>esc | the clause of `Run` runs a capability closure of `Note` after its `resume` (outside `Note`) | W0313 | fault | rejected | no | Z8 (open: Z1-D has no form for a value through a call of a function value; not the form of Z8 part a, "Z8 (as built)") |
| 26 | `verify/partb/p/a4_get_own.wf` | C2 | a closure that performs through `Get` goes to an operation of `Get` itself | W0313 | fault | rejected | no | Z1-D (closed) |
| 27 | `verify/s5/S5a/x/p/e2b_e_job.wf` | C2>VT | forms 2 to 4 with a clause that spawns its argument (capability of `Note` to `Run`, `RunJ`) | 2xW0313, 5xW0314 | fault | rejected | no | Z1-G (closed; planned Z1-D) |
| 28 | `verify/s5/S5a/x/p/e2b_e_mk_job.wf` | C2>VT | as e2b_e_job | 2xW0313, 5xW0314 | fault | rejected | no | Z1-G (closed; planned Z1-D) |
| 29 | `verify/s5/S5a/x/p/e2b_e_struct.wf` | C2>VT | as e2b_e_job | 2xW0313, 5xW0314 | fault | rejected | no | Z1-G (closed; planned Z1-D) |
| 30 | `verify/s5/S5a/x/p/e2b_variants.wf` | C2>VT | as e2b_e_job | 2xW0313, 5xW0314 | fault | rejected | no | Z1-G (closed; planned Z1-D) |
| 31 | `verify/s5/diff/p/v1c_stored.wf` | C2 | form 3: a closure in a field run by `run_it`; the clause keeps the value in a local outside | W0313 | fault | rejected | no | Z1-D (closed) |
| 32 | `fixes/r0e/rv1_b2_h10.wf` | NESTED | a closure that a callee runs spawns a `once` value two times | W0502 | fault | rejected | yes | Z1-E (closed) |
| 33 | `fixes/r0e/rv1_b2_h18.wf` | NESTED | a callee runs the closure that spawns a `once` value two times | W0502 | fault | rejected | yes | Z1-E (closed) |
| 34 | `verify/partb/p/a2_escapes.wf` | C2 | a capability closure as the value of a handled body (via `id`, `wrap`, `pair`, `pop`, ...), no `main` | W0301, 9xW0313 | no `main` | rejected | no | Z1-G (closed) |
| 35 | `fixes/r0kc2b/b03_rc_between_ok.wf` | RC | rc-across-multi: an `rc` object shared between the copies | clean | no fault | clean | no | Z2 (closed) |
| 36 | `fixes/r0kc2b/b07_abort_in_copy_ok.wf` | RC | rc-across-multi: an abort in a copy | clean | no fault | clean | no | Z2 (closed) |
| 37 | `fixes/r0kc2b/b08_handled_after_ok.wf` | RC | rc-across-multi: the rest of the handled body runs again | clean | no fault | clean | no | Z2 (closed) |
| 38 | `fixes/r0kc2b/b09_post_row_ok.wf` | RC | rc-across-multi: a row after the `resume` | clean | no fault | clean | no | Z2 (closed) |
| 39 | `fixes/r0kc2b/b10_post_row_after_ok.wf` | RC | rc-across-multi: a row after the `resume`, a read after the handler | clean | no fault | clean | no | Z2 (closed) |
| 40 | `fixes/r0kc2c/n18_rc_handled_frame_bad.wf` | RC | rc-across-multi: the handled body of `run` holds a reference into the `rc` across `pick` | clean | fault | oldmiss | no | Z2 (closed) |
| 41 | `fixes/r0kc2c/n19_rc_param_arg_bad.wf` | RC | rc-across-multi: a reference into the `rc` as the argument of `pick` | clean | fault | oldmiss | no | Z2 (closed) |
| 42 | `fixes/r0kc2c/p08_rc_between_param_bad.wf` | RC | rc-across-multi: a reference into the `rc` through a parameter of `run` | clean | fault | oldmiss | no | Z2 (closed) |
| 43 | `fixes/r0k2/a05_by_value_bad.wf` | D3 | a `ByMove` capture (static copy refused) | W0301 | fault | rejected | yes | Z3 (closed) |
| 44 | `fixes/r0k2/a05_by_value_ok.wf` | D3 | a `ByMove` capture (clean twin) | clean | no fault | clean | yes | Z3 (closed) |
| 45 | `fixes/r0k2/g26_weak_run_in_callee_bad.wf` | C2 | weak guard order: the weak value goes to `apply`, which the analysis runs before the maker | W0301, W0403, W0405 | fault | rejected | yes | Z3 (closed) |
| 46 | `fixes/r0kb1/n03_clause_runs_ok.wf` | A | form 4 (a clause runs its parameter): the copy region exists, but copies apply only to C2 and D3 | clean | no fault | clean | yes | Z3 (closed) |
| 47 | `fixes/r0kb2/a02_vec_same_id_bad.wf` | C2 | heap slot: one closure id two times in a `Vec`, other captures | clean | fault | oldmiss | yes | Z3 (open: part b not built; the clean twin gets a false W0301 of a clause that runs at two nodes, issue #79) |
| 48 | `fixes/r0kb2/a02_vec_same_id_ok.wf` | C2 | heap slot (clean twin) | clean | no fault | clean | yes | Z3 (open: part b not built; the clean twin gets a false W0301 of a clause that runs at two nodes, issue #79) |
| 49 | `fixes/r0kb2/e04b_field_read_bad.wf` | C2>A | form 3 with a read of another part: no `sole`, so the copy needs the rest of the handled body | clean | fault | oldmiss | yes | Z3 (closed) |
| 50 | `fixes/r0kb2/o01_once_two_runs_bad.wf` | C2 | once: a copy of a `once` closure is refused; two runs | W0502 | fault | rejected | yes | Z3 (closed) |
| 51 | `fixes/r0kb2/o01_once_two_runs_ok.wf` | C2 | once: one run (clean twin) | clean | no fault | clean | yes | Z3 (closed) |
| 52 | `fixes/r0kb2/u12_scope_body_bad.wf` | C2 | a second write of the local of the way by a scope body (the same closure id) | clean | fault | oldmiss | yes | Z3 (closed) |
| 53 | `fixes/r0kb2/u12_scope_body_ok.wf` | C2 | a second write by a scope body (clean twin) | clean | no fault | clean | yes | Z3 (closed) |
| 54 | `fixes/r0kb2/u13_clause_bad.wf` | C2 | a second write of the local of the way by a clause (the same closure id) | clean | fault | oldmiss | yes | Z3 (closed) |
| 55 | `fixes/r0kb2/u13_clause_ok.wf` | C2 | a second write by a clause (clean twin) | clean | no fault | clean | yes | Z3 (closed) |
| 56 | `fixes/r0h/c2_task.wf` | D1 | D1b: the clause spawns the value, then resumes in the scope body; the rest of the handled body writes what the task reads | clean | fault | oldmiss | no | Z5 (closed) |
| 57 | `fixes/r0k/k04_c2_race_ok.wf` | D1 | D1b (clean twin) | clean | no fault | clean | no | Z5 (closed) |
| 58 | `fixes/r0k/rv_p12_c2_task_after_perform.wf` | D1 | D1b: as c2_task; the callee spawns a writer after the perform | clean | fault | oldmiss | no | Z5 (closed) |
| 59 | `fixes/r0k/rv_p12_c2_task_after_perform_ok.wf` | D1 | D1b (clean twin) | clean | no fault | clean | no | Z5 (closed) |
| 60 | `fixes/r0k/rv_p04_c2_multi.wf` | C2>D5 | a `multi` clause runs the value between two `resume`s; the copy brings in a row that only the analysis finds | clean | fault | oldmiss | no | Z7 (closed) |
| 61 | `fixes/r0k/rv_p04_c2_multi_ok.wf` | C2>D5 | as rv_p04 (clean twin) | clean | no fault | clean | no | Z7 (closed) |
| 62 | `fixes/r0k2/a04_two_closures_bad.wf` | D3 | two closures can reach the local (static copy refused) | W0301 | fault | rejected | no | Z6 (closed) |
| 63 | `fixes/r0k2/a04_two_closures_ok.wf` | D3 | two closures (clean twin) | clean | no fault | clean | no | Z6 (closed) |
| 64 | `fixes/r0k2/u03_callee_reassigns_via_clause.wf` | C2 | two values at the run node: a clause of another handler gives `k` a second closure | clean | fault | oldmiss | no | Z6 (closed) |
| 65 | `fixes/r0k2/u05_scope_body.wf` | C2 | two values at the run node: a scope body gives `k` a second closure | clean | fault | oldmiss | no | Z6 (closed) |
| 66 | `fixes/r0k2/u06_handled_body.wf` | C2 | two values at the run node: a nested handled body gives `k` a second closure | clean | fault | oldmiss | no | Z6 (closed) |
| 67 | `fixes/r0k2/u07_if_branch.wf` | C2 | two values at the run node: an `if` branch gives `k` a second closure | clean | fault | oldmiss | no | Z6 (closed) |
| 68 | `fixes/r0k2/u10_clause_of_inner.wf` | C2 | two values at the run node: a clause that a perform of a callee runs gives `k` a second closure | clean | fault | oldmiss | no | Z6 (closed) |
| 69 | `fixes/r0k2/u11_clause_harmless_then.wf` | C2 | two values at the run node: a clause gives `k` a harmless closure (clean twin of the u family) | clean | no fault | clean | no | Z6 (closed) |
| 70 | `fixes/r0kb2/a01_two_paths_bad.wf` | C2 | form 2 with two values: `mk` gives back one of two closures | W0301 | fault | rejected | no | Z6 (closed) |
| 71 | `fixes/r0kb2/a01_two_paths_ok.wf` | C2 | form 2 with two values (clean twin) | clean | no fault | clean | no | Z6 (closed) |
| 72 | `fixes/r0kb2/a03_put_fns_bad.wf` | C2 | a borrow of the local of the way: `put_fns` writes the field before the run | W0301 | fault | rejected | yes | Z6 (open: part C is cut; a later stage) |
| 73 | `fixes/r0kb2/a03_put_fns_ok.wf` | C2 | a borrow of the local of the way (clean twin) | clean | no fault | clean | yes | Z6 (open: part C is cut; a later stage) |
| 74 | `fixes/r0kc/c03_two_runs_bad.wf` | D1 | D1a refusal: two runs | W0301 | fault | rejected | yes | Z4 (closed) |
| 75 | `fixes/r0kc/c03_two_runs_ok.wf` | D1 | D1a refusal: two runs (clean twin) | clean | no fault | clean | yes | Z4 (closed) |
| 76 | `fixes/r0kc/c05_perform_between_bad.wf` | D1 | D1a refusal: a perform between the make and the run | W0301 | fault | rejected | yes | Z4 (closed) |
| 77 | `fixes/r0kc/c05_perform_between_ok.wf` | D1 | D1a refusal: a perform between (clean twin) | clean | no fault | clean | yes | Z4 (closed) |
| 78 | `fixes/r0kc/c06_call_between_bad.wf` | D1 | D1a refusal: a call between the make and the run | W0301 | fault | rejected | yes | Z4 (closed) |
| 79 | `fixes/r0kc/c06_call_between_ok.wf` | D1 | D1a refusal: a call between (clean twin) | clean | no fault | clean | yes | Z4 (closed) |
| 80 | `fixes/r0kc/c07_use_after_bad.wf` | D1 | D1a refusal: a borrow of the closure value | W0301 | fault | rejected | yes | Z4 (closed) |
| 81 | `fixes/r0kc/c07_use_after_ok.wf` | D1 | D1a refusal: a borrow (clean twin) | clean | no fault | clean | yes | Z4 (closed) |
| 82 | `fixes/r0kc/c08_nested_bad.wf` | D1 | D1a refusal: a body inside the clause makes and runs the closure | W0301 | fault | rejected | yes | Z4 |
| 83 | `fixes/r0kc/c08_nested_ok.wf` | D1 | D1a refusal: a body inside the clause (clean twin) | clean | no fault | clean | yes | Z4 |
| 84 | `fixes/r0kc/c09_field_bad.wf` | D1 | D1a refusal: the closure goes through a field | W0301 | fault | rejected | yes | Z4 (closed) |
| 85 | `fixes/r0kc/c09_field_ok.wf` | D1 | D1a refusal: a field (clean twin) | clean | no fault | clean | yes | Z4 (closed) |
| 86 | `verify/s5/R2c: .../p/fd2_v2_closure_resume.wf` | D1 | D1a in a `multi` clause: a perform between, two runs | clean | no fault | clean | no | Z4 |
| 87 | `verify/s5/R2c: .../p/fd2_v3_vec_of_closures.wf` | D1 | D1a through a `Vec` (heap slot), a perform between | clean | no fault | clean | no | Z4 |
| 88 | `verify/s5/R2c: .../p/rr3_v19_sim_run_closure.wf` | D1 | runtime run: `resume` in the block of `sim.run` | clean | no fault | clean | no | Z4b |
| 89 | `verify/s5/R2c: .../p/rr3_v20_with_timeout.wf` | D1 | runtime run: `resume` in the block of `with_timeout` | clean | no fault | clean | no | Z4b |
| 90 | `fixes/r0kd1/d02_multi_weak.wf` | esc | D4 multi: the update after a `multi` resume stays weak, so a closure seems to run outside its handler | clean | no fault | clean | yes | Z8 (closed) |
| 91 | `verify/partb/p/g2_lexical.wf` | D3 | a value through a `resume`: the inner clause gives back a closure that performs to the outer handler | clean | no fault | clean | no | Z8 (closed) |
| 92 | `fixes/r0kd2/s4_spawn_in_closure_ok.wf` | E4 | a spawn in a closure on the scope of the outer body; two writes of `f` | clean | no fault | clean | yes | Z9b (closed) |
| 93 | `fixes/r0f/c09_cc_during_ok.wf` | E2 | two values: code of a caller runs `f` once on the task (the c09 subset of R0k-d3) | clean | no fault | clean | no | Z9a (open: R-CODE) |
| 94 | `fixes/r0j/j01_again_ok.wf` | E2 | code of a caller runs `f` two times on the task | clean | no fault | clean | yes | Z9a (open: R-CODE) |
| 95 | `r3/oracle/probes/i9_kept_write.wf` | E2 | a task runs a kept callback more than once | W0405 | no fault | rejected | no | Z9a (closed) |
| 96 | `r3/oracle/probes/s8_steal_fnparam.wf` | E2 | a task runs a function parameter more than once | clean | no fault | clean | no | Z9a (closed) |
| 97 | `r3/oracle/probes/s9_steal_stored.wf` | E2 | a task runs a stored callback more than once | W0302 | fault (AST engine only) | rejected | no | Z9a (closed) |
| 98 | `fixes/r0e/a13_ok.wf` | NESTED | a spawn of a parameter inside `sim.run` of a callee (task of a callee, no `TaskHow`) | clean | no fault | clean | no | Z9c-C (closed) |
| 99 | `fixes/r0j/j03_nested_ok.wf` | NESTED | a closure spawns a parameter and a task; the closure runs in a callee (two levels of runs) | clean | no fault | clean | yes | Z9d (closed) |
| 100 | `fixes/r0j/j04_value_ok.wf` | VT | a closure spawns a captured closure two times (tasks of a value of the interface) | clean | no fault | clean | yes | Z9c-B (closed) |
| 101 | `fixes/r0j/j07_run_ok.wf` | F18 | a parameter spawned inside `sim.run`; the value changes a local of its maker (task of a callee, no `TaskHow`) | clean | no fault | clean | yes | Z9c-C (closed) |
| 102 | `fixes/r0kb1/c16_c2_nested_bad.wf` | C2>VT | a nested closure in the closure of the maker `mk_cap` (VALUE_TASKS in the facts of the maker) | W0301 | fault | rejected | yes | Z9c |
| 103 | `fixes/r0kb1/c16_c2_nested_ok.wf` | C2>VT | a nested closure in the maker (clean twin) | clean | no fault | clean | yes | Z9c |
| 104 | `fixes/r0kd2/s3_nested_closure_ok.wf` | VT | a task closure runs a value from the environment of the closure that makes the scope | clean | no fault | clean | no | Z9c-B (closed) |
| 105 | `verify/review_core/Core_S2/probes/crash/c10.wf` | NESTED | a recursive higher-order function `y(f)`, no `main` (the worst case of a recursive callee: a task run) | clean | no `main` | clean | no | Z9c (open: part 4 is out after review round 1 of Z9c-C; a later stage) |

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
| 1 | `r3/oracle/runs/m3a/p1414.wf` | D1 | task resume: `fork(|| resume(()), ..)` | W0314 | no fault | rejected | no | Z1-A (closed) |
| 2 | `r3/oracle/runs/m3a/p316.wf` | D1 | task resume: `s.spawn(|| resume(1))` | W0314 | no fault | rejected | no | Z1-A (closed) |
| 3 | `r3/oracle/runs/m3a/p4859.wf` | D1 | task resume: `fork(|| resume(()), ..)` | W0314 | no fault | rejected | no | Z1-A (closed) |
| 4 | `r3/oracle/runs/m3a/p5452.wf` | D1 | task resume: `s.spawn(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A (closed) |
| 5 | `r3/oracle/runs/m3a/p5483.wf` | D1 | task resume: `spawn_m(|| resume(()))` (a callee spawns its parameter) | W0314 | no fault | rejected | no | Z1-A (closed) |
| 6 | `r3/oracle/runs/m3a/p6530.wf` | D1 | task resume: `spawn_m(|| resume(()))` | W0301, W0314 | no fault | rejected | no | Z1-A (closed) |
| 7 | `r3/oracle/runs/m3a/p7888.wf` | D1 | task resume: `spawn_m(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A (closed) |
| 8 | `r3/oracle/runs/m3b/p21941.wf` | D1 | task resume: `spawn_m(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A (closed) |
| 9 | `r3/oracle/runs/m3b/p22442.wf` | D1 | task resume: `spawn_m(|| print(k))` holds the resuming closure | W0301, W0314 | no fault | rejected | no | Z1-A (closed) |
| 10 | `r3/oracle/runs/m3b/p25672.wf` | D1 | task resume: `s.spawn(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A (closed) |
| 11 | `r3/oracle/runs/m3b/p26278.wf` | D1 | task resume: `spawn_m(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A (closed) |
| 12 | `r3/oracle/runs/m3b/p27232.wf` | D1 | task resume: `s.spawn(|| resume(()))` | W0314 | no fault | rejected | no | Z1-A (closed) |
| 13 | `r3/oracle/runs/m3b/p21376.wf` | D1 | D1b: two `resume`s of a `once` continuation in a scope body | W0501 | no fault | rejected | no | Z1-F (closed) |
| 14 | `r3/oracle/runs/m3a/p6152.wf` | C2 | a body with a `typeck` error (W0102) and a C2 body | W0102, W0401, W0405, 4xW0503 | no fault | rejected | no | Z1-G (closed) |
| 15 | `r3/oracle/runs/m3b/p26666.wf` | C2 | errors (W0314, W0403, W0405) in bodies that do not call the C2 body | W0314, W0403, 3xW0405 | no fault | rejected | no | Z1-G (closed) |
| 16 | `r3/quality/big/all.wf` | C2>E2 | a concatenation of the corpus: W01xx errors of `typeck` | 50 codes (W01xx to W1004) | no fault | rejected | no | Z1-G (closed) |
| 17 | `r3/quality/big/all_2.wf` | C2>E2 | as all.wf (two copies) | 50 codes (W01xx to W1004) | timeout | rejected | no | Z1-G (closed) |
| 18 | `verify/s5/S5c/mut/progs/m00982_85_op_args.wf` | C2>D1 | a mutant of 85, no `main`: errors in other bodies (W0313, W0314) | W0313, 10xW0314, W0501 | no `main` | rejected | no | Z1-G (closed) |
| 19 | `verify/s5/S5c/mut/progs/m01268_85_op_args.wf` | C2>D1 | as m00982 | W0313, 11xW0314 | no `main` | rejected | no | Z1-G (closed) |
| 20 | `verify/s5/S5c/mut/progs/m01766_85_op_args.wf` | C2>D1 | as m00982 | W0313, 12xW0314 | no `main` | rejected | no | Z1-G (closed) |
| 21 | `verify/s5/S5c/mut/progs/m02309_85_op_args.wf` | C2>D1 | as m00982 | W0313, 9xW0314 | no `main` | rejected | no | Z1-G (closed) |
| 22 | `r2/oracle/runs/m1/p1669.wf` | D5 | a `multi` clause runs its parameter: a row that only the analysis finds | clean | no fault | clean | no | Z7 (closed) |
| 23 | `r3/oracle/runs/m3a/p5750.wf` | D1 | D1a refusal: a call (`print(r)`) between the make and the run | W0301 | no fault | rejected | no | Z4 (closed) |
| 24 | `r3/oracle/runs/m3a/p7154.wf` | D1 | D1a refusal: a call (`Box.new`) between, a `resume` in a nested handled body | W0301 | no fault | rejected | no | Z4 |
| 25 | `r2/oracle/runs/g2/p2515.wf` | esc | closures that capture a capability in a block of a closure body that no node runs (Z8: the cause is a closure body that runs a closure of its maker, `twice(f1)`) | clean | no fault | clean | no | Z8 (closed) |
| 26 | `r2/oracle/runs/m2/p7046.wf` | E2 | a task runs `run_both(f1, f1)` | clean | no fault | clean | no | Z9a (closed) |
| 27 | `r3/oracle/runs/g3b/p18574.wf` | VT | a function value runs a value of its arguments as a task | W0312 | no fault | rejected | no | Z9c-B (closed) |
| 28 | `r3/oracle/runs/g4p/p25005.wf` | NESTED | a value of a callee runs a value as a task | W0405 | no fault | rejected | no | Z9d (open: R-NREF of the locals) |
| 29 | `r3/oracle/runs/t3/p148.wf` | NESTED | a value of a callee runs a value as a task | W0312 | no fault | rejected | no | Z9d (open: R-NREF of the locals) |
| 30 | `r3/oracle/seeds3/gen3_15687.wf` | VT | a function value runs a value of its arguments as a task | clean | no fault | clean | no | Z9c-B (closed) |
| 31 | `r3/oracle/seeds3/gen3_18180.wf` | NESTED | a value of a callee runs a value as a task | clean | no fault | clean | no | Z9d (open: R-NREF of the locals) |
| 32 | `r3/quality/gen3/closure_chain_100.wf` | chain | a chain of function values deeper than 64, no `main` | clean | no `main` | clean | no | Z10 (closed) |
| 33 | `r3/quality/gen3/closure_chain_200.wf` | chain | as closure_chain_100 | clean | no `main` | clean | no | Z10 (closed) |
| 34 | `r3/quality/gen3/closure_chain_400.wf` | chain | as closure_chain_100 | clean | no `main` | clean | no | Z10 (closed) |
| 35 | `r3/quality/gen3/closure_chain_800.wf` | chain | as closure_chain_100 | clean | no `main` | clean | no | Z10 (closed) |
