# Sources of the hand probes

Stage G2 of `docs/plan/core-ir.md` copied these probes from `SCRATCH`, the scratch
directory of the session that made the plan (plan §2.2). The command
`cargo run -p weft-gate -- copy-probes --probes DIR` makes the copy again and
writes this file. Each path below is relative to `SCRATCH`, and the copy has the
same path below `tests/gate/probes/`. `reviews/` is
`docs/plan/core-ir-inputs/reviews/`.

The copy has the `.wf` files, the packages (a directory with `weft.toml`, with its
`.wf` files) and the judge traces (`ir/judge_sound/*.dl`, `run_all.sh`). It does not
have the generated sets, the copies of the repository, the files larger than
256 KB, and the programs whose text is in a repository set. Tier 2 has all of them.

Totals: 78 directories, 3498 files, 23 packages.

## Directories

| Directory | Files | Packages | Origin | Named in the stage results |
| --- | --- | --- | --- | --- |
| `redteam` | 99 | 1 | round 1 red team (`reviews/redteam_review.md`) | `round1a_results.json`: Core S1: verify review<br>`round1b_results.json`: S4: verify probe |
| `specreview/progs` | 19 | 0 | round 1 spec review (`reviews/spec_review.md`) |  |
| `r2/fidelity/p` | 42 | 0 | round 2 report (`reviews/r2/fidelity.md`) |  |
| `r2/fidelity/repro` | 13 | 0 | round 2 report (`reviews/r2/fidelity.md`) | `round2_results.json`: review2: fidelity |
| `r2/interp/b6` | 3 | 0 | round 2 report (`reviews/r2/interp.md`) |  |
| `r2/interp/probe` | 17 | 0 | round 2 report (`reviews/r2/interp.md`) |  |
| `r2/interp/repro` | 33 | 0 | round 2 report (`reviews/r2/interp.md`) | `round2_results.json`: review2: interp |
| `r2/oracle/fp` | 58 | 0 | round 2 report (`reviews/r2/oracle.md`) |  |
| `r2/oracle/fp2` | 21 | 0 | round 2 report (`reviews/r2/oracle.md`) |  |
| `r2/oracle/fp3` | 15 | 0 | round 2 report (`reviews/r2/oracle.md`) |  |
| `r2/oracle/min` | 29 | 0 | round 2 report (`reviews/r2/oracle.md`) |  |
| `r2/oracle/probes` | 129 | 0 | round 2 report (`reviews/r2/oracle.md`) |  |
| `r2/oracle/repro` | 12 | 0 | round 2 report (`reviews/r2/oracle.md`) | `round2_results.json`: review2: oracle |
| `r2/oracle/sanity` | 4 | 0 | round 2 report (`reviews/r2/oracle.md`) |  |
| `r2/quality/repro` | 11 | 2 | round 2 report (`reviews/r2/quality.md`) | `round2_results.json`: review2: quality |
| `r2/redteam/p` | 82 | 1 | round 2 report (`reviews/r2/redteam.md`) | `round2_results.json`: R2a: loops, places and wildcard rules (foundation, speed, test harness): verify probe |
| `r2/redteam/repro` | 15 | 1 | round 2 report (`reviews/r2/redteam.md`) | `round2_results.json`: review2: redteam |
| `r2/triage` | 2 | 0 | round 2 (triage) | `round2_results.json`: R2: triage |
| `r3/fidelity/p` | 64 | 1 | round 3 report (`reviews/r3/fidelity.md`) |  |
| `r3/fidelity/repro` | 28 | 0 | round 3 report (`reviews/r3/fidelity.md`) |  |
| `r3/interp/probe` | 75 | 0 | round 3 report (`reviews/r3/interp.md`) |  |
| `r3/interp/repro` | 32 | 0 | round 3 report (`reviews/r3/interp.md`) |  |
| `r3/oracle/lib` | 2 | 0 | round 3 report (`reviews/r3/oracle.md`) |  |
| `r3/oracle/probes` | 382 | 0 | round 3 report (`reviews/r3/oracle.md`) |  |
| `r3/oracle/r2probes` | 141 | 0 | round 3 report (`reviews/r3/oracle.md`) |  |
| `r3/oracle/repro` | 14 | 0 | round 3 report (`reviews/r3/oracle.md`) |  |
| `r3/quality/big` | 0 | 0 | round 3 report (`reviews/r3/quality.md`) |  |
| `r3/quality/cli` | 9 | 0 | round 3 report (`reviews/r3/quality.md`) |  |
| `r3/quality/repro` | 14 | 0 | round 3 report (`reviews/r3/quality.md`) |  |
| `r3/redteam/crash` | 10 | 0 | round 3 report (`reviews/r3/redteam.md`) |  |
| `r3/redteam/p` | 73 | 0 | round 3 report (`reviews/r3/redteam.md`) |  |
| `r3/redteam/pkgA` | 0 | 1 | round 3 report (`reviews/r3/redteam.md`) |  |
| `r3/redteam/pkgB` | 0 | 1 | round 3 report (`reviews/r3/redteam.md`) |  |
| `r3/redteam/repro` | 12 | 0 | round 3 report (`reviews/r3/redteam.md`) |  |
| `r3/triage` | 1 | 0 | round 3 (triage) |  |
| `ir/probes` | 28 | 0 | IR design (`docs/ir.md`) |  |
| `ir/work/map` | 4 | 0 | IR design (`docs/ir.md`) |  |
| `ir/work/machine` | 10 | 0 | IR design (`docs/ir.md`) |  |
| `ir/work/mir` | 2 | 0 | IR design (`docs/ir.md`) |  |
| `ir/judge_sound` | 39 | 0 | IR design (`docs/ir.md`) |  |
| `ir/work/judge/p` | 1 | 0 | IR design (`docs/ir.md`) |  |
| `verify/p` | 27 | 0 | stage verifier (rounds 1 and 2) | `round1a_results.json`: Core S2: verify review |
| `verify/partb/S3/p` | 33 | 0 | stage verifier (rounds 1 and 2) | `round1b_results.json`: S3: verify probe |
| `verify/partb/S4/p` | 54 | 0 | stage verifier (rounds 1 and 2) | `round1b_results.json`: S4: verify probe |
| `verify/partb/S4diff/p` | 36 | 0 | stage verifier (rounds 1 and 2) | `round1b_results.json`: S4: verify review |
| `verify/partb/p` | 30 | 0 | stage verifier (rounds 1 and 2) | `round1b_results.json`: S3: verify review |
| `verify/review_core/Core_S1/rt1` | 27 | 0 | stage verifier (rounds 1 and 2) | `round1a_results.json`: Core S1: verify probe |
| `verify/review_core/Core_S2/probes` | 55 | 1 | stage verifier (rounds 1 and 2) | `round1a_results.json`: Core S2: verify probe |
| `verify/s1diff/p` | 38 | 0 | stage verifier (rounds 1 and 2) | `round1a_results.json`: Core S1: verify review |
| `verify/s5/R2c/p` | 28 | 0 | stage verifier (rounds 1 and 2) |  |
| `verify/s5/R2c/repro` | 5 | 0 | stage verifier (rounds 1 and 2) | `round2_results.json`: R2c: effects, continuations, on abort and drops: verify review |
| `verify/s5/R2c: effects, continuations, on abort and drops/p` | 74 | 0 | stage verifier (rounds 1 and 2) | `round2_results.json`: R2c: effects, continuations, on abort and drops: verify probe |
| `verify/s5/R2d/p` | 33 | 0 | stage verifier (rounds 1 and 2) | `round2_results.json`: R2d: tasks, scopes, fork and the scheduler: verify review |
| `verify/s5/R2d: tasks, scopes, fork and the scheduler/p` | 38 | 0 | stage verifier (rounds 1 and 2) | `round2_results.json`: R2d: tasks, scopes, fork and the scheduler: verify probe |
| `verify/s5/R2e: names, interpreter fidelity, proof claims and refactor/adv/p` | 108 | 2 | stage verifier (rounds 1 and 2) | `round2_results.json`: R2e: names, interpreter fidelity, proof claims and refactor: verify probe |
| `verify/s5/R2e: names, interpreter fidelity, proof claims and refactor/p` | 56 | 3 | stage verifier (rounds 1 and 2) |  |
| `verify/s5/R2e_diff/p` | 73 | 4 | stage verifier (rounds 1 and 2) |  |
| `verify/s5/R3a/p` | 37 | 0 | stage verifier (rounds 1 and 2) |  |
| `verify/s5/S5a/x/p` | 114 | 0 | stage verifier (rounds 1 and 2) | `round2_results.json`: S5a: verify probe |
| `verify/s5/S5b/p` | 18 | 0 | stage verifier (rounds 1 and 2) |  |
| `verify/s5/S5c/p` | 23 | 0 | stage verifier (rounds 1 and 2) |  |
| `verify/s5/S5c_diff/probes` | 5 | 0 | stage verifier (rounds 1 and 2) |  |
| `verify/s5/adv_r2e/p` | 108 | 2 | stage verifier (rounds 1 and 2) |  |
| `verify/s5/b/p` | 9 | 0 | stage verifier (rounds 1 and 2) |  |
| `verify/s5/diff/p` | 45 | 0 | stage verifier (rounds 1 and 2) | `round2_results.json`: S5a: verify review |
| `verify/s5/p` | 92 | 2 | stage verifier (rounds 1 and 2) | `round2_results.json`: R2b: closures, function values and stored references: verify review; R2e: names, interpreter fidelity, proof claims and refactor: verify review |
| `verify/s5/repro` | 7 | 0 | stage verifier (rounds 1 and 2) | `round2_results.json`: R2b: closures, function values and stored references: verify review |
| `fix` | 606 | 0 | stage root `fix` (rounds 1 and 2) |  |
| `s2` | 4 | 0 | stage root `s2` (rounds 1 and 2) |  |
| `s2fix` | 3 | 0 | stage root `s2fix` (rounds 1 and 2) | `round1a_results.json`: Core S2: fix+commit |
| `edge` | 81 | 0 | stage root `edge` (rounds 1 and 2) |  |
| `edgefix` | 5 | 1 | stage root `edgefix` (rounds 1 and 2) |  |
| `partb` | 34 | 0 | stage root `partb` (rounds 1 and 2) | `round1b_results.json`: S3: fix+commit; S4: fix+commit |
| `s5` | 16 | 0 | stage root `s5` (rounds 1 and 2) | `round2_results.json`: R2: triage; R2c: effects, continuations, on abort and drops: fix+commit; R2c: effects, continuations, on abort and drops: implement; S5a: implement |
| `s5r` | 6 | 0 | stage root `s5r` (rounds 1 and 2) | `round2_results.json`: S5a: fix+commit |
| `s1fix` | 7 | 0 | stage root `s1fix` (rounds 1 and 2) |  |
| `p` | 15 | 0 | stage root `p` (rounds 1 and 2) |  |
| `core` | 3 | 0 | stage root `core` (rounds 1 and 2) | `round1a_results.json`: Core S1: implement; Core S1: verify probe |

## Same text as a repository program

| Probe | Repository program |
| --- | --- |
| `edge/hold/26_stealable.wf` | `tests/programs/54_stealable.wf` |

## Larger than 256 KB (tier 2 only)

- `r3/quality/big/all.wf`
- `r3/quality/big/all_2.wf`
- `r3/quality/big/all_4.wf`
- `r3/quality/big/all_8.wf`
- `s5/fields_make16000.wf`
- `s5/fields_set16000.wf`
- `s5/h8000.wf`
- `s5/vc_untyped_chain.wf`
- `verify/partb/S4diff/p/wide2.wf`
- `verify/s5/diff/p/stress_if8.wf`

## Claim repros (stage G7)

Stage G7 copied these files from the tier-2 archive (`tests/gate/probes-tier2.tar.zst`),
because a claim of `tests/gate/claims.toml` names them and the copy rules of
plan §2.2 do not take their directories. They keep their paths. `copy-probes`
does not copy them, and it writes this file again without this section: add the
section again after a run of `copy-probes`.

- `verify/partb/S4/run/drops2.wf`
- `verify/partb/S4/run/drops3.wf`
- `verify/partb/S4/run/unset_closure.wf`
- `verify/partb/S4/run/unset_ret.wf`
- `verify/partb/S4/run/vec_fn_drop.wf`
- `verify/partb/S4/run/vec_fn_run.wf`
- `verify/review_core/Core_S1/rt2/clause_capture.wf`
- `verify/review_core/Core_S1/rt4/esc_closure_arg.wf`
- `verify/review_core/Core_S1/rt9/esc_field_ref.wf`
- `verify/review_edge/Edge/f14/overwritten_variants.wf`
- `verify/review_edge/Edge/f14/ow_closure_run.wf`
- `verify/review_edge/Edge/ptr/ptr_generic_fork.wf`
- `verify/s5/R2a: loops, places and wildcard rules (foundation, speed, test harness)/R1_walk_then_write.wf`
- `verify/s5/R2a: loops, places and wildcard rules (foundation, speed, test harness)/R2_bst.wf`
- `verify/s5/R2a: loops, places and wildcard rules (foundation, speed, test harness)/T2_join_swap.wf`
- `verify/s5/R2a: loops, places and wildcard rules (foundation, speed, test harness)/T3_loop_handles.wf`
- `verify/s5/R2a: loops, places and wildcard rules (foundation, speed, test harness)/T4_loop_swap_access.wf`
- `verify/s5/R2b: closures, function values and stored references/V_FD3_more.wf`
- `verify/s5/R2b: closures, function values and stored references/V_OR1_more.wf`
- `verify/s5/R2b: closures, function values and stored references/V_OR3_container_args.wf`
- `verify/s5/R2b: closures, function values and stored references/V_RR2_tuple_elems.wf`
- `verify/s5/R2b: closures, function values and stored references/V_RR7_nested_and_part.wf`
- `verify/s5/R2b: closures, function values and stored references/fd3_fn.wf`
- `verify/s5/R2b: closures, function values and stored references/fd3_localrc2.wf`
- `verify/s5/R2b: closures, function values and stored references/or3_ret.wf`
- `verify/s5/R2b: closures, function values and stored references/or3_variants.wf`
- `verify/s5/R2b: closures, function values and stored references/rr2_tuple.wf`
- `verify/s5/R2b: closures, function values and stored references/rr7_nested.wf`
- `verify/s5/R2b: closures, function values and stored references/rr7_ret2.wf`
- `verify/s5/r2a/t/mu1.wf`
- `verify/s5/r2a/t/mu3.wf`
- `verify/s5/r2a/t/tk1.wf`
- `verify/s5/r2a/t/tk2.wf`
- `verify/s5/r2a/t/tk3.wf`
- `verify/s5/r2a/t/x3.wf`
- `verify/s5/r2a/t/x5.wf`

## Programs that stage F8 added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs.

- `fixes/f8/*.wf`: the variants of the review of the `lost-clean` programs of
  stage F8 (holes H1 to H3; claims F8-H1 to F8-H3).
- `fixes/f8/h3_j*.wf`, `fixes/f8/h3_k*.wf`: the variants of the second review of
  stage F8 (holes N1 and N2; claims F8-H3b and F8-H3c), with the helper functions
  that `main` does not call removed. `fixes/f8/n1_*.wf`, `fixes/f8/n2_*.wf` and
  `fixes/f8/ctl_*.wf`: more shapes and controls of stage F8c.
- `fixes/f8/variant_receiver/*.wf`: the variant-step receivers of the third review
  of stage F8 (hole R1) and more shapes and controls of stage F8d (claims F8-R1).
  `a15_matchRefBindThenWrite.wf` and `b07_returnRefPayload.wf` (stage F8e, helpers
  that `main` does not call removed): a reference into an enum payload after the enum
  gets another variant; the oracle faults on them from F8e.
- `fixes/f8/receiver_bounds/*.wf`: the index receivers of the third review of stage
  F8 (stage F8.3; signed `lost-clean` entry; claim F8-RB). `shrink`, `pop`, `renew`
  and `block` are copies of `crates/weft-interp/tests/receiver_bounds/`.
- `r3/oracle/sweep1/{if,match}__tmp_*__arg.wf` and
  `verify/s5/R3a_diff/sweep/{if,match}__ref_temp*__arg.wf`: copies of the 24
  tier-2 programs of the branch temporaries (claim branch-temps, docs/ir.md 5.12).
- `fixes/f9/*.wf`: the defects of the fact generator that the fact oracle of stage F9
  found (`reads_at` facts; claim F9-C5, docs/ir.md 8.5). `mention_index_read.wf` is a
  variant of the first review of stage F8.

## Programs that stage F10 added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs.

- `fixes/f10/*.wf`: the defects that stage F10a found (claims F10-H1, F10-U1,
  F10-W1, F10-T1, F10-P1).
- `fixes/f10/hb/*.wf`: the variants of the review of stage F10 for hole H-B (a
  body with no IR and no error for it), with one line of header (stage F10.1;
  claim F10-HB).
- `fixes/f10/ha/*.wf`: the variants of the review of stage F10 for hole H-A (a
  reference in a heap slot read back after its referent changes; `hA/`, `h/`,
  `lc/lc22`), with one line of header (stage F10.1; claim F10-HA).
- `fixes/f10/hc/*.wf`: the variants of the second review of stage F10 for hole
  H-C (a callee stores a reference through a reference that its argument
  holds; `t/`, `t2/`, `t3/`, `t4/`, `t6/`, `s/s06`, and the control `t/t90`),
  with one line of header (stage F10.2; claim F10-HC). The control `t4/t90`
  is in `crates/weft-interp/tests/held_store/` (the old pipeline rejects it).

## Programs that stage F11 added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs.

- `fixes/f11/*.wf`: the defects that the preview of stage F11 (closures, the
  groups A, B and C) found (claims F11-L1, F11-P1, F11-M1, F11-O1, F11-U1).
- `fixes/f12/*.wf`: copies of `crates/weft-check/tests/data/fn_values/preview_fixes.wf`,
  `preview_fixes2.wf`
  (the classes of the lost faults of the preview of stage F12: function values, the
  groups A, B and C), `copy_once.wf` (the closure-copy rule for elements,
  fields and pattern parts) and `run_given.wf` (a run of a value against the
  places that the callee gives and the other arguments of the call, found in
  the review of the rows of the preview) and `run_results.wf` (a chain of
  closures that give back closures, from the tier-2 preview) and
  `value_drops.wf` (linear closures that a function value drops, and a
  closure that a loop makes, from the tier-2 preview) (claims F12-R5,
  F12-C1, F12-R6, F12-R7, F12-R8, F12-R9).

## Programs that the F12 fixes added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs. Each one is a variant of the review of the ABC preview
(scratchpad `f12/review.md`, section 4), with one line of header that names the
variant.

- `fixes/f12/h1/*.wf`: hole H1, a closure rebinds a captured reference and then
  changes the new referent (claim F12-H1).
- `fixes/f12/fp1/*.wf`: false positive FP1, a `Vec<fn()>` with no linear closure
  in another `Vec`, an `Option` or a field (claim F12-FP1).
- `fixes/f12/h2/*.wf`: hole H2, a closure that a function or a closure gives back
  goes through a call argument, an `Option`, a field or a tuple (claim F12-H2).
- `fixes/f12/oldholes/*.wf`: old holes that the ABC preview kept (review 4.7: hv_m,
  m09, b14);
  the default pipeline gives them to the old pipeline (ledger `open-old`).
- `fixes/f12/h3/*.wf`: hole H3, a linear closure that a function or a closure
  gives back, dropped by the caller (claim F12-H3).
- `fixes/f12/h4/*.wf`: hole H4, a closure with a `ByRef` capture or a `ByMove`
  capture that holds references in a `Vec` or an array (claim F12-H4).
- `fixes/f12/h5/*.wf`: hole H5, a linear closure that a callee or a closure runs
  on some paths only (claim F12-H5).
- `fixes/f12/h6/*.wf`: hole H6, linear closures that a loop makes and pushes
  into a `Vec` (claim F12-H6).

## Programs that the second F12 fixes added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs. Each one is a variant of the second review of the ABC
preview (scratchpad `f12/review2.md`, section 4), with one line of header that
names the variant.

- `fixes/f12b/n1/*.wf`: hole N1, the result of a closure maker, called or given
  back in a second closure or in a callee (claim F12R2-N1).
- `fixes/f12b/h5b/*.wf`: hole H5b, a callee gives a linear closure to a second
  callee that runs it on some paths only (claim F12R2-H5b).
- `fixes/f12b/h3b/*.wf`: hole H3b, a callee drops or gives back the linear result
  of a closure maker of its caller (claim F12R2-H3b).
- `fixes/f12b/oldholes/*.wf`: old holes b14-run (review 2, 4.5): a callee or a
  closure runs a `once` closure that it copies out of a referent, two times; the
  default pipeline gives them to the old pipeline (ledger `open-old`, claim
  F12R2-OH2).

## Programs that stage F13 added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs. Each one has one line of header.

- `fixes/f13/stored_*.wf`: copies of `crates/weft-check/tests/data/stored/*.wf`:
  function values behind a reference, in a `Vec`, a `Box`, an `Option` and an
  `rc` object, and the W0204 store forms (claims F13-S1, F13-S2, F13-S3).
- `fixes/f13/ol1a_code_runs_stored.wf`, `ol4a_read_back.wf`: the repros of OL-1a
  (with no task) and OL-4a that stage G7 did not have (claims OL-1a, OL-4a).
- `fixes/f13/rc_closure_run.wf`: a closure in an `rc` object that a callee runs
  (ABC accepted it before F13; claim F13-S3).
- `fixes/f13/kept_rebind_ret.wf`: a returned closure keeps a variable that gets a
  reference into a local later (class K3 of stage F12; claim F13-K3).

## Programs that the third F12 fixes added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs. Each one is a file of the third review of the ABC
preview (scratchpad `f12/review3.md`, `f12/variants3/`), with one line of header
that names the class and the review file.

- `fixes/f12c/h7/*.wf`: hole H7, a closure that a maker gives back stores a
  reference into a variable that it captures (claim F12R3-H7), the H7 shapes that
  ABC rejected only through the wrong fact of FP4, and their clean twins (claim
  F12R3-FP4; they failed the fact oracle).
- `fixes/f12c/fp4/*.wf`: false positive FP4, a wrong capture mapping of a made
  closure (claim F12R3-FP4).
- `fixes/f12c/fp3/*.wf`: false positive FP3, the result of a callee that runs code
  of a caller (claim F12R3-FP3).
- `fixes/f12c/w0204/*.wf`: the W0204 class at a unit tail call (claim
  F12R3-W0204), and made closures that read a reference that the maker took
  (`c05*`, claim F12R3-N1c; two of them are F12-fix3 variants).
- `fixes/f12c/b14agg/*.wf`: old holes b14-agg, a `once` closure copied out through
  a reference inside an aggregate argument, and their clean twins (claim
  F12R3-OH3, ledger `open-old`).
- `fixes/f12c/n1d/*.wf`: old holes N1-aggregate that ABC closes (claim
  F12R3-OH4, ledger `open-old`).
- `fixes/f12c/h6/*.wf`: a callee stores a linear closure into a place of its caller
  (`variants2/ah6/h6_08` of the rerun after F13, and two F12-fix3 variants; claim
  F12R3-H6).
- `fixes/f12c/w0502/*.wf`: the W0502 class, a `once` maker that a callee runs one
  time (claim F12R3-W0502).
- `fixes/f12c/n2/tw.wf`: a map N2 row (by design; ledger `new-fp`, `stricter`).

## Programs that the F13 fixes added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs. Each one is a file of the review of stage F13 part 1
(scratchpad `f13/review.md`, `f13/variants/`), with one line of header that
names the class and the review file.

- `fixes/f13b/ab_rc2/*.wf`: class AB-RC2, a reference through a handle in a local
  `Vec`, struct or tuple goes into an `rc` object of the same type (claim
  F13B-AB-RC2), and clean twins.
- `fixes/f13b/ab_rc1/*.wf`: class AB-RC1, a reference through a whole local handle
  of another object (claim F13B-AB-RC1), clean twins, a copy of the handle of the
  store (`k01`, the old pipeline checks it), and the old hole `a13` (ledger
  `open-old`).
- `fixes/f13b/ab_rc3/*.wf`: class AB-RC3, a callee reads the references of an `rc`
  object after a change of the group (claim F13B-AB-RC3), clean twins, and the old
  hole `e17` (ledger `open-old`).
- `fixes/f13b/hs1/*.wf`: class H-S1, a made closure (or a closure that captures a
  reference parameter) in a heap slot of a parameter runs or is read back after a
  change of its referent (claim F13B-HS1; old holes: ledger `open-old`), and clean
  twins.
- `fixes/f13b/hrc1/*.wf`: class H-RC1, a closure in an `rc` object keeps a reference
  into the group (claim F13B-HRC1; old holes: ledger `open-old`), and clean twins.
- `fixes/f13b/k3made/*.wf`: class K3-Made, a closure that a closure makes sees the late
  value of a kept variable (claim F13B-K3MADE), clean twins, and `m01x` (an F13-fix
  variant: the late value is a place of a parameter that `main` clears).
- `fixes/f13b/hlin/*.wf`: class H-LIN, a linear closure in a part of a local, behind
  a reference, in a `Box` or in an `rc` object (claim F13B-HLIN).
- `fixes/f13b/fp/*.wf`: false positives that F13-fix removes: FP-AB-RC (`k05`, claim
  F13B-FP-AB-RC), FP-S2 (claim F13B-FP-S2), FP-K4 (claim F13B-FP-K4), and `both_once`
  (finding (a) of stage F12-fix3, claim F12R3-BOTH).

- `fixes/f13b/fp/w09_ctl_outer_runs_after_maybe_other.wf`: the lost-clean row of the
  F13-fix rerun (F12 sets, `variants3/h5b/w09_ctl`): a callee runs two linear closures
  one time each (claim F12R3-BOTH; ledger `lost-clean`, signed in scratchpad
  `f13/final_check.md` 4).

## Programs that the final check of group C added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs. Each one is a file of the final check of group C
(scratchpad `f13/final_check.md`, `f13/final_variants/`), with one line of header
that names the class and the file of the check.

- `fixes/f13c/ord/*.wf`: class H-ORD, a body that runs two values gets a closure that
  runs a `once` value of the caller two times, or gets the same value as one argument
  and in a closure (claim F13C-ORD), and clean twins (`q04_nested_each_c` runs the
  value in a loop: W0502 in both pipelines). `o11` and `q06`: the old pipeline misses
  them (ledger `open-old` while group C is off).
- `fixes/f13c/w4/w01_*.wf`, `j03_*.wf`, `j04_*.wf`: class AB-RC1-join, a store through
  a reference that can reach the `rc` object of the caller and a local object (claim
  F13C-JOIN; the old pipeline misses them).
- `fixes/f13c/w4/w09_closure_param_store_b.wf`: class H-W9, a closure stores its
  reference parameter into the object of a captured handle (both pipelines miss it;
  ledger `open-old`, issue #41).

## Programs that follow-up F13.2 added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs. Each one has one line of header that names the class and
its file in the scratchpad.

- `fixes/f13d/ur/*.wf`: class UR, a value that a body runs and that no caller
  gives (claim F13D-UR). The five repros of the signature diff of stage F13 part 2
  (`f13p2/hole/`) and `f13p2/t/rb.wf` (`_b`), each with a clean twin (`_c`): a
  closure that a callee made runs a value of the body, and a closure gives a
  function-value local a new value.
- `fixes/f13d/var/*.wf`: more shapes of class UR (`_b`) with clean twins (`_c`): a
  made closure in a loop, in a field, in a vector, in an `Option`, in an `rc`
  object, through a callee and another maker, in a join, a rebound local in a loop
  and into a maker. `a01_*_noref_c` and `a14_*_noref_c`: a closure of the body that
  a callee runs changes its own environment (no W0312).

## Programs that stage F14 added

These programs are not copies of SCRATCH. `copy-probes` does not know them: add
them again if it runs. Each one is a file of the self-attack of stage F14 (scratchpad
`f14/att/v/`), with one line of header that names the class. Each faulting program
has a clean twin (`_c`). They use group D, which is off until stage F17: the old
pipeline checks them by default.

- `fixes/f14/oh/*.wf`: class F14-OH, old holes: a clause stores a parameter into a
  place of the site through another parameter, keeps the result of `resume` in a
  slot of the site, or gives a value with no `resume` that points into the argument
  (M3). Ledger `open-old` while group D is off.
- `fixes/f14/abort/*.wf`: class F14-ABORT, a clause that fails past its handler
  (past the function, or to an outer handler): the abort starts at the node of the
  handled body that runs the clause.
- `fixes/f14/post/*.wf`: class F14-POST, the code of a clause after `resume` and the
  rest of the handled body in the `resume`. The clean twins are the shapes that the
  fact oracle and its summary oracle check at `Post`.
