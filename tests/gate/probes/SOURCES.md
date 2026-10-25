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
