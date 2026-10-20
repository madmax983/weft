# Review round 3, lens "quality"

Commit: b073ea7 (source copy `scratchpad/r3/src`, head of `review/s5` after S5b and S5c).
Range: `git diff bb71618..b073ea7`, with most attention on `f389b46..b073ea7` and on
`crates/weft-sema/src/body/`.
Release CLI: `scratchpad/r3/target/release/weft`. All times in this report are for that
binary on this machine (4 cores), unless the text says otherwise.

Files (all under `SCRATCH/r3/quality/`):

- `repro/`: one or more repro files for each finding.
- `tools/gen3.py`, `tools/gen4.py`: generators of large programs (43 shapes).
- `tools/fuzz.py`: a mutation fuzzer for the CLI.
- `tools/t.sh`: a timing wrapper.
- `gen3/`: the generated programs and the timing inputs.
- `prof/`: callgrind profiles (`cg_cc14.out`, `cg_ct14.out`, `cg_sp500.out`, `cg_lf200.out`).
- `target/release/weft`: a copy of the release build with line tables (for callgrind).
- `target-dbg/release/weft`: a release build with `debug-assertions` and `overflow-checks`.

## Summary

- 1 blocker, 2 majors, 2 minors.
- Q3-1 (blocker): a place field below a second use of one generic type gets no "unset"
  variable. A checked program reads a place field that has no value, and `weft run` stops
  with a run-time error. ADR 0007 says that this case is W0304 and that no gap is open.
- Q3-2 (major): `Lower::closure_has` is exponential in the number of closures that call
  each other. 16 helper closures take 4 s, 18 take 30 s, 20 take 250 s.
- Q3-3 (major): a bare variant name resolves to the first enum of the program that has a
  variant with that name. A user enum with a variant `None`, `Some`, `Ok` or `Err`, or
  two modules with the same variant names, get a false W0102.
- Q3-4 (minor): the search for place fields is exponential in the depth of a type with
  more than one field of one type. It runs only if the program has a place field.
- Q3-5 (minor): three tests still assert a wall-clock bound in a debug build (QA13
  residual).
- The round-2 quality fixes hold (table below). The round-2 repros are fast and give the
  expected errors.
- Fuzzing found no crash, no overflow and no disagreement with the spec:
  - 120 000 mutated corpus programs on the build with `debug-assertions` and
    `overflow-checks`, through `check`, `check --json`, `check --explain` and `agree`;
  - 40 000 more on a second seed set (generated shapes, the R2/S5 corpus files and my
    repros), with no failure and no input slower than 2 s. A first run of that set
    also had the Q3-2 chain as a seed: all its timeouts (7) and slow inputs came from
    programs that hold that chain.
- Scale: 43 generated shapes at 4 sizes each. Apart from Q3-2 and Q3-4, each shape is
  linear or has a documented or inherent quadratic cost (see "Observations").
- The whole corpus in modules (12 835 lines, 1 846 functions) checks in 0.48 s, and 8
  copies of it (103 000 lines) in 3.6 s.

## Round-2 fixes: check

| Round-2 item | Repro | Result now | Before |
|---|---|---|---|
| QA1 loop pass cap | `r2/quality/repro/QA1_loop_pass_cap.wf` | W0301 and W0703, 0.03 s | 0 errors |
| QA2 `on abort` effects | `QA2_on_abort_effects.wf` | W0118 | 0 errors |
| QA3 `in` order | `QA3_param_place_order.wf` | 2 W0301 | 1 W0301 |
| QA4 nested wildcards | `QA4_wild_walk_4loops.wf` | 0.03 s | no result after 300 s |
| QA5 dependency `main` | `QA5_dep_named_main/` | W0107 | 0 errors |
| QA6 wildcard self write | `QA6_wildcard_self_write.wf` | 0 errors | 3 false errors |
| QA7 sequential loops | `QA7_seq_loops_1000.wf` | 0.14 s | 1.3 s |
| QA8 integer chain | `QA8_int_chain_8000.wf` | 0.08 s | 2.6 s |
| QA10 corpus counts | `programs.rs` | sorted lists, not sets | sets |
| QA11 double W0301 | `QA11_duplicate_w0301.wf` | 1 W0301 | 2 W0301 |
| QA13 `in` chain facts | `QA13_in_chain.wf` | `points_into` for all 7 parameters | 2 of 7 |

The round-2 generator shapes (handlers, closures, references, deep and wide types, deep
generics, matches, many functions, many parameters) are linear or close to linear at 4
times the round-2 sizes.

## Findings

### Q3-1 (blocker): a place field below a second use of one generic type has no "unset" variable

- Where: `crates/weft-sema/src/body/mod.rs:2650-2704`, `Lower::unset_paths_into`.
- The function walks the type of a new value to find its place fields. It keeps a stack
  `seen: Vec<AdtId>` of the ADTs on the path. The key is the ADT id only, not the type
  arguments. So the walk stops at the second use of one generic ADT on the path, also
  when the type arguments are different.
- Thus a place field below `Wrap<Wrap<Frame>>`, `Wrap<Holder>` with
  `Holder { inner: Wrap<Frame> }`, `Option<..Option<Frame>..>` or `Box<..Box<Frame>..>`
  gets no hidden "unset" variable. A read of the field before the body gives it a value
  is not W0304.
- ADR 0007 states: "Its place fields have no value, also in a part, in an enum payload
  and behind a `Box`. A read or a borrow of such a field ... is W0304." It also states
  "What stays open (not checked): no known gap."
- Repro 1: `repro/Q3_unset_place_field_nested_generic.wf`.
  - `one_level` (line 13), `control` (line 38) and `one_box` (line 45) give W0304.
  - `two_levels` (line 19), `from_call` (line 26), `other_struct` (line 33) and
    `two_boxes` (line 49) give no error. Each reads a place field that has no value.
- Repro 2: `repro/Q3_unset_place_field_run.wf`.
  - `weft check` gives 0 errors.
  - `weft run` (checked, no `--unchecked`) stops with
    `runtime error: a value is used after it was moved` at line 6.
  - `repro/Q3_unset_place_field_run_control.wf` (one `Wrap`) gives W0304.
- Fix:
  - Key `seen` by the full type (`Ty` after `deep`), or by `(AdtId, args)`. A recursive
    type gives the same key again, so the walk still ends.
  - Better: compute once for each `(AdtId, args)` the list of paths to place fields, and
    keep it in a table. This also fixes Q3-4.
  - Add the repro shapes to `tests/programs/73_immovable.wf`.

### Q3-2 (major): `closure_has` is exponential in closures that call other closures

- Where: `crates/weft-sema/src/body/mod.rs:3070-3107` (`closure_has`, `var_has`) and
  `ty_has_in` (3023).
- `closure_has` pushes the summary on `h.seen` and pops it after the search. So `seen`
  stops a cycle only, and the search visits a closure again on each path to it.
- `var_has` reaches the closure of a local two times: through the type of the local
  (`Ty::Fn` with a summary, in `ty_has_in`) and through `l.summary`. So even a plain chain
  `c_i = || c_{i-1}()` costs 2^n.
- `mode_marks` (`caps.rs`), `val_caps`, `assign_local`, `bind_pattern` and `finish` call
  it for each new value. Callgrind on 14 closures puts 99% of the time in these three
  functions (`prof/cg_ct14.out`).

| shape | closures | `weft check` |
|---|---|---|
| each calls the two before it (`repro/Q3_closure_helpers_16.wf`) | 16 | 4.3 s |
| same (`repro/Q3_closure_dag_18.wf`) | 18 | 31.6 s |
| same | 20 | 249 s |
| each calls all before it | 13 / 14 / 15 / 16 | 1.0 / 2.6 / 8.5 / 23 s |
| each calls the one before it | 20 / 22 / 24 (`repro/Q3_closure_chain_22.wf`: 22) | 2.0 / 7.9 / 31 s |

- Local helper closures that call each other are a common style (an `emit` closure, a
  `row` closure that calls `emit`, and so on). 16 to 20 of them in one function are
  not unusual in generated or table-driven code.
- `Work` has no count of these searches, so no scale test sees it.
- Fix:
  - Do not pop `h.seen`. The query is "some capture has the property". A closure that
    the search finished with "no" gives "no" again, and a "yes" ends the search. So a
    visited set gives the same result in linear time.
  - In `var_has`, do not search `l.summary` again when the type of the local names the
    same summary.
  - Add a work count (`Work::closure_queries`) and a scale test with the helper shape.
- Repro generator: `repro/Q3_exp_gen.py helpers N` and `repro/Q3_exp_gen.py chain N`.

### Q3-3 (major): a bare variant name resolves to the first enum that has the name

- Where:
  - `crates/weft-sema/src/body/call.rs:184` (a call form `Circle(1)`);
  - `crates/weft-sema/src/body/expr.rs:470` (`unit_variant`, a name such as `None`);
  - `crates/weft-sema/src/body/expr.rs:1269` (a pattern with no known type);
  - `crates/weft-sema/src/fip.rs:85`;
  - `crates/weft-interp/src/compile.rs:414` (the interpreter does the same).
- Each takes `prog.variants.get(name).first()`. `prog.variants` is one table for the
  whole program, filled in item order: the prelude first, then the root, then the
  dependencies. The module of the use does not count, and `pub` does not count.
- So:
  - A user enum with a variant `None`, `Some`, `Ok` or `Err` gets the prelude variant
    for the bare name. `return None` in a function that returns the user enum is W0102.
  - In two modules with an enum that has the same variant names, the second module gets
    the variants of the first. The message is `expected `Shape`, found `Shape``.
  - The variant of a private enum in another module is used with no error.
  - A pattern that names the variant works, because it takes the type of the scrutinee.
    The qualified form `Lookup.None` also works. So the bare form behaves differently in
    an expression and in a pattern.
- Repro:
  - `repro/Q3_variant_name_prelude.wf`: W0102 at line 6, 0 expected.
  - `repro/Q3_variant_name_across_modules.wf`: W0102 at line 21, 0 expected.
  - `repro/Q3_variant_name_private.wf`: 0 errors; W0101 expected at line 7.
  - I found this when I checked the corpus as one program with each file in a module:
    the second copy of the corpus gave 12 more errors than the first
    (`big/all_2.wf`, `big/j2.txt`).
- No ADR and no doc states that variant names are global.
- Fix: resolve a bare variant name in the scope of the module, as `Program::lookup` does
  for items. When the expected type is known (a return, an argument, a `let` with a
  type), prefer the enum of that type. Report an ambiguous bare name, as
  `ambiguous_op` does for operations. Do the same in the interpreter and in `fip.rs`.

### Q3-4 (minor): the search for place fields is exponential in the depth of a DAG type

- Where: `crates/weft-sema/src/body/mod.rs:2650-2704` (`unset_paths_into`), called by
  `unset_fields` for each new value of a local (a literal, a call result, a by-value
  parameter).
- The walk pops `seen` after each ADT, so it visits each path of the type tree. A struct
  with two fields of the type below it, `D` levels deep, has `2^D` paths. The walk runs
  only if some struct of the program has a place field (`has_place_fields`), also one
  that the type does not hold.

| program | `weft check` |
|---|---|
| depth 22, 2 fields, place field in the program (`repro/Q3_place_type_dag_22.wf`) | 1.5 s (2.8 s with two locals) |
| same with no place field (`repro/Q3_place_type_dag_22_control.wf`) | 0.01 s |
| depth 14, 3 fields (`repro/Q3_place_type_dag_14x3.wf`) | 1.05 s |
| depth 16, 3 fields, 5 locals (`repro/Q3_place_type_dag_16x3_5locals.wf`) | 62 s |

- Types this deep are rare, so the severity is minor. But the cost is per local, and the
  fix is the same table as for Q3-1.
- Fix: keep, for each `(AdtId, args)`, the paths to its place fields (most types have
  none). Skip a type whose table entry is empty.

### Q3-5 (minor): tests that still assert wall-clock time in a debug build

- QA13 (round 2) asked for counts of work in place of clock bounds. `scale.rs` now gates
  its clock test on a release build. Three other clock asserts remain, with no gate:
  - `crates/weft-check/src/tests.rs:1132`: `step_facts_of_a_wide_struct_are_linear`
    asserts less than 500 ms for 3 200 fields, also in a debug build.
  - `crates/weft-sema/src/props.rs:546`: `a_wide_recursive_type_is_fast`, less than 10 s.
  - `crates/weft-cli/tests/limits.rs:413`: `explain_folds_a_long_derivation`, less than
    60 s.
- The 500 ms bound is the most fragile one: a loaded CI machine can fail it.
- Repro: `repro/Q3_timed_tests.txt` (the three tests and, for contrast, the gated one).
- Fix: count the facts or the steps (the test already counts `alias.len()`), or gate the
  clock with `#[cfg_attr(debug_assertions, ignore = ...)]` as `scale.rs` does.

## Observations (no finding)

- Costs that are inherent or documented, at sizes that a real program does not reach:
  - A ring of `n` functions where each function performs its own effect: the rows hold
    `n * n` effects. 250 functions take 0.7 s, 1000 take 7 s, 2000 take 39 s.
  - A loop that carries a chain of `n` function locals needs `n` passes (ADR 0003).
    200 locals take 0.45 s, 800 take 9.7 s.
  - Nested loops multiply their passes: 6 nested loops with a chain of 3 at each level
    take 0.41 s (about 3.5 times more for each level).
  - `n` closures in a `Vec` and `n` calls of its elements: each call can run each closure.
    400 take 0.73 s, 800 take 3.4 s.
  - 2000 tasks in one `scope` take 2.4 s (the checker compares each task with each active
    node; `witnesses` scans the changers of the shared root for each place list).
  - `check --explain` and `agree` on 800 W0301 errors in one function take 2.5 s: the
    Datalog `invalid` relation has `n * n` facts.
  - A local that gets references into `n` roots: `n * n / 2` `reads_at` facts, as
    `docs/architecture.md` states. 2000 roots take 1.5 s.
- `Infer::shallow` and `Infer::deep` clone the type tree at each call. `ty_has_in` calls
  `shallow` at each level. This is a constant factor today, but it adds to Q3-2 and Q3-4.
- `SourceFile::line_col` gives byte columns, not character columns. A line with non-ASCII
  text before the error gets a column that an editor does not show (old code).
- A UTF-8 byte order mark at the start of a file is W0001 (old code).
- The new code has no `unwrap`, no `expect` and no `panic!` in production paths. The
  `unwrap_or(u32::MAX)` conversions of ids saturate, which is safe at real sizes.
- The checker search (`part_of`, `ranks`, `first_reaching`, the shared whole-graph
  search) agrees with the spec on all fuzz inputs, and its comments match the code.
- `FnFacts::mark` and `rewind` name each field, so a new relation must get a decision.
  `normalize` covers each relation of the spec.
