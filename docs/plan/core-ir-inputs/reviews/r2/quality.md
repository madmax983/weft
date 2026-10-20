# Review round 2, lens "quality"

Commit: 328a39b (worktree `/home/user/wt-edge`, branch `review/r2`).
Range: `git diff bb71618..328a39b`.
Repro files: `SCRATCH/r2/quality/repro/`.
Generators and timing inputs: `.../scratchpad/r2/quality/gen/`.
All times are for the release CLI (`target/release/weft check`) on this machine.

## Summary

- 3 blockers, 5 majors, 5 minors.
- Two blockers are new shapes of unsound acceptance (QA1, QA2). QA2 has a run-time
  fault in the interpreter. QA3 is older code, but a round-1 test hides it.
- QA4 is the most serious performance problem. A 20-line program does not finish in
  300 s. The cost is exponential in the depth of nested wildcard places.
- The round-1 quality fixes hold. I ran the 11 round-1 repros again: no crash, and
  each one is fast. The lint arity, the prelude unit, the user-effect hint, the
  explain size (2.7 KB for 10 000 statements) and the 33-link effect chain are correct.
- Fuzzing found no crash and no disagreement:
  - 275 000 mutated corpus programs, with `agreement()`;
  - 80 000 of them also through `--explain` and every diagnostic render;
  - 6 000 generated programs (round-1 generator);
  - a build with `debug-assertions` and `overflow-checks`;
  - no input took more than 1.5 s.
- I checked the S5 branch (`review/s5`, read only). It does not change the code of
  QA1, QA3, QA4, QA7 or QA8.

## Findings

### QA1 (blocker): the loop fixpoint stops after 8 passes, with no diagnostic

- Where: `crates/weft-sema/src/body/stmt.rs:805-835`
  (`lower_loop`, `MAX_LOOP_PASSES = 8`).
- A chain of locals in a loop needs one pass for each local. A chain of 8 needs
  9 passes. After 8 passes the lowering keeps the values of the last pass. The
  last value never gets to the head of the loop. The lowering does not tell the
  user that it stopped.
- Effect:
  - `g0 = g1; ...; g7 = grow` in a loop: the 9th iteration calls `grow`. `grow`
    invalidates `first`. There is no W0301.
  - `c0 = c1; ...; c7 = b` in a loop: the 9th iteration clears `b.entities`. The
    signature does not state `b.entities`, but there is no W0703. A caller keeps
    references into `b.entities[]` across the call.
  - With 7 locals, the checker gives both errors.
- ADR 0003 states the limit only for a reference that goes deeper in each
  iteration. It says that this case stays sound. The chain case is not sound.
- Repro: `repro/QA1_loop_pass_cap.wf` gives 0 errors, and 2 are expected.
  `repro/QA1_control_chain7.wf` (7 locals) gives W0301 and W0703.
- Fix:
  - Iterate to the fixpoint. The joined state only grows.
  - For the reference that goes deeper, widen. After N passes, replace a place that
    still grows with the wildcard of its base. Replace a function value that still
    changes with "unknown".
  - Never keep the last values silently. If a bound is hit, give an internal error,
    as W0706 does.

### QA2 (blocker): the effects of an `on abort` function do not count

- Where:
  - `crates/weft-sema/src/program.rs:594` (`check_on_aborts` checks only the
    parameter).
  - The lowering does not add the row of the `on abort` function at a node that can
    abort while the value is live.
- `f` holds a `Tx` across `work()`, which can fail. The unwind runs `rollback`, and
  `rollback` performs `Note`. No signature states `Note`, and no handler handles it.
- Repro: `repro/QA2_on_abort_effects.wf`.
  - `weft check` gives 0 errors.
  - `weft run` stops with `runtime error: no handler for 'Note.note' on this task`.
- This shape is not in the open lists of ADR 0005 or ADR 0007.
- Fix:
  - At each `may_abort` node where a value with `on abort` is live, perform the row
    of the `on abort` function (`perform_at`). Also add its mutations.
  - Add the `on abort` function as an edge of `infer::NameGraph`.
  - Another option: require an `on abort` function to have no effects other than the
    effects that an unwind can perform, and report it with W0118.

### QA3 (blocker): an `in` place that names a later `in` parameter gets no places

- Where: `crates/weft-sema/src/body/stmt.rs:48-52`.
- `lower_fn` substitutes the `in` places in the order of the parameters. In
  `fn h(v: &Vec<E>, a: &E in b, b: &E in v[])`, `bases[2]` is still empty when the
  loop does `a`. So `a` has no `points_into`, and no mutation can invalidate it.
- Repro: `repro/QA3_param_place_order.wf`.
  - `h` and `h2` have the same meaning. Only the order of the parameters is different.
  - The checker gives W0301 for `h2` only.
  - `weft facts ... h` shows no `points_into` for `a` (v1).
- This code is older than round 1. But round 1 added the W0201 cycle check for these
  chains, and the test `the_in_place_check_is_fast_on_a_long_chain` uses exactly this
  forward shape (see QA13).
- Fix: substitute in topological order. The W0201 cycle check already has the graph.
  Another fix: repeat the loop until no base changes. There are no cycles, so this
  stops after at most n rounds.

### QA4 (major): `Ctx::overlaps` is exponential in nested wildcard places

- Where:
  - `crates/weft-check/src/rules.rs`: `Ctx::overlaps`, `mutation_kills` and
    `free_kills`. These were added in round 1.
  - `crates/weft-facts/src/lib.rs`: `FnFacts::wildcard`.
- Each call result of an unknown function value points into the wildcard of its
  argument. `cur = step(cur)` therefore makes `head.. .. ..`, one level for each
  call. A loop runs 8 passes, so it adds 8 levels.
- `bases[p]` already holds all the wildcard ancestors of `p`. But `overlaps(a, b)`
  calls itself for each base of `a` and each base of `b`, and each of those calls
  does the same. So the cost is about 2^depth for each pair of places.

| program | levels | `weft check` |
|---|---|---|
| straight line, 20 calls | 20 | 0.03 s |
| straight line, 24 calls | 24 | 0.18 s |
| straight line, 26 calls | 26 | 0.73 s |
| straight line, 28 calls | 28 | 2.8 s |
| straight line, 30 calls | 30 | 12 s |
| straight line, 32 calls | 32 | 47 s |
| 3 loops `while .. { cur = step(cur) }` | 24 | 1.6 s |
| 4 loops | 32 | no result after 300 s |

- The Datalog spec finishes the same 24-level program quickly. Callgrind puts 99.9%
  of the time in `Ctx::overlaps`.
- Repro:
  - `repro/QA4_wild_walk_4loops.wf` does not finish.
  - `repro/QA4_wild_walk_3loops.wf` takes 1.6 s.
  - `repro/QA4_wild_walk_gen.py K` makes the straight-line walk.
- Fix:
  - `p.. ..` is the same set of places as `p..`. Make `FnFacts::wildcard(p)` return
    the outermost wildcard when `p` is already below one.
  - In the checker, compare only the outermost bases. Overlap is closed under
    prefixes, so this is exact. Or iterate over `{a} ∪ bases[a]` × `{b} ∪ bases[b]`
    with no recursion.
  - Add a scale test with 4 such loops.

### QA5 (major): a dependency named `main` shares the effect identities of the root

- Where: `crates/weft-sema/src/effects.rs` (`identity`). The root module becomes
  `main`, and a dependency module gets its manifest name.
- With `[dependencies.main]`, the dependency effect `Note` and the root effect `Note`
  both get the identity `main.Note`. The root handler of its own `Note` then handles
  the `Note` of the dependency. W0701 for `pub fn quiet` is lost.
- Repro:
  - `repro/QA5_dep_named_main/` gives 0 errors.
  - `repro/QA5_control_dep/` is the same package with the dependency named `dep`.
    It gives W0701.
- Fix: give the root a prefix that a manifest name cannot be (for example `<root>`).
  Or reject the dependency name `main` with W0107. Also check `weft deps` and the
  interpreter, which use the same identities.

### QA6 (major): a write through a wildcard reference invalidates that reference

- Where:
  - `spec/weft.dl:123-125,131-132`, and the same rules in `rules.rs`
    (`mutation_kills`).
  - These came in with round 1 (41ba525, "wildcard places").
- Problem 1:
  - A call result with no stated place, such as `-> Option<&Entity>` or the result of
    a function parameter, points into `v..`.
  - A write through the reference itself overlaps `v`, so the reference becomes
    invalid. This is also so for a scalar field through a stable step.
  - So `e.hp -= 1; e.hp -= 1` is W0301.
- Problem 2:
  - The rule `wild_at(M, B), prefix(B, Path)` uses `prefix` where `strict_prefix` is
    correct.
  - So a write below `boxes` invalidates the reference `boxes` itself:
    `b.items.push(1); print(boxes.len())` is W0301.
- These are false positives on common code. ADR 0003 states the wildcard rule, but
  its list of imprecisions does not name this effect.
- Repro: `repro/QA6_wildcard_self_write.wf` gives 3 errors, and 0 are expected.
  With `-> Option<&Entity in v[]>`, the same body gives no error.
- Fix:
  - Use `strict_prefix(B, Path)` in the `wild_at(M, B)` rules.
  - Give each call result its own wildcard instance (a fresh split). Then a write at
    or below that instance through stable steps can use rule 3 for references into
    the same instance.
  - Note: a plain `!prefix(Path, M)` guard is not sound while two results share one
    interned `v..` place.
  - This is a spec change, so the spec lens must agree.

### QA7 (major): each loop pass clones the whole lowering state

- Where: `crates/weft-sema/src/body/stmt.rs:805-1033` (`lower_loop`, `carried`,
  `rewind`).
- Each pass does `let head = self.clone()`. That clones all of `Lower` (60 fields):
  the facts so far, all locals, the `scope` map of `String` keys, and the summaries.
- `carried` formats a `BTreeSet<String>` key for each local outside the loop, twice
  in each pass.
- So one loop costs O(size of the function so far), and a function with many loops
  is quadratic. Callgrind on 500 loops shows that `Lower` clone and drop take more
  than 50% of the time, and `String` clones take 38%.

| loops in one function (typed integers) | `weft check` |
|---|---|
| 250 | 0.09 s |
| 500 | 0.31 s |
| 1000 | 1.25 s |
| 2000 | 5.7 s |

- With 4000 locals before 200 small loops, the time is 1.3 s. With 1000 locals, it
  is 0.36 s.
- Repro: `repro/QA7_seq_loops_gen.py N`, and the sample `repro/QA7_seq_loops_1000.wf`
  (1.3 s).
- Fix:
  - Keep only the loop-carried state: `locals[..outer]`, the part holders and the
    branch state.
  - For the fact vectors, which only grow, keep their lengths at the head and cut
    them back to these lengths on `rewind`.
  - Make the key only for the locals that the loop body assigns. Find them once.

### QA8 (major): the integer type variable chain makes `s += 1` quadratic

- Where:
  - `crates/weft-sema/src/types.rs:145-246` (`Infer::shallow`, `unify`, `bind`,
    `occurs`).
  - Round 1 keeps integer literals open (c710ad0), so the chain grows.
- `unify(IntVar a, IntVar b)` binds the end of the old chain to the new variable of
  the literal. So each `s += 1` adds one link. Then `shallow` and `occurs` walk the
  whole chain. There is no path compression and no union by rank.

| updates of one untyped local | untyped | `let s: i64 = 0` |
|---|---|---|
| 2 000 | 0.17 s | 0.01 s |
| 4 000 | 0.66 s | 0.02 s |
| 8 000 | 2.8 s | 0.03 s |
| 16 000 | 10.9 s | 0.06 s |

- 4 000 `if` blocks with `s += 1` take 1.2 s, for the same reason. Callgrind gives
  80% of the time in `Infer::shallow`.
- Repro: `repro/QA8_int_chain_gen.py N [typed]`, and the sample
  `repro/QA8_int_chain_8000.wf` (2.6 s).
- Fix:
  - When both sides are variables, bind the newer variable to the older one, with
    union by rank.
  - Compress paths in `shallow` (`&mut self`, or `Cell` entries).
  - A bind of a variable to a variable needs no `occurs` walk.

### QA9 (minor): functions and state too large to read; implicit invariants

- `call_fn_as` has 548 lines (`crates/weft-sema/src/body/call.rs:264`). In round 1
  `call_fn` had 324 lines, and item 18 of round 1 reported it.
- `diagnose` has 462 lines (`crates/weft-check/src/diagnose.rs:63`). It had 253.
- `handle` has 266 lines, `call_value` 255 and `closure` 219.
- `Lower` has 60 fields. `lower_loop` clones all of them (QA7). `rewind` keeps 8
  tables from the pass before, and the struct doc says "Put a new field that can
  refer to these tables in `lower_loop` too". Nothing checks this rule, and a new
  field that breaks it gives wrong facts without a test failure.
- `CapId` also carries mode marks in its high bits (`RESUMED`, `NONPORTABLE`,
  `NOT_MANY` in `body/caps.rs:13-25`). Each user of a capability set must filter
  the marks.
- The workspace-wide `too_many_lines = "allow"` hides all of this.
- Repro: `repro/QA9_function_sizes.sh`.
- Fix:
  - Split `call_fn_as` into argument ordering, argument evaluation, call node, place
    checks and function-value effects.
  - Split `diagnose` into one function for each rule.
  - Put the loop-carried state into one struct that `lower_loop` saves and restores.
  - Use a separate type for the mode marks.

### QA10 (minor): the corpus runner compares sets, so it cannot count errors

- Where: `crates/weft-check/tests/programs.rs` (`expected`, `run`). They use
  `BTreeSet<(line, code)>`.
- `72_linear_drops.wf:259` is marked `//~ W0601 W0601`. One error passes this test
  too.
- Six other corpus lines give two errors with the same code today. Their marker
  names the code once.
- Repro: `repro/QA10_corpus_set_compare.txt` and `repro/QA10_find_dups.sh`.
- Fix: compare sorted multisets.

### QA11 (minor): one invalid use gives two W0301 errors, and one names a hidden variable

- `print(w.x.hp)` after `clear` gives two errors: "`w` used after it was
  invalidated" and "the value in `w.x` used after it was invalidated".
- `45_stored.wf:47` shows the internal name `{stored closure}` with braces.
- Repro: `repro/QA11_duplicate_w0301.wf` gives 2 errors at line 13.
- Fix: group W0301 by (use node, invalidating node). Show the user variable and put
  the hidden holder in a note.

### QA12 (minor): the public `diagnose()` returns raw line markers

- `weft_check::diagnose::diagnose` is public. Its notes hold in-band markers such as
  `{line:54}` and `{lines:...}`. Only `check_analysis` calls `resolve_lines`, and the
  doc comment of `diagnose` does not say this.
- A library user gets "invalidated at line {line:54}".
- The markers are also plain text in the note. A label or a place display that
  contains `{line:` would be changed too.
- Repro: `repro/QA12_raw_note_markers.rs`. It is a harness binary, and its output
  is in this report.
- Fix: keep the node offsets in a typed field of the note, such as
  `Note { text, lines: Vec<u32> }`. Or make `diagnose` take the `SourceFile`.

### QA13 (minor): tests that assert too little or depend on the clock

- `the_in_place_check_is_fast_on_a_long_chain` (`crates/weft-sema/src/tests.rs`)
  uses the forward `in` chain of QA3. It checks only the codes and the time. The
  facts of x0 to x(n-2) are empty, and the test does not see it.
  (`repro/QA13_in_chain.wf`: `points_into` exists only for the last two parameters.)
- Wall-clock limits: `scale.rs:39,133` (< 1 s), `sema tests.rs:1059,1080,1097`
  (< 2 s) and `tests.rs:1208` (< 10 s). These can fail on a loaded CI machine. A
  count of work is stable: lowerings, loop passes, calls of `overlaps`.
- No scale test covers QA4, QA7 or QA8. `scale.rs` times only `check()`, not sema.
- Repro: `repro/QA13_tests.txt`.

## Checked with no new finding

- Panics and overflow: there is no `unwrap`, `expect` or `panic!` in the production
  code of the range (only in `#[cfg(test)]`). Index arithmetic in `call_fn_as`
  (`sig.params.len() - first`) is safe now: W0104 stops a method with no `self`.
- `infer.rs`:
  - The worklist and the name graph are linear on a 6 400-function chain (0.18 s).
  - A ring of 400 mutually recursive functions, each with its own effect, takes
    1.4 s (about n^2.5). This is not realistic, so it is not a finding.
- `props.rs`: the fixpoint is linear. Wide and deep types, and an 80-level generic,
  are fast.
- `exhaust.rs`: the matrix budget gives an error, not a silent result. 2 000 arms
  take 1.1 s. Most of that time is the `VariantDef` clone in `match_pattern` (known
  QR16).
- `drops.rs`: `dropped_params` is O(variables × nodes) for generic bodies only. A
  reassignment after a move (`x = f(x)`) does not give a false drop.
- `flow.rs`, `repeat.rs`, `caps.rs`: no defect found. These shapes are fast:
  closures, handlers, tasks, many references, wide structs and many parameters.
- Effect inference converges on the round-1 33-link chain. W0702 is correct.
- The `codes.rs` table covers every emitted code.
