# Core IR: implementation plan

Status: plan for ADR 0012 (proposed). Date: 2026-10-20. Base: the head of `main` after the
R3a merge (`b25faf0`, or later if the R3a workflow in `/home/user/wt-core` lands more
fixes first).

Read with: the specification `ir.md` and the ADR `0012-core-ir.md` (both next to this
file in `SCRATCH/ir/`; stage S00 copies them to `docs/ir.md`,
`docs/adr/0012-core-ir.md` and `docs/plan/core-ir.md`). `SCRATCH` is
`SCRATCH`. A
reference such as "ir §6.5" is a section of the specification.

The main sequence has 57 stages in eight phases. Each stage is one commit that an agent
can do in a few hours. Track P (8 stages, after the removal) holds the precision and
proof work.

| Phase | Stages | Result |
| --- | --- | --- |
| S | S00 | the documents in the repository |
| G | G1 to G7 | the diff gate, the oracle cache, the ledger, the claims test, the baseline |
| T | T1 to T3 | expression ids, the final type table, the THIR tables |
| B | B1 to B12 | the IR crate, the verifier, the builder for each construct |
| I | I1 to I6 | the interpreter runs the IR; the engine differential; landing pads |
| F | F1 to F20 | the analysis, the summaries and the fact generator, one construct group at a time |
| C | C1 to C3 | the full gate, a fresh sweep, the switch of the defaults |
| R | R1 to R5 | the standalone `typeck`; the old pipeline goes away |

---

## 1. Ground rules

1. **TDD.** Each stage writes its tests first and sees them fail for the right reason.
   Then the code, then a refactor. A spec rule change (none is planned before track P)
   follows ADR 0002 and `CLAUDE.md`.
2. **Gates of `CLAUDE.md` at each stage.** `cargo fmt --all`,
   `cargo clippy --workspace --all-targets -- -D warnings`, `cargo test --workspace`.
   `proofs/verify-all.sh` when a file under `proofs/` or `crates/weft-verified` changes.
   No `unwrap()` in production code. No `unsafe`. Docs and comments in ASD-STE100.
3. **The diff gate at each stage** (section 2), from stage G5 on. Tier 1 runs in
   `cargo test --workspace` (the test `crates/weft-gate/tests/tier1.rs`). Tier 2 runs at
   the exit of each stage that the stage text marks "tier 2". A stage that does not turn
   a construct group on must not change any diagnostic or fact of the old pipeline: the
   old snapshot of tier 1 must equal the committed baseline (`tests/gate/baseline-tier1.jsonl`,
   stage G6; a fix under rule 6 updates the baseline in its own commit, with its reason),
   and the `ir` side must not get worse than at the last group stage. A stage that changes
   `crates/weft-interp/src` regenerates `tests/gate/oracle-ast.tsv` and
   `tests/gate/oracle-ir.tsv` in the same commit (the cache key holds the hash of the
   interpreter sources, section 2.4). `tests/tier1.rs` fails with a clear message on a
   stale key; it does not run the oracle itself. A verdict of the `ast` engine must not
   change before stage C3 unless the stage says why (the AST engine is the oracle of the
   old pipeline). A stage that adds programs to tier 1 (G2 after G4, a repro under rule 6,
   F9, C2) adds their verdicts to the committed caches in the same commit.
4. **One commit for each stage.** The message starts with `IR <id>: <title>`.
5. **Time box.** If a stage cannot meet its exit in its box, commit the part that passes
   all gates (the new code stays behind its construct group, which stays off), and add
   follow-up stages `<id>.1`, `<id>.2`, ... to the table of section 5, one for each group
   of remaining differences (grouped by the pair of codes and the shape). A follow-up stage
   has the same gate and exit as its parent. A stage that depends on stage X also depends
   on each follow-up `X.k`: a group-on stage and its follow-ups end before the next stage
   builds on that group.
6. **The old pipeline is frozen.** `crates/weft-sema/src/body/` and
   `crates/weft-interp/src/compile.rs` get only realistic blocker fixes (ship rule). Each
   such fix adds its repro to `tests/gate/probes/fixes/`, so the new pipeline must pass it
   too. After stage F8, a fix of a shape that a group on the new pipeline covers goes into
   the new pipeline only, unless a release before stage C3 ships the old pipeline as the
   default: then the ship rule applies to the old pipeline too.
7. **Defaults.** `--facts=old` and `--engine=ast` stay the defaults until stage C3. The
   new pipeline is used only for programs in scope (section 2.6).
8. **Names.** New code goes where `ir §1.4` says. New tests go where the stage says.
9. **No stage reads `SCRATCH` after G2.** `SCRATCH` belongs to one session and can go
   away. S00 copies the documents and the design inputs. G2 copies the hand probes, the
   Datalog traces of the judges, and the oracle tools into `tools/gate/gen/`
   (`SCRATCH/r3/oracle/{gen3,gen4,mutate3,sweep4,harness}.py`,
   `SCRATCH/r2/oracle/{gen,reduce}.py`), and the review records into
   `docs/plan/core-ir-inputs/reviews/` (`redteam_review.md`, `spec_review.md`,
   `quality_review.md`, `r2/*.md`, `r3/*.md` with `r3/issues.md`, `round1b_tasks.md`,
   `round1a_results.json`, `round1b_results.json`, `round2_results.json`: about 1 MB). A
   later stage reads these copies (G4 the `BENIGN` list of `harness.py`, G7 the reviews,
   C2 the generators). In a stage text after G2, a path `SCRATCH/<p>` of a probe or a
   trace means its copy `tests/gate/probes/<p>`, a review record `SCRATCH/<r>` means
   `docs/plan/core-ir-inputs/reviews/<r>`, an input `SCRATCH/ir/<i>.md` means
   `docs/plan/core-ir-inputs/<i>.md`, and `SCRATCH/ir/work/final/weft_ir_final/` means
   `docs/ir-sketch/`. Tier 2 reads its probes from
   `WEFT_GATE_PROBES`; stage G1 makes an archive of them (section 2.1).

---

## 2. The gate

### 2.1 Inputs

| Set | Source | Files (distinct) | Tier |
| --- | --- | --- | --- |
| corpus | `tests/programs/*.wf` (with `//~` markers) | 138 | 1 |
| interpreter programs | `crates/weft-interp/tests/programs/*.wf` (with `.out`) | 61 | 1 |
| examples | `examples/package`, `examples/gc-lib` (package mode), and each `.wf` below `examples/` | 2 packages | 1 |
| packages | `tests/packages/*` | 1 package (`hidden`) | 1 |
| IR targets (set `ir_targets`) | `tests/ir_targets/*.wf`: the bad cases that the checker accepts today and that the core IR must reject (`docs/traceability.md`) | 6 | 1 |
| hand probes | the hand-written probes of rounds 1 to 3, of their stage verifiers and of the IR design, copied into `tests/gate/probes/` by stage G2 (section 2.2) | 3 112 (3 492 paths; 20 of the entries are packages) | 1 |
| all probes | every `.wf` under the report roots `SCRATCH/redteam`, `specreview`, `r2`, `r3`, `ir`, and the stage roots `SCRATCH/verify`, `fix`, `s2`, `s2fix`, `edge`, `edgefix`, `partb`, `s5`, `s5r`, `s1fix`, `p`, `core`, `backup` and the `.wf` files at the top of `SCRATCH`, with the exclusion rule below | 59 944 paths, 57 393 distinct entries; a package is one entry (the report roots: 51 565 and 49 446; the stage roots and the top add 8 379 and 7 947) | 2 |

The stage roots hold the repros of the stage verifiers (V001 to V138: 86 of the 180
unsound findings) and of most of the open lists. A gate without them would miss half of
what the earlier rounds found.

The exclusion rule of tier 2: skip a file below a directory that holds a `Cargo.toml`
(a copy of the source tree), and a file with a path component `target`, `crates`,
`tests`, `std` or `examples` (copies of the repository; the repository sets have the
current versions). Dedupe by SHA-256 of the text; keep the first path in sorted order and
record the others. The manifest (`target/gate/manifest-tier2.tsv`) is not committed;
`tests/gate/manifest-tier1.tsv` is. `SCRATCH` can go away, so stage G1 also writes an
archive of the tier-2 files (`target/gate/probes-tier2.tar.zst`; about 200 MB of text
before compression), records its SHA-256 in `tests/gate/probes-tier2.sha256`, and
commits the archive as `tests/gate/probes-tier2.tar.zst` (about 6 MB). The tier-2 root
is the flag `--probes`, else the environment variable `WEFT_GATE_PROBES`, else (from
stage G2) the committed archive: `weft-gate` checks its hash and unpacks it into
`target/gate/probes-tier2` when that directory does not record the committed hash.
`SCRATCH` is a tier-2 root only through the flag or `WEFT_GATE_PROBES`.

### 2.2 Hand probes (tier 1)

Stage G2 copies these directories of `SCRATCH` into `tests/gate/probes/<same path>`:
`redteam/` (with `redteam/pkg` as a package), `specreview/progs/`, and below `r2/` and
`r3/` each directory named `p`, `probe`, `probes`, `repro`, `r2probes`, `fp`, `fp2`, `fp3`,
`min`, `sanity`, `b6`, `crash`, `cli`, `big`, `lib`, `pkgA`, `pkgB`, `triage`; and
`ir/probes/`, `ir/work/map/`, `ir/work/machine/` (the `.wf` files only), `ir/work/mir/`,
`ir/judge_sound/` (the `.wf` files and the Datalog traces `*.dl` and `run_all.sh`, which
stage F15 reads), `ir/work/judge/p/`. From the stage roots it copies each directory named
`p`, `probes`, `repro` or `rt1` below `verify/`, and the directories `fix/`, `s2/`,
`s2fix/`, `edge/`, `edgefix/`, `partb/`, `s5/`, `s5r/`, `s1fix/`, `p/` and `core/`.
Generated sets (`runs`, `seeds*`, `sweep*`, `t0`, `gen*`, `fuzz*`, `fz*`, `mut*`,
`effmut_*`, `genout`, `fuzzout`, and `verify/quality/gen/`) and each file larger than
256 KB stay in tier 2. Stage G2 also applies the exclusion rule of tier 2 (section 2.1),
so that each copied file is also in the tier-2 archive. The hand set is then 3 112
distinct entries (3 469 `.wf` files and 23 packages, 6.4 MB). `SOURCES.md`
in `tests/gate/probes/` names the origin of each directory, and the report or stage
result (`SCRATCH/round1a_results.json`, `round1b_results.json`, `round2_results.json`)
that names each verifier repro.

### 2.3 What the gate computes for each program

For each pipeline `old` and `ir` (`--facts=old`, `--facts=ir`):

1. **Diagnostics:** the multiset of `(code, file, line)` of the errors and warnings of
   `check --json`.
2. **Violations:** for each sink relation of the spec, the tuples with variable names and
   node lines (from `FnFacts::vars` and `nodes`).
3. **Fact digest:** for each input relation, the tuples with node ids replaced by
   `(line, label)`, variable ids by names, and place ids by their display text. The gate
   reports the counts of each relation for `old` and `ir` and the tuples that differ. The
   digest is information, except the relation cover check: each input relation that the
   `old` facts emit somewhere on the programs of tier 1 in scope must also appear in the
   `ir` facts of those programs (a missing template shows here). A committed snapshot
   (a baseline) holds the counts of each relation and a SHA-256 of the canonical digest,
   not the tuples: the full digests of tier 1 are 20 to 60 MB. The full digest goes to
   `target/gate/`.
4. **Agreement:** `weft agree` on the `ir` facts (checker equals spec, with the evidence
   check of ADR 0002).
5. **Lints:** `proofs/link/lints/gen_kill.dl` and `unbound_use.dl` on each component of
   the `ir` facts: no result.
6. **Verifier:** `weft_ir::verify::verify_program` on the IR: no broken rule.
7. **Oracle verdict:** from the cache (2.4), for the engine that matches the pipeline:
   `ast` for `old`, `ir` for `ir` (from stage I5 on; before it, `ast` for both).
8. **Cost:** the time of `check` with each pipeline, and the number of facts of each
   function.

### 2.4 The oracle cache

`weft run --unchecked --oracle` (or `weft test` for a file with test blocks, no `main`)
with the six configurations of the round-3 harness: seed and workers (1,1), (2,4), (3,2),
(7,4), (11,1), (42,3); a time limit of 10 s each. The verdict is the first of: `fault`
(an oracle fault or a panic), `timeout`, `fail` (the program fails through `fail`),
`benign` (a fault that stops the run and is not a soundness signal: the `BENIGN` list of
`SCRATCH/r3/oracle/harness.py`: out of bounds, overflow, underflow, does not fit, cannot
listen, division by zero, duration underflow, split point out of bounds), `clean`, or
`not-runnable` (no `main` and no tests). The key is the SHA-256 of the text, the engine
(`ast` or `ir`) and the hash of the interpreter sources. The oracle verdict does not
depend on the fact generator (`--unchecked`), so the gate computes it once for each
interpreter version. Tier 1: `tests/gate/oracle-ast.tsv`, `tests/gate/oracle-ir.tsv`
(committed; rule 3 of section 1 says when to regenerate them). Tier 2:
`$WEFT_GATE_CACHE` (default `target/gate/`).

### 2.5 Classes and rules

Let `D_old`, `D_ir` be the errors of the two pipelines and `O` the oracle verdict of the
engine of the `ir` pipeline. "Accepts" means no error.

| Class | Condition | Rule |
| --- | --- | --- |
| `crash` | the `ir` pipeline panics, the verifier finds a broken rule, agreement fails, or a lint has a result | **blocks** |
| `same` | `D_ir == D_old` | nothing, but see `open` |
| `open` | `ir` accepts and `O` is `fault` (whatever `old` says) | **blocks**, unless the ledger has an entry of class `open` with a finding id whose verdict in `ir §10` is "stays", or with class `edge` and an issue number (ship rule). From stage G6 to C1 an `open` program with an `open-old` entry (stage G6: the old pipeline accepts it and it faults today) is reported, not blocking, unless the claims file says that the enabled groups must close it. At C1 every `open` program needs an entry of class `open` (verdict "stays") or `edge` (with an issue). |
| `fixed` | `old` accepts, `ir` rejects, `O` is `fault` | good; reported |
| `new-fp` | `old` accepts, `ir` rejects, `O` is `clean`, `benign`, `fail` or `not-runnable` | **blocks** in the corpus, the interpreter programs, the examples and the packages. In the probes: a ledger entry with a reason class (a stricter rule of the ADR, a precision loss with an issue). At most 0.1 % of the probes that `old` accepts. |
| `lost-fault` | `old` rejects, `ir` accepts, `O` is `fault` | **blocks** always (a regression) |
| `lost-clean` | `old` rejects, `ir` accepts, `O` is not `fault` | a ledger entry with the false-positive id that it fixes, or a reason, and `signed_by` a reviewer (a person or a review agent that is not the author of the stage). A clean oracle run does not prove soundness. |
| `moved` | both reject; the same codes and counts; other lines | a ledger entry for each group (code, reason) |
| `changed` | both reject; other codes or counts | a ledger entry for each group of code pairs, with a reason |

The ledger is `tests/gate/ledger.toml`:

```toml
[[entry]]
class = "lost-clean"
files = ["tests/gate/probes/r2/oracle/fp/v069_part.wf"]   # paths or globs
finding = "V069"
reason = "STATE: the holder of the part rebinds at the new value"
signed_by = "review agent, stage F8"
stage = "F8"
```

The claims file is `tests/gate/claims.toml` (stage G7):

```toml
[[claim]]
finding = "M3"
kind = "unsound"            # unsound: the ir pipeline must reject; fp: it must accept
group = "D"                 # the construct groups that the repro uses (a set: "CE")
stage = "F15"               # the stage that turns the claim on (ir §10.4)
repro = ["tests/gate/probes/ir/work/machine/m8_abort_value_into_body.wf"]
code = "W0301"              # optional: the code that the rejection must have
line = 11                   # optional
```

A claim is on when each group of its `group` set is on and its stage is done. The scope is
for each program (2.6), so a repro that uses a loop and a closure is in scope only when
groups B and C are both on. From stage F1 on, the claims test checks that `group` equals
the groups that `irbuild/scope.rs` computes for the repro.

### 2.6 Scope: which programs use the new pipeline

`crates/weft-sema/src/irbuild/scope.rs` gives each body the set of construct groups that
it uses:

| Group | Constructs |
| --- | --- |
| A | `let`, assignments, places, borrows, blocks, `if`, `&&`, `||`, `match`, `return`, calls of items and methods (also generic extern items), aggregates, operators, `print`, `assert`, `Rc`, `Box`, `Weak`, performs through the row of the caller, `on abort` |
| B | `while`, `loop`, `for`, `break`, `continue` |
| C | closures, function values, function items as values, stored function values, function parameters |
| D | `handle`, clauses, `resume`, `multi` |
| E | `scope`, `spawn`, `join`, `detach`, `fork`, `sim.run`, `with_timeout` |
| F | user functions with type parameters (bodies with values of a type parameter) |

`Options::ir_groups` is the set of groups that are on. A program is in scope if each of its
bodies uses only groups that are on; else `--facts=ir` and `--facts=both` use the old
pipeline for the whole program and say so (`weft check --facts=ir` prints one note). The
gate reports the coverage: the share of programs of each set in scope. A stage that turns
a group on adds it to the default set of `ir_groups`.

As built (F1): `irbuild/scope.rs` reads the groups from the IR of each function or test
and of each body inside it. A loop that never goes back to its head (`loop { break }`) is
group A. A local whose type has a function part (also through fields) is group C; a task
handle, a scope capability or `sim.run`/`with_timeout` as a value is group E; a
capability or a continuation is group D; a type that names a type parameter is group F. A
body with no IR (a type error, W0303) uses no group: the `ir` pipeline gives it no facts,
and the diagnostics of `typeck` reject the program. A body that the builder does not
lower keeps the program out of scope. A program is in scope when its groups are on and
the fact generator (`factgen::emit`) supports them; until F8 the stub supports none.
As built (F10-fix, hole H-B): a body with no IR keeps the program in scope only if the
program reports an error for the reason (`irbuild::Entry::reported`): a W01xx diagnostic
of `typeck` in the body, a declaration error, or W0303 in the body. A conflict in the THIR
tables, a variant payload, or a type error with no W01xx diagnostic keeps the program out
of scope: no pipeline would check that body. The
gate computes both records in one analysis (`--facts=both`), reports the coverage, and
also the share of programs of each set that use only the groups of each group stage.

### 2.7 Common exit criteria

Each stage that changes `ir` diagnostics ends only if, on the programs in scope:

1. no `crash`, no `lost-fault`, and no `open` program that the claims file or the stage
   says must close;
2. each `new-fp`, `lost-clean`, `moved` and `changed` program has its ledger entry, and
   the corpus, interpreter programs, examples and packages have no `new-fp`;
3. the claims of the enabled groups hold (`cargo test -p weft-gate --test claims`);
4. the cost: the total `check` time of the `ir` pipeline is at most 2 times the `old`
   time on the same programs, the facts of each function are at most 3 times as many, and
   `crates/weft-check/tests/scale.rs` and `crates/weft-cli/tests/limits.rs` pass with
   `--facts=ir`. As decided at stage C1.4 (ADR 0013): a fact is a row of an input
   relation of the spec that the checker reads (each fact of `bridge::each_fact`, also
   `cfg_edge` and the place table). The `ir` pipeline removes the rows that no rule can
   read (`factgen::prune`, `docs/ir.md` 6.2), so these rows do not count; the old facts
   count as they are. The bound for each function is 3 times the old rows plus a fixed
   part of 64 rows (a function of 1 to 4 old rows has no stable ratio). The time is the
   CPU time of one release process for each check of the single-file programs of tier 1
   in scope; the time criterion did not change;
5. tier 2 for the stages that say "tier 2".

### 2.8 Commands

```bash
cargo run -p weft-gate --release -- manifest --tier 1|2           # the manifest
cargo run -p weft-gate --release -- oracle --engine ast|ir --tier 1|2
cargo run -p weft-gate --release -- run --tier 1|2 [--groups ABCDEF] --report target/gate/report.md
cargo run -p weft-gate --release -- run --tier 1|2 --write-baseline  # the old records into the baseline (G6)
cargo run -p weft-gate --release -- engines --tier 1|2             # ast versus ir interpreter (from I5)
cargo run -p weft-gate --release -- sweep --n 50000 --seed-base N  # fresh generated programs (C2)
cargo test -p weft-gate                                             # tier 1, the claims, the ledger syntax
```

Cost (measured on the R3a binary): 6 to 40 ms for each check and 42 ms for each oracle run.
Tier 1 (about 3 300 programs) with both pipelines takes 2 to 5 minutes (a debug check
takes about 40 ms). Tier 2 takes 12 to 80 core-minutes; the oracle cache of tier 2 takes
about 4 core-hours once for each interpreter version.

---

## 3. Stage overview

| Id | Title | Depends on | Tier 2 |
| --- | --- | --- | --- |
| S00 | Documents into the repository | | |
| G1 | `weft-gate` crate and manifests | S00 | |
| G2 | Hand probes into `tests/gate/probes` | G1 | |
| G3 | Snapshots: diagnostics, violations, fact digest | G1 | |
| G4 | The oracle cache | G1 | yes (cache) |
| G5 | Classifier, ledger, report, tier-1 test | G3, G4 | |
| G6 | Baseline of the old pipeline | G2, G5 | yes |
| G7 | Claims file and claims test | G6 | |
| T1 | `ExprId` and `PatId` on the AST | G6 | |
| T2 | `weft-ir` crate: the final type table | S00 | |
| T3 | THIR tables recorded by the old lowering | T1, T2, G6 | yes (D0) |
| B1 | IR types and printer | T1, T2 | |
| B2 | The verifier | B1 | |
| B3 | Builder core: bodies, scopes, locals, frame end, `weft ir` | B2, T3 | |
| B4 | Builder: places, dereferences, borrows, assignments | B3 | |
| B5 | Builder: `if`, `match`, patterns, `Uninit` | B4 | |
| B6 | Builder: loops and jumps | B5 | |
| B7 | Builder: calls, methods, aggregates, `print`, `assert`, performs through the row | B6 | |
| B8 | Builder: cleanup chains | B7 | |
| B9 | Builder: closures and function values (rule CAPTURE) | B8 | |
| B10 | Builder: `handle`, clauses, `resume`, upvars | B9 | |
| B11 | Builder: tasks, `sim.run`, `with_timeout` | B10 | |
| B12 | Builder total on the gate; golden IR of the corpus | B11 | yes |
| I1 | `compile_ir` core and `--engine` | B12 | |
| I2 | `compile_ir`: closures and function values | I1 | |
| I3 | `compile_ir`: handlers and continuations | I2 | |
| I4 | `compile_ir`: tasks, `sim.run`, `with_timeout` | I3 | |
| I5 | Engine differential, parity D1, IR oracle cache | I4, G4 | yes |
| I6 | Landing pads and the unwind order | I5 | yes |
| F1 | `--facts=old|ir|both`, scope, fallback | B12, G5 | |
| F2 | Fact generator skeleton: nodes, roots, α, variables, `RELS` | F1 | |
| F3 | Analysis: domain and transfer (straight-line) | F2 | |
| F4 | Templates: statements, simple terminators, operands | F3 | |
| F5 | Summaries: type, signatures, `apply` at calls | F4 | |
| F6 | `summarize`, the call-graph fixpoint, effect inference | F5 | |
| F7 | Aborts past the function; `on abort` | F6 | |
| F8 | Group A on | F7, I5 | yes |
| F9 | Fact oracle and trace conformance | F8, I6 | |
| F10 | Group B on: loops | F9 | yes |
| F11 | Closures (group C, part 1) | F10 | |
| F12 | Function values (group C, part 2) | F11 | |
| F13 | Stored values and the summary oracle; group C on | F12 | yes |
| F14 | Handlers: splice, perform, `Exit`, `Post` (group D, part 1) | F13 | |
| F15 | Abort destinations of local handlers (group D, part 2) | F14 | |
| F16 | `resume`, continuations, `multi` (group D, part 3) | F15 | |
| F17 | W0313 over roots; group D on | F16 | yes |
| F18 | Tasks: scopes, spawn, join, detach (group E, part 1) | F17 | |
| F19 | `fork`, `sim.run`, `with_timeout`, W0314; group E on | F18 | yes |
| F20 | Generics; group F on | F19 | yes |
| C1 | Full gate at full coverage | F20 | yes |
| C2 | Fresh sweep | C1 | yes |
| C3 | Switch the defaults | C2 | yes |
| R0a to R0z | The fallbacks to the old pipeline (Phase R, R0) | C3 | yes |
| R1 | Standalone `typeck`, part 1 | C3 and one review round | yes (D0) |
| R2 | Standalone `typeck`, part 2; switch the THIR source | R1 | yes |
| R3 | Remove the old fact generator | R2, R0z | yes |
| R4 | Remove the AST compiler of the interpreter | R3 | yes |
| R5 | Documents and checklists | R4 | |

T2 can run in parallel with phase G after S00. T1 and T3 change code of the old pipeline
(the parser, `body/`), so they wait for the baseline of G6: the gate must show that the
old pipeline does not change. Phase B follows T1 and T2. Phase I can run in parallel with
F1 to F7. Track P (section 6) starts after R5.

---

## 4. Stages

Each stage lists: the stage it depends on, the sections of `ir.md` to read, the goal, the
files, the tests to write first, the work, the gate and the exit. "The common gates" are
rule 2 of section 1. "The common exit" is section 2.7.

### Phase S

#### S00 Documents into the repository

- Depends on: nothing.
- Read: `docs/adr/0012-core-ir.md`, `docs/ir.md` §1, this plan §1 to §3.
- Goal: the decisions, the specification and the plan are in the repository, so later
  stages and reviewers read them there.
- Files: `docs/adr/0012-core-ir.md` (from `docs/adr/0012-core-ir.md`), `docs/ir.md`
  (from `docs/ir.md`), `docs/plan/core-ir.md` (from `docs/plan/core-ir.md`);
  `docs/plan/core-ir-inputs/` (the inputs of the design, from `SCRATCH/ir/`:
  `root_causes.md`, `semantics.md`, `map_lowering.md`, `design_machine.md`,
  `design_mir.md`, `design_minimal.md`, `judge_soundness.md`, `judge_feasibility.md`,
  `judge_proofs.md`, and `work/findings.py`, the data of the verdicts that stage G7 reads);
  `docs/ir-sketch/` (the sources of the compiled sketch,
  `SCRATCH/ir/work/final/weft_ir_final/src/*.rs` and its `Cargo.toml`, as reference
  files: not a workspace member); `docs/architecture.md` (one paragraph: "A core IR is
  coming; see ADR 0012"); `README.md` (the layout table lists `docs/ir.md`).
- Tests first: none (documents). Check that the links in the copied files resolve:
  replace each `docs/ir.md` and `docs/ir.md` link by `docs/ir.md`, each `plan.md`
  link by `docs/plan/core-ir.md`, each `ir/<input>.md` link by
  `docs/plan/core-ir-inputs/<input>.md`, and keep `SCRATCH` paths only for the probes.
- Gate: the common gates (they pass with no code change).
- Exit: the three files are in `docs/`; ADR 0012 has status "proposed".

### Phase G: the gate

#### G1 `weft-gate` crate and manifests

- Depends on: S00.
- Read: this plan §2.1, §2.2, §2.8.
- Goal: a development crate that lists the programs of the gate.
- Files: `Cargo.toml` (workspace member), `crates/weft-gate/Cargo.toml`
  (`publish = false`; depends on `weft-cli`, `weft-check`, `weft-sema`, `weft-interp`,
  `serde`, `serde_json`, `toml`), `crates/weft-gate/src/main.rs` (subcommands),
  `crates/weft-gate/src/manifest.rs`, `crates/weft-gate/tests/manifest.rs`.
- Tests first: in a temporary directory tree, the manifest (a) finds `.wf` files, (b)
  skips a file below a directory with a `Cargo.toml` and a file with a path component
  `target`, `crates`, `tests`, `std` or `examples`, (c) dedupes by SHA-256 and keeps the
  first path in sorted order, (d) marks `has_main` and `has_tests`, (e) treats a directory
  with `weft.toml` as one package entry.
- Do: `manifest --tier 1` lists the repository sets of §2.1 and `tests/gate/probes/`
  (empty until G2) into `tests/gate/manifest-tier1.tsv`; `manifest --tier 2` reads
  `WEFT_GATE_PROBES` (default: the committed archive from stage G2 on, section 2.1),
  takes the report roots and the stage roots of
  §2.1, and writes `target/gate/manifest-tier2.tsv`. Columns: hash, path, set, mode (file
  or package), has_main, has_tests, other paths. `archive --tier 2` writes the archive of
  §2.1 and its SHA-256.
- Gate: the common gates.
- Exit: `cargo run -p weft-gate -- manifest --tier 2` lists 57 393 distinct entries
  (59 944 paths; a package is one entry): 49 446 (51 565) from the report roots and
  7 947 more (8 379) from the stage roots and the `.wf` files at the top of `SCRATCH`;
  tier 1 lists 138 corpus programs, 61 interpreter programs, 2 example packages and
  1 package; the archive exists and its hash is committed; the tests pass.

#### G2 Hand probes into `tests/gate/probes`

- Depends on: G1.
- Read: this plan §2.2; `docs/ir.md` §10.2 (the new probes) and §10.4 (the repros
  of the round 2 and round 3 blockers).
- Goal: the curated probes of rounds 1 to 3 and of the IR design are in the repository, so
  CI runs them at each commit.
- Files: `tests/gate/probes/**` (copies), `tests/gate/probes/SOURCES.md`, `tools/gate/gen/`
  (the oracle tools of rule 9, as they are), `docs/plan/core-ir-inputs/reviews/` (the
  review records of rule 9),
  `crates/weft-gate/src/copy.rs` (a `copy-probes` subcommand, so the copy can run again),
  `tests/gate/manifest-tier1.tsv` (regenerated).
- Tests first: `crates/weft-gate/tests/manifest.rs`: the tier-1 manifest holds each probe
  of `ir §10.2` (M1 to M4, J1 to J6, `postres.wf`, `opres.wf`, `fnres2.wf`, p2, p9, p10,
  p25, p27) and each control (`j5b_kept_write.wf`, `j5c_kept_borrow_task.wf`,
  `d5_count.wf`, `m6_resume_result_body_local.wf`, `m9_resume_twice_tail.wf`).
- Do: copy the directories of §2.2, `.wf` files only (and package directories with their
  `weft.toml`, and the judge traces `ir/judge_sound/*.dl`). Keep the relative paths.
  Dedupe against the repository sets. Each repro path of `ir §10.4` must be in the copy.
  Also: add `tests/ir_targets/` to tier 1 as its own set `ir_targets` (section 2.1);
  make the committed archive the default tier-2 root (section 2.1), so that `SCRATCH`
  is a root only through `WEFT_GATE_PROBES`.
- Gate: the common gates. The repository grows by about 10 MB; check that `git status`
  shows only text files.
- Exit: about 3 100 distinct hand probes in `tests/gate/probes/`, with the repros of the
  stage verifiers; the tests pass (also a test that each repro path of `ir §10.4` exists
  in the copy). Result: 3 112 distinct entries (3 492 paths), from 78 directories;
  `SCRATCH/edge/hold/26_stealable.wf` is not copied (it is
  `tests/programs/54_stealable.wf`); each copied program is in the tier-2 archive.
  The tier-1 manifest lists 3 320 distinct entries (3 700 paths).

#### G3 Snapshots: diagnostics, violations, fact digest

- Depends on: G1.
- Read: this plan §2.3.
- Goal: one record for each program and pipeline, in process (no `weft` process for each
  file), on the large stack (`weft_sema::on_large_stack`).
- Files: `crates/weft-gate/src/snapshot.rs`, `crates/weft-gate/src/digest.rs`,
  `crates/weft-gate/tests/snapshot.rs`, small programs in
  `crates/weft-gate/tests/data/*.wf`.
- Tests first: for three small programs (one W0301, one W0601 with a package, one clean),
  the record has the expected diagnostics `(code, file, line)`, the violations with
  variable names and lines, and a digest whose `cfg_edge`, `points_into` and `scope_end`
  counts match `weft facts`. A panic of the pipeline gives a record of kind `crash`, not a
  panic of the gate.
- Do: `snapshot --tier N --facts old --out FILE.jsonl`. The digest maps node ids to
  `(line, label)`, variable ids to names and place ids to their display text. A record
  holds the diagnostics, the violations, the counts of each relation and the SHA-256 of
  the canonical digest; `--full-digest DIR` writes the tuples to files in `DIR` (not
  committed). A time
  limit of 60 s for each program (a `timeout` record). Parallel over programs with a
  thread pool (`std::thread`, one large-stack thread for each worker).
- Gate: the common gates.
- Exit: a tier-1 snapshot of the old pipeline in less than 5 minutes; the tests pass.

#### G4 The oracle cache

- Depends on: G1.
- Read: this plan §2.4.
- Goal: the oracle verdict of each program, computed once for each interpreter version.
- Files: `crates/weft-gate/src/oracle.rs`, `crates/weft-gate/tests/oracle.rs`,
  `tests/gate/oracle-ast.tsv`.
- Tests first: the verdict of `crates/weft-gate/tests/data/` programs: a dangling read
  gives `fault`; an index out of bounds gives `benign`; a `fail` gives `fail`; a program
  with no `main` and no test gives `not-runnable`; a program with test blocks runs the
  tests; an endless loop gives `timeout` (with a short limit in the test).
- Do: `oracle --engine ast --tier N` runs the six configurations through
  `weft_interp::run_analysis_main` and `run_analysis_tests` with `oracle: true`, unchecked.
  The key: text hash, engine, and the hash of the sources of `crates/weft-interp/src`. A
  cache hit skips the run. The `BENIGN` list of `SCRATCH/r3/oracle/harness.py` becomes a
  constant with the same texts (from the copy `tools/gate/gen/harness.py`; if G4 runs
  before G2, G4 makes that copy).
- Gate: the common gates. Tier 2: build the tier-2 cache of the `ast` engine once
  (about 4 core-hours; run it in the background).
- Exit: `tests/gate/oracle-ast.tsv` covers tier 1; the tier-2 cache exists in
  `target/gate/`.

#### G5 Classifier, ledger, report, tier-1 test

- Depends on: G3, G4.
- Read: this plan §2.5, §2.7.
- Goal: the classes and rules of §2.5 as code, and the CI test.
- Files: `crates/weft-gate/src/classify.rs`, `crates/weft-gate/src/ledger.rs`,
  `crates/weft-gate/src/report.rs`, `crates/weft-gate/tests/classify.rs`,
  `crates/weft-gate/tests/tier1.rs`, `tests/gate/ledger.toml` (empty).
- Tests first: synthetic snapshot pairs for each class of §2.5, with and without a
  ledger entry: `crash`, `lost-fault` and an unledgered `new-fp` in the corpus set block;
  a ledgered `lost-clean` with no `signed_by` blocks; a glob entry covers a group; a
  ledger entry that matches no program is a warning (stale entry).
- Do: `run --tier N` computes both snapshots (only programs in scope use `ir`; before
  F1 both are `old`), reads the oracle cache, classifies, writes
  `target/gate/report.md` (counts for each class and set, the coverage of each group, the
  list of blockers) and exits with a failure on a blocker. `tests/tier1.rs` runs
  `run --tier 1` (skipped with a message if `WEFT_GATE_SKIP=1`, for quick local loops).
- Gate: the common gates.
- Exit: `cargo test -p weft-gate` passes; with the old pipeline on both sides each
  program is `same` or `open`.

#### G6 Baseline of the old pipeline

- Depends on: G2, G5.
- Read: this plan §2.5 (class `open`).
- Goal: the record of today: which programs the old pipeline accepts and the oracle
  faults on.
- Files: `tests/gate/baseline-tier1.jsonl` (the old snapshot of tier 1, in the committed
  form of §2.3: no tuples),
  `tests/gate/ledger.toml` (entries of class `open-old`), `target/gate/baseline-tier2.jsonl`.
- Tests first: `crates/weft-gate/tests/tier1.rs` checks that the old snapshot equals the
  committed baseline (a change of the old pipeline shows), and that each `open` program
  of tier 1 has an `open-old` entry.
- Do: run tier 1 and tier 2 with the old pipeline. Group the `open` programs (old accepts,
  `ast` oracle faults) by the fault kind and the shape; give each group a finding id where
  a file name or `docs/plan/core-ir-inputs/root_causes.md` names one (M1 to M4, J1, J5d, N1 to N4, and
  the open lists), else `unclassified`. Write them as `open-old` entries. Record the counts
  in the report.
- Gate: the common gates; tier 2.
- Exit: the baseline files exist; `cargo test -p weft-gate` passes.

#### G7 Claims file and claims test

- Depends on: G6.
- Read: `ir §10` (the verdicts; §10.4 gives the stage of each blocker claim),
  `docs/plan/core-ir-inputs/root_causes.md`, `docs/plan/core-ir-inputs/findings.py`, this
  plan §2.5 (claims).
- Goal: each verdict "construction" or "one rule" with a repro becomes a test that the
  stage of its group must make pass (the MIR claims test).
- Files: `tests/gate/claims.toml`, `crates/weft-gate/src/claims.rs`,
  `crates/weft-gate/tests/claims.rs`.
- Tests first: the claims test (a) fails on a claim whose repro file does not exist, (b)
  skips a claim whose group is off, (c) fails if the `ir` pipeline accepts an `unsound`
  repro of an enabled group, or rejects an `fp` repro of an enabled group at the claimed
  line.
- Do: one claim for each row of `ir §10.4` and for each finding of `ir §10.1` and §10.2
  that has a repro among the hand probes (search the file names for the finding id, the
  repro paths in the round reports `SCRATCH/r2/*.md`, `SCRATCH/r3/*.md` and
  `SCRATCH/r3/issues.md`, the stage results `SCRATCH/round1a_results.json`,
  `round1b_results.json` and `round2_results.json` for V001 to V138, the "Open after"
  sections of `SCRATCH/round1b_tasks.md` for the `OL-` items, and the probes of
  `ir §10.2`). Set `group` to the set of construct groups that the repro uses and `stage`
  to the stage of `ir §10.4` (or of the group). A finding with no repro gets a comment
  line, not a claim.
- Gate: the common gates.
- Exit: `claims.toml` has the claims, with a claim for each row of `ir §10.4` that has a
  claim stage; with no group on, the test passes (each claim is skipped, each repro
  exists).

### Phase T: the typed tree

#### T1 `ExprId` and `PatId` on the AST

- Depends on: G6 (T1 changes the parser, so the gate must show that the old pipeline does
  not change).
- Read: `ir §2.1`.
- Goal: each expression and each pattern has an id, so the THIR tables can key on it.
- Files: `crates/weft-syntax/src/ast.rs` (`ExprId`, `PatId` newtypes; an `id` field on
  `Expr` and `Pat`), `crates/weft-syntax/src/parser.rs` (a counter for each unit),
  `crates/weft-syntax/src/pretty.rs` (ignores ids), `crates/weft-syntax/tests/parser.rs`.
- Tests first: the ids of one unit are unique and dense; a reparse of the pretty-printed
  program gives the same tree up to ids; the hidden locals of long chains get ids too.
- Do: add the fields; update each construction site of `Expr` and `Pat` (the parser and
  the desugaring of long chains). The ids carry no meaning across units. `Pattern` is an
  enum today: it becomes `struct Pattern { id: PatId, kind: PatternKind }`, and the 76
  matches on `Pattern::` (in `weft-syntax`, `body/`, `fip.rs`, `compile.rs`) match on
  `.kind`: a mechanical change. `PartialEq` of `Expr` and `Pattern` ignores the id, so
  the tests that compare trees stay as they are.
- Gate: the common gates; `crates/weft-cli/tests/limits.rs` passes; tier 1 equals the
  baseline of G6.
- Exit: every `Expr` and `Pat` has an id; no other behaviour changes.

#### T2 `weft-ir` crate: the final type table

- Depends on: S00.
- Read: `ir §2.3`, §3.1.
- Goal: the crate of the IR exists, with the final types that the THIR and the IR use.
- Files: `Cargo.toml` (member), `crates/weft-ir/Cargo.toml` (depends on `weft-syntax`
  only), `crates/weft-ir/src/lib.rs`, `crates/weft-ir/src/ty.rs` (`Ty`, `TyId`, `TyTable`
  interner, `AdtDecl`, `EffectDecl`, `IntTy`), `crates/weft-sema/src/types.rs` (a function
  `to_ir_ty` that zonks a settled `Ty` and drops the closure summary of `Ty::Fn`),
  `crates/weft-sema/src/props.rs` (a function `ir_props(&TyTable, TyId) -> Props`),
  `crates/weft-ir/tests/ty.rs`.
- Tests first: interning gives equal ids for equal types; `to_ir_ty` gives a free type
  variable the type unit and a free integer variable `i64` (`ir §2.3`), and is an error
  for `Ty::Error`; `ir_props` of the corpus types equals the old
  `props.rs` flags (a table test over the types of `tests/programs/35_wild_places.wf`,
  `83_kept_values.wf`, `153_partial_linear.wf`).
- Do: write the types from the case list of `ir §2.3`. `Props` has the fields of
  `ir §3.2`.
- Gate: the common gates.
- Exit: `weft-ir` builds with no dependence on `weft-sema`; the tests pass.

#### T3 THIR tables recorded by the old lowering

- Depends on: T1, T2, G6.
- Read: `ir §2.1`, §2.2.
- Goal: the THIR tables of each body, right by construction for the old types.
- Files: `crates/weft-sema/src/thir/mod.rs` (`Tables`: `expr_ty`, `pat_ty`, `binding`,
  `res`, `call`, `adjust`, `field`, `int_ty`, `closure`, `handle`, `effect`),
  `crates/weft-sema/src/thir/record.rs` (the recorder), the record calls in
  `crates/weft-sema/src/body/{expr,stmt,call,args,fnval,mod}.rs`,
  `crates/weft-sema/src/lib.rs` (`Analysis::thir: Vec<Tables>` for each body),
  `crates/weft-sema/tests/thir.rs`.
- Tests first (D0, part 1): on each tier-1 program, (a) each `Expr` of a body that the
  old lowering lowers has a type with no inference variable; (b) each name has a `res`;
  (c) each call has a `CallInfo` and its argument order equals `FnFacts::arg_order` for
  its span; (d) each arithmetic expression has an `int_ty` equal to `FnFacts::int_ops`;
  (e) each implicit dereference of a field, an index and a receiver has an `adjust` entry
  (compare with the derefs that `compile.rs` emits).
- Do: record in the last lowering of each body (the lowering after which the inference
  stops), after the types settle; zonk with `to_ir_ty`. The recorder only adds; no fact
  and no diagnostic changes (the gate shows `same` everywhere, and tier 1 equals the
  baseline of G6). The old lowering visits some expressions more than once in one
  lowering (the passes of a loop, `handled_again`): the recorder records each visit, and
  D0 fails if two visits disagree.
- Gate: the common gates; tier 1 all `same`; tier 2 runs D0 (a `thir` subcommand of the
  gate) with no failure.
- Exit: D0 part 1 holds on tiers 1 and 2.

### Phase B: the IR and the builder

#### B1 IR types and printer

- Depends on: T1, T2 (`Origin` holds an `ExprId`).
- Read: `ir §3`, §3.3; the sketch `SCRATCH/ir/work/final/weft_ir_final/src/lib.rs` and
  `example.rs`.
- Goal: the IR types of `ir §3.2` in `weft-ir`, and the text form.
- Files: `crates/weft-ir/src/lib.rs` (the ids and the module list),
  `crates/weft-ir/src/body.rs`, `place.rs`, `stmt.rs`, `term.rs`, `decl.rs` (from the
  sketch, with `TyId` from `ty.rs`), `crates/weft-ir/src/print.rs`,
  `crates/weft-ir/tests/print.rs`, `crates/weft-ir/tests/data/m3.ir`.
- Tests first: the M3 program of `example.rs` (moved into `crates/weft-ir/tests/`) prints
  to `m3.ir` exactly; each statement and terminator kind prints once (a table test).
- Do: copy the types (with `Program::tests` and `TestDecl` of `ir §3.2`, which the sketch
  does not have); keep the doc comments of the sketch; the printer prints places as
  `(*_1).0[_3]`, operands as `copy`/`move`/`const`, and each terminator with its successors
  and its cleanup block.
- Gate: the common gates.
- Exit: the tests pass; `missing_docs` gives no warning.

#### B2 The verifier

- Depends on: B1.
- Read: `ir §4`; the sketch `verify.rs`.
- Goal: `verify_program` with V1 to V18.
- Files: `crates/weft-ir/src/verify.rs`, `crates/weft-ir/tests/verify.rs`.
- Tests first: one test for each rule: a hand-built body that breaks only that rule gives
  only that `Broken` value (the sketch has seven such tests; add V8 to V10, V12, V14 to
  V18). The M3 program and the J5d program with `ByRef` pass; J5d with `Kept` breaks V13.
- Do: port the sketch rules; add the type rules with the `TyTable` (V8, V9, V10) and V12,
  V18. V16 takes the order of `ir §4` (`_0` first), not the order of the sketch. A
  broken rule names the body, the block and the local.
- Gate: the common gates.
- Exit: the tests pass.

#### B3 Builder core: bodies, scopes, locals, frame end, `weft ir`

- Depends on: B2, T3.
- Read: `ir §5.1.1` to §5.1.5, §5.2, §5.3, §5.4, §5.5, §5.10, §5.11, §5.15, §5.16.
- Goal: the builder for straight-line code of functions and tests.
- Files: `crates/weft-sema/src/irbuild/mod.rs` (the `Builder`: the scope stack, locals,
  temporaries, blocks, `into`, `operand`, `place`), `irbuild/frame.rs` (the frame end and
  jumps), `irbuild/stmt.rs`, `irbuild/expr.rs` (literals, names, operators, blocks,
  `let`, assignment to a local, `return`), `crates/weft-cli/src/lib.rs` (`weft ir FILE
  [FUNCTION]`), `crates/weft-sema/tests/ir_golden.rs`,
  `crates/weft-sema/tests/ir_golden/{let_tail,ops,ret_ref,block_tail}.wf` with `.ir`.
- Tests first: the golden files (the IR of each small program, printed); each body
  verifies; `x + { x = 5; 1 }` reads `x` into a temporary before the block (choice A);
  a block tail moves into its destination before the block locals end; a function that
  returns `&local` has `Dead(local)` before `Return` and the `Return` origin is the tail.
- Do: the rules of the sections above. A construct that a later stage handles returns
  `Unsupported(construct)` from the builder (no panic). `weft ir` prints the bodies of a
  file or of one function.
- Gate: the common gates.
- Exit: the golden tests pass; the builder is total (no panic) on the corpus: each body
  builds or is `Unsupported`.

#### B4 Builder: places, dereferences, borrows, assignments

- Depends on: B3.
- Read: `ir §5.6`, §5.7, §5.8, §5.9, §5.32.
- Goal: every place form.
- Files: `crates/weft-sema/src/irbuild/place.rs`, `irbuild/expr.rs`,
  `crates/weft-sema/tests/ir_golden/{places,deref_rc_box,index_bounds,compound,borrow_value,assign_through}.wf`
  with `.ir`.
- Tests first: golden files for: `r.f` through a reference, a `Box` and an `Rc`; `v[i]`
  with `Bounds`; `&v[]`; `&value` into a `Borrowed` temporary; `p.f = v` (value first);
  `(*r).f = v` with `Drop` only for a maybe-linear old value (V17); `x += v` on a
  reference local writes through it; a place in statement position is a `Mention`.
- Do: apply the THIR `adjust` entries as `Deref` projections; splits get one `SplitId`
  for each call and parameter.
- Gate: the common gates.
- Exit: the golden tests pass; each body verifies.

#### B5 Builder: `if`, `match`, patterns, `Uninit`

- Depends on: B4.
- Read: `ir §5.12`, §5.13, §5.3 (patterns), §5.17 (place fields).
- Goal: branches, short circuits, `match` and patterns.
- Files: `crates/weft-sema/src/irbuild/branch.rs`, `irbuild/pattern.rs`,
  `irbuild/unset.rs` (the place fields of a full type, keyed by the full type with a
  visited set), golden files `{if_tail,and_or,match_bind,match_ref,let_tuple,linear_destructure,wild_part,place_fields,match_literals,match_nested,match_string}.wf`.
- Tests first: golden files; a recursive and a polymorphic type with place fields end
  (the R3a review item on `place_paths`); `match` on `(*r)` binds by reference; `_` over a
  linear part is a move into a temporary and its `Dead`; a variant with no payload of a
  linear scrutinee is a `Consume`; integer, bool, unit and string literal patterns and
  nested tuple and variant patterns test in pre-order, the first arm that matches wins,
  and no binding or move comes before the last test of its arm (`ir §5.13`).
- Do: the rules of the sections above.
- Gate: the common gates.
- Exit: the golden tests pass; each body verifies.

#### B6 Builder: loops and jumps

- Depends on: B5.
- Read: `ir §5.14`, §5.1.5, §5.15.
- Goal: `while`, `loop`, `for`, `break`, `continue`, `return` across scopes, W0315.
- Files: `crates/weft-sema/src/irbuild/looping.rs`, `irbuild/frame.rs`, golden files
  `{while_cond,for_elems,for_range,break_nested_block,continue_temps,return_in_arg,loop_tail_temp,break_in_closure}.wf`
  (the grammar has no `break` with a value: `break_nested_block` breaks from a block inside
  the loop with live temporaries; `break_in_closure` is W0111 from `typeck`).
- Tests first: golden files; a `return` in a later argument ends the earlier argument
  temporaries (OL-3c); the tail temporaries of a loop body end at each iteration; a jump
  out of a handled body is W0315 from the builder (with a test once B10 exists; here the
  fence logic with a closure body).
- Do: the rules of the sections above; the back edge is a `Goto` to the head.
- Gate: the common gates.
- Exit: the golden tests pass; each body verifies.

#### B7 Builder: calls, methods, aggregates, `print`, `assert`, performs through the row

- Depends on: B6.
- Read: `ir §5.17` to §5.20, §5.26 (the `Row` case), §5.33, §5.34, §5.1.8.
- Goal: every call form of group A.
- Files: `crates/weft-sema/src/irbuild/call.rs`, `irbuild/aggregate.rs`,
  `irbuild/caps.rs` (capability environments), golden files
  `{call_args,named_args,method_ref,method_value,struct_lit,positional,vec_lit,array_lit,print_borrow,interp_borrow,duration_lit,trailing_block,perform_path,assert,perform_row,generic_extern}.wf`.
- Tests first: golden files; named arguments in parameter order (from the THIR); a
  method receiver read after the arguments; a struct literal in written order with the
  aggregate in field order; `print` and an interpolation `{v}` of a non-plain value
  borrow it; `2.s` is a `Const::Duration`; `[a, b]` is a `Vec` aggregate, or an `Array`
  one with an array type; a trailing block is a closure argument; `Log.info(m)` is a
  perform; `assert` has an `unwind` block (an empty chain until B8); `Box.new(S { .. })`
  marks `in_place`.
- Do: the rules of the sections above; each call passes `CapArgs::Lexical`.
- Gate: the common gates.
- Exit: the golden tests pass; each body verifies.

#### B8 Builder: cleanup chains

- Depends on: B7.
- Read: `ir §5.1.6`, §5.28, §4 (V10, V16).
- Goal: the cleanup chain of each terminator with `can_abort()`.
- Files: `crates/weft-sema/src/irbuild/cleanup.rs` (chains, shared suffixes, actions from
  types), golden files `{abort_chain,on_abort_value,linear_parts,scope_value_chain,temps_in_chain}.wf`.
- Tests first: golden files; the order of a chain (`_0` first, only after its
  assignment, then temporaries newest first, locals from the highest index, then the
  parameters); a type with
  `on abort` gets `OnAbort(f)`; a linear part with no `on abort` gets `Fault`; two chains
  with one suffix share its blocks; V10 and V16 hold.
- Do: the rules of the sections above.
- Gate: the common gates.
- Exit: the golden tests pass; each body verifies.

#### B9 Builder: closures and function values (rule CAPTURE)

- Depends on: B8.
- Read: `ir §5.1.7`, §5.21, §5.22, §5.23, §5.35.
- Goal: closure aggregates, closure bodies, calls of function values, items as values.
- Files: `crates/weft-sema/src/irbuild/closure.rs` (`capture_mode`),
  `irbuild/call.rs`, golden files
  `{closure_ref,closure_move,closure_kept_counter,closure_borrow_plain,closure_nested_move,fn_value_call,item_value,once_closure}.wf`
  (with `SCRATCH/ir/judge_sound/j5d_maker_borrow.wf` and `j5b_kept_write.wf`).
- Tests first: golden files; rule CAPTURE: `|| count += 1` is `Kept`, `|| print(norm(&p))`
  is `ByRef`, a moved capture is `ByMove`, an inner move makes the outer closure move;
  V13 holds; a `once` closure is moved at its call.
- Do: the rules of the sections above; one `ClosureDecl` for each literal.
- Gate: the common gates.
- Exit: the golden tests pass; each body verifies.

#### B10 Builder: `handle`, clauses, `resume`, upvars

- Depends on: B9.
- Read: `ir §5.24`, §5.25, §5.26, §5.27, §5.1.7 (upvars), §5.1.8.
- Goal: handlers as bodies with upvar locals.
- Files: `crates/weft-sema/src/irbuild/handle.rs`, `irbuild/upvar.rs`,
  `irbuild/caps.rs`, golden files
  `{handle_value,clause_resume,clause_no_resume,multi_tail_upvar,perform_local,resume_closure,cont_field,nested_handle}.wf`
  (with the M3 probe).
- Tests first: golden files; the M3 program gives the IR of `ir §5.37`; an upvar local
  has no `Live` or `Dead` (V14); a clause chain starts with `UnwindKont` (V16); a perform
  inside a closure in a handled body names the `Cap` field of the environment; `Row(E)`
  in a clause for an effect of the caller (V11); W0315 for `return` in a handled body.
- Do: the rules of the sections above.
- Gate: the common gates.
- Exit: the golden tests pass; each body verifies.

#### B11 Builder: tasks, `sim.run`, `with_timeout`

- Depends on: B10.
- Read: `ir §5.29`, §5.30, §5.31.
- Goal: the last constructs.
- Files: `crates/weft-sema/src/irbuild/task.rs`, golden files
  `{scope_wait,spawn_handle,spawn_stmt_result,join,detach,fork,sim_run,with_timeout}.wf`.
- Tests first: golden files; a spawn in statement position gives a `TaskResult` local of
  the scope body that `ScopeWait` fills; `_0` of a scope body is in the chain of
  `ScopeWait`; the `ScopeCap` local is finished on the chain (cancel and join).
- Do: the rules of the sections above.
- Gate: the common gates.
- Exit: the golden tests pass; no construct returns `Unsupported` any more.

#### B12 Builder total on the gate; golden IR of the corpus

- Depends on: B11.
- Read: `ir §5.1.9`, §4.
- Goal: the builder works on every program of the gate.
- Files: `crates/weft-gate/src/main.rs` (an `ir-build` subcommand),
  `crates/weft-sema/tests/ir_build_corpus.rs`, `crates/weft-sema/tests/ir_corpus/*.ir`
  (the IR of each corpus program, reviewed), `crates/weft-cli/tests/limits.rs`.
- Tests first: `ir_build_corpus.rs` builds and verifies each tier-1 program and compares
  the corpus programs with their `.ir` files (`UPDATE_IR=1` rewrites them);
  `limits.rs` builds the IR of its largest programs on a 2 MiB thread.
- Do: run `ir-build --tier 2`; fix each panic and each broken rule (bugs of the builder).
  Review the golden IR of ten corpus programs by hand against `ir §5` and record the
  review in the commit message.
- Gate: the common gates; tier 2 `ir-build` with no panic and no broken rule.
- Exit: the builder is total and the verifier is clean on tiers 1 and 2.

### Phase I: the interpreter runs the IR

The AST compiler (`compile.rs`) stays the default and stays as the differential oracle
until stage R4. `--engine=ir` falls back to the AST compiler for a program with a
construct that `compile_ir` does not handle yet, and says so.

#### I1 `compile_ir` core and `--engine`

- Depends on: B12.
- Read: `ir §8.1`, §8.4, §5.1.1 (choice A), §5.1.2 (loop tail temporaries).
- Goal: the interpreter runs the IR of group A and B programs.
- Files: `crates/weft-interp/src/compile_ir.rs` (new), `crates/weft-interp/src/code.rs`
  (new ops `Deref`, `Len`, `Tag`, `JumpTable`, `Bounds`, `DropPlace`, `Consume`,
  `EndTemp`),
  `crates/weft-interp/src/machine/exec.rs` (the new ops), `crates/weft-interp/src/lib.rs`
  (`RunOptions::engine: Engine { Ast, Ir }`), `crates/weft-cli/src/lib.rs`
  (`--engine=ast|ir` for `run` and `test`), `crates/weft-interp/tests/compile_ir.rs`,
  `crates/weft-interp/tests/semantics.rs` (one test for each new op).
- Tests first: each of the 42 interpreter programs that uses only groups A and B gives
  its `.out` with `--engine=ir`, except the expected changes; `x + { x = 5; 1 }` prints 2
  with `ir` and 6 with `ast`; a loop tail temporary ends at each iteration
  (`SCRATCH/ir/probes/p24_loop_tail_temp.wf` with `Weak.upgrade`); each new op has a unit
  test.
- Do: the table of `ir §8.1` for slots, temporary cells (`EndTemp`), `Live`, `Dead`,
  `Assign`, operands, places with `Deref`, `Binary` with `CheckInt`, `Unary`, `Concat`
  with `ToStr`, aggregates, `Switch`, `Iter` and `IterNext`, calls of items, `Print`,
  `Assert`, `Return`, back edges with `BackEdge`. Each op carries its IR location. The
  interpreter still unwinds with `frame_values` (landing pads come in I6); IR temporaries
  are temporary cells, so `frame_values` keeps the order of today.
- Gate: the common gates; `tests/gate/oracle-ast.tsv` is regenerated (rule 3) and no
  verdict of the `ast` engine changes.
- Exit: the tests pass; the AST engine is unchanged.

#### I2 `compile_ir`: closures and function values

- Depends on: I1.
- Read: `ir §8.1` (closures), §5.1.7, §5.22.
- Goal: group C programs run with `--engine=ir`.
- Files: `crates/weft-interp/src/compile_ir.rs`, `crates/weft-interp/tests/compile_ir.rs`.
- Tests first: the interpreter programs with closures give their `.out`
  (`capture_by_value.wf` among them); a `Kept` counter closure shares its cell with the
  maker; a `ByRef` capture reads the new value of the variable; a `ByMove` capture moves
  when the closure is made; `--oracle` faults on `SCRATCH/ir/judge_sound/j5d_maker_borrow.wf`
  (the borrowed cell ended) with both engines.
- Do: `MakeClosure` with the shared cells of the `Kept` operands and the owned list of
  the `ByMove` operands (the moved values) and the `ByRef` operands (the references that
  `&x` made, so that `(*env.k)` reads through a reference and the oracle sees a read after
  the end of `x`); `CallValue`; `Const::Fn` values. The capture decision comes from the
  IR, not from `FnFacts::by_value`.
- Gate: the common gates.
- Exit: the tests pass.

#### I3 `compile_ir`: handlers and continuations

- Depends on: I2.
- Read: `ir §8.1` (upvars, `Handle`, `Perform`, `Resume`), §5.24 to §5.27.
- Goal: group D programs run with `--engine=ir`.
- Files: `crates/weft-interp/src/compile_ir.rs`, `crates/weft-interp/tests/compile_ir.rs`.
- Tests first: the interpreter programs with handlers give their `.out`
  (`effects_log.wf`, `abort_on_abort.wf` and the others with `handle`); an upvar local is
  the captured cell of the site; a move of an upvar local in a handled body moves the
  site local; a `multi` resume copies the cells of the handled body and shares the site
  cells (`SCRATCH/ir/judge_sound/j4_multi_outer_ref.wf` faults under `--oracle` with both
  engines).
- Do: `HandleBody` and `Clause` code units with the cells of their upvar locals;
  `Perform` (the machine still finds the handler; a debug assertion checks that it is the
  one of the `CapOperand`); `Resume` as `CallValue` of the continuation.
- Gate: the common gates.
- Exit: the tests pass.

#### I4 `compile_ir`: tasks, `sim.run`, `with_timeout`

- Depends on: I3.
- Read: `ir §8.1`, §5.29 to §5.31.
- Goal: every program runs with `--engine=ir`; no fallback is left.
- Files: `crates/weft-interp/src/compile_ir.rs`, `crates/weft-interp/tests/compile_ir.rs`.
- Tests first: all 42 interpreter programs give their `.out` with `--engine=ir` (or an
  expected change listed in the test); `crates/weft-interp/tests/determinism.rs` and
  `stress.rs` pass with `--engine=ir`.
- Do: `ScopeBody` with `ScopeWait`, the spawn, join and detach natives with operands,
  `Fork`, `sim.run` and `with_timeout`. Remove the fallback of `--engine=ir`.
- Gate: the common gates.
- Exit: the tests pass with both engines.

#### I5 Engine differential, parity D1, IR oracle cache

- Depends on: I4, G4.
- Read: `ir §8.3`, §8.5 (engine differential, D1).
- Goal: the two engines differ only where `ir §8.3` says, and the gate has the oracle of
  the IR engine.
- Files: `crates/weft-gate/src/engines.rs` (the `engines` subcommand),
  `crates/weft-gate/tests/engines.rs`, `crates/weft-sema/tests/exports_parity.rs` (D1),
  `tests/gate/oracle-ir.tsv`, `tests/gate/ledger.toml` (class `engine` entries).
- Tests first: D1: on tier 1, the `ByMove` captures of the IR equal `FnFacts::by_value`,
  and each other difference is a `Kept`-versus-`ByRef` case of rule CAPTURE; the argument
  order of each IR call equals `FnFacts::arg_order`; the `IntTy` of each `Binary` equals
  `FnFacts::int_ops`. `engines --tier 1` reports no unledgered difference.
- Do: `engines --tier N` runs both engines with `--oracle` and the six configurations on
  each runnable program and compares the output, the exit status and the kind and line of
  each fault. Ledger each expected difference with its class: `choice-a`, `loop-temps`,
  `capture`, and `unwind-order` for a value of `_0` that unwinds after the locals before
  I6 (the shapes of F3-7, `ir §8.3`). Build `oracle --engine ir` for tier 1 (committed) and tier 2 (cache). From
  this stage on, the gate classifies the `ir` pipeline with the `ir` oracle.
- Gate: the common gates; tier 2 `engines`.
- Exit: no unledgered engine difference on tiers 1 and 2; the IR oracle cache exists.

#### I6 Landing pads and the unwind order

- Depends on: I5.
- Read: `ir §8.2`, §5.1.6, §8.3 (unwind order).
- Goal: the unwinder runs the cleanup chains of the IR.
- Files: `crates/weft-interp/src/compile_ir.rs` (a landing-pad table for each `Code`),
  `crates/weft-interp/src/code.rs` (unwind-mode ops), `crates/weft-interp/src/machine/effects.rs`
  (`unwind_frame` runs the chain for an IR frame; `frame_values` stays as a check),
  `crates/weft-interp/src/oracle.rs` (the check: no live linear value is left after a
  chain), `crates/weft-interp/tests/compile_ir.rs`.
- Tests first: `SCRATCH/ir/probes/p18_abort_order.wf` keeps the order of today with
  `ir`; `p20_clause_unwind_order.wf` prints the continuation value first with `ir` (the
  model order); a value of a scope body in `_0` with `on abort` is finished when
  `ScopeWait` aborts; the oracle check finds a hand-made chain that misses a value.
- Do: the rules of `ir §8.2`. Ledger the order change of a clause (class
  `unwind-order`), and remove the `unwind-order` entries of I5 for `_0`: the chain finishes
  `_0` first, as the AST engine does. Recompute the IR oracle cache (the interpreter
  changed).
- Gate: the common gates; tier 2 `engines` and `oracle --engine ir`.
- Exit: no unledgered engine difference; the frame-scan check finds nothing on tiers 1
  and 2.

### Phase F: analysis, summaries and facts

The new fact generator lives in `crates/weft-sema/src/analysis/` and
`crates/weft-sema/src/factgen/` (`ir §1.4`). It writes `FnFacts` with the schema of
today, so the checker, the spec, the bridge and `diagnose.rs` read both pipelines. A
construct group turns on only at the stage that says "group X on"; before that, its code
runs only in unit tests and in the preview report of the gate (`run --groups ABC...`
with the group forced on, report only).

#### F1 `--facts=old|ir|both`, scope, fallback

- Depends on: B12, G5.
- Read: this plan §2.6; `ir §1.3`.
- Goal: the switch between the pipelines, with a fallback for each program.
- Files: `crates/weft-sema/src/lib.rs` (`Options::facts: FactGen { Old, Ir, Both }`,
  `Options::ir_groups: Groups`, `Analysis::ir_facts` for `Both`),
  `crates/weft-sema/src/irbuild/scope.rs` (the groups of each body),
  `crates/weft-sema/src/factgen/mod.rs` (a stub `emit` that returns
  `Unsupported(group)`), `crates/weft-cli/src/lib.rs` (`--facts` for `check`, `facts`,
  `agree`, `lint`, `run`, `test`), `crates/weft-gate/src/snapshot.rs` (`--facts=ir`),
  `crates/weft-sema/tests/scope.rs`.
- Tests first: the groups of small programs (one for each group, and mixed ones); a
  program out of scope uses the old pipeline and `check --facts=ir` prints the note;
  `--facts=both` returns both fact sets; with the stub, every program is out of scope, and
  the gate reports 0 % coverage and all `same`; with a test hook that puts a program in
  scope and an empty emit, a W0313 of the old lowering goes away and a W01xx of the old
  lowering stays (`ir §2.4`).
- Do: the dispatch in `analyze`; the scope test reads the IR of each body. The IR
  pipeline also fills the span-keyed exports from the IR (capture modes, argument order,
  integer types), so `--engine=ast` can run an IR-checked program. Until R2 the old
  lowering runs in `ir` mode too, because it records the THIR: the `ir` mode keeps only
  its `typeck` diagnostics (`ir §2.4`) and drops its other diagnostics and its facts. The
  cost criterion of §2.7 counts the old lowering in the `ir` time.
- Gate: the common gates.
- Exit: the tests pass; the gate runs with `--facts=ir` and shows the coverage.

#### F2 Fact generator skeleton: nodes, roots, α, variables, `RELS`

- Depends on: F1.
- Read: `ir §6.1`, §6.2, §6.3, §6.7 (`RELS`); the sketch `facts.rs` and `rels.rs`.
- Goal: the parts of the fact generator that do not need the analysis.
- Files: `crates/weft-sema/src/factgen/nodes.rs` (`NodeKey`, `Phase`, the node table,
  the edges of blocks and phases), `factgen/alpha.rs` (roots and α for projections that
  need no abstract value), `factgen/vars.rs` (the `S`, `H`, `U`, `C` variables and their
  flags), `factgen/rels.rs` (the `Rel` enum, `row_of`, the spec input list from
  `include_str!("../../../../spec/weft.dl")`), `crates/weft-sema/tests/factgen_units.rs`.
- Tests first: `rels`: each input relation of the spec has a row (the sketch tests
  `rows_match_the_spec` and `each_node_relation_has_a_part_or_a_reason`); a test that
  destructures `weft_facts::FnFacts` field by field (as `FnFacts::mark` does) and maps each
  relation field to a `Rel`; `nodes`: the phases of each terminator in the order of
  `ir §6.2`; `alpha`: α of `Field`, `Variant`, `Index` of a `Vec` and of an array,
  `Elems`, `Split`, `Deref(Box)`, `Deref(Rc)` (the group root and the handle place).
- Do: the code of the sections above. `alpha` returns an error for `Deref(Ref)` of a
  move path until F3 gives abstract values.
- Gate: the common gates.
- Exit: the tests pass.

#### F3 Analysis: domain and transfer (straight-line)

- Depends on: F2.
- Read: `ir §6.6` (domain, transfer, joins), §6.3 (α of `Deref(Ref)`).
- Goal: the abstract values for group A bodies with no calls.
- Files: `crates/weft-sema/src/analysis/mod.rs` (the driver: a worklist over blocks in
  reverse post-order), `analysis/domain.rs` (`AbsVal`, `State`, joins),
  `analysis/transfer.rs` (one function for each statement kind and for `Switch`, `Goto`,
  `Return`), `crates/weft-sema/tests/analysis_units.rs`.
- Tests first: on hand-built IR: `Ref(q)` gives `refs = α(q)`; `Use(copy r)` of a
  reference copies its places; an aggregate keeps the structure of the move paths (a
  tuple of two references, a struct field); a join is a union of the may parts and an
  intersection of the must parts; `uniq` is the meet; `empty` for `None`; α of
  `Deref(Ref)` reads the state.
- Do: the transfer functions of the statements; the per-body fixpoint (no loops yet:
  the worklist is in place, widening comes in F10).
- Gate: the common gates.
- Exit: the tests pass.

#### F4 Templates: statements, simple terminators, operands

- Depends on: F3.
- Read: `ir §6.4` (operands, statements, `Switch`, `Return`), §6.3 (variables).
- Goal: the facts of bodies with no calls.
- Files: `crates/weft-sema/src/factgen/templates.rs`, `factgen/kernel.rs` (the
  reference-fragment rules as pure functions: `Ref`, `Copy` of a reference, reads and
  writes through a reference), `factgen/mod.rs` (`emit` for bodies with no `Call`,
  `Perform` or `Resume`), `crates/weft-sema/tests/factgen_units.rs`.
- Tests first: for each statement kind, the facts of a one-statement body (a table
  test against `ir §6.4`); `Dead` always emits `scope_end` (also for a value that is not
  plain data) and `unwound_at` on a cleanup path; `Return` uses `_0`; a part move emits
  `moved_at` of the whole local, `moved_part` and `rest_linear` (the R3a encoding); a
  `Drop` behind a reference emits a drop pair that ends at the `Assign`; `print` of a
  reference reads through it; the first value after `Live` writes nothing and an
  overwrite of a source local is `mutates_at` of its root (`ir §6.4`); a new value of a
  part with an `H` variable replaces the places of the part, and `S(l)` does not hold
  them (R3RT10, `ir §6.3`); the relations of `ir §6.3` "Relations with no node" come from
  the declarations (a table test for `shared_root`, `declared_mut`, `has_signature`,
  `task`, `fork_task`, `library`, `started`, `no_runtime`, `std_effect`).
- Do: the templates; one function for each statement kind; no other code emits node
  facts.
- Gate: the common gates; `weft agree --facts=ir` on the call-free bodies of the corpus
  (a forced preview of group A without calls).
- Exit: the tests pass; agreement holds on the preview.

#### F5 Summaries: type, signatures, `apply` at calls

- Depends on: F4.
- Read: `ir §6.7` (interface roots, parts, kinds of run node), §6.4 (`Call`, `Ret`,
  `FrameEnd`), §6.3 (the callee frame root).
- Goal: calls of items whose summary comes from a signature.
- Files: `crates/weft-sema/src/analysis/summary.rs` (the `Summary` type with the parts
  of `ir §6.7`, interface roots, places cut at 8 steps), `analysis/sig.rs`
  (`from_signature`: a summary from a stated signature or an extern function: `mut`
  places, `in` places, the row, `drops`, `holds`; a `mut` place gets the held references
  of the other arguments only where its type can hold a reference to their pointee type,
  R3RT6), `analysis/apply.rs` (`apply(Σ, σ, n,
  kind)` for the parts `muts`, `reads`, `frees`, `lends`, `performs`, `aborts`, `ret`,
  `drops`, `holds`, `uniq_needs`, `only_self`), `factgen/templates.rs` (the `Call` phases
  `Main`, `Ret`, `FrameEnd`; the call checks `call_arg`, `call_mut`, `arg_at`, `param_in`,
  `uniq_param`, `arg_aliased`, `fn_arg_effect`, `param_effect`, `writes_via` at a method
  call), `crates/weft-sema/tests/analysis_units.rs`.
- Tests first: `Vec.new`, `push`, `len`, `clear` from their prelude signatures give the
  facts of today at a call (compare the digest with the old pipeline on
  `tests/programs/02_bad.wf`); a held argument moves at `Ret`; the result binds at `Ret`;
  a callee frame place in a result ends at `FrameEnd`; `writes_via` at `v.push(x)` with
  `v` one reference.
- Do: the code above. `RELS` decides which part each relation of the callee goes to.
- Gate: the common gates.
- Exit: the tests pass.

#### F6 `summarize`, the call-graph fixpoint, effect inference

- Depends on: F5.
- Read: `ir §6.6` (interprocedural order), §6.7 (`summarize`, an operation of a caller,
  code of a caller), §6.8.
- Goal: user functions get their summaries from their bodies; effect inference runs over
  the IR.
- Files: `crates/weft-sema/src/analysis/summarize.rs` (the projection of the facts of a
  body onto its interface, by `RELS`), `analysis/callgraph.rs` (the graph of "reads the
  summary of", SCCs callees first, monotone iteration, the W0706 guard),
  `analysis/unknown.rs` (an operation of a caller: the caller frame root, map N1),
  `analysis/sig.rs` (`to_effect_sig`), `crates/weft-sema/src/lib.rs` (the IR pipeline
  uses this fixpoint instead of `infer.rs` re-lowering), `crates/weft-gate/src/sigdiff.rs`
  (the gate compares `to_effect_sig` with the `EffectSig` of the old pipeline for each
  function of an in-scope program), `crates/weft-sema/tests/analysis_units.rs`.
- Tests first: a recursive pair of functions reaches a fixpoint; a row that only grows;
  a perform through `Row(E)` gives `escapes_at` and a result that points into the
  argument places and the caller frame root (`SCRATCH/ir/work/map/opres.wf`); the
  `EffectSig` projection of the corpus functions of group A equals the old one, or the
  difference is ledgered (class `sig`).
- Do: the code above; `to_effect_sig` feeds W0701, `weft deps` and `pins`.
- Gate: the common gates; the signature diff on tier 1 (preview of group A).
- Exit: the tests pass; each signature difference on tier 1 has a ledger entry.

#### F7 Aborts past the function; `on abort`

- Depends on: F6.
- Read: `ir §6.5` (abort destinations, cleanup copies, `spared_at`), §6.4 (`UnwindValue`,
  `Assert`), §5.28, §6.9 (W0118).
- Goal: abort paths to the caller, with their cleanup copies.
- Files: `crates/weft-sema/src/factgen/frames.rs` (destinations, cleanup copies for each
  destination with `NodeKey::dest`, `FrameEnd(d)`), `factgen/templates.rs`
  (`UnwindValue`, `Assert`, `may_abort`), `analysis/apply.rs` (`RunKind::OnAbort`),
  `factgen/checks.rs` (W0118 as a query over the summary of the `on abort` function),
  `crates/weft-sema/tests/factgen_units.rs`.
- Tests first: a call whose callee can fail keeps its abort edge and `may_abort`; a call
  whose callee cannot abort has no abort edge; `assert` aborts (`SCRATCH/ir/probes/p25_assert_abort.wf`,
  `p27_assert_callee.wf`: W0602); `unwound_at` only on the cleanup nodes; an `on abort`
  function that changes a place through a reference in its value is W0118 and its change
  shows at the caller (F3-1); a child failure at `ScopeWait`, `Join` and `Fork` inside a
  local `handle Fail` aborts to that handler (with its `AbortValue`), and with no local
  handler past the function; a cancel aborts past the function (`ir §6.5`).
- Do: the code above.
- Gate: the common gates.
- Exit: the tests pass.

#### F8 Group A on

- Depends on: F7, I5.
- Read: this plan §2.5 to §2.7; `ir §6.9` (diagnostics), §10.
- Goal: the new pipeline is the one that checks group-A programs in the gate.
- Files: `crates/weft-sema/src/lib.rs` (group A in the default `ir_groups`),
  `crates/weft-check/src/diagnose.rs` (W0204 for `error(_0, Return)` of a function or a
  closure at the span of the `Return` origin; W0301 with "the value leaves after its place
  ends" in a handled body, a scope body or a clause; names of temporaries from `TempKind`
  and `Origin`),
  `crates/weft-check/tests/programs_ir.rs` (the corpus markers with `--facts=ir` on the
  programs in scope; a moved marker needs a ledger entry),
  `crates/weft-check/tests/hypotheses.rs` (the lints on each component in IR mode),
  `tests/gate/ledger.toml`, `tests/gate/claims.toml` (the group-A claims are on).
- Tests first: `programs_ir.rs` and the claims of group A (TEMP, TAIL, DROP, ORDER,
  ACCESS, DEREF, CALLS findings; semantics N1 to N4; map N1); W0204 on
  `tests/programs/95_stated_refs.wf` and the local forms keep their lines.
- Do: run tier 1 and tier 2 on the group-A scope; fix each `crash`, `lost-fault` and each
  `open` program that a group-A claim covers; ledger each other difference with its reason
  and finding id; review the `lost-clean` entries with a second agent and sign them.
  Follow-ups `F8.k` for groups of differences that do not fit the box (rule 5).
- Gate: the common gates; the common exit; tier 2.
- Exit: the common exit on the group-A scope.

#### F9 Fact oracle and trace conformance

- Depends on: F8, I6.
- Read: `ir §8.5` (trace conformance, fact oracle).
- Goal: the run-time checks of the B6 hypotheses on every accepted program.
- Files: `crates/weft-interp/src/oracle.rs` (the cell-to-root map; the checks C1, C4, C5,
  F4, D1, D4), `crates/weft-interp/src/lib.rs` (`RunOptions::fact_oracle`,
  `--ir-trace`), `crates/weft-sema/src/factgen/mod.rs` (the map from IR locations to fact
  nodes for each component), `crates/weft-gate/src/oracle.rs` (the `fact-oracle` and
  `trace` checks for each accepted program of the scope), `crates/weft-interp/tests/fact_oracle.rs`.
- Tests first: a hand-broken fact set (a `scope_end` removed, a `points_into` removed, an
  edge removed) makes the fact oracle or trace conformance fail on a small program; the
  corpus programs with `main` pass.
- Do: the checks of `ir §8.5`. Run them on the group-A scope of tiers 1 and 2; each
  failure is a defect of the fact generator: fix it, and add its program to
  `tests/gate/probes/fixes/`.
- Gate: the common gates; the common exit.
- Exit: no fact-oracle and no trace failure on the group-A scope.

#### F10 Group B on: loops

- Depends on: F9.
- Read: `ir §6.6` (widening, one-place instances), §5.14, §6.4 (`IterNext`).
- Goal: loops in the new pipeline.
- Files: `crates/weft-sema/src/analysis/widen.rs` (the rules of `ir §6.6`),
  `analysis/mod.rs` (loop heads, back edges), `factgen/alpha.rs` (one-place instances
  off on cycles), `factgen/templates.rs` (`IterNext`), `crates/weft-sema/tests/analysis_units.rs`,
  `crates/weft-sema/src/lib.rs` (group B in the default set).
- Tests first: the loop programs of the corpus that guard precision
  (`tests/programs/35_wild_places.wf`, `102_wild_instances.wf`, `103_wild_lend.wf`)
  keep their markers; a loop that grows a place deeper than 8 steps widens and ends; RR1,
  V025, V041 repros of the claims file are rejected; `scale.rs` stays linear on a long
  loop chain.
- Do: the code above. W0707 is not reported by the IR pipeline.
- Gate: the common gates; the common exit; tier 2.
- Exit: the common exit on the scope of groups A and B.

#### F11 Closures (group C, part 1)

- Depends on: F10.
- Read: `ir §6.1`, §6.3 (cell roots, `Arg` roots), §6.5 (the entry of a component,
  instantiation), §6.7 (`Call` of a closure value; `CaptureCell`, `Capture`; `uses`,
  `moves`), §5.1.7, §5.22.
- Goal: closure components and calls of closures that the body knows.
- Files: `crates/weft-sema/src/analysis/transfer.rs` (the closure aggregate value),
  `analysis/summarize.rs` (closure summaries in interface terms; the `rebinds` part),
  `analysis/apply.rs`
  (`Call` of a known closure: σ maps `ByRef` captures to the current value of the
  variable), `factgen/instantiate.rs` (the `Arg` roots of a component become the union
  of their actuals, or `a place of a caller`), `factgen/vars.rs` (`C(x)` cell variables),
  `factgen/templates.rs` (`moved_at` of a `once` callee),
  `crates/weft-sema/tests/factgen_units.rs`.
- Tests first: RR7 (a closure reads the new value of a captured reference) and V103 are
  W0301; O3-11 (move `x`, give `x` a new value, then run a closure that holds `&x`) is
  accepted; a returned `Kept` counter closure is accepted (`d5_count.wf`); J5d is W0204;
  a closure that changes two aliased captures sees the alias (instantiation); a `once`
  closure called twice is W0502; a task closure that writes a `Kept` counter while the
  parent reads it is W0405 (σ maps the `Kept` field to the root of the variable); F3-11
  (`r3/fidelity/repro/F3-11_closure_rebind.wf`) is accepted (the `rebinds` part) and a
  closure that gives the capture a new value on one path only is not; R3RT5 is accepted.
- Do: the code above. Group C stays off; run the gate preview with group C forced on and
  record the report.
- Gate: the common gates.
- Exit: the tests pass.

#### F12 Function values (group C, part 2)

- Depends on: F11.
- Read: `ir §6.6` (function sets), §6.7 (`ret` with closures, code of a caller, `runs`
  and `Many`), §5.21, §5.23, §5.35.
- Goal: function values through locals, fields, tuples, returns and parameters.
- Files: `crates/weft-sema/src/analysis/domain.rs` (function sets with widening to
  `Unknown`), `analysis/unknown.rs` (code of a caller: `lends_mut` of the reachable
  places, the caller frame root, map N2), `analysis/summarize.rs` (`ret` with closures in
  interface terms; `runs` with `Once` or `Many`), `analysis/apply.rs` (a second `apply` at
  `Ret` for `Many`; an item value with type arguments), `factgen/checks.rs` (the summary
  check of a value that a caller can run, `check_item_value` of today),
  `crates/weft-sema/tests/analysis_units.rs`.
- Tests first: RT6, RT7, RR2, V107 (a function value through a tuple, an `if`, a field,
  a return) apply the right summary; OR3 (a callee runs a callback twice) is W0301;
  `SCRATCH/ir/work/map/fnres2.wf` (map N2) is rejected; a function parameter call lends
  the argument places; the Q3-2 repros (`r3/quality/repro/Q3_closure_chain_22.wf`,
  `Q3_closure_dag_18.wf`) check in less than one second in a release build (each closure
  summary is computed once).
- Do: the code above.
- Gate: the common gates.
- Exit: the tests pass.

#### F13 Stored values and the summary oracle; group C on

- Depends on: F12.
- Read: `ir §6.6` (heap slots), §6.7 (`stores`, `reaches`, stored values), §6.9 (W0204
  store forms), §8.5 (summary oracle).
- Goal: closures stored behind references, in boxes, vectors and `rc` objects; the
  summary oracle; group C on.
- Files: `crates/weft-sema/src/analysis/heap.rs` (heap slots, cut at a fixed depth),
  `analysis/summarize.rs` (`stores`, `reaches`), `analysis/apply.rs` (a node of unknown
  code runs each value in a reachable heap slot), `factgen/vars.rs` (heap slot
  variables), `factgen/checks.rs` (the W0204 store check over `stores` of every body),
  `crates/weft-interp/src/oracle.rs` (the summary oracle), `crates/weft-gate/src/oracle.rs`,
  `crates/weft-sema/src/lib.rs` (group C in the default set).
- Tests first: O3-5 (a task runs a closure from a struct field) and OL-1a are W0405 or
  W0301 as the claims say; V037, OL-4a, V087, V108, FD3 (stores behind a parameter or into
  an `rc` object) are W0204; the summary oracle fails on a hand-broken summary (a missing
  `muts` place) and passes on the corpus.
- Do: the code above; then the gate for groups A to C (rules of F8); the summary oracle
  runs on each accepted program of the scope.
- Gate: the common gates; the common exit; tier 2.
- Exit: the common exit on the scope of groups A to C; no summary-oracle failure.

#### F14 Handlers: splice, perform, `Exit`, `Post` (group D, part 1)

- Depends on: F13.
- Read: `ir §6.1` (splices), §6.2, §6.3 (the capability root, `K(h)`), §6.4 (`Handle`,
  `Perform`), §6.5 (the splice), §6.7 (resume points, `pre` and `post`, `Perform` through a
  local handler, `Handle` `Post`), §6.10 (M1, J1, J3).
- Goal: the normal path of a `handle`.
- Files: `crates/weft-sema/src/factgen/frames.rs` (the splice edges, `Exit`, `Post`),
  `analysis/clause.rs` (resume points; the `pre` and `post` parts), `analysis/apply.rs`
  (`Perform` through a local capability applies `pre`; `Post` applies `post` with
  `ResumeResult` mapped to `_0` of the handled body), `analysis/transfer.rs` (the result
  of a perform: the resume values of the clauses), `factgen/templates.rs` (`Handle`
  `Main`, `Exit`, `Post`; `footprint`, `handler`, `clause_performs`, `clause_multi`,
  `body_multi`), `crates/weft-sema/tests/factgen_units.rs`.
- Tests first: M1 (`m1_post_resume.wf`, `postres.wf`), J1, J2 (resume through a
  closure), J3 are W0301; O3-2 is W0301 at `Exit`; a clause parameter maps onto the
  argument places (F3, V035); `m6_resume_result_body_local.wf` and
  `m9_resume_twice_tail.wf` are accepted; O3-7 (one closure argument of an operation) and
  R3RT7 (`in` on an operation parameter: W0203, not W0312) as `ir §10.4` says.
- Do: the code above. Group D stays off; gate preview with D forced on.
- Gate: the common gates.
- Exit: the tests pass.

#### F15 Abort destinations of local handlers (group D, part 2)

- Depends on: F14.
- Read: `ir §6.5` (abort destinations, `AbortValue`, cleanup copies, `spared_at`,
  `Landing`), §6.4 (`AbortValue`, `FrameEnd`), §6.3 (`F(n)`, `K(h)`), §6.10 (M3).
- Goal: aborts to a local handler, with the value of the clause.
- Files: `crates/weft-sema/src/factgen/frames.rs` (destinations for local handlers,
  `AbortValue(h)`, `FrameEnd(h)`, the cleanup copies for `h`, `Landing`, `spared_at`),
  `analysis/clause.rs` (a clause that can end with no resume point; its value),
  `crates/weft-sema/tests/factgen_units.rs`.
- Tests first: M3 (`m8_abort_value_into_body.wf`) and M4 (`m10_abort_value_callee_local.wf`)
  are W0301; J6 and O3-3 stay rejected; a value outside the handled body is spared at a
  perform of a local handler (OR4, OL-R2c-1); no node binds and frees one variable (the
  `gen_kill.dl` lint on the M3 and F3-2 facts; `SCRATCH/ir/judge_sound/m3_machine.dl` and
  `f32_machine.dl` give the expected facts).
- Do: the code above.
- Gate: the common gates.
- Exit: the tests pass.

#### F16 `resume`, continuations, `multi` (group D, part 3)

- Depends on: F15.
- Read: `ir §6.4` (`Resume`), §6.5 (re-entry edges, the `Copy` rule), §6.7 (the
  continuation summary), §6.3 (`R(n)`, the continuation root), §6.10 (O3-14, J4).
- Goal: `resume` and `multi` re-runs, for local handlers and handlers of a caller.
- Files: `crates/weft-sema/src/analysis/cont.rs` (the continuation summary of each
  handler: the rest of the handled body, `ret` = `_0`), `factgen/templates.rs`
  (`Resume` phases; `resumes_at`; `moved_at` of a `once` continuation), `factgen/frames.rs`
  (re-entry edges from `Post` or from the function `Return`; `Copy` rebinds only the
  variables whose places are all in the copied frames; one-place instances off on these
  cycles), `crates/weft-sema/tests/factgen_units.rs`.
- Tests first: M2 (`m6b_resume_result_ref.wf`) is W0301; RR5, V121, R3RT4 as the claims
  say; O3-14 is W0302; J4 stays rejected; OL-R2a (a `multi` operation of a handler of a
  caller) is rejected; V097 (one-place instances on a re-run) as the claim says; W0503
  for a `once` value live across a `multi` point; R3RT4 (a `resume` with a closure
  parameter) is W0301; O3-8 (a closure with its own `multi` handler) is accepted.
- Do: the code above.
- Gate: the common gates.
- Exit: the tests pass.

#### F17 W0313 over roots; group D on

- Depends on: F16.
- Read: `ir §6.9` (W0313 rows), §6.3 (capability and continuation roots).
- Goal: the escape rule of W0313 over the roots of the analysis; group D on.
- Files: `crates/weft-sema/src/factgen/checks.rs` (W0313 for capabilities and
  continuations, with the spans of today), `crates/weft-check/src/diagnose.rs` (an `error`
  whose evidence free is a capability or continuation root folds into the W0313
  diagnostic as a note, with its fact key), `crates/weft-sema/src/lib.rs` (group D in the
  default set), `tests/gate/claims.toml` (group-D claims on).
- Tests first: `tests/programs/62_cap_escape.wf`, `83_kept_values.wf` and
  `122_cont_escape.wf` keep each W0313 marker with `--facts=ir` (also `as_result`,
  `in_tuple`, `in_struct`, `in_closure`, `copies`, `copies_vec`, `takes_out`); RT16, V046,
  V047, RR3, V120 as the claims say; `each_violation_has_one_diagnostic` holds in IR mode.
- Do: the check over the abstract values at the end of each root; then the gate for
  groups A to D (rules of F8), with the fact oracle and the summary oracle.
- Gate: the common gates; the common exit; tier 2.
- Exit: the common exit on the scope of groups A to D.
- As built (three commits; group D goes on in the follow-up F17.1, rule 5): part 0
  fixes the findings of the independent review of group D (the region of the
  continuation of a `resume`, `factgen::handlers::Region`; the resume cover A4 of the
  fact oracle); part 1 is W0313 for a capability over the values of the analysis
  (`clause::Escape`, `factgen::checks::cap_escapes`), the weak update of D-REBIND, W0118
  in IR mode and `each_violation_has_one_diagnostic` in IR mode; part 2 is the hole
  D-CLAUSE-RUNS that the default gate with group D found, the ledger entries of the
  group-D classes, and the claims O3-8 and map-N1 moved to F16.2 and F16.3. W0313 for a
  continuation stays with the old pipeline (a captured continuation is F16.1); corpus 83
  and 122 keep their markers through the fallback. Group D went on in the follow-up
  F17.1, after the second independent review of group D (its findings fixed first, its
  signatures of the twelve `lost-clean` rows in the ledger).

#### F18 Tasks: scopes, spawn, join, detach (group E, part 1)

- Depends on: F17.
- Read: `ir §6.4` (`Scope`, `ScopeWait`, `Spawn`, `Join`, `Detach`), §6.5 (the scope
  splice, the cancel on a scope abort), §6.6 (task sets, must-set), §5.29.
- Goal: tasks in a scope.
- Files: `crates/weft-sema/src/analysis/tasks.rs` (task sets of handles, may and must),
  `factgen/templates.rs` (the task templates; `joined_at` of the scope tasks on the
  cleanup chain of a scope body), `factgen/frames.rs` (the scope splice),
  `analysis/summarize.rs` (the `tasks` part), `crates/weft-sema/tests/factgen_units.rs`.
- Tests first: O3-4 (a spawn statement drops a linear result) is W0601; F3-7 (the value of
  a scope body across `ScopeWait`) is W0602; O3-6 (a task reads through an `Rc` handle;
  the parent moves it) is W0405; V084 (a scope abort cancels and joins) is accepted;
  V096 (the must-set of handle holders) as the claim says; `kept(T, root(x))` for a `Kept`
  capture of a task; O3-9 (joins through a callee, a tuple, an `Option`, `id`, a closure)
  is accepted; the `detach` control of F3-6 has one W0601 and no W0602 (N1 of
  `r3/issues.md`).
- Do: the code above. Group E stays off; gate preview.
- Gate: the common gates.
- Exit: the tests pass.
- As built (group E stays off; the gate with `--groups ABCDE` is a preview):
  `analysis/tasks.rs` runs a scope body from the state before the `scope` (the scope
  body splices into its site: `handlers::splice_root`, `NodeTable::splice_scopes`,
  `Frames::past_scope`), runs a task body at its spawn as a closure run with no
  arguments, and keeps the task sites of each handle (`AbsVal::tasks`, may) with the
  sites whose handles left the values of the component (`State::lost_tasks`: a call
  argument, a store behind a reference, a `detach`, an overwrite, the end of a local).
  A `join` ends each site of its handle that no other value holds and that is not
  lost (`tasks::must_join`, V096). The templates (`templates::spawn`, `join`,
  `scope_wait`, `detach`, `scope_main`, `scope_exit`, `scope_unwind`, `task_ends`)
  give `spawned_at`, `task_reads`/`task_writes` (the changes and reads of the run at
  the spawn, without the places of a caller and the environment of the task),
  `captures`, `mut_through`, `kept` (not for a variable that a captured reference
  points into), `joined_at` at a `join`, at `ScopeWait` and at the `UnwindValue` of
  the `ScopeCap` local (V084), `lends_mut` of the writes of an ended task at the node
  after its end, the later values of a `ByRef` or `Kept` capture, and the drop pair of
  `detach` (one W0601, no W0602). The summary part `joins` (the task handle
  parameters and captures that a body joins on each path to `Return`) ends tasks at a
  call of a callee or a closure (O3-9), and a `Consume` of an empty variant ends the
  tasks that only its value holds. The summary part `pins` replaces the old part.
  Not in scope until F19 (fallback): `fork`, a spawn on a scope that the body does not
  own (in a closure, a clause, a parameter), a task that runs code of a caller or runs
  a value more than once, a task that performs an operation of an enclosing `handle`
  or of a caller (W0314; `Fail` goes to `join` and `ScopeWait`), `sim.run`,
  `with_timeout`. Tests: `crates/weft-check/tests/ir_tasks.rs` (data
  `tests/data/tasks/`), `factgen_units.rs` (kept, the ends of a scope, the must rule,
  part `joins`), and the ignored corpus preview of `programs_ir.rs`. Probes
  `tests/gate/probes/fixes/f18/` with claims (stage F18, off).

#### F19 `fork`, `sim.run`, `with_timeout`, W0314; group E on

- Depends on: F18.
- Read: `ir §6.4` (`Fork`), §5.30, §5.31, §6.7 (`runs` as a task), §6.9 (W0314).
- Goal: the rest of group E; group E on.
- Files: `factgen/templates.rs` (`Fork`; the `sim.run` facts `handler`, `sim_root`,
  `sim_run_at`), `analysis/apply.rs` (`with_timeout` runs its closure once and can
  abort; `runs` as a task: `spawned_at` at `Main`, `joined_at` at `Ret`),
  `factgen/checks.rs` (W0314 over the `tasks` part), `crates/weft-sema/src/lib.rs` (group
  E in the default set).
- Tests first: OR7, V126, V127, V132 (a callee runs an argument as a task) as the claims
  say; the W0314 markers of `122_cont_escape.wf` and the task programs of the corpus stay;
  `sim.run` as a value is W0802 in a library (RT17); IP6 (a `fork` of units gives a
  tuple); I3-8 (a `multi` operation in a scope body after a spawn statement) is W0503;
  O3-10 (two spawns of function parameters) and O3-12 (a clause and its own task) are
  accepted.
- Do: the code above; then the gate for groups A to E (rules of F8).
- Gate: the common gates; the common exit; tier 2.
- Exit: the common exit on the scope of groups A to E.
- As built (group E goes on in a separate last commit, "IR F19: group E on": the
  default groups are A to E, the corpus markers of nine programs get the words
  `old:` and `ir:`, the tier-1 and tier-2 baselines change for the W0405 rule
  below, and the open-old entries O3-5, I3-1 and OL-R2d-box go; fourteen
  tier-1 and five tier-2 `lost-clean` rows wait for an independent signature):
  - `Fork`: the nodes `Main`, one `Task(i)` node for each branch, a `Task`
    node where the branches end, and `Ret` (`nodes::phases_with`). Branch
    `i` starts at its node (`templates::task_start`, the code that a spawn
    and a branch share), so a branch that starts later runs at the same time
    as the branches before it (W0405); each branch is a `fork_task` (W0401,
    W0403); `Ret` binds the tuple of the results (IP6). The abort edge of
    `Main` has no task that runs. A child failure raises past the function
    with no local `Fail` handler (`raises`).
  - `sim.run` and `with_timeout` have summaries (`sig::intrinsic`): they run
    their block once. `with_timeout` performs `Fail` through the row, so a
    local `Fail` handler stops it (5.31). A call of `sim.run` gives
    `sim_run_at`, a root handler of the simulation for each standard effect,
    and no standard effect of the block leaves the call or a node of the
    block (`factgen::sim_blocks`). `sim.run` as a value applies its summary
    (RT17: W0802 at the value).
  - A value that a callee runs as a task (OR7, V126, V127, V132): the summary
    part `runs` has `task` and `TaskHow` (`thread`, `twice`, `with`, the
    places that the callee writes and reads while the task runs;
    `tasks::task_hows` over the facts of the callee). A call of such a
    callee has four `Task` nodes for each such run (`frames::TASK_NODES`):
    the start (the values of the argument apply there as a task of the
    call), a second start (`twice`), the code that runs at the same time
    (`with`, the places of the callee), and the end
    (`templates::call_tasks`). A task of the callee that runs a function
    parameter is `opaque` in the callee, and the body does not pin for it.
    A value that a callee can run as a task in the worst way (a foreign
    function, code of a caller: `TaskHow::foreign`) keeps the fallback of
    stage F18 (group C) when it changes places.
  - A spawn in a closure body or in a clause on a scope of the maker (part
    `tasks`): the node that runs the closure, or the node that runs the part
    of the clause with the spawn (`handlers::project`), starts the task too;
    the scope ends it. A spawn as the value of a closure or a scope gives a
    handle whose discarded temporary drops only the result
    (`vars::spawn_dest`). A scope in a clause splices into the clause
    (`handlers::spliceable`), and so does a `fork`. A task that a closure
    body starts is `opaque` (the facts do not name the captures of a
    closure made in a closure body).
  - W0314 (`templates::task_w0314`): an operation of a task through a
    captured capability, through a local handler of the body, of an effect
    that is not standard (from a closure), or of any effect with no runtime.
    Another effect of the row goes to the summary part `task_effects`; a
    call of a callee whose `task_effects` a local handler handles is W0314
    at the call (`templates::task_effects_at`).
  - Precision: an access of a part of a variable reads the part, not the
    root (OR8 keeps the root read for a whole variable; corpus 136
    `field_part`); a perform through a local handler whose clause has no
    `resume` has no normal successor (`clause::perform_never_returns`;
    `abort_handle_given.wf`); a perform of a clause through a local handler
    outside it is `clause_performs` (W0801, corpus 15 `nested`); a task
    whose run applies a `multi` summary has no `multi_at` (O3-10); the
    writes of a task that a task starts are no `lends_mut` at the end of the
    outer task; the scope capability and a `TaskResult` local are not once
    values.
  - The tier-1 baseline changed for four probes (one W0405 for each task
    and span: a node whose span is inside the span of another node of the
    same conflict folds into its error, in both pipelines).
  - Fallbacks that stay (group E): a `scope` or a `fork` in a closure body, a task that
    runs a function value that runs another value twice (`again`), a task
    that runs a shared function variable that gets a new value, a value
    that a function value (not an item) runs as a task, and a spawn on a
    scope parameter.
  - Deviations: I3-8 (a `multi` operation in a scope body after a spawn
    statement) is not W0503: the probes of the shape (`multi_scope.wf`,
    `c3`, `c4`, `fd4_*`, `ms1`) run clean, the I3-8 repro is the same text
    as `c4_multi_scope_fail.wf`, and W0503 there gives eight `new-fp` probes
    (more than the 0.1 % share of §2.5). The claims I3-8, OR10 (a call reads
    each place of an argument) and RR12 (W0304 of a closure and a clause
    that give a local its value) move to follow-up F19.1.
- As built (follow-up F19.2, section 5): a closure that a callee made and that runs a
  capture two times did not move a `once` value of the capture (group C, found at
  F19: `scratchpad f19/or3c1.wf`). The run of the made closure now moves its value,
  and the run again uses it (W0502; `transfer::apply_runs` with `made`, docs/ir.md
  6.6). Probes `tests/gate/probes/fixes/c1once/`, claim C1-ONCE.
- As built (follow-up F19.3, section 5: the independent review of group E, scratchpad
  `ereview/review.md`): a callee or a closure that joins a handle (part `joins`) ended
  the task at the `Main` node of the call, and the abort edge leaves `Main` too (E-1).
  The part `abort_joins` (the handles that the body joins on each path where an abort
  leaves it) decides: the task ends at `Main` only if the handle is there too, else at
  `Ret` (`templates::call_joins`), and the abort edge loses the handle
  (`transfer::lose_given`). The fact oracle has a task check: a task with
  `joined_at(T, n)` must be joined when the run leaves `n` (it failed on each E-1 hole
  before the fix). A closure that a callee runs at `Ret` starts its tasks at `Main` only
  where W0602 or another run of the call needs it (E-2), and a closure that gives back
  the handle of its task gives the handle its task site (part `ret.tasks`, E-3).
  Probes `tests/gate/probes/fixes/e1/`, claims E-1, E-2, E-3; the review signed 8
  `lost-clean` rows of stage F19.
- As built (follow-up F19.4, section 5: the second review of group E, scratchpad
  `ereview/review_r2.md`): a task that a late run starts now starts before the call node
  when the call runs code of a local handler after the run (`Run::then`, R2-1), and a
  clause that ends the callee loses the handles that the callee does not join on the
  abort paths (R2-2). The fact oracle checks the start of a task when a clause runs. The
  review signed the 6 refused rows of F19.3 and 11 clean twins of E-1, which are now in
  `tests/gate/probes/fixes/e1/`; `e13_loop_direct_join_c` stays out of the gate.
- As built (follow-up F19.5, section 5: issue #50, R3-1 and R3-2 of the third review of
  group E, scratchpad `ereview/review_r3.md`; issue #51, R3-3 and R3-4): the start rule
  of F19.4 saw only a handler of the same component, and no part of a summary said
  which places a task of the callee accesses while the callee waits for a handler of a
  caller. The new summary part `waits` (docs/ir.md 6.4, 6.7) gives, for each effect, the
  places that the tasks change and read at each node that sends the effect past the
  function: the tasks that are active there, the tasks that a late run starts when the
  callee or the value can wait after the run, the tasks of a value that the callee runs
  as a task, and σ of the part `waits` of the summaries that the node applies (callee
  chains, closures, stored closures, `with_timeout`, `fail`). A call that runs a clause
  of a local handler gets four `Task` nodes for the handler and two tasks
  (`templates::WaitTask`): one changes the places of the tasks and conflicts with what
  the clause accesses; the other changes what the clause changes and conflicts with what
  the tasks read. So the clause conflicts with the tasks, and the parts of the call at
  `Main` do not: a task of a late run no longer starts on the edges into `Main` for a
  clause (R3-3, R3-4), and for an abort to a local handler it starts at the `FrameEnd`
  of the abort. The fact oracle checks the tasks of callees when a clause runs. Probes
  `tests/gate/probes/fixes/f195/` (claims R3-1, R3-2, R3-3, R3-4).

#### F20 Generics; group F on

- Depends on: F19.
- Read: `ir §5.20`, §6.7 (`drops`, `holds`), §5.35.
- Goal: user functions with type parameters; full coverage.
- Files: `crates/weft-sema/src/analysis/summarize.rs` (`drops` and `holds` as queries:
  a `Dead` or an overwrite of a maybe-initialized value of a type parameter; such a value
  live across a node that can abort or resume more than once), `analysis/apply.rs` (the
  check with the type arguments of the call; held arguments move at `Ret`),
  `factgen/vars.rs` (the `immovable` flag: off for an `in_place` local and for a
  construction that `into` writes, so the spec rule `moved_immovable` gives W0604,
  `ir §5.36`),
  `crates/weft-sema/src/lib.rs` (group F in the default set).
- Tests first: OL-3a, RR9, V081, V031, V056 as the claims say; OL-R2c-3 (a `holds` with
  the type argument, not the worst case) is accepted; the generic programs of the corpus
  keep their markers.
- Do: the code above; then the gate for all groups (rules of F8).
- Gate: the common gates; the common exit; tier 2.
- Exit: the common exit on all programs; the coverage of each set is 100 %.
- As built (group F goes on in a separate last commit, "IR F20: group F on"; until
  then `--groups=ABCDEF` gives the preview):
  - `check_supported` has no group-F fallback. While the fact generator works on
    the component of a generic body (a local of the component names a type
    parameter), a type parameter is linear in `props::ir_props`
    (`props::GenericBody`, a mode of the thread; `once` stays strict), as the old
    lowering of a generic body. Each variable that is linear only through a type
    parameter has these type parameters in `VarInfo::generic.linear`
    (`vars::generic_linear`, the closures through `templates::fns_generic`).
  - `factgen::generic::finish` asks the queries of the spec over the facts of the
    component: `drops` (the value is live where its variable ends, gets a new
    value or is overwritten), `holds` (live at a node that can abort or resume
    more than once, or moved into a task), and the new part `forks` (a `fork`
    branch captures a value that a type argument can make nonportable,
    OL-NR-ptrfork). A linear value whose `on abort` comes from a type argument (a
    `Task<T>` handle, `Generic::on_abort`) that is live at a node that can abort
    gives `holds` (OL-3a: the old pipeline misses `g2_generic_task_hold.wf`). Then
    the variables lose `linear`: the generic body has no error of its own.
  - A call applies the parts with its type arguments: a linear type argument in
    `drops` is a dropped value (W0601), also a linear closure in an argument of
    the type parameter (V056); an argument of a type parameter in `holds` moves at
    `Ret`, and a type argument in `holds` that no argument gives is a variable in a
    part of the graph of its own across a node that can abort or resume more than
    once (`generic::held_across`, W0602, W0503); a nonportable type argument in
    `forks` is a `fork` branch of its own that captures it (W0401). A generic
    function item as a value gets the same checks where it is made
    (`generic::item_values`, RR9, V081; the fallback of `checks::item_value` goes).
    A value of a type parameter can be a function value: a parameter of a type
    parameter is `FnVal::Param`, `reach_fns` follows it (V075), a result of a type
    parameter has `ret.fns`, and a linear closure of an argument of a type
    parameter comes back linear. A task handle that a result of a type
    parameter gives back is no longer lost (`State::find_tasks`; O3-9
    `through_id`: its `join` ends the task).
  - `Drop(p)` changes `p` (the IR engine clears the cell; fact oracle C5 on a
    generic body whose type argument is plain data).
  - Follow-up F8.1: a whole local that moves (`place = move t`) takes along the
    references of its value that point behind a `Box` of `t`
    (`transfer::relocate_moved`): the target of the `Box` does not move. An
    assignment that moves a local with a `Box` part in a program with a place field
    gets a node of `Phase::Overwrite` before `Main`: the change of the old value of
    the destination is there, so the new references stay valid (154 `move_set`).
    A new value of a part rebinds the part variables below it, also behind a
    pointer (154 `second_node_cleared`, `n.next = None`).
  - Follow-up F16.3, the part for type parameters: an effect has no type
    parameter, so no type of an operation names one; `clause::given_ops` no longer
    tests it.
  - W0604 of a `!Move` value that goes to a parameter of a type parameter: the
    `immovable` flag of stage F7 (`vars.rs`: off for an `in_place` local and a
    construction that `into` writes, on for a temporary that a call that does not
    build it in place takes) already gives it; `tests/data/generics/modes.wf`.
  - Fallbacks left: the fallbacks of the earlier stages (group C: function values
    that code of a caller runs on another thread, an operation that gives a
    function value; group D: a captured continuation, a handler in a closure body,
    `GIVES_BACK` for a function value or a reference result, a `multi` operation of
    a handler of a caller in a clause, a capability that leaves its handler; group
    E: tasks in nested bodies, a task that runs a callback more than once or a
    rebound function variable; group B: a loop that the widening does not end).
  - Precision (issues): a linear closure copied out of an `Option` payload (issue
    47) is a `new-fp` of `c4_generic_clean.wf`; an item value is checked at the
    value only, not again at a call of the local that holds it.

### Phase C: cut over

#### C1 Full gate at full coverage

- Depends on: F20.
- Read: this plan §2; `ir §10`.
- Goal: every criterion of the gate holds on all programs with all groups on.
- Files: `tests/gate/ledger.toml`, `tests/gate/claims.toml`, `target/gate/report.md`
  (attached to the commit message as a summary), `crates/weft-check/tests/scale.rs` and
  `crates/weft-cli/tests/limits.rs` (an IR mode for each test).
- Tests first: the claims test with all groups on; the precision corpus programs
  (`35_wild_places.wf`, `102_wild_instances.wf`, `103_wild_lend.wf`, `143_arg_roots.wf`,
  `125_multi_values.wf`, `83_kept_values.wf`) keep their markers with `--facts=ir`.
- Do: run tiers 1 and 2 with all groups. Every `open` program now needs its entry:
  closed (the `ir` pipeline rejects it), or a finding id whose verdict is "stays", or
  class `edge` with an issue (ship rule). Check the cost criterion. Write the counts of
  each class into `docs/plan/core-ir.md` §5 ("Gate record").
- Gate: the common gates; the common exit; tier 2.
- Exit: the common exit on all programs; no unledgered `open` program; the claims test
  passes with all groups.
- As built (stage C1, on top of F20.4 ec00112):
  - The new-fp share: the precision causes of the 98 tier-2 rows of F20 (issues #56 to
    #59) are fixed (`docs/ir.md` 5.20, "As built (stage C1)"); 91 rows are `same` now.
    Of the 7 rows that stay, 4 (`h0` of `r2/oracle/runs`) are `stricter`: a function
    parameter that runs in the body of a local `Fail` handler can be an item that fails
    (probe `fixes/c1/n57_param_fails_b.wf`, `fixed`). Tier 2 has 12 `new-fp` rows of
    12548 probes that `old` accepts (0.096 %): the share blocker is gone. The rule of the
    share did not change.
  - The self-attack of the stage found two old holes of the `ir` pipeline (a closure that
    rebinds a captured function variable to a linear closure; a store of a linear closure
    into a function field of a local of plain data). Both are fixed.
  - `open` programs: F3-6 (`fk4`, `tk6`, `g14_fork_result_lin`, `jc`) are class `open`
    (verdict "stays", 10.3); `a13`, `e17`, `w09` are class `edge` (issue #41); `opres` and
    `d1_callee_mut*` are class `edge` (issue #48, the `GIVES_BACK` fallback of F16.3).
    `h3_div_min` and `c14_big` (the interpreter rejects the literal of the largest `u64`)
    are class `edge` (issue #63).
  - IR modes: `scale.rs` (`the_programs_of_this_file_check_with_the_ir_facts`, and the
    `ir` time in `many_locals_check_in_time`) and `limits.rs` (`pipeline` had it; the
    derivation tests now run with the `ir` facts too). The precision programs of the
    corpus keep their markers (`programs_ir.rs`); `143_arg_roots.wf` and
    `83_kept_values.wf` stay with the old pipeline (a function value that an operation
    gives to a handler, F14; issue #64).
  - The cost criterion does not hold (§5, gate record C1; issue #62): tier 1 `check`
    time 2.2 times the old time, and 10617 of 37667 functions have more than 3 times the
    facts. Follow-up C1.4 fixes the time and the facts (§5; two functions of the abort
    shape of `scale_ops.wf` stay over the bound of the facts; follow-up C1.4b brings them under it).
  - The independent reviews of C1 signed 13 of the 25 new tier-2 `lost-clean` rows. Their
    variants found holes C1-H1 (follow-up C1.1), C1-H2, C1-H3 (follow-up C1.2) and C1-H4
    (follow-up C1.3). 12 rows (p3038, p21058, p22405, p42423, p43731, p44831, p13470,
    p7192, p31046, p10437, p31901, p7514) wait for a signature.

#### C2 Fresh sweep

- Depends on: C1.
- Read: this plan §2.5; the generators in `tools/gate/gen/` (`gen3.py`, `gen4.py`,
  `mutate3.py`, `sweep4.py`, `gen.py`; G2 copied them from `SCRATCH`).
- Goal: 50 000 new generated programs find no accepted fault.
- Files: `tools/gate/gen/*.py` (the generators, changed to take their seeds as arguments),
  `crates/weft-gate/src/sweep.rs` (the `sweep` subcommand: generate, check with
  `--facts=ir`, run the oracle on each accepted program), `tests/gate/probes/sweep/` (each
  accepted program that faults, reduced by hand or with `tools/gate/gen/reduce.py`).
- Tests first: `sweep --n 20 --seed-base 1` runs end to end in the test.
- Do: `sweep --n 50000` with seed bases that no earlier round used. Each accepted fault is
  a defect: fix it in the new pipeline (or ledger it as `edge` with an issue, ship rule),
  add the reduced program to `tests/gate/probes/sweep/`, and run the sweep again for that
  generator.
- Gate: the common gates; the common exit; tier 2.
- Exit: the last sweep of 50 000 programs finds no accepted fault (realistic shapes) and
  no unledgered edge fault.
- As built (stage C2, on top of C1.4b 0699a28):
  - The generators take their seed as an argument (`tools/gate/gen/genmain.py`):
    `GEN.py SEED` writes one program, and `GEN.py --seed-base B --n N --out DIR` writes
    the programs of the seeds `B` to `B+N-1`. Run them with `python3 -I`. `gen3.py` and
    `gen4.py` read their prelude from `tests/gate/probes/r3/oracle/lib/`; `mutate3.py`
    mutates the corpus and the interpreter programs of the repository; `sweep4.py` gives
    a random program of a larger set for each seed (`--all DIR` writes the round-3 set).
  - `weft-gate sweep --n N --seed-base B` (`crates/weft-gate/src/sweep.rs`) divides `N`
    among the five generators, checks each program with both pipelines in one analysis
    (the `ir` record is `--facts=ir`), and runs the oracle with the `ir` engine in the
    first three configurations (`--runs`, the seeds 1, 2 and 3) on each program that
    the `ir` pipeline accepts (`--oracle-all`: on each program). It keeps each accepted
    program that faults and each crash in `OUT/kept/`, writes the seed list
    `OUT/programs.tsv` and the report, and removes the other programs. `oracle-run`
    takes `--runs K`. Test: `crates/weft-gate/tests/sweep.rs`.
  - Seed bases: the earlier rounds used seeds up to 102 999 (`r2/oracle/runs`,
    `r3/oracle/runs`, `verify/quality/gen`, `verify/s5/S5c/mut`). Stage C2 used
    1 000 000 (first sweep) and 2 000 000 (last sweep), each generator the seeds from
    the base to the base + 9 999.
  - First sweep (base 1 000 000, `--oracle-all`, 3 workers, 955 s, 52 programs/s; 170
    programs/s without `--oracle-all`): 50 000 programs, 46 349 distinct, 12 092 that
    `--facts=ir` accepts, 22 790 that fault, 4 accepted faults. gen4 seed 1002955: a
    part of a tuple result with a stated place (`pair_of(&a.items)`, `-> (&u64 in v[],
    u64)`) did not get the handle place of the `Rc` handle `a`, so a new value of `a`
    did not make the part invalid (a read of a freed cell; the old pipeline rejects
    it). Fix: `analysis::apply::stated_places` gives each stated part the handles of
    its root, as for a whole result (`docs/ir.md` 6.7, "As built (plan stage C2)");
    probes `tests/gate/probes/sweep/c2_tuple_rc_*` (claim C2-TUPLE-RC), test
    `ir_preview` `a_part_of_a_tuple_result_depends_on_the_handles_of_the_argument`. The
    sweep of gen4 with the same seeds then found no accepted fault. mutate3 seeds
    1000291, 1001825 and 1006663: a spawn in statement position gives a linear `Tx`
    with no `on abort` to a scope that aborts (F3-6, verdict "stays"; both pipelines
    accept it); ledger class `edge`, issue #73, probe
    `tests/gate/probes/sweep/c2_spawn_linear_no_abort.wf`.
  - Last sweep (base 2 000 000, after the fix, `--oracle-all`, 3 workers, 940 s, 53
    programs/s): 50 000 programs, 46 360 distinct, 12 151 that `--facts=ir` accepts,
    22 674 that fault, 3 accepted faults (mutate3 seeds 2000223, 2000459 and 2001167),
    each the shape of issue #73 (ledgered `edge`). Counts of each generator (generated,
    `ir` accepts, faulted, accepted faults): gen3 10 000, 2 271, 6 256, 0; gen4 10 000,
    3 556, 2 985, 0; mutate3 10 000, 1 674, 2 524, 3; gen 10 000, 1 953, 6 240, 0;
    sweep4 10 000, 2 697, 4 669, 0. No crash. For information: 24 programs that the old
    pipeline accepts and the `ir` pipeline rejects (4 fault, 20 do not fault), and
    1 291 that only the `ir` pipeline accepts (none faults).

#### C3 Switch the defaults

- Depends on: C2.
- Read: ADR 0012 (Consequences); `ir §8.3`.
- Goal: the new pipeline is the default.
- Files: `crates/weft-sema/src/lib.rs` (`FactGen::Ir` and all groups by default),
  `crates/weft-interp/src/lib.rs` (`Engine::Ir` by default), `crates/weft-cli/src/lib.rs`
  (help text), `tests/programs/*.wf` (the markers that the ledger moved, each with a
  comment line that names the reason), `docs/adr/0012-core-ir.md` (status: accepted),
  `docs/adr/0010-interpreter.md` (the interpreter runs the IR; landing pads; the unwind
  order), `docs/design.md` (the order of evaluation, choice A; the end of temporaries;
  the unwind order), `docs/architecture.md` (the pipeline of `ir §1.3`; effect inference
  as a fixpoint over summaries; W0707 and W0704 no longer reported),
  `docs/traceability.md` (each rule to its template and summary part), `README.md`,
  `tests/gate/baseline-c3.jsonl` (the `ir` snapshot of tier 1 with the new defaults, in the
  committed form of §2.3) and `target/gate/baseline-c3-tier2.jsonl` (with its hash
  committed): stages R2 and R3 compare with them.
- Tests first: `crates/weft-check/tests/programs.rs` (the corpus with the defaults) and
  every interpreter test pass with the defaults; `--facts=old` and `--engine=ast` still
  work (tested once each).
- Do: switch; move the corpus markers; update the documents.
- Do (second review of F8, section 3): the cut-over makes `--engine=ir` the default of
  `weft run`. The AST engine reads an operand when it uses it, not where the IR copies
  it (choice A, `ir` 5.1.1, 5.16, 5.33). So a program that both checkers accept can stop
  on the AST engine with "a place does not exist (the value changed shape)", for example
  `r.hp * { v.clear(); 1 }` (`f8/variants2/semN/n_l_clear.wf`; `--engine=ir` prints
  1). The claims sem-N1 and sem-N2 hold only with the IR engine as the reference
  semantics. Until the switch, the ledger `engine` entry of p1, p2 and p9 records the
  difference.
- Gate: the common gates; tier 2.
- Exit: the defaults are `ir`; the old pipeline stays behind its flags for one review
  round. Then the review round of the ship rule runs (outside this plan). Phase R starts
  when that round has no realistic blocker that the old pipeline does not also have.
- As built (stage C3, on top of C2 6ac7a67):
  - The defaults: `weft_sema::Options::default()` has `FactGen::Ir` and each group
    (`DEFAULT_GROUPS`, A to F); `weft_interp::RunOptions::default()` has `Engine::Ir`;
    the help text of `weft` says so. `--facts=old` and `--engine=ast` still work (tests
    `cli.rs` `the_ir_pipeline_is_the_default_and_facts_old_still_works`,
    `the_ir_engine_is_the_default_and_engine_ast_still_works`; `scope.rs`
    `the_ir_pipeline_is_the_default`; `compile_ir.rs` `the_ir_engine_is_the_default`).
    `weft_cli::check_path` uses the defaults. A program that the `ir` pipeline does not
    cover goes to the old pipeline with the note of `--facts=ir`.
  - The gate names its pipelines: the oracle (`oracle.rs`), D0 (`thir.rs`) and
    `ir-build` analyze with `FactGen::Old`, as before, so the verdicts of the cache do
    not depend on the default; `run`, `snapshot`, `sigdiff` and `sweep` named their
    pipelines already (`Both`, `--facts`).
  - The markers (`crates/weft-check/tests/common/mod.rs`): the codes after `//~` are
    the result of the `ir` pipeline; the codes after the word `old:` are the result of
    the old pipeline on that line (`//~ W0302 old: W0301`, `//~ W0301 old:`). The word
    `ir:` is gone (test `no_corpus_marker_has_the_word_ir`). `programs.rs` checks the
    corpus with the defaults (`corpus`) and with `--facts=old` (`corpus_old`). Each
    line with `old:` has a comment line above it with the reason: the ledger class and
    the stage (or the issue). 30 corpus files have such lines; each one matches the
    ledger entry that the gate uses for the program. `120_on_abort_effects.wf` had only
    the general entry of the bodies with no IR; it gets an entry of its own (class
    `changed`, stage C3: W0601 and W0602 of a `Vec<fn()>` of a linear struct, W0118 in
    both pipelines).
  - Four core IR targets are done with the `ir` pipeline (the test `ir_targets` of
    `weft-check` asks to move them): O3-5, O3-6, R3RT2 and R3RT3 moved to
    `tests/programs/177_o3_5_field_closure_tasks.wf` to `180_r3rt3_held_refs_at_call.wf`,
    with `old:` markers. O3-5 got W0403 markers at the four `fork` branches that run a
    closure of a field that changes a captured local (ADR 0006, as for
    `fork(|| v.push(2), ...)`); the two `ok_fork` functions run clean. F3-2 and F3-6
    stay targets.
  - Tests that test the old pipeline on purpose name it (`FactGen::Old`,
    `--facts=old`, `Engine::Ast`): the unit tests of the old lowering
    (`weft-sema/src/tests.rs`); the comparisons with the old pipeline (`scope.rs`,
    `factgen_units.rs`, `driver.rs`, `limits.rs`, `scale.rs`
    `the_ir_facts_have_at_most_three_times_the_rows_of_the_old_facts` and
    `the_programs_of_this_file_check_with_the_ir_facts`); the bodies of the old lowering
    in the preview (`ir_preview.rs`) and in `ir_ty.rs`; the B6 lints for each old
    function (`hypotheses.rs`; the components of the `ir` pipeline have their own test);
    the texts of the old lowering (`body_texts.rs`: 4 tests, `diagnostics.rs`: 6,
    `weft-check` `w0301_says_why_the_owner_is_gone`, `units.rs`: the hints of W0702 of
    a function with an unknown effect in its signature); the work counts of the
    checker on the shapes of the old facts (`scale.rs`: the causes of W0301, QA4, QA7,
    QA8); the counts of `weft facts` in the gate test `snapshot.rs`; the guard texts and
    the oracle of the AST compiler (`guards.rs`, `compile_ir.rs`
    `a_payload_place_of_a_variant_reads_the_payload_or_faults`). `semantics.rs`
    `unsigned_underflow_is_an_error` checks both engines; `weft-interp` `programs.rs`
    `static_corpus_runs` lets `main` of a program that the checker rejects stop with an
    oracle fault (164).
  - The oracle caches: the interpreter sources changed (`Engine::Ir` is the default of
    `RunOptions`), so stage C3 computed the caches of tiers 1 and 2 for both engines
    again. Each verdict is the verdict of C2 (tier 1: 4497 programs with the same text,
    and the 34 changed files by path; tier 2: 57393 programs), except
    `r3/quality/fuzz/o11/cur.wf` (tier 2), `benign` at C2 and `timeout` at C3 on both
    engines, also alone on one worker (the run is near the limit of 10 s).
  - The old records: the baseline of tier 1 (`baseline-tier1.jsonl`) is written again
    for the 34 changed files only: with the lines mapped through the comment lines and
    the new paths, each old record (diagnostics, violations, counts, kind) is the
    record of C2. Each other record is the same. Tier 2: 0 differences against
    `target/gate/baseline-tier2.jsonl` (5 unknown, as C2).
  - The `ir` baselines for stages R2 and R3: `tests/gate/baseline-c3.jsonl` (the `ir`
    snapshot of tier 1, `snapshot --tier 1 --facts ir`, in the committed form: no time;
    4530 ok, 1 error: `badutf.wf`) and `target/gate/baseline-c3-tier2.jsonl` (tier 2;
    57377 ok, 5 timeout, 11 error; SHA-256 in `tests/gate/baseline-c3-tier2.sha256`).
  - Gates: tier 1 0 blockers (each class count as C2; the warnings of C2); tier 2 (2
    workers) 0 blockers, new-fp 12 (0.096 %), each row with the class and the entry of
    C2; fact oracle tier 1 0 failures (16 timeouts, C2: 15); sigdiff tier 1 31642 same,
    6067 with an entry, 0 with no entry (as C2); `weft agree` (the defaults) agrees on
    the 155 corpus files, the 61 interpreter programs, the examples and the packages;
    `weft-gate sweep --n 2000 --seed-base 3000000`: 576 accepted, 0 accepted faults, 0
    crashes; IR goldens: `60_jumps.ir` has other lines in its W0315 notes, and the four
    moved targets have goldens.
  - `weft run` and `weft test` with the defaults and with `--engine=ast` on the corpus,
    the interpreter programs and the examples that the checker accepts: each program
    has the same exit code on both engines; the 7 programs that fail on both are the
    failures that the programs show (`fail`, `assert`, an integer underflow of
    `int_width.wf`, `06_http.wf` with no client, `display.wf` reads a file by a path
    relative to its crate).
  - The engine note of the stage text: the ledger `engine` entry of p1, p2 and p9
    (class `choice-a`) now says that the IR engine is the default and the reference
    semantics, and what the AST engine does (checked: p1 prints 6, p2 and p9 read a
    freed cell with the oracle, `r.hp * { v.clear(); 1 }` stops with "a place does
    not exist (the value changed shape)"; the IR engine prints 2, 2, `1 1` and 1).
  - Issues: #15 (O3-10), #17 (O3-12), #50 (R3-1, R3-2) and #68 (G4) are fixed in the
    default pipeline (their repros give the result of the issue; the old pipeline keeps
    the old result). #47: the W0601 is fixed (F20.1); the W0602 of
    `verify/s5/R3x/p2/h6_option_closure.wf` stays (`new-fp`, `precision`, ledger issue
    47).
  - Open: the `ir` pipeline gives other texts in 13 tests of diagnostic texts (the
    tests name the old pipeline); on the shapes of `scale.rs`, the work of the checker
    on the `ir` facts is not linear (`nested_wildcard_places_check_quickly` with 1000
    calls: 1 001 000 overlaps, `walk in a line`: 40 401 for 200 calls, 160 801 for
    400; the causes of W0301: `move part` 4200 searches for 1000 uses); the IR engine
    gives other guard texts for an unchecked program (a moved `Vec`: "a `Vec` is
    needed here"), and in the IR `let (a, b) = q` through a reference binds references,
    so the race detector sees no read where the AST engine copies the parts.

### Phase R: removal

#### R0 The fallbacks to the old pipeline

At C3 the old pipeline still checks each program that the `ir` pipeline does not
cover: 331 programs of tier 1 and 7770 of tier 2 (the scope report of Phase R,
scratchpad `rscope/report.md`; the note of `weft check` names the reason of the first
body that fails, so the counts are lower bounds). Stage R3 removes the old pipeline, so
these fallbacks must go first. R3 cannot hold "no difference against C3": each program
that comes into scope changes its `ir` record. So stage R0z writes a new baseline.

| Stage | Goal | Reasons of the scope report | Size |
| --- | --- | --- | --- |
| R0a | The diagnostic texts of the `ir` pipeline name the source value (issue #74) | (texts) | done (77efbd0) |
| R0b | A callee with no IR, or an extern callee, gets a worst-case summary from its declaration; N1 becomes a `typeck` error (W0121); a handler with no clause for an operation passes it on (I1) | C3, E6, P1, C1 with a type error, N1, I1 | done (e13c8d3) |
| R0c | The leftovers of groups A and B | A1, A2, B1 | done (this stage) |
| R0d | Handlers in closure bodies; the two shapes of a handler that passes an operation on that R0b left | D2, C5 (C8, D5 stay: design note of R0d) | done (this stage) |
| R0e | Tasks in closure bodies | E1, E3 | L |
| R0f | Task runs (`http.serve` callbacks, code of a caller on another thread) | C1, E2, E4, E5, C7 | M |
| R0g | Continuations and capabilities in closures | D1, D4, C4, C6 | L |
| R0h | Function values across operations | C2, D3 | M |
| R0i | The other old inputs: `ValueProps`, W0502, W0303, `Analysis::sigs`, the seed facts (can run beside R1 and R2) | | M |
| R0z | 0 fallbacks; a new committed baseline of tiers 1 and 2 that R3 compares against | | S |

Each stage gates as C3 did: tier 1 0 blockers; tier 2 (2 workers) 0 blockers and
new-fp at most 0.1 %; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no
entry; a program that comes into scope is no new hole (lost-fault 0). The L stages are
in the families where the reviews of groups D and E found blockers: each one needs its
own review.

R0b as built:

- A callee with no summary of its body gets the worst case of its declaration
  (`analysis::sig::from_declaration`): a body with no IR (a type error, W0303) and a
  body that the fact generator does not support. The summary reads only the types, the
  stated places and the stated row of the source signature (`FnDef::sig`), never the
  parts of the old inference. An extern function keeps `from_signature` on its source
  signature (the same signature as before: the old inference does not change it). The
  worst case of a body (`sig::body_worst_case`): with no stated row it changes each
  place that a parameter reaches and each `rc` object that a parameter type reaches,
  and it performs each effect of the program; it can abort (`raises`, `assert`),
  resume more than once, give a place of its frame, drop, hold and fork each type
  parameter; it runs each function value of each parameter many times, as a task on
  another thread at the same time as the other values, while it changes and reads
  each place that it gets, and it can keep and give back each of them
  (`foreign_fn_parts` with `foreign` off, so the run node gives the accesses of the
  task: a closure that changes a captured place is W0403 and W0405 at the call, not a
  reason to use the old pipeline). `callgraph::failed` is gone: the callers of a body
  that the fact generator does not support use the worst case too, so the note of the
  fallback names the reason of that body.
- A callee with no IR in a program with no error is not possible: a body with no IR
  keeps the program in scope only if the program reports an error for it
  (`irbuild::Entry::reported`). So each program that comes into scope has an error,
  and the worst case keeps the facts of its callers sound but not precise: the callers
  of such a callee get W0702 for the effects of the program, W0403 and W0405 for a
  closure that changes a place, and the effects in the rows that the `ir` pipeline
  infers (ledger `sig` entry of stage R0b).
- N1 (`o.A` of a variant with no field or with more than one field): `typeck` reports
  the new code W0121 (`body/expr.rs`, `Lower::field_of`). The body has no IR for a type
  error, so the program is in scope. The other choice, an rvalue tuple, is larger: the
  builder would need a form for a borrow, a move and an assignment of `o.A`, and the IR
  engine would run other code with no change of the interpreter sources (the key of
  the oracle cache, F8.2). `docs/ir.md` 5.8 and 5.36 say so; claims F10-HB name W0121.
- I1 (a perform in the handled body of a handler with no clause for its operation,
  `handle E {} in op()`): the builder passes the operation on to the handler outside
  (`irbuild/caps.rs`, `Builder::op_cap`): the capability of the site, else `Row(E)`;
  V11 accepts that `Row(E)` in the handled body of such a handler when no environment
  around the handler binds `E` (`weft-ir` `verify.rs`, `passes_on`). The interpreter
  does the same at run time, and the test `semantics.rs`
  `partial_handler_forwards_other_operations` states it as the semantics: a handler
  that has a clause for only some operations is common (`handle Log { fn info(m) ...
  }`, about 200 files of the tiers), so a `typeck` error would reject valid programs.
  A closure in such a handled body and a handler with no clause nested in another one
  with no clause keep the old capability (the old pipeline checks such a program).
- Tests: `crates/weft-sema/tests/scope.rs` (`a_callee_with_no_ir_gets_the_worst_case_of_its_declaration`,
  `the_note_of_a_fallback_names_the_body_that_the_fact_generator_does_not_support`,
  `a_variant_payload_of_no_field_or_of_more_fields_is_w0121`,
  `a_handler_with_no_clause_for_an_operation_passes_it_on`); corpus
  `tests/programs/181_variant_payload.wf` (W0121), `182_handler_no_clause.wf` (W0702
  for an operation that the handler passes on, and the clean cases),
  `183_no_ir_callee.wf` (the worst case, with `old:` markers); `weft-check`
  `ir_handlers.rs`: `g_row_struct.wf` (a callee with a type error) is in scope now.
- The fallbacks, before (77efbd0) and after, tier 1 / tier 2, by the note of
  `weft check` (scratchpad `r0b/before-t*.tsv`, `after-t*.tsv`): C3 11/46 to 0/0, E6
  1/312 to 0/0, P1 1/1 to 0/0, N1 5/0 to 0/0, I1 1/1 to 0/0, C1 40/191 to 39/106. The
  programs whose first failing body was one of these and that still fall back now show
  their own reason: E1 52/3647 to 53/3669, D2 33/2520 to 33/2538, D3 29/54 to 34/59,
  C2 16/100 to 17/103, D4 19/114 to 19/117, E2 10/20 to 10/22, E5 3/11 to 3/14, A2 2/8
  to 2/9. Total 331/7770 to 318/7382. 14 programs of tier 1 and 389 of tier 2 come
  into scope. Each one but `redteam/crash/c02.wf` (I1, with no `main`; both pipelines
  accept it) has an error of `typeck` or W0303, so the `ir` pipeline accepts none of
  them (tier 1: 10 `changed`, 4 `same`; tier 2: 282 `changed`, 104 `same`, 3
  `moved`). One program of each tier goes out of scope (`r3/interp/probe/k6_http_once.wf`: the closure of `http.serve`
  calls `take`, a callee with a type error, and the worst case of `take` makes the
  closure a C1 case of stage R0f).
- Gates: tier 1 0 blockers (3602 same, 10 open, 246 fixed, 1 new-fp, 101 lost-clean,
  125 moved, 449 changed; the 19 more `changed` have W01xx in both pipelines, ledger
  entry of F8; the new `fixed` is `182_handler_no_clause.wf`); the old records of the 5
  `hb` probes (W0121) and of the 3 new corpus files are new in
  `tests/gate/baseline-tier1.jsonl`. Tier 2 (2 workers) 0 blockers after a `moved`
  entry for 2 mutants of `113_returned_closures.wf`; the old records of tier 2 do not
  change: 43735 same, 10 open, 88 fixed, 12 new-fp (0.096 %, the rows of C1), 0
  lost-fault, 2476 lost-clean, 1605 moved, 9467 changed. Fact oracle tier 1 0 failures
  (the 7 faults of C3). Sigdiff tier 1 0 rows with no entry (a `sig` entry for the callers of a callee with no IR in 52
  programs, and one for the rows of a handler that passes an operation on). The review
  script of group E (`ereview/ev.sh`) on the 403 programs that come into scope: 0
  HOLE (278 rejected by both pipelines with no fault, 123 rejected with a fault of the
  oracle, 2 accepted with no fault: the two copies of `redteam/crash/c02.wf`).
- Open: the baselines `tests/gate/baseline-c3.jsonl` and `baseline-c3-tier2` keep the
  `ir` records of C3; R0z writes the new ones. A callee with no IR makes each caller
  perform each effect of the program, so its W0702 lines are noise next to the type
  error. A handler with no clause for an operation still falls back in two shapes: a
  closure in its handled body that performs the operation (a perform through a
  captured capability), and a handler with no clause nested in another one of the
  same effect with no clause.

R0c as built:

- A1 (a reference through a copy of an `rc` handle into an `rc` object of the same type,
  `factgen::stored_behind`): the W0204 store check decides the case and the program stays
  in scope. A must alias from the IR shows that the objects are the same
  (`templates::same_object`): the store reaches the object through one whole handle
  parameter `c` only, the local handle `d` gets its value at one place of the frame only
  (`d = Rc.clone(&c)` or `d = c`), `c` never gets a new value, no reference to the whole
  handle of `d` or `c` exists other than the receiver of an `Rc.clone`, and no closure
  captures `d` or `c` by reference. Each body of the frame counts (upvar locals are the
  same cells). Then `d` holds a copy of the value of `c`, so the reference goes away with
  the object: no W0204. In each other case the check reports W0204 as for a handle of
  another object (`Stored::maybe_same`): the facts cannot tell, and the object of `d` can
  go away at the return. Why this choice: a conservative W0204 alone is the smallest sound
  fix, but it made `k01_clone_of_param.wf` (clean, the form of the scope example) a second
  `new-fp` probe of tier 1, over the 0.1 % rule (2 of 1460 probes that `old` accepts). A
  precise identity in the analysis (a must alias in the values) is larger: the values are
  may sets, and a handle can get a new value between the copy and the store. The rule of
  the IR covers the common form (a copy of the handle parameter) and is sound by
  construction: each write of the two handles fails it. `a13_nested_rc_rc_b.wf` (the store
  handle is in an `rc` object, old hole AB-RC1, issue #41) is W0204 now (`fixed`; the
  `edge` entry is gone; claim F13B-AB-RC1 names it). `docs/ir.md` 6.9.
- A2 (a perform whose rest of the handled body the facts do not find, `handlers.rs`
  `Region::starts`): the clause runs in a task. A task that W0314 rejects
  (`templates::task_w0314`, at a spawn, a fork branch or a task of a callee) puts the
  bodies of its closures into `Handlers::w0314_bodies`. `Region::starts` skips a run of a
  clause at a node of such a body, or of a body inside it: the clause cannot run on this
  task, so the rest of the handled body does not run after it. This is sound because the
  set only gets a body when W0314 is reported for the task: the `ir` pipeline rejects each
  such program. The runs of the clause on this task keep their region. The diagnostic is
  W0314 from the part `tasks`, on the line of the old one (the span starts at the spawn
  call, not at the closure). 1 program of tier 2 keeps the reason in another form
  (`r2/oracle/runs/g7/p43333.wf`: a `return` in a handled body, W0315 in both pipelines,
  leaves dead code whose closure runs the clause; no task).
- B1 (a loop whose widening does not end, `analysis/mod.rs`): rule 5 of the widening
  (`widen.rs`, `docs/ir.md` 6.6). At a loop head a part of the value of a local deeper than
  `DEPTH_MAX` = 8 steps becomes one summary part: the part at depth 8 is a leaf with the
  join of the part and of each part below it (`Tree::limit_depth`). A read below it gets
  the summary (`Tree::get` joins the tops above the path), so the widened value holds each
  value of the join (each reference, function value, capability, task, and the must flags
  of the join): sound. The depth is finite, so a loop that builds a list (`l = Cons(i,
  l)`) ends. Precision: a list keeps four levels of its own parts; the elements from the
  fifth on share one summary. A reference deep in a list stays in the value
  (`186_recursive_list_loop.wf` `deep`: W0301 after a push of the vector that the first
  element points into). The rule changes no program of tier 1 or tier 2 that was in scope.
- Tests: `crates/weft-sema/tests/scope.rs`
  (`a_reference_through_a_copy_of_an_rc_handle_stays_in_scope`,
  `a_task_that_performs_through_a_handler_of_this_task_is_w0314_in_scope`,
  `a_loop_that_builds_a_recursive_value_ends`); corpus
  `tests/programs/184_rc_handle_copy.wf` (W0204 with `old:` markers: `fixed`, the clean
  copy of a handle parameter), `185_task_perform_rest.wf` (W0314 of a spawn, of a closure
  that runs on this task and as a task, and of a fork branch; a clean task; `main` runs
  the clean case only, as `static_corpus_runs` of `weft-interp` needs),
  `186_recursive_list_loop.wf` (W0301 in a list, at the head and deep; clean lists), with
  their IR goldens.
- The fallbacks, before (e13c8d3) and after, tier 1 / tier 2, by the note of `weft check`
  (scratchpad `r0c/after-t*.tsv`): A1 2/0 to 0/0, A2 2/9 to 0/1, B1 2/2 to 0/0. The other
  reasons do not change. Total 318/7382 to 312/7372. 6 programs of tier 1 and 10 of
  tier 2 come into scope (with the 3 corpus files: 9 of tier 1).
- Gates: tier 1 0 blockers (3603 same, 9 open, 248 fixed, 1 new-fp, 101 lost-clean, 125
  moved, 450 changed; `fixed` +2: `184_rc_handle_copy.wf` and `a13_nested_rc_rc_b.wf`;
  `open` -1: the `edge` entry of issue #41 is gone; `changed` +1: `redteam/t03_items.wf`,
  W0702 at the spawn of an item and at a fork branch next to the W0314 of both pipelines,
  ledger entry of R0c); the old records of the 3 new corpus files are new in
  `tests/gate/baseline-tier1.jsonl`. Tier 2 (2 workers) 0 blockers after a `changed`
  entry for `r3/oracle/sweep3/callee__task_result.wf` (old W0313 at the escape of the closure, `ir`
  W0805 at its run; W0314 in both); the old records of tier 2 do not change: 43731 same
  (-4), 10 open, 88 fixed, 12 new-fp (0.096 %, the rows of C1), 0 lost-fault, 2476
  lost-clean, 1605 moved, 9471 changed (+4: `t03_items.wf`, `callee__task_result.wf`,
  `g00032.wf`, `g01306.wf`; the last two have entries of their own). Fact oracle tier 1
  0 failures (the 7 faults of C3; 1179 pass, +3: `k01_clone_of_param.wf` and the two `m1`
  lists). Sigdiff tier 1 0 rows with no entry. The review script of group E
  (`ereview/ev.sh`) on the 19 programs that come into scope (the 3 corpus files, 6 of
  tier 1, 10 of tier 2): 0 HOLE (7 `held`,
  2 `oldmiss`: `a13_nested_rc_rc_b.wf` and `184_rc_handle_copy.wf`, faults that only the
  `ir` pipeline rejects; 5 `both-reject` with no fault in the run; 5 `nofault`: `k01` and
  the `m1` lists, accepted and clean).
- Open: `p43333.wf` (above). The rule of `same_object` covers a copy of a handle
  parameter only: a copy of a local handle, a chain of copies and a store handle in an
  `rc` object stay W0204 (sound, not precise). The summary part of rule 5 loses the
  position of the elements of a list from the fifth on.
- Other tests that change: `weft-check` `ir_stored.rs` (`rc_clone_handle.wf` is in scope
  and accepted now); the template table of `factgen_units.rs` lets the nodes where a
  task ends give `scope_end` (`scope wait`, the `unwind value` of a
  scope, `join`: the frames of the callees of a task end where the task ends,
  `templates::task_end_lends` of stage F19; `spawned` of corpus 185 is the first body of
  the corpus with a task that calls a function and no call of its own).

R0d as built:

- D2 (a handler in a closure body, `factgen/mod.rs`): the bodies of a closure are the
  closure body and each handled body, clause and scope body whose root is the closure
  body (`alpha::unit_root`, `closure_units`). A handled body splices into the closure
  body as into a function body, in the facts of the summary (`closure_summary`) and in
  the instantiated facts of the component of the function (`emit_closure`): the nodes
  and the splice edges of each body that splices into it, the abort destinations of
  `Frames::of_bodies` of the bodies of the closure, the re-entry edges of the rows of
  each spliced body, the cycles of the handlers of the closure (`Cycles::add_handlers`).
  The analysis of the closure body runs each `handle` as in a function body. Then the
  facts of each clause of the closure come (`emit_clause`, from the states that the
  analysis of the closure body found), and the passes over the clauses run on them:
  `project`, the owners of the roots, `continuations` and `late_uses` in the facts of
  the summary; in the component of the function the tables of the handlers of the
  closure go into the tables of the function (`merge_handlers`), so the passes of the
  function cover them. A closure that a clause of the closure makes starts from the
  states of that clause. The function facts do not frame or emit a body of a closure.
  A nested body names the environment of the closure through an upvar local:
  `alpha::env_capture` follows the upvar chain, and the tests of the instantiation
  (`kept_whole`, `place_value`, `in_interface`), `captured_cap`, `captured_calls`,
  `captured_multi_nodes` and `clause_run_in_closure` read the root body. A run of a
  clause of an inner handler in a closure maps to the node that runs the closure
  (`Region::starts`). A closure with no nested body keeps the code of R0c (one test:
  `unit.len() > 1`), so no program that was in scope changes (the tier-1 recount: 0
  programs in scope with other codes).
- What the closure summary carries, in the terms of its interface (`docs/ir.md` 6.5,
  "Handlers in closure bodies"): the code of each clause at the nodes that run it (with
  σ of each perform), the effects that leave the closure, the performs through a
  captured capability (`Cap(k)`, also from a nested body), the aborts of the nested
  bodies (`summarize::nested_aborts`: an `assert`, and a failure of a callee unless the
  `Fail` handler of the call is a handler of the closure), part `multi` from the
  `multi_at` rows (a perform of a local handler of the closure is no such row, O3-8),
  the runs of the values of the interface in a clause (each `many`), a reference into a
  local of a nested body as a place of the frame. The `multi` re-entry of a handler in
  the closure: the runs of the values of the interface after such a node are in a cycle
  (E2 of `docs/ir.md` 5.20), so they are `many`; the run of the closure is no `multi`
  point of the caller for it. The C1.5 allow-list does not change: each exception E1 to
  E4 reads the cycles and the rows of the bodies of the closure now, and the fallback
  test of C1.5 (`ir_handlers.rs`) keeps the row in a clause as a fallback and puts
  `cap_nested.wf` and `h4_nested.wf` in scope (W0502 and W0503 at the run of the
  closure, as for the same closure with no handler; the old pipeline gives W0503 inside
  the closure).
- C5 (a capability in a closure that a closure makes): α of a `Cap` field of an
  environment is the place of the field, and its value holds that place
  (`factgen::env_value`, `transfer::move_path`). A run node in the closure body that
  applies a summary with `Cap(k)` whose σ is such a field (`clause::env_cap_of`) is a
  perform through the capture of the closure body itself: its summary gets `Cap(j)`
  (`apply::main`), and the node that runs it runs the clause (`check_cap_apps` accepts
  it). The node that runs such a closure in the instantiated facts runs the clauses of
  the handler of the capture (`captured_calls`, also for a late run at `Ret` of a
  callee), and a run of a function value in a closure body counts as a perform of a
  `multi` handler when a closure that the body makes captures a capability of such a
  handler again (`frames::recaptures_multi`, a row of `Cycles::add_captured`). A
  perform through a captured capability reads the field. A `Kont` capture stays with
  the old pipeline (stage R0g). The interpreter check of the old review sets found the
  first two forms open in a first build (`r67/v/a05_nested_closure.wf`,
  `f172/att/a29_nested_closure_in_closure_rowfn.wf`: programs of the reason "a
  capability that leaves its handler" that the C5 rule put in scope); probes
  `fixes/r0d/c5_rc1.wf` to `c5_rc8.wf` (a run through a callee, a vector, a struct
  field, three levels).
- The two shapes of a handler that passes an operation on (R0b): `clause::serving`
  gives the handler that serves an operation (the handler of the capability if it has a
  clause for it, else the handler of the effect around its `handle`: the first
  environment of that chain that adds the effect, through the capture of a closure
  environment), or none: the operation passes on to a caller (`passes_to_caller`, a
  perform through the row). The analysis (`perform_run`, `note_reentry`), the templates
  (`perform_local`, `templates::perform`, `clause_run_in_closure`, `captured_calls`
  with `serving_all`), the abort destinations (`frames::reach`) and
  `captured_multi_nodes` use it. Before R0d the destinations took the innermost handler
  of the effect, and a closure that performs the operation ran no clause. Three of these
  forms were holes of the `ir` pipeline in scope at R0c (`fixes/r0d/ph1_closure_pass_on.wf`
  and `ph5_callee_pass_on.wf`: W0301, the old pipeline misses them too;
  `ph3_landing_pass_on.wf`: W0602, the old pipeline gives it); `ph2` and `ph7` were the
  fallback of R0b ("handler h1 has no clause of an operation").
- A clause of a handler in a closure body that performs through a captured capability
  forwards the effect (`clause_performs`, so W0801 does not count it as a root handler;
  `m01732_15_library.wf`).
- The sparing at `Post` (issue #57): a later `resume` of a `multi` clause runs the rest
  of the handled body again at `Post`; if no node of the handled body can abort in the
  facts (a node that runs a clause of another handler counts, before the projection),
  the values outside the handled body are spared there, as at a perform of the handler
  (ADR 0005, `handlers::quiet_reruns`). The `resume` itself still can abort. Before R0d
  the static destinations made each run of a function value an abort past the
  function. This closes the tier-2 `new-fp` row `r2/oracle/runs/g7/p43563.wf` (its
  ledger entry of issue #57 is gone) and the new one `p3926.wf`; probes
  `fixes/r0d/ra1_resume_aborts.wf` (W0602 stays where the rest can fail) and
  `ra2_resume_value_run_ok.wf`. A first form that took the abort off the `resume` broke
  the rule of ADR 0005 (W0602 for a value inside the handled body), and R0d does not
  keep it.
- The fix of the review of R0d (a second commit). The review found three holes: an
  operation that a handler in a closure body with no clause for it passes on, performed
  through a callee, a function value or an inner closure (`fixes/r0d/pi1_*` to
  `pi3_*`, and the variants `pi_c6*`). Cause: `serving` covered only a perform that
  names the operation. A call names only the effect, so the destinations of the call
  (`frames::reach`) took the innermost handler of the effect, `call_clauses` dropped
  its `escapes_at` with no test of a pass-on, and a run of a closure that performs
  through the capability of such a handler (`Cap(k)` with σ a local capability) gave
  the closure summary nothing. Fix: `clause::serving_path` gives where each operation
  goes, up to the first closure environment (`Served::Local`, `Capture(cb, k)`,
  `Caller`); `frames::served_dests` replaces each local handler of a call by the
  handlers that serve its operations (and past the function for the others), so the
  analysis, the abort destinations and the clause runs of each consumer
  (`call_handlers`, `run_handlers`, `call_clauses`) see them; `call_clauses` keeps the
  `escapes_at` of an operation that passes on to a caller and records `Cap(k)` for one
  that goes out of the closure (then `captured_calls` runs the clauses of the handler
  of the capture); a perform through a local capability whose operation goes out of
  the closure is a perform through the capture (`passes_to_capture`); a call in such a
  handled body whose operation goes to a capture of a `multi` handler is a row of
  `add_captured` (`frames::passes_out_multi`; probes `pi_pm1` to `pi_pm4`, which the
  review did not have). The same rule closes the function-body form through a callee,
  a hole of R0c and of the old pipeline (`pi_ph5_direct_callee.wf`, `pi_c6z_*`), and
  the both-miss forms `pi_c6_passon_nested_closure`, `pi_c6g`, `pi_c6k`, `pi_c6q`; `pi_c6s`
  gets its W0602. Corpus `tests/programs/189_indirect_pass_on.wf`. The fact oracle over
  the 2391 programs of tier 2 that R0d brings into scope: 40 failures, each in a program
  that the `ir` pipeline rejects (the oracle runs it with `--unchecked`): the same rate
  and classes (C1, C5, A3 of code of a caller) as 2400 rejected programs of tier 2 in
  scope at R0c (48 failures); none in an accepted program. The reviewer signed the
  lost-clean rows of R0d.
- Fix 2 (round 2 of the review, a third commit), hole HOLE4: a `multi` operation of a
  caller that two handlers with no clause pass on (the handler of a closure and the
  handler of the function), performed by a callee in the closure. Fix 1 recorded
  `Cap(k)` for the operation that leaves the closure, and the summary of a closure
  leaves out each `multi_at` row at a node with `Cap(k)` (the clause of the handler of
  the capture is the `multi` point): here no handler serves the operation, so the run
  of the closure was no `multi` point of the row. Fix: `frames::row_multi` counts an
  effect that a local handler passes on to a caller (`serving_all(..).1`, through
  each capture) as an effect of the row; a node with `Cap(k)` whose operation can reach
  a caller keeps its row in the summary (`Handlers::cap_callers`). The same rule closes
  the function-level forms that R0c had too (`pj_a9f_no_inner_handler.wf`, `pj_b6_*`,
  `pj_b8_*`), and `a9` of the review gets W0503. A call that a `multi` resume runs
  again runs the clauses of the other handlers that the callee reaches at `Ret` too:
  this closes `pj_b9c_*` and `pj_b9d_*` (both pipelines missed them; the clause after
  the operation that resumed runs again). Probes `fixes/r0d/pj_*`, corpus 189
  `caller_multi_pass_on` and its clean twin. Open (precision): `b10b_three_levels_ok_maybe.wf`
  of the review (`served_dests` runs the clause of the outer handler for `a`, which a
  middle handler of the closure serves).
- Three covers of the fact and summary oracles that the new bodies needed: a handled body
  or a clause that moves a value out of the environment of the closure lends the place
  at the node (`templates::moved`; the machine takes the value out of a frame below);
  a `Kept` source of a closure literal through a reference (`*env.k`) reads the
  reference, also in a program with tasks (OR8 kept the read out); and the timeout of
  `with_timeout` runs the clause of the local `Fail` handler while the frame of the
  block waits at its `UnwindExit`: the reads and the changes of the clause are at those
  nodes too (`handlers::timeout_unwind_nodes`; `interrupt_inside_on_abort.wf`, whose
  function `rollback` fails the summary oracle at R0c too).
- Design note: D5 and C8 stay fallbacks (a row of a caller, or a `multi` local handler,
  re-enters a clause). The size: a second `resume` of the outer handler runs the code
  of the clause after the row again, then the continuation of the clause (the rest of
  the handled body after the perform P that ran the clause), then the rest of the
  function. The facts need (1) re-entry edges in the component of the clause, from its
  `Return`, its landing and its `Resume` nodes to a `Copy` node of the row, and a run
  of the analysis of the clause from the block after the row (`run_rows` for a clause
  body, with the locals of the clause copied and the heap of the end of the function);
  (2) each node that runs the clause as a row of the function (P: a `Copy` node with
  edges from the `Return`s of the function, also on the path of the abort of a clause
  that lands, to its `Landing`; for a row in the `post` part, the `Post` node of the
  `handle`, which has no `Copy` phase today); (3) the cycles of E2 for P and for `Post`;
  (4) for C8, the same with the `Post` of the local `multi` handler in place of the
  `Return` of the function (`handle_run` with `nested`). The once-after-multi family
  showed that each re-entry form needs its own proof of E1 to E4; this one needs a new
  kind of copied frame (a clause frame that waits for a continuation) and a new cover
  of the fact oracle (A4 for copied clause frames). The old pipeline gives W0503 for
  the `once` continuation that is live across the row (the D5 and C8 examples), so the
  fallback is sound.
- Tests: corpus `tests/programs/187_closure_handlers.wf` (W0301, W0503, W0602 of
  handlers in closure bodies; the clean cases with `old:` markers: O3-8 and a `Fail`
  handler inside the closure) and `188_captured_pass_on.wf` (the pass-on shapes, W0301
  and W0602 with `old:` where the old pipeline misses them; a capability captured
  again), with their IR goldens; probes `tests/gate/probes/fixes/r0d/` (20 programs:
  bad and clean forms of D2, C5 and the pass-on shapes); `ir_handlers.rs`
  `the_rows_of_clauses_stay_with_the_old_pipeline` (was
  `the_rows_of_clauses_and_closure_handlers_stay_with_the_old_pipeline`).
- The fallbacks, before (157ff56) and after, tier 1 / tier 2, by the note of `weft
  check` (scratchpad `r0d/t1-final.tsv`, `t2-final.tsv`): D2 33/2538 to 0/0, C5 4/125 to 0/0, D4 19/117 to
  15/46 (the C5 rule puts the capability that a closure of a closure captures again in
  scope). The programs whose first failing body was a handler in a closure body and that
  still fall back show their own reason: E1 53/3669 to 57/3958, A2 0/1 to 1/41 (a run of
  a clause at the run of a closure that left its handler: the region of the `resume`
  has no node for it; corpus `62_cap_escape.wf` was D4), C6 3/4 to 6/15, C1 39/106 to
  39/107, C7 2/2 to 2/3, D5 15/113 to 15/114; C8 and D5 stay (design note). Total
  312/7372 to 279/4981. 33 programs of tier 1 and 2391 of tier 2 come into scope (with
  the 2 corpus files and the 30 probes of `fixes/r0d`: 65 of tier 1); no program goes out
  of scope. Of the programs that were in scope, 0 of tier 1 and 4 of tier 2 change their
  codes (the sparing at `Post`: one W0602 fewer, each still rejected but
  `r2/oracle/runs/g7/p43563.wf`, which is clean).
- Gates: tier 1 0 blockers (4237 of 4569 in scope; 3612 same, 9 open, 251
  fixed, 1 new-fp, 108 lost-clean, 128 moved, 460 changed; `fixed` +3: `188` and the
  probes `ph1`, `ph7`; `lost-clean` +7, `moved` +3, `changed` +10, each ledgered; the old
  records of the 32 new entries are new in `tests/gate/baseline-tier1.jsonl`). Tier 2
  (2 workers) 0 blockers (49747 of 57393 in scope; 42437 same, 10 open, 88 fixed, 12
  new-fp: 12 of 12549, 0.096 %, the rows of C1 with `p23249.wf` in place of `p43563.wf`,
  0 lost-fault, 2853 lost-clean, 1707 moved, 10286 changed; the old records of tier 2 do
  not change; ledger entries for 371 `lost-clean` rows in six classes, 44 generated
  programs of class D-GEN, 4 `moved` and 1 `changed`). Fact oracle tier 1 0 failures.
  Sigdiff tier 1 0 rows with no entry (one `sig` entry of R0d). `ereview/ev.sh` on each
  program that comes into scope and that the `ir` pipeline accepts, on the 4 programs
  whose codes change, on the corpus files and the probes (669 programs): 0 HOLE (640
  no fault, 24 held, 3 oldmiss: the pass-on probes, 2 both reject with no fault). On the
  review sets of group D and of the once-after-multi family (`f17`, `f172`, `dreview`,
  `dreview2`, `dreview3`, `c1sign`, `r67/v`, `r67b/att`, `r67b/v`, `c15review`,
  `c16/att4`: 1936 programs): the same verdicts as the R0c binary (0 HOLE; the 2
  `HOLE(AST-only)` of the AST engine are older). Cost: tier 1 `check` CPU time old /
  `ir` 31.6 s / 51.5 s (1.63 times, 4267 programs in scope; R0c 1.55 on fewer
  programs); `scale.rs` passes. At the first commit the lost-clean rows of R0d said
  `signed_by = "UNSIGNED"`; the review signed them with the fix (below).
- Open: D5 and C8 (above). The tier-2 `new-fp` row `r2/oracle/runs/g5/p23249.wf` is a
  precision loss that function bodies have at R0c too (issue #56): a copied frame of a
  closure run holds a wildcard place of a reference parameter (`p2..`) that a later
  change invalidates (W0301). A run of a capture in a clause of the closure is `many` even when one perform
  runs the clause (D-CLAUSE-RUNS, as for a parameter of a function).

#### R1 Standalone `typeck`, part 1

- Depends on: C3 and one review round.
- Read: `ir §2.2`, §2.1.
- Goal: a type pass that does not need `body/`, for expressions and calls.
- Files: `crates/weft-sema/src/thir/typeck/mod.rs`, `typeck/expr.rs`, `typeck/call.rs`,
  `typeck/names.rs` (carved out of a copy of the inference parts of
  `crates/weft-sema/src/body/expr.rs`, `call.rs`, `args.rs`, `mod.rs`: unification, names,
  methods, operators, argument order, integer types, implicit dereferences), with no fact
  or value-flow code; `crates/weft-sema/tests/thir.rs` (D0, part 2).
- Tests first: D0 part 2: for each tier-1 body with no closure, handler, pattern
  binding or generic, the tables of `typeck` equal the recorded tables (`expr_ty`, `res`,
  `call`, `adjust`, `field`, `int_ty`).
- Do: carve; keep the diagnostics of the parts that move (W0102, the W01xx of
  expressions); a body that `typeck` does not cover yet uses the recorder.
- Gate: the common gates; tier 2 D0 on the covered bodies.
- Exit: D0 part 2 holds on the covered bodies of tiers 1 and 2.

#### R2 Standalone `typeck`, part 2; switch the THIR source

- Depends on: R1.
- Read: `ir §2.2`, §2.4.
- Goal: `typeck` covers every body and is the source of the THIR.
- Files: `crates/weft-sema/src/thir/typeck/pattern.rs`, `typeck/closure.rs`,
  `typeck/handle.rs`, `typeck/generic.rs`, `typeck/exhaust.rs` (W0120 with its budget,
  from `body/exhaust.rs`), `crates/weft-sema/src/lib.rs` (the IR pipeline takes its tables
  from `typeck`), `crates/weft-sema/tests/thir.rs`.
- Tests first: D0 part 2 on every body of tiers 1 and 2; W01xx, W0119, W0120 and W0504
  diagnostics equal the old ones on the corpus.
- Do: carve the rest; switch the source; the gate runs with the new source.
- Gate: the common gates; the common exit; tier 2.
- Exit: D0 holds on all bodies; the gate shows no new difference against C3.

#### R3 Remove the old fact generator

- Depends on: R2 and R0z.
- Read: ADR 0012 (D20).
- Goal: one fact generator.
- Files: delete `crates/weft-sema/src/body/`, `crates/weft-sema/src/thir/record.rs`,
  the re-lowering loop of `crates/weft-sema/src/infer.rs` (keep `growth_limit` for
  W0706), `FactGen::Old` and `Both`, `Options::ir_groups` and `irbuild/scope.rs` (all
  groups are on), `FnFacts::mark`/`rewind`/`FactMark` in `crates/weft-facts/src/lib.rs`,
  the closure summary of `Ty::Fn` and `fn_joins` in `crates/weft-sema/src/types.rs`,
  W0707 and W0704 in `crates/weft-check/src/codes.rs` (their texts say "no longer
  reported" or the codes go, with the test `every_code_has_a_test` updated),
  `crates/weft-gate` (the `old` side becomes the committed baseline of R0z).
- Tests first: the gate compares the new pipeline with the committed R0z snapshot
  (the baselines of tiers 1 and 2 that stage R0z writes, with 0 fallbacks): no
  difference.
- Do: delete; fix the imports; update `CLAUDE.md` ("Fact generation:
  `crates/weft-sema/src/irbuild/`, `analysis/`, `factgen/`").
- Gate: the common gates; tier 2 against the R0z snapshot.
- Exit: `body/` is gone; no gate difference against the R0z baseline.

#### R4 Remove the AST compiler of the interpreter

- Depends on: R3.
- Read: `ir §8.1`.
- Goal: one compiler for the interpreter.
- Files: delete `crates/weft-interp/src/compile.rs`, `Engine::Ast`, `--engine`, the
  span-keyed exports `FnFacts::by_value`, `arg_order`, `int_ops` and their users
  (`weft_interp::{by_value_captures, arg_orders, int_ops, exports}`), `StmtBegin` and
  `StmtEnd` if no IR code uses them; `crates/weft-gate/src/engines.rs` (removed).
- Tests first: every interpreter test passes; the IR oracle cache does not change (the
  interpreter sources hash changes, so recompute it once and compare the verdicts).
- Do: delete; fix the imports.
- Gate: the common gates; tier 2 oracle recomputation with no verdict change.
- Exit: `compile.rs` is gone; no verdict changes.

#### R5 Documents and checklists

- Depends on: R4.
- Read: ADR 0002 (the checklist), `CLAUDE.md`.
- Goal: the documents describe the code that exists.
- Files: `docs/adr/0002-datalog-spec-and-checker.md` (the checklist step "fact
  generation": a template entry in `factgen/templates.rs` or a summary part, and a `RELS`
  row in `factgen/rels.rs`), `CLAUDE.md` (the rule list), `docs/architecture.md` (no
  `body/`, no `compile.rs`), `docs/traceability.md`, `docs/ir.md` (status: implemented;
  the parts that changed during the work), `README.md`.
- Tests first: none (documents); the tests that read the documents (for example the code
  table tests) pass.
- Do: update the documents; record the final gate counts.
- Gate: the common gates; tier 1.
- Exit: the documents match the code; the migration is complete.

---

## 5. Follow-up stages and the gate record

Rule 5 of section 1 adds a row here for each follow-up stage. A follow-up stage has the
gate and the exit of its parent, limited to its group of differences.

| Id | Parent | Group of differences (code pair, shape) | Status |
| --- | --- | --- | --- |
| F8.1 | F8 | W0301 / W0304: a place-field reference in a `!Move` value travels with the moved value in the analysis (`r2/oracle/probes/n?_immov_*.wf`, `changed`; `tests/programs/154_unset_nested.wf` `move_set`, group F, a W0301 false positive). Fix (stage F20): a move of a whole local takes along the references that point behind its `Box` (`transfer::relocate_moved`), and the old value of the destination goes at a node of `Phase::Overwrite` before the new value binds. A `!Move` value that moves by value stays W0604 (the `n?_immov` probes keep `changed`). Probes `tests/gate/probes/fixes/f20/f81_*` (claim F8.1) | done (F20) |
| F8.2 | F8 | the gate: the key of the `ir` oracle cache is the hash of `crates/weft-interp/src` only, so a change of the IR builder does not make the cache stale. Stage F8 regenerated both `ir` caches by hand | open |
| F8.3 | F8 | lost-clean W0301 / none: receiver order and `Bounds` (second review of F8, 4.2). In `w.entities[0].plus(shrink(&w))` the `ir` pipeline accepts the program (old: W0301), and the IR engine stops at the borrow with "index 0 is out of bounds" (benign). The safety rests on the second index check of the engine at the borrow (`crates/weft-interp/tests/compile_ir.rs`). The third review of F8 signed the `lost-clean` entry after the fix of hole R1 (a variant step in a receiver place, F8d). The 11 programs are in `tests/gate/probes/fixes/f8/receiver_bounds/` (tier 1, 11 `lost-clean`, 0 blockers); claim F8-RB is on and holds | done (F8.3) |
| F10.1 | F10 | lost-fault W0301, W0302, W0601 / none in group A (review of stage F10, before group B). Hole H-B: a body with no IR (a type error with no W01xx diagnostic, a conflict in the THIR tables, a variant payload) got no facts, and the program stayed in scope, so no pipeline checked the body. Fix: such a program is out of scope (`irbuild::Entry::reported`). The root cause of the loop shapes (`let best = None` before `best = Some(e)` later in a loop: the lowering visits the body in more than one pass, and the THIR recorder kept the types of each pass) is fixed too: the THIR tables keep the decisions of the last pass of each loop (`Recorder::next_pass`). A variant payload of two fields (`e.A`) still has no IR (typeck accepts it): such a program is out of scope. The programs are in `tests/gate/probes/fixes/f10/hb/`; claim F10-HB. Hole H-A: a reference stored behind a reference parameter (a heap slot) and read back after its referent changes was accepted (no variable held the places of the slot). Fix: each heap slot has variables of its own (`factgen::holders`, docs/ir.md 6.6 "As built (F10.1)"); the 22 programs are in `tests/gate/probes/fixes/f10/ha/` (14 group A: `moved`, the ir pipeline reports the read in the body, the old pipeline the call in the caller); claim F10-HA | done (F10.1) |
| F10.2 | F10 | lost-fault W0301 / none in group A (second review of stage F10, hole H-C). A callee stores a reference through a reference that its argument holds (`out[0].push(&v[0])` with `out: &Vec<&Vec<&T>>`); the caller did not give the referent of `out[0]` the stored places, so `v.clear(); print(inner[0].hp)` was accepted (5 regressions where the referent is behind a parameter, 11 programs that both pipelines missed). Fix: the part `stores` reaches the referents of the references that an argument holds (`σ(Held(j))`, or `σ(Param(j))` of a by-value argument), with the reach of the part `muts` and the R3RT6 type rule on the type of the root of the referent (`analysis::apply::stores`, docs/ir.md 6.7 "As built (F10.2)"). The programs are in `tests/gate/probes/fixes/f10/hc/` (16 group A, 2 group AB, 1 control) and `tests/programs/165_store_through_held_ref.wf`; claim F10-HC | done (F10.2) |
| F13.1 | F13 | the review of stage F13 part 1 (scratchpad `f13/review.md`): the default-AB release blockers AB-RC1, AB-RC2 (a regression), AB-RC3 (W0204 and W0301 with `rc` handles and heap slots), the ABC holes H-S1, H-RC1, K3-Made, H-LIN, the summary oracle over `puts` and `put_fns`, and the false positives FP-AB-RC, FP-S2, FP-K4 and `both(f, g)` (docs/ir.md 6.6, 6.9; probes `tests/gate/probes/fixes/f13b/`). The final check of group C then found H-ORD (a regression of the order flag of `both(f, g)`) and the old hole AB-RC1-join; both are fixed before group C goes on (probes `tests/gate/probes/fixes/f13c/`, claims F13C-ORD and F13C-JOIN). Old holes left (ledger `open-old`, issue #41): AB-RC1 through a handle in an `rc` object (`a13`), AB-RC3 `e17`, H-W9 (a closure stores its reference parameter into the object of a captured handle) | done (F13.1) |
| F13.2 | F13 | lost-fault W0301 / none in group C, found by the signature diff of stage F13 part 2 (no gate probe has the shape). An unknown function value that runs in a body (the capture of a made closure that holds a function parameter of the maker, `let f = mk_call(push1, world); f()`; a function-value local that a closure gives a new value, `let set = \|\| { g = grow }; set(); g(world)`) is code of a caller. Its `lends_mut` of the reference parameter and of `a place of a caller` do not reach the summary of the body, so a caller of the body misses the change (`verify/p/v06_ret_paths.wf` `ret_passthrough`, the tier-2 mutant `m01258_43_loops.wf` `item_later_pub`; the summary oracle fails on a caller). Fix (docs/ir.md 6.8 "As built (follow-up F13.2)"): a made closure runs the values that it holds with the places of the run, a rebound local gets the values that the closure puts there, and the summary of a function body has the part `lends` for code that no caller gives; a value that a closure runs through a capture changes its environment (no W0312). Probes `tests/gate/probes/fixes/f13d/` (class UR, claim F13D-UR); the sigdiff rows of `mk2` (v06_ret_paths.wf) join the `sig` entry of a maker of a maker | done (F13.2) |
| F16.1 | F16 | fallback (old pipeline) / group D: a continuation that a closure captures (`CaptureMode::Kont`, a `resume` in a closure that a clause makes; 40 tier-1 programs fall back), and the continuation summary of `ir` 6.7 (`analysis/cont.rs`). Claims R3RT4, V121, J2 and RT8 hold only through the fallback today. Do: a run of such a closure in its clause is a resume point at the run node; a closure that holds the continuation and leaves the clause is W0313 (stage F17) | open |
| F16.2 | F16 | fallback / group D: a handler in a closure body (11 tier-1 programs; claim O3-8), a closure that a clause gives to the handled body (`resume(\|\| ..)`, 4), a `multi` resume point in a clause or a closure inside the handled body (2). Do: the clause runs of the closure body in its own facts; the states of the clause where the given closure runs | open (a handler in a closure body: done at R0d) |
| F16.3 | F16 | fallback / group D: `GIVES_BACK`, a call that runs a clause of an operation with a function value, a type parameter or a reference result and a clause that resumes (18 tier-1 programs; σ(Caller) at the call is the resumed values, and only code of a caller lends places of `Caller`), and a `multi` operation of a handler of a caller in a clause (14). Type parameters: done at stage F20 (an effect has no type parameter, so the test goes) | open (function values, references) |
| F17.1 | F17 | lost-clean / group D: group D on, after the second independent review of group D (scratchpad `dreview2/review.md`). Fixed first: ORACLE-GAP-2 (A4 of copied callee and closure frames), D-MULTI-MID (a `multi` clause changes a place between two `resume`s while a copied callee or closure frame holds a reference into it; the copy of the frame is used at the `Copy` node), D-COPY-WAIT-CALL (the caller changes the place after the call, an old hole), FP-W0313-RUN (`clause::performs_cap`). The reviewer signed the 12 `lost-clean` rows; the `new-fp` `h6_option_closure.wf` is a precision loss of the groups A and C (issue to file). Then the default groups are A to D (`DEFAULT_GROUPS`), `done` gets F14 to F17.1, the 15 `open-old` entries of the old holes that group D closes go, the signature differences of the new bodies have `sig` entries, and the tests of the default groups change | done (F17.1) |
| F17.2 | F17 | lost-fault W0312, W0301, W0302 / group D, after the third independent review of group D (scratchpad `dreview3/review.md`). ORACLE-GAP-3: the clause cover A5 of the fact oracle. D-FNVAL-ROW: a function item or a function parameter that runs in the handled body of a local handler of its row runs the clauses of the handler (`frames::value_effects`); a call in a closure body through a captured capability runs the clauses of its handler (`handlers::captured_calls`, also FP-W0805-FNVAL). D-ROW-MID (an old hole): a known callee of a `multi` re-entry through the row gets the copy of its frame. Probes `fixes/f17/fnval_row`, `fixes/f17/row_mid` | done (F17.2) |
| F16.4 | F16 | lost-fault W0301 / none in groups A and C, found by the self-attack of stage F16 (class C-RR, scratchpad `f16/open/crr_*.wf`). A closure that holds a reference to a container of references (`kr: &Vec<&i64>`) reads through it; the node that runs the closure used only the variables of the captures, not of the references on the chain, so `v.clear(); g()` was accepted (the old pipeline also missed it through a callee or a returned closure). Fix (docs/ir.md 6.9 "As built (follow-up F16.4)"): the run node follows the chain from σ(`CaptureHeld(k)`) of each such capture, as `deep_uses` of a call argument; the type test also looks into the fields of a struct and the payloads of an enum. Probes `tests/gate/probes/fixes/crr/` (claim C-RR; ledger `open-old` for the group-D probe `crr03_opfn.wf`, `moved` for `crr01_direct.wf`) | done (F16.4) |
| F19.1 | F19 | open items of group E after stage F19. I3-8 (W0503 for a `multi` operation in a scope body after a spawn statement): the construction verdict of `ir` §10.4 gives eight `new-fp` probes that run clean (the repro has the text of `c4_multi_scope_fail.wf`); decide the verdict or the probes. OR10: a call reads each place of its arguments, so a task that calls `grow_w(&w)` conflicts with a write of `w.score` (needs a precise part `reads`). RR12: W0304 when a closure or a clause gives a local its first value (groups C and D). RR4/V134: a scope capability that leaves its scope (the capability is a plain value in the analysis). Fallbacks: a `scope` in a closure body, a spawn on a scope parameter, a task that runs a value twice or a shared function variable that gets a new value | open |
| F19.2 | F19 | lost-fault W0502 / none in group C, found at stage F19 (scratchpad `f19/or3c1.wf`; the old pipeline rejects it). A function or a closure makes a closure that runs its capture two times (`fn wrap(f: fn()) -> fn() { \|\| { f(); f() } }`), and the caller gives it a `once` closure and runs the result one time (`let g = wrap(\|\| eat(b)); g()`): the run faults ("a value is used after it was moved"). Root cause: `transfer::apply_runs` gave `once_args` (the move of the value that holds a `once` closure, and the use at the second run) only to a run of a parameter. A `Made` closure holds the values of its captures in its own value (`made_held`), so a run of a capture moved nothing. Fix (docs/ir.md 6.6 "As built (follow-up F19.2)"): a capture of a `Made` closure that runs more than once gives the `once` value the operand of the run node (the value of the made closure) in `once_args`, also when an earlier run of the node applied the value one time (`wrap(wrap1(\|\| eat(b)))`). Probes `tests/gate/probes/fixes/c1once/` (class C1-ONCE, claim C1-ONCE; ledger `moved` for `c07`, `c12`, `changed` for `c06`) | done (F19.2) |
| F19.3 | F19 | the independent review of group E (scratchpad `ereview/review.md`). E-1 (blocker; lost-fault W0405 / none, the old pipeline rejects each program): a callee, a closure, a chain of callees or a closure in a second local that joins a task handle (part `joins`) ended the task at the `Main` node of the call, and the abort edge of the call leaves `Main` too. If the callee aborts before its `join` (a `fail`, a clause that does not resume, a failed scope of the callee) and a handler of the caller stops the abort, the code after the `handle` races the task. Fix (docs/ir.md 6.4 and 6.9 "As built (follow-up F19.3)"): the must part `abort_joins` of the summary (the handles that the body joins on each path to an `UnwindExit`); a call ends a task at `Main` only if the callee joins the handle on the abort paths too, else at `Ret` with its `lends_mut` at the normal `FrameEnd`; the abort edge of a terminator loses the task sites of the handles that it takes. ORACLE GAP: the fact oracle checks each `joined_at(T, n)`: when the run leaves `n` on any edge, each task of `T` of the run must be joined (`fact oracle (task end)`; the oracle follows the frames of scope bodies for this check). E-2 (FP): a closure that a callee runs at `Ret` starts its tasks at `Main` only if a linear value moves into the call there or another run of the call can run while the task runs. E-3 (FP): the part `ret.tasks` of a closure summary (the spawn sites whose handle `_0` holds). Probes `tests/gate/probes/fixes/e1/` (claims E-1, E-2, E-3); the clean twins of E-1 are lost-clean rows of the old pipeline and stay in `crates/weft-check/tests/data/tasks/e1_twins/` until a reviewer signs them. The review signed 8 `lost-clean` rows of stage F19 (ledger); 6 rows (`fixes/f18/join/k01`, `k03`, `k04`, `k05`, `k06`, `o39_joins`) wait for a second review | done (F19.3) |
| F19.4 | F19 | the second independent review of group E (scratchpad `ereview/review_r2.md`). R2-1 (blocker; a regression of the E-2 fix of F19.3, lost-fault W0312 / none for R04): a callee runs a closure that starts a task in a scope of the caller, then performs, fails, or calls code that does, and a clause of a local handler of the caller runs at the call while the task runs; the task started only at `Ret`, after the code of the clause at `Main`. The same gap held before F19.3 for a task that reads (old W0312, `ir` none) and for a value that a callee runs as a task while a clause runs. Fix (docs/ir.md 6.4 "As built (follow-up F19.4)"): `CallNodes::local_code`, the field `Run::then` of the part `runs`, and a start of the task on each edge into `Main` when the code of a local handler can run after the start. R2-2 (open-old, the old pipeline misses it too): a clause that ends a callee started from the state after the call, where a handle that the callee joins only on the normal path was not lost; `clause::call_clauses` now loses it (`transfer::given_tasks`). R2-5: the fact oracle checks the start of a task when a clause runs ("fact oracle (task start)"). Probes `tests/gate/probes/fixes/e1/r1_*`, `r2_*` (claims R2-1, R2-2); the 11 E-1 twins that the review signed move into the gate (claim E-1, sound). Not fixed (issues): R2-3 (`R44_returned_handle_task_inside_c`), R2-4 (`R15_loop_closure_fail_then_join_c`), R2-6 (`D7`) | done (F19.4) |
| F19.5 | F19 | issue #50 (R3-1 and R3-2 of the third review of group E, scratchpad `ereview/review_r3.md`; open-old: the old pipeline misses both) and issue #51 (R3-3 and R3-4). R3-2: a task of a callee changes a place while the callee waits at an operation that a handler of a caller handles, and the clause of the caller reads the place (W0312 catches only a clause that writes). R3-1: a callee of the scope function runs a closure that starts the task, then performs to a handler of a caller of the scope function (a regression of F19.3 against the flip). Fix (docs/ir.md 6.4 "As built (follow-up F19.5)"): the summary part `waits` (the places of the tasks that can run while the body waits at an operation of each effect), the wait nodes and the two tasks of a call that runs a clause of a local handler (`templates::WaitTask`). R3-3 and R3-4 (FP): a task of a late run started on the edges into `Main` and conflicted with its own run node, also on a branch; the clause now conflicts with the tasks of the wait nodes, and an abort starts the task at its `FrameEnd`. R3-6: the fact oracle checks the tasks of the callees when a clause runs ("fact oracle (task start)"; it failed on P15 and P19 with the facts of F19.4). Probes `tests/gate/probes/fixes/f195/` (claims R3-1, R3-2, R3-3, R3-4; ledger `changed` for `r33_clause_other_place_b`). Not fixed: R3-5 (`Q05_c`), R2-3, R2-4, and the precision loss of a value that performs before its spawn when the handler is in a caller (issue) | done (F19.5) |
| F20.1 | F20 | issue #47 (new-fp W0601 / none in the groups A and C; tier 1 `verify/partb/S4/p/c4_generic_clean.wf` `closure_in_some`, F20 self-attack `n03_wrap_closure_c`, tier 2 `verify/s5/R3x/p2/h6_option_closure.wf`). A linear closure in an `Option`: the type `Option<fn()>` has no linear part, so the arm `None` wrote no `Consume` (`irbuild/pattern.rs`, `Act::Finish` tested only `maybe_linear` of the type), the local stayed linear on that path, and `match o { Some(g) => g(), None => {} }` was W0601 at the end of the scope of `o`. Fix (docs/ir.md 5.13 "As built (follow-up F20.1)"): the arm of a variant with no payload also consumes a value with a function part if the root of the place is a temporary or a local with the flag `linear` from the analysis (not a capture: V9; not a struct pattern: a `_` over a function part does not move it). Probes `tests/gate/probes/fixes/f47/` (claim ISSUE-47), tests `ir_closures` and `ir_generics` (`option_payload.wf`); self-attack 22 pairs, 0 holes; 13 pairs in the gate. Not fixed: a linear closure in a payload of a user enum (`Job.Run(fn())`; `binding_props_of` reads only the type arguments, `mentions_fn`; the old pipeline rejects it too) | done (F20.1) |
| F20.2 | F20 | the independent review of group F at a813be3 (scratchpad `freview/review.md`). F-1 (blocker; lost-fault W0301, W0502, W0503 / none): an argument that a generic callee holds moved only at `Ret`, and a `once` closure (plain data in the IR) did not move; fix: the argument moves at `Main`, and a variable of the type argument (or of a linear or `once` closure in the argument) is live across a node of its own that gets the abort and the `multi` of `Main` (`templates::held_args`, `generic::held_var`, `held_node`, `copy_held`; `handlers::moved_at_main` moves it too). FP-1 (new-fp W0602): the type of the argument, not the type argument, gave the held value; fixed by F-1. F-2 (blocker; lost-fault W0405 / none): `back_tasks` (O3-9) ended each task of each handle argument of a type parameter; fix: only one parameter names a type parameter, it is not a reference, and the argument holds one task site. P-1 (lost-fault W0301 / none, not of group F): a move of a `ByMove` capture in a closure body did not free its places; fix: `moved_part` also for a move of the whole capture. P-2 (W0401, W0403 / none, not of group F): a `fork` branch that a closure body gives to a callee had no captures (the task was only pinned); fix: if the maker is the body that the template emits, the captures of the branch are checked as in a function body, through `alpha::capture_source` for a `Kept` or `ByRef` capture of the maker; no `kept` cell (RR4). The 18 tier-1 lost-clean rows of F20 and the tier-2 classes that the review marked SIGN are signed (`signed_by = "independent review of group F (freview/review.md)"`); `verify/s5/p/f1_closure_stash.wf` waits for the second review. Probes `tests/gate/probes/fixes/f20_2/` (claims F20.2-F1, -FP1, -F2, -P1, -P2), tests `ir_generics` (`held_args.wf`, `held_multi.wf`, `pick_handles.wf`), `ir_closures` (`nested_move.wf`), `ir_tasks` (`fork_in_closure.wf`). Not fixed: O-1 (a value of a type parameter can hold a reference), O-2 (`forks` of item values), O-3 (`!Move` through `Vec<T>.push`); the old pipeline misses them too | done (F20.2) |
| F20.3 | F20 | the second independent review of group F at 088dcdb and b6a417f (scratchpad `freview2/review.md`). B-1 (blocker; lost-fault W0302 / none; generic since F20.2, not generic also before group F): a clause of a local handler that uses an argument that the call moved; the uses of the clause were at the run node, the node of the move, and the spec gives `moved` only after it. Fix (`handlers::project`): a use of the clause of a variable that the run node moves goes to each successor of the run node too. I-2 (lost-fault W0502 / none; a hole before group F for a tuple, extended by F20 to generic calls): one `once` or linear closure in two operands of one node; fix (`templates::dup_moves`, at an assignment and at a call): each second move of a whole local is a move and a use in a part of the graph of its own. `verify/s5/p/f1_closure_stash.wf` is signed by the second review. The 98 tier-2 new-fp rows have entries of class `new-fp` (`precision`) with the issues #56 (N1), #57 (N2), #58 (N3) and #59 (N4). Probes `tests/gate/probes/fixes/f20_3/` (claims F20.3-B1, F20.3-I2), tests `ir_generics` (`clause_moved_arg.wf`) and `ir_closures` (`same_operand_twice.wf`). Open: the rule of the new-fp share counts the ledgered rows too, so tier 2 keeps that blocker; I-3 (`back_tasks` with two type parameters, precision) | done (F20.3) |
| F20.4 | F20 | the third independent review of group F at d1ddac6 (scratchpad `freview3/review.md`). B-2 (blocker; lost-fault W0301 / none; generic since F20, not generic also before group F): a clause reads a reference into an argument that the call moved; the fix of B-1 copied only a use of the moved variable. Fix (`handlers::late_uses`, after the owners and the versions of the parts): a use of the clause goes to each successor of the run node also if the variable points into a place that a move of the run node frees; a move of a part counts only if the clause accesses that part, and a use after a new value in the clause does not count (`handlers::exposed`; this also removes the false W0302 of I-10). I-8 (lost-fault W0302, W0502 / none): `dup_moves` compares whole places (`(p.0, p.0)`), takes the variable of a capture of a closure body, and runs at a perform. Probes `tests/gate/probes/fixes/f20_4/` (claims F20.4-B2, F20.4-I8), tests `ir_generics` (`clause_ref_moved_arg.wf`, `same_place_twice.wf`). Open: I-9 (a clause reads a reference into an element that the callee changed; both pipelines miss it), O-1 to O-3, I-3 | done (F20.4) |
| C1.1 | C1 | hole C1-H1 of the independent review of C1 (lost-fault W0502, W0503 / none; C1 made it): a callee runs a value of the caller that can resume more than once, then a `once` closure (`run_both(\|\| { pick() }, \|\| commit(t))`). The fix of #56 stopped the re-entry edges after code of a caller from making the later runs `many`, and the caller did not see the order of the runs. Fix: the part `after` of a run (`Run::after`, `Cycles::code_from`, `factgen::runs_after`): the values of the interface whose code of a caller comes before the run on a path back from a re-entry; `transfer::apply_runs` runs it again if a value that the caller gives for such a key is `multi` or performs a `multi` operation through a captured capability. Probes `tests/gate/probes/fixes/c1/h1_*.wf` (claim C1-H1), tests `ir_handlers` (`run_after_multi*.wf`), `ir_generics` (`run_after_multi_generic.wf`); the 202 variants of the review and the self-attack (`c1/att4`): 0 HOLE. The tier-2 rows of C1 do not change | done (C1.1) |
| C1.2 | C1 | holes C1-H2 and C1-H3 of the second review of C1 (lost-fault W0301, W0502, W0503 / none). H2 (C1 made it): a closure that a callee made runs a value that resumes two times, then a `once` capture; the `after` of C1.1 set `again`, but a capture of a made closure moves the value of the closure only for `many`. Fix: that move for each value of such a run too. H3 (older than C1): a callee runs such a value and gives a `once` closure argument out again (back, in a field, a struct, an `Option`, a tuple, a `Vec`, through a callee, in a made closure); the caller runs it two times. Fix: `templates::given_out` (a variable of the closure live across a node with the `multi` of the call, W0503; parts `ret.fns` and `put_fns`). Probes `tests/gate/probes/fixes/c1/h2_*`, `h3_*` (claims C1-H2, C1-H3), tests `ir_handlers` (`give_out_*.wf`, `made_run_after_multi.wf`); the variants `c1sign/v`, `c1sign/v2` and the self-attack `c1/att5`: 0 HOLE | done (C1.2) |
| C1.3 | C1 | hole C1-H4 of the third review of C1 (lost-fault W0502, W0503 / none; the form through a callee is a C1 regression, the direct call is older): a closure performs a `multi` operation through a captured capability, then runs or gives out a `once` closure (a capture, a parameter). Fix: the blocks after such a perform are in a cycle of the closure body (`frames::captured_multi_nodes`, `Cycles::add_captured`; no re-entry edge), a `ByMove` capture is a value in the value of the closure (a run again moves the closure), and a value call gives out a `once` closure of an argument or a capture again (`templates::captures_given_out`, `given_out`). Probes `tests/gate/probes/fixes/c1/h4_*` (claim C1-H4), tests `ir_handlers` (`h4_*.wf`); `c1sign/v3` and the self-attack `c1/att6`: 0 HOLE (2 old misses of fallback programs stay) | done (C1.3) |

| C1.4 | C1 | the cost criterion (§2.7.4, issue #62). Causes: each test of the chain of a `match` gave each variant test variable of the scrutinee a new value (`rebound_at`, `points_into`: quadratic); rows that no rule reads (the `rebound_at`, `empty_at`, `uses`, `scope_end` of temporaries of plain data, the `reads_at` and `owner` rows of place trees that no reference or task reaches, edges through nodes with no fact, the places of such trees); quadratic passes (`handlers::exposed` built the predecessors of the whole graph for each use of a clause, `late_uses` read all rows for each use, `frames::cyclic` walked from each block, `Weights::count` read all runs for each handler, `handlers::spliced` for each clause, `receiver_ref` searched the body for each call, `Vars::variant_tests` searched its list for each key, `sig::Inferred::join` compared each changed place with each other one, `clause::finish_handle` walked the parent chain for each local, the type table copied its effects for each body, `State::remove_bodies` read each local, and a join of states copied the chunks that it did not share). Fixes: a test binds only the `W` variables of the variants that its `Switch` selects (`templates::selected_variants`); `factgen::prune` (`docs/ir.md` 6.2; ADR 0013); indexes for the passes, Tarjan's components, shared chunks and shared type declarations. The verdicts do not change (tier 1: each program has the same diagnostics and violations; `agreement_random` `pruned_facts_give_the_same_violations`). Test `scale.rs` `the_ir_facts_have_at_most_three_times_the_rows_of_the_old_facts` | done (C1.4) |
| C1.4b | C1.4 | the rows of `unbound_at_aborts` (#62): the facts of the abort shape of `verify/s5/S5a/x/p/scale_ops.wf` and `s5r/p/scale400.wf`: `handlers::unbound_at_aborts` gives each captured local of a handled body that no path to an abort has assigned a new value at the `AbortValue` node of each such abort (a quadratic number of `rebound_at` rows: 22.6 and 6.4 times the old rows). Fix (`docs/ir.md` 6.2, "As built (plan stage C1.4b)"): the generator keeps the rows (the precision of `scale400.wf` stays), and a last step of the prune, `share_new_values`, puts the rows of the nodes that lead to one node and give nested sets of variables new values on one chain of new nodes, with one row for each variable; the module text of `factgen/prune.rs` gives the argument for each rule that reads `rebound_at`. No rule of the spec changes. Rows: `scale_ops.wf` `many` 1 154 311 to 30 061 (0.59 times the old rows), `scale400.wf` `many` 87 861 to 8 061 (0.59 times); `check` CPU time of `scale_ops.wf` 7.6 s to 4.4 s (old 0.8 s), of `scale400.wf` 0.50 s to 0.34 s (old 0.07 s). Quadratic passes of the profile (callgrind) that this stage fixes: the order of the work list of `handlers::assigned`, `clause::captured_locals` for each abort (now once for each body), a copy of a large value for each join that does not change it (`Tree::includes`), and a copy one by one of the locals of a chunk that the other state has none of (`Chunked::adopt_missing`, the kept values along a cleanup chain). Open: a call of a closure local with `n` closure values computes `reach_refs` of the callee for each value (`transfer::value_out_ty`, `apply_value`); the shared search of `rules::invalidation` visits a quadratic number of nodes on this shape (as at C1.6); the effect inference of the old lowering (`body::Lower::join_fn`). Gates: tier 1 `snapshot --facts ir` the same diagnostics and violations as C1.6 for each of 4526 programs (tier 2: each of 57393); tier 1 0 blockers, each class and each row as C1.6; tier 2 (2 workers) 0 blockers, new-fp 12, the list of the programs that are not `same` as C1.6; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `weft agree --facts=ir` agrees on the corpus, the interpreter programs and the examples. Functions over the bound of ADR 0013: 0 (C1.6: 2). Tests: `agreement_random` `shared_new_values_give_the_same_violations`, `scale.rs` (the abort shape in the row bound), `prune::tests` | done (C1.4b) |
| C1.5 | C1.3 | the reviews of C1.3: holes C1-H5 and C1-H6, gaps G1 to G5 (lost-fault W0502, W0503 / none; G1 and G4 are older than C1, the old pipeline misses G4). The rule of #56 is an allow-list now (`docs/ir.md` 5.20, "As built (stage C1.5)"): a run of a value of the interface is `many` where a cycle or a re-entry edge reaches it, except where the exceptions E1 to E4 hold, with a proof sketch. Step 1 restored the rule of ec00112 (each re-entry edge makes the runs after it `many`); step 2 fixed the gaps: G1 a nested body runs again where its site is in a cycle (`Cycles` reads the chain of sites), G2/H6 the walk after a row goes through the spliced graph (into a nested body, up to its site), H5 a closure that a callee made holds the values of its captures (`made_held` in `captures_given_out`, `capture_fns`), G3 the key of a run has the part `result` and a result of a closure gives back the values that the closure holds, G4 (issue #68) a stated row is no bound for `multi` of code of a caller, G5 a key with no values is `multi` and the test reads the values that each value runs (`Apps::inner`); step 3 brought the precision back (E1 to E4; a run after a value of the interface of the caller gets its key in `after`, not `again`). The two parts of the analysis that do not find the rows of a body (a clause body, a handler in a closure body) stay with the old pipeline; tests pin both fallbacks. Tier-2 new-fp: 85 after step 1, 85 after step 2, 12 after step 3 (the 12 rows of C1). The 4 rows of the review of issue #67 with a condition are signed (each H5, H6 and H6c variant is W0502 or W0503). Cost of G4: W0503 at 5 control lines of `39_multi_params.wf` and `81_generic_holds.wf` (marker `ir:`), and 3 tier-2 rows that do not run. Probes `tests/gate/probes/fixes/c1/c15_*` (claims C1-G1, C1-H5, C1-H6, C1-G3, C1-G4), tests `ir_handlers` (data `handlers/c15/`) | done (C1.5) |
| C1.6 | C1.5 | issue #71: holes C1-HA, C1-HB and C1-HC of the review of C1.5 (lost-fault W0503 / none; older than C1; the old pipeline catches HB and HC, and misses most HA forms). In each hole a `once` closure runs a second time after a `multi` operation resumes two times. HA and HB (cause): the flag `once` of the variable of a local of a function type came only from the old analysis (`binding_props_of`), which does not follow a closure through a destructure of a call result, a projection of a call, a binding of a `match` arm, a temporary, or a store into a part (`s.o = Some(g)`, `put(g, &s)`). Fix (`docs/ir.md` 5.20, "As built (stage C1.6)"): each template that gives a local a value calls `templates::mark_fn_once` (the analysis of the IR gives the flag, as `mark_fn_linear_in` gives `linear`), also for the parts `put_fns` and the changed places of a callee; this covers tuples, structs, enum payloads, nested structs, `Box` and `Vec`. HC (cause): the node of a value that `given_out` gives out got the `multi` of `Main` only, but a late run of a value of an argument is at `Ret` (the guess of the review about struct fields was wrong). Fix: `held_like_call` (`Main` and `Ret`). Six programs of the test data get one more W0503 at a line that has an error already (`opt_run`, `tup_run`, `struct_run`, `res_made`, `run_once_multi`, `give_out_field`: the callee holds the `once` argument across the late run). The review sets `r67b/att`, `r67b/v`, `r67b/z`: 0 HOLE (`e04_tuple_res.wf` stays with the old pipeline, which misses it too); the earlier sets: no change. The 8 tier-2 rows of #67 that wait: each variant v06, v07, v08, v11 and v12 is W0502 or W0503 now (not signed). Gates: tier 1 0 blockers; tier 2 new-fp 12 of 12548 (0.096 %, the rows of C1.5; each tier-2 row has the class of C1.5); reg_204 as C1.5; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry. Probes `tests/gate/probes/fixes/c1/c16_*` (claims C1-HA, C1-HB, C1-HC), tests `ir_handlers` (data `handlers/c16/`) | done (C1.6) |
| C2 | C1 | the fresh sweep (`weft-gate sweep`, 50 000 programs from each of the seed bases 1 000 000 and 2 000 000): lost-fault W0301 / none of a part of a tuple result into an `rc` object (gen4 seed 1002955; fix `apply::stated_places`, claim C2-TUPLE-RC, probes `sweep/c2_tuple_rc_*`); F3-6 (both pipelines accept; issue #73, ledger `edge`, probe `sweep/c2_spawn_linear_no_abort.wf`). The last sweep: 3 accepted faults, each the shape of issue #73. Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 of 12548 (0.096 %), each class count as C1.6; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry | done (C2) |
| C3 | C2 | the switch of the defaults (`--facts=ir` with all groups, `--engine=ir`): no difference of the gate; the corpus markers give the `ir` result (`old:` for the old pipeline); the core IR targets O3-5, O3-6, R3RT2 and R3RT3 move to the corpus; the baselines `tests/gate/baseline-c3.jsonl` and `target/gate/baseline-c3-tier2.jsonl` (`tests/gate/baseline-c3-tier2.sha256`). Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %); fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `weft agree` on 220 programs; `sweep --n 2000 --seed-base 3000000` 0 accepted faults | done (C3) |
| R0b | C3 | the fallbacks of a callee with no IR (C3, E6, P1, C1 with a type error), N1 and I1 (Phase R, R0b): a worst-case summary from the declaration, W0121, a handler with no clause passes the operation on. Fallbacks 331/7770 to 318/7382 (tier 1 / tier 2). Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry | done (R0b) |
| R0c | R0b | the fallbacks A1, A2 and B1 (Phase R, R0c): W0204 for a reference through a local `rc` handle that is not sure to be a copy of the handle parameter of the store (`templates::same_object`), the region of a `resume` skips the runs of a clause in a task that W0314 rejects, rule 5 of the widening (a summary part below depth 8). Fallbacks 318/7382 to 312/7372 (tier 1 / tier 2). Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `ev.sh` 0 HOLE on the 19 programs that come into scope | done (R0c) |
| R0d | R0c | handlers in closure bodies (Phase R, R0d; D2, C5, and the two pass-on shapes of R0b): a handled body splices into the closure body and the clauses are parts of the facts of the closure (`closure_units`), the closure summary carries the code of the handlers in the terms of its interface, `clause::serving` for a handler with no clause for an operation (it closes three holes of the pipeline of R0c, `fixes/r0d/ph1`, `ph3`, `ph5`), a capability that a closure of a closure captures again, the sparing at `Post` when the rest of the handled body cannot abort (issue #57). D5 and C8 stay (design note in R0d). Fallbacks 312/7372 to 279/4981. Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `ev.sh` 0 HOLE on the 669 programs that come into scope or change and on the review sets of group D and of the once-after-multi family. The review found three holes (an operation that a handler with no clause passes on, performed through a callee, a value or an inner closure): fixed in the second commit (`clause::serving_path`, `frames::served_dests`), which also closes the function-body form of R0c (`pi_ph5_direct_callee.wf`); the reviewer signed the lost-clean rows | done (R0d) |

Some stages are larger than a few hours. If such a stage does not fit its box, rule 5
splits it at these points (each part keeps the gates; the code of a later part stays
behind its group):

| Stage | First part | Second part |
| --- | --- | --- |
| T3 | `expr_ty`, `pat_ty`, `binding`, `res`, `call` with D0 (a) to (c) | `adjust`, `field`, `int_ty`, `closure`, `handle`, `effect` with D0 (d), (e) |
| B10 | `Handle`, the handled body, the `Cap` local, upvar locals, a local perform | clauses, `Kont`, `Resume`, `Kont` fields of a closure, nested handlers |
| I1 | slots, temporary cells, `Live`, `Dead`, `Assign`, operands, places, `Binary`, `Switch` | aggregates, `Iter`, `IterNext`, calls of items, `Print`, `Assert`, back edges |
| F6 | `summarize` and the call-graph fixpoint (no rows) | effect rows, `to_effect_sig`, the signature diff of the gate |
| F14 | the splice and `Exit` | resume points, `pre` and `post`, `Post` |
| F16 | `Resume` and the continuation summary | re-entry edges and `Copy` |

Gate record (filled at G6, F8, F10, F13, F17, F19, F20, C1, C2):

| Stage | Programs in scope | same | fixed | new-fp | lost-clean | moved | changed | open (ledgered) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| G6 (baseline) | | | | | | | | |
| F8 (tier 1, group A) | 1184 of 3394 | 3235 | 12 | 0 | 5 (signed) | 8 | 61 | 73 (open-old) |
| F8 (tier 2, group A) | 2560 of 57393 | 56867 | 10 | 0 | 6 (5 signed; `verify/s5/R3a_diff/blk.wf` needs a reviewer) | 11 | 411 | 88 (tier-2 policy; 2 in scope: open-old `unclassified`) |
| F10 (tier 1, groups A and B) | 1373 of 3509 | 3263 | 47 | 0 (`pt09` of the review: a precision loss, test `ir_loops`, track P1) | 18 (signed) | 37 | 71 | 73 (open-old) |
| F10 (tier 2, groups A and B) | 2852 of 57393 | 56822 | 10 | 0 | 8 (signed) | 16 | 449 | 88 (tier-2 policy) |
| F13 (tier 1, groups A to C) | 2154 of 3893 | 3411 | 117 | 1 (`fixes/f12c/n2/tw.wf`, map N2, `stricter`) | 45 (signed) | 67 | 185 | 67 (open-old) |
| F13 (tier 2, groups A to C) | 4049 of 57393 | 56527 | 19 | 1 (`verify/s5/r2a/t/ln1.wf`, map N2, `stricter`) | 35 (signed) | 66 | 666 | 79 (tier-2 policy) |
| F17.1 (tier 1, groups A to D, default) | 2846 of 4169 | 3554 | 159 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 57 (signed; 12 by the second review of group D) | 88 | 254 | 56 (open-old) |
| F17.1 (tier 2, groups A to D, default) | 5043 of 57393 | 56303 | 34 | 2 (`ln1.wf`, stricter; `verify/s5/R3x/p2/h6_option_closure.wf`, precision) | 44 (signed) | 91 | 855 | 64 (tier-2 policy) |
| F17.2 (tier 1, groups A to D, default) | 2877 of 4201 | 3580 | 165 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 57 (signed) | 89 | 253 | 56 (open-old) |
| F17.2 (tier 2, groups A to D, default) | 5041 of 57393 | 56307 | 34 | 2 (as F17.1) | 44 (signed) | 92 | 850 | 64 (tier-2 policy) |
| F19 (tier 1, groups A to E, default) | 3468 of 4227 | 3503 | 180 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 71 (57 signed; 14 group-E rows wait for an independent signature) | 107 | 323 | 42 (open-old) |
| F19 (tier 2, groups A to E, default) | 6730 of 57393 | 55613 | 51 | 2 (as F17.1) | 49 (44 signed; 5 wait for a signature) | 131 | 1500 | 47 (tier-2 policy) |
| F19.2 (tier 1, groups A to E, default) | 3500 of 4259 | 3528 | 184 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 71 (57 signed; the 14 group-E rows of F19 wait for a signature) | 109 | 324 | 42 (open-old) |
| F19.3 (tier 1, groups A to E, default) | 3522 of 4281 | 3551 | 184 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 71 (65 signed; the 6 rows `fixes/f18/join/k01`, `k03`, `k04`, `k05`, `k06`, `o39_joins` wait for a second review) | 109 | 323 | 42 (open-old) |
| F19.3 (tier 2, groups A to E, default) | 6729 of 57393 | 55614 | 51 | 2 (as F17.1) | 49 (signed) | 131 | 1499 | 47 (tier-2 policy) |
| F19.4 (tier 1, groups A to E, default) | 3545 of 4304 | 3555 | 188 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 82 (signed; the second review of group E signed the 6 rows of F19.3 and 11 clean twins of E-1) | 109 | 327 | 42 (open-old) |
| F19.4 (tier 2, groups A to E, default) | 6730 of 57393 | 55614 | 51 | 2 (as F17.1) | 49 (signed) | 131 | 1499 | 47 (tier-2 policy) |
| F19.5 (tier 1, groups A to E, default) | 3581 of 4340 | 3577 | 201 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 82 (signed) | 109 | 328 | 42 (open-old) |
| F19.5 (tier 2, groups A to E, default) | 6730 of 57393 | 55614 | 51 | 2 (as F17.1) | 49 (signed) | 131 | 1499 | 47 (tier-2 policy) |
| F20 (tier 1, groups A to E, default) | 3585 of 4357 | 3592 | 202 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 82 (signed) | 109 | 328 | 43 (open-old) |
| F20 (tier 1, groups A to F, default after the flip) | 3973 of 4357 | 3502 | 236 | 2 (`tw.wf`; `verify/partb/S4/p/c4_generic_clean.wf`, issue 47, precision: over the 0.1 % share) | 100 (82 signed; 18 wait for an independent signature) | 122 | 386 | 9 (open-old) |
| F20 (tier 2, groups A to E, default) | 6730 of 57393 | 55614 | 51 | 2 (as F17.1) | 49 (signed) | 131 | 1499 | 47 (tier-2 policy) |
| F20 (tier 2, groups A to F, default after the flip) | 46950 of 57393 | 44263 | 88 | 104 (6 ledgered; 98 precision losses of the groups A to E in programs that the generic `id` of a shared header kept out of scope: they need an issue) | 2523 (49 signed; 2474 wait for an independent signature: most give the diagnostics of the groups A to E on the program with `id` inlined, 62 are the `join` through `id` of O3-9) | 1594 | 8811 | 10 (open-old) |
| F20.1 (tier 1, groups A to F, default) | 3999 of 4383 | 3528 | 236 | 1 (`fixes/f12c/n2/tw.wf`, ledgered; `c4_generic_clean.wf` is `same` now) | 101 (82 signed; 19 wait for an independent signature: the 18 of F20 and `verify/s5/p/f1_closure_stash.wf`, which was `changed` with the W0601 of issue 47) | 124 | 384 | 9 (open-old) |
| F20.1 (tier 2, groups A to F, default) | 46951 of 57393 | 44265 | 88 | 103 (`h6_option_closure.wf` keeps its W0602 only; `c4_generic_clean.wf` is `same`) | 2524 (as F20, and `verify/s5/p/f1_closure_stash.wf`) | 1594 | 8809 | 10 (open-old) |
| F20.2 (tier 1, groups A to F, default) | 4023 of 4407 | 3548 | 236 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (100 signed: the 18 of F20 by the review of group F; `verify/s5/p/f1_closure_stash.wf` waits for the second review) | 124 | 388 (+4: the `f20_2` probes, ledgered) | 9 (open-old) |
| F20.2 (tier 2, groups A to F, default) | 46951 of 57393 | 44347 | 88 | 103 (as F20.1: 98 precision losses of the groups A to E with no issue yet, over the 0.1 % share) | 2451 (2450 signed by the review of group F; the 70 W0401/W0403 rows that it refused are `same` or `changed` now (P-2), and 3 W0301 rows are `same` (P-1); `f1_closure_stash.wf` waits) | 1597 | 8797 | 10 (open-old) |
| F20.4 (tier 1, groups A to F, default) | 4057 of 4441 | 3579 | 237 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 124 | 390 | 9 (open-old) |
| F20.4 (tier 2, groups A to F, default) | 46951 of 57393 | 44347 | 88 | 103 (98 with issues #56 to #59; over the 0.1 % share) | 2451 (signed) | 1597 | 8797 | 10 (open-old) |
| C1 (tier 1, groups A to F, default) | 4082 of 4466 | 3604 | 238 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 124 | 389 | 9 (3 `open` F3-6 "stays"; 4 `edge`: #41 three, #48 one; 2 `open-old` with no issue: `h3_div_min`, `c14_big`) |
| C1 (tier 2, groups A to F, default) | 46958 of 57393 | 44728 | 88 | 12 of 12548 (0.096 %: 4 `stricter` `h0` rows, 3 precision rows of #57 to #59, the 5 of F20 and before) | 2476 (2451 signed; 25 new rows wait for an independent signature) | 1608 | 8471 | 10 (4 `open` F3-6; 4 `edge` #48; 2 `open-old`: `h3_div_min`, `c14_big`) |
| C1.1 (tier 1, groups A to F, default) | 4090 of 4474 | 3604 | 238 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 124 | 397 (+8: the `h1` probes, ledgered) | 9 (3 `open` F3-6; 6 `edge`: #41 three, #48 one, #63 two) |
| C1.1 (tier 2, groups A to F, default) | 46958 of 57393 | 44728 | 88 | 12 of 12548 (0.096 %, as C1) | 2476 (2459 signed; the 17 that the review of C1 refused wait) | 1608 | 8471 | 10 (4 `open` F3-6; 6 `edge`: #48 four, #63 two) |
| C1.2 (tier 1, groups A to F, default) | 4100 of 4484 | 3604 | 239 (+1: `h3_ret_first_b`) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 124 | 406 (+9: the `h2`/`h3` probes, ledgered) | 9 (as C1.1) |
| C1.2 (tier 2, groups A to F, default) | 46958 of 57393 | 44728 | 88 | 12 of 12548 (0.096 %, as C1) | 2476 (2469 signed; 7 refused by the second review of C1 wait) | 1608 | 8471 | 10 (as C1.1) |
| C1.3 (tier 1, groups A to F, default) | 4106 of 4490 | 3604 | 240 (+1: `h4_param_b`) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 124 | 411 (+5: the `h4` probes, ledgered) | 9 (as C1.1) |
| C1.3 (tier 2, groups A to F, default) | 46958 of 57393 | 44728 | 88 | 12 of 12548 (0.096 %, as C1) | 2476 (2464 signed; 12 wait: the 7 refused rows and the 5 whose signature the third review withdrew) | 1608 | 8471 | 10 (as C1.1) |
| C1.4 (tier 1, groups A to F, default) | 4106 of 4490 | 3604 | 240 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 124 | 411 | 9 (as C1.1); each program has the class and the diagnostics of C1.3 |
| C1.4 (tier 2, groups A to F, default) | 46958 of 57393 | 44728 | 88 | 12 of 12548 (0.096 %, as C1) | 2476 (12 wait, as C1.3) | 1608 | 8471 | 10 (as C1.1); the classes and the blockers of C1.3 |
| C1.5 (tier 1, groups A to F, default) | 4127 of 4511 | 3610 (+8 probes; `81_generic_holds.wf` and the copy of `h_multi.wf` leave) | 242 (+2: `c15_g_row_fwd_b`, `c15_h6_oldmiss_min_b`) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 125 (+1: `r2/redteam/p/h_multi.wf`, G4, ledgered) | 423 (+12: 11 `c15` probes and `81_generic_holds.wf` of G4, ledgered) | 9 (as C1.1) |
| C1.5 (tier 2, groups A to F, default) | 46958 of 57393 | 44710 (-18: G4, mostly mutants of `39_multi_params.wf` and `81_generic_holds.wf`; ledgered) | 88 | 12 of 12548 (0.096 %, the rows of C1) | 2476 (2468 signed; the 8 rows that the review of issue #67 refused wait) | 1610 (+2: G4, ledgered) | 8487 (+16) | 10 (as C1.1) |
| C1.6 (tier 1, groups A to F, default) | 4142 of 4526 | 3615 (+5: the 4 `c16` clean probes and `c16_hb_store_b`) | 245 (+3: `c16_ha_tuple_b`, `c16_ha_proj_b`, `c16_ha_nested_b`) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 125 | 430 (+7: the other `c16` probes, ledgered) | 9 (as C1.1) |
| C1.6 (tier 2, groups A to F, default) | 46958 of 57393 | 44710 | 88 | 12 of 12548 (0.096 %, the rows of C1; each row and class as C1.5) | 2476 (2468 signed; the 8 rows of issue #67 wait) | 1610 | 8487 | 10 (as C1.1) |
| C1.4b (tier 1, groups A to F, default) | 4142 of 4526 | 3615 | 245 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 125 | 430 | 9 (as C1.1); each program has the class, the diagnostics and the violations of C1.6 |
| C1.4b (tier 2, groups A to F, default) | 46958 of 57393 | 44710 | 88 | 12 of 12548 (0.096 %, the rows of C1) | 2476 (each signed) | 1610 | 8487 | 10 (as C1.1); each program has the class, the diagnostics and the violations of C1.6 |
| C2 (tier 1, groups A to F, default) | 4147 of 4531 | 3619 (+4: the `sweep/c2_tuple_rc_*` probes; the `_b` probes are W0301 in both pipelines) | 245 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 125 | 430 | 10 (as C1.1, and `sweep/c2_spawn_linear_no_abort.wf`: `edge`, issue #73) |
| C2 (tier 2, groups A to F, default) | 46958 of 57393 | 44710 | 88 | 12 of 12548 (0.096 %, the rows of C1) | 2476 (each signed) | 1610 | 8487 | 10 (as C1.1) |
| C3 (tier 1, groups A to F, the new defaults) | 4147 of 4531 | 3619 | 245 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 125 | 430 | 10 (as C2); each program has the class of C2; the 30 corpus files with `old:` markers and the 4 targets that moved to the corpus have the old records of C2 with other lines and paths only |
| C3 (tier 2, groups A to F, the new defaults) | 46957 of 57393 (one more check timeout at the limit of 60 s on a loaded machine) | 44710 | 88 | 12 (0.096 %, the rows of C1) | 2476 (each signed) | 1610 | 8487 | 10 (as C1.1); each row has the class and the entry of C2 |
| R0b (tier 1, the defaults) | 4163 of 4534 | 3602 | 246 (+1: `182_handler_no_clause.wf`) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 125 | 449 (+19: programs that come into scope, W01xx in both) | 10 (as C3) |
| R0b (tier 2, the defaults) | 47345 of 57393 | 43735 | 88 | 12 (0.096 %, the rows of C1) | 2476 (each signed) | 1605 | 9467 | 10 (as C3) |
| R0c (tier 1, the defaults) | 4172 of 4537 | 3603 (+1: the new corpus files 185 and 186; `t03_items.wf` leaves) | 248 (+2: `184_rc_handle_copy.wf`, `a13_nested_rc_rc_b.wf`) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 101 (signed) | 125 | 450 (+1: `t03_items.wf`, ledgered) | 9 (the `edge` entry of issue #41 is gone) |
| R0c (tier 2, the defaults) | 47355 of 57393 | 43731 | 88 | 12 (0.096 %, the rows of C1) | 2476 (each signed) | 1605 | 9471 (+4, ledgered) | 10 (as C3) |
| R0d (tier 1, the defaults) | 4237 of 4569 | 3612 | 251 (+3: `188_captured_pass_on.wf`, `fixes/r0d/ph1`, `ph7`) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 108 (+7, ledgered; `signed_by` UNSIGNED, the review signs) | 128 (+3, ledgered) | 460 (+10, ledgered) | 9 |
| R0d (tier 2, the defaults) | 49747 of 57393 | 42437 | 88 | 12 (0.096 %; `p43563.wf` leaves, `p23249.wf` comes, issue #56) | 2853 (+377; 371 in six classes of R0d, `signed_by` UNSIGNED) | 1707 | 10286 (ledgered) | 10 (as C3) |
| R0d fix (tier 1, the defaults) | 4265 of 4597 | 3628 | 260 (+9: corpus 189 and the probes of the review holes, `fixes/r0d/pi*`) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 108 (signed by the review of R0d) | 128 | 463 (+3, ledgered) | 9 |
| R0d fix (tier 2, the defaults) | 49747 of 57393 | 42437 | 88 | 12 (0.096 %, as R0d) | 2853 (signed by the review of R0d) | 1707 | 10286 | 10 (as C3) |
| R0d fix 2 (tier 1, the defaults) | 4274 of 4606 | 3635 | 262 (+2: `fixes/r0d/pj_b9c_*` and `pj_b9d_*`, which both pipelines missed) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 108 (signed) | 128 | 463 | 9 |
| R0d fix 2 (tier 2, the defaults) | 49747 of 57393 | 42437 | 88 | 12 (0.096 %, as R0d) | 2853 (signed) | 1707 | 10286 | 10 (as C3) |

Cost at C1 (§2.7.4, release, tier 1, the 4112 single-file programs in scope, one process
for each check): `check` takes 32.6 s with the old facts and 72.0 s with the `ir` facts
(2.2 times; the limit is 2 times). 10617 of 37667 functions have more than 3 times the
facts of the old pipeline (1436 of them with 20 or more old facts; the largest factor is
46 on `verify/s5/S5a/x/p/scale_ops.wf`). In `scale.rs` (release) the `ir` check of
`many_variants(8000)` takes 28 s (old 0.27 s): each test of the chain of a `match` gives
each part variable of the scrutinee a new value. The criterion does not hold (issue #62).

Cost at C1.4 (follow-up C1.4; the definition of ADR 0013; release; the 4136 single-file
programs of tier 1 in scope; one process for each check; CPU time, user and system, of
the process; scripts `c14/cost3.py` and `c14/crit.py` of the scratchpad):

| Measure | C1.3 (e1902fb) | C1.4 |
| --- | --- | --- |
| tier 1 `check`, CPU time, old / `ir` | 38.0 s / 79.6 s (2.10 times) | 37.9 s / 62.4 s (1.65 times) |
| tier 1 `check`, wall time, old / `ir` | 41.2 s / 83.0 s (2.02 times) | 41.6 s / 65.9 s (1.59 times) |
| rows of all functions, old / `ir` | 1 887 499 / 6 632 522 (3.51 times) | 1 887 499 / 2 465 536 (1.31 times) |
| functions over 3 times the old rows (of 37 787) | 10 674 (1 468 with 20 or more old rows) | 493 (460 with 1 to 4 old rows; 26 with 20 or more) |
| functions over 3 times the old rows plus 64 (the bound of ADR 0013) | 102 | 2 (`scale_ops.wf` `many`, 22.6 times; `s5r/p/scale400.wf` `many`, 6.4 times: follow-up C1.4b) |
| `scale_ops.wf` `many`: rows; `check` time | 2 331 262 (45.7 times); 14.9 s (old 0.8 s) | 1 154 311 (22.6 times); 8.6 s |
| `edge/chain*.wf`, `n100.wf` `f`, `154_unset_nested.wf` `mk_chain` | 36 to 42 times; 995 rows (old 1); 128 rows (old 2) | 0 or 1 row; 0 rows; 60 rows (in the fixed part) |

`scale.rs` (`many_locals_check_in_time`, release, in one process; the C1 column is the
record of stage C1):

| Shape | C1 `ir` | C1.4 `ir` | old |
| --- | --- | --- | --- |
| `blocks` (4000) | 2.9 s | 1.3 s | 0.6 s |
| `types` (3200) | | 0.11 s | 0.06 s |
| `fields` (16000) | 2.5 s | 1.1 s | 0.4 s |
| `variants` (8000) | 28 s | 1.0 s | 0.2 s |
| `handlers` (4000) | 1.9 s | 1.8 s | 0.4 s |

The time criterion holds (1.65 times the old time). The facts criterion holds for each
function but the two of follow-up C1.4b. `scale.rs` and `limits.rs` pass with `--facts=ir`.

Cost at C1.4b (the same method; the 4172 single-file programs of tier 1 in scope at
C1.6; the two columns are measured one after the other on the same machine):

| Measure | C1.6 (304883e) | C1.4b |
| --- | --- | --- |
| tier 1 `check`, CPU time, old / `ir` | 39.3 s / 63.4 s (1.61 times) | 35.3 s / 54.9 s (1.55 times) |
| rows of all functions, old / `ir` | 1 891 878 / 2 469 068 (1.31 times) | 1 891 878 / 1 264 807 (0.67 times) |
| functions over 3 times the old rows (of 37 942) | 493 (26 with 20 or more old rows) | 491 (24 with 20 or more old rows) |
| functions over 3 times the old rows plus 64 (the bound of ADR 0013) | 2 | 0 (the largest: `116_rc_stores.wf` `main`, 453 rows, old 135) |
| `scale_ops.wf` `many`: rows; `check` CPU time | 1 154 311 (22.6 times); 7.6 s (old 0.8 s) | 30 061 (0.59 times); 4.4 s |
| `s5r/p/scale400.wf` `many`: rows; `check` CPU time | 87 861 (6.4 times); 0.50 s (old 0.07 s) | 8 061 (0.59 times); 0.34 s |

The facts criterion holds for each function (issue #62).

---

## 6. Track P: precision and proofs (after R5)

These stages are not on the path of the migration. Each one is one commit with the same
rules. They follow `ir §9` and §11.

| Id | Title | Work | Exit |
| --- | --- | --- | --- |
| P1 | Reference versions | One fact variable for each definition of a move path that can hold a reference; a use uses the versions that reach it; a later definition makes an old version unbound (`rebound_at`); a re-entry `Copy` rebinds a version only if all its places are in the copied frames (`ir §9.6`). Files: `factgen/vars.rs`, `factgen/templates.rs`, `analysis/domain.rs`. | the gate (all tiers) has no `lost-fault`, J4 stays rejected, and the STATE false positives OL-NR-flow, OL-R2b-holds, V069, R3RT10 and the J3 variant `resume; u.clear(); &u[0]` are accepted |
| P2 | The verified fact kernel | Move `factgen/kernel.rs` (the templates of `Borrow`, `Child`, `Copy`, `Read`, `Write`, `Call`, `MkClosure`, `Invoke`, `Alloc`, `Free`) into `crates/weft-verified/src/factgen.rs` as Verus code; sema calls it; `proofs/link/src/lib.rs` includes it with `#[path]`; `proofs/link/check-copies.sh` lists it. | `proofs/verify-all.sh`; no gate difference |
| P3 | L0: `ir_wf` | The rules V1 to V7 and V12 move into `crates/weft-verified/src/ir_wf.rs` as exec Verus code over a small mirror of a body, with a spec `ir_wf` and the proof `ir_wf_check(body) == true ==> ir_wf(body)`; `weft_ir::verify` calls it; `proofs/link/src/lib.rs` includes it with `#[path]` and `check-copies.sh` lists it (the link includes only Verus code, `ir §9.7`). | `proofs/verify-all.sh`; the old and the new verifier agree on the corpus; a vacuity guard and a mutation row |
| P4 | L2-IR | The embedding of `ir §9.1` with the two-node call; `facts(ir) == link_facts(embed(ir))` for the B1 relations, with versions. | `proofs/verify-all.sh`; the hypotheses `facts_ok`, `bound_before_use`, `no_gen_kill` become lemmas for the fragment |
| P5 | B1+ and L2-free | `Alloc`, `Free`, `FreeSub` in `proofs/borrowing/src/cfg.rs` and `model.rs`; the join lemma of the sets of locals; L2 with `frees_at`. | `proofs/verify-all.sh`; mutation rows |
| P6 | The effects model order and moves | `max_slot` compares slots; `Call { block, caps, moves }`; `inv_b` (`own.rs`, `own_steps.rs`), L3 (`unwind_linked` in `proofs/link/src/lifecycle_link.rs`), the examples and the mutation tables follow. | `proofs/verify-all.sh` |
| P7 | The effects CFG lift and L4 | The join of `SS` (`env` equal, `lin` equal, `k` the conjunction); L4: acceptance of W0601, W0602, W0501, W0503 on the facts implies `check(embed_eff(program))` for the fragment with no tasks. | `proofs/verify-all.sh` |
| P8 | B1 closure values and L2-clo | A B1 extension for closure values as call arguments; L2 with `MkClosure` and `Invoke`. | `proofs/verify-all.sh` |

---

## 7. Estimates and risks

**Size.** About 23 500 new lines of code (THIR recorder and `typeck` 4 500, IR crate
2 500, builder 6 000, analysis 3 500, summaries 2 000, fact generator 2 500, checks 600,
`compile_ir` and landing pads 1 800) and 3 000 lines of tests, plus the gate crate (about
1 500). About 21 000 lines go away (`body/`, `compile.rs`, the re-lowering of `infer.rs`).

**Time.** 57 stages of a few hours each, about 25 to 35 agent-days of stage work. The F
stages that turn a group on (F8, F10, F13, F17, F19, F20, C1, C2) will need follow-up
stages for their differences; expect 30 to 60 follow-ups, about 15 to 30 more agent-days.
The R stages start after one review round.

**Risks.**

| Risk | Likelihood | Mitigation |
| --- | --- | --- |
| Precision regressions in the gate (one-place instances, part holders, known closures, `writes_via`, split ids must come back as features of the analysis) | high | the precision corpus programs are tests of F8, F10, C1; zero new false positives in the repository programs; the 0.1 % budget in the probes |
| The analysis and the summary procedure become single points of failure | medium | `RELS`; the fact oracle, the summary oracle and trace conformance on each accepted program; the claims test; the fresh sweep |
| `typeck` extraction is hard (inference mixed with value flow) | high | the recorder (T3) gives the tables at once; the extraction (R1, R2) comes last, with the recorded tables as its oracle |
| Cost: more nodes, variables, cleanup copies for each destination, SCC iteration | medium | the cost criterion of §2.7 at each group stage; no facts for temporaries of plain data with no references; merged fact-free nodes |
| Diagnostics move lines or name temporaries | medium | `Origin` spans; the ledger records each moved marker; the W0204 span rule of `ir §6.9` |
| Two pipelines while the R3a workflow and reviews still fix the old one | medium | the freeze rule (§1, rule 6); each old fix adds a gate probe |
| The two review rounds after the cut over find a new class | medium | the gate runs every probe of three rounds and a fresh sweep, and blocks on every accepted fault, also one that the old pipeline accepts too |
| Run-time changes surprise a user | low | `docs/design.md` states them; the engine differential lists each changed program |
| The oracle cannot run 93 of 134 corpus programs (no `main`, no tests) | certain | the corpus markers protect them; a `lost-clean` needs a signed entry |
| `SCRATCH` goes away before the migration ends | high | rule 9: the repository holds each file that a stage reads; the tier-2 probes are in an archive with a committed hash (§2.1) |
| A stale oracle cache makes `cargo test` red after an interpreter change | medium | rule 3: the stage that changes the interpreter regenerates the cache in its commit; `tier1.rs` names the stale key |
