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
| R0c | The leftovers of groups A and B | A1, A2, B1 | done (157ff56) |
| R0d | Handlers in closure bodies; the two shapes of a handler that passes an operation on that R0b left | D2, C5 (C8, D5 stay: design note of R0d) | done (ec9563d) |
| R0e | Tasks in closure bodies; a spawn that does not name its scope | E1, E3 (a new reason E3b stays for 2 programs of tier 1 and 3 of tier 2: R0e as built) | done (8b2c59c) |
| R0f | Task runs (`http.serve` callbacks, code of a caller on another thread) | C1, C7, E7 (E2, E4, E5 stay: R0f as built) | done (f364e26) |
| R0g | Continuations and capabilities in closures; a construct with no full facts is in scope only if the `ir` pipeline rejects the program | D1, D4, C4, C6, D5, C8 (D1 15/49, D4 1/2, D5 5/5 stay: R0g as built) | done (5aea3a8) |
| R0h | Function values across operations: an operation of a caller gets a function value; a clause gets a function value of the callee, or gives a reference or a function value back to it | C2, D3 (after the fix of R0h C2 17/68, D3 1/1 stay; E2, E4, E5, C7, E7 stay: R0h as built, R0h fix as built) | done (c9da6d3) |
| R0i | The other old inputs, part a: `Analysis::sigs` (the declaration parts, `pins`, `reaches`, `old_rows`, the rows of the functions with no IR, `fip`, the on-abort rows), the seed facts, `body::roots` (R0i design note, R0i as built, R0i fix as built) | | done (f5a179d, fix 07d8576) |
| R0i-b | The other old inputs, part b: `ValueProps`, W0502 of `keep_modes`, W0303 (design in the R0i design note; R0i-b as built, R0i-b fix as built) | | done (d698a8b; the fix of the review: this stage) |
| R0j | The task fallbacks: a task that runs a callback more than once, a function variable that gets a new value, or code of a caller; a function value that runs a value of its arguments as a task, or that a function value of a callee runs as a task; a spawn on one of more than one scope (R0j design note, R0j as built) | E (TASK_AGAIN, TASK_LATE, TASK_CODE, E3b), C (VALUE_TASKS, R0e fix 2) | done (cb44033) |
| R0k | The operation fallbacks and the task leftovers of R0j: R0k-b (probes, ledger, design note), R0k-a (C2, D3: call-site copies of the callees, R0k-a as built), R0k-a2 (static closure-body copies at run nodes, generic callees, the closure guard; R0k-a2 as built), R0k-b1 (closure-body copies with an environment local, design note), R0k-c (D1, D5, C8: resume points and copied clause frames); D4, A and the task forms stay (R0k design note) | C2, D3, D1, D5, C8, D4, A, F18, E2, E4, E5, R0e fix 2 | R0k-b done (5d8106c); R0k-a done (66123df, 6077076); R0k-a2 done (f8463fe, fix 6bab2f8, 8402500); R0k-b1 not built: the handler environment of a closure blocks the copy (R0k-b1 design check; the direction B1' is for R0z); R0k-c1 done (0b425d7); R0k-c2 (D5, C8): design note after the review (a1fdcca; the cheap step R0k-c2a is not possible), done (R0k-c2 as built: D5 and C8 in scope, a row that only the analysis finds stays); R0k-d1 done (8be4ab5); R0k-d2 done (f90d76e); R0k-d3 not built: design check (E2 M-L; R0e fix 2 and `VALUE_TASKS` one L design; `TASK_CODE` with F18); HENV-SHADOW fix done (the closure of a callee in an outer local handler; "HENV-SHADOW fix" below) |
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

R0e as built:

- E1 (a task in a nested body, `factgen/mod.rs` `check_supported`): a scope body or a
  `fork` in a closure body is in scope. `handlers::spliceable` accepts a closure body as
  the root of a splice, so a scope body in a closure splices into it as a handled body
  does at R0d (the closure units, `Frames::of_bodies`, the splices of `closure_summary`
  and `emit_closure`). A spawn in a scope body or a handled body inside a closure body or
  a clause, on a scope of the maker, is in scope too
  (`handlers::frame_of_closure_or_clause`).
- The summary of such a closure (`docs/ir.md` 6.4, "As built (plan stage R0e)"): its
  facts have a task for each task that starts and ends in a run of the closure (a spawn
  on a scope of the closure, `handlers::owned_site`; a branch of a `fork` there;
  `decls::tasks_where`), with `task_ends`. These tasks give the part `runs`
  (`summarize::apply_hows`, the code of `summarize` for a function body: `twice`,
  `thread`, `with`, the places) and the pins (with the code of a caller left out). They
  are not in the part `tasks` (only the tasks of a scope of the maker are). The summary
  of a closure has the pins of its callees too, as the summary of a function body.
- Three consumers that the new form needed. (1) A task whose closure has a spawn or a
  `fork` in its bodies starts those tasks (`spawns_in`, `templates::inner_tasks`; the
  rule `pinned(T) :- spawns_in(T, U), pinned(U)` of the spec fired only in the old facts
  of `134_steal_pins.wf` before). (2) The tasks of a component are in the order of the
  source (`decls::tasks`): a spawn inside the task of another spawn has a lower site id,
  so the `stealable` marks of the corpus named the wrong tasks. (3) A value that a value
  of a callee runs as a task (`transfer::apply_runs` at depth > 0: a closure with a scope
  that spawns a value of its maker, run by a callee, `sim.run` or `with_timeout`; or a
  closure that calls a callee that runs a capture as a task) applies as plain code at the
  call, and the body runs the value as a task in the worst way (`RunOf::task`,
  `TaskHow::foreign`). Before, `task_run` held an index of the summary of the inner
  value, and the call template dropped the run: W0314 of the caller was lost. This was a
  hole of R0d too (`fixes/r0e/a13c_callee_bg_param.wf`: the old pipeline gives W0314, the
  run faults); the first build of R0e found it in the review probes (`a13`, `a13b`:
  `sim.run` and a callee). Such a program now falls back (C: "a function value that
  changes places ... and that code of a caller can run on another thread") when the
  value of the caller is not task-safe.
- E3 (a spawn that does not name its scope, `SpawnDecl::scope` is `None`). In a program
  with such a spawn (`tasks::unowned`), the value of each scope capability local points
  into the root of the local (`tasks::scope_cap_value`): a copy of the capability is
  invalid after the end of the scope body (W0301, RR4), and the analysis finds the scope
  of the spawn from the references of its scope operand (`Handlers::site_scopes`,
  `tasks::SiteScope`). The spawn needs exactly one scope and no other value
  (`templates::unowned_spawn`), else the program falls back with the new reason "a task
  of a scope that the spawn does not name and that the analysis does not find (stage
  R0e)": two scopes (`fixes/r0e/u03_two_scopes.wf`), a spawn through a reference to the
  capability (`u10`), a capability that a generic callee gives back (`e03`, `m3.wf`: the
  summary of `hold<T>` does not give the reference back). In the facts of a closure in
  the terms of its interface, the scope can be a scope of the maker (no reference into a
  scope capability of the closure, and the spawn is not in a scope body of the closure):
  part `tasks`. `ScopeWait` and the cleanup chain end the task (`templates::site_in_scope`);
  for a spawn in a closure that the component emits after the scope, `unowned_joins` adds
  these ends at the end of the component. Each `ScopeWait` of such a program can abort
  (`frames::destinations`). A spawn statement of this form has no `TaskResult` local: a
  drop pair at the terminator (`vars.rs`, as for `detach`) gives W0601 for a linear
  result. The old pipeline misses it (`u04_linear_result.wf`: a linear leak at run time).
- Why not a simpler E3 rule: a task of a scope that the facts do not know must end at the
  `ScopeWait` of its real scope, or the facts lose a conflict or a dangling capture; and a
  capability can leave its scope (the 132 shapes), so a lexical choice of the scope is
  not sound. The reference of the capability gives both the scope and the escape check.
- Tests: corpus `tests/programs/190_closure_tasks.wf` (W0405, W0301, W0602, W0403 and
  W0601 of tasks in closures, `with_timeout { fork }`, the handle of an ended task, and
  the E3 shapes; the clean twins; W0601 `old:` for the linear result) with its IR golden;
  `132_scope_escape.wf` and `134_steal_pins.wf` (markers of the `ir` pipeline with
  `old:`); `ir_handlers.rs` (`h4_scope.wf` is in scope: W0502 and W0503 at the run of
  the closure, as `h4_nested.wf`); probes `tests/gate/probes/fixes/r0e/` (63 programs:
  the adversarial forms of the brief with their clean twins: a callee that runs the
  closure later, closures in a struct and a vector, a spawn in a clause in a closure,
  three levels, a capture of a capture, a linear value with an abort before the join,
  `with_timeout { fork }`, a handle out of a closure, `sim.run`, `multi` re-entry `m1` to
  `m7`, the E3 forms `u01` to `u12`, the hole forms `a13*` and `a14*`). The `multi`
  re-entry (a handler that resumes two times runs code with spawns and joins again) is
  in neither oracle, so the probes `m1` to `m7` and `u11` check it by hand: each form
  that faults at run time (a value moved two times, a handle joined two times, an
  operation of another task) is rejected by the `ir` pipeline (W0302, W0503, W0314);
  `m1`, `m1_ok` and `m5_ok` are accepted with no fault (each copy of the frame has its
  own scope and children, I3-8).
- The fallbacks, before (ec9563d) and after, tier 1 / tier 2, by the note of `weft
  check` (scratchpad `r0e/t1-final.tsv`, `t2-final.tsv`, the lists of the scope report):
  E1 57/3958 to 0/0, E3 6/152 to 0/0. The new reason E3b ("a task of a scope that the
  spawn does not name and that the analysis does not find") has 2/3. The programs whose
  first failing body was E1 and that still fall back show their own reason: C7 2/3 to
  12/80 (a closure value that runs a value of its interface as a task, `VALUE_TASKS`,
  stage R0f), C1 39/107 to 41/139, E4 5/11 to 5/91, A2 1/41 to 2/53, E2 10/22 to 11/23,
  D5 15/114 to 15/116, D4 15/46 to 15/47, D1 60/308 to 60/309. Total 279/4981 to
  232/1080. 47 programs of tier 1 and 3901 of tier 2 come into scope (with the new corpus
  file and the 63 probes of `fixes/r0e`: 111 of tier 1); no program goes out of scope, and no
  program that was in scope changes its codes (the recount of both tiers).
- Gates: tier 1 0 blockers (4378 of 4670 in scope; 3680 same, 9 open, 265 fixed, 1
  new-fp, 112 lost-clean, 128 moved, 475 changed; `fixed` +3: `u04_linear_result.wf`,
  `a14_child_failure.wf`, `a14b_child_failure_callee.wf`, which the old pipeline misses;
  `lost-clean` +4 (`fixes/r0e/m1_ok`, `m1_pick_before_spawn`, `m5_ok`: the scope
  capability is not `once`, I3-8; `rt22b.wf`: the handle of an ended task), `changed`
  +12, each ledgered; the old records of the 64 new entries are new in
  `tests/gate/baseline-tier1.jsonl`, and the records of `132` and `134` have the hash
  of the new markers). Tier 2 (2 workers) 0 blockers (53648 of 57393 in
  scope; 40462 same, 10 open, 88 fixed, 12 new-fp: the 12 rows of R0d, 0.096 %; 0
  lost-fault; 3441 lost-clean, +588 in four classes R0E-T2-TASK, -REF, -ARGS, -ONCE;
  1824 moved; 11556 changed; the old records of tier 2 do not change). Each lost-clean
  row of R0e says `signed_by = "UNSIGNED"`: the review of R0e signs them. Fact oracle
  tier 1 0 failures (8 faults of accepted programs: the 7 of C3 and
  `r3/interp/probe/g14_fork_result_lin.wf`, which comes into scope; F3-6, issue #73, both
  pipelines accept it). Sigdiff tier 1 0 rows with no entry (one `sig` entry of R0e:
  `task_effects`, `pins`, `raises` of a closure that no one runs, and the parts of a
  closure that the result gives back). The fact oracle over the 3901 programs of tier 2
  that come into scope: 37 failures (summary oracle A3, code of a caller), each in a
  program that the `ir` pipeline rejects; none in an accepted program.
- `ereview/ev.sh` (binary `r0e/bin/weft-final`) on each program of tier 2 that comes into
  scope and that the `ir` pipeline accepts (854): 853 no fault, 1 HOLE+oldmiss
  (`g14_fork_result_lin.wf`, F3-6 above); on the 111 programs of tier 1 (the new ones,
  the probes, the corpus files): 0 HOLE but that one (52 no fault, 33 held, 21 both
  reject with no fault, 3 `oldmiss`: `u04`, `a14`, `a14b`, which only the `ir` pipeline
  rejects); on the 92 `changed` and `moved` rows of tier 2: no lost fault line. The review
  sets of R0d (`r0drev/p`, `p2`, `p3`, 174 programs): the same verdicts as the R0d fix 2
  binary (the 5 `HOLE+oldmiss` rows `r5`, `r7*` are older: both pipelines miss them).
- Open (issue candidates). (1) A function body `call_with(f, v)` whose task writes `v`
  while it runs `f`, which reads `v` (`r0e/t/or7a.wf`): the `ir` pipeline of R0d accepts
  it, the old pipeline gives W0312, the oracle finds a data race; R0e does not change it
  (the program was in scope before). The R0e fix closes it (below). (2) The summary of a closure has no part
  `task_effects`: a standard effect of its task goes to the root handlers (the run
  agrees), but a function body gives W0314 for the same task (`r0e/t/te3.wf`). (3) A
  closure that runs a value of its interface as a task falls back at a call of the
  value (C7, stage R0f), and a value of a caller that is not task-safe falls back at a
  callee (C1). (4) The scope capability is not a `once` value (I3-8, F19.1): R0e keeps
  the policy for a scope in a closure. (5) A scope with tasks in a closure raises in the
  summary of the closure also when no task can fail, as a scope in a function body does
  (precision: a `Fail` clause that changes a place then is W0301; the old pipeline
  accepts the function-body form `r0e/t/ab10ok.wf`, and the `ir` pipeline of R0d rejects
  it). (6) `hold(s)` of a generic
  callee loses the reference of the capability: E3b.

R0e fix as built (OR7: a task of a callee and a function value that the callee runs;
`docs/ir.md` 6.4, "As built (stage R0e fix, OR7)"):

- Cause. A closure that captures a local of the caller by reference gives the call only
  the place of its environment (`call_arg`), so the alias check (W0312) does not compare
  the local with the reference arguments; the run of the value (part `runs`) checks its
  accesses in the order of the code of the callee. No part of the summary had the tasks
  that run while the callee runs the value as plain code (`TaskHow` is for a value that
  runs as a task, `waits` for an operation of a handler of a caller). So a task of the
  callee that changes a place while the value reads it was a race that the caller did
  not see. A closure that captures a reference parameter points into the place itself,
  so W0312 caught that form (`or7/arg2.wf`).
- Fix. `Run::during` (6.7): the interface places that the tasks of the body change and
  read while it runs the value (`tasks::run_during` when the facts of the component are
  whole, and σ of the part of each callee that runs the value: `Applied::during_writes`,
  `during_reads`, `Em::run_during`). A call that applies a value that the body knows
  (`templates::during_check`) gives each place of the value a `call_arg` with the root
  `roots::fn_arg` if a task changes a place (a `call_mut` of each change of the value if
  a task reads a place): W0312 at the call, as the old pipeline gives. An effect that the
  value performs gives these places to the `WaitTask` of a local handler of the call
  (W0405): this closes the handler form (`or7_handler_value.wf`, `or7_handler_fail.wf`,
  which both pipelines missed). No rule of the spec changes.
- Probes `tests/gate/probes/fixes/r0e/or7_*` (42 files): 20 forms that faulted with no
  diagnostic of the `ir` pipeline (a capture of a local, of a field, of the whole local
  while the task changes a field, two values, a struct, an `Option`,
  a tuple, a loop, a callee that passes the value on, a runner, two levels, a local
  closure, a closure with a scope that a callee runs, a closure of the callee that spawns
  on the scope of the callee, `sim.run`, `with_timeout`, a vector behind a reference, an
  `rc` object, the two handler forms) are rejected now; the clean twins stay clean but
  `or7_maker_scope_ok.wf` (precision: the summary of the closure does not order its
  spawn, join and run; the old pipeline rejects it too). Corpus
  `tests/programs/191_value_runs_with_tasks.wf` with its IR golden.
- Gates: tier 1 0 blockers (4713 programs: 3709 same, 9 open, 269 fixed (+4: `or7_rc`,
  `or7_handler`, `or7_handler_value`, `or7_handler_fail`, which the old pipeline misses),
  1 new-fp, 116 lost-clean (+4, the clean twins that the old pipeline rejects, ledgered,
  `signed_by` UNSIGNED), 128 moved, 481 changed (+6, ledgered); no row of R0e changes
  class). Tier 2 (2 workers) 0 blockers: 40461 same, 10 open, 88 fixed, 12 new-fp
  (0.096 %, as R0e), 3441 lost-clean (as R0e), 1824 moved, 11557 changed, 0 lost-fault;
  one row goes from same to changed (`r2/oracle/runs/g7/p43726.wf`, a program that
  faults: one more W0312), and five changed rows get other W0312 rows. Fact oracle tier 1
  0 failures (the 8 faults and 16 timeouts of R0e); sigdiff tier 1 0 rows with no entry.

R0e fix 2 as built (the review of R0e, round 1: blockers B1 and B2, and the older holes
O1 and O2; `docs/ir.md` 6.4, "As built (plan stage R0e)"):

- B1 (a spawn on an outer scope in a scope body in a clause). Cause: `project` maps the
  nodes of a clause and of the handled bodies in it to the nodes that run the clause
  (`handlers::clause_nodes`), but not the nodes of a scope body in it. So the task of
  such a spawn did not start at the perform, and a write in such a scope body did not
  reach the perform either: the second form is a hole since C3 (`fixes/r0e/rv1_cs2_*`,
  which the old pipeline catches). R0e put the first form in scope through
  `frame_of_closure_or_clause`. Fix: `clause_nodes` maps a scope body to the block of its
  `scope` in the clause, as a handled body to its `handle`; a task that the clause also
  ends (a task of a scope inside the clause) does not start at the node that runs the
  clause. Real fix: the 10 forms of the review (`rv1_b1_*`) give W0405 at the race.
- O1 (a clause of a handler in a closure spawns on a scope of the maker, since R0d):
  `closure_summary` did not put the spawn sites of the clauses of the closure in the part
  `tasks`. Fix: `emit_clause` gives them back. Real fix (`rv1_o1_*`).
- O2 (a callee spawns its parameter two times, since R0a): the task nodes of a call did
  not move the `once` argument. Fix (`templates::task_runs` path): for a run as a task
  with `TaskHow::twice`, or `Run::many` of a callee with a body (not a foreign run), the
  first task node moves the argument of the parameter and the second one uses it
  (W0502). Only the operand of the parameter counts (a value that it runs gets its runs
  from its own summary: `fixes/f20_3/i2_ctl_twice_c.wf` stays clean). Real fix
  (`rv1_o2_h16.wf`, `rv1_o2_seq.wf`: a spawn, a join and a spawn again).
- B2 (a `once` value that a value of a callee runs as a task more than once): fallback.
  R0e applied such a run as plain code, and a plain run of a value of a value loses the
  second run of a `once` value. This is older and wider: with no task at all,
  `fn run2(g: fn(fn()), f: fn()) { g(f); g(f) }` with `run2(|x| x(), || take(v))` is
  accepted by the `ir` pipeline since C3 (the old pipeline gives W0502; issue
  candidate, not fixed here; R0e fix 3 closes it, below). A fix in proportion is not possible in this stage, so
  `transfer::apply_runs` at depth > 0 with a run as a task that has function values
  gives the new fallback reason
  E7 "a function value that a function value of a callee runs as a task (stage R0e fix
  2)". The forms `a13`, `a13b` and `a13c` of R0e fall back too (the old pipeline catches
  them). The clean twin `rv1_b2_ok.wf` gets the old W0502 again (a false positive of the
  old pipeline, as before R0e).
- The fallbacks (scope-report lists, tier 1 / tier 2): E7 0/0 to 3/19 (C1 41/139 to
  40/126, C7 12/80 to 12/79, D4 15/47 to 15/46: the first failing body changes); total
  232/1080 to 234/1084. The fallback needs a function value of the run: a run of a
  capture that holds no function value (the `fork` of `fixes/f20_2/p2_fork_*`, test
  `ir_tasks.rs` `a_fork_that_a_closure_body_starts_checks_its_branches`) stays in
  scope. 2 programs of tier 1 (`crash/c08.wf`, `c10.wf`: a foreign run of a recursive
  value; `sim1.wf` changes its reason) and 4 of tier 2 go out of scope; each was in
  scope at R0e. 9 programs of tier 2 that stay in scope change their codes: 4 get the
  W0312 of the R0e fix, 3 get W0502 (O2), and 2 (`m3a/p2018.wf`, `p6386.wf`) lose a
  W0405 at a `fork` in a clause that the old pipeline does not give either (a task of
  the clause that the clause ends).
- Tests: corpus `tests/programs/192_clause_scope_tasks.wf` (B1, O1, O2, the clean
  twins) with its IR golden; probes `tests/gate/probes/fixes/r0e/rv1_*` (26 files).
- Gates: tier 1 0 blockers (4439 of 4740 in scope; 3723 same, 9 open, 269 fixed, 1
  new-fp, 117 lost-clean (+1: `rv1_o1_ok.wf`, UNSIGNED), 128 moved, 493 changed).
  Tier 2 (2 workers) 0 blockers (53644 of 57393 in scope; 40476 same, 10 open, 88
  fixed, 12 new-fp (0.096 %), 0 lost-fault, 3441 lost-clean, 1822 moved, 11544 changed).
  Fact oracle tier 1 0 failures (the 8 faults and 16 timeouts of R0e). Sigdiff tier 1 0
  rows with no entry (one `sig` entry: a scope with no task in a clause does not
  raise). The reviewer signed the lost-clean rows of R0e; the rows of the R0e fix and of
  this fix wait for the review.

R0e fix 3 as built (H19, the plain form of B2 above; `docs/ir.md` 6.4, "As built (plan
stage R0e)"):

- Cause. A callee gives a `once` closure `f` to code of a caller, a function value `g`
  of its interface (`g(f); g(f)`). The callee does not know `g`: the run of `f` is the
  worst way of that code (`task`, `TaskHow::foreign`), and its `Run::many` is true for
  each such value. The rule of O2 above leaves out the `many` of a foreign run (else each
  `once` closure that goes to code of a caller is W0502), and the run of `g` at the
  caller does not know that its argument is `f`. So no rule counted the second run (a
  hole since C3, `fixes/r0e/h19_*`; the old pipeline gives W0502). A callee that is a
  function item (`call(f); call(f)`) was right: its summary runs its parameter.
- Fix. `Run::via_only` and `Run::via` (`docs/ir.md` 6.7): the body only gives the value
  to code of a caller, and the values and arguments of that code
  (`transfer::apply_value`; `Via::again` for two blocks or a loop). A call that knows each
  value of the code counts the runs of the argument in their summaries
  (`transfer::via_twice`, `arg_runs`), added over the entries; else the count is two.
  Two runs or more: the task nodes of the call move the argument and use it again
  (`Applied::via_twice`, W0502). This keeps the precision of the `ir` pipeline where `g`
  runs `f` one time or not at all. Fallback E7 (B2) stays: it is a run as a task of a
  value of a value at depth > 0, which has no task nodes; this fix does not change it.
- Probes `tests/gate/probes/fixes/r0e/h19_*` (24 files): 10 forms that faulted with no
  diagnostic of the `ir` pipeline (two runs of `g`, `async`, two runs inside `g`, a
  capture in `g`, an item `g`, a struct field, an `Option`, a loop, both arguments, a
  closure that runs `f`) are W0502 now. The clean twins stay clean but
  `h19_nested_ok.wf` (`g(|| f())`: no `via` for a value that the given value runs in
  turn; the old pipeline rejects it too). Corpus
  `tests/programs/193_value_runs_once_value.wf` with its IR golden.
- Gates: tier 1 0 blockers (4460 of 4765 in scope; 3740 same, 9 open, 269 fixed, 1
  new-fp, 122 lost-clean (+5, the clean twins that the old pipeline rejects,
  `signed_by` UNSIGNED), 128 moved, 496 changed (+3, ledgered); no row of R0e fix 2
  changes class). Tier 2 (2 workers) 0 blockers, each row as R0e fix 2 (40476 same, 10
  open, 88 fixed, 12 new-fp (0.096 %), 0 lost-fault, 3441 lost-clean, 1822 moved, 11544
  changed). Fact oracle tier 1 0 failures (the faults and timeouts of R0e fix 2).
  Sigdiff tier 1 0 rows with no entry. `ereview/ev.sh` on `r0erev/p` and
  `fixes/r0e` (342 programs): 0 HOLE; only the `h19_*` rows change.

R0e fix 4 as built (the review of R0e, round 2: blocker R2-B1 and three older holes;
`docs/ir.md` 6.4, "As built (plan stage R0e)"):

- R2-B1 (a regression of fix 2). Cause: the lift filter of `handlers::project` skipped
  the start of a task at the node that runs a clause when any `joined_at` of the task
  was in the clause. A join on one path (also in a loop that does not run) and a detach
  on the other let the task run past the clause, and the race after the perform was
  lost (`b16`, `b17` to `b19`, `b21`, `b24`, `b25` of the review; `b17` was a B1 form
  of round 1). Fix: the start is skipped only for a task that starts and ends in the run
  of the clause: a spawn on a scope whose scope body is in the clause, or a branch of a
  `fork` there (`owned_by_clause`; the `t/cs1.wf` false positive of fix 2), or a task of
  an outer scope that the clause joins on each path from the spawn before a `resume`,
  an edge out of the clause or the end of the clause (`joined_in_clause`). So `b01_ok`
  and `b27_ok` (a join on each path) stay clean; the old pipeline rejects them.
- Older holes (old W0312, the `ir` pipeline 0 since the R0e fix or before; fixed in
  proportion): `a15` and `a35`: the callee runs the value in a clause of its own handler
  (or a clause gives it to a callee) while its task runs. `Run::during` read the
  `run_at` and `run_during` of the main `Em` only. Now `emit_clause` gives back its own,
  and `handlers::clause_run_at` maps a run node of a clause to the nodes that run the
  clause (function and closure summaries). `a31`: the callee runs the value in a second
  task while the first one clears `v`. `tasks::task_hows` did not count the changes of
  another task that runs at the same time as the task of the value; now `TaskHow::writes`
  and `reads` have them (W0405 at the call).
- Tests: corpus `192_clause_scope_tasks.wf` gets `clause_join_or_detach` (W0405) and the
  clean `clause_join_both` (`old:` W0405); probes `tests/gate/probes/fixes/r0e/rv2_*`
  (17: the R2-B1 forms, the three older holes, and their clean twins).
- Gates: tier 1 0 blockers (4477 of 4782 in scope; 3744 same, 9 open, 269 fixed, 1
  new-fp, 128 lost-clean (+6: the clean twins, UNSIGNED), 128 moved, 503 changed (+7);
  no row of fix 3 changes class). Tier 2 (2 workers) 0 blockers (53644 of 57393 in scope;
  40476 same, 10 open, 88 fixed, 12 new-fp (0.096 %), 0 lost-fault, 3441 lost-clean,
  1822 moved, 11544 changed; one changed row, `r3/oracle/runs/m3b/p24092.wf`, gets the
  W0405 at line 76 that the old pipeline gives). Fact oracle tier 1 0 failures (the 8
  faults and 16 timeouts); sigdiff tier 1 0 rows with no entry. `ereview/ev.sh` on
  `r0erev/p`, `r0erev2/p` and `fixes/r0e` (517 programs) against the fix 3 binary: the
  20 HOLE rows are held; no other row changes; the one `HOLE+oldmiss` is `a04` (both
  pipelines miss it). The reviewer signed the rows of the R0e fix and of fix 2.

R0f design note (task runs: a value of a caller that a callee runs as a task):

- Where a value of a caller runs as a task. (1) A callee with a body: the part `runs`
  says it (`Run::task`, `TaskHow`: `thread`, `twice`, `with`, the places of the body
  while the task runs), and the run node applies the value at its task nodes
  (`templates::call_tasks`). (2) A foreign function (`extern fn`) and a function of the
  prelude with no body (`http.serve`): `sig::foreign_fn_parts`, the worst way. (3) Code
  of a caller: a value that the body gives to a function value that it does not know
  (`transfer::apply_value` with `Given::Args`): a task with no task of the body, the
  worst way (`TaskHow::foreign`). (4) A function value of the caller whose summary runs
  a value of its arguments as a task (C7). (5) A closure that spawns a value of its
  interface on a scope of its maker (part `tasks`): the task runs the value after the
  call of the closure.
- Before R0f, (2) and (3) fell back for a value that can race (`transfer::task_unsafe`,
  C1), (4) fell back always (`VALUE_TASKS`, C7), a task run of a value of a value fell
  back at depth > 0 (E7, R0e fix 2), and (5) was a plain run at the node only (a hole:
  the task did not have the places of the value).
- The checks. W0314: `task_w0314` of the values of the task (a task node, a task of a
  scope of a maker). W0405: the footprint of the task (`task_writes`, `task_reads`), a
  second start for `twice`, the places of the other values (`with`) and of the callee at
  the third task node. W0401 and W0403: `thread` (`fork_task`, `captures`,
  `mut_through`). W0502 and W0601: the task nodes move a `once` argument that runs two
  times (`twice`, `many` of a callee with a body, `via_twice`, O2 and H19 of R0e). Pins
  and steal: a task of code of a caller is `opaque` (pinned), as before. Raises: the
  call aborts as the summary says (no change). The R0e fixes stay: `Run::during`,
  `Run::via`, `via_twice` and the lift filter of a clause task are not changed; the worst
  way of code of a caller and `via_plain` read them.
- The worst way. A foreign function: on another thread (the old lowering,
  `Lower::callee_task_runs`), two at one time, with the other values, while it changes
  and reads what it gets. `http.serve`: the same, but its tasks are pinned (no
  `thread`). Code of a caller: on another thread, with the other values of the
  interface. Two tasks of one value of code of a caller and the changes of the code
  itself are not in its worst way: with them, a value that a callee gives to itself
  through code of a caller (`Core_S2/probes/crash/c08.wf`) was a new false positive over
  the 0.1 % rule of both tiers. A value that changes a captured place is W0403 there,
  and a run node that knows the code uses the way of the code (below).
- A run node that knows the code of a caller uses its summaries (`transfer::via_plain`):
  plain code as many times as `via_twice` counts, with the places of the tasks of the
  callee while it runs the code (`Run::during` of the run of the code), when no value
  of the code runs the argument as a task, gives it back, puts it into a place, starts a
  task of a scope of its maker or runs it while a task of its own runs; else a task, two
  tasks at one time if a value of the code runs the argument so
  (`transfer::via_code_twice`).
- A task that the facts of the callee do not describe (a task in a clause of the callee,
  `r0erev3/p3/k05_value_in_clause_task.wf`) keeps the fallback C1 for a value that can
  race: the worst way of code of a caller does not have the places of the other tasks of
  the callee (the first build of R0f accepted `k05`, a race).
- A call of a function value has four task nodes for each argument that can hold a
  function value (`frames::value_task_args`): (4) and the values of (3) that can race
  apply there (`templates::value_slots`). With no such value the call keeps its facts
  of R0e (the task nodes are not in `Em::task_nodes`).
- (5): the summary of the closure has the spawn site in `TaskHow::tasks` of the run of
  the value; the run node gives the changes and the reads of the value to that task too
  (`templates::maker_task_runs`, also W0314).
- Size: C1, C7 and E7 in one commit; E2 (a task that runs a value more than once: a
  spawn has one node), E4 (a task that runs a variable that gets a new value) and E5 (a
  task of code that the body does not follow) stay (next stage).

R0f as built:

- The changes of the design note: `summarize::apply_hows` (the worst way of code of a
  caller: `thread`, `with`), `sig::from_signature` (a foreign function: `thread`,
  `TaskHow::no_body`), `transfer::apply_runs` (no fallback for a foreign run of a value
  that can race, but for a task of the callee with no `TaskHow` and no `via`;
  `via_plain`, `via_code_twice`, `via_tasks`; E7 only for a known value; at depth > 0 a
  task run is `RunOf::task`, not `task_run`), `transfer::apply_value` (code of a caller
  that gets a value that can race: each value of the arguments is a task of the call,
  `Applied::task_how`), `templates::call_tasks` (slots: `item_slots`, `value_slots`),
  `templates::call_value` (the task nodes of a call of a function value),
  `frames::add_tasks` (`value_task_args`), `templates::maker_task_runs` and
  `closure_summary` (`TaskHow::tasks`, `Em::maker_site`, `Em::maker_runs`). No rule of
  the spec changes (`docs/ir.md` 6.4, "As built (plan stage R0f)").
- Tests: corpus `tests/programs/194_task_runs.wf` (W0401, W0403, W0405, W0502, W0314,
  W0312 of the forms of the design note, with `old:` where the old pipeline differs;
  clean cases) with its IR golden; the markers of `38_callbacks.wf`, `61_task_paths.wf`,
  `82_stored_spawns.wf` and `133_task_params.wf`, which come into scope; probes
  `tests/gate/probes/fixes/r0f/` (43: the adversarial forms of the brief with clean
  twins: a callback that runs two times, concurrently with the code of the caller or of
  the callee, with a `once` or linear capture, an `Rc` capture, a `&mut`-like capture,
  an operation of a local handler, a callee that stores the callback, a value of a value,
  a generic callee, a field, `http.serve` with a handler that writes a local, and the
  maker-scope forms); `ir_fn_values.rs`
  (`a_closure_that_code_of_a_caller_can_run_on_another_thread_is_a_task_of_the_call`)
  and `ir_handlers.rs` (`gen_k.wf` is in scope).
- The probes found three holes of HEAD (R0e fix 4) in scope, which R0f closes: a value
  that code of a caller runs as plain code while a task of the callee changes its place
  (`c16_cc_during_plain.wf`, old W0405), and a closure that spawns its parameter on a
  scope of its maker while the maker writes (`c29d`, old W0405) or with an operation of
  a local handler (`c29f`, old W0314); and two that both pipelines missed (`c26c`,
  `c29g`: a reader, a dangling reference).

- The fallbacks, before (R0e fix 2 recount, the lists of the scope report; R0e fix 3 and
  fix 4 do not change the scope) and after, tier 1 / tier 2 (scratchpad `r0f/fb-x12.tsv`):
  C1 40/126 to 0/0 (1/2 now show C2, "a function value that an operation gives to a
  handler", and 0/2 show E2: the first failing body changes), C7 12/79 to 7/11, E7 3/19
  to 2/5; E2 11/23 to 10/24, E5 3/14 to 4/15 and E4 5/91 to 5/91 stay (design note). 45
  programs of the scope-report list of tier 1 and 204 of tier 2 come into scope; no
  program goes out of scope (tier 2: 53644 to 53848 in scope, +204). Of the programs
  that were in scope, no row of tier 1 or tier 2 changes class or codes but
  `fixes/r0e/h19_linear.wf` (`changed` to `same`: the code of the caller runs the
  linear capture as plain code, no W0602).
- Gates: tier 1 0 blockers (4570 of 4826 in scope; 3741 same, 9 open, 274 fixed (+5:
  `fixes/r0f/c10_generic`, `c26c`, `c29`, `c29e`, `c29g`, which the old pipeline
  misses), 1 new-fp, 134 lost-clean (+6, UNSIGNED: `fixes/r0f/c05_cc_plain_ok`,
  `c06_cc_once_ok`, `c22_cc_two_values_ok`, `verify/s5/diff/p/fp1.wf`, `fp2.wf`, and
  `fixes/r0e/rv1_b2_ok.wf`), 128 moved, 539 changed (+36, ledgered); the old records of
  the new entries and of the four corpus files with new markers are new in
  `tests/gate/baseline-tier1.jsonl`). Tier 2 (2 workers) 0 blockers (53848 of 57393 in
  scope; 40368 same, 10 open, 88 fixed, 12 new-fp (0.096 %, the rows of R0d), 0
  lost-fault, 3443 lost-clean (+2: `fp1`, `fp2`), 1823 moved (+1), 11649 changed
  (+105, ledgered); the old records of tier 2 do not change). Fact oracle tier 1 0
  failures (the 8 faults of R0e; 22 timeouts: the 16 of R0e and six programs with
  `http.serve` that come into scope). The first run found a summary-oracle failure (A3)
  in the clean twin of the older hole `c17` below: the probe is not in the repository.
  Sigdiff tier 1 0 rows with no entry (one `sig` entry of R0f for the 29 programs that
  come into scope). The fact oracle over the programs that come into scope: 0 failures
  (79 that run; 170 have `http.serve` or an `extern fn` and do not run).
- `ereview/ev.sh` (binary `r0f/bin/weft-final`) on the 249 programs that come into scope:
  0 HOLE (28 held, 12 no fault, 39 rejected by both pipelines with no fault: the old
  pipeline rejected them at R0e fix 4 too; 170 do not run: the `ir` pipeline rejects each
  one that the old pipeline rejects). On the review sets of R0e (`r0erev/p`,
  `r0erev2/p`, `r0erev3/p`, `p2`, `p3`) and on `fixes/r0e` and `fixes/r0d` (756
  programs) against the R0e fix 4 binary: no verdict gets worse; the 8 HOLE rows are
  older (the open holes of the review of R0e, round 3, and `a04`); `j02_mid_known_g_ok`
  goes from both-reject to no fault; three clean programs that fell back to the old
  pipeline (which rejects them) are rejected by both pipelines now (`h19_multi_ok`,
  `a04_g_to_h_ok`, `g16_via_after_multi_in_g`: W0502 of the worst way of code of a
  caller after a `multi` value or of a value of a value, as the old pipeline). The first
  build of R0f had two HOLE rows there (`r0erev2/p/e05_depth1_during.wf`: the code of the
  caller runs the value while a task of its own changes the place; `r0erev3/p3/k05`: a
  task in a clause of the callee): `via_plain` refuses a code with its own `during`, and
  a task with no `TaskHow` keeps the fallback C1.
- Open (issue candidates). (1) Code of a caller that keeps a value in a place
  (`copy(src, dst)` run by `apply(k, a, b) { k(a, b) }`): the summary of the code gets
  `Given::Opaque`, so the value that it puts is lost (`r0f/p/c17_cc_store_ref.wf`: a
  hole since C3, the old pipeline gives W0301; the summary oracle finds it in the clean
  twin). (2) The code of a caller is a closure that spawns its parameter on a scope of
  `main` and an item runs it (`c26b`, `c26d`): both pipelines miss the race after the
  call. (3) An item callee that runs a value that changes what another argument points
  into (`r0f/t/f4a.wf`: in scope at R0e fix 4, the old pipeline gives W0312). (4) A
  closure of a local handler that code of a caller can keep gets W0314, not W0313
  (rejected for the other reason). (5) E2, E4, E5 and the rest of C7 and E7 stay.

R0f fix as built (the review of R0f, round 1: blockers B1 and B2; `docs/ir.md` 6.4, "As
built (plan stage R0f)"):

- B1 (the E7 relaxation of R0f). R0f took the fallback E7 off a task run of an `Unknown`
  value at depth > 0, because the callee runs that value in the worst way. But in the
  body that gives a reader to code of a caller (`transfer::apply_value` with
  `Given::Args`), the values became tasks only when they can race, and the worst way has
  no changes of the code itself: `outer(g) { let c = ..; g(|| print(c.k), &c) }` with a
  `g` of `main` that spawns the reader and writes `d.k` was accepted (`r0frev/p/c04_e7_*`,
  `c09`, `c12`, `c16`, `c22`, `c24`, `c25`; held at R0e fix 4 by E7). Fix, both options
  of the review: (b) code of a caller that gets a place in an argument with no function
  value makes each value of the arguments a task of the call also when a value of the
  body reads a place (`transfer::local_reads`), with these places as the changes of the
  code (`TaskOf::writes`); this closes `rv1_c15_unknown_extern_value.wf` (code from a
  foreign function, an older hole); a place that only the environment of a value
  reaches does not count (`r0frev/p/c26_e7_caller_place_ok.wf` stays clean). (a) E7
  stays for an `Unknown` value whose task runs while the value changes places or runs
  other values (`TaskHow::writes`, `with`): one program of tier 2 goes out of scope
  again; `rv1_b2_ok.wf` stays clean.
- B2. `templates::item_slots` made a slot for each entry of `runs` that runs as a task,
  also for a value that `via_plain` runs as plain code (no values in the slot), and
  `call_tasks` then put the empty task places of that parameter in place of its plain
  places, so the `with` of the other slot found nothing (`h03`, `h03d`, `h07`, `h08`,
  `h10` of the review; held at R0e fix 4). Fix: a slot with no values starts no task and
  keeps the plain places. `maker_task_runs` runs for a value at a task node too, so a
  value that goes to a task of a scope of a maker through the code of a caller
  (`via_tasks`) and runs in a task of the call gives its places to that task (`h10`).
- Probes `tests/gate/probes/fixes/r0f/rv1_*` (8: `c04` and its twin, `h03` and its twin,
  `h07` and its twin, `h10`, `c15`); `48_lend_alias.wf` gets the W0405 of the old pipeline
  at `give_closure`. The reviewer signed the lost-clean rows of R0f; the new lost-clean
  row `rv1_h07_callee_task_and_via_plain_ok.wf` waits for round 2.
- `ereview/ev.sh` on the 127 programs of the review (`r0frev/p`) against the R0e fix 4
  binary: 0 new HOLE (the 12 HOLE rows of R0f are held; the 3 HOLE rows that remain are
  older: `g03`, `b13`, and `b08` = `c26b`). Precision: `h01_cc_code_writes_capture_ok`
  (W0405: the code writes `c` after the scope, the worst way of the task of the call)
  and `f07_vc_fork_rc` (W0401 for an `Rc` in a `fork` branch, the rule of ADR 0006) stay
  rejected by the `ir` pipeline only.
- Gates: tier 1 0 blockers (4574 of 4834 in scope; 3747 same, 9 open, 274 fixed, 1
  new-fp, 135 lost-clean (+1, UNSIGNED), 128 moved, 540 changed (+1); the old records of
  the 8 new probes and of `48_lend_alias.wf` are new in `tests/gate/baseline-tier1.jsonl`).
  Tier 2 (2 workers) 0 blockers (53847 of 57393 in scope; 40371 same, 10 open, 88 fixed,
  12 new-fp (0.096 %), 0 lost-fault, 3443 lost-clean, 1824 moved (+1, a mutant of corpus
  48, ledgered), 11645 changed; 4 mutants of corpus 48 and `rt5_variants.wf` get the
  W0405 of the old pipeline). Fact oracle tier 1 0 failures (8 faults, 22 timeouts, as
  R0f). Sigdiff tier 1 0 rows with no entry. On the review sets of R0e, `fixes/r0e` and
  `fixes/r0d` (756 programs) each verdict is as at R0f. The fallbacks: E7 2/5 to 2/6 (the
  program that goes out of scope); the other counts of R0f do not change.

R0g design note (continuations and capabilities in closures; the reasons D1, D4, C4, C6,
and D5 and C8, which R0d left):

- The six reasons are of two kinds. C4, C6 and part of D4 are forms that the facts can
  model with the rules that exist: a closure whose maker frame is gone, a captured
  capability of a closure that a callee or a closure made, and an escape through an
  abort. D1 (a `resume` in a closure: the run of the closure is a resume point of the
  clause), D5 and C8 (a re-entry of a clause frame after a `multi` operation, the design
  note of R0d) need new kinds of facts: a summary part "resumes the continuation of
  capture `k`" that splits the clause at the run node, and copied clause frames. Each one
  is a stage of its own (size L), with its own proofs of E1 to E4.
- The forms of the first kind. C4: σ of a closure that a clause gives to the handled body
  or to the site takes the environment from the closure value (`made_sigma`), as for a
  closure that a callee made: the states there have no values of the locals of the
  clause. C6: σ of a captured capability of a made closure is the capability of the
  handler that the capture names, if its handled body runs at the node, else none.
  D4: an abort to a local handler outside the handler leaves the locals outside its
  handled body with their values: W0313, as the old lowering does on its abort paths.
- The forms of the second kind, in proportion. Most programs of D1, D5 and C8 are
  rejected by the old pipeline (W0313 for a continuation that leaves the clause, W0502
  for a `once` closure that resumes two times, W0503 for a `once` continuation that is
  live across a `multi` operation). The facts with a weak form of the construct give the
  same errors: a `resume` in a closure moves its argument and uses the continuation, a
  clause has no re-entry. A rejected program does not run, so a rejection with facts
  that are not whole lets no fault through. So such a program is in scope only if the
  `ir` pipeline rejects it (`Scope::pending`, `weft_check::check_analysis`); else the old
  pipeline checks it, as before. The same rule takes the D4 runs whose W0313 the fact
  generator does not find. W0313 for a continuation is a new Rust check of the `ir`
  pipeline (`clause::check_kont_escape`), with the texts of the old lowering.
- What stays. A clean program with a `resume` in a closure (D1), a clause that performs
  a `multi` operation after its `resume` (D5, C8), and a D4 form that the `ir` pipeline
  accepts: the old pipeline checks them. Stage R0z needs the full forms (above) for them.
- No rule of the spec changes. Probes: `tests/gate/probes/fixes/r0g/` (the bad form and
  the clean twin of each shape). Corpus: `tests/programs/195_closure_conts.wf`.

R0g as built:

- C4 (`apply::closure_sigma`): a closure that runs where the locals of its maker clause
  have no value (`clause::runs_with_maker` is false) gets σ of `made_sigma`. C6
  (`made_sigma`): a `Cap` capture maps to the capability of the handler that the capture
  names through the makers, if its handled body runs at the node (`apply::live_cap`), else
  to nothing. A `Kont` capture maps to nothing and is pending (below).
- D4 (`transfer::check_cap_apps`): a run with no capability for a `Cap(k)` perform notes
  the handler of the capture (`clause::note_pending_escape`); a run whose node does not
  run the clause of a live handler notes it with the flag "a W0314 is enough". At the end
  of `factgen::emit` each noted handler needs a W0313 at the span of its `handle` (also of
  another function: a closure that a callee made; `checks::handle_span`), else the
  program is pending. The escape check of a `handle` also reads the abort edges to a
  local handler outside it (`clause::note_past`, `Open::past`): a closure in a local that
  lives on there is W0313 ("the local `f` keeps it", as `check_local_keeps`).
- W0313 for a continuation (`clause::check_kont_escape`, `Escape::Kont`,
  `checks::kont_escape`): at each end of a clause (its `Return` before and after its
  `resume`, `run_clause` and `run_handled`) and at each `resume` of the clause, a closure
  that can resume the continuation of the clause (`clause::resumes_kont`: a `Kont`
  capture through the makers, `kont_capture_clause`, or a `Kept`/`ByRef` capture whose
  value holds such a closure) in the value of the clause, in a local outside the `handle`,
  in a heap slot, or in the argument of the `resume`. Escapes are one report for each
  handler and clause (`Escape::same_report`).
- Pending (`clause::note_pending`, `factgen::Scope::pending`, `factgen::Pending`):
  a `resume` of a captured continuation (`clause::KONT_CAPTURED`, in `check_supported`,
  `clause::resume`, `handlers::resume` and the `Kont` captures of σ), a row in a clause
  (`analysis::run_rows`), a `multi` resume of a nested node (`clause::handle_run`), and a
  D4 handler with no W0313. Each one has a weak form, and the program keeps both views
  (`lib.rs`). `weft_check::check_analysis` (`check_pending`) checks the `ir` facts; with
  an error the result is the `ir` result (alone in the `ir` mode, as `Checked::ir` in the
  `both` mode), else the old pipeline checks the program and the scope gets the reason.
  `factgen::components` gives no components for such a program (the fact oracle checks
  nothing); `weft-gate` `oracle.rs` reads the fallback after the check, and `sigdiff.rs`
  decides the scope with the check.
- Tests: corpus `tests/programs/195_closure_conts.wf` (W0301, W0313, W0502, W0503 of the
  forms, the clean twins) with its IR golden; the markers of `71_closure_modes.wf`,
  `123_resume_scope_ends.wf` and `124_local_suspends.wf`, which come into scope (`old:`
  where the facts with a weak form give other lines); probes
  `tests/gate/probes/fixes/r0g/` (24: the bad form and the clean twin of each shape);
  `weft-check` `ir_handlers.rs`
  (`a_construct_with_no_full_facts_is_in_scope_only_if_the_ir_pipeline_rejects_it`, data
  `tests/data/handlers/r0g/`; `the_rows_of_clauses_stay_with_the_old_pipeline` now has
  three programs that the `ir` pipeline rejects), `weft-sema` `scope.rs`
  (`a_construct_with_no_full_facts_keeps_both_views_for_the_check`; the stub of the
  fallback tests is a clause that gives a function value back, D3), `cli.rs` (the same
  stub).
- The fallbacks, before (R0f fix, binary `weft-r0ffix1`) and after, tier 1 / tier 2, by
  the note of `weft check` over each tier-1 file and over the programs of tier 2 that fell
  back at C3 or R0f (scratchpad `r0g/before-t*.tsv`, `x9-t*.tsv`): D1 60/309 to 15/49, D4
  15/46 to 1/2, C4 7/22 to 0/0, C6 6/15 to 0/0, D5 15/116 to 5/5, C8 2/2 to 0/0. The
  programs whose first failing body was one of these and that still fall back show their
  own reason: D3 34/59 to 36/93, C2 18/105 to 19/121, A2 2/53 to 3/61. 80 programs of tier
  1 and 396 of tier 2 come into scope; no program goes out of scope. Each one that comes
  into scope is rejected by both pipelines: the facts with a weak form are in scope only
  for a program that the `ir` pipeline rejects, and the old pipeline rejects each C4, C6
  and D4 program of the lists too. What stays: the clean programs of D1 (a closure that
  resumes in its clause, a `resume` in a task), D5 (a clause that performs the `multi`
  operation after its `resume`), and three D4 forms (the analysis keeps a value of a local
  of the site from the resume point after the `handle`: `partb/p/e1_fp.wf`; a run in a
  clause of a closure of an outer local handler: `r3/fidelity/p/sp1.wf`).
- Gates: tier 1 0 blockers (4672 of 4859 in scope; 3731 same, 9 open, 274 fixed, 1
  new-fp, 135 lost-clean, 139 moved, 570 changed; the 41 new `moved` and `changed` rows
  are programs that come into scope, rejected by both pipelines, ledgered; the old
  records of the 25 new entries and of the three corpus files with new markers are new
  in `tests/gate/baseline-tier1.jsonl`, and the other old records do not change). Tier 2
  (2 workers) 0 blockers (54243 of 57393 in scope; 40149 same, 10 open, 88 fixed, 12
  new-fp (0.096 %, the rows of R0d), 0 lost-fault, 3443 lost-clean, 1837 moved, 11854
  changed; the 222 rows that leave `same` come into scope, each ledgered, most by the
  entries of the older stages for their codes). No new lost-clean row, so no row waits
  for a signature. Fact oracle tier 1 0 failures (8 faults and 22 timeouts, as R0f; 1302
  pass); a pending program gives the oracle no components. Sigdiff tier 1 0 rows with no
  entry (one `sig` entry of R0g for 24 programs that come into scope). The fact oracle
  over the 476 programs that come into scope (`ev.sh`): 0 failures (102 run it; the
  pending programs give it nothing). `ereview/ev.sh` (binary `r0g/bin/weft-final`)
  on the 476 programs that come into scope: 0 HOLE (380 rejected by both pipelines with
  no fault, 96 held); on the 24 probes of the stage and the four corpus files: 0 HOLE (9
  held, 10 rejected by both, 9 no fault); on the review sets of R0d to R0f (`r0frev/p`, `r0frev2/p`, `r0erev*/p*`,
  `fixes/r0d`, `fixes/r0e`, `fixes/r0f`: 972 programs) each verdict is as at R0f fix (the
  HOLE rows are older); one IR record changes (`r0erev3/p/d03_multi_clause.wf`, a D5
  program that the `ir` pipeline now rejects with the W0312 of the old pipeline).
- Open. The full facts of D1 (a summary part "resumes the continuation of capture `k`"
  and the split of the clause at the run node), of D5 and C8 (copied clause frames), and
  of the D4 forms above, for stage R0z. The facts with a weak form give fewer errors than
  the old pipeline in some rejected programs (`123_resume_scope_ends.wf`: four W0301 of
  the old pipeline after the run of a closure that resumes, in `resume_in_closure`,
  `resume_in_callee`, `moved_in_closure` and `cleared_in_closure`; the text of the
  ledger entry is correct from the R0g fix); such a program is rejected for its other
  errors, and with no error it falls back.

R0g fix as built (the review of R0g, round 1: blocker B1):

- B1. A closure that a clause gives to the handled body (C4, in scope from R0g) runs
  on a task of a scope, and the `ir` pipeline lost its changes: `weft check` gave no
  error and the run read a freed cell (`r0grev/p/c4_14c_task_unit.wf` and six more;
  the old pipeline gave W0301). The same hole is older for a closure that a closure
  makes (`let mk = || (|| v.clear()); let f = mk()`, spawned or run in a scope body:
  `t_06`, `t_11`, `t_13`, `t_14`, a HOLE at R0f fix too).
- The root cause is not in the task path. A spawn is always in a scope body, and a
  scope body is a body of its own that names the locals of its site through upvar
  locals. `apply::made_sigma` took the variable of a `Kept` or `ByRef` capture only when
  the walk through the makers reached the body of the run (`made_capture_source`,
  `maker == body`), and `apply::other_maker` walked up from a handled body and a clause,
  but not from a scope body. So in a scope body σ of the capture named only the place
  of the closure value. For a task that place is the task's own (`task_start`, the
  `own` filter), so `task_writes` and the change at the spawn node had nothing; for a
  run in the scope body the change was of the place of `f`.
- The fix (`crates/weft-sema/src/analysis/apply.rs`): `frame_capture_source` tries
  `made_capture_source` for the body of the run and for each body whose frame it runs
  in (a scope body, a handled body, a clause: as `alpha::unit_root`), and α reads the
  source in the body that it found; `other_maker` walks up from a scope body too. The
  states of a body have the values of the locals of those bodies, so the run changes
  the variable itself (`mutates_at`/`reads_at` at the node, `task_writes`/`task_reads`
  of the task, through the code of `task_start` that exists). This closes B1 and the
  older `t_06` family; no fallback is added. A handled body and a clause that run a
  closure that a closure of the site made now name the variable too (more exact facts
  for `fixes/f14/made/k1`, `k2`, `k6`, with the same diagnostics).
- Tests: corpus `tests/programs/196_made_closure_tasks.wf` (W0301 of C4 on a task, of a
  clause closure in a local of the site on a task, of a made closure on a task and in a
  scope body; the clean twins) with its IR golden; probes
  `tests/gate/probes/fixes/r0g/rv1_*.wf` (11: the bad forms and their clean twins;
  `rv1_c4_scope_direct.wf` falls back with an older F16 reason); `weft-check`
  `ir_handlers.rs`
  (`a_task_of_a_closure_whose_value_holds_its_environment_changes_the_environment`, data
  `tests/data/handlers/r0g/rv1_*`).
- The ledger text of `123_resume_scope_ends.wf` (R0g) now names the functions with the
  four `old:` W0301 (`resume_in_closure`, `resume_in_callee`, `moved_in_closure`,
  `cleared_in_closure`, lines 86, 97, 113 and 126): a `resume` in a closure, not in a
  scope body.
- Gates (binary `r0gfix/bin/weft-final`, `weft-gate`): see the rows "R0g fix" of the
  table of the gates. Tier 1 0 blockers: only the 12 new files change (the snapshot of
  the `ir` records against R0g: 7 programs with other diagnostics, all new; 17 other
  digests, the 12 new files and `fixes/f14/made/k1`, `k1_c`, `k2`, `k2_c`, `k6`, `k6_c`).
  The 12 old records are new in `tests/gate/baseline-tier1.jsonl`. Two new lost-clean
  rows (`rv1_c4_task_unit_ok.wf`, `rv1_c4_site_local_spawn_ok.wf`: the old pipeline
  gives W0301 at the spawn line, the interpreter runs them with no fault) are UNSIGNED.
  Tier 2 (2 workers): each class count as R0g, and the rows that are not `same` are
  as R0g. Fact oracle tier 1 0 failures. Sigdiff tier 1 0 rows with no entry (two `sig`
  entries of the fix: `pins` for a task of such a closure, which is `opaque` as at R0g;
  no `raises` for a scope body with no task). `ereview/ev.sh` on the 105 probes of the
  review and the 35 probes of `fixes/r0g`: 0 HOLE but the old `c4_07` (`r0gfix/ev-final.tsv`);
  the 11 HOLE rows of B1 and of the `t_06` family are `held`. The `weft check` result of
  the 1448 programs of the R0g review sets and of R0g's `into.paths` does not change.
- Open: `c4_07` (a clause stores a closure over a clause local into a field of a
  parameter: old W0204, `ir` 0; R0f fix the same), issue #78.

R0h design note (function values across operations: the reasons C2 and D3, and the rest
of C7, E2, E4, E5 and E7):

- The counts before R0h (binary `weft-r0gfix1`, by the note of `weft check`, tier 1 /
  the tier-2 list of R0g; scratchpad `r0h/before-t*.tsv`): C2 19/121, D3 39/93, E2 13/24,
  E7 12/6, C7 10/11, E4 5/91, E5 4/15. `ereview/ev.sh` on these 463 programs: the old
  pipeline rejects each C2, C7 and E5 program. It accepts 15 D3 programs (five of them
  fault: `opres.wf` and three `d1_callee_mut*.wf` of tier 2, a reference that a clause
  gives back), 4 E2, 6 E4 and 3 E7 programs. So the risk of a new false positive is in
  D3 and E only, and the 0.1 % rule of tier 2 has room for no new row.
- C2 (a function value in an argument of an operation of a handler of a caller,
  `templates::perform`). The clause is code of a caller: the body does not know it. So
  the perform node runs the values of the arguments as code of a caller runs them
  (`transfer::apply_value` with `FnVal::Unknown` and `Given::Args`), with the parameter
  types and the result type of the operation: each value can run many times, also after
  the others, and a value that can race (`task_unsafe`) is a task of the node in the
  worst way (W0401, W0403, W0405), as the old lowering does. A perform with such a value
  gets task nodes, as a call of a function value (`frames::value_task_args`). The result
  of the operation can be one of the values (the clause can resume with it). The facts
  of the perform itself (the places of the callers, `escapes_at`, `multi_at`) do not
  change. A perform through a captured capability of a local handler keeps the reason
  (its clause is known, and it runs in the closure).
- D3 (a call that runs a clause of a local handler whose operation gives a function
  value or a reference back to the callee, `clause::given_ops`). Three forms:
  - P: a parameter of the operation holds a function value. The clause gets a value of
    the callee: in the clause it is code of a caller (`FnVal::Unknown`) whose
    environment is the places that the call gives (`clause::given`). So a run of it in
    the clause lends those places.
  - R: the result holds a reference and the clause resumes. σ(`Caller`) of the call gets
    the places that the clauses can give to `resume`: the wildcard places of the locals
    of the site that the clauses name, what their references point into, their `rc`
    groups and the given places. So a change of the callee through the result of the
    operation is a change of those places at the call (F16.3).
  - F: the result holds a function value. The callee runs it as code of a caller runs a
    value: the call node runs the values that the clauses give to `resume` many times,
    at `Main` and at `Ret`, and the result of the call can hold them. A value that can
    race keeps the reason: the call has no task nodes for it (the worst way needs them),
    and the old pipeline accepts a clean sequential run (a new false positive).
- E2, E4, E5, the rest of C7 and E7: each one needs a node or a value that the facts do
  not have (a second run node of a spawn, the values that a shared cell gets after the
  spawn, the places of code that no caller gives). The stage looks at them after C2 and
  D3; a reason that does not get full facts at a reasonable size stays, and "R0h as
  built" says why.
- No rule of the spec changes. `Scope::pending` is not used. Probes:
  `tests/gate/probes/fixes/r0h/` (the bad form and the clean twin of each shape). Corpus:
  `tests/programs/197_fn_values_across_ops.wf`.

R0h as built:

- C2 (`templates::perform`, `transfer::perform_row`): a perform of an operation of a
  handler of a caller with a function value in an argument runs the clause as code of a
  caller that gets the arguments (`transfer::op_value_out`, `OpTy`), with task nodes for
  each argument that can hold a function value (`frames::perform_to_caller`,
  `nodes::phases_with`) and the facts of `templates::value_run` (the part of
  `call_value` that both use). The result of the operation joins the result of the
  code. Two forms keep the reason: a closure that does not race and has a capture whose
  type holds a reference or a function value (`transfer::kept_value_risk`: the code can
  keep it and run it after a change, and the facts of code of a caller have no part for
  a kept value, R0f open item 1; `fixes/r0h/c2_stored_ref.wf` was a hole of the first
  build), and a perform through a captured capability of a local handler.
- D3 (`clause::call_clauses`; the early test of `factgen::emit` and
  `clause::given_ops` are gone): form P, a function value of the callee in a parameter
  of a clause, is code of a caller whose environment is the places that the call gives
  (`clause::Given::values`). Form R, a reference result: σ(`Caller`) of the call also
  names the places that the clauses can give back (`clause::back_places`,
  `Handlers::back`, `Handlers::back_refs`); the new summary part `caller_muts` (the
  body changes a place of a caller; also the worst cases and code of a caller) changes
  them at the call (`apply::main`), the call reads them (`handlers::call_clauses`) and
  its result can point into them (`transfer::back_ret`). This closes the old misses
  `ir/work/map/opres.wf` (issue #48: W0301 in the callee) and `d1_callee_mut*.wf` of tier
  2 (W0301 at the site). Form F, a function value result: the call runs each value that a
  clause gives to `resume` at `Main` and `Ret` as code of a caller runs a value that it
  gets (`transfer::given_back_apps`, `apply_given_back`, `templates::given_back_runs`,
  `Handlers::given_back`, `given_refs`), and the result of the call can be one of them.
  A value that can race, that holds a reference or a function value in a capture, or
  that is `once` keeps the reason (no task nodes for the worst way, no part for a kept
  value, no operand that a second run uses). Only a call that can perform the operation
  counts (`clause::call_performs`): a value call of a closure of a clause that performs
  nothing (`let f = get(); f()`) gives the clause nothing back.
- E2, E4, E5 and the rest of C7 and E7 stay (no full facts at a reasonable size in this
  stage). E2: a spawn has one node, and a second run of a `once` value needs a node after
  the first run; the old pipeline accepts four clean programs of the form
  (`s8_steal_fnparam.wf` in both tiers, `m2/p7046.wf`, `fixes/r0f/c09_cc_during_ok.wf`),
  so a coarse rule is a new false positive (the 0.1 % rule of tier 2 has no room). E4:
  the task needs the values that the shared cell gets after the spawn (the states of the
  later assignments); the old pipeline accepts six clean programs of tier 2
  (`seeds3/gen3_*`, `gen4_*`). E5: a task of code that no caller gives needs the worst way
  of a task with the places of each parameter; each program of the lists is rejected by
  the old pipeline, two with a fault, and the stage leaves it for the next one. C7 and E7:
  a value that a value of a callee runs as a task runs at depth > 0, where the call has no
  task nodes. `Scope::pending` is not used.
- Tests: corpus `tests/programs/197_fn_values_across_ops.wf` (W0403, W0405, W0502 of C2
  and D3 form P; W0301 of form R with an `old:` marker; the clean twins) with its IR
  golden; the `old:` markers of the corpus files that come into scope (63, 86, 89, 122,
  137, 143); probes `tests/gate/probes/fixes/r0h/` (29: the bad forms and their clean
  twins: values run once and twice, on a task, kept in a field, given back as the result,
  with a reference capture, `once` and linear values; references given back, changed,
  given back again, made invalid by a second clause, into a local of a clause; function
  values given back, run after a change, given back again, `once`, racing, spawned);
  `weft-check` `ir_handlers.rs`
  (`function_values_and_references_across_operations_have_full_facts`, data
  `tests/data/handlers/r0h/`), `weft-sema` `scope.rs`
  (`function_values_and_references_across_operations_are_in_scope`; the stub of the
  fallback tests is a clause that gives the callee a value that can race), `cli.rs` (the
  same stub). The claim map-N1 (`opres.wf`) holds in scope; its `edge` entry and the
  `edge` entry of the three `d1_callee_mut` programs of tier 2 are gone.
- The fallbacks, before (R0g fix, binary `weft-r0gfix1`) and after, tier 1 (the 4848
  files of the manifest of R0g fix) / tier 2 (the list of R0g), by the note of `weft
  check` (scratchpad `r0h/before-t*.tsv`, `after-t*.tsv`): C2 19/121 to 5/7, D3 39/93 to
  2/13. The programs whose first failing body was one of these and that still fall back
  show their own reason: C7 10/11 to 14/15, E5 4/15 to 6/31, A2 3/61 to 4/85. E2 13/24,
  E4 5/91 and E7 12/6 do not change. 44 programs of tier 1 and 150 of tier 2 come into
  scope; no program goes out of scope.
- Gates (binary `r0h/bin/weft-final`, `weft-gate`): tier 1 0 blockers (4743 of 4901 in
  scope; 3739 same, 14 open (+6 `open-old` probes of the forms that stay, -1 `opres.wf`),
  276 fixed (+2: `opres.wf`, `fixes/r0h/d3r_callee_mut.wf`, which the old pipeline
  misses), 1 new-fp, 0 lost-fault, 139 lost-clean (+2, UNSIGNED:
  `fixes/r0g/c4_resume_arg_ok.wf`, `partb/s3fix/p/dbg2.wf`), 145 moved (+3), 587 changed
  (+16), each new row ledgered; no program that was in scope changes its class). The old
  records of the 30 new files are new in `tests/gate/baseline-tier1.jsonl`, and the other
  old records do not change. Tier 2 (2 workers) 0 blockers (54393 of 57393 in scope, +150;
  40044 same, 6 open (-4: `opres.wf` and three `d1_callee_mut` programs are `fixed`), 92
  fixed, 12 new-fp (0.096 %, the rows of R0e), 0 lost-fault, 3444 lost-clean (+1, the
  copy of `dbg2.wf`, the UNSIGNED entry), 1857 moved (+20), 11938 changed (+84); each
  row that changes is a program that comes into scope). Fact oracle tier 1 0 failures (8
  faults and 22 timeouts, as R0g; 1315 pass). Sigdiff tier 1 0 rows with no entry (five
  `sig` entries of R0h for 17 programs that come into scope). `ereview/ev.sh` (2 at one
  time): the 44 programs of tier 1 that come into scope, the 29 probes and corpus 197: 0
  HOLE (30 held, 17 rejected by both, 19 no fault, 8 old misses that the `ir` pipeline
  rejects or that fall back); the 150 of tier 2: 0 HOLE (30 held, 111 rejected by both,
  5 no fault, 4 old misses that the `ir` pipeline now rejects); the review sets of R0g
  (`r0grev/p`, `r0grev2/p`) and `fixes/r0g` (245): each verdict as with `weft-r0gfix1`
  but one better (`c4_08` from no fault to rejected by both); the 3 HOLE rows are older
  (`c4_07`, `k09`, `k10`).
- Open: the forms that stay (above); code of a caller that keeps a value (R0f open item
  1, the reason the risky forms stay); the summary oracle (A3) attributes a read or a
  change through a reference that a clause gave to the handled body to the node `handle
  post` (`verify/s5/diff/p/v1d.wf`, also an older program with a direct perform; the
  programs that show it are rejected); a function with a stated row whose body changes a
  place through a reference of an operation result has no such `mut` in its summary
  (W0703 rejects it; `p8_opref_store_caller.wf`).

R0h fix as built (the review of R0h, round 1: seven HOLE rows of one root cause):

- The root cause. `clause::call_clauses` let a value that a clause gives back to the
  callee go on when it could not race, held no reference in a capture and was not `once`.
  For a value of the interface of the site (`FnVal::Param`, `ParamResult`, `Capture`) all
  three tests are false. But the callee can keep such a value in a place that the call
  gives, and the summary of the callee says that the place holds code of a caller
  (`transfer::put_values` gives `FnVal::Unknown`), not the value: so a later run of the
  place in the site or in its caller does not apply the closure that the caller gave
  (`r0hrev/p/f32_param_back_keep.wf`: `s(k)` gives `k` back, `keep(&h)` puts it into
  `h.f`, `main` runs `h.f` after it took a reference into the vector that the closure
  clears; the old pipeline gives W0301, the run reads a freed cell). The same holds for
  a value that a second local clause keeps (`f44`) and through a deeper perform (`f50`).
- The fix (the minimal sound form): only a closure or an item that a clause gives back
  goes on (`clause::call_clauses`); another value keeps the old pipeline (GIVES_BACK).
  The same rule holds for C2: a value of the interface, or a value that the analysis does
  not know, in an argument of an operation of a caller keeps the old pipeline
  (`transfer::op_fn_args`; `c13_param_fn_vec`, `c14`, `c16` of the review; the old
  pipeline misses them too). The precise form (a part of the summary for the values that
  code of a caller keeps, R0f open item 1) is larger: it changes `put_values` for each
  summary, and the review issues #78 and #79 keep it.
- Two more forms of the review. `r01_two_level_mut` (both pipelines missed it): a body
  that calls a function with the part `caller_muts` and has no back places passes the
  part on (`Handlers::caller_muts_at`, `Emitted::caller_muts`, `FnParts::caller_muts`),
  so `outer() { clear_picked() }` changes the places that the clause of `main` gives
  back: W0301. A function with no body has `caller_muts` only for an effect with an
  operation whose result holds a reference. `r39_two_level_param` (a HOLE of R0h; both
  pipelines miss it): the callee holds a reference into its argument `&d` while a callee
  of it clears `d` through the reference that the clause gives back; its own facts do not
  see that the two places are one. A call whose callee changes a place of a caller and
  whose arguments reach a root that a clause names itself (an upvar of the site, a value
  that a clause gave to `resume`) keeps the old pipeline (`transfer::callee_caller_muts`,
  `clause::BackPlaces::named`).
- The summary-oracle failure "a callee makes a read ... at `handle post`" of the review
  showed on the seven programs and on the clean twin `f47_param_back_keep_ok.wf`: these
  programs now keep the old pipeline, so the oracle checks no facts there. The older
  form of the failure (a direct perform, `r0h/t/v3.wf`) stays on rejected programs.
- Not fixed (issues #78, #79): `p02_param_keep`, `p11_closure_relay_keep` (D3 form P: the
  clause keeps a value of the callee; they keep the old pipeline through C2 in the
  callee now, and the old pipeline misses them), `f54_param_result_back` (keeps the old
  pipeline now), and the false positive `c10_ret_fn_out` (2 W0405 of the worst way of
  code of a caller; the old pipeline accepts it, the run is clean).
- Tests: probes `tests/gate/probes/fixes/r0h/rv1_*` (the seven blockers, the clean twin
  `f47`, `r01`); `weft-check` `ir_handlers.rs`
  (`a_given_back_value_of_the_interface_keeps_the_old_pipeline`, data
  `tests/data/handlers/r0h/rv1_*`). The reviewer signed the lost-clean entry of R0h.
- The fallbacks after the fix, tier 1 / tier 2 (the lists of R0h; scratchpad
  `r0h/fix-t*.tsv`): C2 19/121 before R0h, 5/7 at R0h, 17/68 now; D3 39/93, 2/13, 1/1 now
  (most D3 programs whose callee gives a parameter to an operation show C2 now); C7 10/11,
  E5 5/16, A2 3/62. 39 programs of tier 1 and 143 of tier 2 come into scope against R0g
  fix (5 and 7 fewer than at R0h: the copies of the `v1c` files and two mutants of tier 2,
  `m00647_83_kept_values`, `m02208_66_cap_paths`, keep the old pipeline again, which
  rejects them); no program goes out of scope against R0g fix.
- Gates (binary `r0h/bin/weft-fix1`, `weft-gate`): tier 1 0 blockers (4739 of 4910 in
  scope; 3752 same, 14 open, 277 fixed (+1: `rv1_r01_two_level_mut.wf`), 1 new-fp, 0
  lost-fault, 139 lost-clean, 145 moved, 582 changed (-5: the `v1c` files keep the old
  pipeline); the old records of the 9 new probes are new in
  `tests/gate/baseline-tier1.jsonl`). Tier 2 (2 workers) 0 blockers (54386 of 57393 in
  scope; 40051 same, 6 open, 92 fixed, 12 new-fp (0.096 %), 0 lost-fault, 3444
  lost-clean, 1857 moved, 11931 changed; the rows that differ from R0h are the 7 programs
  that keep the old pipeline again). Fact oracle tier 1 0 failures (8 faults, 22
  timeouts, 1315 pass). Sigdiff tier 1 0 rows with no entry (the `sig` entry of the `v1c`
  files is gone). `ereview/ev.sh` (2 at one time) on `fixes/r0h`, `r0hrev/p`,
  `r0grev/p`, `r0grev2/p`, `fixes/r0g` and the into-scope lists of R0h (581 programs):
  0 new HOLE; against `weft-r0gfix1` each verdict is the same or better (127 from no
  fault to rejected by both) but `r0hrev/p/c10_ret_fn_out.wf` (no fault to FP-IR, a
  precision loss); the seven blockers are `held` (the old pipeline rejects them), `f47`
  has no fault; the 3 HOLE rows are older (`c4_07`, `k09`, `k10`).

R0i design note (the other old inputs of the `ir` pipeline; the scope report, "Other
reads of `body/` that R1/R2 do not cover"):

- The inventory at c9da6d3 (scratchpad `r0i/notes.md`). The `ir` pipeline reads:
  - the facts of the old lowering (`Analysis::bodies`): the first facts of each body
    (`factgen::seed`: the name, `effect_names`, `hidden_effects`, `library()`,
    `started()`, `no_runtime()`), the function and the unit of each body (the builder,
    the call graph, `factgen::run`), `no_runtime` of the handlers (`emit_parts`), the
    row of a test body (`BodyFacts::effects`), and the exports of a body with no IR
    (`exports::copy_old`, stage R4);
  - the signatures of the old inference (`Analysis::sigs`). Most reads take a part of
    the declaration (the types, the parameters, the stated places and row,
    `declared`), equal to `FnDef::sig`: the inference changes only `effects`, and only
    the parts other than the row of a function with a stated row. The reads of real
    inferred parts: `pins` of a function with a stated row (`callgraph::summary_of`,
    `effect_sig`), `reaches` of W0118 (`checks::on_abort_rows`), W0701 with the old
    row (`Inference::old_rows`), the rows of the functions with no IR (`IrFacts::sigs`
    starts as a copy of the old signatures), the rows that `fip::check` reads (W1004),
    and the old W0118 for an emit that gives none (`OnAbortRows::old`);
  - the diagnostics of the old lowering that `typeck_only` keeps: the W01xx, W0119,
    W0120 and W0504 of `typeck` (stages R1 and R2), W0303 (a move through a
    reference; `irbuild::reported` reads it for `NoIr::MoveThroughRef`), and W0502 of
    `keep_modes` (a `once` closure into a place of plain data);
  - `Binding::value` of the THIR tables (`ValueProps`: `linear`, `no_on_abort`,
    `once`, `nonportable`): the recorder joins the `VarInfo` of the old value flow, and
    `Builder::binding_props_of` puts it into the `LocalDecl::props` of a local of a
    function type (also the cleanup: a `linear` local gets an `UnwindValue`);
  - the constants `body::roots`.
- The stage is two parts. Part a (this commit, "R0i as built") removes each read of the
  old inference and of the old facts but `copy_old`: the declarations of the bodies
  come from the program, the effect names from the facts of the IR, each signature
  part from the declaration or from the summary, W0118 and W1004 from the signatures of
  the `ir` pipeline. It changes no class of the gate.
- Part b (R0i-b, the design for the next stage): the reads of the old value flow and of
  the move diagnostics. They share one need: the builder must know the closures that
  a local of a function type can hold, and it must go on after an error.
  - `ValueProps`: the builder makes each body with the properties of the types only,
    then a pass over the IR of the component joins, for each local of a function type,
    the properties of the closures that reach it (`closure_props` of each
    `Aggregate(Closure)`, a `Use` of another local, a field or an element read of a
    place that holds one, the `ret.fns` and `ret.linear` of the summary of a callee,
    the values that a clause or a resume gives). A parameter of a function type, and
    code of a caller, are `many` and not linear (the caller cannot give a `once` or a
    linear closure there: W0502, W0601 at the call). The cleanup reads `linear`, so a
    body whose locals get a new property is built again with them (a fixpoint: at
    most four bits for each local). The test: for each body of tiers 1 and 2, the
    properties equal the `ValueProps` of the recorder, else a ledger entry.
  - W0502 of `keep_modes`: with these properties, `factgen` checks each operand that
    holds a `once` value and goes into a place of plain data: a field or an element of
    an aggregate, the place of an assignment that is not a new binding, an argument of
    a parameter that the callee keeps (the parts `puts` and `put_fns` of its summary),
    with the text of the old lowering.
  - W0303: the builder records each move through a reference with the span of the
    expression and the text of its type (`TyTable::show`, with the text of the old
    lowering for a function type: `fn() -> ()`), gives a placeholder operand and goes
    on; a body with a record has the outcome `NoIr::MoveThroughRef` and the builder
    gives the diagnostics (14 programs of tier 1 have more than one W0303 in a body).
    `irbuild::reported` reads them, and W0303 joins `IR_DROPS`. A body that the
    builder stops for another reason after a record keeps the record (the program has
    the error, so it stays in scope as now).
  - The gate: ideally no class change; `ereview/ev.sh` on each program whose
    diagnostics change.

R0i as built (part a):

- The constants of the roots are `crate::roots` (`body::roots` uses them again for
  the old lowering; `weft-check` reads `weft_sema::roots`).
- `Analysis::decls` holds a `BodyDecl` for each body (the function, the unit, the
  module, the name, `library()`, `started()`, `no_runtime()`), from the program and
  the options (`lib.rs`, `body_decls`). `factgen::seed`, the builder, the call graph,
  `factgen::run` and `exports::fill` read it, not the old facts.
- `decls::effect_names` (with `std_effect`, before `decls::std_effects`) gives the
  names of the user effects from the facts of the IR. 13 programs of tier 1 change
  only the text of a diagnostic: an effect that only the facts of the IR name showed
  its identity (`main.Note`) and the note of a private effect; now it shows its name
  (`Note`) and the note of a missing handler (W0805, W0702; for example
  `r2/fidelity/p/e1_resume_abort.wf`).
- The reads of a declaration part take `FnDef::sig`. `pins` of a function with a
  stated row comes from the body only (65 functions of 30 files of tier 1 lose the
  `pins` of the old inference: a `sig` entry of class F19-SIG-PINS; the interpreter
  reads `pins` only for a function item that `http.serve` runs, and none of them is
  one). `Inference::old_rows` is gone (each function with IR has a summary).
  `factgen::ir_sigs` gives `IrFacts::sigs`: the summary rows, and the declaration of
  each other function; `IrFacts::no_ir` lists the functions whose body has no IR, and
  `weft-gate sigdiff` and the test of the corpus signatures do not compare them. A
  first build gave such a function the row of the worst case of its declaration: then
  W1004 (`49_fip_paths.wf`, `unknown`) and W0901 (four packages of tier 2, for
  example `verify/partb/S3/pkg1`) came from the worst case, as more errors of a
  program with a type error. A test body has an empty row.
- W0118 reads `reaches` from the summary (`checks::reaches`: a run of the part `runs`
  that is not a task, or `unknown_multi`), only for a function with IR. The 14 programs
  of tier 1 with this W0118 keep it. A first build counted each run and the worst case
  too: then a function with a type error (`fd1_v2_generic.wf`, nine mutants of
  `r2/oracle/runs`) and `verify/s5/R3x/p1/c14_task.wf` (a task `s.spawn(|| x)` with
  `x` of a type parameter: the summary has a run of the parameter as a task) got one
  more W0118. `factgen::run` gives W0118 for an emit with none. `OnAbortRows` is gone.
- `fip`: `factgen::run` checks each `fip` function with the signatures of the `ir`
  pipeline.
- Test: `weft-sema` `tests.rs`
  `the_ir_pipeline_reads_no_old_signature_and_no_old_fact` (a run on an analysis with
  wrong old signatures and old facts gives the same facts, rows and diagnostics).
- What still reads the old pipeline: `copy_old` (stage R4), the THIR tables and the
  `typeck` diagnostics (stages R1, R2), `ValueProps`, W0502 and W0303 (R0i-b).
- Gates (binary `r0i/bin/weft-final`, `weft-gate`): tier 1 0 blockers, each row as at
  R0h fix (4739 of 4910 in scope; 3752 same, 14 open, 277 fixed, 1 new-fp, 0
  lost-fault, 139 lost-clean, 145 moved, 582 changed). Tier 2 (2 workers) 0 blockers,
  each row as at R0h fix (54386 of 57393 in scope; 40051 same, 6 open, 92 fixed, 12
  new-fp (0.096 %), 0 lost-fault, 3444 lost-clean, 1857 moved, 11931 changed; 4
  timeouts). Fact oracle tier 1 0 failures (8 faults, 22 timeouts, 1315 pass, as R0h
  fix). Sigdiff tier 1 0 rows with no entry (40076 functions compared, 584 fewer: the
  functions with no IR; the new `sig` entry of R0i for `pins`). No new probe, so the
  manifest, the oracle caches and the baseline of tier 1 do not change; no new
  lost-clean row. The diagnostics of `weft check` on `tests/programs` and
  `tests/gate/probes` (5247 files) against `weft-r0hfix1`: only the 13 texts of the
  effect names change; `ereview/ev.sh` on those 13 and the 30 files of the `pins` entry
  (44 with the first-build file `fd1_v2_generic.wf`): each verdict and each fact-oracle
  column as with `weft-r0hfix1` (21 held, 14 rejected by both, 7 no fault, 2 old
  misses; 0 HOLE).

R0i fix as built (the review of R0i, round 1: no blocker; the lost diagnostics of the
review, scratchpad `r0irev/notes.md`):

- W0118 `reaches` (`checks::reaches`). Part a left out each task run ("the scope gives
  W0118 already"), but a local `Fail` handler around the scope catches the failure of
  the scope (`summarize::caught`): `r31`, `r34`, `r35`, `r37`, `r38`, `r40`, `r41` of
  the review lost the W0118 of the old inference, and the unwinder run faults (no
  handler for `Ask.ask`); W0601 and W0602 of the old `ValueProps` held them, so they
  would be holes after R0i-b. Now a run of the part `runs` counts, a call or a task,
  if it is a run of a capture or of a parameter whose type has a function part
  (`props::ir_has_fns`); a task of a value of a type parameter (`s.spawn(|| x)`,
  `verify/s5/R3x/p1/c14_task.wf`) does not.
- A run of a function value that the body does not know: `unknown_multi` is the
  `multi` of the program, so part a missed the run in a program with no `multi`
  operation (`r16`: W0118 lost; `r05`, `r14`, `r17`, `r19`: the line lost). The new
  summary part `unknown_runs` (`Em::code_unknown`: a run of code of a caller that is no
  value of the interface; `Handlers::unknown_runs_at`: a call of a function or a
  closure with the part; `Inferred::unknown_runs`) gives it, also through a callee:
  `r18` (an `on abort` function that calls a function that runs an extern result) now
  gets W0118, which both binaries before missed (`ev.sh`: HOLE+oldmiss to oldmiss; the
  fault is the stub of the extern function). `unknown_multi` does not count any more:
  the worst case of a callee with no IR has it (`r28` keeps its rows).
- `weft deps`: a function whose body has no IR gets the row of the worst case of its
  declaration again (`factgen::ir_sigs`; a stated row stays), so W0901 of
  `fixes/r0i/pkg1_deps_noir` stays (it names each standard effect but `io`, not only
  `log`). The four packages of tier 2 that got a new W0901 in the first build of part
  a get it (`verify/partb/S3/pkg1`, `verify/review_edge/Edge/pkg2`: an unknown name;
  `verify/quality/manifests/depitems`, `verify/review_edge/Edge/pkg3`: a declaration
  error); the worst case is sound but not precise (`pkg3` `info` only prints), and each
  program has the error of the body already (a comment in the ledger). `fip` takes the
  declaration of a function with no IR: `f06` of the review loses the old W1004 (its
  W1003 and W0102 stay).
- `irbuild::reported` and `typeck_error` count no code of `OLD_INFERENCE_CODES` (W0118
  and W1001 to W1004: `analyze` gives them from the old signatures for the old
  pipeline). The test `the_ir_pipeline_reads_no_old_signature_and_no_old_fact` also
  takes these diagnostics out of `Analysis::diags` and puts wrong ones in, and it has
  a program with a declaration error and the probes `r31`, `r16`.
- The ledger entry F19-SIG-PINS of R0i names the part `pins` of the summary too (the
  `opaque` mark of a task, the stealable sink, the callers): the review found the same
  `weft facts` and the same oracle runs on the 30 files.
- R3 must move `crate::infer::{growth_limit, not_converged, SIG_PLACE_STEPS}` out of
  `infer.rs` before it deletes it (R3 text).
- Probes `tests/gate/probes/fixes/r0i/` (15 files of the review and the package
  `pkg1_deps_noir`); tests `analysis_units.rs`
  `an_on_abort_function_that_runs_an_unknown_value_is_w0118`, `cli.rs`
  `a_dependency_function_with_no_ir_keeps_its_authority`.
- Gates (binary `r0i/bin/weft-fix1`, `weft-gate-fix1`): tier 1 0 blockers (4926; 3756
  same, 14 open, 278 fixed, 1 new-fp, 0 lost-fault, 139 lost-clean, 145 moved, 593
  changed: the 16 new probes are 4 same, 1 fixed (`r18`) and 11 changed, each one
  rejected by both and accepted by entry 6; the other rows as at R0i). The manifest, the
  two oracle caches and `tests/gate/baseline-tier1.jsonl` get the 16 rows of the new
  probes, and no other row changes. Tier 2 (2 workers) 0 blockers (40047 same, 6 open,
  92 fixed, 12 new-fp (0.096 %), 0 lost-fault, 3444 lost-clean, 1857 moved, 11935
  changed; 4 timeouts): against R0h fix only the four packages of the W0901 of the
  worst case (`same` to `changed`, both reject, `ev.sh` the same verdicts with both
  binaries). Fact oracle tier 1 0 failures (8 faults, 22 timeouts, 1315 pass). Sigdiff
  tier 1 0 rows with no entry (two `sig` entries of the fix for the new probes). The
  diagnostics of `weft check` on `tests/programs`, `tests/gate/probes` and
  `r0irev/p` against `weft-r0hfix1`: the 13 texts of R0i, `r18` (one more W0118, a
  real one) and `f06` (W1004 goes); `ereview/ev.sh` on these: each verdict the same but
  `r18` (HOLE+oldmiss to oldmiss); 0 new HOLE. The review probes `r31` to `r41`, `r05`,
  `r14`, `r16`, `r17`, `r19` and `r28` have the diagnostics of `weft-r0hfix1` again.

R0i-b as built (the old value flow and the move diagnostics; the review of R0i, round
2, also found that the part `unknown_runs` was not set in closure and clause bodies):

- `irbuild::values` gives the properties of the values of the bindings
  (`BindingValues`: linear, no `on abort`, `once`, nonportable) from the IR: a value flow
  over the whole program to its fixpoint. Each local starts with the props of its
  declaration; a closure gets the props of its captures (`once` also for a capture that
  is not `many` or `@ uniq`, and for a body that calls a `once` value) and of
  `ClosureDecl::once`; an assignment, an aggregate, a reference, an iterator, a call (the
  result of the callee with the arguments for the parameters that its result can be),
  a write behind a reference or into an `rc` object (also of a callee, by parameter, and
  of a callee with no body into an argument that is a reference to a type with a
  function part: `Vec.push`), a perform (the clause parameters, the values of `resume`),
  a `handle`, a `scope` and an upvar pass them on. A parameter gets nothing from the
  callers, as in the old value flow. `Builder::binding_props_of` reads them
  (`Decls::values`), not `thir::Binding::value`. The builder runs in rounds
  (`irbuild::build_all`, at most `MAX_ROUNDS`): the first with the props of the types,
  each next one with the values of the IR of the round before, until they do not change
  (the cleanup reads `linear`, so the IR depends on them). `build_with` is the test hook
  that builds with given values. A closure that captures a `@ uniq` value (the analysis
  knows the mode, the builder does not) is not `many`: `factgen::not_many` marks each
  variable of a local of a type with a function part that can hold it (W0503).
- A scratch test compared the local props of the bindings with those of the old values
  on the 5374 files of `tests/programs`, `tests/gate/probes` and the review probes
  (scratchpad `r0i/vcmp.tsv`): 113 144 the same, 203 more and 193 fewer in an early
  build. The IR gives more for a linear closure that a clause parameter, a `Vec` or a
  handle result gets, and for a closure of a returned closure; fewer for a closure that
  captures a `@ uniq` reference (`not_many` gives it in the facts) and for parts of a
  container whose type does not show them. The diagnostics decide: the diff below.
  A capture of a type with no function part takes the props of its declaration (a part
  of a linear struct is not linear by itself: `verify/s5/R3x/p1/c1_closure.wf` keeps
  W0118 of a dropped type parameter), and a reference to a place behind a reference
  (`&(*ks)`) points where that reference points (so a callee that pushes into `ks` gives
  its caller the value, not its own parameter: `stored_linear.wf` of `weft-check`).
- W0303: the builder records each move through a reference (`read_place` with the
  location of the expression, of the statement for `let x = <place>`; `bind_how`) and
  goes on; the body has no IR and the builder gives each W0303 (`Decls::moves`). A move
  out of an `rc` object gives W0303 with IR (the old lowering gave it). A copy of a
  function value behind a reference or an `rc` object whose value can be a closure that
  moves a capture and whose type does not come from a declared function type is W0303
  too (`values::once_reads`, `fixes`: `r3/redteam/p/f2_kesc.wf`). `irbuild::reported`
  does not read W0303 of the old lowering; W0303 and W0502 join `IR_DROPS`.
- W0502 of `keep_modes`: `values::once_into_plain` (`docs/ir.md` 5.36). A closure that
  moves a capture and is not linear goes into a field of a declared function type of a
  struct or variant literal, into an assignment to such a field, or into an argument of
  a function item whose parameter type is not a function type while another argument is
  a place of a stated type (a parameter, a `let` with a stated type, `Decls::stated`, a
  field). A body with no IR gives no W0502 (`verify/s5/R2c/p/c1.wf` and `or9_v1.wf`
  lose the old W0502 of a body with a type error).
- `unknown_runs` in closure and clause bodies: `closure_summary` gives it from its `Em`
  (`summarize::closure`), a clause sets `Handlers::clause_unknown`, and the function
  counts each node of `Handlers::unknown_runs_at` (the clauses of the function too). So
  `u06`, `u13`, `u14` of the review get W0118 again, and `u18` to `u20` (an item that
  runs an extern result, called from a clause, a closure or a task) get it now (each
  pipeline before missed them). `u04` (an item that runs an extern result as a task)
  stays (ledger `open-old` R0i-U04: the fault is the stub of the extern function).
- r31 to r41 of the first review: each one is still rejected (W0118 of `reaches`, and
  W0601 and W0602 of the values of the IR).
- Tests: `weft-sema` `tests.rs` `the_ir_pipeline_reads_no_old_signature_and_no_old_fact`
  (also wrong `Binding::value` and wrong W0303 and W0502 of the old lowering),
  `analysis_units.rs` (`the_builder_gives_w0303_and_w0502_of_a_once_closure`,
  `the_values_of_the_bindings_come_from_the_ir`, the probes `u06` to `u20` in
  `an_on_abort_function_that_runs_an_unknown_value_is_w0118`); probes
  `tests/gate/probes/fixes/r0i/` (`u01` to `u20`, `g01` to `g07` of the review).
- What still reads the old pipeline: `copy_old` (stage R4), the THIR tables and the
  `typeck` diagnostics (R1, R2). The recorder still fills `Binding::value`, and no part of
  the `ir` pipeline reads it.
- Gates (binaries `r0i/bin/weft-b1`, `weft-gate-b1`): tier 1 0 blockers (4953 of
  them; 3768 same, 15 open, 283 fixed, 1 new-fp, 0 lost-fault, 140 lost-clean, 145
  moved, 601 changed: the 27 new probes are 13 same, 1 open (`u04`, ledger `open-old`),
  5 fixed (`u03`, `u09`, `u18` to `u20`), 8 changed; `c2_linear_drop` gets W0601 and
  W0602 of the clause (ledger `changed`); `d6_closure_via_clause` is `lost-clean`
  (UNSIGNED, below); the other rows as at R0i fix). The manifest, the oracle caches and
  the baseline of tier 1 get the 27 rows of the new probes, and no old record changes.
  Tier 2 (2 workers) 0 blockers (40045 same, 6 open, 92 fixed, 12 new-fp (0.096 %), 0
  lost-fault, 3446 lost-clean (+2: `d6` and `verify/s5/R3t/w0303.wf`, both UNSIGNED),
  1857 moved, 11935 changed; 4 timeouts). The rows that differ from R0i fix: `w0303.wf`
  (lost-clean: the old W0303 of a copy of a closure that moves no capture), `o35vv.wf`
  (the same W0303 goes, still rejected; ledger `changed`), `p4982`, `p25330` (one more
  W0401 or W0503 on a line with the code), two mutants of corpus 122 and the copies of
  `c1.wf` and `or9_v1.wf` (the old W0502 of a body with no IR goes), `d6`. Fact oracle
  tier 1 0 failures (8 faults, 22 timeouts, 1316 pass). Sigdiff tier 1 0 rows with no
  entry (ledger `sig` entries for `g03`, `g05`, `u09`, `u12`).
- The diagnostics of `weft check` on `tests/programs`, `tests/gate/probes` and the review
  probes (`r0irev/p`, `r0irev2/p`) against `weft-r0ifix1`: `c2_linear_drop` (+W0601,
  W0602), `d6_closure_via_clause` (-W0601 at the end of `main`), `c1.wf` and `or9_v1.wf`
  (-W0502 in a body with a type error), and the probes `u01`, `u02`, `u06`, `u08`,
  `u09`, `u13` to `u16`, `u18` to `u20` (W0118 of `reaches`). `ereview/ev.sh` (2 at one
  time) on these and on the rows of tier 2 above (23 files): each verdict is the same or
  better (`u06`, `u13`, `u14` HOLE to held; `u18` to `u20` HOLE+oldmiss to oldmiss;
  `w0303` both-reject to no fault) but `d6`: held(AST-only) to HOLE(AST-only). The IR
  engine runs `d6` clean (seeds 1 to 3) and the fact oracle passes; only the AST engine
  faults, when it runs the `on abort` of `tx` that the closure kept by the clause owns
  (the AST compiler goes in stage R4). The lost-clean row is UNSIGNED for the review.

R0i-b fix as built (the review of R0i-b, round 1: a blocker of one root cause):

- The blocker. `irbuild::values` had no rule for the terminators `Spawn`, `Join`, `Fork`
  and `Resume`, though each one gives its destination a value. A linear closure that
  came back from `t.join()`, from a `fork` branch or as the value of `resume(..)` in a
  clause was not linear in the IR, so the cleanup gave the local no `UnwindValue`, and
  on an abort the `on abort` of the captured value did not run (the IR engine: "a live
  linear value is left after the cleanup chain"; `fixes/r0i/rb/a16_task_join`, `a21`,
  `a22`, `a23_fork_result`, `a28_resume_dest`).
- The fix: a task handle names its spawn site (`Val::tasks`), and the result of each
  site is the result of a run of the value of the task (`Flow::tasks`, also for a branch
  of a `fork` and for the `TaskResult` local of a task that the scope keeps); a `join`
  gives the result of each site of the handle, a `fork` the results of its branches,
  and `resume` the value `_0` of the handled body of its clause (`Flow::handled_of`, also
  from a closure of the clause). Each terminator that gives a destination a value has a
  rule now. The probes give `rollback 1` on the IR engine, as with `weft-r0ifix1`, and
  `a07`, `a09`, `a11`, `a19` (HOLE with `weft-r0ifix1`) stay closed.
- A capture of a type with a function part in a field (`Holder { cb: fn() }`) takes
  the value of the flow (`props::ir_has_fns`, not `TyTable::mentions_fn`, which sees
  only the type arguments); `the_values_of_the_bindings_come_from_the_ir` checks that
  such a struct holds a linear closure.
- Not fixed: `a25_join_dropped`, `a27_fork_dropped` (a linear closure from a `join` or a
  `fork` that the program drops: no W0601 in any binary of the `ir` pipeline; the old
  pipeline rejects them). The IR has the value now (the local is linear and its cleanup
  runs), but the analysis of the facts gives the run of a task the result
  `FnVal::Unknown` with no linear flag (`tasks::task_result`, `handle_value`), so no
  W0601 at the end of the local. The fix needs the result of a task in the domain of the
  analysis (a part for the values of a task); it is larger than this fix, and the two
  probes, which are `lost-fault`, are not in the probe set (scratchpad
  `r0i/rb-excluded/`). `n06_resume_fork` (W0401 of a nonportable closure that comes back
  from an operation and a `fork` branch runs; the oracle does not check it, so the
  gate class is new-fp, which the 0.1 % rule of tier 1 has no room for; FP-IR also with
  `weft-r0ifix1`) is not in the set either, and neither are `a07_resume` and
  `n06_resume_spawn`: the summary oracle (A3) fails on them with each binary
  (`weft-r0ifix1` too; a read of a value that a clause gave to the handled body is at
  the node `handle post`, the open item of R0h fix), so they would be the first
  failures of the fact oracle of tier 1; `a07` (a HOLE of `weft-r0ifix1`) runs clean
  on the IR engine with the fix.
- Probes: the 127 other probes of the review in `tests/gate/probes/fixes/r0i/rb/`; the
  test `analysis_units.rs`
  `a_linear_closure_from_a_task_a_fork_or_resume_is_linear` (the five blockers). The
  reviewer signed the two lost-clean rows of R0i-b (`d6_closure_via_clause`,
  `verify/s5/R3t/w0303.wf`). New ledger rows: 12 lost-clean probes of the review that the
  `ir` pipeline accepts and the IR engine runs clean (UNSIGNED), 28 `changed` and 1
  `moved` (both pipelines reject), three `sig` entries.
- Gates (binaries `r0i/bin/weft-b2`, `weft-gate-b2`): tier 1 0 blockers (5080; 3847 same,
  15 open, 285 fixed, 1 new-fp, 0 lost-fault, 152 lost-clean, 146 moved, 634 changed:
  the 127 probes are 79 same, 2 fixed, 12 lost-clean, 1 moved, 33 changed; the other
  rows as at R0i-b). The manifest, the oracle caches and the baseline of tier 1 get the
  127 rows, and no old record changes. Tier 2 (2 workers) 0 blockers, each row as at
  R0i-b (40045 same, 6 open, 92 fixed, 12 new-fp (0.096 %), 0 lost-fault, 3446
  lost-clean, 1857 moved, 11935 changed; 5 timeouts, one more than R0i-b on a loaded
  machine). Fact oracle tier 1 0 failures (8 faults, 22 timeouts, 1350 pass). Sigdiff
  tier 1 0 rows with no entry.
- The diagnostics of `weft check` on `tests/programs`, `tests/gate/probes` and the
  review probes against `weft-r0ib1`: only `rb/n04_holder_whole_fork` and
  `rb/n13_holder_callee_fork` (W0401 a second time on the line of the `fork`: the holder
  holds the nonportable closure, `ir_has_fns`). Against `weft-r0ifix1`: the changes of
  R0i-b and these two. `ereview/ev.sh` (2 at one time) with the three binaries on the
  36 files that change, and on the five blockers and `a07`, `a09`, `a11`, `a19`: the
  blockers HOLE (with `weft-r0ib1`) to no fault (as with `weft-r0ifix1`); `a07`, `a09`,
  `a11`, `a19` no fault (HOLE with `weft-r0ifix1`); each other verdict as with
  `weft-r0ib1` (`n06_resume_fork` FP-IR with each binary, `d6` HOLE(AST-only), signed);
  `a25`, `a27` HOLE with each binary (above).

R0j design note (the task fallbacks of groups E and C; 58 programs of tier 1 with
`weft-r0ib2`):

- The six reasons. E: a task that runs a callback more than once (`TASK_AGAIN`, 13), a
  task that runs a function variable that gets a new value (`TASK_LATE`, 11), a task
  that runs code of a caller (`TASK_CODE`, F19, 8), a task of a scope that the spawn does
  not name and that the analysis does not find (E3b, 4). C: a function value that a
  function value of a callee runs as a task (R0e fix 2, 12), a function value that runs
  a value of its arguments as a task (`VALUE_TASKS`, 10).
- Full facts. E3b: a scope operand that can be the capability of more than one scope,
  and of no other value. Each of these scopes is live at the spawn, so the scopes are
  nested, and the task ends at or before the end of the outer scope. The facts end the
  task at the outer scope (`SiteScope::end`: `joined_at` at its `ScopeWait` and on its
  cleanup chain). A task that ends at an inner scope runs a longer time in the facts:
  this is sound for each check of a running task, and it can only add errors. A spawn
  through a reference to the capability, or on scopes that are not nested in one unit,
  stays pending (below).
- The other five reasons need facts of a new kind: a second node for each run of a
  value that a task runs again (a spawn has one node), the later values of a shared
  cell in the run at the spawn node, the worst way of code of a caller (with the places
  that the code changes), and the task nodes of a value that a value runs as a task.
  Each one is a stage of its own (size L), with its own proofs. In this stage these
  forms use the rule of stage R0g (`Scope::pending`): the facts keep the weak form (the
  run at the spawn node, the code of a caller as a plain run), the `ir` pipeline checks
  the program first, and an `ir` error is final. Else the old pipeline checks the
  program, as before. A rejected program does not run, so a rejection with facts that
  are not whole lets no fault through. The `ir` pipeline can report fewer errors of a
  rejected program than the old pipeline (corpus `84_task_stores.wf`,
  `114_repeated_callbacks.wf`: `old:` markers).
- What stays. A program of these five forms that the `ir` pipeline accepts: the old
  pipeline checks it. A function value that changes places or holds a nonportable value,
  and that code of a caller can run on another thread (F18, `TASK_RUN`), which R0j
  shows on four programs of tier 1 that failed first on another reason: with the weak
  facts the worst way of a foreign task gives W0403 at the call of a clean program
  (`fixes/r0j/j07_run_ok.wf`), so the pending rule does not apply, and the reason stays.
- No rule of the spec changes. Probes: `tests/gate/probes/fixes/r0j/` (a bad form and a
  clean twin of each reason). Tests: `scope.rs` `the_task_fallbacks_are_pending`,
  `analysis_units.rs` `a_spawn_on_one_of_nested_scopes_ends_its_task_at_the_outer_scope`.

R0j as built:

- E3b (full facts): `tasks::SiteScope::end` gives the scope that ends the task: the one
  scope of the operand, or the outer one of more than one scope whose bodies nest in one
  unit (`unit_inside`), if the operand can be no other value. `templates::site_in_scope`,
  `unowned_spawn`, `handlers::owned_by_value` and `handlers::owned_by_clause` read it.
  A spawn through a reference to the capability (`fixes/r0e/u10_ref_scope.wf`) stays
  pending.
- Pending (`templates::pending`, `clause::note_pending`): `TASK_AGAIN`, `TASK_LATE`,
  `TASK_CODE` (`templates::task_start`), `VALUE_TASKS` (`value_run`: the run keeps no
  task nodes) and R0e fix 2 (`transfer::NESTED_TASK_RUN`). `TASK_RUN` (F18) stays a
  fallback (design note).
- Corpus: `84_task_stores.wf` (three lines `old: W0314`), `114_repeated_callbacks.wf`
  (one line `old: W0301`). The probe `fixes/r0i/rb/n11_enum_nongeneric_fork.wf` leaves
  the gate set: with the pending rule its correct W0401 (a nonportable closure in a
  `fork` branch) is a new-fp row of the oracle, which sees no fault, and tier 1 has room
  for no second new-fp row.
- Fallbacks: tier 1 125 to 84 on the files of R0i-b (91 with the 17 probes of
  `fixes/r0j/`; left of the R0j reasons: `TASK_AGAIN` 4, R0e fix 2 4, `TASK_LATE` 3, and
  `TASK_RUN` 4, which the end of the first reason shows); tier 2 3007 to 2907.
- Gates (binaries `r0j/bin/weft-j1`, `weft-gate-j1`): tier 1 0 blockers (5096; 3838 same,
  14 open, 286 fixed, 1 new-fp, 0 lost-fault, 152 lost-clean, 146 moved, 659 changed);
  tier 2 (2 workers) 0 blockers (39990 same, 6 open, 92 fixed, 12 new-fp (0.096 %), 0
  lost-fault, 3446 lost-clean, 1858 moved, 11989 changed); fact oracle tier 1 0 failures
  (8 faults, 22 timeouts, 1352 pass); sigdiff tier 1 0 rows with no entry. No new
  lost-clean row. New ledger rows: one `changed` entry, one `moved` entry, two `sig`
  entries; the `open-old` entry R0i-U04 goes (the `ir` pipeline gives W0118 now).
- `ereview/ev.sh` on the 48 files whose diagnostics or scope change, against
  `weft-r0ib2`: 31 held to held, 13 fallback to both-reject, `j06_unowned_ok` no fault,
  `fixes/r0i/u04_item_task_extern.wf` FP-IR (its fault is the stub of an extern function,
  "a task needs a closure", which `ev.sh` does not count; the gate row is `fixed`). No
  HOLE.

R0k design note (revised at R0k-a; the first form of the note is in 5d8106c): the
operation fallbacks C2 and D3, the re-entry forms and the task leftovers (91 fallbacks
of tier 1 with `weft-r0j1`: C2 21, D3 18, D1 18, D5 6, F18 6, E2 5, R0e fix 2 5, E4 4,
A 3, D4 2, E5 1, C8 1, `VALUE_TASKS` 1):

- The pending rule does not apply to C2 and D3: its weak forms reject clean programs
  (`fixes/r0k/k01_c2_param_ok`, `k02_c2_capture_ok`, `fixes/r0h/d3f_dangling_ok`).
- C2 and D3 by call-site copies (stage R0k-a, below): a call that a local handler serves
  with a function value or a reference gets a copy of the code of the callee, so the
  perform is a perform of the local handler. The design review of R0k (scratchpad
  `r0kdes/notes.md`) showed that a summary part (`op_values`, and the order part
  `before(o)`/`after(o)`/`Back(o)` of the first form of this note) is unsound for a
  perform that runs more than once (a loop, two performs, `multi`) unless it has a cycle
  for each repeated perform, and the copy gets those orders from the CFG.
- What stays for later stages:
  - Closure-body copies: a perform in a closure that the callee (or the site) makes and
    runs, and a perform through a captured capability of a local handler. R0k-a2 (below)
    copies a closure that the body makes and runs (`rv_p07_d3_in_closure` and its twin).
    The other forms need the value at the run node from the states and an environment
    local (R0k-b1 design note): `verify/s5/S5a/x/p/e2b_e_job`, `e2b_e_mk_job`,
    `e2b_e_struct`, `e2b_variants`, `verify/partb/p/a2_escapes`, `a4_get_own`,
    `verify/s5/diff/p/v1c_stored`, `partb/s3fix/p/b2_call`,
    `tests/programs/66_cap_paths.wf`, `85_op_args.wf`, and `verify/partb/p/g2_lexical`
    (D3, a closure that a clause makes performs the effect of an outer handler).
  - Recursive callees and callees over the bound: the summary-part design of the first
    form of this note, with the changes of the design review (a cycle
    `Back(o) -> after(o) -> Back(o)` for a repeated perform, a clause run per perform,
    loans and reads in the split, composition through calls and closure runs, the abort
    edges, `multi` re-entry to `Back(o)`), is the plan for them. No program of tier 1
    needs it now.
  - D1, D5 and C8 (stage R0k-c): a resume point of the clause at the run node of a closure
    that resumes a captured continuation, and copied clause frames for a `multi`
    operation in a clause. A copy that brings such a construct in keeps the fallback
    (`rv_p04_c2_multi`, `rv_p12_c2_task_after_perform`).
  - The task leftovers, D4 and A: as in the first form of this note (E2 a second node of
    the run at the spawn; E4 the values of the cell at each assignment; R0e fix 2 and
    `VALUE_TASKS` the task nodes of a value that a value runs as a task; F18 the places of
    the other tasks of the callee in the worst way; D4 a strong update after a `resume`;
    A the starts of the region of a `resume` for a clause run that maps to no node).

R0k-a as built (call-site copies for C2 and D3; `docs/ir.md` 6.1, "As built (plan stage
R0k-a)"):

- The copy (`factgen/instantiate.rs`). An IR-to-IR pass gives a program in which a call
  that a local handler serves gets the code of its callee: the environment of the call
  binds an effect that the callee performs through its row (also through its callees)
  with a function value or a reference in an argument or the result (`Needs`, a fixpoint
  over the calls). Bounds: no type arguments, a body, not recursive (the call graph),
  a chain of at most 8 copies, at most 6000 added blocks (`Bounds`). The parameters
  are variables bound to the operands at a new entry block, `_0` is a temporary that a
  `Return` moves into the destination, the `UnwindExit` of the callee goes to the
  cleanup block of the call. Each body inside the callee gets a copy with new
  closure, handler, scope, spawn and environment ids; a body inside a closure of the
  callee keeps the environment of the closure body (`Copy::ctx`). A perform through the
  row that the environment of the call serves goes to the capability of the serving
  handler (upvar locals in the bodies on the way); a closure of the callee gets a `Cap`
  capture for each served effect that its code can use (performs, the rows of its
  calls, each effect for a call of a value with no stated row), as the builder does for
  a closure of the site. The copies are scanned again, so a callee of a copy gets a
  copy. The verifier checks the result (V16 is not checked in a body with a copy).
- The scope (`factgen::run`, `components_built`). The copies are made only if the
  program falls back with C2 (`OP_KEPT`) or D3 (`GIVES_BACK`) without them, so no
  program that was in scope changes. The second emit runs on the copy; a fallback of
  the second emit gives its own reason, and a construct with no full facts that the
  copy brings in (`Scope::pending`, the D5 weak form of `rv_p04_c2_multi_ok`) keeps the
  first fallback. The fact oracle runs the copy (`weft-interp`, `components_built`).
- The weak form and its invariant. In the facts of a callee, a perform through the row
  with a value that the clause can keep has the weak form of R0h (`WeakRowOps`,
  `transfer::op_fn_args`). The invariant: no call that a local handler serves applies
  the summary of such a body. `Instantiated::weak_ok` checks it on the copy (no served
  call of such a callee is left, and no closure, function item value, `main` or test
  can run one); the analysis checks it again (`transfer::note_weak_call`: a served
  call of a summary with the weak form, also through a callee or a function item
  value, is `OP_KEPT`). The test `analysis_units` `copies::a_served_call_of_a_summary_
  with_the_weak_form_keeps_the_old_pipeline` turns the weak form on with no copies and
  sees the guard refuse the program.
- Three fixes that the copies needed (each one shows on the inline form today):
  - A call of a function value runs no clause of a local handler when the analysis
    knows each value that it runs and none performs the effect of the handler or runs a
    function value (`clause::call_clauses`, `Handlers::no_clause`, `run_handlers`; a
    `Fail` handler stays). Before, the static destinations of the call ran the clause
    again at the run of a value that the clause gave back, so a `once` closure that the
    clause made moved its capture again (`k06_d3_once_ok`: W0302; `let c = || eat(v);
    resume(c)` run once: W0502). The cause was not `made_sigma`. With the clause
    gone from such a node, σ of a closure that a clause makes and the handled body
    runs maps a `Kept` or `ByRef` capture of an upvar of the clause to the variable of
    the site (`apply::made_capture_source` follows the upvar locals), so the node
    reads the variable (the summary oracle found the missing read on
    `fixes/r0h/d3f_returned_ok`, `d3f_dangling_ok` and `fixes/r0k/k08_d3_kept_ok`).
  - The D3 fallback applies to a `multi` operation whose result holds a function value
    (`clause::op_multi`): the run of the clause stops at its first `resume`, so the
    values of a later `resume` were not in the facts (`rv_p09_d3_multi`, an `ir` hole).
  - The fact oracle (`oracle/facts.rs`, `step`): a clause frame takes `Post` of the
    `handle` as its site only when it leaves the location of a `resume`; the read of the
    operand of a `resume` that is the first location of the clause is code before the
    resume point (`resume(k)` of a local of the site failed A3 at `handle post`:
    `rv1_f47_param_back_keep_ok`, `k05_d3_param_ok`, `rv_p05_d3_two_performs_ok`). Test
    `summary_oracle.rs` `a_clause_that_resumes_with_a_site_local_reads_it_at_the_perform_node`
    (the facts pass; with the read gone they fail). No fact changes.
- Tests: `analysis_units` `copies` (parameters and result, the cleanup edge, the served
  perform, a callee of a callee, a closure of a copy, a recursive callee, the bounds, the
  weak guard); `weft-interp` `copies.rs` (each probe of `fixes/r0h` and `fixes/r0k` with a
  copy runs with and without the copies with the same output and fault);
  `summary_oracle.rs` (above); `ir_handlers.rs` (`c2_stored_ref`, `d3f_mut_race`,
  `d3f_reader_ok`, `rv1_f32`, `rv1_f47`, `rv1_c13` in scope;
  `a_call_with_no_copy_keeps_the_old_pipeline`: a recursive callee and a perform in a
  closure that the callee runs); `scope.rs` and `cli.rs` (the stub of the fallback tests is
  a perform in a closure that the callee runs). Probes `fixes/r0k/`: the clean twins of
  the probes of the design review (`rv_*_ok`), `k09` (a `once` value of the site that the
  clause gives back, run once, then `v` used: W0302; and the clean twin), `k10` (a `once`
  value that the clause makes), `k11` (a value of the site given back at the first location
  of the clause, and the clean twin, for the fact oracle).
- Not done: a note of the diagnostic that names the call of a copy (a diagnostic in the
  code of a copy points into the callee).
- The fallbacks, tier 1 (the 5142 files of the manifest; scratchpad `r0k/a/base2-t1.tsv`,
  `ka1-t1.tsv`), before (`weft-r0j1`) and after: all 132 to 72; C2 35 to 12, D3 42 to 4.
  Of the 39 C2 and D3 programs of tier 1 before R0k (without `fixes/r0k`), 26 come into
  scope (19 rejected, 7 accepted). What stays: the closure forms of R0k-a2 (R0k design
  note: `e2b_*`, `a2_escapes`, `a4_get_own`, `v1c_stored`, `b2_call`, `66_cap_paths`,
  `85_op_args`, `g2_lexical`, `rv_p07` and its twin), `rv_p04` and its twin (the copy brings
  in D5), `fixes/r0h/d3f_task` (the copy brings in a task that runs code of a caller), and
  `83_kept_values` (with the copies: a perform whose rest of the handled body the facts do
  not find). No program that was in scope changes its record in tier 1 but
  `rv_p09_d3_multi` (W0301, the hole is closed). Tier 2 (the 57393 files; `base-t2.tsv`,
  `ka1-t2.tsv`): C2 68 to 39 (7 into scope, 22 show the reason A now), D3 1 to 1; in scope
  54486 to 54493. Three programs of tier 2 that were in scope lose a diagnostic of the
  `ir` pipeline that the old pipeline does not give either (the clause of a local handler
  ran at a call of a function value that cannot perform its effect:
  `r2/oracle/runs/g5/p21542.wf` W0312, `r3/oracle/runs/g3b/p11406.wf` W0602) or gives at
  other lines (`r2/oracle/t0/q266.wf` W0602); each one stays rejected.
- Size and time: the facts of the programs that come into scope have about the rows of
  the old facts (9419 against 9791 for the 57 programs of tier 1 of the prototype; the
  largest ratio 3.45, `rv_p10_d3_abort_path`). Programs that were in scope have the same
  facts. The tier-1 check time does not change (the slowest program, `s5/h4000.wf`, has no
  copy; the slowest program with a copy takes 0.08 s).
- Gates (binaries `r0k/a/bin/weft-ka1`, `weft-gate-ka1`): tier 1 0 blockers (5142; 3862
  same, 12 open, 305 fixed, 1 new-fp, 0 lost-fault, 153 lost-clean, 146 moved, 663
  changed); tier 2 (2 workers) 0 blockers (39989 same, 6 open, 92 fixed, 12 new-fp
  (0.096 %), 0 lost-fault, 3446 lost-clean, 1858 moved, 11990 changed); fact oracle tier 1
  0 failures (8 faults, 22 timeouts, 1376 pass); sigdiff tier 1 0 rows with no entry
  (three `sig` entries of R0k: the weak C2 summaries, the bodies with a copy, `main` with a
  local `multi` handler). The interpreter sources changed (the fact oracle), so the oracle
  caches of tiers 1 and 2 were made again; the verdicts of tier 1 are the same but for
  two runs at the time limit (`r3/fidelity/p/hs1.wf`, `s5/h4000.wf`: timeouts, no fault).
  Ledger: the `open-old` entries of R0h-STAYS keep only the probes that still fall back
  and fault (`c2_task`, `rv_p04`, `rv_p07`, `rv_p12`); the entry of `k02`, `k06`, `k07`,
  `k08` and the entry R0k-P09 go (class `fixed`); a `changed` entry for four programs that
  come into scope, and an UNSIGNED `lost-clean` entry for `d3f_returned_ok` (the old W0301
  is a false positive). `ereview/ev.sh` on the 65 files of tier 1 and the 10 of tier 2
  whose record changes, against `weft-r0j1`: no HOLE; 19 faults that both pipelines
  missed are now rejected by the `ir` pipeline (`rv_p09` was a HOLE); no new FP-IR.

R0k-a2 as built (static closure copies, generic callees, the closure guard; `docs/ir.md` 6.1,
"As built (plan stage R0k-a2)"):

- A, the static closure copy (`instantiate::closure_copy`, `What::Closure`,
  `copy_code`). A call of a function value whose callee is a local with one value, a
  closure that the same body makes (`single_value`, also through a copy into the callee
  temporary), gets a copy of the closure body, if the closure performs an operation with a
  function value or a reference through a captured capability, or calls a callee that
  performs one. The environment goes to the site (`PlaceMap`): `Kept` the source, `ByRef`
  a new borrow at the entry (ended at each exit of the copy), `Cap` the capability. The
  copy mentions the closure value at its entry. The capability environment of the copy is
  the one where the closure is made (the maker is the site). Refused, so the call keeps the
  summary of the closure: another way to give the local a value (`a04_two_closures`: two
  closures can reach it), a move or a borrow of the local, a `once` closure, a `ByMove` or
  `Kont` capture (`a05_by_value`), a source of a `Kept` or `ByRef` capture that ends or gets
  a new cell between the closure and the run (the source language gives a value of a block
  instead, `a06_ends`, refused for its other value; the test `analysis_units`
  `copies::a_closure_copy_is_refused_for_a_source_that_ends_before_the_run` puts a `Dead`
  in by hand), a use of the whole environment, a body inside the closure that names the
  environment.
- C, a generic callee (`subst_program`, `subst_ty`): the copy has the body under the type
  arguments of the call (the types of the locals, the aggregates, the calls and the
  function item values, new types in the type table, the properties of a changed type
  again; a `move` of a place of a copy type is a copy, V9). The language has no traits or
  bounds, so a type parameter of a callee is a plain type. The reviewer's `c09_generic` and
  the probes `c09_generic_two_*` (two type arguments at two sites) are in scope.
- D, the closure guard. A perform through a captured capability with a function value has
  the weak form in the facts of its closure (`templates::perform`, `OP_FN_ARGS` with
  `WeakRowOps`). `transfer::WeakKey` keeps the summaries with the weak form, of functions
  and of closures (`weak_owner`: the innermost closure of the body, else its function).
  `note_weak_call` (from `clause::call_clauses`) checks the callee, the values that a call
  of a function value runs, and the values that a call gives to its callee;
  `weak_values_stay` (each terminator) refuses a `spawn`, a `fork`, a `perform` or a
  `resume` that gives such a value away. The structural check of `weak_ok` does not
  change. Test: `analysis_units`
  `copies::a_served_run_of_a_closure_with_the_weak_form_keeps_the_old_pipeline` (the weak
  form on, no copy: the guard refuses the run; with the copy the program is in scope).
- The fix of the review of R0k-a2 (round 1, a blocker: `u04_task_reassigns` and
  `u08_task_join` were new holes). The one-value rule read only the statements of the body
  that owns the local; a body inside it (a scope body or a task, a handled body, a clause,
  also a clause that a perform of a callee runs, a closure, and each body inside them) can
  give the local another closure through an upvar local or a capture, and the copy then
  checked a program that does not run. Now each write, move or borrow of a place of a body
  inside the owner whose cell is the local refuses the copy (`nested_writes`: `cell_of`
  follows the upvar locals to the parent, and `env.k` of a `Kept` capture and `(*env.k)` of
  a `ByRef` capture to the source in the maker; the inner bodies come from the parent
  chain, not from a list of body kinds). A write through a reference to the local needs a
  borrow of it: in the owner the one-value rule refuses it, in a body inside the owner
  `nested_writes` sees the borrow. Probes `fixes/r0k2/u03` to `u10` (bad: each keeps the
  fallback or is rejected), `u11` (the clean twin: it keeps the fallback), `g26` (a closure
  with the weak form given to `apply`, which the analysis runs before the maker: the guard
  refuses); tests `analysis_units`
  `copies::a_closure_copy_is_refused_when_a_nested_body_writes_the_local` and
  `copies::the_weak_guard_refuses_a_value_given_to_a_body_analyzed_before_its_maker`. The
  refusal under a shadowed capability (`s05`, `s05b` of the review) stays.
- c10 (a task of the callee runs the given-back value) stays a fallback: with the copy the
  program brings in a task that runs code of a caller (E, `TASK_CODE`, pending), so the
  first fallback stays (R0k-a, step 2). It is task work (the task nodes of a given-back
  value), not a copy.
- Probes `tests/gate/probes/fixes/r0k2/`: `a01_kept`, `a02_byref`, `a03_cap` (the three
  capture kinds; bad: W0301, ok: no error), `a04_two_closures`, `a05_by_value`, `a06_ends`
  (the refusals; both twins keep the fallback), `c09_generic_two` (bad: W0301). The
  differential test `copies.rs` reads `fixes/r0k2` and needs at least 8 probes with a
  closure copy.
- The fallbacks, against `weft-r0ka1` (R0k-a), tier 1 (the 5156 files of the manifest;
  scratchpad `r0k/a2/ka1-t1.tsv`, `ka2-t1.tsv`): all 86 to 76, C2 14 to 12, D3 16 to 8. The
  rows that change: `rv_p07_d3_in_closure` (W0301: both pipelines missed its fault) and its
  twin, and the new probes `a01`, `a02`, `a03`, `c09_generic_two` (bad: W0301; ok: no
  error). No program that was in scope changes. Tier 2 (57393; `r0k/a/ka1-t2.tsv`,
  `r0k/a2/ka2-t2.tsv`): no row changes (C2 39, D3 1, 234 noted fallbacks; in scope 54493):
  its closure forms are the forms of R0k-b1. The reviewer's `c09_generic` and
  `w05_callee_calls_helper_closure` come into scope with W0301.
- Gates (binaries `r0k/a2/bin/weft-ka2`, `weft-gate-ka2`): tier 1 0 blockers (5156; 3874
  same, 11 open, 307 fixed, 1 new-fp, 0 lost-fault, 153 lost-clean, 146 moved, 664
  changed; one `changed` entry for `a03_cap_bad`: the old W0312 of the worst way); tier 2
  (2 workers) 0 blockers (39989 same, 6 open, 92 fixed, 12 new-fp (0.096 %), 0 lost-fault,
  3446 lost-clean, 1858 moved, 11990 changed); fact oracle tier 1 0 failures (8 faults, 22
  timeouts, 1381 pass); sigdiff tier 1 0 rows with no entry. The interpreter sources do not
  change, so the oracle caches only get the rows of the new probes. Ledger: `rv_p07` leaves
  the `open-old` entry R0h-STAYS (class `fixed`). `ereview/ev.sh` against `weft-r0ka1` on
  the 10 rows that change and on the 51 probes of the review of R0k-a (`r0karev/p`): no
  HOLE, no new FP-IR; `rv_p07`, `c09_generic_two_bad`, `c09_generic` and `w05` go from an
  old miss with a fallback to rejected by the `ir` pipeline.

R0k-b1 design note: copies of closure bodies with an environment local (not built: B1 as
written is not sound, see "R0k-b1 design check" after the note):

- The forms. After R0k-a2 the C2 and D3 fallbacks are performs in closures whose value at
  the run node the IR does not show (R0k design note): (2) a closure that a callee makes
  and gives back, run later by the site (`e2b_e_cap` `mk_cap`, `e2b_e_mk_job`, 85 `mk` and
  `mk_spawner`, `a2_escapes` `via_id`, `via_wrap`, `via_pair`); (3) a closure in a field,
  a `Vec`, an `Option` or a `Box`, read out and run (`e2b_e_struct` `m.c`, `v1c_stored`
  `Job.f` in `run_it`, 66 `box_out`, `a2_escapes` `via_pop`, `via_option`); (4) a closure
  that a clause gets and runs or spawns (`e2b_e_job`, 85 `callee_gives*`, `a4_get_own`);
  (5) a program where `weak_ok` is false because a closure performs a risky operation
  through its row (85 `mk`). Each one is rejected by the old pipeline (W0313, W0314) but
  the tier-2 mutants of 66 and 85 count for R0z.
- The closure identity at the run node, from the first phase. The first emit stops at the
  first body with an `Unsupported`, so its states are not whole. B1 adds a probe run of the
  analysis before the copies: each body is analyzed with `Later` noted, not raised (the
  `Scope::pending` machinery of R0g, with a note in place of the error), callees first as
  in `callgraph::infer`, and `Handlers` records the values of the callee operand at each
  call of a function value (`run_values: (BodyId, BlockId) -> BTreeSet<FnVal>`, from
  `transfer::reach_fns` on the state before the call). `instantiate` reads the map. A run
  node gets a copy only if its set is one closure (`FnVal::Closure(c)` or `FnVal::Made(c)`)
  or one function item (`FnVal::Item(f, ts)`: the call becomes `Callee::Fn(f, ts)` and gets
  the copy of R0k-a). A set with more than one value, `Unknown`, a parameter, or a capture
  of an outer closure keeps the summary. The probe states are not used for facts. The identity must
  be exact (the review of R0k-a2): a copy replaces the run by the body of one closure, so it
  is sound only if the value is always that closure. (a) The probe states over-approximate
  the function values of each local: an unmodeled construct (a noted `Later`) widens each
  local that it can write to `Unknown`. (b) The writes through upvars and captures of the
  bodies inside the owner count (the R0k-a2 fix `nested_writes` of the static copy is the
  same rule in a syntactic form). (c) The fact oracle checks at each copied run node that
  the run sees the copied closure (a cheap net for (a) and (b)).
- The environment local. The copy of the closure body at the run node binds the
  environment to the closure value instead of rewriting each capture to a place of the
  site (R0k-a2): a new local kind `LocalKind::CopyEnv(ClosureId)` in the site body is a view
  of the callee operand (`env := copy l` at the entry of the copy, as `Env` names the
  closure value of the run node; no `Live` or `Dead`, as `Env`). `env.k..` keeps its form.
  - α: `alpha::env_capture` accepts a `CopyEnv(c)` local of any body (closure `c`, capture
    `k`); α of `env.k` is σ of capture `k` of the made value, as `apply::made_sigma` gives it
    at the run node: for a `Kept` or `ByRef` capture whose variable is a variable of the
    frame (`made_capture_source`, the upvar walk of R0k-a2) that variable, else the places
    of the closure value and its references and cells (`transfer::cell_values`); for `Cap`
    the live capability (`apply::live_cap`); for `ByMove` the place of the field of the
    closure value.
  - The variables: `E(copy, k)` for a `ByMove` capture (as `E(cb, k)` of a closure body),
    owned by the closure value variable; `S` of the callee local stays the owner of the
    places of the environment, so a use of `env.k` uses it.
  - The templates: the statements of the copy use the env forms of the closure body
    (`Em::base_var`, `vars_in` with a `CopyEnv` local); a `once` closure moves `E` at its
    moves; the copy mentions the callee operand at its entry (R0k-a2), so the loans of the
    closure value live up to the run.
  - The verifier: V-rules on `CopyEnv` as on `Env` (only fields, a move of a field only for
    a `once` closure), and V11 for `Local(env.k)` performs of a `Cap` field.
  - The interpreter and the fact oracle: the IR engine evaluates `env.k` on the value of
    the local (the closure object of the callee operand); the oracle names the cells of the
    fields of that object as the places of α of `env.k` (the rule of a closure frame today,
    "a captured cell of a closure frame is the cell of `env.k`"), with the copy as a part of
    the frame of the site.
- Captures of callee locals that end before the run. The closure value keeps the cells of
  its `Kept` captures (the interpreter keeps them alive; the facts give them the places of
  the value and its cells, `made_sigma`). The copy reads and writes those places through
  `env`, never through the dead local of the callee, so no `Dead` of the callee frame is on
  the way. A reference into such a cell is valid while the closure value lives: the cells
  are places of the closure value variable, so its `scope_end` and its moves end them (W0301
  for a later use), as for a run of a made closure today.
- The forms, in the design: (2) the run node of the callee local holds `Made(c)` → copy with
  `CopyEnv(c)`; (3) the value read out of the field into the callee temporary holds
  `Made(c)` or `Closure(c)` → the same; a run straight from a heap slot (`(*h).f()`) keeps the
  summary; (4) a run in a clause body (`f()` of a parameter `f` that the analysis knows as
  one closure) → a copy into the clause body (the clause is a component of its own; the
  copy is a part of it); a spawn or a fork of such a value keeps the fallback (a task run is
  no call node; W0314). The made value can hold a reference into a local of the frame of
  the performer (C2), and the clause can run it after its `resume`, when that frame has
  ended: `CopyEnv` keeps the cells of the `Kept` captures, but a reference in them still
  points into the frame. The clause facts end those referents at the `resume` node of the
  clause at the latest (the end of the performer's frame is in the resume region,
  `handlers.rs` `of`), so a run after it is W0301. Acceptance tests: the probes p01, p02 and
  p03 of the design review of R0k, written so that the clause runs the value (no call-site
  copy); (5) `weak_ok` accepts a closure with a risky row perform if each run
  node of it in the probe states got a copy (a set of copied run nodes per closure), and the
  analysis guard (`note_weak_call`, `weak_values_stay`, R0k-a2) stays on in the second
  emit: the run nodes of the probe states are a may set.
- Bounds: the block bound and the depth bound of R0k-a (a closure copy counts in the chain
  with the closure id, so a closure that runs itself through a value gets no copy); at most
  one closure per run node (above); no copy at a run node inside a loop whose closure value
  changes in the loop (the probe set has more than one value there anyway).
- What stays a fallback: a run node with more than one value or an unknown value, a task run
  of a closure (`spawn`, `fork`, a clause that spawns its argument: E2/W0314 work), a `Kont`
  capture (D1), a run of a closure outside the handler of its capability (W0313, the escape
  check rejects most), a generic closure value whose type arguments the run node does not
  give, and the D5 and E pending forms that a copy brings in (R0k-a).
- Size L plus M: the copy with `CopyEnv` (a new local kind: the verifier, the IR printer and
  the goldens, both interpreter engines that run the copy, the fact oracle and α; no spec
  relation changes) is L; the probe run (an analysis mode with notes in place of errors) is
  a second part of size M. Tests: the probes of forms 2 to 5 with bad and clean twins, the
  R0k-a2 copies test extended to `CopyEnv`, the fact oracle on each copy, the guard tests,
  and these acceptance probes: a callee that returns one of two closures on two paths (it
  stays a fallback); the same closure id pushed twice into a `Vec` with other captures, the
  second run after the source of the first one changed; a closure read from a field that a
  callee overwrites (`put_fns`) before the run; a closure assigned in a scope body, a clause
  and a task before the run (`u03` to `u10` of the review of R0k-a2, in the form of B1); a
  `once` closure copied at two run nodes (the second run is W0502).

R0k-b1 design check (the stage stopped before the build; probes `fixes/r0k3/`):

- Why B1 as written is not sound. A closure runs with the handler environment of its
  maker: the interpreter runs a closure value with the handlers of the point where it was
  made (`c.henv`), and a function item with the handlers of the call. The IR builder gives
  a closure a `Cap` capture only for an effect that a local handler serves where the
  closure is made. Each other effect of the closure body uses the handler environment of
  the maker: a perform through the row, a call that passes the root environment, a
  failure of the runtime to `Fail`. That environment is not a field of the closure value,
  so `CopyEnv` does not hold it, and `FnVal::Made(c)` names the code but not the
  environment. A copy of the closure body at the run node takes the handlers of the run
  node, so it changes the target of those performs, calls and failures. For a closure
  that a callee makes (form 2; forms 3 and 5 with a closure of a callee) the environment
  is that of the call of the maker, which the run node does not know. The probes:
  `h01_row_in_maker_env` (m1: a closure made in the handled body of `Run` runs in the
  handled body of `Note`, and its `note` goes to the row of `main`: W0805);
  `h02_made_closure_row` (m2: the closure of `mk` runs in the local handler of `outer`,
  and its `run` goes to the handler of `main`: the program prints 1, not 9);
  `h03_made_closure_keep_bad` (m3: the same, and the clause of `main` keeps the function
  value, which reads a local of `outer` after `outer` ends: a read of a freed cell; today
  the C2 fallback, and the old pipeline misses it, ledger `R0k3-HENV`; a copy with the
  handlers of the run node gives the value to the harmless local handler, and the copied
  program has no fault, a hole) and its clean twin `h03_made_closure_keep_ok`.
- The exact subset. A closure that the function of the run node makes (in its body, or in
  its handled bodies, clauses and scope bodies) has the static environment of its
  declaration (`cap_env`), and the copy can map the row and the calls through it, as
  R0k-a2 does; a function item value runs with the handlers of the run node. The subset
  gains about 0 files of the tiers (by a read of the targets): each target file keeps a
  reason. A closure that a callee makes (`mk_cap`, `mk_job`, `mk_struct`, `mk`,
  `mk_spawner`): `85_op_args`, `e2b_e_job`, `e2b_e_mk_job`, `e2b_e_struct`,
  `e2b_variants`, the fuzz copy of 85, and the 31 tier-2 mutants of 66 and 85. A run in
  another function through a parameter (`run_it`, `apply`): `v1c_stored`, `g26`. A clause
  that gets the value from a call (a parameter of a clause is `Unknown` at a call) and
  runs it as a task (W0314, a task run stays a fallback): `e2b_e_job`, the
  `callee_gives*` functions of 85. A capability that leaves its handler (W0313): `box_out`
  of 66, `a4_get_own`, `a2_escapes`. Other reasons: `rv_p04` (D5), `g2_lexical` and
  `a04` to `a06` (D3), `u03` to `u11` (two values at the run node), and the large
  programs with task runs (`r3/oracle/runs/m3a/p6152`, `m3b/p26666`).
- The direction for a later B1'. The handler environment becomes explicit: the builder
  gives each closure a capture for each effect of its row and for `Fail`, and at the
  point where the closure is made binds each capture to the capability of the maker (a
  pass-on capability for an effect that the maker performs through its row, `Row(E)`).
  Then the closure value holds its environment, and `CopyEnv` is exact: `env.k` of such a
  capture is the capability of the maker at the run. B1' needs a new capture form or a
  new capability operand, the verifier, both interpreter engines, the fact oracle and α.
  It is needed for R0z (forms 2 to 5, the 31 tier-2 mutants of 66 and 85), and it needs a
  design review of its own.

R0k-c1 as built (copies of continuation closures in clauses, D1a and D1c; `docs/ir.md`
6.1, "As built (plan stage R0k-c1)"):

- The design check (scratchpad `r0k/c/notes.md`). D1 has four forms in the tiers: a
  closure that the clause makes and runs (D1a), the same closure given to a callee that
  runs it (D1c), a `resume` in a scope body while a task of the scope is alive (D1b), and
  a resume in a task, a fork or a closure that the runtime runs (`sim.run`,
  `with_timeout`). For D1a and D1c the identity is exact: the closure is made in the clause,
  so its handler environment is the static environment of its declaration (the gap of
  R0k-b1 does not apply), and its `Kont` capture is the continuation of the same
  activation of the clause. The other forms stay fallbacks (task work, and code of the
  runtime).
- The copy (`instantiate::instantiate_kont`, `Inst::kont_copy`, `kont_wants`). A run of a
  closure in a clause that resumes the continuation of the clause gets a copy of the
  closure body; a callee that gets such a closure gets a copy at the call first (the
  rules of R0k-a: bounds, `weak_ok`, the verifier). The hard rules of `docs/ir.md` 6.1 (a
  call, a chain of whole locals, no use in a body inside the clause, no other use of the
  continuation, each path from the make reaches the run with no unwind edge, no abort,
  no perform and no call) decide the copy; if one fails, the program keeps its fallback.
  For a `once` continuation the make and the steps of the chain go (the copy resumes the
  continuation local); for a `multi` one the make stays and the copy reads the source.
  V16 (`KontNotFirst`) does not hold for a cleanup chain that starts in a block of a copy.
- The phase (`factgen::run`, `kont_view`, `Pending::copy`, `weft_check::check_pending`,
  `factgen::components_built`). The copies apply only to a program whose constructs with
  no full facts are all `KONT_CAPTURED`. The emit with the copies covers the closures of
  the copies (`clause::KontCovered`: their bodies keep the weak `resume`, and no run applies
  their summary) and must have no construct with no full facts. The check takes the facts
  without the copies first: with an error, the result is as before; else the facts of the
  copies check the program, and it is in scope. So no program that was in scope changes.
- Tests: `analysis_units` `kont_copies` (the `once` copy and the removal of the make, the
  `multi` copy, D1c, each refusal: two runs, a perform between, a call between, a borrow of
  the value, a make in a body inside the clause, a field, the continuation named again, a
  body inside the clause that names the chain, a spawn, a path that misses the run, and
  the view of the copies); `weft-interp` `copies.rs`
  `the_copies_of_continuation_closures_do_not_change_the_runs` (each probe of `fixes/r0kc`
  and `fixes/r0g` with such a copy runs with and without it with the same output and
  fault; at least 8 probes, at least 4 with the removal of the make). Probes
  `tests/gate/probes/fixes/r0kc/` (bad: W0301 after the clause clears a vector that the
  handled body borrowed; clean twin): `c01_once`, `c02_multi`, `c04_callee` (in scope),
  `c03_two_runs`, `c05_perform_between`, `c06_call_between`, `c07_use_after`,
  `c08_nested`, `c09_field` (fallback).
- The fallbacks, against `weft-r0ka2r2`, tier 1 (5188 files; scratchpad
  `r0k/c/r2-t1b.tsv`, `kc1-t1.tsv`): all 107 to 96, D1 39 to 28. The 11 rows that change:
  `fixes/r0g/d1_kont_once_ok` (accepted), `d1_kont_post_ref`,
  `ir/judge_sound/j2_post_resume_closure`, `R2c/rr5_v8_resume_in_closure`,
  `rr5_v9_closure_resume_frees` (W0301, the same codes and lines as the old pipeline),
  and the probes `c01`, `c02`, `c04` (bad and clean). No other row changes.
  Tier 2 (57393; `r0k/c/r2-t2.tsv`, `kc1-t2.tsv`): all 232 to 212, D1 49 to 27 (C2 39, D3
  1, D5 5 do not change). The 22 rows that change come into scope, each rejected by both
  pipelines: `j2`, `rr5_v8`, `rr5_v9` (as in tier 1) and 19 mutants of `rr5_v8` in
  `r3/oracle/runs/m3a` and `m3b` (a closure that resumes in the clause, and the same closure
  given to `call_it`), with the codes of the old pipeline. Two of them
  (`m3a/p2942`, `m3a/p4814`) lose the old W0301 at line 119: the mutant clears the
  vector before the perform, so the clause takes `r` after the clear and nothing changes
  it later; a variant that `main` reaches runs clean and the `ir` pipeline accepts it
  (scratchpad `r0k/c/x/h2.wf`), so that W0301 was a false positive of the old pipeline.
  Both stay rejected (W0301 at line 81; ledger entry of the class `changed` of the earlier
  stages). No other row changes (7 large programs time out at 120 s in the census with
  `weft-r0ka2r2`, a slower build; with `r0k/b1/bin/weft-b1note`, the release build of the
  same code, their rows are the same as with `weft-r0kc1`).
- Gates (binaries `r0k/c/bin/weft-r0kc1`, `weft-gate-r0kc1`): tier 1 0 blockers (5188;
  3900 same, 17 open, 307 fixed, 1 new-fp, 0 lost-fault, 153 lost-clean, 146 moved, 664
  changed: the 18 new probes are `same`, and each other count is that of R0k-b1); tier 2
  (2 workers) 0 blockers (39987 same, 6 open, 92 fixed, 12 new-fp, 0 lost-fault, 3446
  lost-clean, 1858 moved, 11992 changed: the two rows above leave `same`); fact oracle
  tier 1 0 failures (8 faults, 22 timeouts, 1386 pass); sigdiff tier 1 0 rows with no
  entry. The interpreter sources do not change (the differential test runs the copy
  through the public API), so the oracle caches only get the rows of the new probes.
  `ereview/ev.sh` against `weft-r0ka2r2` on the 23 rows of tier 1 (the 18 probes and the
  5 programs that come into scope) and the 19 mutants of tier 2: no HOLE, no FP-IR; the
  fact oracle passes on each copy.

R0k-c2 design note (D5 and C8: a re-entry of a clause frame; built, R0k-c2 as built below; the design review
gave GO WITH CHANGES, and this text has its changes, scratchpad `r0kc2des/notes.md`):

- The forms. A clause performs a `multi` operation of a handler of a caller (D5) or of a
  local handler (C8) after or before its `resume`; each later `resume` of that handler
  runs the rest of the clause again from a copy of the clause frame, then the code that
  the clause returns to (the rest of the function after the `handle`). Tier 1: 7 files,
  all clean (`fixes/r0g/d5_after_resume_ok`, `c8_nested_after_ok`,
  `r2/fidelity/p/multi_nested_drop`, `multi_nested_drop2`, `multi_nested_ok`, the copy of
  `multi_nested_drop` in `weft-interp`, `R2c/fd2_v1_three_levels`); tier 2: 5 (four of the
  same files, `r2/oracle/runs/m1/p1669`). `fd2_v2` and `fd2_v3` also need it (with D1).
  The fallback also hides a fault that the old pipeline misses: `fixes/r0kc2/m7_rc_shared`
  (a read of a freed cell in the second copy; open-old `R0k2C-M7`), so the stage is a
  soundness gain too.
- No IR copy: the number of re-entries is a value of the run. The facts need the design
  of the R0d note: re-entry edges in the component of the clause from its `Return`, its
  landing and its `Resume` nodes to a `Copy` node of the row; a run of the analysis of the
  clause from the block after the row; each node that runs the clause as a row of the
  function (a `Copy` node with edges from the `Return`s of the function to its `Landing`;
  for a row in the `post` part, a `Copy` phase of the `Post` node of the `handle`); the
  cycles of E2; for C8 the `Post` of the local `multi` handler in place of the `Return` of
  the function. A clause frame that waits at its `resume` waits there in the copy too
  (`copy_list`).
- The continuation records. The machine copies them: `copy_frames`
  (`weft-interp/src/machine/effects.rs`, the copy of a `Frame::Clause` and of the nested
  continuation records) gives each copy of a clause frame a new record of its
  continuation, in the state of the record at the row, with a copy of its frames
  (`proofs/link/README.md`, "Differences"). Each copy resumes or drops its own record. So
  the re-entry state of the continuation local of the clause, and of each continuation in
  a copied frame, is its state at the row, not the state at the end of the previous copy
  (E6). The facts take the row state: the re-entry seed has the locals of the copied
  frames as at the row node (as the re-entry of a function body does, OL-R2a). A carried
  state (the state at the end of the previous copy) would only be conservative for a
  `once` continuation (a fresh one is W0503 across the row in both models, `m4`; one that
  is used before the row is used in both, `m5`), but it is not the model, so the facts do
  not use it.
- The re-entry heap rule (E5), for every frame of the continuation: the clause frame, the
  function that has the local handler and its `post` code, the callers up to the handled
  body of the `multi` handler, and the frames of the nested continuations. A place that
  these frames own (their slots and temporaries, and the buffers that their values own,
  `heap.owned_cells`: a `Vec` or a `Box`, from the types) takes its state at the row, and
  a reference into it is valid as at the row (the machine remaps it to the copy): `m3`
  (the function clears its own local after the `handle`; the second copy reads a
  reference into its copy: clean). A shared place (an `rc` object, a place of a frame
  above the `multi` handler, a cell that no copied frame owns) takes its state after the
  previous run and the code of the outer clause between the resumes: `m7` (the function
  clears a `Vec` in an `rc` object after the `handle`: a read of a freed cell), `m1` (the
  outer clause clears a vector of `main` between its resumes: W0301). This is the rule of
  the re-entry of a function body (owned cells copied, `rc` shared), applied to all the
  copied frames, not only to the locals of the clause. "The heap of the end of the
  function" for owned places gives a false W0301 on `m3`.
- The check of the environments. The handler environment of a clause frame is static (the
  outer environment of the handler), so it is exact. The ownership of the cells that a
  copy duplicates is a property of the values at the run; the facts decide it from the
  types, as the re-entry of a function body does (`m3` and `m7` are the probes).
- Proofs: E1 to E4 for the new cycle (a run of a value of the interface in the re-entered
  region is `many` unless they hold), and:
  - E5: the owned/shared split of the re-entry state (above), with the references into
    owned cells remapped;
  - E6: the state of each continuation record at the re-entry is its state at the row;
  - E7: each value that is not `many` (a task handle, a scope, a `!Move` value, a fresh
    `once` continuation) and that is live across the row in any copied frame, not only in
    the clause, is W0503 (as the old pipeline gives; `m4`).
- The fact oracle (A4). It must name the copied cells (the `map` of `copy_frames`) as the
  places of the copied frame, so that an access in a copy is checked against the facts of
  the `Copy` node, and check the state of each reference at the re-entry (valid for an
  owned place, as after the previous run for a shared one). Two mutation tests: a build
  whose re-entry state takes the state at the end of the function for owned places must
  fail the oracle on `m3`, and one that takes the row state for shared places must fail it
  on `m7`.
- What it needs: the new nodes and edges (`handlers.rs`, `nodes.rs`, `frames.rs`), the
  re-run of the clause in the analysis (`run_rows` for a clause body, now pending, and a
  seed of the facts of the clause after the row: the facts of a clause have one seed at
  its entry today, `Handlers::info`), A4 with the names of the copied cells, and the
  proofs E1 to E7. Size L + M (A4). No spec relation changes.
- The cheap step (stage R0k-c2a) is not possible: D5 and C8 are already under the rule of
  R0g (`Scope::pending`), and their weak form has no re-entry, so the `ir` pipeline
  accepts `m7` and the old pipeline checks it. A weak form that rejects `m7` needs the
  re-entry edges into the clause after the row (the new seed of the facts of the clause,
  the main part of this design), and it cannot drop the owned/shared split: a re-entry
  with the state at the end of the function for all places gives the false W0301 of
  `m3`, an error that the full facts do not give. So `m7` stays open (ledger) until this
  stage.
- Acceptance: the 7 files of tier 1 and the 5 of tier 2 in scope with no change of their
  records; the probes of `tests/gate/probes/fixes/r0kc2/`: `m1_outside_ref_cleared` (W0301)
  and `m1_ok`, `m3_run_local_after_handle` (clean), `m5_once_used_before_row` (clean),
  `m6_abort_in_copy` (clean), `m7_rc_shared` (W0301) and `m7b_rc_shared_ok`, `m8_c8_local`
  (W0301), and `m2`, `m4` (W0503 across the row) of the review.

R0k-c2 as built (D5 and C8: the re-entry of a clause frame; `docs/ir.md` 6.5, "As built
(plan stage R0k-c2)"; the notes of the build: scratchpad `r0k/c2/notes2.md`):

- The rows of a clause (`frames::clause_rows`): the nodes of the clause, and of the bodies
  that splice into it, of `frames::row_multi`, before the first `resume` (`pre`) or after
  it (`post`). A node that runs a clause with a `pre` row is a node of `row_multi` too
  (`frames::runs_row_clause`): it waits at the operation while the clause waits. So it
  gets the re-entry of a node of a function body (OL-R2a): a `Copy` node with an edge from
  each `Return` of the function, and the analysis runs the rest of the handled body again
  from the block after it. Its `Copy` node also has an edge to the `FrameEnd` node of each
  abort destination of the node (`NodeTable::copy_abort_edges`): the rest of the clause
  can end with no `resume` (an abort to its handler) or abort. A `handle` whose clause has
  a `post` row gets a `Copy` node (copy `nodes::ROW`) with an edge from each `Return` and
  an edge to its `Post` node (`NodeTable::post_row_edges`); its template is the `Copy`
  rule with the state of the rows.
- The re-entry edges into the clause (E6, E5). Each row of the clause gets a `Copy` node
  with an edge from each `Return` of the function (or closure) below which the clause runs
  (`handlers::clause_chain`; `emit_clause`). The `Copy` rule (`handlers::copy_node`, the
  argument `chain`) copies the frames of the function and of the chain of clauses: a
  variable whose value points only into them (a local, its `Vec` and `Box` buffers; the
  continuation local of the clause, in its state at the row) is bound again, and empty if
  it is not linear; a variable that points into a shared place (an `rc` group, a place of
  a caller or of a frame above the handler) keeps its state after the previous run. The
  `Copy` nodes of a clause are not code of the clause at the node that runs it
  (`handlers::clause_nodes`): the node has its own `Copy` node.
- The analysis. The run of a function body gives each row of a clause below it the heap
  slots of its `Return`s (`clause::Handlers::row_heap`); the normal edge of the row joins
  them in each run of the clause (`analysis::edges`). The run of the facts of a clause
  runs the clause again from the block after each of its rows with the state of the row
  and these slots (the second seed, `analysis::run_rows`).
- C8 (`clause::handle_run`, `handlers::local_chain`). A node of a clause inside the
  handled body of a local `multi` handler that runs a clause of the handler that can
  resume more than once is a re-entry of the handler (`Frames::reentries`): an edge from
  `Post` of the `handle` to its `Copy` node, then to its `Ret`
  (`NodeTable::clause_reentry_edges`); its normal edge joins the values of the locals
  outside the handled body at the later `resume` and the heap
  (`clause::Handlers::row_join`); the copied frames are the frames of the handled body and
  of the clauses on the way.
- E7. A value that is not `many` and that is live across the row: in the clause frame,
  W0503 at the row (the continuation of `m4`, the linear value of
  `fixes/r0kc2b/b06_once_across_bad`); in the frame of the function, W0503 at the node that
  runs the clause (`multi_at`, as before); the `Copy` node gives a linear value no
  `empty_at`.
- What stays (the reason D5, with the text of R0g): a row of a clause that only the
  analysis finds (`clause::Handlers::dyn_rows`, a run of a function value that can resume
  more than once): the nodes that run the clause get no re-entry for it, so the program
  keeps the pending rule (`analysis::static_row`). `c15/clause_after_m` (a post part that
  runs a value that performs a `multi` operation) and `r2/oracle/runs/m1/p1669` (a clause
  that runs its parameter) keep the fallback.
- The fact oracle (A4 of re-entries; `FactOracle::note_reentries`, `reentry_copy`,
  `reentry_events`; `copy_frames` gives a fault). At a `multi` operation each followed
  frame of the continuation keeps the references of its locals and the `Copy` nodes of the
  frames of its component (the frame of a function waits at its `handle`, so its locals go
  on at the `Copy` nodes of its handled body and its clauses). At each copy of the frames
  (each `resume`): a reference into a cell of the `map` of `copy_frames` whose variable
  points only into places of the copied frames must have `rebound_at` at one of the
  `Copy` nodes (an owned place, valid in the copy); at a later copy, a reference into a
  shared cell that a write strictly above it, a move or a free reached since the operation
  must not. The two mutation tests (`weft-interp` `fact_oracle.rs`): facts with no
  `rebound_at` at the `Copy` nodes (the state at the end of the function for owned places)
  fail A4 on `m3`; facts with a `rebound_at` of each variable at the `Copy` nodes (the row
  state for shared places) fail A4 on `m7`, before the read of the freed cell.
- Open (older than the stage; the re-entry of a function body has them too; scratchpad
  `r0k/c2/y`): a reference through an `Rc` handle of a copied frame is invalid at the
  re-entry after the end of the handle in the previous run (a false W0301:
  `root_rc_ok.wf` with `weft-r0kd2`, `rc_clause_ok.wf`); and the variable "the copy of the
  frame" of a call (D-MULTI-MID) points only into the places below the references that the
  call uses, not into the `rc` groups that they reach: a change of such a group by the
  outer clause between two `resume`s does not reach the copied callee frame
  (`root_rc_between.wf`: HOLE with `weft-r0kd2`; `root_rc_fo.wf`: an A4 failure on a clean
  program). The probes of the stage keep out of both forms; the four bad probes
  `b07`-`b10` (rejected) fail the old A4 of copies in `main` for the second reason.
- Probes `tests/gate/probes/fixes/r0kc2b/` (a bad case and a clean twin of each):
  `b01_vec_owned` (a `Vec` of the clause: clean; in an `rc` object: W0301),
  `b02_clause_local_ref`, `b03_rc_between` (an `rc` object of `main` shared by the
  copies), `b04_frame_above` (a vector of `main` above the handler), `b05_c8_pre` (C8),
  `b06_once_across` (E7), `b07_abort_in_copy` (the second copy fails to a `Fail` handler of
  `run`), `b08_handled_after` (the rest of the handled body runs again), `b09_post_row`
  and `b10_post_row_after` (a row after the `resume`). Tests: `analysis_units` `r0kc2`
  (the re-entry edges of the seed, E5, E7, C8); `fact_oracle.rs` (the two mutations, and
  each probe that the `ir` pipeline accepts passes the fact oracle with A4 of re-entries).
- The fallbacks, against `weft-r0kd2` (census by the note of `weft check`; scratchpad
  `r0k/d2/kd2-t1.tsv`, `kd2-t2.tsv`, `r0k/c2/w4-t1.tsv`, `w4-t2.tsv`): tier 1 (5232
  files, the 20 new probes) 96 to 83: D5 12 to 0, C8 1 to 0. The 13 rows come into scope
  with no error but `m7_rc_shared` (W0301 at line 11; the old pipeline misses the fault,
  so the open-old entry `R0k2C-M7` goes): `multi_nested_drop` (two copies),
  `multi_nested_drop2`, `multi_nested_ok`, `fd2_v1_three_levels`, `d5_after_resume_ok`,
  `c8_nested_after_ok`, `m1_ok`, `m3`, `m5`, `m6`, `m7b`. No row leaves the scope.
  `verify/s5/R2c/p/o5` (C8, rejected) gets the W0302 of the old pipeline. Tier 2 (57393)
  112 to 108: D5 5 to 1. `multi_nested_drop`, `_drop2`, `_ok` and `fd2_v1` come into
  scope with no error; `r2/oracle/runs/m1/p1669` keeps the fallback (a row that only the
  analysis finds: the clause runs its parameter `f`); `o5` as in tier 1. No row of tier 1
  or tier 2 leaves the scope, and no other row changes its codes.
- Gates (binaries `r0k/c2/bin/weft-r0kc2`, `weft-gate-r0kc2`): tier 1 0 blockers (5232;
  3930 same, 17 open, 314 fixed, 1 new-fp, 154 lost-clean, 148 moved, 668 changed; the
  new probes have their old records in `tests/gate/baseline-tier1.jsonl`); tier 2 (2
  workers) 0 blockers (39917 same, 6 open, 92 fixed, 12 new-fp, 0 lost-fault, 3480
  lost-clean, 1860 moved, 12026 changed: the copies of `i5_nested_multi` and `e2_spared`
  are `moved`); fact
  oracle tier 1 0 failures (8 faults, 22 timeouts, 1418 pass); sigdiff tier 1 0 rows with
  no entry. Ledger: `R0k2C-M7` removed; `changed` `b04_frame_above_bad` (W0301 for the
  W0312 of the old pipeline); `moved` `i5_nested_multi`, `e2_spared` (W0602 at the
  `resume` of the clause). The interpreter sources change (A4), so the oracle caches of
  tier 1 (both engines) and of tier 2 run again. `ereview/ev.sh` on the rows that change
  and the probes (40 rows of tier 1, 6 of tier 2): no HOLE, no FP-IR (22 no fault, 9
  held, 2 rejected by both, 7 oldmiss: `m7` and the bad probes `b01`, `b03`, `b07` to
  `b10`, which the `ir` pipeline rejects and the old pipeline misses).

R0k-d1 as built (A through the pending rule, D4; the depth bound stays; `docs/ir.md`, "As
built (plan stage R0k-d1)"; the census and the design check: scratchpad
`r0k/d/notes.md`):

- A (`handlers::Region::of`, `REST_NOT_FOUND`): a run of a clause that maps to no node of
  the handled body is pending with a weak form: the resume has no region, so the facts of
  the resume get no change and no free of the rest of the handled body, and can only miss
  an error. The `ir` pipeline checks the program first. Every A program of the tiers is
  rejected by the old pipeline (an A form is a run outside the handler: W0313, W0314,
  W0503); none is clean, so the check of "no new error on a clean A program" has no
  program to fail. Each A program that comes into scope is rejected by the `ir` pipeline.
  The codes differ in the families of `62_cap_escape` (W0314 in place of W0313 for a value
  given to a parameter or to an operation of a caller: the rule of code of a caller) and
  `67_task_starts` (a W0405 at line 46 that the old pipeline does not give: a program with
  `calls_result` alone faults at that line, and `weft-r0kc1` gives the same W0405 for
  it; one W0314 fewer); the corpus markers have `old:` words for them.
- D4 (`clause::must_written`, `State::join_values_but_keys`): after the `resume` of a
  `once` continuation, a local of the site that the rest of the handled body gives a whole
  value on each path after each node that runs a clause of the handler has only its value
  at the end of the handled body (a strong update). A `multi` continuation, a write on some
  paths only, or a body inside the handled body (not a closure body) that runs a clause of
  the handler keeps the weak update. `fixes/r0g/d4_reassigned_ok` and `partb/p/e1_fp`
  come into scope with no error (the two W0502 of the old pipeline in `e1_fp` are on a
  closure that captures nothing: a false positive, UNSIGNED lost-clean). The D4 row
  `r2/oracle/runs/g2/p2515` (closures that capture the capability in a block of a closure
  body that no node runs) stays.
- The depth bound (a chain of function values deeper than 64) is not built. The memo of
  the walk (`Apps::modes`) bounds the depth by the number of values of the program, but
  the cost of a level is not constant: with the bound taken out, `closure_chain_100`
  takes 5.1 s and `closure_chain_200` 160 s to check (the fallback: 0.04 s and 0.2 s), so
  `closure_chain_400` and `_800` would pass the time limit of the gate. A walk with no
  bound needs a summary of a chain that does not apply each level again; it is a design of
  its own. The four `closure_chain` files of tier 2 keep the fallback.
- Probes `tests/gate/probes/fixes/r0kd1/`: `a01_escape_bad` (A: the escaped closure gives
  its inner closure to `apply`, which runs it after the `handle`: W0313, held) and
  `a01_escape_ok`; `d01_strong_ok` (in scope, no error) and `d01_strong_bad` (the write on
  one path only: W0313, held); `d02_multi_weak` (a `multi` continuation: the fallback
  stays) and `d02_multi_ok`. Tests: `analysis_units` `r0kd1` (A is pending, the strong
  update, a `multi` continuation keeps the weak update).
- The fallbacks, against `weft-r0kc1` (scratchpad `r0k/d/kc1-t1b.tsv`, `kd1-t1.tsv`),
  tier 1 (5204 files): all 105 to 98, A 5 to 1 (the one left is `83_kept_values`, whose
  copy of R0k-a brings the form in: the first reason, C2, stays), D4 4 to 1
  (`d02_multi_weak`). The 8 rows that change: `62_cap_escape`, `67_task_starts`,
  `partb/p/f1_multi` (A; rejected by both pipelines), `fixes/r0g/d4_reassigned_ok`,
  `partb/p/e1_fp` (D4; accepted), and the probes `a01_escape_bad`, `d01_strong_ok`;
  `83_kept_values` changes its reason (A to C2 with the copies).
  Tier 2 (57393; `kc1-t2.tsv`, `kd1-t2.tsv`): all 212 to 149. 63 rows come into scope
  (62 A rows, each rejected by both pipelines: 16 mutants of `62_cap_escape` and 13 of
  `67_task_starts` in `S5c/mut`, 30 `sweep3` programs (`apply__*`, `nested__*`), two `g7`
  runs, `f1_multi`; and `e1_fp`, accepted); 24 rows keep
  a fallback with their next reason (C2; most are mutants of `83_kept_values`, whose copy
  of R0k-a brings the A form in); no row leaves the scope.
- Gates (binaries `r0k/d/bin/weft-r0kd1`, `weft-gate-r0kd1`): tier 1 0 blockers (5204;
  3911 same, 18 open, 307 fixed, 1 new-fp, 154 lost-clean, 146 moved, 667 changed); tier 2
  (2 workers) 0 blockers (39952 same, 6 open, 92 fixed, 12 new-fp, 0 lost-fault, 3447
  lost-clean, 1858 moved, 12026 changed); fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry (a `sig` entry for the parts `tasks`, `pins` and `reaches` of three functions of `67_task_starts`).
  Ledger: two `changed` entries for the tier-1 corpus files and the tier-2 A rows (the codes
  above), one UNSIGNED `lost-clean` entry for `e1_fp`. `ereview/ev.sh` against
  `weft-r0kc1` on the 90 A rows, the D4 rows and the 6 probes: no HOLE, no FP-IR (the A rows
  that come into scope are held or rejected by both pipelines; `d4_reassigned_ok` and
  `e1_fp` run clean).

R0k-d2 as built (E4, `TASK_LATE`: the window of a task; `docs/ir.md` 6.4; the census and
the design: scratchpad `r0k/d2/notes.md`):

- The census (45 rows: tier 1 4, all clean; tier 2 41). The rule of R0j
  (`templates::runs_rebound_cell`) made a task late if the variable of a `Kept` or `ByRef`
  capture that the task runs had more than one whole `Assign` anywhere, or if the capture
  came through the environment of the maker (`env.k`). Two shapes: the other writes are
  before the spawn (two arms of a `match`) or after the `join` (tier 1); the task closure
  is made in a closure, so the capture is `env.k` (tier 2, 41).
- The rule now (`templates::late_write`): the cell is the variable that the capture
  names, whole, through upvar locals and the `Kept` and `ByRef` captures of the makers
  (`instantiate::whole_cell_of`); a capture of a part of a variable or of a place behind
  a reference is late, as before. For a spawn on the scope of its own body (a scope body,
  through its `ScopeCap`) or a `fork`, a whole write (an `Assign` or a terminator
  destination) counts only in the window: in the body of the terminator on a path from it
  (for a spawn up to a `join` of its handle; a `fork` waits for its branches, so none),
  in a body inside it, or in a body that the window can call; the bodies above it wait, so
  their writes do not count. For any other spawn (on a scope of another body: the task can
  outlive the body) the rule of R0j stays: more than one whole write. Soundness: with no
  write in the window the value of the cell for the whole task is its value at the spawn,
  which the state of the spawn node has, so the run at the spawn node is exact. A late
  task stays pending (the rule of R0g).
- A first form of the rule counted each write of the cell, also a write of a part of it
  (`w3.score += 1`) and the one write that gives the variable its value; the tier-2
  census showed 9 programs in scope that it put out of scope (`r3/oracle/runs/g3a/p1675`
  and 8 more: a spawn in a clause on the scope of the outer body). The rule above (whole
  writes; more than one with no window) keeps each of them in scope.
- What stays: a write in the window (each such program of the probes is also a W0405
  race, which both pipelines reject); a spawn in a closure on an outer scope with two
  writes (`s4_spawn_in_closure_ok`; the `p13880` shape); a write of a part of the
  variable is not a write of the cell (a function value has no parts).
- Probes `tests/gate/probes/fixes/r0kd2/` (a bad case and a clean twin of each shape):
  `s1_before_spawn` (two paths before the spawn; bad: the value of `f` changes `v` while
  the scope body reads it: W0405), `s2_after_join_ok` and `s2_in_window_bad` (a write after
  the `join`, a write in the window: W0405), `s3_nested_closure_ok` (the capture through
  the environment of `g`; the next reason, `VALUE_TASKS`, keeps the fallback) and
  `s3_nested_closure_late` (W0405), `s4_spawn_in_closure_ok` (conservative: the fallback
  stays) and `s4_spawn_in_closure_bad` (W0405). Tests: `analysis_units` `r0kd2`.
- The fallbacks, against `weft-r0kd1` (scratchpad `r0k/d2/kd1-t1b.tsv`, `kd2-t1.tsv`,
  `kd2-t2.tsv`): tier 1 (5212 files) 102 to 96, E4 8 to 1 (`s4_spawn_in_closure_ok`); the
  rows that change: `fixes/r0i/rb/n01_option_spawn`, `n11_enum_nongeneric_spawn`,
  `q02_pop_spawn`, `fixes/r0j/j02_late_ok` and the probes `s1_before_spawn_ok`,
  `s2_after_join_ok` come into scope with no error; `s3_nested_closure_ok` changes its
  reason (E4 to `VALUE_TASKS`). Tier 2 (57393): 149 to 112, E4 41 to 0; 37 rows come into
  scope (4 clean seeds, accepted; 33 that the old pipeline rejects and the `ir` pipeline
  accepts, with no fault: lost-clean, UNSIGNED), 4 change their reason to C (`VALUE_TASKS`,
  R0e fix 2); no row leaves the scope. The 33 lost-clean rows: the old W0405 is at an
  access after a `join` that it does not see (a handle in a tuple: `let (t, _) = pt`; a
  `join` in a callee: `join_it(t)`) or at another field than the one that the task changes;
  in `g3b/p13297` the old W0301 is on a closure call after its captured variable was moved
  and got a new value; in `g3b/p13259` the old W0601 is on a closure that `apply` calls once.
- Gates (binaries `r0k/d2/bin/weft-r0kd2`, `weft-gate-r0kd2`): tier 1 0 blockers (5212;
  3919 same, 18 open, 307 fixed, 1 new-fp, 154 lost-clean, 146 moved, 667 changed); tier 2
  (2 workers) 0 blockers (39919 same, 6 open, 92 fixed, 12 new-fp, 0 lost-fault, 3480
  lost-clean, 1858 moved, 12026 changed); fact oracle tier 1 0 failures (1396 pass, 8 faults, 22 timeouts); sigdiff tier 1 0 rows
  with no entry (a `sig` entry for `n11_enum_nongeneric_spawn` and `s4_spawn_in_closure_bad`:
  the parts `reaches` and `pins`). `ereview/ev.sh` against `weft-r0kd1` on the 12 rows of
  tier 1 (the 4 programs and the 8 probes) and on the 37 rows of tier 2 that come into
  scope: no HOLE, no FP-IR.

R0k-d3 design check (the task fallbacks that R0k-d2 left; not built; scratchpad
`r0k/d3/notes.md`). Each reason is pending since R0j, so the rows left are programs that
the facts with a weak form accept (census with `weft-r0kd2`):

| reason | tier 1 | tier 2 | the rows |
|---|---|---|---|
| E2 `TASK_AGAIN` | 5 | 4 | `fixes/r0j/j01_again_ok`, `fixes/r0f/c09_cc_during_ok`, `r3/oracle/probes/s8_steal_fnparam` (clean); `i9_kept_write` (old W0405), `s9_steal_stored` (old W0302); tier 2: the copies of s8, s9, i9 and `r2/oracle/runs/m2/p7046` (clean) |
| R0e fix 2 (`NESTED_TASK_RUN`) | 5 | 4 | `fixes/r0j/j03_nested_ok`, `fixes/r0e/a13_ok`, `Core_S2/probes/crash/c10` (clean); `fixes/r0e/rv1_b2_h10`, `h18` (old W0502); tier 2: `c10`, `r3/oracle/runs/t3/p148` (W0312), `g4p/p25005` (W0405), `seeds3/gen3_18180` |
| `VALUE_TASKS` | 2 | 2 | `fixes/r0j/j04_value_ok`, `fixes/r0kd2/s3_nested_closure_ok` (clean); tier 2: `g3b/p18574` (W0312), `seeds3/gen3_15687` |
| `TASK_CODE` | 2 | 0 | `fixes/r0h/d3f_task`, `fixes/r0j/j05_code_old` (W0314 from both pipelines) |

- E2, a task that runs a value more than once (code of a caller `g(f)` with `g` a
  parameter, or a loop in the task body): the run at the spawn node is one run; a second
  run needs a second node of the run in the task region, after the first (a cycle for a
  loop), so that the effects of the first run reach the second (a `once` value: W0502; a
  reference that the first run ends). That is a new phase of the `Spawn` node, the split of
  the applications of `templates::task_start` between the two nodes, the task facts of the
  second node, and a new cover of the fact oracle for a task that runs a value again. Size
  M-L. Gain: tier 1 3 clean programs, tier 2 1.
- R0e fix 2 and `VALUE_TASKS` are one design (size L): a value of a callee, or a closure,
  runs a value of its arguments or of its captures as a task (`j03`: the argument of `run2`
  spawns its parameter; `j04`: `f` spawns `g` two times). The task starts and ends inside
  the run of the outer value, with the code of that value that runs at the same time, and
  through two levels of runs for R0e fix 2. The summary parts `joins`, `abort_joins` and
  `task_effects` are for one level of tasks of the body itself; the design needs a summary
  part for the tasks of the values of the interface (the window and the footprint of the
  code that runs with them) and its application at the run node, with its proofs and the
  summary oracle.
- `TASK_CODE`, a task that runs code of a caller (the value of an operation): the worst
  way of a foreign task, which is the design of F18 (`TASK_RUN`); it goes with F18. Both
  rows are rejected by both pipelines.
- No weak form helps (the reasons are pending already). The one exact subset that is
  cheap is E2 for `c09` (the code of the caller runs `f` once; a copy of `mid` at the call
  shows it): one program, no stage. The whole gain of R0k-d3 is about 8 clean programs of
  tier 1 (probes) and 4 of tier 2.

##### HENV-SHADOW fix

The hole (in scope since stage C1; the R0k-b1' review, scratchpad `b1prev/notes.md`): a
closure runs with the handler environment of its maker (`c.henv` in `call_value`). A
callee `mk` makes a closure that performs an effect E through its row. `mk` is called in
the handled body of a local handler H of E, and the closure runs in the handled body of
an inner local handler H2 of E. At run time the perform goes to H. The facts resolved E
only to the innermost local handler, H2, and past the function (`frames::reach`,
`value_effects`), so the clause of H was not in the facts of the run node. Probes
`q02`, `q06`, `q08` (the interpreter reads a freed cell; the `ir` pipeline gave no error;
the old pipeline gives W0301).

The choice: option (a), the exact form, not (b), the pending form. Each change is in
`frames::reach` and `clause::note_cap_apps` (about 200 lines, most of them comments), and the census
showed no change of a program of tiers 1 and 2 before the new probes. Option (b) would put
the same programs out of scope and need a new pending reason, with no gain in precision.

As built (`docs/ir.md` 6.5, "As built (HENV-SHADOW fix)"):

- `frames::henv_unknown`: a call can run a function value whose handler environment
  the facts do not know. Known: a constant (a function item), a local that
  `closure_only` accepts (closures of the function capture each local handler that they
  perform through), and a parameter of a function or a closure that gets no other value
  (`entry_param`: the value existed before the frame). Not known: the result of a call, a
  field, an element of a container, the result of an operation. A call of a function
  value checks the callee and each argument; a call of a function item checks each
  argument if the summary runs a value (`runs`, `unknown_runs`).
- The review of the fix (scratchpad `henvrev/notes.md`; no soundness hole) found 3 new
  false positives in scope (`fixes/henv/fp01_made_in_inner`, `fp02_vec_in_inner`,
  `fp03_fail_inner`): `mk` is called in the inner handler H2, and its closure runs there,
  so it performs to H2 only, but each call result was not known. Now a value that was
  made in this run of the handled body of the innermost local handler of the effect at
  the run node is known (`frames::made_under`, `docs/ir.md` 6.9): its local belongs to a
  body that runs in each run of that handled body, and each whole write is a new
  closure, a constant, a copy of such a local (also a field or an element of it), or the
  result of a call of a function item whose environment sends the effect to that handler
  first and whose `ret.fns` are only closures of the callee and function items; no
  write of a part, no reference to the local. The bad forms of the review stay rejected
  (tuple, `Option`, `Box`, `Rc`, a resume value, a maker of a maker, a new instance in a
  loop), and two more scratch probes (a callee that gives back an outer closure; an
  outer closure put into a `Vec` of H2). `entry_param` and `made_under` look only at the
  body of the local and at the bodies with upvar locals (`writers`). The review also
  said that a known `entry_param` value keeps the innermost local handler where past
  the function is the destination of a closure of a caller: the innermost one is
  necessary for a function item, and more than necessary (not wrong) for a closure; a
  note in `docs/ir.md` 6.9 says so.
- Round 2 of the review (scratchpad `henvrev2/`; 37 probes) found two gaps of
  `made_under` that opened holes again: a declaration (`Vec.pop`, `Box.new`,
  `Rc.clone`, `Weak.upgrade`: a result of type `T`, so `ret.fns` is empty) counted as a
  maker (`p13` to `p16`); a closure that shares the cell of the local (a `Kept` capture)
  wrote another value into it (`p07`, `p07d`). Now a maker needs an IR body and a
  non-empty `ret.fns`, and a closure that shares the cell and can write it
  (`shares_cell`, `writes_capture`) makes the local unknown. Round 3 found one more form,
  a hole since stage C1 (`weft-r0kd2` misses it too): a closure of the function made in
  H2 captures a closure that `mk` made in H and runs it (`p30`). A `closure_only` local
  is now known only if its closures capture no other function value
  (`plain_closures`), also in `value_effects`. An aggregate whose function parts are
  `made_under` is known (`c30` `Option`, `c31` struct: the false positives of round 2
  are gone). Left as false positives (issue #79; no row of the tiers has them): `c29`
  (a `RetFn::Param` result), `c32` (the receiver `&vs` of `push`), `p07c` (a closure
  writes the cell with a value made in H2; the rule above is conservative).
- `frames::resolve_all`: each local handler on the chain of the environment that adds
  the effect, up to a captured capability, and past the function. `frames::run_dests`
  uses it for a row effect and for `Fail` if the chain has more than one such handler and
  the call is `henv_unknown`; else it is `resolve`. The check runs only then, so the cost
  does not change (a first form that ran it at each call made
  `verify/s5/S5c_diff/scale/c8000.wf` 2.8 times slower).
- `clause::note_cap_apps` gives a failure of such a value to each local `Fail` handler of
  the chain.
- The fact oracle gap: A5 passed on `q02`, because it failed only on a node with
  `escapes_at` of the effect, and the node of the run sent the effect to H2. A5 now also
  fails if no node of the frames of the component above the `handle` has `performs_at`
  with the capability of the handler, for a clause with a resume point (a clause with
  none aborts, and trace conformance checks the abort edge; a first form with no such
  limit failed on 31 correct programs of tier 1, each a `Fail` clause at the end of a
  scope). With the facts before the fix, A5 fails on each probe of `fixes/henv` (bad and
  clean); with the facts of the fix, it passes.
- Probes `tests/gate/probes/fixes/henv/` (a bad case and a clean twin of each): `q02`,
  `q06`, `q08` of the review; `h01_vec` (an element of a `Vec`), `h02_clause_value` (a
  clause gives the closure), `h03_field` (a field), `h04_callee_runs` (a callee runs the
  closure). `h01_bad` and `h03_bad` are old misses (the old pipeline accepts them):
  class `fixed`. The clean probes of the review: `fp01_made_in_inner`,
  `fp02_vec_in_inner`, `fp03_fail_inner`, `c30_option_ok`, `c31_struct_ok`. The probes
  of round 2 and 3, each bad and clean: `p13_pop`, `p14_box_new`, `p07_closure_writes`,
  `p07d_closure_write_callee`, `p30_closure_captures_outer`. Tests: `ir_handlers.rs`
  `a_closure_that_a_call_made_performs_to_each_local_handler_of_the_chain` (it fails
  before the fix: no error on each bad probe),
  `a_closure_made_in_the_run_of_the_inner_handler_performs_to_it` (it fails with the
  first form of the fix: W0301 on `fp01`), `summary_oracle.rs`
  `a_clause_that_no_node_runs_fails_the_clause_cover`.
- The census of the fallbacks (the line "note: --facts=ir: the old pipeline checks the
  program:"), against `weft-r0kd2` (scratchpad `r0k/d2/kd2-t1.tsv`, `kd2-t2.tsv`;
  `henv/census/`): tier 1 (5212 files) 96 to 96, tier 2 (57393) 112 to 112, each reason
  the same; no row moves in or out of scope, and before round 3 no diagnostic of a row
  changes (round 3: two tier-2 rows, below). Three
  tier-2 rows time out at 60 s in the census under load (`r3/quality/big/all_2.wf`,
  `scale/c8000.wf`, `scale/h8000.wf`); alone, with no limit, they give the record of
  `weft-r0kd2`, in the same time.
- The diagnostics against `weft-r0kd2` on the lists `s00`, `s01`, `s02`, `s04`, `s06`,
  `s07`, `s08`, `s10` of scratchpad `c14v` (7034 files): 3 files change
  (`c1sign/v2/p7192_multi2_MK.wf`, `p7192_multi2_PS.wf`, `r67/v/rows/p7192_h5.wf`). Each
  gets one more W0301; each is rejected by both pipelines already and faults (`ev.sh`:
  held). On the 29 probes of `fixes/henv`, the 24 probes of the review (scratchpad
  `henvrev/p`), the 37 probes of round 2 (`henvrev2`) and the 3 files: no HOLE; FP-IR
  only on `c29`, `c32` and `p07c` (above). After round 3 the census of tier 2 has two
  more changed rows, each rejected by both pipelines and faulting, and each still class
  `changed` (ledger entry 287): `r2/oracle/runs/g3/p5307.wf` (one more W0302, at line
  88) and `r2/oracle/runs/g5/p21857.wf` (a W0302 at line 101: `g12` captures `f8`, so
  the run of `g12` runs the clauses of the local handlers).
- Ledger: no entry. No row of tier 1 or tier 2 changes its class; the 29 probes are
  new rows of tier 1 (27 `same`; `h01_vec_bad`, `h03_field_bad`: `fixed`).
- The oracle caches: the interpreter sources changed (the fact oracle), so the caches of
  tier 1 (both engines) and of tier 2 (`ir`) were made again. Each verdict is the same,
  but for runs at the time limit or with a port in use: tier 1 `fixes/r0f/c01_serve_read_ok`
  (timeout to benign) and `verify/partb/S4diff/p/wide3.wf` (timeout to not-runnable: it
  has no `main`), on both engines; tier 2 7 rows between timeout, benign and clean. No
  verdict changes to or from `fault`.
- Gates (binaries scratchpad `henv/bin/weft-henv3`, `weft-gate-henv3`, after round 3):
  tier 1 0 blockers (5241; 3946 same, 18 open, 309 fixed, 1 new-fp, 154 lost-clean, 146
  moved, 667 changed); tier 2 (2 workers) 0 blockers (39919 same, 6 open, 92 fixed, 12
  new-fp, 3480 lost-clean, 1858 moved, 12026 changed: each count as at R0k-d2); fact
  oracle tier 1 0 failures (1414 pass, 8 faults, 21 timeouts); sigdiff tier 1 0 rows with
  no entry. The changes of the review rounds do not change the interpreter sources, so
  the oracle caches only get the rows of the new probes.

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
  W0706: the `ir` pipeline uses `crate::infer::{growth_limit, not_converged,
  SIG_PLACE_STEPS}` in `analysis/callgraph.rs` and `analysis/sig.rs`, so move them
  out of `infer.rs` before it goes; review of R0i), the checks that `analyze` runs on
  the old signatures (`program::check_on_abort_rows`, `fip::check` with the old
  signatures, `OLD_INFERENCE_CODES`), `FactGen::Old` and `Both`, `Options::ir_groups` and `irbuild/scope.rs` (all
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
| F16.3 | F16 | fallback / group D: `GIVES_BACK`, a call that runs a clause of an operation with a function value, a type parameter or a reference result and a clause that resumes (18 tier-1 programs; σ(Caller) at the call is the resumed values, and only code of a caller lends places of `Caller`), and a `multi` operation of a handler of a caller in a clause (14). Type parameters: done at stage F20 (an effect has no type parameter, so the test goes) | references: done at R0h (σ(`Caller`) names the places that the clauses give back, part `caller_muts`); function values: done at R0h for a value that cannot race, holds no reference in a capture and is not `once` |
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
| R0e | R0d | tasks in closure bodies and spawns that do not name their scope (Phase R, R0e; E1, E3): a scope body in a closure splices into it, the closure summary has the tasks that start and end in a run of the closure (`runs`, pins, raises), `spawns_in`, the order of the tasks of the source, a value that a value of a callee runs as a task is run in the worst way (it closes a hole of R0d, `fixes/r0e/a13c_callee_bg_param.wf`), the scope capability points into its own root in a program with a spawn that does not name its scope (the scope from the analysis, W0601 for a lost linear result). Fallbacks 279/4981 to 232/1080. Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `ev.sh` 0 new HOLE on the programs that come into scope and on the review sets of R0d. The lost-clean rows wait for the review | done (R0e) |
| R0e fix | R0e | OR7: a task of a callee runs while the callee runs a function value that captures a local of the caller (`r0e/t/or7a.wf`, a hole since C3 that the old pipeline catches). `Run::during` (the places of the tasks that run while the body runs the value), `templates::during_check` (W0312 at the call; the places go to the `WaitTask` of a local handler of an effect of the value, W0405). 20 forms close (3 that both pipelines missed). Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry. The 4 new lost-clean rows wait for the review | done (R0e fix) |
| R0e fix 2 | R0e fix | the review of R0e, round 1: B1 (a scope body in a clause: its code and its spawns reach the node that runs the clause; also a hole since C3, `rv1_cs2_*`), O1 (the spawns of a clause in a closure are in the part `tasks`), O2 (the task nodes move a `once` argument that runs as a task two times), B2 (fallback E7: a value that a value of a callee runs as a task). Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12, lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry. Open: the plain form of B2 (`run2(\|x\| x(), \|\| take(v))`, since C3) | done (R0e fix 2) |
| R0e fix 3 | R0e fix 2 | H19, the plain form of B2: a callee gives a `once` closure to a function value of its interface two times (a hole since C3 that the old pipeline catches). `Run::via_only`, `Run::via`, `transfer::via_twice`: a caller that knows the value counts the runs of the argument in its summary (W0502 at two runs or more), else the worst way. 10 forms close. Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, each row as R0e fix 2; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry. The 5 new lost-clean rows wait for the review | done (R0e fix 3) |
| R0e fix 4 | R0e fix 3 | the review of R0e, round 2: R2-B1 (the lift filter of fix 2 dropped a clause task that is joined on one path only: now only a task of a scope of the clause, a `fork` there, or a task that the clause joins on each path is skipped), and the older holes a15, a35 (a run of the value in a clause, `clause_run_at`) and a31 (a value that runs in a task next to another task of the callee, `task_hows`). Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry. The 6 new lost-clean rows wait for the review | done (R0e fix 4) |
| R0f | R0e fix 4 | task runs (Phase R, R0f; C1, C7, E7): a value of a caller that a foreign function, `http.serve`, code of a caller or a function value runs as a task applies at the task nodes of the call (the worst way, or the way of the code of a caller that the node knows: `via_plain`, `via_code_twice`); a call of a function value has task nodes for its arguments; a closure that spawns a value of its interface on a scope of its maker gives the value to that task (`TaskHow::tasks`; closes `c29d`, `c29f`, older holes). Fallbacks C1 40/126 to 0/0, C7 12/79 to 7/11, E7 3/19 to 2/5. Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `ev.sh` 0 new HOLE. The 6 new lost-clean rows wait for the review | done (R0f) |
| R0f fix | R0f | the review of R0f, round 1: B1 (a reader that code of a caller runs as a task while the code changes a place it gets: the values become tasks of the call with the places of the code; E7 stays for an `Unknown` value whose task runs with changes or other values) and B2 (a slot of a value that runs as plain code kept no plain places for `with`; a value in a task of the call gives its places to a maker task). Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `ev.sh` 0 new HOLE on the 127 review probes. The reviewer signed the lost-clean rows of R0f; 1 new row waits for round 2 | done (R0f fix) |
| R0g | R0f fix | continuations and capabilities in closures (Phase R, R0g; D1, D4, C4, C6, D5, C8): σ of a closure that a clause gives takes the environment from the value; a captured capability of a made closure maps to its live handler; W0313 through an abort past the handler; W0313 for a continuation; a `resume` in a closure, a row in a clause, a nested `multi` resume and a run outside a handler with no W0313 are in scope only if the `ir` pipeline rejects the program (`Scope::pending`). Fallbacks D1 60/309 to 15/49, D4 15/46 to 1/2, C4 7/22 to 0/0, C6 6/15 to 0/0, D5 15/116 to 5/5, C8 2/2 to 0/0. Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `ev.sh` 0 new HOLE. No new lost-clean row | done (R0g) |
| R0g fix | R0g | the review of R0g, round 1: B1 (a closure that a clause gives to the handled body runs on a task of a scope and its changes were lost; the same hole is older for a closure that a closure makes, `t_06`). A scope body runs in the frame of its site: `made_sigma` finds the variable of a capture through the makers in the bodies of that frame (`apply::frame_capture_source`), and `other_maker` walks up from a scope body. No fallback is added. Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, each count as R0g (new-fp 12, 0.096 %; lost-fault 0); fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `ev.sh` 0 HOLE but the old `c4_07`. 2 new lost-clean rows wait for the review | done (R0g fix) |
| R0h | R0g fix | function values and references across operations (Phase R, R0h; C2, D3): the clause of an operation of a caller is code of a caller that gets the arguments (`transfer::op_value_out`, task nodes of a perform); a function value of the callee in a clause is code of a caller; σ(`Caller`) of a call names the places that its local clauses give back (`Handlers::back`, part `caller_muts`, `back_ret`); a function value that a clause gives back runs at the call as code of a caller runs it. A value that the code can keep with a reference in it, and a given-back value that can race or is `once`, keep the reason; E2, E4, E5, C7, E7 stay. Closes the old misses `opres.wf` (issue #48) and `d1_callee_mut*` (tier 2). Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `ev.sh` 0 new HOLE. 2 new lost-clean rows wait for the review | done (R0h) |
| R0h fix | R0h | the review of R0h, round 1: seven HOLE rows of one root cause (a value of the interface of the site that a clause gives back, kept by the callee: the summary says that the place holds code of a caller). Only a closure or an item goes on in D3 form F; a value of the interface or an unknown value in an argument of an operation of a caller keeps the old pipeline (C2); `caller_muts` passes on through a body (`r01`); a callee with `caller_muts` whose arguments reach a root that a clause names keeps the old pipeline (`r39`). Gates: tier 1 0 blockers; tier 2 (2 workers) 0 blockers, new-fp 12 (0.096 %), lost-fault 0; fact oracle tier 1 0 failures; sigdiff tier 1 0 rows with no entry; `ev.sh` 0 new HOLE | done (R0h fix) |

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
| R0e (tier 1, the defaults) | 4378 of 4670 | 3680 | 265 (+3: `fixes/r0e/u04_linear_result.wf`, `a14_child_failure.wf`, `a14b_child_failure_callee.wf`, which the old pipeline misses) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 112 (+4, ledgered; `signed_by` UNSIGNED, the review signs) | 128 | 475 (+12, ledgered) | 9 |
| R0e (tier 2, the defaults) | 53648 of 57393 | 40462 | 88 | 12 (0.096 %, the rows of R0d) | 3441 (+588 in four classes of R0e, `signed_by` UNSIGNED) | 1824 | 11556 (ledgered) | 10 (as C3) |
| R0e fix (tier 1, the defaults) | 4421 of 4713 | 3709 | 269 (+4: `fixes/r0e/or7_rc`, `or7_handler`, `or7_handler_value`, `or7_handler_fail`, which the old pipeline misses) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 116 (+4, ledgered; `signed_by` UNSIGNED, the review signs) | 128 | 481 (+6, ledgered) | 9 |
| R0e fix (tier 2, the defaults) | 53648 of 57393 | 40461 | 88 | 12 (0.096 %, as R0e) | 3441 (as R0e) | 1824 | 11557 (+1, `p43726.wf`, ledgered) | 10 (as C3) |
| R0e fix 2 (tier 1, the defaults) | 4439 of 4740 | 3723 | 269 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 117 (+1, `rv1_o1_ok.wf`, UNSIGNED; the R0e rows signed) | 128 | 493 (+12, ledgered) | 9 |
| R0e fix 2 (tier 2, the defaults) | 53644 of 57393 | 40476 | 88 | 12 (0.096 %, as R0e) | 3441 (as R0e) | 1822 | 11544 | 10 (as C3) |
| R0e fix 3 (tier 1, the defaults) | 4460 of 4765 | 3740 | 269 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 122 (+5, the `h19_*` clean twins, UNSIGNED) | 128 | 496 (+3, ledgered) | 9 |
| R0e fix 3 (tier 2, the defaults) | 53644 of 57393 | 40476 | 88 | 12 (0.096 %, as R0e) | 3441 (as R0e) | 1822 | 11544 | 10 (as C3) |
| R0e fix 4 (tier 1, the defaults) | 4477 of 4782 | 3744 | 269 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 128 (+6, UNSIGNED; the rows of the R0e fix and of fix 2 signed) | 128 | 503 (+7, ledgered) | 9 |
| R0e fix 4 (tier 2, the defaults) | 53644 of 57393 | 40476 | 88 | 12 (0.096 %, as R0e) | 3441 (as R0e) | 1822 | 11544 | 10 (as C3) |
| R0f (tier 1, the defaults) | 4570 of 4826 | 3741 | 274 (+5: `fixes/r0f/c10_generic`, `c26c`, `c29`, `c29e`, `c29g`, which the old pipeline misses) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 134 (+6, UNSIGNED) | 128 | 539 (+36, ledgered) | 9 |
| R0f (tier 2, the defaults) | 53848 of 57393 | 40368 | 88 | 12 (0.096 %, as R0e) | 3443 (+2, UNSIGNED) | 1823 | 11649 (+105, ledgered) | 10 (as C3) |
| R0f fix (tier 1, the defaults) | 4574 of 4834 | 3747 | 274 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 135 (+1, UNSIGNED; the rows of R0f signed) | 128 | 540 (+1, ledgered) | 9 |
| R0f fix (tier 2, the defaults) | 53847 of 57393 | 40371 | 88 | 12 (0.096 %, as R0e) | 3443 (as R0f; signed) | 1824 (+1, ledgered) | 11645 | 10 (as C3) |
| R0g (tier 1, the defaults) | 4672 of 4859 | 3731 | 274 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 135 (as R0f fix) | 139 (+11, ledgered) | 570 (+30, ledgered) | 9 |
| R0g (tier 2, the defaults) | 54243 of 57393 | 40149 | 88 | 12 (0.096 %, as R0e) | 3443 (as R0f fix) | 1837 (+13, ledgered) | 11854 (+209, ledgered) | 10 (as C3) |
| R0g fix (tier 1, the defaults) | 4683 of 4871 | 3737 | 274 | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 137 (+2, `rv1_c4_task_unit_ok.wf`, `rv1_c4_site_local_spawn_ok.wf`, UNSIGNED) | 142 (+3, ledgered) | 571 (+1, `196_made_closure_tasks.wf`, ledgered) | 9 |
| R0g fix (tier 2, the defaults) | 54243 of 57393 | 40149 | 88 | 12 (0.096 %, as R0e) | 3443 (as R0g) | 1837 (as R0g) | 11854 (as R0g) | 10 (as C3) |
| R0h (tier 1, the defaults) | 4743 of 4901 | 3739 | 276 (+2: `opres.wf`, `fixes/r0h/d3r_callee_mut.wf`, which the old pipeline misses) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 139 (+2, `c4_resume_arg_ok.wf`, `dbg2.wf`, UNSIGNED) | 145 (+3, ledgered) | 587 (+16, ledgered) | 14 (+6 `open-old` probes of R0h, -1 `opres.wf`) |
| R0h (tier 2, the defaults) | 54393 of 57393 | 40044 | 92 (+4: `opres.wf`, three `d1_callee_mut` programs) | 12 (0.096 %, as R0e) | 3444 (+1, the copy of `dbg2.wf`, UNSIGNED) | 1857 (+20, ledgered) | 11938 (+84, ledgered) | 6 (-4) |
| R0h fix (tier 1, the defaults) | 4739 of 4910 | 3752 | 277 (+1: `rv1_r01_two_level_mut.wf`) | 1 (`fixes/f12c/n2/tw.wf`, ledgered) | 139 (signed by the review of R0h) | 145 | 582 (-5: the `v1c` files keep the old pipeline) | 14 |
| R0h fix (tier 2, the defaults) | 54386 of 57393 | 40051 | 92 | 12 (0.096 %, as R0e) | 3444 (signed) | 1857 | 11931 | 6 |

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
