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
   `--facts=ir`;
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
| R1 | Standalone `typeck`, part 1 | C3 and one review round | yes (D0) |
| R2 | Standalone `typeck`, part 2; switch the THIR source | R1 | yes |
| R3 | Remove the old fact generator | R2 | yes |
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

### Phase R: removal

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

- Depends on: R2.
- Read: ADR 0012 (D20).
- Goal: one fact generator.
- Files: delete `crates/weft-sema/src/body/`, `crates/weft-sema/src/thir/record.rs`,
  the re-lowering loop of `crates/weft-sema/src/infer.rs` (keep `growth_limit` for
  W0706), `FactGen::Old` and `Both`, `Options::ir_groups` and `irbuild/scope.rs` (all
  groups are on), `FnFacts::mark`/`rewind`/`FactMark` in `crates/weft-facts/src/lib.rs`,
  the closure summary of `Ty::Fn` and `fn_joins` in `crates/weft-sema/src/types.rs`,
  W0707 and W0704 in `crates/weft-check/src/codes.rs` (their texts say "no longer
  reported" or the codes go, with the test `every_code_has_a_test` updated),
  `crates/weft-gate` (the `old` side becomes the committed baseline of C3).
- Tests first: the gate compares the new pipeline with the committed C3 snapshot
  (`tests/gate/baseline-c3.jsonl`): no difference.
- Do: delete; fix the imports; update `CLAUDE.md` ("Fact generation:
  `crates/weft-sema/src/irbuild/`, `analysis/`, `factgen/`").
- Gate: the common gates; tier 2 against the C3 snapshot.
- Exit: `body/` is gone; no gate difference.

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
| F8.1 | F8 | W0301 / W0304: a place-field reference in a `!Move` value travels with the moved value in the analysis (`r2/oracle/probes/n?_immov_*.wf`, `changed`; `tests/programs/154_place_fields.wf` `move_set`, group F, a W0301 false positive). Fix: relocate place-field references on a move (ADR 0007). Needs group F for 154 | open (do it at or before F20) |
| F8.2 | F8 | the gate: the key of the `ir` oracle cache is the hash of `crates/weft-interp/src` only, so a change of the IR builder does not make the cache stale. Stage F8 regenerated both `ir` caches by hand | open |
| F8.3 | F8 | lost-clean W0301 / none: receiver order and `Bounds` (second review of F8, 4.2). In `w.entities[0].plus(shrink(&w))` the `ir` pipeline accepts the program (old: W0301), and the IR engine stops at the borrow with "index 0 is out of bounds" (benign). The safety rests on the second index check of the engine at the borrow (`crates/weft-interp/tests/compile_ir.rs`). The third review of F8 signed the `lost-clean` entry after the fix of hole R1 (a variant step in a receiver place, F8d). The 11 programs are in `tests/gate/probes/fixes/f8/receiver_bounds/` (tier 1, 11 `lost-clean`, 0 blockers); claim F8-RB is on and holds | done (F8.3) |
| F10.1 | F10 | lost-fault W0301, W0302, W0601 / none in group A (review of stage F10, before group B). Hole H-B: a body with no IR (a type error with no W01xx diagnostic, a conflict in the THIR tables, a variant payload) got no facts, and the program stayed in scope, so no pipeline checked the body. Fix: such a program is out of scope (`irbuild::Entry::reported`). The root cause of the loop shapes (`let best = None` before `best = Some(e)` later in a loop: the lowering visits the body in more than one pass, and the THIR recorder kept the types of each pass) is fixed too: the THIR tables keep the decisions of the last pass of each loop (`Recorder::next_pass`). A variant payload of two fields (`e.A`) still has no IR (typeck accepts it): such a program is out of scope. The programs are in `tests/gate/probes/fixes/f10/hb/`; claim F10-HB. Hole H-A: a reference stored behind a reference parameter (a heap slot) and read back after its referent changes was accepted (no variable held the places of the slot). Fix: each heap slot has variables of its own (`factgen::holders`, docs/ir.md 6.6 "As built (F10.1)"); the 22 programs are in `tests/gate/probes/fixes/f10/ha/` (14 group A: `moved`, the ir pipeline reports the read in the body, the old pipeline the call in the caller); claim F10-HA | done (F10.1) |
| F10.2 | F10 | lost-fault W0301 / none in group A (second review of stage F10, hole H-C). A callee stores a reference through a reference that its argument holds (`out[0].push(&v[0])` with `out: &Vec<&Vec<&T>>`); the caller did not give the referent of `out[0]` the stored places, so `v.clear(); print(inner[0].hp)` was accepted (5 regressions where the referent is behind a parameter, 11 programs that both pipelines missed). Fix: the part `stores` reaches the referents of the references that an argument holds (`σ(Held(j))`, or `σ(Param(j))` of a by-value argument), with the reach of the part `muts` and the R3RT6 type rule on the type of the root of the referent (`analysis::apply::stores`, docs/ir.md 6.7 "As built (F10.2)"). The programs are in `tests/gate/probes/fixes/f10/hc/` (16 group A, 2 group AB, 1 control) and `tests/programs/165_store_through_held_ref.wf`; claim F10-HC | done (F10.2) |

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
