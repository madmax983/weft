# Weft

Weft is a systems language with no garbage collector. Its compiler asks four questions
of every expression: what it is (type), how it may be used (mode), where it points
(place), and what it may do (effect).

This repository holds **Phase 1**: the core calculus, its checker, its Datalog
specification, Verus proofs, and a reference interpreter.

```weft
fn bad(world: &World) / mut(world.entities) {
    let first = &world.entities[0]
    world.entities.push(Entity.new())
    print(first.hp)   // error
}
```

```
error[W0301]: `first` used after it was invalidated
  --> bad.wf:4:5
  first : &Entity in world.entities[]  (line 2)
  push : mut(world.entities)           (line 3)
  world.entities is a strict prefix of world.entities[], through an unstable step  →  invalidated at line 3
  used at line 4
```

## Quick start

```bash
cargo build --release
W=./target/release/weft
$W check tests/programs/02_bad.wf                  # diagnostics
$W check --explain tests/programs/02_bad.wf        # Datalog derivation trees
$W check --json tests/programs/08_ingest.wf        # for coding agents
$W agree tests/programs/05_effects.wf              # checker == spec?
$W facts tests/programs/02_bad.wf bad              # the facts of one function
$W lint --rules examples/lints/ref_across_abort.dl tests/programs/18_polymorphism.wf
$W check examples/package                          # a package; `json` asks for too much
$W deps examples/package                           # dependency authority
$W run crates/weft-interp/tests/programs/effects_log.wf   # check, then run `fn main`
$W test tests/programs/10_sim.wf                   # check, then run the test blocks
$W explain W0405
$W help
```

`run` and `test` check the program first. They do not run a program that has errors,
unless you give `--unchecked`. `--seed N` and `--workers N` set the deterministic
scheduler of the reference interpreter. The exit code is 0 on success, 1 when the
program has errors or fails, and 2 on a usage error.

A single file sets its options with marker lines. `// weft: library` checks it as a
library (no root handlers). `// weft: no-runtime` selects the embedded profile (`main`
handles every standard effect). A package sets the same options in `weft.toml`
(`kind = "lib"`, `runtime = "none"`). The flags `--lib` and `--no-runtime` add to them.

## Layout

| Path | Content |
| --- | --- |
| `spec/weft.dl` | The static semantics as Datalog. This is the specification. |
| `crates/weft-syntax` | Lexer with automatic statement ends, parser, AST, pretty-printer, diagnostics. |
| `crates/weft-sema` | Names, types, places, modes, effect inference, fact generation. |
| `crates/weft-facts` | The fact tables that the rules query, and the violation sets. |
| `crates/weft-datalog` | A Datalog engine with stratified negation and provenance. |
| `crates/weft-check` | The production checker, the bridge to the spec, diagnostics, `weft explain` texts. |
| `crates/weft-verified` | The verified core (Verus): place algebra, gen/kill fixpoint, modes, lifecycles. |
| `crates/weft-interp` | The reference interpreter: handlers, continuations, scopes, deterministic simulation. |
| `crates/weft-cli` | The `weft` command and packages (`weft.toml`). |
| `proofs/` | Verus soundness models: group borrowing and algebraic effects. See `proofs/README.md`. |
| `std/prelude.wf` | The standard prelude. |
| `tests/programs` | The design examples and at least one negative program per rule. |
| `examples/` | A package with dependencies, a library, and a lint rule file. |
| `docs/` | The design, the plan, ADRs, the grammar and the architecture. |

## Status

- Phase 1 gate 1b (the checker agrees with the spec): tested on every corpus program and
  on random fact sets. Agreement is over the facts that sema emits. The fact generator
  is not proved.
- Phase 1 gate 1a (mechanized soundness): not complete. `proofs/borrowing` proves B1-B5
  for its model, and `proofs/effects` proves E1 and E4. `proofs/README.md` lists what is
  proved and what is not.
- The reference interpreter runs `main` and test blocks (`weft run`, `weft test`). It is
  the dynamic semantics, not the Phase 2 runtime.
- Phase 2 (native compiler, `std.rt` on io_uring/kqueue/IOCP, HTTP/2/3, TLS) and Phase 3
  (GC tier) are not started. See `docs/adr/0001-phase-1-scope.md`.

## Development

```bash
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
proofs/verify-all.sh          # needs `verus` on PATH; fails if a proof crate is missing
```

License: Apache-2.0.
