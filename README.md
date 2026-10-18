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
  first : &Entity in world.entities[]  (line 2)
  push : mut(world.entities)           (line 3)
  world.entities is a strict prefix of world.entities[], through an unstable step  →  invalidated at line 3
  used at line 4
```

## Quick start

```bash
cargo build --release
./target/release/weft check tests/programs/02_bad.wf            # diagnostics
./target/release/weft check --explain tests/programs/02_bad.wf  # Datalog derivation trees
./target/release/weft check --json tests/programs/08_ingest.wf  # for coding agents
./target/release/weft agree tests/programs/05_effects.wf        # checker == spec?
./target/release/weft lint --rules examples/lints/ref_across_abort.dl FILE
./target/release/weft deps examples/package                     # dependency authority
./target/release/weft run FILE                                  # reference interpreter
./target/release/weft test tests/programs/10_sim.wf             # tests with the simulator
./target/release/weft explain W0405
```

## Layout

| Path | Content |
| --- | --- |
| `spec/weft.dl` | The static semantics as Datalog. This is the specification. |
| `crates/weft-syntax` | Lexer with automatic statement ends, parser, AST, diagnostics. |
| `crates/weft-sema` | Names, types, places, modes, effect inference, fact generation. |
| `crates/weft-facts` | The fact tables that the rules query. |
| `crates/weft-datalog` | A Datalog engine with stratified negation and provenance. |
| `crates/weft-check` | The production checker, the bridge to the spec, diagnostics. |
| `crates/weft-verified` | The verified core (Verus): place algebra, fixpoint, modes, lifecycles. |
| `crates/weft-interp` | The reference interpreter: handlers, scopes, deterministic simulation. |
| `crates/weft-cli` | The `weft` command and packages (`weft.toml`). |
| `proofs/` | Verus soundness proofs: group borrowing and algebraic effects. |
| `std/prelude.wf` | The standard prelude. |
| `tests/programs` | The design doc examples and one negative program per rule. |
| `docs/` | Plan, ADRs, grammar, architecture, traceability. |

## Status

- Phase 1 gate 1b (checker agrees with the spec): tested on every corpus program and on
  random fact sets.
- Phase 1 gate 1a (mechanized soundness): see `proofs/README.md` for what is proved and
  what remains.
- Phase 2 (native compiler, `std.rt` on io_uring/kqueue/IOCP, HTTP/2/3, TLS) and Phase 3
  (GC tier) are not started. See `docs/adr/0001-phase-1-scope.md`.

## Development

```bash
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
proofs/verify-all.sh          # needs `verus` on PATH, see proofs/README.md
```

License: Apache-2.0.
