# Phase 1 plan

Status: accepted. Date: 2026-10-18.

This plan tells how we build Phase 1 of Weft. The design doc is the source. Phase 1
ends when two gates pass:

1. The core calculus has a mechanized soundness proof.
2. The production checker agrees with the Datalog rules on every test program.

## 1. Scope

In scope:

- A parser for the Weft syntax in the design doc.
- Name resolution, types, places, modes and effects for that syntax.
- Fact generation: the compiler writes the tables that the rules query.
- The Datalog specification (`spec/weft.dl`) and a Datalog engine that runs it.
- The production checker. It is a specialized implementation of the same rules.
- Agreement tests between the checker and the Datalog engine.
- Diagnostics that show the derivation. JSON output for agents.
- User lint rules as Datalog queries over the same facts.
- A verified core in Verus: the place algebra, the dataflow fixpoint, the mode lattice,
  and the continuation and linear-value state machines.
- Soundness proofs in Verus for group borrowing and for algebraic effects (section 6).
- A reference interpreter. It gives the dynamic semantics of handlers, one-shot
  continuations, `on abort`, scopes, cancellation and deterministic simulation.
- The package authority check and the root-handler rule.

Out of scope (gated by the roadmap):

- A native code generator and `std.rt` on io_uring, kqueue or IOCP (Phase 2).
- HTTP/2, HTTP/3, TLS, the SQL driver interface and the task profiler (Phase 2).
- The GC tier (Phase 3). Phase 1 keeps it possible: stability is a property that pointer
  types declare.

## 2. Brainstorming

We collected ideas without judgment first. Then we kept the ideas marked (+).

- (+) Use the Polonius architecture: facts per function, rules over facts, and a fast
  specialized checker.
- (+) Write our own small Datalog engine. It must load rules at run time (for user lint
  rules) and record provenance (for derivations). Compile-time engines cannot do this.
- (-) Use Soufflé. It is an external C++ tool and it has no provenance API for us.
- (+) Make the verified Verus code the shipped code. `vstd` compiles on stable Rust, so
  the `verus!` macro erases proofs in a normal build.
- (+) Use one verified gen/kill propagation for all forward and backward analyses:
  invalidation, moves, linear liveness, task activity and liveness across `multi`.
- (+) Treat a spawn as a mutation at the spawn node. Then the normal invalidation rule
  covers references that a task can break after it joins.
- (+) Use split segments (`v[..k]`, `v[k..]`) to prove that `split_mut` parts are
  disjoint.
- (+) Make the scheduler read a `stealable(T)` relation from the checker.
- (+) Use Go-style automatic semicolons, because the doc syntax has no semicolons.
- (+) Use the design doc examples as acceptance tests.
- (+) Extend the existing group-borrowing soundness proof
  (madmax983/group-borrowing-soundness) instead of a new proof.
- (-) Mechanize the full calculus in Rocq/Iris now. This is a research project.
- (+) Prove effects as an abstract machine in Verus: frames, handler frames, delimited
  one-shot continuations and an unwinder.
- (+) Write the interpreter as a CEK machine. Captured continuations are then a slice of
  the frame stack.

## 3. Reverse brainstorming

Question: "How can we make Phase 1 fail?" Each answer has a prevention.

| How it fails | Prevention |
| --- | --- |
| The spec and the checker drift apart. | Agreement tests on every program and on random fact sets. CI gate. |
| The proof verifies a model, not the shipped code. | Verified exec functions are the shipped functions. Proofs link the exec core to the model. |
| The fact generator misses a fact. | One negative test per rule. Doc examples. Tests for each fact kind. |
| A proof is vacuous. | Each theorem has a satisfiable-hypothesis example and a mutation test, as in the original proof. |
| The newline grammar is ambiguous. | Automatic semicolons with fixed rules. Parser tests on every doc snippet. |
| Effect inference does not terminate. | Subsumption of places and a depth limit. |
| The checker rejects the doc examples. | The doc examples are acceptance tests. |
| Scope grows to HTTP/3 and TLS. | Roadmap gates. Explicit out-of-scope list. |
| Errors are not explainable. | Snapshot tests of diagnostics and derivations. |
| The Verus build is slow or breaks CI. | A separate, cached CI job with a pinned Verus revision. |
| Handlers break the frame argument. | Model handlers and closures as calls with captured arguments (proof item B2). |

## 4. Six thinking hats

**White (facts).** The repository was empty. Rust 1.97 is stable here. Verus builds
from source at revision `1888846b`. `vstd` from crates.io compiles on stable. The
group-borrowing proof verifies with 33 verified and 0 errors. It covers straight-line,
single-threaded programs with no stored references.

**Red (feelings).** The place algebra feels right. The interaction of handlers and
places feels risky. One pull request for a full runtime feels too large.

**Black (risks).** The full calculus has no soundness proof. Handler footprints and
callee aliasing are subtle. Generics over types, modes, places and effects are hard. A
naive Datalog engine can be slow.

**Yellow (benefits).** One mechanism does borrow checking and effect checking. Errors are
derivations that people and agents can walk. Simulation makes concurrency tests
deterministic.

**Green (new ideas).** One verified propagation for all analyses. Spawn as mutation.
Split segments. A `stealable` relation. A call-site aliasing rule that also covers
handler footprints.

**Blue (process).** Each rule follows the loop SPEC, PROOF, RED, GREEN, REFACTOR. We
commit after GREEN. We stop review rounds at three.

## 5. Work breakdown

| # | Work package | Output |
| --- | --- | --- |
| W1 | Workspace, AST, grammar, fact schema, Datalog spec | `crates/*`, `docs/grammar.md`, `spec/weft.dl` |
| W2 | Datalog engine | `crates/weft-datalog` |
| W3 | Parser | `crates/weft-syntax` |
| W4 | Verified core | `crates/weft-verified` |
| W5 | Production checker and agreement tests | `crates/weft-check` |
| W6 | Semantic analysis and fact generation | `crates/weft-sema` |
| W7 | Reference interpreter and simulation | `crates/weft-interp` |
| W8 | CLI, manifest, lint rules, prelude | `crates/weft-cli`, `std/` |
| W9 | Soundness proofs | `proofs/borrowing`, `proofs/effects` |
| W10 | Review, traceability, pull request | `docs/traceability.md` |

## 6. Proof workstream

The order comes from the review of the group-borrowing proof.

Borrowing (`proofs/borrowing`, extends the original proof):

- B1. Branches and loops. The join is the intersection of valid references. Lemma: if the
  invariant holds for a set of references, it holds for each subset.
- B2. Captured references. A closure or handler is code plus captured `(var, is_mut)`
  pairs. A call, a perform or a resume is a `Call` with the captured references added.
- B3. Inline layout. Interior pointers, a layout set by the type, and out-of-bounds
  access as UB. This covers stable fields and inline enum payloads.
- B4. Task separation. Two interleaved instruction streams. Theorem: no data race.
- B5. Progress. A checked instruction can step or stops with a defined abort.
- B6. Executable checker. The exec core is proven to implement the spec rule.

Effects (`proofs/effects`):

- E1. Effect safety. A checked program never performs an effect with no handler.
- E2. One-shot safety. A `once` continuation resumes at most once.
- E3. Abort safety. Each linear value is consumed or aborted exactly once. `on abort`
  never runs on the normal path.
- E4. Lexical resolution. A perform reaches the handler bound where the code was written.
- E5. Multi-shot restriction. A frame that a `multi` continuation can copy holds no
  linear value.

## 7. TDD loop

For each rule:

1. SPEC. Write the Datalog rule and, for core rules, the Verus spec.
2. PROOF. Prove the core lemma in Verus.
3. RED. Add a failing test: a happy path, an edge case and a negative program.
4. GREEN. Add fact generation and the checker code.
5. REFACTOR. Keep proofs, agreement tests and unit tests green.

## 8. Gates

- Gate 1a: the proofs in section 6 verify with no `assume`, `admit` or
  `external_body` in the proof crates.
- Gate 1b: the checker and the Datalog engine agree on all test programs and on random
  fact sets.
- CI order: format, clippy (pedantic and nursery), tests, coverage, Verus.
