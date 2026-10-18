# ADR 0001: Phase 1 scope and roadmap gates

Status: accepted. Date: 2026-10-18.

## Context

The design has three phases. Phase 1 proves the core. Phase 2 builds the systems
compiler and `std.rt`. Phase 3 can add a GC tier. The repository was empty.

## Decision

- We build Phase 1: parser, semantic analysis, fact generation, the Datalog spec, the
  production checker, agreement tests, Verus proofs, and a reference interpreter.
- The reference interpreter gives the dynamic semantics. It is not the Phase 2 runtime.
- Phase 2 items (native code, io_uring/kqueue/IOCP, HTTP/2, HTTP/3, TLS, SQL, profiler)
  wait for the Phase 1 gates.
- Phase 1 keeps Phase 3 possible: pointer types declare stability (ADR 0003).

## Consequences

- The gates are measurable: proofs verify, and the checker agrees with the spec.
- Users can check and run Weft programs, but only in the interpreter.
