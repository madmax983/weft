# Architecture

## Pipeline

```mermaid
flowchart LR
    src[".wf source"] --> lex["lexer<br/>(statement ends)"] --> parse[parser] --> ast[AST]
    prelude["std/prelude.wf"] --> parse
    ast --> collect["items and signatures"] --> infer["effect inference<br/>(fixpoint)"] --> lower["lowering"]
    lower --> facts["FnFacts<br/>(per function)"]
    facts --> checker["production checker<br/>(weft-check)"]
    facts --> engine["Datalog engine<br/>(spec/weft.dl)"]
    checker --> violations1[Violations]
    engine --> violations2[Violations]
    violations1 -. "must be equal" .- violations2
    checker --> diags["diagnostics"]
    engine --> trees["derivation trees"]
    verified["weft-verified<br/>(Verus)"] --> checker
    ast --> interp["reference interpreter"]
    checker -- "stealable(T)" --> interp
```

## One mechanism for borrows and effects

```mermaid
flowchart TD
    call["call f(args)"] --> subst["substitute f's mut(...) with argument places"] --> mut["mutates_at(P, M)"]
    perform["perform op"] --> cap["performs_at(P, Cap)"] --> fp["footprint(Cap, M)"] --> mut
    spawn["s.spawn(closure)"] --> tw["task_writes(T, M)"] --> mut
    mut --> inv["invalidated_at(R, P)"] --> invalid["invalid(R, Q)"] --> err["error(R, P) = W0301"]
    drop["moved_at(V, P), scope_end(V, P)"] --> own["owner(Rt, V), root_of(Path, Rt)"] --> inv
```

A mutation invalidates a reference only through an unstable step. A move or the end of
the owner frees the memory, so it invalidates every reference into the owned value.

## Verified pieces

| Piece | Verified property | Used by |
| --- | --- | --- |
| `places::invalidates` | equals rule 3 (strict prefix, unstable step after it) | checker W0301 |
| `places::within` | inclusion; a cover invalidates at least as much | checker W0703, W0402 |
| `places::overlaps` | symmetric may-alias; split sides are disjoint | checker W0312, W0405 |
| `dataflow::propagate` | result is exactly the least fixpoint of the gen/kill rules | every dataflow rule |
| `modes::{submode, join}` | partial order and least upper bound | mode checks |
| `lifecycle::Continuation` | a `once` continuation resumes at most once | interpreter |
| `lifecycle::Linear` | a linear value finishes once: consumed or aborted | interpreter |
