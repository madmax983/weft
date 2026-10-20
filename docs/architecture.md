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
    spawn["s.spawn(closure)"] -- "sema" --> mut
    tend["end of a task: join, scope end"] -- "the writes of the task" --> lend
    value["call of a closure or an item value"] --> given["substitute its parameter places with the given places"] --> mut
    unknown["call of a function parameter or an unknown value"] --> lend["lends_mut(P, M)"] --> inv
    lend --> tc
    mut --> inv["invalidated_at(R, P)"] --> invalid["invalid(R, Q)"] --> err["error(R, P) = W0301"]
    drop["moved_at(V, P), scope_end(V, P), unwound_at(V, P), moved_part(M, P)"] --> own["owner(Rt, V)"] --> frees["frees_at(P, M)"] --> inv
    resume["resume after a change above a clause parameter"] --> rel["releases_at(P, M)"] --> frees
    via["write through a reference R"] --> wv["writes_via(P, R)"] -. "spares R" .-> inv
    frees --> tc["task_conflict(T, P) = W0405"]
    mut --> tc
```

## Linear values and values that are not set

```mermaid
flowchart TD
    bind["rebound_at(V, P)"] --> live["live_linear(V, Q)"]
    moved["moved_at(V, P)"] -. "ends" .-> live
    unwound["unwound_at(V, P)"] -. "ends on an abort path" .-> live
    empty["empty_at(V, P)"] -. "nothing to consume" .-> live
    over["overwrites(V, P)"] -. "a new part" .-> live
    live --> unc["unconsumed(V, P) = W0601"]
    send["scope_end(V, P)"] --> unc
    live --> ow["overwritten(V, P) = W0601"]
    bind --> ow
    over["overwrites(V, P)"] --> ow
    live --> ab["abort_unhandled(V, P) = W0602"]
    abort["may_abort(P)"] --> ab
    spared["spared_at(V, P)"] -. "outside the body of a local handler" .-> ab
    decl["unset_at(V, P)"] --> unset["unset(V, Q)"] --> ubs["use_before_set(V, P) = W0304"]
    bind -. "ends" .-> unset
    uses["uses(V, P)"] --> ubs
```

A linear variable is live from a new value until a move. A new value with no linear
part, such as `None`, has nothing to consume (`empty_at`). A new value of a part makes
the variable live too. It must not be live where it goes out of scope or where it gets
a new value. A new value of a part drops the old value of the part too (`overwrites`).
An abort while it is live needs `on abort`. An operation of a local handler aborts only
the values of its handled body (`spared_at`). On the path of an abort to the end of a
`handle`, the unwinder finishes the values of the handled body (`unwound_at`). A `let`
can declare a variable with no value, and a place field can have no value. Each path
must give it a value before a use.

A mutation invalidates a reference only through an unstable step. A move or the end of
the owner frees the memory, so it invalidates every reference into the owned value. A
free or a mutation while a task is active must not overlap the task footprint.

A function value can mutate through its reference parameters. A call that knows the
value (a closure or an item, also one that a higher-order callee lends places to)
mutates the places that it gives. A call of a function parameter or of an unknown
value gives its places away: `lends_mut` invalidates references as a mutation does,
and the caller sees the real mutation. A lent place is also a `call_mut` of the call,
so it must not overlap another argument (W0312). See ADR 0005.

## Effect inference

Sema infers the effects of each function that does not state them
(`crates/weft-sema/src/infer.rs`). A worklist lowers callees before callers. When a
signature changes, sema lowers again only the bodies that name that function. A last
lowering of every body finds a read that the names do not show. A new row is joined
with the old row, so a row only grows, and the lattice of rows is finite. So the
inference reaches a fixpoint. The bound for one row is the height of its lattice
(`infer::growth_limit`). A row that grows past it shows a checker bug: the inference
stops, and each function whose signature can still change gets W0706, an error.

Each body, also one whose function states its effects, also infers the other parts of
its signature:

- What it lends to its function parameters.
- What its returned function value does, and the places of its parameters that the
  value points into.
- Which function parameters it stores.
- Whether it can run a stored function value, what it gives to that value, and
  whether it can run one more than once.
- Whether an unknown function value that it calls can resume more than once.
- Which parameters a task of the body can call, and how a task runs a function
  parameter: on another thread, two times at one time, with which other parameters,
  and which places of the parameters the body writes and reads while it runs
  (`task_runs`, ADR 0006).
- Whether the body can start a pinned task for a reason that a caller does not see
  (`pins`).
- Which function parameters it gives to an operation of a handler of a caller, and
  what the values that it gives there perform.
- Which effects its tasks perform through a handler of a caller.
- Which function parameters it can call more than once.
- Which reference parameters can get a function value.
- Which parameters give references that it can put into an `rc` object.
- The places of its parameters that the closures that it puts behind a reference
  parameter point into.
- The type parameters of the values that it can drop or hold across an abort (ADR
  0007).

A new lowering replaces these parts, so they do not only grow. The parts of one
function can change at most 32 times and two more times for each function
(`infer::parts_limit`). After that, the inference keeps the last parts of that
function, and its callers use them. Its row can still grow. A function whose parts
still change at the end gets W0704, an error.

## Code structure of calls and diagnostics

Sema lowers a call of a function item in parts, each a function of its own
(`crates/weft-sema/src/body/call.rs`, `call_fn_as`): the order of the arguments
(`body/args.rs`), their evaluation, the call node, the checks of the argument places,
the effects, the function values that the callee gets, what the callee keeps, and the
result. `crates/weft-check/src/diagnose.rs` has one function for each rule.

The capability set of a value holds `caps::Held` elements: the capability of a local
handler (`Held::Cap`) or a mark, such as `Held::Nonportable`, `Held::NotMany` or
`Held::Resumed`. A `CapId` is always the capability of a handler.

## Commands

| Command | Stages |
| --- | --- |
| `weft check` | load (file or package) → sema → checker and, for a package, dependency authority (W0901, W0902) → diagnostics; `--explain` adds the spec derivations, each with the diagnostic that reports its fact |
| `weft agree` | load → sema → checker and spec → compare the violation sets, and the evidence of W0301 and W0405 with the derivations of the spec (`weft_check::evidence`) |
| `weft run`, `weft test` | load → sema → checker → refuse on errors (unless `--unchecked`) → interpreter |
| `weft deps` | load → sema → dependency authority (W0901, W0902) |

Authority names only the standard effects: a user effect of a dependency needs a
handler of the caller, not authority (ADR 0005). `weft run` and `weft test` use the same
checks as `weft check`, so an authority error of a package also stops them. `weft deps` shows only the authority errors and the authority
of each dependency.

`weft check --json` writes one JSON object for each diagnostic: the code, the
severity, the message, the location and the notes. A note with a location has its
line (`{"text": ..., "line": N}`). With `--explain`, each derivation is one more object
with the fact, its tree, the function and the code and location of its diagnostic
(`"diagnostic"`). A diagnostic holds the keys of the spec facts that it reports
(`Diagnostic::facts`, for example `body 3: error(v1, n6)`). The key holds the index
of the body, because two bodies can have the same name. The corpus test
`each_violation_has_one_diagnostic` checks that each violation has one diagnostic.

A single file takes its options from marker lines: `// weft: library` and
`// weft: no-runtime`. A package takes them from `weft.toml`. The flags `--lib` and
`--bin`, `--no-runtime` and `--runtime` win over both. An unknown word in a marker
gets W0804, a warning.

## Size limits

The parser rejects nesting deeper than 96 levels and chains of more than about 150
prefix operators, postfix steps or `else if` branches. It keeps each part of 32 binary
operators of a long chain in a hidden local, so a flat chain has no limit. Sema and the
interpreter walk the tree recursively. `crates/weft-cli/tests/limits.rs` runs the
parser, the printer, sema, the checker, the spec and the interpreter on a 2 MiB thread
for the largest program that parses, also for chains inside nested blocks.

The derivation printer of `check --explain` (`weft_check::bridge::render_derivation`)
uses a stack, not recursion. It shows at most 32 levels of indent. A chain is a path of
premises whose relations depend on each other in the spec: `invalid` after `invalid`, or
`live_out` and `live_in` in turn. The printer folds a chain of more than 8 steps. It
shows the first 3 and the last 3 steps, and one line ``... N more `invalid` steps ...``.
So a path of 10 000 statements gives a few kilobytes of text. `limits.rs` tests this on
a 2 MiB thread for the derivations of W0301 and W0503.

The library entry points run on a thread with a 256 MiB stack, as a margin
(`weft_sema::on_large_stack`, `weft_sema::STACK`): `weft_sema::analyze`,
`weft_sema::analyze_source`, `weft_check::check_source`, the `run_*` functions of
`weft_interp` and `weft_cli::run`. A nested call runs on the same thread. An
`Analysis` and a `Checked` are `Send` and `Sync`, so the result comes back to the
caller. `limits.rs` runs each of them for the deepest programs on a 256 KiB thread.

## Cost of the checker

The rules W0301, W0302 and W0304 run the searches of one variable in the part of
the graph that can reach its uses (`weft_check::rules::part_of`): the uses, and each
node with a path to a use whose inner nodes are not kill nodes. A path of a
propagation from a gen node to a use has only nodes of this part. So the verified
propagation in the part gives the same result at each use as in the whole graph, and
so does the evidence search of W0301. Only a node of the part can invalidate a
reference that the part can see, and each invalidating node needs a place with the
root of the reference. So a reference with a small part costs little, also in a
large function. `crates/weft-check/tests/scale.rs` checks 1000 uses of each cause of
W0301 in less than 1 s in a debug build.

Sema keeps each place that a reference local gets (ADR 0003), and a use of the local
reads each of them (W0405). So a body where one local gets references into `n`
different roots, such as `r = &v[0]` for `n` new vectors `v`, has about `n * n / 2`
`reads_at` facts. The checker cost stays linear in these facts.

## Verified pieces

| Piece | Verified property | Used by |
| --- | --- | --- |
| `places::invalidates` | equals rule 3 (strict prefix, unstable step after it) | checker W0301 |
| `places::within` | inclusion; a cover invalidates at least as much | checker W0703, W0402, W0203, W0204, W0605 |
| `places::overlaps` | symmetric may-alias; split sides are disjoint | checker W0312, W0405 |
| `places::{step_alias, step_within, step_class}` | equal their spec functions; steps of different classes are not related | bridge (pairwise step facts) |
| `places::concat` | concatenation of paths | not yet used (sema substitutes places with its own code) |
| `dataflow::propagate` | result is exactly the least fixpoint of the gen/kill rules | every dataflow rule |
| `modes::{submode, join}` | partial order and least upper bound | checker W0406, W0403, W0401, `pinned`; sema the uniqueness of joined values, branch states and closure captures, and the pins of tasks |
| `lifecycle::Continuation` | a `once` continuation resumes at most once | interpreter |
| `lifecycle::Linear` | a linear value is consumed or aborted at most once; a live value with no `on abort` does not unwind | interpreter |
