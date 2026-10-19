# Weft language design

Oct 18, 2026 · @Mark

> This is the design document that Phase 1 implements. It is kept here as the source of
> the traceability matrix (`docs/traceability.md`).

Weft is a systems language with no garbage collector. Its compiler asks four questions of every expression: what it is (type), how it may be used (mode), where it points (place), and what it may do (effect).

## Decisions

Weft starts as a systems language with no garbage collector. A layered, higher-level tier may come later, but only after the core is proven sound.

| Area | Decision | Why |
| --- | --- | --- |
| Niche | Systems first, no GC; layered tier deferred | Places matter most without a GC, and building low-level first is the cheaper direction |
| References | One kind, indexed by the place it points into | Replaces lifetimes, and `Cell`/`RefCell` within a thread |
| Mutation | An effect on places, declared on functions | Makes borrow checking and effect checking one mechanism |
| Threads | Modes (`portable`, `shared`, `uniq`), not traits | Shared-XOR-mutable applies only where threads or tasks meet |
| Resources | Affine by default; `linear` opt-in with `on abort` | Guaranteed cleanup, including on cancellation |
| Immovability | A `!Move` kind | Replaces `Pin` |
| Effects | Lexical capabilities with place footprints; one-shot continuations by default | A perform is checked like a call; no effect variables in surface syntax |
| Async | No keyword; `async` is an effect; the standard library ships the runtime | Go-style ergonomics without function coloring |
| Root handlers | Only binaries and tests install them | Prevents runtime and ecosystem splits |
| Checker | Specified as Datalog rules | A real spec, explainable errors, user-written lint rules |

Non-goals: no lifetime parameters, no `Send`/`Sync` traits, no `Cell`/`RefCell`, no `Pin`, no `async`/`await` keywords, and no tracing GC in this phase.

## Places and mutation

Every reference records the place it points into, and only a mutation of an enclosing place can invalidate it. This is group borrowing, the approach Valen and Ante are converging on.

### Places

A place is a path from a root through fields, collection elements and enum variants: `world.entities[].hp`, `opt.Some`. Single ownership guarantees each object has exactly one path. A root is a local, a parameter or a global.

Each step in a path is either **stable** or **unstable**:

- **Stable:** struct fields, fixed-size arrays, primitives. Mutation never moves or frees what's behind them.
- **Unstable:** enum payloads, a collection's heap buffer, the target of a reassignable `Box`. Mutation can free or replace what's behind them.

### Rules

1. A reference's type includes its place: `&Entity in world.entities[]`.
2. A function declares the places it mutates as an effect: `/ mut(e)`.
3. A `mut(p)` effect invalidates references that point strictly inside `p` through at least one unstable step.
4. References *to* `p`, and references into stable parts of `p`, survive.
5. Using an invalidated reference is a compile error.

There is one reference kind. Mutability lives on the function, not on the reference type.

### Example

```weft
struct World { entities: Vec<Entity>, events: Vec<Event>, score: u32 }

// `e` points somewhere inside world.entities[]; step may mutate only e
fn step(world: &World, e: &Entity in world.entities[]) / mut(e) {
    e.advance()
    let hit = world.collision_for(e)   // reading all of world: fine
    e.resolve(hit)
}

fn tick(world: &World) / mut(world.entities[], world.events, world.score) {
    for e in world.entities[] {
        step(world, e)
        if e.hp <= 0 {
            world.events.push(Died(e.id))  // disjoint from entities: e stays valid
            world.score += 10              // stable place: invalidates nothing
        }
    }
}
```

### What the checker rejects

```weft
fn bad(world: &World) / mut(world.entities) {
    let first = &world.entities[0]
    world.entities.push(Entity.new())
    print(first.hp)   // error
}
```

The diagnostic is the derivation, not just a message:

```
error[W0301]: `first` used after it was invalidated
  first  : &Entity in world.entities[]          (line 2)
  push   : mut(world.entities)                   (line 3)
  world.entities is a strict prefix of world.entities[]  →  invalidated at line 3
  used at line 4
```

### Inference and signatures

Places and `mut` effects are inferred inside function bodies. Public signatures state them, so callers and agents can read them without running a language server. A wildcard such as `mut(world..)` means "anywhere inside `world`" and keeps signatures short.

## Modes and threads

Weft enforces shared-XOR-mutable only where threads or tasks meet, using OxCaml-style modes instead of `Send`/`Sync` traits. Within one task, group borrowing allows shared mutation.

> **Phase 1 note.** At a call, the checker is stricter than this. A callee sees each
> reference parameter as a separate place, so `attack(x, y)` with `x` and `y` both in
> `world.entities[]` gets W0312 when `attack` mutates them. To allow the aliasing, the
> callee states the shared place with `in`:
> `fn attack(w: &World, a: &Entity in w.entities[], b: &Entity in w.entities[]) / mut(a, b)`.
> See ADR 0005 and `tests/programs/34_alias_in_one_task.wf`.

| Mode axis | Values | Meaning |
| --- | --- | --- |
| Uniqueness | `uniq`, `aliased` | Whether other references to the value may exist |
| Portability | `portable`, `nonportable` | Whether the value may cross to another thread |
| Contention | `uncontended`, `shared` | `shared` means read-only from every thread |
| Affinity | `once`, `many` | Whether the value (often a closure or continuation) may be used more than once |

### Rules

- A shared-mutable reference is always `nonportable`. It cannot be captured by anything that runs on another thread.
- Closures passed to `fork` or spawned as stealable tasks must be `portable`.
- Data visible to several threads must be `shared`, or split into `uniq` parts whose places are proven disjoint.
- Immutable plain data crosses modes automatically (mode crossing), so most code writes no modes at all.
- A type has at most one mode on each axis. Also `uniq` and `shared` contradict: other threads can read a `shared` value, so other references to it exist. Both are errors (W0119).

Modes are inferred in bodies and appear only in public signatures that need them.

### Example

```weft
fn total_hp(world: &World @ shared) -> u64 / par {
    let (l, r) = world.entities.split_at(world.entities.len() / 2)
    let (a, b) = fork(|| sum_hp(l), || sum_hp(r))   // closures must be @ portable
    a + b
}

fn heal_all(world: &World) / mut(world.entities[]), par {
    let (l, r) = world.entities.split_mut(mid)     // l, r : @ uniq, disjoint places
    fork(|| heal(l), || heal(r))
}
```

## Linear and immovable types

Values are affine by default: usable at most once, dropped automatically. Types that hold resources can be `linear`, which means they must be consumed, and each must say what happens if an effect aborts its scope.

### Linear types

```weft
linear struct Tx { conn: Conn, ... }
    on abort = rollback        // runs only if an effect aborts the scope

fn transfer(db: &Db, from: Id, to: Id, amt: u64) / io, fail {
    let tx = db.begin()
    tx.debit(from, amt)        // `fail` may abort here: allowed because Tx declares `on abort`
    tx.credit(to, amt)
    tx.commit()
}   // dropping tx without commit or rollback on the normal path → compile error
```

- A linear value must be moved or consumed on every normal path.
- It may be live across an operation that can abort only if its type declares `on abort`.
- `on abort` runs during unwinding (cancellation, `fail`), never on the normal path.
- A linear value may not be live across a `multi` effect operation (see Effects).

This gives the guarantee Rust's proposed `!Forget` trait aims for, and it covers async cleanup with the same rule.

### Immovable types

`!Move` is a kind: values of a `!Move` type keep a fixed address for their whole life and are constructed in place. Self-referential structs and task stacks use it. There is no `Pin`.

## Effects and handlers

An effect handler is a capability value whose type records the places it mutates, its footprint. Performing an operation is checked exactly like calling a function with that footprint.

### Rules

- Effects are sets of declared operations. Functions list their effects after `/`; bodies infer them, public signatures state them.
- Handlers are lexical: an operation reaches the handler in scope where the function was written, not whichever handler happens to be on the dynamic stack.
- Each perform site is checked as a call with the handler's footprint, so it invalidates references exactly as that call would.
- Functions that only pass effects through don't name effect variables. Effect polymorphism stays silent, following the modal effect types approach.

### Example

```weft
effect Log { fn log(msg: String) }

fn simulate(world: &World) / mut(world.entities[]), Log {
    for e in world.entities[] {
        step(world, e)
        log("stepped {e.id}")    // checked as a call with the handler's footprint
    }
}

fn main(env: Env) / io {
    let world = World.load(env.fs)
    let lines = Vec.new()
    handle Log { fn log(msg) { lines.push(msg); resume(()) } }   // footprint: mut(lines)
    in simulate(&world)
    env.stdout.write_all(lines)
}
```

`simulate` never points into `lines`, so logging invalidates nothing. If it held a reference into `lines`, the perform site would be rejected exactly like an ordinary call.

### Continuations

A continuation is a value with a mode and the places it captured.

- Continuations are `once` by default: a handler may resume at most once.
- An operation declared `multi` may resume several times. Everything live across its perform site must be `@ many`, which rules out linear values and unique borrows there.

This closes the hole where a handler resumes twice and uses the same moved value twice.

### Authority

Effects double as capabilities. `main` receives the root capabilities (filesystem, network, clock, randomness) through `env`. The package manager checks each dependency's effect signatures against the authority the project grants it, so a JSON parser that asks for `Net` is rejected at install time.

## Memory without a garbage collector

Weft has three memory tiers, all checked by the same place rules, and no tracing GC in this phase.

1. **Owned values.** The default: on the stack or in a `Box`, freed deterministically at the end of their scope.
2. **`rc` groups.** A reference-counted type carries a group place shared by all its clones. Mutating through any clone is `mut(group)`, which invalidates unstable references into the group. Graphs and doubly-linked structures work without runtime borrow flags.
3. **Fully in-place functions.** Functions marked `fip` are checked so that pure code over uniquely owned data compiles to in-place updates with no allocation.

Cycles in `rc` groups still leak unless broken with weak references; the place rules make cyclic mutation safe, not cyclic collection.

### Keeping a GC tier possible

A future layered tier would add GC'd types. The core must not rule that out:

- A GC'd pointer will be modeled as a **stable** step, so references reached through it survive any mutation. The calculus must therefore treat stability as a property pointer types declare, not a fixed list.
- Enum payloads stored inline inside a GC'd object stay unstable. Matching on them would copy, as Ante does for its shared types.
- Libraries may never require the GC. Only a binary may switch it on.

## Concurrency and the async runtime

The standard library defines the concurrency and IO effects and ships one runtime, `std.rt`, which the generated entry point installs before `main`. There is no `async` keyword and no future type.

### Root handlers

The standard effects are `Async`, `Net`, `Fs`, `Clock`, `Rand`, `Log` and `Blocking`. `std.rt` handles all of them with a work-stealing scheduler sized to the machine's cores, on io\_uring, kqueue or IOCP.

- **Only binaries and test harnesses may install a root handler** for a standard effect.
- Libraries may *intercept* standard effects (retries, tracing, rate limiting, mocks) but can never be the runtime.
- The runtime handles only the standard effects. So `main` and each test must handle every other effect that they perform (W0805).

Libraries are written against the effect interfaces and can't name a runtime, so the ecosystem can't split by runtime.

```weft
fn main(env: Env) / io {
    http.serve(env.net.listen(":8080"), handle)
}

fn handle(req: Request) -> Response / net, log {
    let user = db.user(req.param("id"))   // suspends here: no await, no future type
    log.info("served {user.id}")
    Response.json(user)
}
```

### Tasks

A task is a one-shot continuation. An IO call performs `Async.suspend`; the runtime parks the continuation with the event poller and a worker resumes it when the IO is ready. A function that can suspend has `/ async` in its type, usually inferred, and effect polymorphism means higher-order code like `map` works with async closures unchanged.

### Scopes and cancellation

Scopes are the only way to spawn. Task handles are `linear`: they must be joined or explicitly detached.

```weft
fn profile_page(id: Id) -> Page / net {
    scope { s =>
        let user  = s.spawn(|| api.user(id))
        let posts = s.spawn(|| api.posts(id))
        Page(user.join(), posts.join())
    }   // children can't outlive the scope; one failure cancels the siblings
}

let page = with_timeout(2.s) { profile_page(id) }   // a handler that aborts the block
```

Cancellation means "abort at the next suspension point." It unwinds the task and runs each live linear value's `on abort`, so partially completed work can't be silently dropped.

### Separation between tasks

**Tasks that may run at the same time must have separate footprints**, even on one thread. Spawning is checked like `fork`:

```weft
fn ingest(batch: &Batch, stats: &Stats) / mut(stats), async {
    scope { s =>
        s.spawn(|| stats.count += batch.len())   // mut(stats)
        s.spawn(|| upload(batch))                // reads batch only: fine
        s.spawn(|| print(stats.count))           // error: reads stats while task 1 mutates it
    }
}
```

Three things follow:

- **References survive suspension.** No other task can touch a task's mutated places, so suspending never invalidates its references.
- **Preemption is free.** Being descheduled is invisible, so the compiler inserts yield points at loop back-edges without marking pure loops `async`.
- **Work stealing follows from modes.** A task whose captured state is `@ portable` may move between workers; one that captured a thread-local reference stays pinned. The scheduler reads this from the type.

### Blocking

Foreign calls and blocking syscalls carry a `/ blocking` effect:

```weft
extern fn sqlite3_step(stmt: *Stmt) -> i32 / blocking
```

`std.rt` moves every `blocking` call onto a separate blocking thread pool. The compiler knows statically which calls block, so no task can stall a worker by accident.

### Deterministic simulation

The test harness can replace every root handler at once: clock, network, randomness and the scheduler.

```weft
test "election survives a partition" {
    sim.run(seed: 42) {
        let cluster = Cluster.start(5)
        sim.net.partition([0, 1], [2, 3, 4])
        sim.clock.advance(30.s)
        assert cluster.leaders().len() == 1
    }
}
```

The scheduler is simulated too, so task interleavings are deterministic and a failing seed replays exactly.

### Implementation notes

- **Stacks.** Weft can't grow stacks by copying them as Go does, because it has interior references and `!Move` types. Tasks get lazily committed virtual-memory stacks with guard pages.
- **Stackless tasks.** Suspension is in the type, so the compiler knows which frames can be live across a suspend point. Shallow tasks compile to stackless state machines for Go-like density.
- **Dispatch.** `Async` is a built-in handler, so a perform compiles to a direct stack switch rather than a handler search.
- **WebAssembly.** The runtime maps onto Wasm stack switching where available, with a continuation-passing fallback.
- **Embedded.** A no-runtime profile lets `main` install a minimal executor in place of `std.rt`.

## Standard library

The standard library is batteries-included, versioned with the language, and has one blessed way to do each job. Third-party libraries compete on features, never on which runtime they use.

What ships:

- The runtime and scheduler, channels, and `select` (built on scopes, so losing branches are cancelled cleanly).
- HTTP/1.1, HTTP/2 and HTTP/3 server and client, plus TLS.
- JSON, a SQL driver interface, structured logging and tracing.
- One formatter, one test runner with the simulator built in, and one profiler that understands tasks.

Rules that keep it prescriptive:

- Libraries cannot name or depend on a specific runtime; they use the standard effect interfaces.
- Libraries may intercept standard effects but may not install root handlers.
- The standard effect interfaces change only with a language edition.

## Static semantics as Datalog

Weft's rules for places, effects and modes are published as a Datalog program over facts the compiler extracts from its intermediate representation. That program is the specification.

```
invalidated_at(R, P) :- points_into(R, Path), mutates_at(P, M),
                        strict_prefix(M, Path), crosses_unstable(M, Path).
invalid(R, Q)        :- invalidated_at(R, P), cfg_edge(P, Q).
invalid(R, Q)        :- invalid(R, P), cfg_edge(P, Q), !rebound_at(R, P).
error(R, P)          :- uses(R, P), invalid(R, P).

mutates_at(P, M)     :- performs_at(P, Cap), footprint(Cap, M).   // effects feed the same relation
```

What this buys:

- **A real spec.** The rules define the checker; they don't just describe it.
- **Explainable errors.** Every error is a derivation tree that people and coding agents can walk.
- **User lint rules.** Projects can add their own rules as queries over the same facts.

The production checker is a specialized implementation that must agree with the rules on every test program. That follows the Polonius lesson: a general Datalog engine didn't scale for Rust, but the model did.

Generating the facts is not relational. Type inference, trait resolution, and place and mode inference happen first and produce the tables the rules query.

## Roadmap

Weft is built bottom-up: prove the core, then build the systems compiler, and only later consider a layered GC tier.

Phase 1 ends when the core calculus has a mechanized soundness proof and the production checker agrees with the Datalog rules. Phase 2 ends when a real HTTP service and its simulation tests run on `std.rt`. The GC tier waits until both gates pass.

## Open problems

The biggest risk is soundness: group borrowing combined with effect footprints has no proof yet, and Phase 1 exists to settle it.

- **Soundness.** The core calculus of places, modes, footprints and one-shot handlers needs a mechanized proof, in the style of OxCaml's mode-crossing work in Rocq/Iris.
- **Private fields leak.** Places expose field names in public signatures. Weft needs abstract places that a type can export without revealing its fields.
- **Polymorphism.** Generics over types, modes, places and effects at once is the largest ergonomic risk. The design relies on inference and on keeping these parameters out of sight by default.
- **Multi-shot continuations.** Restricting them to `@ many` state rules out some backtracking idioms over linear data.
- **Task density.** Virtual-memory stacks cost more per task than Go's goroutines unless the stackless optimization applies.
- **`rc` cycles.** Cyclic mutation is safe, but cyclic structures leak without weak references.
- **Checker performance.** The production checker must match the Datalog spec while staying fast on large codebases.

## Prior art

See the original issue for links: group borrowing (Valen, Ante), Rust's borrow checker within and Polonius, OxCaml modes and mode crossing, immobile types, FP² (Koka), modal effect types, Lexa lexical handlers, Flix effect-based supply chain defence, Scala tracked capabilities, Eio, Go `testing/synctest`, Zig 0.16 I/O, and `wasm_of_ocaml` stack switching.
