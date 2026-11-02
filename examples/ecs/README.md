# Typed ECS prototype

A small ECS written in Weft. It has two archetypes with dense component columns,
generation-checked entity handles, row migration, and a deferred command queue.
It uses only the current language and prelude. It needs no compiler changes.

## Run

From the repository root:

```sh
cargo build --release -p weft-cli
./target/release/weft run --oracle examples/ecs/ecs.wf
./target/release/weft test --oracle examples/ecs/ecs.wf
cargo test -p weft-interp --test ecs
```

The demo creates 64 entities. Every second entity has velocity. It runs movement
and damage for 10 ticks. The expected output is:

```text
entities=64 ticks=10 checksum=12768
```

The Rust integration test also runs all Weft test blocks with both the AST and IR
interpreter engines. Each engine uses `(seed, workers)` values `(1, 1)` and
`(42, 4)`. Oracle checks are on. An IR fallback fails the test. Static checks use
the default fact pipeline; this does not claim that the unfinished IR fact
pipeline has been validated for tasks.

## Storage

| Archetype | Dense columns | Matching systems |
| --- | --- | --- |
| Moving | entity slot, Position, Velocity, Health | movement, damage, dead-entity collection |
| Still | entity slot, Position, Health | damage, dead-entity collection |

Each entity handle has a slot index and a `u32` generation. The slot records the
archetype and row. Despawn fills a hole with the last row and repairs that row's
slot. It then increments the generation and returns the slot to a free list.
A slot at the maximum generation is retired on despawn. Generations never wrap.

Adding Velocity moves a row from Still to Moving. Removing it moves the row back.
Position and Health survive the move. The handle does not change.

The schema is fixed. These two tables are the implementation of the queries.
There is no type-erased component registry, generic query DSL, change tracking,
plugin registration, or automatic system scheduler yet. Plain structs are copy
values, so components in this prototype must be plain data.

## API

The functions live in `ecs.wf`. For example, this body uses the ECS:

```weft
let w = world_new()
let q = Vec.new()
let player = spawn(&w, Position(0, 0), Some(Velocity(2, 1)), 100)

integrate(&w)
damage(&w, 1)
q.push(SetVelocity(player, None))
collect_dead(&w, &q)
apply_commands(&w, &q)

assert position(&w, player) == Some(Position(2, 1))
assert valid(&w)
```

`position` returns a copy of the component. `contains`, `position`, `despawn`,
and `set_velocity` validate the handle before indexing. Stale or out-of-range
handles return `false` or `None`.

Handles belong to the world that created them. This first version has no world
identity in a handle. Passing one to another world is outside the API contract.
Weft currently has no field privacy. Clients must treat slots, columns, the free
list, `reserve`, and row-removal functions as internal. `valid` checks their
invariants for tests and debugging. It is not a hot-path operation.

## Place rules

The key system signatures are:

```weft
fn integrate(w: &World) / mut(w.moving.positions[])
fn damage(w: &World, amount: i64) / mut(w.moving.health[], w.still.health[])
fn collect_dead(w: &World, q: &Vec<Command>) / mut(q)
```

Movement changes existing elements. A reference into the Position column remains
valid across it. Enqueuing commands also preserves component references: it only
changes the separate queue. Applying commands changes the table storage. A
component reference used after that barrier is rejected with W0301.

The integration tests cover the same rejection after spawn, despawn, and migration.
They also require checker/spec agreement for the positive program and the negative
cases. A conflicting pair of tasks must produce W0405.

`heal_moving` shows explicit parallel work. It splits the Health column with
`split_mut` and gives each `fork` branch a unique slice. This is a simulated
parallelism test. The interpreter uses virtual workers.

Structural function signatures conservatively name both tables. A call can
invalidate more references than its particular runtime branch needs to. Keep
structural changes at explicit barriers.

## Commands

Commands are `Spawn`, `Despawn`, and `SetVelocity`. They run in FIFO order.
The queue is cleared after a successful flush. The result is the number of
successful commands. Stale entity commands are skipped. A queued spawn does not
reserve or return a handle before the flush.

A flush is not a transaction. A runtime failure can leave earlier commands
applied. There is no rollback. Systems should collect structural changes first,
finish all component-reference uses, and then flush.

## Comparison controls

The optional Rust project uses Bevy ECS 0.20.1 and a direct Rust column loop:

```sh
cargo test --manifest-path examples/ecs/compare/Cargo.toml
cargo run --release --manifest-path examples/ecs/compare/Cargo.toml -- 64 10
# Larger native-only smoke measurement:
cargo run --release --manifest-path examples/ecs/compare/Cargo.toml -- 100000 100
```

Both must produce the same checksum as Weft for `64 10`: **12768**. Their unit test
checks empty, single-entity, odd-sized, and even-sized worlds, with zero, one, and
ten ticks. The expected checksum is computed independently:

`3*n*(n-1)/2 + 100*n - ticks*n + 3*ticks*ceil(n/2)`.

The Rust column control has the same component column layout and update order as
the Weft hot loop. It does not implement the handle allocator or command queue.
The Bevy control uses a single-threaded schedule with movement followed by damage.
Setup and schedule initialization are outside the timer. Each program reports one
elapsed sample. Bevy's schedule and change-tracking work remain in its sample.
These are smoke measurements, not statistically controlled benchmarks.

Do not compare those native timings to the Weft interpreter as a language speed
result. Native Weft code generation is needed for that comparison. This first
workload checks semantic agreement and gives a reproducible starting point.

Next workloads should exercise component churn, cached queries over many
archetypes, and parallel scheduling. Keep storage policy, command visibility,
workload, and final state checks equivalent on both sides.

Sources:

- [Bevy queries and storage](https://docs.rs/bevy_ecs/latest/bevy_ecs/system/struct.Query.html)
- [Bevy deferred commands](https://docs.rs/bevy_ecs/latest/bevy_ecs/system/struct.Commands.html)
- [Weft place model](../../docs/adr/0003-place-model.md)
- [Weft modes and tasks](../../docs/adr/0006-modes-and-tasks.md)
