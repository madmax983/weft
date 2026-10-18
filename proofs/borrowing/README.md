> Origin: this proof starts from
> [madmax983/group-borrowing-soundness](https://github.com/madmax983/group-borrowing-soundness)
> at commit `5dd0de3b4af29a28f1afc50c6d4ee15bbe8d0525` (Apache-2.0). Weft extends it. See `../README.md` for the extension list.

# Group Borrowing: soundness, machine-checked in Verus

A formal model of **group borrowing** (Nick Smith's proposal, written up at
<https://verdagon.dev/blog/group-borrowing>) with a [Verus](https://github.com/verus-lang/verus)
proof that the borrow checker rules out dangling-reference dereferences.

```
verification results:: 33 verified, 0 errors     (~2 s)
```

No `assume`, `admit`, `external_body` or extra axioms.

## The rules being verified

* Every reference has a **group**: a local plus a path of child-group labels, e.g.
  `d`, `d.rings*`, `d.rings*.gems*`. A *child group* holds anything that can be
  destroyed independently of its parent: a `Box` target, list elements, a variant payload.
* Any number of references, **mutable or not, may alias** within a group.
* A possibly-mutating use (a call that takes a reference as `mut`) of a reference in group
  `G` **invalidates references into strict child groups of `G`, and nothing else**.
  References to `G` itself, to sibling groups and to ancestors stay valid.
* Writing an inline primitive field invalidates nothing.

## The theorem

`src/soundness.rs`:

```rust
pub proof fn soundness_from_start(prog: Seq<Instr>, trace: Seq<DState>)
    requires
        is_trace(prog, trace),                       // any execution: any indices, any callees
        wf(trace[0]),                                // any well-formed starting heap
        check(initial_sstate(trace[0]), prog),       // the group-borrowing checker accepts prog
    ensures
        forall|k: int| 0 <= k < trace.len() && k < prog.len() ==> !#[trigger] ub(trace[k], prog[k]),
```

`ub` means dereferencing a reference whose allocation is gone, or whose address now
holds a *different* allocation (addresses may be reused; allocation stamps act as
provenance) or a different type.

## The model (`src/model.rs`)

* **Heap:** allocations with a stamp, a type, inline `data`, and labelled owning
  `kids`. Ownership is a forest rooted at the locals (`wf`).
* **Instructions:** `Borrow` (`&x`), `Child` (`&src.label[i]` with a runtime-chosen
  `i`), `Copy`, `Read`, `Write` (an inline field), and `Call`.
* **Calls are arbitrary.** A call passes a list of `(ref, is_mut)` arguments, which may
  alias, may come from different groups, and may sit at different depths. Its effect is
  *any* new heap that keeps the ownership forest well-formed and changes nothing outside
  what the mutable arguments own (`callee_effect`). Inside that footprint the callee may
  mutate, move, free and allocate as it likes, but it cannot destroy the argument
  objects themselves. A call can return a reference into a child group of one of its
  arguments.

## The proof idea

The invariant (`inv`) says that every reference the checker considers valid is live, and
can be reached from its group's root local by a route whose labels are exactly the
group's path. It rests on two facts:

1. **Unique routes.** Ownership is a forest, so each allocation has exactly one route from
   the roots (`lemma_resolve_unique`). Anything a callee could free is a strict
   descendant of some mutable argument, so it lies in a strict child group of that
   argument's group. Those are exactly the references the checker kills
   (`lemma_survivor_not_below`).
2. **Frame.** Every other reference's route avoids the callee's footprint, so both the
   route and the allocation survive the call (`lemma_route_preserved`).

## Sanity checks (`src/examples.rs`)

* **Checker accepts:** `d.damage(10)` followed by `d.hp` is accepted.
* **Checker rejects:** using `ring_ref` (in `d.rings*`) after `d.damage(10)` is rejected.
* **The rule is necessary:** there is a concrete execution of that rejected program where
  `damage` frees the ring and the final read is UB.
* **The theorem's hypotheses are satisfiable:** the accepted prefix of that same
  execution meets every hypothesis of `soundness_from_start`.
* **Mutable aliasing** (`attack(entities[i], entities[j])` with two `mut` references
  that may alias) is accepted. Rust rejects this.
* **Sibling child groups:** `power_up_ring(d, mut d.rings[0])` keeps `armor_ref` (in
  `d.armor*`) valid.

Mutation test: weakening the rule so that only grandchild groups are invalidated makes
the soundness proof fail.

## Scope and limitations

* **No stored references.** References are second-class: they live in reference
  variables and are never stored in the heap. This is the "no back channels" assumption
  that makes `callee_effect`'s frame justified. Storing references in objects would need
  the proposal's isolation rules.
* **Abstract callee bodies.** A callee's own body is not checked. It is modelled by the
  most general effect allowed by its signature.
* **Straight-line programs.** Programs are straight-line with nondeterministic indices
  and callees. Branches and loops (a join of the checker states) are future work.
* **Single-threaded.**

## Running

```bash
./verify.sh          # needs `verus` on PATH
```

CI (`.github/workflows/verify.yml`) builds Verus at the revision pinned in
`VERUS_VERSION` and runs `./verify.sh`.
