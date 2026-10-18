# ADR 0011: Abstract places (proposal, open problem)

Status: proposed. Date: 2026-10-18.

## Context

The design lists an open problem: places expose field names in public signatures.
`fn tick(w: &World) / mut(w.entities[])` tells every caller that `World` has a field
`entities`. Phase 1 has no field privacy, so the problem does not break anything yet.

## Proposal

- A type exports named places: `struct World { entities: Vec<Entity>, place units = entities[] }`.
- A signature outside the module can name only exported places: `mut(w.units)`.
- Inside the module, `w.units` is the same place as `w.entities[]`.
- Outside the module, `w.units` is an opaque step. Two exported places of one type are
  disjoint unless the type declares that one contains the other. The defining module
  proves the declaration with the place algebra (`within` and `overlaps`).
- The stability of an opaque step is the stability of its last real step, so rule 3
  stays the same.

## Why not now

Field privacy does not exist in Phase 1. Without it, an abstract place only hides a name
in a diagnostic. We do this work together with module privacy.
