//! # B3. Inline layout: the model
//!
//! This file refines the base model with inline layout.
//!
//! * A type schema gives each type a size and a shape: a primitive (one data
//!   slot), a struct (inline fields at fixed offsets), or an enum (a tag slot
//!   at offset 0 and the payload of the active variant at offset 1). The
//!   `data` of each object has exactly the size of its type.
//! * A pointer is an allocation plus an inline path (`IPtr`). A path of
//!   `Field` steps names an inline field. A `Variant` step enters an enum
//!   payload. The step is valid only while the tag selects that variant.
//! * The schema gives each child-group label of a type the inline path that
//!   owns the kids (for example the `players` field of `World`) and the kid type.
//! * UB is a use after free, a type confusion (a path through a variant that
//!   is not active now), or an access outside the layout of the type (out of bounds).
//!
//! The checker uses Weft places: a root plus a path of steps. `Field` steps
//! are stable. `Variant` and `Kid` steps are unstable. A `mut(p)` kills a
//! reference at place `q` iff `q` is strictly inside `p` through at least one
//! unstable step (`lkills`). A mutable argument at an interior place `x.f`
//! has a footprint of the inline part `x.f` and the kids owned under `x.f` only.
//!
//! `layout_proof.rs` proves that checked programs have no UB.

use vstd::prelude::*;
use crate::model::*;

verus! {

// ---------------------------------------------------------------------------
// Types and layout
// ---------------------------------------------------------------------------

/// One step of a place.
pub enum PStep {
    /// An inline struct field. Stable.
    Field(nat),
    /// The payload of an inline enum variant. Unstable: a mutation can switch the variant.
    Variant(nat),
    /// A child group: heap data that a mutation can free. Unstable.
    Kid(Label),
}

/// The inline layout of a type.
pub enum Shape {
    /// One data slot.
    Prim,
    /// Field `f` has the type `fields[f].1` at the offset `fields[f].0`.
    Struct { fields: Seq<(nat, Ty)> },
    /// A tag slot at offset 0. The payload of variant `v` has the type `variants[v]` at offset 1.
    Enum { variants: Seq<Ty> },
}

/// A type: its size (the length of `data`), its shape, and its child groups.
/// `kids[l] = (owner, kid_ty)`: the kids with label `l` are owned under the
/// inline path `owner`, and have the type `kid_ty`.
pub struct TyDef {
    pub size: nat,
    pub shape: Shape,
    pub kids: Map<Label, (Seq<PStep>, Ty)>,
}

/// The type schema: the definition of each type.
pub type Schema = Map<Ty, TyDef>;

/// The schema is consistent: each field and each payload fits inside its
/// type, the fields of a struct do not overlap, and each enum has room for its tag.
pub open spec fn ty_ok(sc: Schema, t: Ty) -> bool {
    let d = sc[t];
    &&& match d.shape {
        Shape::Prim => d.size == 1,
        Shape::Struct { fields } => {
            &&& forall|f: int|
                0 <= f < fields.len() ==> sc.contains_key(#[trigger] fields[f].1) && fields[f].0
                    + sc[fields[f].1].size <= d.size
            &&& forall|f: int, g: int|
                0 <= f < fields.len() && 0 <= g < fields.len() && f != g ==> #[trigger] fields[f].0
                    + sc[fields[f].1].size <= #[trigger] fields[g].0 || fields[g].0 + sc[fields[g].1].size
                    <= fields[f].0
        },
        Shape::Enum { variants } => {
            &&& 1 <= d.size
            &&& forall|v: int|
                0 <= v < variants.len() ==> sc.contains_key(#[trigger] variants[v]) && 1 + sc[variants[v]].size
                    <= d.size
        },
    }
    &&& forall|l: Label| #[trigger] d.kids.contains_key(l) ==> sc.contains_key(d.kids[l].1)
}

/// Each type of the schema is consistent.
pub open spec fn wf_schema(sc: Schema) -> bool {
    forall|t: Ty| #[trigger] sc.contains_key(t) ==> ty_ok(sc, t)
}

/// One inline step from type `t` at offset `off` of `d`. A `Variant` step
/// reads the tag: it is valid only if the tag selects that variant.
pub open spec fn dstep(sc: Schema, t: Ty, d: Seq<int>, off: nat, st: PStep) -> Option<(Ty, nat)> {
    if !sc.contains_key(t) {
        None
    } else {
        match sc[t].shape {
            Shape::Struct { fields } => match st {
                PStep::Field(f) => if f < fields.len() {
                    Some((fields[f as int].1, off + fields[f as int].0))
                } else {
                    None
                },
                _ => None,
            },
            Shape::Enum { variants } => match st {
                PStep::Variant(v) => if v < variants.len() && off < d.len() && d[off as int] == v as int {
                    Some((variants[v as int], off + 1))
                } else {
                    None
                },
                _ => None,
            },
            Shape::Prim => None,
        }
    }
}

/// Follow the inline path `fp` from type `t` at offset `off` of `d`: the type
/// and the offset at its end. `None` if a step is outside the layout or goes
/// through a variant that is not active.
pub open spec fn view(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>) -> Option<(Ty, nat)>
    decreases fp.len(),
{
    if fp.len() == 0 {
        Some((t, off))
    } else {
        match dstep(sc, t, d, off, fp[0]) {
            Some(r) => view(sc, r.0, d, r.1, fp.drop_first()),
            None => None,
        }
    }
}

/// One step of the static type: like `dstep`, but with no tag check.
pub open spec fn sstep(sc: Schema, t: Ty, st: PStep) -> Option<Ty> {
    if !sc.contains_key(t) {
        None
    } else {
        match sc[t].shape {
            Shape::Struct { fields } => match st {
                PStep::Field(f) => if f < fields.len() {
                    Some(fields[f as int].1)
                } else {
                    None
                },
                _ => None,
            },
            Shape::Enum { variants } => match st {
                PStep::Variant(v) => if v < variants.len() {
                    Some(variants[v as int])
                } else {
                    None
                },
                _ => None,
            },
            Shape::Prim => None,
        }
    }
}

/// The static type at the end of the inline path `fp` from type `t`.
pub open spec fn sview(sc: Schema, t: Ty, fp: Seq<PStep>) -> Option<Ty>
    decreases fp.len(),
{
    if fp.len() == 0 {
        Some(t)
    } else {
        match sstep(sc, t, fp[0]) {
            Some(t1) => sview(sc, t1, fp.drop_first()),
            None => None,
        }
    }
}

/// The path has only `Field` steps.
pub open spec fn field_only(fp: Seq<PStep>) -> bool {
    forall|j: int| 0 <= j < fp.len() ==> #[trigger] fp[j] is Field
}

/// The kids with label `l` of type `t` are owned under the inline path `fp`.
pub open spec fn owned_under(sc: Schema, t: Ty, l: Label, fp: Seq<PStep>) -> bool {
    &&& sc.contains_key(t)
    &&& sc[t].kids.contains_key(l)
    &&& fp.is_prefix_of(sc[t].kids[l].0)
}

// ---------------------------------------------------------------------------
// Dynamic state
// ---------------------------------------------------------------------------

/// An interior pointer: an allocation (address, stamp, type) and an inline path.
pub struct IPtr {
    pub addr: Addr,
    pub stamp: Stamp,
    pub ty: Ty,
    pub fp: Seq<PStep>,
}

/// The run-time state of the layout model: like `DState`, with interior pointers and no closures.
pub struct LState {
    pub heap: Heap,
    pub locals: Map<Local, Addr>,
    pub vars: Map<Var, IPtr>,
    pub next_stamp: Stamp,
}

/// The ownership forest of the base model (`wf`).
pub open spec fn heap_wf(h: Heap, locals: Map<Local, Addr>, n: Stamp) -> bool {
    wf(DState { heap: h, locals, vars: Map::empty(), clos: Map::empty(), next_stamp: n })
}

/// Each object has the layout of its type, and each kid has the kid type of its label.
pub open spec fn layout_wf(sc: Schema, h: Heap) -> bool {
    forall|a: Addr|
        #[trigger] h.contains_key(a) ==> {
            &&& sc.contains_key(h[a].ty)
            &&& h[a].data.len() == sc[h[a].ty].size
            &&& forall|i: int|
                0 <= i < h[a].kids.len() ==> sc[h[a].ty].kids.contains_key(#[trigger] h[a].kids[i].0)
                    && h[h[a].kids[i].1].ty == sc[h[a].ty].kids[h[a].kids[i].0].1
        }
}

/// The heap is an ownership forest, and each object has the layout of its type.
pub open spec fn lwf(sc: Schema, s: LState) -> bool {
    heap_wf(s.heap, s.locals, s.next_stamp) && layout_wf(sc, s.heap)
}

/// A pointer to the whole allocation at `a`.
pub open spec fn lptr_to(h: Heap, a: Addr) -> IPtr {
    IPtr { addr: a, stamp: h[a].stamp, ty: h[a].ty, fp: Seq::empty() }
}

/// The type and the offset that pointer `p` designates now.
pub open spec fn view_of(sc: Schema, s: LState, p: IPtr) -> Option<(Ty, nat)> {
    view(sc, p.ty, s.heap[p.addr].data, 0, p.fp)
}

/// The pointer designates the live allocation it was made for, and its
/// inline path is valid in the current data (no type confusion).
pub open spec fn ilive(sc: Schema, s: LState, p: IPtr) -> bool {
    &&& s.heap.contains_key(p.addr)
    &&& s.heap[p.addr].stamp == p.stamp
    &&& s.heap[p.addr].ty == p.ty
    &&& view_of(sc, s, p) is Some
}

/// Variable `v` holds no valid pointer.
pub open spec fn ldangling(sc: Schema, s: LState, v: Var) -> bool {
    !s.vars.contains_key(v) || !ilive(sc, s, s.vars[v])
}

/// The data slot that `path` names from the target of `p`, if it is a
/// primitive inside the object's data.
pub open spec fn slot(sc: Schema, s: LState, p: IPtr, path: Seq<PStep>) -> Option<nat> {
    match view(sc, p.ty, s.heap[p.addr].data, 0, p.fp + path) {
        Some(r) => if sc.contains_key(r.0) && sc[r.0].shape is Prim && r.1 < s.heap[p.addr].data.len() {
            Some(r.1)
        } else {
            None
        },
        None => None,
    }
}

/// The target of `p` is an enum, and `v` is one of its variants.
pub open spec fn variant_ok(sc: Schema, s: LState, p: IPtr, v: nat) -> bool {
    match view_of(sc, s, p) {
        Some(r) => sstep(sc, r.0, PStep::Variant(v)) is Some,
        None => false,
    }
}

// ---------------------------------------------------------------------------
// Programs
// ---------------------------------------------------------------------------

/// The instructions of the layout model.
pub enum LInstr {
    /// `dst = &x`
    Borrow { dst: Var, x: Local },
    /// `dst = &src.f`: an interior pointer to an inline field
    Field { dst: Var, src: Var, f: nat },
    /// `if let V(..) = *src { dst = &payload }`: a safe abort if the tag is not `v`
    Variant { dst: Var, src: Var, v: nat },
    /// `dst = &src.label[i]` for a runtime-chosen `i`
    Child { dst: Var, src: Var, label: Label },
    /// `dst = src`
    Copy { dst: Var, src: Var },
    /// read the primitive at `src` plus the field path `path`
    Read { src: Var, path: Seq<PStep> },
    /// write the primitive at `src` plus the field path `path`
    Write { src: Var, path: Seq<PStep>, val: int },
    /// Call an arbitrary function with `args[k] = (var, is_mut)`.
    Call { args: Seq<(Var, bool)> },
}

/// Undefined behaviour: a use after free, a type confusion, or an access
/// outside the layout of the type.
pub open spec fn lub(sc: Schema, s: LState, i: LInstr) -> bool {
    match i {
        LInstr::Borrow { .. } => false,
        LInstr::Copy { .. } => false,
        LInstr::Field { src, f, .. } => ldangling(sc, s, src) || view_of(
            sc,
            s,
            IPtr { fp: s.vars[src].fp.push(PStep::Field(f)), ..s.vars[src] },
        ) is None,
        LInstr::Variant { src, v, .. } => ldangling(sc, s, src) || !variant_ok(sc, s, s.vars[src], v),
        LInstr::Child { src, .. } => ldangling(sc, s, src),
        LInstr::Read { src, path } => ldangling(sc, s, src) || slot(sc, s, s.vars[src], path) is None,
        LInstr::Write { src, path, .. } => ldangling(sc, s, src) || slot(sc, s, s.vars[src], path) is None,
        LInstr::Call { args } => exists|k: int| 0 <= k < args.len() && #[trigger] ldangling(sc, s, args[k].0),
    }
}

/// The pointers that a call passes, with their modes.
pub open spec fn lptrs(s: LState, args: Seq<(Var, bool)>) -> Seq<(IPtr, bool)> {
    Seq::new(args.len(), |k: int| (s.vars[args[k].0], args[k].1))
}

/// `c` is a strict descendant of `m` through a kid that is owned under the
/// inline path `fp` of `m`.
pub open spec fn fbelow(sc: Schema, h: Heap, m: Addr, fp: Seq<PStep>, c: Addr) -> bool {
    exists|r: Route| r.len() > 0 && #[trigger] resolve(h, m, r) == Some(c) && owned_under(sc, h[m].ty, r[0].0, fp)
}

/// The callee can free `c`: it is below a mutable argument, through a kid
/// that the argument owns.
pub open spec fn full_fp(sc: Schema, h: Heap, ps: Seq<(IPtr, bool)>, c: Addr) -> bool {
    exists|k: int| 0 <= k < ps.len() && ps[k].1 && #[trigger] fbelow(sc, h, ps[k].0.addr, ps[k].0.fp, c)
}

/// Some mutable argument points into `a`.
pub open spec fn mut_target(ps: Seq<(IPtr, bool)>, a: Addr) -> bool {
    exists|k: int| 0 <= k < ps.len() && ps[k].1 && #[trigger] ps[k].0.addr == a
}

/// Slot `j` of `o` is inside the inline region of `fp`.
pub open spec fn in_region(sc: Schema, o: Obj, fp: Seq<PStep>, j: int) -> bool {
    match view(sc, o.ty, o.data, 0, fp) {
        Some(r) => r.1 <= j < r.1 + sc[r.0].size,
        None => false,
    }
}

/// Slot `j` of allocation `a` is inside the inline region of a mutable argument.
pub open spec fn in_mut_region(sc: Schema, h: Heap, ps: Seq<(IPtr, bool)>, a: Addr, j: int) -> bool {
    exists|k: int| 0 <= k < ps.len() && ps[k].1 && ps[k].0.addr == a && #[trigger] in_region(sc, h[a], ps[k].0.fp, j)
}

/// The kids with label `l` of allocation `a` are owned by a mutable argument.
pub open spec fn kid_mut(sc: Schema, h: Heap, ps: Seq<(IPtr, bool)>, a: Addr, l: Label) -> bool {
    exists|k: int| 0 <= k < ps.len() && ps[k].1 && ps[k].0.addr == a && #[trigger] owned_under(sc, h[a].ty, l, ps[k].0.fp)
}

/// What an arbitrary callee may do to the heap. The footprint of a mutable
/// argument at `(a, fp)` is the inline region of `fp` in `a`, the kids of
/// `a` owned under `fp`, and everything below those kids. The callee may
/// switch enum variants inside the region. Kids of other fields keep their
/// positions.
pub open spec fn lcallee_effect(sc: Schema, s: LState, ps: Seq<(IPtr, bool)>, h2: Heap, n2: Stamp) -> bool {
    let h = s.heap;
    &&& lwf(sc, LState { heap: h2, next_stamp: n2, ..s })
    &&& n2 >= s.next_stamp
    // frame: outside the footprint nothing changes
    &&& forall|a: Addr|
        #[trigger] h.contains_key(a) && !full_fp(sc, h, ps, a) && !mut_target(ps, a) ==> h2.contains_key(a)
            && h2[a] == h[a]
    // an argument object: same allocation, and only its owned parts change
    &&& forall|a: Addr|
        #[trigger] h.contains_key(a) && !full_fp(sc, h, ps, a) && mut_target(ps, a) ==> {
            &&& h2.contains_key(a)
            &&& h2[a].stamp == h[a].stamp
            &&& h2[a].ty == h[a].ty
            &&& forall|j: int|
                0 <= j < h[a].data.len() && !in_mut_region(sc, h, ps, a, j) ==> #[trigger] h2[a].data[j]
                    == h[a].data[j]
            &&& forall|i: int|
                0 <= i < h[a].kids.len() && !kid_mut(sc, h, ps, a, h[a].kids[i].0) ==> i < h2[a].kids.len()
                    && #[trigger] h2[a].kids[i] == h[a].kids[i]
        }
    // stamp honesty: an object is either the same allocation as before, or fresh
    &&& forall|a: Addr|
        #[trigger] h2.contains_key(a) ==> h2[a].stamp >= s.next_stamp || (h.contains_key(a) && h[a].stamp
            == h2[a].stamp && h[a].ty == h2[a].ty)
}

/// One (non-UB) step.
pub open spec fn lstep(sc: Schema, s: LState, i: LInstr, s2: LState) -> bool {
    match i {
        LInstr::Borrow { dst, x } => s.locals.contains_key(x) && s2 == LState {
            vars: s.vars.insert(dst, lptr_to(s.heap, s.locals[x])),
            ..s
        },
        LInstr::Field { dst, src, f } => {
            let q = IPtr { fp: s.vars[src].fp.push(PStep::Field(f)), ..s.vars[src] };
            !ldangling(sc, s, src) && view_of(sc, s, q) is Some && s2 == LState { vars: s.vars.insert(dst, q), ..s }
        },
        LInstr::Variant { dst, src, v } => {
            let q = IPtr { fp: s.vars[src].fp.push(PStep::Variant(v)), ..s.vars[src] };
            !ldangling(sc, s, src) && view_of(sc, s, q) is Some && s2 == LState { vars: s.vars.insert(dst, q), ..s }
        },
        LInstr::Child { dst, src, label } => !ldangling(sc, s, src) && exists|idx: nat|
            {
                let res = #[trigger] kid_at(s.heap, s.vars[src].addr, (label, idx));
                res is Some && s2 == LState { vars: s.vars.insert(dst, lptr_to(s.heap, res->0)), ..s }
            },
        LInstr::Copy { dst, src } => s2 == LState {
            vars: if s.vars.contains_key(src) {
                s.vars.insert(dst, s.vars[src])
            } else {
                s.vars.remove(dst)
            },
            ..s
        },
        LInstr::Read { src, path } => !ldangling(sc, s, src) && slot(sc, s, s.vars[src], path) is Some && s2 == s,
        LInstr::Write { src, path, val } => {
            let p = s.vars[src];
            let o = s.heap[p.addr];
            let j = slot(sc, s, p, path);
            !ldangling(sc, s, src) && j is Some && s2 == LState {
                heap: s.heap.insert(p.addr, Obj { data: o.data.update(j->0 as int, val), ..o }),
                ..s
            }
        },
        LInstr::Call { args } => (forall|k: int| 0 <= k < args.len() ==> !#[trigger] ldangling(sc, s, args[k].0))
            && exists|h2: Heap, n2: Stamp|
            #[trigger] lcallee_effect(sc, s, lptrs(s, args), h2, n2) && s2 == LState { heap: h2, next_stamp: n2, ..s },
    }
}

// ---------------------------------------------------------------------------
// Static checker (Weft places)
// ---------------------------------------------------------------------------

/// A place in structured form: a root, the hops through child groups (each
/// hop: the inline path that owns the kid, and the label), and an inline tail.
pub struct LPlace {
    pub root: Local,
    pub hops: Seq<(Seq<PStep>, Label)>,
    pub tail: Seq<PStep>,
}

/// The steps of the hops, as one flat path.
pub open spec fn flat_hops(hops: Seq<(Seq<PStep>, Label)>) -> Seq<PStep>
    decreases hops.len(),
{
    if hops.len() == 0 {
        Seq::empty()
    } else {
        flat_hops(hops.drop_last()) + hops.last().0 + seq![PStep::Kid(hops.last().1)]
    }
}

/// The Weft place path: a flat sequence of steps from the root.
pub open spec fn flat(p: LPlace) -> Seq<PStep> {
    flat_hops(p.hops) + p.tail
}

/// A step that a mutation can invalidate: an enum payload or a child group.
pub open spec fn unstable(st: PStep) -> bool {
    !(st is Field)
}

/// **The Weft rule.** `mut(p)` kills a reference at place `q` iff `q` is
/// strictly inside `p` through at least one unstable step.
pub open spec fn lkills(p: LPlace, q: LPlace) -> bool {
    &&& p.root == q.root
    &&& flat(p).is_prefix_of(flat(q))
    &&& exists|j: int| flat(p).len() <= j < flat(q).len() && #[trigger] unstable(flat(q)[j])
}

/// The checker state of the layout model: the locals, their types, and the place of each valid reference.
pub struct LSState {
    pub locals: Set<Local>,
    /// The type of each local.
    pub lty: Map<Local, Ty>,
    pub vars: Map<Var, LPlace>,
}

/// The child-group labels of the hops.
pub open spec fn hop_labels(hops: Seq<(Seq<PStep>, Label)>) -> Seq<Label> {
    Seq::new(hops.len(), |i: int| hops[i].1)
}

/// The static type of the allocation at the end of the hops from a root of type `t0`.
/// Each hop must go through the inline path that owns its label.
pub open spec fn alloc_ty(sc: Schema, t0: Ty, hops: Seq<(Seq<PStep>, Label)>) -> Option<Ty>
    decreases hops.len(),
{
    if hops.len() == 0 {
        Some(t0)
    } else {
        match alloc_ty(sc, t0, hops.drop_last()) {
            Some(t) => if sc.contains_key(t) && sc[t].kids.contains_key(hops.last().1) && sc[t].kids[hops.last().1].0
                == hops.last().0 {
                Some(sc[t].kids[hops.last().1].1)
            } else {
                None
            },
            None => None,
        }
    }
}

/// The static type of the allocation that place `p` is in.
pub open spec fn place_alloc_ty(sc: Schema, ss: LSState, p: LPlace) -> Option<Ty> {
    alloc_ty(sc, ss.lty[p.root], p.hops)
}

/// The static type of place `p`.
pub open spec fn place_ty(sc: Schema, ss: LSState, p: LPlace) -> Option<Ty> {
    match place_alloc_ty(sc, ss, p) {
        Some(t) => sview(sc, t, p.tail),
        None => None,
    }
}

/// The static type at `p` plus `path` is a primitive, through fields only.
pub open spec fn prim_at(sc: Schema, ss: LSState, p: LPlace, path: Seq<PStep>) -> bool {
    &&& field_only(path)
    &&& match place_ty(sc, ss, p) {
        Some(t) => match sview(sc, t, path) {
            Some(t2) => sc.contains_key(t2) && sc[t2].shape is Prim,
            None => false,
        },
        None => false,
    }
}

/// The static type at `p` has the inline step `st`.
pub open spec fn step_ok(sc: Schema, ss: LSState, p: LPlace, st: PStep) -> bool {
    match place_ty(sc, ss, p) {
        Some(t) => sstep(sc, t, st) is Some,
        None => false,
    }
}

/// A call with the arguments `args` kills the reference at place `q`.
pub open spec fn lkilled(ss: LSState, args: Seq<(Var, bool)>, q: LPlace) -> bool {
    exists|k: int| 0 <= k < args.len() && args[k].1 && #[trigger] lkills(ss.vars[args[k].0], q)
}

/// The reference variables that survive a call.
pub open spec fn lsurvivors(ss: LSState, args: Seq<(Var, bool)>) -> Map<Var, LPlace> {
    Map::new(ss.vars.dom().filter(|v: Var| !lkilled(ss, args, ss.vars[v])), |v: Var| ss.vars[v])
}

/// The checker accepts instruction `i` in state `ss`.
pub open spec fn linstr_ok(sc: Schema, ss: LSState, i: LInstr) -> bool {
    match i {
        LInstr::Borrow { x, .. } => ss.locals.contains(x),
        LInstr::Field { src, f, .. } => ss.vars.contains_key(src) && step_ok(sc, ss, ss.vars[src], PStep::Field(f)),
        LInstr::Variant { src, v, .. } => ss.vars.contains_key(src) && step_ok(sc, ss, ss.vars[src], PStep::Variant(v)),
        LInstr::Child { src, label, .. } => ss.vars.contains_key(src) && match place_alloc_ty(sc, ss, ss.vars[src]) {
            Some(t) => sc.contains_key(t) && sc[t].kids.contains_key(label) && sc[t].kids[label].0 == ss.vars[src].tail,
            None => false,
        },
        LInstr::Copy { .. } => true,
        LInstr::Read { src, path } => ss.vars.contains_key(src) && prim_at(sc, ss, ss.vars[src], path),
        LInstr::Write { src, path, .. } => ss.vars.contains_key(src) && prim_at(sc, ss, ss.vars[src], path),
        LInstr::Call { args } => forall|k: int| 0 <= k < args.len() ==> ss.vars.contains_key(#[trigger] args[k].0),
    }
}

/// The checker state after instruction `i`.
pub open spec fn lpost(ss: LSState, i: LInstr) -> LSState {
    match i {
        LInstr::Borrow { dst, x } => LSState {
            vars: ss.vars.insert(dst, LPlace { root: x, hops: Seq::empty(), tail: Seq::empty() }),
            ..ss
        },
        LInstr::Field { dst, src, f } => LSState {
            vars: ss.vars.insert(dst, LPlace { tail: ss.vars[src].tail.push(PStep::Field(f)), ..ss.vars[src] }),
            ..ss
        },
        LInstr::Variant { dst, src, v } => LSState {
            vars: ss.vars.insert(dst, LPlace { tail: ss.vars[src].tail.push(PStep::Variant(v)), ..ss.vars[src] }),
            ..ss
        },
        LInstr::Child { dst, src, label } => LSState {
            vars: ss.vars.insert(
                dst,
                LPlace {
                    root: ss.vars[src].root,
                    hops: ss.vars[src].hops.push((ss.vars[src].tail, label)),
                    tail: Seq::empty(),
                },
            ),
            ..ss
        },
        LInstr::Copy { dst, src } => LSState {
            vars: if ss.vars.contains_key(src) {
                ss.vars.insert(dst, ss.vars[src])
            } else {
                ss.vars.remove(dst)
            },
            ..ss
        },
        LInstr::Read { .. } => ss,
        LInstr::Write { .. } => ss,
        LInstr::Call { args } => LSState { vars: lsurvivors(ss, args), ..ss },
    }
}

/// Checker state before instruction `k`.
pub open spec fn lss_at(ss0: LSState, prog: Seq<LInstr>, k: nat) -> LSState
    decreases k,
{
    if k == 0 {
        ss0
    } else {
        lpost(lss_at(ss0, prog, (k - 1) as nat), prog[k - 1])
    }
}

/// The checker accepts each instruction of `prog`.
pub open spec fn lcheck(sc: Schema, ss0: LSState, prog: Seq<LInstr>) -> bool {
    forall|k: nat| k < prog.len() ==> #[trigger] linstr_ok(sc, lss_at(ss0, prog, k), prog[k as int])
}

/// A trace of `prog` from `trace[0]`.
pub open spec fn is_ltrace(sc: Schema, prog: Seq<LInstr>, trace: Seq<LState>) -> bool {
    &&& 1 <= trace.len() <= prog.len() + 1
    &&& forall|k: int| 0 <= k < trace.len() - 1 ==> lstep(sc, #[trigger] trace[k], prog[k], trace[k + 1])
}

/// The checker state at the start: the locals and their types, no references.
pub open spec fn linitial(s0: LState) -> LSState {
    LSState {
        locals: s0.locals.dom(),
        lty: Map::new(s0.locals.dom(), |x: Local| s0.heap[s0.locals[x]].ty),
        vars: Map::empty(),
    }
}

} // verus!
