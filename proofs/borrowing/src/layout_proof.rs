//! # B3. Inline layout: soundness
//!
//! Main theorem (`layout_soundness`): if the checker accepts a program, then
//! no execution of it has UB: no use after free, no type confusion, and no
//! access outside the layout of a type.
//!
//! The proof follows the base proof. Two new facts carry it:
//!   * **Inline frame** (`lemma_reads_in_region`): a valid inline path reads
//!     a tag slot inside the region of another valid path `fp` only if it
//!     extends `fp` through a `Variant` step. So a mutation of `fp` keeps
//!     every reference that the Weft rule keeps.
//!   * **Field-sensitive kids** (`lemma_not_full_fp`): by unique routes, an
//!     allocation that a mutable argument at `x.f` can free sits behind a
//!     kid that `x.f` owns, so its place is `x.f ... Kid ...`, which the
//!     Weft rule kills.

use vstd::prelude::*;
use crate::model::*;
use crate::soundness::*;
use crate::layout::*;

verus! {

// ---------------------------------------------------------------------------
// Inline paths
// ---------------------------------------------------------------------------

/// The type at the end of a valid inline path.
pub open spec fn vty(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>) -> Ty {
    (view(sc, t, d, off, fp)->0).0
}

/// The offset at the end of a valid inline path.
pub open spec fn voff(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>) -> nat {
    (view(sc, t, d, off, fp)->0).1
}

/// The inline path `fp` reads the tag at slot `j` of `d` (it has a `Variant`
/// step there).
pub open spec fn reads(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>, j: int) -> bool
    decreases fp.len(),
{
    if fp.len() == 0 {
        false
    } else {
        ||| (fp[0] is Variant && j == off)
        ||| match dstep(sc, t, d, off, fp[0]) {
            Some(r) => reads(sc, r.0, d, r.1, fp.drop_first(), j),
            None => false,
        }
    }
}

/// The view of a concatenation follows the first path, then the second.
pub proof fn lemma_view_concat(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp1: Seq<PStep>, fp2: Seq<PStep>)
    ensures
        view(sc, t, d, off, fp1 + fp2) == match view(sc, t, d, off, fp1) {
            Some(r) => view(sc, r.0, d, r.1, fp2),
            None => None,
        },
    decreases fp1.len(),
{
    if fp1.len() == 0 {
        assert(fp1 + fp2 =~= fp2);
    } else {
        assert((fp1 + fp2)[0] == fp1[0]);
        assert((fp1 + fp2).drop_first() =~= fp1.drop_first() + fp2);
        match dstep(sc, t, d, off, fp1[0]) {
            Some(r) => lemma_view_concat(sc, r.0, d, r.1, fp1.drop_first(), fp2),
            None => {},
        }
    }
}

/// The view of a path plus one step.
pub proof fn lemma_view_push(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>, st: PStep)
    ensures
        view(sc, t, d, off, fp.push(st)) == match view(sc, t, d, off, fp) {
            Some(r) => dstep(sc, r.0, d, r.1, st),
            None => None,
        },
{
    assert(fp.push(st) =~= fp + seq![st]);
    lemma_view_concat(sc, t, d, off, fp, seq![st]);
    match view(sc, t, d, off, fp) {
        Some(r) => {
            assert(seq![st][0] == st);
            assert(seq![st].drop_first() =~= Seq::<PStep>::empty());
            match dstep(sc, r.0, d, r.1, st) {
                Some(r2) => {
                    assert(view(sc, r2.0, d, r2.1, seq![st].drop_first()) == Some((r2.0, r2.1)));
                },
                None => {},
            }
        },
        None => {},
    }
}

/// A valid inline path stays inside the region of its start type.
pub proof fn lemma_view_region(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>)
    requires
        wf_schema(sc),
        sc.contains_key(t),
        view(sc, t, d, off, fp) is Some,
    ensures
        sc.contains_key(vty(sc, t, d, off, fp)),
        off <= voff(sc, t, d, off, fp),
        voff(sc, t, d, off, fp) + sc[vty(sc, t, d, off, fp)].size <= off + sc[t].size,
        fp.len() > 0 && fp[0] is Variant ==> off + 1 <= voff(sc, t, d, off, fp),
    decreases fp.len(),
{
    if fp.len() > 0 {
        let r = dstep(sc, t, d, off, fp[0])->0;
        assert(ty_ok(sc, t));
        match sc[t].shape {
            Shape::Struct { fields } => {
                let f = fp[0]->Field_0 as int;
                assert(fields[f].1 == r.0);
            },
            Shape::Enum { variants } => {
                let v = fp[0]->Variant_0 as int;
                assert(variants[v] == r.0);
            },
            Shape::Prim => {},
        }
        lemma_view_region(sc, r.0, d, r.1, fp.drop_first());
    }
}

/// A path that reads a tag reads it inside the region of its start type.
pub proof fn lemma_reads_region(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>, j: int)
    requires
        wf_schema(sc),
        sc.contains_key(t),
        view(sc, t, d, off, fp) is Some,
        reads(sc, t, d, off, fp, j),
    ensures
        off <= j < off + sc[t].size,
    decreases fp.len(),
{
    let r = dstep(sc, t, d, off, fp[0])->0;
    assert(ty_ok(sc, t));
    match sc[t].shape {
        Shape::Struct { fields } => {
            let f = fp[0]->Field_0 as int;
            assert(fields[f].1 == r.0);
        },
        Shape::Enum { variants } => {
            let v = fp[0]->Variant_0 as int;
            assert(variants[v] == r.0);
        },
        Shape::Prim => {},
    }
    if !(fp[0] is Variant && j == off) {
        lemma_reads_region(sc, r.0, d, r.1, fp.drop_first(), j);
    }
}

/// A path that reads a tag has a `Variant` step.
pub proof fn lemma_reads_variant(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>, j: int)
    requires
        reads(sc, t, d, off, fp, j),
    ensures
        exists|i: int| 0 <= i < fp.len() && #[trigger] fp[i] is Variant,
    decreases fp.len(),
{
    if fp[0] is Variant {
        assert(fp[0] is Variant);
    } else {
        let r = dstep(sc, t, d, off, fp[0])->0;
        lemma_reads_variant(sc, r.0, d, r.1, fp.drop_first(), j);
        let i = choose|i: int| 0 <= i < fp.drop_first().len() && #[trigger] fp.drop_first()[i] is Variant;
        assert(fp[i + 1] is Variant);
    }
}

/// A path reads the same view from data that agrees on the tags it reads.
pub proof fn lemma_view_agree(sc: Schema, t: Ty, d: Seq<int>, d2: Seq<int>, off: nat, fp: Seq<PStep>)
    requires
        d2.len() == d.len(),
        forall|j: int| #[trigger] reads(sc, t, d, off, fp, j) ==> d2[j] == d[j],
    ensures
        view(sc, t, d2, off, fp) == view(sc, t, d, off, fp),
    decreases fp.len(),
{
    if fp.len() > 0 {
        if fp[0] is Variant {
            assert(reads(sc, t, d, off, fp, off as int));
        }
        assert(dstep(sc, t, d2, off, fp[0]) == dstep(sc, t, d, off, fp[0]));
        match dstep(sc, t, d, off, fp[0]) {
            Some(r) => {
                assert forall|j: int| #[trigger] reads(sc, r.0, d, r.1, fp.drop_first(), j) implies d2[j] == d[j] by {
                    assert(reads(sc, t, d, off, fp, j));
                }
                lemma_view_agree(sc, r.0, d, d2, r.1, fp.drop_first());
            },
            None => {},
        }
    }
}

/// **Inline frame.** If a valid path `q` reads a tag inside the region of
/// the valid path `fp`, then `q` extends `fp` through a `Variant` step.
pub proof fn lemma_reads_in_region(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>, q: Seq<PStep>, j: int)
    requires
        wf_schema(sc),
        sc.contains_key(t),
        view(sc, t, d, off, fp) is Some,
        view(sc, t, d, off, q) is Some,
        reads(sc, t, d, off, q, j),
        voff(sc, t, d, off, fp) <= j < voff(sc, t, d, off, fp) + sc[vty(sc, t, d, off, fp)].size,
    ensures
        fp.is_prefix_of(q),
        exists|i: int| fp.len() <= i < q.len() && #[trigger] q[i] is Variant,
    decreases fp.len(),
{
    if fp.len() == 0 {
        lemma_reads_variant(sc, t, d, off, q, j);
        assert(fp =~= q.subrange(0, 0));
    } else {
        let r = dstep(sc, t, d, off, fp[0])->0;
        let rq = dstep(sc, t, d, off, q[0])->0;
        assert(ty_ok(sc, t));
        lemma_view_region(sc, t, d, off, fp);
        if fp[0] == q[0] {
            if q[0] is Variant && j == off {
                assert(false);
            } else {
                lemma_reads_in_region(sc, r.0, d, r.1, fp.drop_first(), q.drop_first(), j);
                let i = choose|i: int|
                    fp.drop_first().len() <= i < q.drop_first().len() && #[trigger] q.drop_first()[i] is Variant;
                assert(q[i + 1] is Variant);
                assert(fp =~= q.subrange(0, fp.len() as int)) by {
                    assert forall|k: int| 0 <= k < fp.len() implies fp[k] == q[k] by {
                        if k > 0 {
                            assert(fp[k] == fp.drop_first()[k - 1]);
                            assert(q[k] == q.drop_first()[k - 1]);
                        }
                    }
                }
            }
        } else {
            match sc[t].shape {
                Shape::Struct { fields } => {
                    let f = fp[0]->Field_0 as int;
                    let g = q[0]->Field_0 as int;
                    assert(f != g);
                    lemma_view_region(sc, r.0, d, r.1, fp.drop_first());
                    lemma_reads_region(sc, rq.0, d, rq.1, q.drop_first(), j);
                    assert(fields[f].0 + sc[fields[f].1].size <= fields[g].0 || fields[g].0 + sc[fields[g].1].size
                        <= fields[f].0);
                },
                Shape::Enum { variants } => {},
                Shape::Prim => {},
            }
        }
    }
}

/// A valid path's view gives its static type.
pub proof fn lemma_view_sview(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>)
    requires
        view(sc, t, d, off, fp) is Some,
    ensures
        sview(sc, t, fp) == Some(vty(sc, t, d, off, fp)),
    decreases fp.len(),
{
    if fp.len() > 0 {
        let r = dstep(sc, t, d, off, fp[0])->0;
        assert(sstep(sc, t, fp[0]) == Some(r.0));
        lemma_view_sview(sc, r.0, d, r.1, fp.drop_first());
    }
}

/// A path of fields only is valid in any data, if it is valid in the type.
pub proof fn lemma_field_only_view(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>)
    requires
        field_only(fp),
        sview(sc, t, fp) is Some,
    ensures
        view(sc, t, d, off, fp) is Some,
        vty(sc, t, d, off, fp) == sview(sc, t, fp)->0,
    decreases fp.len(),
{
    if fp.len() > 0 {
        assert(fp[0] is Field);
        let t1 = sstep(sc, t, fp[0])->0;
        let r = dstep(sc, t, d, off, fp[0])->0;
        assert(r.0 == t1);
        assert(field_only(fp.drop_first())) by {
            assert forall|j: int| 0 <= j < fp.drop_first().len() implies #[trigger] fp.drop_first()[j] is Field by {
                assert(fp[j + 1] is Field);
            }
        }
        lemma_field_only_view(sc, t1, d, r.1, fp.drop_first());
    }
}

/// No valid path goes on after a primitive.
pub proof fn lemma_prim_end(sc: Schema, t: Ty, d: Seq<int>, off: nat, fp: Seq<PStep>, ext: Seq<PStep>)
    requires
        view(sc, t, d, off, fp) is Some,
        sc.contains_key(vty(sc, t, d, off, fp)),
        sc[vty(sc, t, d, off, fp)].shape is Prim,
        ext.len() > 0,
    ensures
        view(sc, t, d, off, fp + ext) is None,
{
    lemma_view_concat(sc, t, d, off, fp, ext);
}

// ---------------------------------------------------------------------------
// Places
// ---------------------------------------------------------------------------

/// The flat path of the hops plus one hop.
pub proof fn lemma_flat_hops_push(hops: Seq<(Seq<PStep>, Label)>, hp: (Seq<PStep>, Label))
    ensures
        flat_hops(hops.push(hp)) == flat_hops(hops) + hp.0 + seq![PStep::Kid(hp.1)],
{
    assert(hops.push(hp).drop_last() =~= hops);
}

/// The flat path of a concatenation of hops.
pub proof fn lemma_flat_hops_concat(a: Seq<(Seq<PStep>, Label)>, b: Seq<(Seq<PStep>, Label)>)
    ensures
        flat_hops(a + b) == flat_hops(a) + flat_hops(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(flat_hops(a) + flat_hops(b) =~= flat_hops(a));
    } else {
        let bl = b.drop_last();
        lemma_flat_hops_concat(a, bl);
        assert((a + b).drop_last() =~= a + bl);
        assert((a + b).last() == b.last());
        assert(flat_hops(a + b) =~= flat_hops(a) + flat_hops(b));
    }
}

/// **Kid case of the Weft rule.** If `q` goes through the hops of `p`, then
/// through a kid that is owned under the tail of `p`, then `mut(p)` kills `q`.
pub proof fn lemma_kills_kid(p: LPlace, q: LPlace)
    requires
        p.root == q.root,
        p.hops.len() < q.hops.len(),
        q.hops.subrange(0, p.hops.len() as int) == p.hops,
        p.tail.is_prefix_of(q.hops[p.hops.len() as int].0),
    ensures
        lkills(p, q),
{
    let n = p.hops.len() as int;
    let hp = q.hops[n];
    let seg = hp.0;
    let e = seg.subrange(p.tail.len() as int, seg.len() as int);
    assert(seg =~= p.tail + e);
    let rest = q.hops.subrange(n + 1, q.hops.len() as int);
    assert(q.hops =~= p.hops.push(hp) + rest);
    lemma_flat_hops_concat(p.hops.push(hp), rest);
    lemma_flat_hops_push(p.hops, hp);
    let ext = e + seq![PStep::Kid(hp.1)] + flat_hops(rest) + q.tail;
    assert(flat(q) =~= flat(p) + ext);
    let j = (flat(p).len() + e.len()) as int;
    assert(flat(q)[j] == PStep::Kid(hp.1));
    assert(unstable(flat(q)[j]));
    assert(flat(p).is_prefix_of(flat(q))) by {
        assert(flat(p) =~= flat(q).subrange(0, flat(p).len() as int));
    }
}

/// **Variant case of the Weft rule.** If `q` has the hops of `p` and its tail
/// extends the tail of `p` through a `Variant` step, then `mut(p)` kills `q`.
pub proof fn lemma_kills_variant(p: LPlace, q: LPlace, i: int)
    requires
        p.root == q.root,
        p.hops == q.hops,
        p.tail.is_prefix_of(q.tail),
        p.tail.len() <= i < q.tail.len(),
        q.tail[i] is Variant,
    ensures
        lkills(p, q),
{
    let ext = q.tail.subrange(p.tail.len() as int, q.tail.len() as int);
    assert(q.tail =~= p.tail + ext);
    assert(flat(q) =~= flat(p) + ext);
    let j = flat_hops(p.hops).len() as int + i;
    assert(flat(q)[j] == q.tail[i]);
    assert(unstable(flat(q)[j]));
    assert(flat(p).is_prefix_of(flat(q))) by {
        assert(flat(p) =~= flat(q).subrange(0, flat(p).len() as int));
    }
}

/// A prefix of typed hops is typed.
pub proof fn lemma_alloc_ty_prefix(sc: Schema, t0: Ty, hops: Seq<(Seq<PStep>, Label)>, k: int)
    requires
        alloc_ty(sc, t0, hops) is Some,
        0 <= k <= hops.len(),
    ensures
        alloc_ty(sc, t0, hops.subrange(0, k)) is Some,
    decreases hops.len(),
{
    if k < hops.len() {
        lemma_alloc_ty_prefix(sc, t0, hops.drop_last(), k);
        assert(hops.drop_last().subrange(0, k) =~= hops.subrange(0, k));
    } else {
        assert(hops.subrange(0, k) =~= hops);
    }
}

/// Typed hops are fixed by their labels: each hop goes through the inline
/// path that owns its label.
pub proof fn lemma_hops_eq(sc: Schema, t0: Ty, h1: Seq<(Seq<PStep>, Label)>, h2: Seq<(Seq<PStep>, Label)>)
    requires
        alloc_ty(sc, t0, h1) is Some,
        alloc_ty(sc, t0, h2) is Some,
        hop_labels(h1) == hop_labels(h2),
    ensures
        h1 == h2,
    decreases h1.len(),
{
    assert(h1.len() == hop_labels(h1).len());
    assert(h2.len() == hop_labels(h2).len());
    if h1.len() > 0 {
        assert(hop_labels(h1.drop_last()) =~= hop_labels(h2.drop_last())) by {
            assert forall|i: int| 0 <= i < h1.len() - 1 implies hop_labels(h1.drop_last())[i] == hop_labels(h2.drop_last())[i] by {
                assert(hop_labels(h1)[i] == hop_labels(h2)[i]);
                assert(hop_labels(h1)[i] == h1[i].1);
                assert(hop_labels(h2)[i] == h2[i].1);
                assert(h1.drop_last()[i] == h1[i]);
                assert(h2.drop_last()[i] == h2[i]);
                assert(hop_labels(h1.drop_last())[i] == h1.drop_last()[i].1);
                assert(hop_labels(h2.drop_last())[i] == h2.drop_last()[i].1);
            }
        }
        lemma_hops_eq(sc, t0, h1.drop_last(), h2.drop_last());
        assert(hop_labels(h1)[h1.len() - 1] == hop_labels(h2)[h1.len() - 1]);
        assert(hop_labels(h1)[h1.len() - 1] == h1[h1.len() - 1].1);
        assert(hop_labels(h2)[h1.len() - 1] == h2[h1.len() - 1].1);
        assert(h1.last().1 == h2.last().1);
        let t = alloc_ty(sc, t0, h1.drop_last())->0;
        assert(h1.last().0 == sc[t].kids[h1.last().1].0);
        assert(h2.last().0 == sc[t].kids[h2.last().1].0);
        assert(h1.last() == h2.last());
        assert(h1 =~= h1.drop_last().push(h1.last()));
        assert(h2 =~= h2.drop_last().push(h2.last()));
    } else {
        assert(h1 =~= h2);
    }
}

// ---------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------

/// The facts of the base `wf`, stated for a heap and its locals.
pub proof fn lemma_heap_wf_facts(h: Heap, locals: Map<Local, Addr>, n: Stamp)
    requires
        heap_wf(h, locals, n),
    ensures
        forall|x: Local| #[trigger] locals.contains_key(x) ==> h.contains_key(locals[x]) && unowned(h, locals[x]),
        forall|x: Local, y: Local|
            locals.contains_key(x) && locals.contains_key(y) && #[trigger] locals[x] == #[trigger] locals[y] ==> x == y,
        forall|b: Addr, i: int| h.contains_key(b) && 0 <= i < h[b].kids.len() ==> h.contains_key(#[trigger] h[b].kids[i].1),
        unique_owners(h),
{
    let d = DState { heap: h, locals, vars: Map::empty(), clos: Map::empty(), next_stamp: n };
    assert(wf(d));
    assert(d.locals == locals && d.heap == h);
    assert forall|x: Local| #[trigger] locals.contains_key(x) implies h.contains_key(locals[x]) && unowned(h, locals[x]) by {
        assert(d.locals.contains_key(x));
    }
    assert forall|x: Local, y: Local|
        locals.contains_key(x) && locals.contains_key(y) && #[trigger] locals[x] == #[trigger] locals[y] implies x == y by {
        assert(d.locals.contains_key(x) && d.locals.contains_key(y) && d.locals[x] == d.locals[y]);
    }
    assert forall|b: Addr, i: int| h.contains_key(b) && 0 <= i < h[b].kids.len() implies h.contains_key(#[trigger] h[b].kids[i].1) by {
        assert(d.heap.contains_key(b));
    }
}

/// Pointer `p`, which the checker believes is valid at place `pl`, really
/// is: it is live with a valid inline path equal to the tail of `pl`, its
/// allocation has the static type of the hops, and a route with the hop
/// labels leads to it.
pub open spec fn lptr_ok(sc: Schema, s: LState, ss: LSState, pl: LPlace, p: IPtr) -> bool {
    &&& s.locals.contains_key(pl.root)
    &&& ilive(sc, s, p)
    &&& p.fp == pl.tail
    &&& alloc_ty(sc, ss.lty[pl.root], pl.hops) == Some(p.ty)
    &&& exists|r: Route|
        labels(r) == hop_labels(pl.hops) && #[trigger] resolve(s.heap, s.locals[pl.root], r) == Some(p.addr)
}

/// The invariant of the layout model.
pub open spec fn linv(sc: Schema, s: LState, ss: LSState) -> bool {
    &&& wf_schema(sc)
    &&& lwf(sc, s)
    &&& ss.locals == s.locals.dom()
    &&& forall|x: Local|
        #[trigger] s.locals.contains_key(x) ==> ss.lty.contains_key(x) && ss.lty[x] == s.heap[s.locals[x]].ty
    &&& forall|v: Var|
        #[trigger] ss.vars.contains_key(v) ==> s.vars.contains_key(v) && lptr_ok(sc, s, ss, ss.vars[v], s.vars[v])
}

proof fn lemma_lptr_transfer(sc: Schema, s: LState, s2: LState, ss: LSState, ss2: LSState, pl: LPlace, p: IPtr)
    requires
        lptr_ok(sc, s, ss, pl, p),
        s2.heap == s.heap,
        s2.locals == s.locals,
        ss2.lty == ss.lty,
    ensures
        lptr_ok(sc, s2, ss2, pl, p),
{
    let r = choose|r: Route|
        labels(r) == hop_labels(pl.hops) && #[trigger] resolve(s.heap, s.locals[pl.root], r) == Some(p.addr);
    assert(resolve(s2.heap, s2.locals[pl.root], r) == Some(p.addr));
}

/// After a step that only changes the variables, the other variables stay valid.
proof fn lemma_linv_vars(sc: Schema, s: LState, ss: LSState, s2: LState, ss2: LSState, dst: Var)
    requires
        linv(sc, s, ss),
        s2.heap == s.heap,
        s2.locals == s.locals,
        s2.next_stamp == s.next_stamp,
        ss2.locals == ss.locals,
        ss2.lty == ss.lty,
        forall|v: Var| v != dst && #[trigger] ss2.vars.contains_key(v) ==> ss.vars.contains_key(v) && ss2.vars[v] == ss.vars[v]
            && s2.vars.contains_key(v) && s2.vars[v] == s.vars[v],
        ss2.vars.contains_key(dst) ==> s2.vars.contains_key(dst) && lptr_ok(sc, s2, ss2, ss2.vars[dst], s2.vars[dst]),
    ensures
        linv(sc, s2, ss2),
{
    assert forall|v: Var| #[trigger] ss2.vars.contains_key(v) implies s2.vars.contains_key(v) && lptr_ok(sc, s2, ss2, ss2.vars[v], s2.vars[v]) by {
        if v != dst {
            lemma_lptr_transfer(sc, s, s2, ss, ss2, ss.vars[v], s.vars[v]);
        }
    }
}

// ---------------------------------------------------------------------------
// Calls
// ---------------------------------------------------------------------------

/// A root is never in the part a callee can free: roots have no owner.
pub proof fn lemma_root_not_full_fp(sc: Schema, s: LState, ps: Seq<(IPtr, bool)>, x: Local)
    requires
        heap_wf(s.heap, s.locals, s.next_stamp),
        s.locals.contains_key(x),
    ensures
        !full_fp(sc, s.heap, ps, s.locals[x]),
{
    let h = s.heap;
    let r0 = s.locals[x];
    lemma_heap_wf_facts(s.heap, s.locals, s.next_stamp);
    if full_fp(sc, h, ps, r0) {
        let k = choose|k: int| 0 <= k < ps.len() && ps[k].1 && #[trigger] fbelow(sc, h, ps[k].0.addr, ps[k].0.fp, r0);
        let m = ps[k].0.addr;
        let r = choose|r: Route| r.len() > 0 && #[trigger] resolve(h, m, r) == Some(r0) && owned_under(sc, h[m].ty, r[0].0, ps[k].0.fp);
        let b = lemma_resolve_owner(h, m, r, r0);
        assert(unowned(h, r0));
        assert(owns(h, b, r.last().1 as int, r0));
    }
}

/// **Field-sensitive kids.** A pointer that the checker keeps is not in the
/// part a callee can free: by unique routes, its place would go through a
/// kid owned under a mutable argument's place, and the Weft rule kills it.
proof fn lemma_not_full_fp(sc: Schema, s: LState, ss: LSState, args: Seq<(Var, bool)>, pl: LPlace, p: IPtr)
    requires
        linv(sc, s, ss),
        forall|k: int| 0 <= k < args.len() ==> ss.vars.contains_key(#[trigger] args[k].0),
        lptr_ok(sc, s, ss, pl, p),
        !lkilled(ss, args, pl),
    ensures
        !full_fp(sc, s.heap, lptrs(s, args), p.addr),
{
    let h = s.heap;
    let ps = lptrs(s, args);
    let c = p.addr;
    lemma_heap_wf_facts(s.heap, s.locals, s.next_stamp);
    if full_fp(sc, h, ps, c) {
        let k = choose|k: int| 0 <= k < ps.len() && ps[k].1 && #[trigger] fbelow(sc, h, ps[k].0.addr, ps[k].0.fp, c);
        let w = args[k].0;
        assert(ss.vars.contains_key(w));
        let pw = s.vars[w];
        let gw = ss.vars[w];
        assert(ps[k].0 == pw && ps[k].1 == args[k].1);
        assert(lptr_ok(sc, s, ss, gw, pw));
        let m = pw.addr;
        let tau = choose|r: Route| r.len() > 0 && #[trigger] resolve(h, m, r) == Some(c) && owned_under(sc, h[m].ty, r[0].0, pw.fp);
        let rp = choose|r: Route|
            labels(r) == hop_labels(gw.hops) && #[trigger] resolve(h, s.locals[gw.root], r) == Some(m);
        let rq = choose|r: Route|
            labels(r) == hop_labels(pl.hops) && #[trigger] resolve(h, s.locals[pl.root], r) == Some(c);
        lemma_resolve_concat(h, s.locals[gw.root], rp, tau, m);
        assert(unowned(h, s.locals[gw.root]));
        assert(unowned(h, s.locals[pl.root]));
        lemma_resolve_unique(h, s.locals[gw.root], s.locals[pl.root], rp + tau, rq, c);
        assert(gw.root == pl.root);
        lemma_labels_concat(rp, tau);
        let n = gw.hops.len() as int;
        assert(hop_labels(pl.hops) == hop_labels(gw.hops) + labels(tau));
        assert(pl.hops.len() == hop_labels(pl.hops).len());
        assert(gw.hops.len() == hop_labels(gw.hops).len());
        assert(pl.hops.len() == n + tau.len());
        lemma_alloc_ty_prefix(sc, ss.lty[pl.root], pl.hops, n);
        lemma_alloc_ty_prefix(sc, ss.lty[pl.root], pl.hops, n + 1);
        assert(hop_labels(pl.hops.subrange(0, n)) =~= hop_labels(gw.hops)) by {
            assert forall|i: int| 0 <= i < n implies #[trigger] hop_labels(pl.hops.subrange(0, n))[i] == hop_labels(gw.hops)[i] by {
                assert(hop_labels(pl.hops)[i] == pl.hops[i].1);
                assert(hop_labels(pl.hops.subrange(0, n))[i] == pl.hops.subrange(0, n)[i].1);
                assert((hop_labels(gw.hops) + labels(tau))[i] == hop_labels(gw.hops)[i]);
            }
        }
        lemma_hops_eq(sc, ss.lty[pl.root], pl.hops.subrange(0, n), gw.hops);
        let sub1 = pl.hops.subrange(0, n + 1);
        assert(sub1.drop_last() =~= pl.hops.subrange(0, n));
        assert(sub1.last() == pl.hops[n]);
        let l = pl.hops[n].1;
        assert(hop_labels(pl.hops)[n] == l);
        assert((hop_labels(gw.hops) + labels(tau))[n] == labels(tau)[0]);
        assert(l == tau[0].0);
        assert(pw.ty == h[m].ty);
        assert(pl.hops[n].0 == sc[pw.ty].kids[l].0);
        assert(pw.fp.is_prefix_of(pl.hops[n].0));
        lemma_kills_kid(gw, pl);
        assert(lkills(ss.vars[args[k].0], pl));
        assert(lkilled(ss, args, pl));
    }
}

/// Routes that avoid the part a callee can free survive the call.
proof fn lemma_lroute_preserved(
    sc: Schema,
    s: LState,
    ps: Seq<(IPtr, bool)>,
    h2: Heap,
    n2: Stamp,
    a: Addr,
    r: Route,
    c: Addr,
)
    requires
        lcallee_effect(sc, s, ps, h2, n2),
        resolve(s.heap, a, r) == Some(c),
        !full_fp(sc, s.heap, ps, c),
    ensures
        resolve(h2, a, r) == Some(c),
    decreases r.len(),
{
    let h = s.heap;
    if r.len() > 0 {
        let st = r.last();
        let b = lemma_resolve_owner(h, a, r, c);
        if full_fp(sc, h, ps, b) {
            let k = choose|k: int| 0 <= k < ps.len() && ps[k].1 && #[trigger] fbelow(sc, h, ps[k].0.addr, ps[k].0.fp, b);
            let m = ps[k].0.addr;
            let q = choose|q: Route| q.len() > 0 && #[trigger] resolve(h, m, q) == Some(b) && owned_under(sc, h[m].ty, q[0].0, ps[k].0.fp);
            lemma_resolve_push(h, m, q, st);
            assert(q.push(st)[0] == q[0]);
            assert(resolve(h, m, q.push(st)) == Some(c));
            assert(fbelow(sc, h, m, ps[k].0.fp, c));
            assert(full_fp(sc, h, ps, c));
        }
        if mut_target(ps, b) && kid_mut(sc, h, ps, b, st.0) {
            let k = choose|k: int| 0 <= k < ps.len() && ps[k].1 && ps[k].0.addr == b && #[trigger] owned_under(sc, h[b].ty, st.0, ps[k].0.fp);
            let w = Seq::<Step>::empty().push(st);
            lemma_resolve_push(h, b, Seq::empty(), st);
            assert(resolve(h, b, w) == Some(c));
            assert(w[0] == st);
            assert(fbelow(sc, h, b, ps[k].0.fp, c));
            assert(full_fp(sc, h, ps, c));
        }
        lemma_lroute_preserved(sc, s, ps, h2, n2, a, r.drop_last(), b);
        assert(h.contains_key(b));
        if mut_target(ps, b) {
            assert(h[b].kids[st.1 as int].0 == st.0);
            assert(h2[b].kids[st.1 as int] == h[b].kids[st.1 as int]);
        } else {
            assert(h2[b] == h[b]);
        }
        assert(kid_at(h2, b, st) == kid_at(h, b, st));
    }
}

/// **Inline frame for calls.** The inline path of a pointer that the
/// checker keeps reads no tag that the callee can change.
proof fn lemma_view_kept(
    sc: Schema,
    s: LState,
    ss: LSState,
    args: Seq<(Var, bool)>,
    h2: Heap,
    n2: Stamp,
    pl: LPlace,
    p: IPtr,
)
    requires
        linv(sc, s, ss),
        forall|k: int| 0 <= k < args.len() ==> ss.vars.contains_key(#[trigger] args[k].0),
        lcallee_effect(sc, s, lptrs(s, args), h2, n2),
        lptr_ok(sc, s, ss, pl, p),
        !lkilled(ss, args, pl),
        mut_target(lptrs(s, args), p.addr),
        !full_fp(sc, s.heap, lptrs(s, args), p.addr),
    ensures
        view(sc, p.ty, h2[p.addr].data, 0, p.fp) == view(sc, p.ty, s.heap[p.addr].data, 0, p.fp),
{
    let h = s.heap;
    let ps = lptrs(s, args);
    let c = p.addr;
    let d = h[c].data;
    let d2 = h2[c].data;
    let s2 = LState { heap: h2, next_stamp: n2, ..s };
    lemma_heap_wf_facts(s.heap, s.locals, s.next_stamp);
    assert(layout_wf(sc, h2));
    assert(h.contains_key(c));
    assert(h2.contains_key(c) && h2[c].ty == h[c].ty);
    assert(d2.len() == d.len());
    assert forall|j: int| #[trigger] reads(sc, p.ty, d, 0, p.fp, j) implies d2[j] == d[j] by {
        lemma_reads_region(sc, p.ty, d, 0, p.fp, j);
        if in_mut_region(sc, h, ps, c, j) {
            let k = choose|k: int| 0 <= k < ps.len() && ps[k].1 && ps[k].0.addr == c && #[trigger] in_region(sc, h[c], ps[k].0.fp, j);
            let w = args[k].0;
            assert(ss.vars.contains_key(w));
            let pw = s.vars[w];
            let gw = ss.vars[w];
            assert(ps[k].0 == pw && ps[k].1 == args[k].1);
            assert(lptr_ok(sc, s, ss, gw, pw));
            assert(pw.ty == p.ty);
            lemma_reads_in_region(sc, p.ty, d, 0, pw.fp, p.fp, j);
            let i = choose|i: int| pw.fp.len() <= i < p.fp.len() && #[trigger] p.fp[i] is Variant;
            let rp = choose|r: Route|
                labels(r) == hop_labels(gw.hops) && #[trigger] resolve(h, s.locals[gw.root], r) == Some(c);
            let rq = choose|r: Route|
                labels(r) == hop_labels(pl.hops) && #[trigger] resolve(h, s.locals[pl.root], r) == Some(c);
            assert(unowned(h, s.locals[gw.root]));
            assert(unowned(h, s.locals[pl.root]));
            lemma_resolve_unique(h, s.locals[gw.root], s.locals[pl.root], rp, rq, c);
            assert(gw.root == pl.root);
            lemma_hops_eq(sc, ss.lty[pl.root], gw.hops, pl.hops);
            lemma_kills_variant(gw, pl, i);
            assert(lkills(ss.vars[args[k].0], pl));
            assert(lkilled(ss, args, pl));
        }
    }
    lemma_view_agree(sc, p.ty, d, d2, 0, p.fp);
}

/// **Frame lemma.** A pointer that the call does not kill stays valid.
proof fn lemma_lcall_survivor(
    sc: Schema,
    s: LState,
    ss: LSState,
    args: Seq<(Var, bool)>,
    h2: Heap,
    n2: Stamp,
    pl: LPlace,
    p: IPtr,
)
    requires
        linv(sc, s, ss),
        forall|k: int| 0 <= k < args.len() ==> ss.vars.contains_key(#[trigger] args[k].0),
        lcallee_effect(sc, s, lptrs(s, args), h2, n2),
        lptr_ok(sc, s, ss, pl, p),
        !lkilled(ss, args, pl),
    ensures
        lptr_ok(sc, LState { heap: h2, next_stamp: n2, ..s }, ss, pl, p),
{
    let h = s.heap;
    let ps = lptrs(s, args);
    let c = p.addr;
    let s2 = LState { heap: h2, next_stamp: n2, ..s };
    lemma_not_full_fp(sc, s, ss, args, pl, p);
    let rq = choose|r: Route|
        labels(r) == hop_labels(pl.hops) && #[trigger] resolve(h, s.locals[pl.root], r) == Some(c);
    lemma_lroute_preserved(sc, s, ps, h2, n2, s.locals[pl.root], rq, c);
    assert(resolve(s2.heap, s2.locals[pl.root], rq) == Some(c));
    assert(h.contains_key(c));
    if mut_target(ps, c) {
        lemma_view_kept(sc, s, ss, args, h2, n2, pl, p);
    } else {
        assert(h2[c] == h[c]);
    }
    assert(ilive(sc, s2, p));
}

proof fn lemma_lpreserve_call(sc: Schema, s: LState, ss: LSState, args: Seq<(Var, bool)>, s2: LState)
    requires
        linv(sc, s, ss),
        linstr_ok(sc, ss, LInstr::Call { args }),
        lstep(sc, s, LInstr::Call { args }, s2),
    ensures
        linv(sc, s2, lpost(ss, LInstr::Call { args })),
{
    let (h2, n2) = choose|h2: Heap, n2: Stamp|
        #[trigger] lcallee_effect(sc, s, lptrs(s, args), h2, n2) && s2 == LState { heap: h2, next_stamp: n2, ..s };
    let ps = lptrs(s, args);
    let ss2 = lpost(ss, LInstr::Call { args });
    lemma_heap_wf_facts(s.heap, s.locals, s.next_stamp);
    assert forall|x: Local| #[trigger] s2.locals.contains_key(x) implies ss2.lty.contains_key(x) && ss2.lty[x]
        == s2.heap[s2.locals[x]].ty by {
        lemma_root_not_full_fp(sc, s, ps, x);
        assert(s.heap.contains_key(s.locals[x]));
    }
    assert forall|v: Var| #[trigger] ss2.vars.contains_key(v) implies s2.vars.contains_key(v) && lptr_ok(sc, s2, ss2, ss2.vars[v], s2.vars[v]) by {
        lemma_lcall_survivor(sc, s, ss, args, h2, n2, ss.vars[v], s.vars[v]);
    }
}

// ---------------------------------------------------------------------------
// Preservation and no UB
// ---------------------------------------------------------------------------

/// A write of a primitive changes no tag that a valid path reads.
proof fn lemma_write_keeps_view(sc: Schema, t: Ty, d: Seq<int>, fw: Seq<PStep>, q: Seq<PStep>, val: int)
    requires
        wf_schema(sc),
        sc.contains_key(t),
        d.len() == sc[t].size,
        view(sc, t, d, 0, fw) is Some,
        sc.contains_key(vty(sc, t, d, 0, fw)),
        sc[vty(sc, t, d, 0, fw)].shape is Prim,
        voff(sc, t, d, 0, fw) < d.len(),
        view(sc, t, d, 0, q) is Some,
    ensures
        view(sc, t, d.update(voff(sc, t, d, 0, fw) as int, val), 0, q) == view(sc, t, d, 0, q),
{
    let j = voff(sc, t, d, 0, fw) as int;
    let d2 = d.update(j, val);
    assert(ty_ok(sc, vty(sc, t, d, 0, fw)));
    assert forall|i: int| #[trigger] reads(sc, t, d, 0, q, i) implies d2[i] == d[i] by {
        lemma_reads_region(sc, t, d, 0, q, i);
        if i == j {
            lemma_reads_in_region(sc, t, d, 0, fw, q, i);
            let ext = q.subrange(fw.len() as int, q.len() as int);
            assert(q =~= fw + ext);
            lemma_prim_end(sc, t, d, 0, fw, ext);
        }
    }
    lemma_view_agree(sc, t, d, d2, 0, q);
}

/// **Preservation.** A step of an accepted instruction keeps the invariant.
pub proof fn lemma_lpreserve(sc: Schema, s: LState, ss: LSState, i: LInstr, s2: LState)
    requires
        linv(sc, s, ss),
        linstr_ok(sc, ss, i),
        lstep(sc, s, i, s2),
    ensures
        linv(sc, s2, lpost(ss, i)),
{
    let ss2 = lpost(ss, i);
    lemma_heap_wf_facts(s.heap, s.locals, s.next_stamp);
    match i {
        LInstr::Borrow { dst, x } => {
            let a = s.locals[x];
            let e = Seq::<Step>::empty();
            assert(labels(e) =~= hop_labels(Seq::<(Seq<PStep>, Label)>::empty()));
            assert(resolve(s2.heap, s2.locals[x], e) == Some(a));
            assert(s.heap.contains_key(a));
            lemma_linv_vars(sc, s, ss, s2, ss2, dst);
        },
        LInstr::Field { dst, src, f } => {
            assert(lptr_ok(sc, s, ss, ss.vars[src], s.vars[src]));
            let rs = choose|r: Route|
                labels(r) == hop_labels(ss.vars[src].hops) && #[trigger] resolve(s.heap, s.locals[ss.vars[src].root], r) == Some(s.vars[src].addr);
            assert(resolve(s2.heap, s2.locals[ss2.vars[dst].root], rs) == Some(s2.vars[dst].addr));
            lemma_linv_vars(sc, s, ss, s2, ss2, dst);
        },
        LInstr::Variant { dst, src, v } => {
            assert(lptr_ok(sc, s, ss, ss.vars[src], s.vars[src]));
            let rs = choose|r: Route|
                labels(r) == hop_labels(ss.vars[src].hops) && #[trigger] resolve(s.heap, s.locals[ss.vars[src].root], r) == Some(s.vars[src].addr);
            assert(resolve(s2.heap, s2.locals[ss2.vars[dst].root], rs) == Some(s2.vars[dst].addr));
            lemma_linv_vars(sc, s, ss, s2, ss2, dst);
        },
        LInstr::Child { dst, src, label } => {
            let pl = ss.vars[src];
            let p = s.vars[src];
            assert(lptr_ok(sc, s, ss, pl, p));
            let idx = choose|idx: nat|
                {
                    let res = #[trigger] kid_at(s.heap, s.vars[src].addr, (label, idx));
                    res is Some && s2 == LState { vars: s.vars.insert(dst, lptr_to(s.heap, res->0)), ..s }
                };
            let st: Step = (label, idx);
            let a = p.addr;
            let c = kid_at(s.heap, a, st)->0;
            assert(s.heap.contains_key(c));
            let rs = choose|r: Route|
                labels(r) == hop_labels(pl.hops) && #[trigger] resolve(s.heap, s.locals[pl.root], r) == Some(a);
            lemma_resolve_push(s.heap, s.locals[pl.root], rs, st);
            lemma_labels_push(rs, st);
            let npl = ss2.vars[dst];
            assert(npl.hops == pl.hops.push((pl.tail, label)));
            assert(hop_labels(npl.hops) =~= hop_labels(pl.hops).push(label));
            assert(resolve(s2.heap, s2.locals[npl.root], rs.push(st)) == Some(c));
            assert(npl.hops.drop_last() =~= pl.hops);
            assert(s.heap[a].kids[idx as int].0 == label);
            assert(s.heap[c].ty == sc[s.heap[a].ty].kids[label].1);
            assert(alloc_ty(sc, ss.lty[npl.root], npl.hops) == Some(s.heap[c].ty));
            assert(lptr_ok(sc, s2, ss2, npl, s2.vars[dst]));
            lemma_linv_vars(sc, s, ss, s2, ss2, dst);
        },
        LInstr::Copy { dst, src } => {
            if ss.vars.contains_key(src) {
                lemma_lptr_transfer(sc, s, s2, ss, ss2, ss.vars[src], s.vars[src]);
            }
            lemma_linv_vars(sc, s, ss, s2, ss2, dst);
        },
        LInstr::Read { .. } => {},
        LInstr::Write { src, path, val } => {
            let p = s.vars[src];
            let a = p.addr;
            let h = s.heap;
            let h2 = s2.heap;
            let fw = p.fp + path;
            let j = slot(sc, s, p, path)->0;
            assert(h2.dom() =~= h.dom());
            assert forall|b: Addr| #[trigger] h.contains_key(b) implies h2[b].kids == h[b].kids
                && h2[b].stamp == h[b].stamp && h2[b].ty == h[b].ty by {}
            assert forall|b: Addr, k: int, c: Addr| #[trigger] owns(h2, b, k, c) == owns(h, b, k, c) by {}
            assert forall|r: Route, a0: Addr| #[trigger] resolve(h2, a0, r) == resolve(h, a0, r) by {
                lemma_resolve_same_kids(h, h2, a0, r);
            }
            assert(heap_wf(h2, s2.locals, s2.next_stamp));
            assert(layout_wf(sc, h2)) by {
                assert forall|b: Addr| #[trigger] h2.contains_key(b) implies {
                    &&& sc.contains_key(h2[b].ty)
                    &&& h2[b].data.len() == sc[h2[b].ty].size
                    &&& forall|k: int|
                        0 <= k < h2[b].kids.len() ==> sc[h2[b].ty].kids.contains_key(#[trigger] h2[b].kids[k].0)
                            && h2[h2[b].kids[k].1].ty == sc[h2[b].ty].kids[h2[b].kids[k].0].1
                } by {
                    assert forall|k: int| 0 <= k < h2[b].kids.len() implies sc[h2[b].ty].kids.contains_key(#[trigger] h2[b].kids[k].0)
                        && h2[h2[b].kids[k].1].ty == sc[h2[b].ty].kids[h2[b].kids[k].0].1 by {
                        assert(h.contains_key(h[b].kids[k].1));
                    }
                }
            }
            assert forall|v: Var| #[trigger] ss2.vars.contains_key(v) implies s2.vars.contains_key(v) && lptr_ok(sc, s2, ss2, ss2.vars[v], s2.vars[v]) by {
                let q = s.vars[v];
                let ql = ss.vars[v];
                assert(lptr_ok(sc, s, ss, ql, q));
                let r = choose|r: Route|
                    labels(r) == hop_labels(ql.hops) && #[trigger] resolve(s.heap, s.locals[ql.root], r) == Some(q.addr);
                assert(resolve(s2.heap, s2.locals[ql.root], r) == Some(q.addr));
                if q.addr == a {
                    assert(q.ty == p.ty);
                    lemma_write_keeps_view(sc, p.ty, h[a].data, fw, q.fp, val);
                }
                assert(ilive(sc, s2, q));
            }
        },
        LInstr::Call { args } => {
            lemma_lpreserve_call(sc, s, ss, args, s2);
        },
    }
}

/// **No UB.** An accepted instruction in a state that satisfies the
/// invariant has no use after free, no type confusion, and no access
/// outside the layout.
pub proof fn lemma_lno_ub(sc: Schema, s: LState, ss: LSState, i: LInstr)
    requires
        linv(sc, s, ss),
        linstr_ok(sc, ss, i),
    ensures
        !lub(sc, s, i),
{
    match i {
        LInstr::Field { src, f, .. } => {
            let p = s.vars[src];
            assert(lptr_ok(sc, s, ss, ss.vars[src], p));
            let d = s.heap[p.addr].data;
            lemma_view_sview(sc, p.ty, d, 0, p.fp);
            lemma_view_push(sc, p.ty, d, 0, p.fp, PStep::Field(f));
        },
        LInstr::Variant { src, v, .. } => {
            let p = s.vars[src];
            assert(lptr_ok(sc, s, ss, ss.vars[src], p));
            lemma_view_sview(sc, p.ty, s.heap[p.addr].data, 0, p.fp);
        },
        LInstr::Child { src, .. } => {
            assert(lptr_ok(sc, s, ss, ss.vars[src], s.vars[src]));
        },
        LInstr::Read { src, path } => {
            lemma_lno_ub_access(sc, s, ss, src, path);
        },
        LInstr::Write { src, path, .. } => {
            lemma_lno_ub_access(sc, s, ss, src, path);
        },
        LInstr::Call { args } => {
            assert forall|k: int| 0 <= k < args.len() implies !#[trigger] ldangling(sc, s, args[k].0) by {
                assert(ss.vars.contains_key(args[k].0));
                assert(lptr_ok(sc, s, ss, ss.vars[args[k].0], s.vars[args[k].0]));
            }
        },
        _ => {},
    }
}

/// An access that the checker accepts names a primitive slot inside the object.
proof fn lemma_lno_ub_access(sc: Schema, s: LState, ss: LSState, src: Var, path: Seq<PStep>)
    requires
        linv(sc, s, ss),
        ss.vars.contains_key(src),
        prim_at(sc, ss, ss.vars[src], path),
    ensures
        !ldangling(sc, s, src),
        slot(sc, s, s.vars[src], path) is Some,
{
    let p = s.vars[src];
    assert(lptr_ok(sc, s, ss, ss.vars[src], p));
    let d = s.heap[p.addr].data;
    lemma_view_sview(sc, p.ty, d, 0, p.fp);
    let r = view(sc, p.ty, d, 0, p.fp)->0;
    let t2 = sview(sc, r.0, path)->0;
    lemma_field_only_view(sc, r.0, d, r.1, path);
    lemma_view_concat(sc, p.ty, d, 0, p.fp, path);
    assert(sc.contains_key(p.ty));
    lemma_view_region(sc, p.ty, d, 0, p.fp + path);
    assert(ty_ok(sc, t2));
}

// ---------------------------------------------------------------------------
// Main theorem
// ---------------------------------------------------------------------------

proof fn lemma_lss_lty(ss0: LSState, prog: Seq<LInstr>, k: nat)
    ensures
        lss_at(ss0, prog, k).lty == ss0.lty,
        lss_at(ss0, prog, k).locals == ss0.locals,
    decreases k,
{
    if k > 0 {
        lemma_lss_lty(ss0, prog, (k - 1) as nat);
    }
}

proof fn lemma_linv_along(sc: Schema, ss0: LSState, prog: Seq<LInstr>, trace: Seq<LState>, k: nat)
    requires
        linv(sc, trace[0], ss0),
        lcheck(sc, ss0, prog),
        is_ltrace(sc, prog, trace),
        k < trace.len(),
    ensures
        linv(sc, trace[k as int], lss_at(ss0, prog, k)),
    decreases k,
{
    if k > 0 {
        let km = (k - 1) as nat;
        lemma_linv_along(sc, ss0, prog, trace, km);
        assert(linstr_ok(sc, lss_at(ss0, prog, km), prog[km as int]));
        assert(lstep(sc, trace[km as int], prog[km as int], trace[k as int]));
        lemma_lpreserve(sc, trace[km as int], lss_at(ss0, prog, km), prog[km as int], trace[k as int]);
    }
}

/// **Soundness with inline layout.** If the checker accepts the program,
/// then no execution of it has UB: no use after free, no type confusion
/// (a path through a variant that is not active), and no access outside
/// the layout of a type.
pub proof fn layout_soundness(sc: Schema, ss0: LSState, prog: Seq<LInstr>, trace: Seq<LState>)
    requires
        linv(sc, trace[0], ss0),
        lcheck(sc, ss0, prog),
        is_ltrace(sc, prog, trace),
    ensures
        forall|k: int| 0 <= k < trace.len() && k < prog.len() ==> !#[trigger] lub(sc, trace[k], prog[k]),
{
    assert forall|k: int| 0 <= k < trace.len() && k < prog.len() implies !#[trigger] lub(sc, trace[k], prog[k]) by {
        lemma_linv_along(sc, ss0, prog, trace, k as nat);
        assert(linstr_ok(sc, lss_at(ss0, prog, k as nat), prog[k]));
        lemma_lno_ub(sc, trace[k], lss_at(ss0, prog, k as nat), prog[k]);
    }
}

/// Soundness with inline layout from a fresh start: a consistent schema, a
/// well-formed heap, no references yet.
pub proof fn layout_soundness_from_start(sc: Schema, prog: Seq<LInstr>, trace: Seq<LState>)
    requires
        wf_schema(sc),
        lwf(sc, trace[0]),
        lcheck(sc, linitial(trace[0]), prog),
        is_ltrace(sc, prog, trace),
    ensures
        forall|k: int| 0 <= k < trace.len() && k < prog.len() ==> !#[trigger] lub(sc, trace[k], prog[k]),
{
    let s0 = trace[0];
    let ss0 = linitial(s0);
    assert forall|x: Local| #[trigger] s0.locals.contains_key(x) implies ss0.lty.contains_key(x) && ss0.lty[x]
        == s0.heap[s0.locals[x]].ty by {
        assert(s0.locals.dom().contains(x));
    }
    assert(linv(sc, s0, ss0));
    layout_soundness(sc, ss0, prog, trace);
}

} // verus!
