//! # The ownership invariant (`inv_b`)
//!
//! A position is a stack frame, a pending frame, or a frame of a fresh `once`
//! continuation. These are the owning positions: when the machine finishes,
//! they are all gone. `inv_b` says:
//! * each live resource is held by exactly one slot of one owning position,
//!   and only live resources are held;
//! * each fresh `once` continuation is held by exactly one owning position,
//!   and a continuation inside a continuation is older (smaller id);
//! * the slots of each owning frame match the checker state; frames that wait
//!   for an abort (pending, or in a fresh `once` continuation) hold only
//!   values with `on abort`;
//! * the frames of a `multi` continuation hold nothing linear and no fresh
//!   `once` continuation.

use vstd::prelude::*;
use crate::model::*;
use crate::checker::*;
use crate::scope::*;

verus! {

/// `p` is an owning position of `s`.
pub open spec fn owning(s: State, p: Pos) -> bool {
    match p {
        Pos::Stk(i) => i < s.stack.len(),
        Pos::Pnd(i) => i < s.pending.len(),
        Pos::Knt(k, i) => fresh_once(s, k) && i < s.konts[k].frames.len(),
    }
}

/// `p` is an owning position with a code frame.
pub open spec fn ocode(s: State, p: Pos) -> bool {
    owning(s, p) && frame_at(s, p) is Code
}

/// The code frame at `p`.
pub open spec fn cf_at(s: State, p: Pos) -> CFrame {
    frame_at(s, p)->Code_0
}

/// Some slot of `m` holds `r`.
pub open spec fn has_res(m: Map<Slot, ResId>, r: ResId) -> bool {
    exists|sl: Slot| #[trigger] m.contains_key(sl) && m[sl] == r
}

/// Position `p` holds resource `r`.
pub open spec fn holds(s: State, p: Pos, r: ResId) -> bool {
    ocode(s, p) && has_res(cf_at(s, p).slots, r)
}

/// Position `p` holds continuation `kid`.
pub open spec fn holdsk(s: State, p: Pos, kid: KId) -> bool {
    ocode(s, p) && cf_at(s, p).k == Some(kid)
}

/// Resource `r` is live.
pub open spec fn live(s: State, r: ResId) -> bool {
    s.res.contains_key(r) && s.res[r].st == RState::Live
}

/// No two slots of `m` hold the same resource.
pub open spec fn injective(m: Map<Slot, ResId>) -> bool {
    forall|a: Slot, b: Slot|
        #[trigger] m.contains_key(a) && #[trigger] m.contains_key(b) && m[a] == m[b] ==> a == b
}

/// The slots of `f` match its checker state: each slot is live in the
/// checker, its resource is live, and the `on abort` flags agree. With
/// `full`, each live checker slot holds a resource.
pub open spec fn slots_typed(prog: Prog, s: State, f: CFrame, full: bool) -> bool {
    let lin = ss_of(prog, f).lin;
    &&& code_ok(prog, f)
    &&& forall|sl: Slot|
        #[trigger] f.slots.contains_key(sl) ==> lin.contains_key(sl) && live(s, f.slots[sl])
            && s.res[f.slots[sl]].on_abort == lin[sl]
    &&& full ==> forall|sl: Slot| #[trigger] lin.contains_key(sl) ==> f.slots.contains_key(sl)
}

/// A `once` continuation of `f` is usable in the checker iff it is fresh.
pub open spec fn k_sync(prog: Prog, s: State, f: CFrame) -> bool {
    f.k is Some && s.konts.contains_key(f.k->0) && !s.konts[f.k->0].multi ==> ss_of(prog, f).k
        == !s.konts[f.k->0].used
}

/// The continuation of `f`, if any, exists.
pub open spec fn k_known(s: State, f: CFrame) -> bool {
    f.k is Some ==> s.konts.contains_key(f.k->0)
}

/// The conditions on an owning code frame. `full`: every live checker slot
/// holds a resource. `abort`: every live slot declares `on abort`.
pub open spec fn frame_good(prog: Prog, s: State, f: CFrame, full: bool, abort: bool) -> bool {
    &&& slots_typed(prog, s, f, full)
    &&& injective(f.slots)
    &&& k_sync(prog, s, f)
    &&& k_known(s, f)
    &&& abort ==> all_abortable(ss_of(prog, f))
}

/// The conditions on the code frame at owning position `p`. Pending frames
/// lose slots as the unwinder runs. Frames that wait for an abort hold only
/// values with `on abort`.
pub open spec fn pos_ok(prog: Prog, s: State, p: Pos) -> bool {
    frame_good(prog, s, cf_at(s, p), !(p is Pnd), !(p is Stk))
}

/// A frame of a `multi` continuation: no linear value, and any `once`
/// continuation that it names is used.
pub open spec fn clean(prog: Prog, s: State, f: CFrame) -> bool {
    &&& code_ok(prog, f)
    &&& forall|sl: Slot| !#[trigger] f.slots.contains_key(sl)
    &&& forall|sl: Slot| !#[trigger] ss_of(prog, f).lin.contains_key(sl)
    &&& f.k is Some && s.konts.contains_key(f.k->0) && !s.konts[f.k->0].multi ==> s.konts[f.k->0].used
        && !ss_of(prog, f).k
}

/// Every code frame of `fr` is clean.
pub open spec fn all_clean(prog: Prog, s: State, fr: Seq<Frame>) -> bool {
    forall|i: int| 0 <= i < fr.len() && #[trigger] fr[i] is Code ==> clean(prog, s, fr[i]->Code_0)
}

/// Each owning code frame is good.
pub open spec fn b_pos(prog: Prog, s: State) -> bool {
    forall|p: Pos| #[trigger] ocode(s, p) ==> pos_ok(prog, s, p)
}

/// No resource has two owners.
pub open spec fn b_unique_res(s: State) -> bool {
    forall|p1: Pos, p2: Pos, r: ResId| #[trigger] holds(s, p1, r) && #[trigger] holds(s, p2, r) ==> p1 == p2
}

/// Each live resource has an owner.
pub open spec fn b_owned(s: State) -> bool {
    forall|r: ResId| #[trigger] live(s, r) ==> exists|p: Pos| #[trigger] holds(s, p, r)
}

/// No fresh `once` continuation has two holders.
pub open spec fn b_unique_k(s: State) -> bool {
    forall|p1: Pos, p2: Pos, kid: KId|
        fresh_once(s, kid) && #[trigger] holdsk(s, p1, kid) && #[trigger] holdsk(s, p2, kid) ==> p1 == p2
}

/// Each fresh `once` continuation has a holder.
pub open spec fn b_held_k(s: State) -> bool {
    forall|kid: KId| #[trigger] fresh_once(s, kid) ==> exists|p: Pos| #[trigger] holdsk(s, p, kid)
}

/// A continuation inside a continuation is older.
pub open spec fn b_order(s: State) -> bool {
    forall|k2: KId, i: nat, kid: KId|
        #[trigger] holdsk(s, Pos::Knt(k2, i), kid) && fresh_once(s, kid) ==> kid < k2
}

/// Every `multi` continuation holds only clean frames.
pub open spec fn b_multi(prog: Prog, s: State) -> bool {
    forall|k: KId| #[trigger] s.konts.contains_key(k) && s.konts[k].multi ==> all_clean(prog, s, s.konts[k].frames)
}

/// The ownership invariant.
pub open spec fn inv_b(prog: Prog, s: State) -> bool {
    &&& b_pos(prog, s)
    &&& b_unique_res(s)
    &&& b_owned(s)
    &&& b_unique_k(s)
    &&& b_held_k(s)
    &&& b_order(s)
    &&& b_multi(prog, s)
}

// ---------------------------------------------------------------------------
// Relabeling
// ---------------------------------------------------------------------------

/// The conditions under which the resource and continuation parts of
/// `inv_b` carry over from `s` to `s2`. `bk` maps a position of `s2` back to
/// `s`, and `fw` maps a position of `s` forward to `s2`.
pub open spec fn relabel_ok(s: State, s2: State, bk: spec_fn(Pos) -> Pos, fw: spec_fn(Pos) -> Pos) -> bool {
    // resources
    &&& forall|p: Pos, r: ResId| #[trigger] holds(s2, p, r) && live(s, r) ==> holds(s, bk(p), r)
    &&& forall|p: Pos, q: Pos| #[trigger] ocode(s2, p) && #[trigger] ocode(s2, q) && p != q ==> bk(p) != bk(q)
    &&& forall|p1: Pos, p2: Pos, r: ResId|
        #[trigger] holds(s2, p1, r) && #[trigger] holds(s2, p2, r) && !live(s, r) ==> p1 == p2
    &&& forall|q: Pos, r: ResId| #[trigger] holds(s, q, r) && live(s2, r) ==> holds(s2, fw(q), r)
    &&& forall|r: ResId| #[trigger] live(s2, r) && !live(s, r) ==> exists|p: Pos| #[trigger] holds(s2, p, r)
    // continuations
    &&& forall|kid: KId| #[trigger] fresh_once(s2, kid) && s.konts.contains_key(kid) ==> fresh_once(s, kid)
    &&& forall|p: Pos, kid: KId|
        #[trigger] holdsk(s2, p, kid) && fresh_once(s2, kid) && s.konts.contains_key(kid) ==> holdsk(
            s,
            bk(p),
            kid,
        )
    &&& forall|p1: Pos, p2: Pos, kid: KId|
        #[trigger] holdsk(s2, p1, kid) && #[trigger] holdsk(s2, p2, kid) && fresh_once(s2, kid)
            && !s.konts.contains_key(kid)
            ==> p1 == p2
    &&& forall|q: Pos, kid: KId|
        #[trigger] holdsk(s, q, kid) && fresh_once(s2, kid) && s.konts.contains_key(kid) ==> holdsk(
            s2,
            fw(q),
            kid,
        )
    &&& forall|kid: KId|
        #[trigger] fresh_once(s2, kid) && !s.konts.contains_key(kid) ==> exists|p: Pos| #[trigger] holdsk(
            s2,
            p,
            kid,
        )
}

/// The resource and continuation parts of `inv_b` carry over a relabeling.
pub proof fn lemma_relabel(s: State, s2: State, bk: spec_fn(Pos) -> Pos, fw: spec_fn(Pos) -> Pos)
    requires
        b_unique_res(s),
        b_owned(s),
        b_unique_k(s),
        b_held_k(s),
        relabel_ok(s, s2, bk, fw),
    ensures
        b_unique_res(s2),
        b_owned(s2),
        b_unique_k(s2),
        b_held_k(s2),
{
    assert forall|p1: Pos, p2: Pos, r: ResId| #[trigger] holds(s2, p1, r) && #[trigger] holds(s2, p2, r) implies p1
        == p2 by {
        if live(s, r) {
            assert(holds(s, bk(p1), r));
            assert(holds(s, bk(p2), r));
        }
    }
    assert forall|r: ResId| #[trigger] live(s2, r) implies exists|p: Pos| #[trigger] holds(s2, p, r) by {
        if live(s, r) {
            let q = choose|q: Pos| #[trigger] holds(s, q, r);
            assert(holds(s2, fw(q), r));
        }
    }
    assert forall|p1: Pos, p2: Pos, kid: KId|
        fresh_once(s2, kid) && #[trigger] holdsk(s2, p1, kid) && #[trigger] holdsk(s2, p2, kid) implies p1
        == p2 by {
        if s.konts.contains_key(kid) {
            assert(holdsk(s, bk(p1), kid));
            assert(holdsk(s, bk(p2), kid));
        }
    }
    assert forall|kid: KId| #[trigger] fresh_once(s2, kid) implies exists|p: Pos| #[trigger] holdsk(s2, p, kid) by {
        if s.konts.contains_key(kid) {
            assert(fresh_once(s, kid));
            let q = choose|q: Pos| #[trigger] holdsk(s, q, kid);
            assert(holdsk(s2, fw(q), kid));
        }
    }
}

/// The initial state satisfies `inv_b`.
pub proof fn lemma_b_init(prog: Prog)
    requires
        check(prog),
    ensures
        inv_b(prog, init(prog)),
{
    let s = init(prog);
    let f = s.stack[0]->Code_0;
    assert(block_ok(prog, prog.main));
    assert(ss_of(prog, f) == entry(prog.blocks[prog.main].sig));
    assert(f.slots.dom() =~= Set::empty());
    assert forall|p: Pos| #[trigger] ocode(s, p) implies pos_ok(prog, s, p) by {
        assert(p == Pos::Stk(0));
    }
    assert forall|p1: Pos, p2: Pos, r: ResId| #[trigger] holds(s, p1, r) && #[trigger] holds(s, p2, r) implies p1
        == p2 by {
        assert(p1 == Pos::Stk(0));
    }
    assert forall|p1: Pos, p2: Pos, kid: KId|
        fresh_once(s, kid) && #[trigger] holdsk(s, p1, kid) && #[trigger] holdsk(s, p2, kid) implies p1
        == p2 by {}
}

} // verus!
