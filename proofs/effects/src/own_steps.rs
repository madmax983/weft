//! # Preservation of `inv_b` by each step

use vstd::prelude::*;
use crate::model::*;
use crate::checker::*;
use crate::scope::*;
use crate::scope_steps::*;
use crate::own::*;

verus! {

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// `f2` holds what `f` holds, and has the same checker state for slots and `k`.
pub open spec fn same_hold(prog: Prog, f: CFrame, f2: CFrame) -> bool {
    &&& f2.slots == f.slots
    &&& f2.k == f.k
    &&& f2.block == f.block
    &&& code_ok(prog, f2)
    &&& ss_of(prog, f2).lin == ss_of(prog, f).lin
    &&& ss_of(prog, f2).k == ss_of(prog, f).k
}

/// `s2` keeps the resources of `f` live with the same flags, and keeps the
/// continuation of `f` with the same mode and use.
pub open spec fn keeps(s: State, s2: State, f: CFrame) -> bool {
    &&& forall|sl: Slot|
        #[trigger] f.slots.contains_key(sl) ==> live(s2, f.slots[sl]) && s2.res[f.slots[sl]].on_abort
            == s.res[f.slots[sl]].on_abort
    &&& f.k is Some ==> s2.konts.contains_key(f.k->0) && s2.konts[f.k->0].multi == s.konts[f.k->0].multi
        && s2.konts[f.k->0].used == s.konts[f.k->0].used
}

/// A good frame moves to `s2` (possibly with a new pc and a weaker kind).
pub proof fn lemma_good_move(
    prog: Prog,
    s: State,
    s2: State,
    f: CFrame,
    f2: CFrame,
    full: bool,
    abort: bool,
    full2: bool,
    abort2: bool,
)
    requires
        frame_good(prog, s, f, full, abort),
        same_hold(prog, f, f2),
        keeps(s, s2, f),
        full2 ==> full,
        abort2 ==> abort,
    ensures
        frame_good(prog, s2, f2, full2, abort2),
{
    assert forall|sl: Slot| #[trigger] f2.slots.contains_key(sl) implies ss_of(prog, f2).lin.contains_key(sl)
        && live(s2, f2.slots[sl]) && s2.res[f2.slots[sl]].on_abort == ss_of(prog, f2).lin[sl] by {
        assert(f.slots.contains_key(sl));
    }
}

/// A frame with no slots, no live checker slots and no continuation is good.
pub proof fn lemma_good_empty(prog: Prog, s: State, f: CFrame)
    requires
        code_ok(prog, f),
        f.slots == Map::<Slot, ResId>::empty(),
        ss_of(prog, f).lin == Map::<Slot, bool>::empty(),
        f.k is None,
    ensures
        frame_good(prog, s, f, true, true),
{
}

/// `clean` survives when continuations are only added or marked used.
pub proof fn lemma_clean_mono(prog: Prog, s: State, s2: State, f: CFrame)
    requires
        clean(prog, s, f),
        forall|k: KId| #[trigger] s.konts.contains_key(k) ==> s2.konts.contains_key(k)
            && s2.konts[k].multi == s.konts[k].multi && (s.konts[k].used ==> s2.konts[k].used),
        k_known(s, f),
    ensures
        clean(prog, s2, f),
{
}

/// `b_multi` survives when continuations are only added (once, or clean) or
/// marked used, and frames do not change.
pub proof fn lemma_multi_mono(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        b_multi(prog, s),
        forall|k: KId| #[trigger] s.konts.contains_key(k) ==> s2.konts.contains_key(k)
            && s2.konts[k].multi == s.konts[k].multi && s2.konts[k].frames == s.konts[k].frames
            && (s.konts[k].used ==> s2.konts[k].used),
        forall|k: KId|
            #[trigger] s2.konts.contains_key(k) && !s.konts.contains_key(k) && s2.konts[k].multi ==> all_clean(
                prog,
                s2,
                s2.konts[k].frames,
            ),
    ensures
        b_multi(prog, s2),
{
    assert forall|k: KId| #[trigger] s2.konts.contains_key(k) && s2.konts[k].multi implies all_clean(
        prog,
        s2,
        s2.konts[k].frames,
    ) by {
        if s.konts.contains_key(k) {
            let fr = s.konts[k].frames;
            assert(kont_ok(prog, s, s.konts[k]));
            assert forall|i: int| 0 <= i < fr.len() && #[trigger] fr[i] is Code implies clean(
                prog,
                s2,
                fr[i]->Code_0,
            ) by {
                assert(all_clean(prog, s, fr));
                assert(frame_ok(prog, s, fr[i]));
                lemma_clean_mono(prog, s, s2, fr[i]->Code_0);
            }
        }
    }
}

/// `b_order` survives when continuation frames do not change, a continuation
/// is only added with a fresh id, and continuations are marked used.
pub proof fn lemma_order_mono(s: State, s2: State)
    requires
        b_order(s),
        forall|k: KId| #[trigger] fresh_once(s2, k) && s.konts.contains_key(k) ==> fresh_once(s, k)
            && s2.konts[k].frames == s.konts[k].frames,
        forall|k: KId| #[trigger] fresh_once(s2, k) && !s.konts.contains_key(k) ==> false,
    ensures
        b_order(s2),
{
    assert forall|k2: KId, i: nat, kid: KId| #[trigger] holdsk(s2, Pos::Knt(k2, i), kid) && fresh_once(s2, kid) implies kid
        < k2 by {
        assert(fresh_once(s2, k2));
        assert(holdsk(s, Pos::Knt(k2, i), kid));
    }
}

// ---------------------------------------------------------------------------
// The capture rule (the flow argument)
// ---------------------------------------------------------------------------

/// A suspended frame that passes up capability `h`, whose effect has an
/// operation of mode `mode`, satisfies the abort rule or the multi rule.
pub proof fn lemma_up_rule(prog: Prog, s: State, f: CFrame, h: HId, mode: Mode)
    requires
        check(prog),
        cf_ok(prog, s, f),
        suspended(prog, f),
        up_has(prog, f, h),
        s.hinfo.contains_key(h),
        has_mode(prog, s.hinfo[h].eff, mode),
    ensures
        mode == Mode::Once ==> all_abortable(ss_of(prog, f)),
        mode == Mode::Multi ==> all_many(sig_of(prog, f), ss_of(prog, f)),
{
    lemma_susp_ss(prog, f);
    let pre = ss_at(prog, f.block, (f.pc - 1) as nat);
    let ss = ss_of(prog, f);
    let sig = sig_of(prog, f);
    match susp_instr(prog, f) {
        Instr::Call { block, caps } => {
            let jj = choose|jj: int| 0 <= jj < caps.len() && f.env[#[trigger] caps[jj] as int] == h;
            assert(caps[jj] < pre.env.len());
            assert(ss.env[caps[jj] as int] == pre.env[caps[jj] as int]);
            assert(s.hinfo[f.env[caps[jj] as int]].eff == ss.env[caps[jj] as int]);
            assert(has_mode(prog, prog.blocks[block].sig.caps[jj], mode));
            assert(any_mode(prog, prog.blocks[block].sig.caps, mode));
        },
        Instr::Handle { eff, clauses, body } => {
            let m = choose|m: int| 0 <= m < f.env.len() && f.env[m] == h;
            assert(s.hinfo[f.env[m]].eff == ss.env[m]);
            if m < pre.env.len() {
                assert(ss.env[m] == pre.env[m]);
                assert(has_mode(prog, pre.env[m], mode));
            } else {
                let jr = m - pre.env.len();
                let rets = prog.blocks[body].sig.rets;
                assert(rets[jr] < pre.env.len());
                assert(ss.env[m] == pre.env.push(eff)[rets[jr] as int]);
                assert(ss.env[m] == pre.env[rets[jr] as int]);
                assert(has_mode(prog, pre.env[rets[jr] as int], mode));
            }
            assert(any_mode(prog, pre.env, mode));
        },
        Instr::Resume => {
            let m = choose|m: int| 0 <= m < f.env.len() && f.env[m] == h;
            assert(s.hinfo[f.env[m]].eff == ss.env[m]);
            assert(has_mode(prog, pre.env[m], mode));
            assert(any_mode(prog, pre.env, mode));
        },
        _ => {},
    }
}

/// The frames that a perform captures satisfy the abort rule (for a `once`
/// operation) or the multi rule (for a `multi` operation).
pub proof fn lemma_capture_rules(prog: Prog, s: State, cap: nat, op: nat, j: int)
    requires
        check(prog),
        inv_a(prog, s),
        at_instr(prog, s),
        instr_at(prog, tf(s)) == (Instr::Perform { cap, op }),
        perform_ok_dyn(prog, s, cap, op, j),
    ensures
        forall|m: int|
            j < m < s.stack.len() && #[trigger] s.stack[m] is Code ==> {
                let g = s.stack[m]->Code_0;
                &&& op_mode(prog, s, tf(s).env[cap as int], op) == Mode::Once ==> all_abortable(ss_of(prog, g))
                &&& op_mode(prog, s, tf(s).env[cap as int], op) == Mode::Multi ==> all_many(
                    sig_of(prog, g),
                    ss_of(prog, g),
                )
            },
{
    let f = tf(s);
    let st = s.stack;
    let t = st.len() - 1;
    let c = f.env[cap as int];
    let mode = op_mode(prog, s, c, op);
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    let ss = ss_of(prog, f);
    assert(f.env.contains(c));
    assert(s.hinfo[c].eff == ss.env[cap as int]);
    assert(has_mode(prog, s.hinfo[c].eff, mode));
    assert forall|m: int| j < m < s.stack.len() && #[trigger] s.stack[m] is Code implies {
        let g = s.stack[m]->Code_0;
        &&& mode == Mode::Once ==> all_abortable(ss_of(prog, g))
        &&& mode == Mode::Multi ==> all_many(sig_of(prog, g), ss_of(prog, g))
    } by {
        if m < t {
            let g = st[m]->Code_0;
            assert(code_susp(prog, st, m));
            assert(frame_ok(prog, s, st[m]));
            assert(scope_at(prog, s, st, m, t));
            assert(reaches(s, st[t], c));
            if hid_in(st, m + 1, t, c) {
                let m2 = choose|m2: int| m + 1 <= m2 < t && 0 <= m2 < st.len() && #[trigger] is_handler(st[m2], c);
                assert(!is_handler(st[m2], c));
            }
            lemma_up_rule(prog, s, g, c, mode);
        }
    }
}

// ---------------------------------------------------------------------------
// Steps that remove a position holding nothing
// ---------------------------------------------------------------------------

/// `inv_b` survives when `s2` drops some positions of `s` that hold nothing.
pub proof fn lemma_b_subset(prog: Prog, s: State, s2: State)
    requires
        inv_b(prog, s),
        s2.res == s.res,
        s2.konts == s.konts,
        forall|p: Pos| #[trigger] ocode(s2, p) ==> ocode(s, p) && cf_at(s2, p) == cf_at(s, p),
        forall|q: Pos|
            #[trigger] ocode(s, q) && !ocode(s2, q) ==> !nonempty(cf_at(s, q).slots) && !holds_fresh(
                s,
                cf_at(s, q),
            ),
    ensures
        inv_b(prog, s2),
{
    assert forall|p: Pos| #[trigger] ocode(s2, p) implies pos_ok(prog, s2, p) by {
        assert(pos_ok(prog, s, p));
    }
    let id = |p: Pos| p;
    assert forall|q: Pos, r: ResId| #[trigger] holds(s, q, r) && live(s2, r) implies holds(s2, id(q), r) by {
        if !ocode(s2, q) {
            let sl = choose|sl: Slot| #[trigger] cf_at(s, q).slots.contains_key(sl) && cf_at(s, q).slots[sl] == r;
            assert(nonempty(cf_at(s, q).slots));
        }
    }
    assert forall|q: Pos, kid: KId| #[trigger] holdsk(s, q, kid) && fresh_once(s2, kid) && s.konts.contains_key(kid) implies holdsk(
        s2,
        id(q),
        kid,
    ) by {}
    assert forall|p: Pos, r: ResId| #[trigger] holds(s2, p, r) && live(s, r) implies holds(s, id(p), r) by {}
    assert forall|p: Pos, kid: KId|
        #[trigger] holdsk(s2, p, kid) && fresh_once(s2, kid) && s.konts.contains_key(kid) implies holdsk(
        s,
        id(p),
        kid,
    ) by {}
    assert(relabel_ok(s, s2, id, id));
    lemma_relabel(s, s2, id, id);
    assert forall|k2: KId, i: nat, kid: KId| #[trigger] holdsk(s2, Pos::Knt(k2, i), kid) && fresh_once(s2, kid) implies kid
        < k2 by {
        assert(holdsk(s, Pos::Knt(k2, i), kid));
    }
    assert forall|k: KId| #[trigger] s2.konts.contains_key(k) && s2.konts[k].multi implies all_clean(
        prog,
        s2,
        s2.konts[k].frames,
    ) by {
        assert(all_clean(prog, s, s.konts[k].frames));
    }
}

pub proof fn lemma_b_pop(prog: Prog, s: State, s2: State)
    requires
        inv_b(prog, s),
        step_pop(s, s2),
    ensures
        inv_b(prog, s2),
{
    assert forall|p: Pos| #[trigger] ocode(s2, p) implies ocode(s, p) && cf_at(s2, p) == cf_at(s, p) by {}
    assert forall|q: Pos| #[trigger] ocode(s, q) && !ocode(s2, q) implies !nonempty(cf_at(s, q).slots)
        && !holds_fresh(s, cf_at(s, q)) by {
        assert(q == Pos::Stk((s.stack.len() - 1) as nat));
    }
    lemma_b_subset(prog, s, s2);
}

pub proof fn lemma_b_unwind_pop(prog: Prog, s: State, s2: State)
    requires
        inv_b(prog, s),
        step_unwind_pop(s, s2),
    ensures
        inv_b(prog, s2),
{
    assert forall|p: Pos| #[trigger] ocode(s2, p) implies ocode(s, p) && cf_at(s2, p) == cf_at(s, p) by {}
    assert forall|q: Pos| #[trigger] ocode(s, q) && !ocode(s2, q) implies !nonempty(cf_at(s, q).slots)
        && !holds_fresh(s, cf_at(s, q)) by {
        assert(q == Pos::Pnd((s.pending.len() - 1) as nat));
    }
    lemma_b_subset(prog, s, s2);
}

// ---------------------------------------------------------------------------
// Steps that change one position and push empty frames
// ---------------------------------------------------------------------------

/// A new stack frame that holds nothing.
pub open spec fn empty_new(prog: Prog, s2: State, p: Pos) -> bool {
    &&& p is Stk
    &&& cf_at(s2, p).slots == Map::<Slot, ResId>::empty()
    &&& cf_at(s2, p).k is None
    &&& frame_good(prog, s2, cf_at(s2, p), true, false)
}

/// The resources of `f` (old) and `f2` (new) at the changed position.
pub open spec fn local_res_ok(s: State, s2: State, f: CFrame, f2: CFrame) -> bool {
    &&& forall|r: ResId| #[trigger] has_res(f2.slots, r) && live(s, r) ==> has_res(f.slots, r)
    &&& forall|r: ResId| #[trigger] has_res(f.slots, r) && live(s2, r) ==> has_res(f2.slots, r)
    &&& forall|r: ResId| #[trigger] live(s2, r) && !live(s, r) ==> has_res(f2.slots, r)
    &&& forall|r: ResId|
        #[trigger] live(s, r) && !has_res(f.slots, r) ==> live(s2, r) && s2.res[r].on_abort == s.res[r].on_abort
}

/// `inv_b` survives a step that changes position `p0` and adds empty stack frames.
pub proof fn lemma_b_local(prog: Prog, s: State, s2: State, p0: Pos)
    requires
        inv_b(prog, s),
        s2.konts == s.konts,
        !(p0 is Knt),
        ocode(s, p0),
        ocode(s2, p0),
        cf_at(s2, p0).k == cf_at(s, p0).k,
        frame_good(prog, s2, cf_at(s2, p0), !(p0 is Pnd), !(p0 is Stk)),
        local_res_ok(s, s2, cf_at(s, p0), cf_at(s2, p0)),
        forall|p: Pos|
            #[trigger] ocode(s2, p) && p != p0 ==> (ocode(s, p) && cf_at(s2, p) == cf_at(s, p)) || empty_new(
                prog,
                s2,
                p,
            ),
        forall|q: Pos| #[trigger] ocode(s, q) && q != p0 ==> ocode(s2, q) && cf_at(s2, q) == cf_at(s, q),
    ensures
        inv_b(prog, s2),
{
    let f = cf_at(s, p0);
    let f2 = cf_at(s2, p0);
    assert forall|p: Pos| #[trigger] ocode(s2, p) implies pos_ok(prog, s2, p) by {
        if p != p0 && ocode(s, p) && cf_at(s2, p) == cf_at(s, p) {
            let g = cf_at(s, p);
            assert(pos_ok(prog, s, p));
            assert forall|sl: Slot| #[trigger] g.slots.contains_key(sl) implies live(s2, g.slots[sl])
                && s2.res[g.slots[sl]].on_abort == s.res[g.slots[sl]].on_abort by {
                let r = g.slots[sl];
                assert(holds(s, p, r));
                if has_res(f.slots, r) {
                    assert(holds(s, p0, r));
                }
            }
            lemma_good_move(prog, s, s2, g, g, !(p is Pnd), !(p is Stk), !(p is Pnd), !(p is Stk));
        }
    }
    let id = |p: Pos| p;
    assert forall|p: Pos, r: ResId| #[trigger] holds(s2, p, r) && live(s, r) implies holds(s, id(p), r) by {
        if p == p0 {
            assert(has_res(f2.slots, r));
        } else if ocode(s, p) && cf_at(s2, p) == cf_at(s, p) {
        } else {
            let sl = choose|sl: Slot| #[trigger] cf_at(s2, p).slots.contains_key(sl) && cf_at(s2, p).slots[sl] == r;
        }
    }
    assert forall|p1: Pos, p2: Pos, r: ResId|
        #[trigger] holds(s2, p1, r) && #[trigger] holds(s2, p2, r) && !live(s, r) implies p1 == p2 by {
        assert forall|p: Pos| holds(s2, p, r) && p != p0 implies false by {
            if ocode(s, p) && cf_at(s2, p) == cf_at(s, p) {
                assert(holds(s, p, r));
                assert(pos_ok(prog, s, p));
                let sl = choose|sl: Slot| #[trigger] cf_at(s, p).slots.contains_key(sl) && cf_at(s, p).slots[sl] == r;
            } else {
                let sl = choose|sl: Slot| #[trigger] cf_at(s2, p).slots.contains_key(sl) && cf_at(s2, p).slots[sl] == r;
            }
        }
    }
    assert forall|q: Pos, r: ResId| #[trigger] holds(s, q, r) && live(s2, r) implies holds(s2, id(q), r) by {
        if q == p0 {
            assert(has_res(f.slots, r));
        }
    }
    assert forall|r: ResId| #[trigger] live(s2, r) && !live(s, r) implies exists|p: Pos| #[trigger] holds(s2, p, r) by {
        assert(holds(s2, p0, r));
    }
    assert forall|p: Pos, kid: KId|
        #[trigger] holdsk(s2, p, kid) && fresh_once(s2, kid) && s.konts.contains_key(kid) implies holdsk(
        s,
        id(p),
        kid,
    ) by {
        if p != p0 && !(ocode(s, p) && cf_at(s2, p) == cf_at(s, p)) {
            assert(empty_new(prog, s2, p));
        }
    }
    assert forall|q: Pos, kid: KId| #[trigger] holdsk(s, q, kid) && fresh_once(s2, kid) && s.konts.contains_key(kid) implies holdsk(
        s2,
        id(q),
        kid,
    ) by {}
    assert(relabel_ok(s, s2, id, id));
    lemma_relabel(s, s2, id, id);
    assert forall|k2: KId, i: nat, kid: KId| #[trigger] holdsk(s2, Pos::Knt(k2, i), kid) && fresh_once(s2, kid) implies kid
        < k2 by {
        let p = Pos::Knt(k2, i);
        if !(ocode(s, p) && cf_at(s2, p) == cf_at(s, p)) {
            assert(empty_new(prog, s2, p));
        }
        assert(holdsk(s, p, kid));
    }
    assert forall|k: KId| #[trigger] s2.konts.contains_key(k) && s2.konts[k].multi implies all_clean(
        prog,
        s2,
        s2.konts[k].frames,
    ) by {
        assert(all_clean(prog, s, s.konts[k].frames));
    }
}

/// The positions of a state whose stack changes only at the top and grows.
pub proof fn lemma_top_positions(s: State, s2: State, n: nat)
    requires
        running(s),
        s2.pending == s.pending,
        s2.konts == s.konts,
        s2.stack.len() == s.stack.len() + n,
        forall|i: int| 0 <= i < s.stack.len() - 1 ==> s2.stack[i] == s.stack[i],
    ensures
        forall|q: Pos|
            #[trigger] ocode(s, q) && q != Pos::Stk((s.stack.len() - 1) as nat) ==> ocode(s2, q) && cf_at(
                s2,
                q,
            ) == cf_at(s, q),
        forall|p: Pos|
            #[trigger] ocode(s2, p) && p != Pos::Stk((s.stack.len() - 1) as nat) ==> (ocode(s, p) && cf_at(
                s2,
                p,
            ) == cf_at(s, p)) || (p is Stk && p->Stk_0 >= s.stack.len()),
{
}

pub proof fn lemma_b_acquire(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
        step_acquire(prog, s, s2),
    ensures
        inv_b(prog, s2),
{
    let f = tf(s);
    let t = (s.stack.len() - 1) as nat;
    let p0 = Pos::Stk(t);
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    match instr_at(prog, f) {
        Instr::Acquire { slot, on_abort } => {
            let rn = s.next_res;
            let f2 = CFrame { slots: f.slots.insert(slot, rn), ..adv(f) };
            assert(s2.stack[t as int] == Frame::Code(f2));
            assert(!s.res.contains_key(rn));
            assert(ocode(s, p0));
            assert(pos_ok(prog, s, p0));
            lemma_top_positions(s, s2, 0);
            // the new top frame
            let lin = ss_of(prog, f).lin;
            assert(ss_of(prog, f2).lin == lin.insert(slot, on_abort));
            assert forall|sl: Slot| #[trigger] f2.slots.contains_key(sl) implies ss_of(prog, f2).lin.contains_key(sl)
                && live(s2, f2.slots[sl]) && s2.res[f2.slots[sl]].on_abort == ss_of(prog, f2).lin[sl] by {
                if sl != slot {
                    assert(f.slots.contains_key(sl));
                }
            }
            assert forall|a: Slot, b: Slot|
                #[trigger] f2.slots.contains_key(a) && #[trigger] f2.slots.contains_key(b) && f2.slots[a] == f2.slots[b] implies a
                == b by {
                if a != slot {
                    assert(f.slots.contains_key(a));
                }
                if b != slot {
                    assert(f.slots.contains_key(b));
                }
            }
            assert forall|sl: Slot| #[trigger] ss_of(prog, f2).lin.contains_key(sl) implies f2.slots.contains_key(sl) by {
                if sl != slot {
                    assert(lin.contains_key(sl));
                }
            }
            assert(frame_good(prog, s2, f2, true, false));
            // resources
            assert forall|r: ResId| #[trigger] has_res(f2.slots, r) && live(s, r) implies has_res(f.slots, r) by {
                let sl = choose|sl: Slot| #[trigger] f2.slots.contains_key(sl) && f2.slots[sl] == r;
                assert(sl != slot);
                assert(f.slots.contains_key(sl));
            }
            assert forall|r: ResId| #[trigger] has_res(f.slots, r) && live(s2, r) implies has_res(f2.slots, r) by {
                let sl = choose|sl: Slot| #[trigger] f.slots.contains_key(sl) && f.slots[sl] == r;
                assert(f2.slots.contains_key(sl));
            }
            assert forall|r: ResId| #[trigger] live(s2, r) && !live(s, r) implies has_res(f2.slots, r) by {
                assert(f2.slots.contains_key(slot));
            }
            assert(local_res_ok(s, s2, f, f2));
            assert forall|p: Pos| #[trigger] ocode(s2, p) && p != p0 implies (ocode(s, p) && cf_at(s2, p) == cf_at(
                s,
                p,
            )) || empty_new(prog, s2, p) by {}
            lemma_b_local(prog, s, s2, p0);
        },
        _ => {},
    }
}

pub proof fn lemma_b_consume(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
        step_consume(prog, s, s2),
    ensures
        inv_b(prog, s2),
{
    let f = tf(s);
    let t = (s.stack.len() - 1) as nat;
    let p0 = Pos::Stk(t);
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    match instr_at(prog, f) {
        Instr::Consume { slot } => {
            let r0 = f.slots[slot];
            let f2 = CFrame { slots: f.slots.remove(slot), ..adv(f) };
            assert(s2.stack[t as int] == Frame::Code(f2));
            assert(ocode(s, p0));
            assert(pos_ok(prog, s, p0));
            lemma_top_positions(s, s2, 0);
            let lin = ss_of(prog, f).lin;
            assert(ss_of(prog, f2).lin == lin.remove(slot));
            assert forall|sl: Slot| #[trigger] f2.slots.contains_key(sl) implies ss_of(prog, f2).lin.contains_key(sl)
                && live(s2, f2.slots[sl]) && s2.res[f2.slots[sl]].on_abort == ss_of(prog, f2).lin[sl] by {
                assert(f.slots.contains_key(sl));
                assert(f.slots[sl] != r0);
            }
            assert forall|a: Slot, b: Slot|
                #[trigger] f2.slots.contains_key(a) && #[trigger] f2.slots.contains_key(b) && f2.slots[a] == f2.slots[b] implies a
                == b by {
                assert(f.slots.contains_key(a));
                assert(f.slots.contains_key(b));
            }
            assert forall|sl: Slot| #[trigger] ss_of(prog, f2).lin.contains_key(sl) implies f2.slots.contains_key(sl) by {
                assert(lin.contains_key(sl));
            }
            assert(frame_good(prog, s2, f2, true, false));
            assert forall|r: ResId| #[trigger] has_res(f2.slots, r) && live(s, r) implies has_res(f.slots, r) by {
                let sl = choose|sl: Slot| #[trigger] f2.slots.contains_key(sl) && f2.slots[sl] == r;
                assert(f.slots.contains_key(sl));
            }
            assert forall|r: ResId| #[trigger] has_res(f.slots, r) && live(s2, r) implies has_res(f2.slots, r) by {
                let sl = choose|sl: Slot| #[trigger] f.slots.contains_key(sl) && f.slots[sl] == r;
                assert(r != r0);
                assert(sl != slot);
                assert(f2.slots.contains_key(sl));
            }
            assert forall|r: ResId| #[trigger] live(s, r) && !has_res(f.slots, r) implies live(s2, r)
                && s2.res[r].on_abort == s.res[r].on_abort by {
                assert(f.slots.contains_key(slot));
                assert(r != r0);
            }
            assert(local_res_ok(s, s2, f, f2));
            assert forall|p: Pos| #[trigger] ocode(s2, p) && p != p0 implies (ocode(s, p) && cf_at(s2, p) == cf_at(
                s,
                p,
            )) || empty_new(prog, s2, p) by {}
            lemma_b_local(prog, s, s2, p0);
        },
        _ => {},
    }
}

/// `f2` replaces the top frame `f` with the same slots and continuation, and
/// the checker state keeps the same slots and continuation flag.
pub proof fn lemma_b_push(prog: Prog, s: State, s2: State, f2: CFrame, n: nat)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
        running(s),
        s.stack.last() is Code,
        s2.pending == s.pending,
        s2.konts == s.konts,
        s2.res == s.res,
        s2.stack.len() == s.stack.len() + n,
        forall|i: int| 0 <= i < s.stack.len() - 1 ==> s2.stack[i] == s.stack[i],
        s2.stack[s.stack.len() - 1] == Frame::Code(f2),
        same_hold(prog, tf(s), f2),
        forall|i: int|
            s.stack.len() <= i < s2.stack.len() && #[trigger] s2.stack[i] is Code ==> {
                let g = s2.stack[i]->Code_0;
                &&& code_ok(prog, g)
                &&& g.slots == Map::<Slot, ResId>::empty()
                &&& g.k is None
                &&& ss_of(prog, g).lin == Map::<Slot, bool>::empty()
            },
    ensures
        inv_b(prog, s2),
{
    let f = tf(s);
    let t = (s.stack.len() - 1) as nat;
    let p0 = Pos::Stk(t);
    assert(ocode(s, p0));
    assert(pos_ok(prog, s, p0));
    lemma_top_positions(s, s2, n);
    lemma_good_move(prog, s, s2, f, f2, true, false, true, false);
    assert(cf_at(s2, p0) == f2);
    assert(local_res_ok(s, s2, f, f2));
    assert forall|p: Pos| #[trigger] ocode(s2, p) && p != p0 implies (ocode(s, p) && cf_at(s2, p) == cf_at(s, p))
        || empty_new(prog, s2, p) by {
        if !(ocode(s, p) && cf_at(s2, p) == cf_at(s, p)) {
            let i = p->Stk_0 as int;
            assert(s2.stack[i] is Code);
            lemma_good_empty(prog, s2, cf_at(s2, p));
        }
    }
    lemma_b_local(prog, s, s2, p0);
}

pub proof fn lemma_b_call(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
        step_call(prog, s, s2),
    ensures
        inv_b(prog, s2),
{
    let f = tf(s);
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    match instr_at(prog, f) {
        Instr::Call { block, caps } => {
            let f2 = CFrame { env: f.env + call_rets(prog, f.env, block, caps), ..adv(f) };
            let callee = CFrame { block, pc: 0, env: call_env(f.env, caps), slots: Map::empty(), k: None };
            assert(block_ok(prog, block));
            assert(ss_of(prog, callee) == entry(prog.blocks[block].sig));
            assert(ss_of(prog, f2) == ss_of(prog, adv(f)));
            assert(s2.stack[s.stack.len() as int] == Frame::Code(callee));
            lemma_b_push(prog, s, s2, f2, 1);
        },
        _ => {},
    }
}

pub proof fn lemma_b_handle(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
        step_handle(prog, s, s2),
    ensures
        inv_b(prog, s2),
{
    let f = tf(s);
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    match instr_at(prog, f) {
        Instr::Handle { eff, clauses, body } => {
            let c = s.next_h;
            let benv = f.env.push(c);
            let f2 = CFrame { env: f.env + handle_rets(prog, benv, body), ..adv(f) };
            let b = CFrame { block: body, pc: 0, env: benv, slots: Map::empty(), k: None };
            assert(block_ok(prog, body));
            assert(ss_of(prog, b) == entry(prog.blocks[body].sig));
            assert(ss_of(prog, f2) == ss_of(prog, adv(f)));
            assert(s2.stack[s.stack.len() as int + 1] == Frame::Code(b));
            assert(s2.stack[s.stack.len() as int] == Frame::Handler(c));
            lemma_b_push(prog, s, s2, f2, 2);
        },
        _ => {},
    }
}

pub proof fn lemma_b_unwind_abort(prog: Prog, s: State, s2: State)
    requires
        inv_b(prog, s),
        step_unwind_abort(s, s2),
    ensures
        inv_b(prog, s2),
{
    let f = pf(s);
    let l = (s.pending.len() - 1) as nat;
    let p0 = Pos::Pnd(l);
    let sl0 = choose|sl: Slot|
        #[trigger] max_slot(pf(s).slots, sl) && slot_live(s, pf(s), sl) && s.res[pf(s).slots[sl]].on_abort
            && s2 == do_abort(s, sl);
    let r0 = f.slots[sl0];
    let f2 = CFrame { slots: f.slots.remove(sl0), ..f };
    assert(ocode(s, p0));
    assert(pos_ok(prog, s, p0));
    assert(cf_at(s2, p0) == f2);
    assert forall|sl: Slot| #[trigger] f2.slots.contains_key(sl) implies ss_of(prog, f2).lin.contains_key(sl)
        && live(s2, f2.slots[sl]) && s2.res[f2.slots[sl]].on_abort == ss_of(prog, f2).lin[sl] by {
        assert(f.slots.contains_key(sl));
        assert(f.slots[sl] != r0);
    }
    assert forall|a: Slot, b: Slot|
        #[trigger] f2.slots.contains_key(a) && #[trigger] f2.slots.contains_key(b) && f2.slots[a] == f2.slots[b] implies a
        == b by {
        assert(f.slots.contains_key(a));
        assert(f.slots.contains_key(b));
    }
    assert(frame_good(prog, s2, f2, false, true));
    assert forall|r: ResId| #[trigger] has_res(f2.slots, r) && live(s, r) implies has_res(f.slots, r) by {
        let sl = choose|sl: Slot| #[trigger] f2.slots.contains_key(sl) && f2.slots[sl] == r;
        assert(f.slots.contains_key(sl));
    }
    assert forall|r: ResId| #[trigger] has_res(f.slots, r) && live(s2, r) implies has_res(f2.slots, r) by {
        let sl = choose|sl: Slot| #[trigger] f.slots.contains_key(sl) && f.slots[sl] == r;
        assert(r != r0);
        assert(sl != sl0);
        assert(f2.slots.contains_key(sl));
    }
    assert forall|r: ResId| #[trigger] live(s, r) && !has_res(f.slots, r) implies live(s2, r)
        && s2.res[r].on_abort == s.res[r].on_abort by {
        assert(f.slots.contains_key(sl0));
        assert(r != r0);
    }
    assert(local_res_ok(s, s2, f, f2));
    assert forall|q: Pos| #[trigger] ocode(s, q) && q != p0 implies ocode(s2, q) && cf_at(s2, q) == cf_at(s, q) by {}
    assert forall|p: Pos| #[trigger] ocode(s2, p) && p != p0 implies (ocode(s, p) && cf_at(s2, p) == cf_at(s, p))
        || empty_new(prog, s2, p) by {}
    lemma_b_local(prog, s, s2, p0);
}

// ---------------------------------------------------------------------------
// Steps that move frames
// ---------------------------------------------------------------------------

/// Position `p` of `s` holds no resource and no fresh `once` continuation.
pub open spec fn hollow(s: State, p: Pos) -> bool {
    !nonempty(cf_at(s, p).slots) && !holds_fresh(s, cf_at(s, p))
}

/// The resource and continuation parts of `inv_b` survive a step that moves
/// frames. `bk` maps positions of `s2` back, `fw` maps positions of `s`
/// forward. `pn` (if `has_pn`) is a new position that holds only the new
/// continuation `kn`.
pub proof fn lemma_b_corr(
    s: State,
    s2: State,
    bk: spec_fn(Pos) -> Pos,
    fw: spec_fn(Pos) -> Pos,
    has_pn: bool,
    pn: Pos,
    kn: KId,
)
    requires
        b_unique_res(s),
        b_owned(s),
        b_unique_k(s),
        b_held_k(s),
        forall|p: Pos, r: ResId| #[trigger] holds(s, p, r) ==> live(s, r),
        forall|p: Pos| #[trigger] ocode(s, p) ==> k_known(s, cf_at(s, p)),
        s2.res == s.res,
        forall|p: Pos|
            #[trigger] ocode(s2, p) && !hollow(s2, p) && !(has_pn && p == pn) ==> ocode(s, bk(p)) && cf_at(
                s2,
                p,
            ).slots == cf_at(s, bk(p)).slots && (cf_at(s2, p).k == cf_at(s, bk(p)).k || cf_at(s2, p).k is None),
        forall|p: Pos, q: Pos| #[trigger] ocode(s2, p) && #[trigger] ocode(s2, q) && p != q ==> bk(p) != bk(q),
        forall|q: Pos|
            #[trigger] ocode(s, q) && nonempty(cf_at(s, q).slots) ==> ocode(s2, fw(q)) && !(has_pn && fw(q)
                == pn) && cf_at(s2, fw(q)).slots == cf_at(s, q).slots,
        forall|q: Pos|
            #[trigger] ocode(s, q) && holds_fresh(s, cf_at(s, q)) && fresh_once(s2, cf_at(s, q).k->0) ==> ocode(
                s2,
                fw(q),
            ) && !(has_pn && fw(q) == pn) && cf_at(s2, fw(q)).k == cf_at(s, q).k,
        has_pn ==> ocode(s2, pn) && !nonempty(cf_at(s2, pn).slots) && cf_at(s2, pn).k == Some(kn)
            && !s.konts.contains_key(kn),
        forall|k: KId| #[trigger] fresh_once(s2, k) && s.konts.contains_key(k) ==> fresh_once(s, k),
        forall|k: KId| #[trigger] fresh_once(s2, k) && !s.konts.contains_key(k) ==> has_pn && k == kn,
    ensures
        b_unique_res(s2),
        b_owned(s2),
        b_unique_k(s2),
        b_held_k(s2),
{
    assert forall|p: Pos, r: ResId| #[trigger] holds(s2, p, r) && live(s, r) implies holds(s, bk(p), r) by {
        let sl = choose|sl: Slot| #[trigger] cf_at(s2, p).slots.contains_key(sl) && cf_at(s2, p).slots[sl] == r;
        assert(nonempty(cf_at(s2, p).slots));
        assert(cf_at(s, bk(p)).slots.contains_key(sl));
    }
    assert forall|p1: Pos, p2: Pos, r: ResId|
        #[trigger] holds(s2, p1, r) && #[trigger] holds(s2, p2, r) && !live(s, r) implies p1 == p2 by {
        let sl = choose|sl: Slot| #[trigger] cf_at(s2, p1).slots.contains_key(sl) && cf_at(s2, p1).slots[sl] == r;
        assert(nonempty(cf_at(s2, p1).slots));
        assert(cf_at(s, bk(p1)).slots.contains_key(sl));
        assert(holds(s, bk(p1), r));
    }
    assert forall|q: Pos, r: ResId| #[trigger] holds(s, q, r) && live(s2, r) implies holds(s2, fw(q), r) by {
        let sl = choose|sl: Slot| #[trigger] cf_at(s, q).slots.contains_key(sl) && cf_at(s, q).slots[sl] == r;
        assert(nonempty(cf_at(s, q).slots));
        assert(cf_at(s2, fw(q)).slots.contains_key(sl));
    }
    assert forall|p: Pos, kid: KId|
        #[trigger] holdsk(s2, p, kid) && fresh_once(s2, kid) && s.konts.contains_key(kid) implies holdsk(
        s,
        bk(p),
        kid,
    ) by {
        assert(holds_fresh(s2, cf_at(s2, p)));
    }
    assert forall|p1: Pos, p2: Pos, kid: KId|
        #[trigger] holdsk(s2, p1, kid) && #[trigger] holdsk(s2, p2, kid) && fresh_once(s2, kid)
            && !s.konts.contains_key(kid) implies p1 == p2 by {
        assert forall|p: Pos| holdsk(s2, p, kid) implies p == pn by {
            if !(has_pn && p == pn) {
                assert(holds_fresh(s2, cf_at(s2, p)));
                assert(ocode(s, bk(p)));
                assert(k_known(s, cf_at(s, bk(p))));
            }
        }
    }
    assert forall|q: Pos, kid: KId| #[trigger] holdsk(s, q, kid) && fresh_once(s2, kid) && s.konts.contains_key(kid) implies holdsk(
        s2,
        fw(q),
        kid,
    ) by {
        assert(holds_fresh(s, cf_at(s, q)));
    }
    assert forall|kid: KId| #[trigger] fresh_once(s2, kid) && !s.konts.contains_key(kid) implies exists|p: Pos| #[trigger] holdsk(
        s2,
        p,
        kid,
    ) by {
        assert(holdsk(s2, pn, kid));
    }
    assert(relabel_ok(s, s2, bk, fw));
    lemma_relabel(s, s2, bk, fw);
}

/// Facts from `b_pos` that `lemma_b_corr` needs.
pub proof fn lemma_b_pos_facts(prog: Prog, s: State)
    requires
        b_pos(prog, s),
    ensures
        forall|p: Pos, r: ResId| #[trigger] holds(s, p, r) ==> live(s, r),
        forall|p: Pos| #[trigger] ocode(s, p) ==> k_known(s, cf_at(s, p)),
{
    assert forall|p: Pos, r: ResId| #[trigger] holds(s, p, r) implies live(s, r) by {
        assert(pos_ok(prog, s, p));
        let sl = choose|sl: Slot| #[trigger] cf_at(s, p).slots.contains_key(sl) && cf_at(s, p).slots[sl] == r;
    }
    assert forall|p: Pos| #[trigger] ocode(s, p) implies k_known(s, cf_at(s, p)) by {
        assert(pos_ok(prog, s, p));
    }
}

/// The frames of a fresh `once` continuation do not hold that continuation.
pub proof fn lemma_no_self_hold(s: State, kid: KId, m: nat)
    requires
        b_order(s),
        fresh_once(s, kid),
    ensures
        !holdsk(s, Pos::Knt(kid, m), kid),
{
}

/// Only one position holds a fresh `once` continuation.
pub proof fn lemma_sole_holder(s: State, kid: KId, p: Pos, q: Pos)
    requires
        b_unique_k(s),
        fresh_once(s, kid),
        holdsk(s, p, kid),
        ocode(s, q),
        q != p,
    ensures
        cf_at(s, q).k != Some(kid),
{
    if cf_at(s, q).k == Some(kid) {
        assert(holdsk(s, q, kid));
    }
}

/// `kid` marked used: the other continuations keep their state.
pub proof fn lemma_keeps_used(s: State, s2: State, kid: KId, f: CFrame)
    requires
        s2.res == s.res,
        s2.konts == s.konts.insert(kid, Kont { used: true, ..s.konts[kid] }),
        f.k != Some(kid),
        k_known(s, f),
        forall|sl: Slot| #[trigger] f.slots.contains_key(sl) ==> live(s, f.slots[sl]),
    ensures
        keeps(s, s2, f),
{
}

pub proof fn lemma_b_return_drop(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        inv_b(prog, s),
        step_return(prog, s, s2),
        holds_fresh(s, tf(s)),
    ensures
        inv_b(prog, s2),
{
    let f = tf(s);
    let t = (s.stack.len() - 1) as nat;
    let kid = f.k->0;
    let kf = s.konts[kid].frames;
    let ptop = Pos::Stk(t);
    assert(s2.pending == kf);
    assert(ocode(s, ptop));
    assert(holdsk(s, ptop, kid));
    lemma_b_pos_facts(prog, s);
    let bk = |p: Pos|
        match p {
            Pos::Pnd(m) => Pos::Knt(kid, m),
            _ => p,
        };
    let fw = |q: Pos|
        match q {
            Pos::Knt(k, m) => if k == kid {
                Pos::Pnd(m)
            } else {
                q
            },
            _ => q,
        };
    assert forall|k: KId| #[trigger] fresh_once(s2, k) && s.konts.contains_key(k) implies fresh_once(s, k) by {}
    // positions of s2 come from s
    assert forall|p: Pos| #[trigger] ocode(s2, p) implies ocode(s, bk(p)) && cf_at(s2, p) == cf_at(s, bk(p))
        && p != ptop && (p is Pnd ==> bk(p) is Knt) && (!(p is Pnd) ==> bk(p) == p) by {}
    assert forall|q: Pos| #[trigger] ocode(s, q) && q != ptop implies ocode(s2, fw(q)) && cf_at(s2, fw(q)) == cf_at(s, q)
        by {
        match q {
            Pos::Knt(k, m) => {
                if k != kid {
                    assert(fresh_once(s2, k));
                }
            },
            _ => {},
        }
    }
    assert forall|q: Pos| #[trigger] ocode(s, q) && nonempty(cf_at(s, q).slots) implies ocode(s2, fw(q)) && !(false
        && fw(q) == ptop) && cf_at(s2, fw(q)).slots == cf_at(s, q).slots by {
        assert(q != ptop);
    }
    assert forall|q: Pos| #[trigger] ocode(s, q) && holds_fresh(s, cf_at(s, q)) && fresh_once(s2, cf_at(s, q).k->0) implies ocode(
        s2,
        fw(q),
    ) && !(false && fw(q) == ptop) && cf_at(s2, fw(q)).k == cf_at(s, q).k by {
        assert(q != ptop);
    }
    lemma_b_corr(s, s2, bk, fw, false, ptop, 0);
    // b_pos
    assert forall|p: Pos| #[trigger] ocode(s2, p) implies pos_ok(prog, s2, p) by {
        let q = bk(p);
        assert(pos_ok(prog, s, q));
        let g = cf_at(s, q);
        if q is Knt && q->Knt_0 == kid {
            lemma_no_self_hold(s, kid, q->Knt_1);
        } else {
            lemma_sole_holder(s, kid, ptop, q);
        }
        lemma_keeps_used(s, s2, kid, g);
        lemma_good_move(prog, s, s2, g, g, !(q is Pnd), !(q is Stk), !(p is Pnd), !(p is Stk));
    }
    // order and multi
    lemma_order_mono(s, s2);
    lemma_multi_mono(prog, s, s2);
}

pub proof fn lemma_b_return(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        inv_b(prog, s),
        step_return(prog, s, s2),
    ensures
        inv_b(prog, s2),
{
    if holds_fresh(s, tf(s)) {
        lemma_b_return_drop(prog, s, s2);
    } else {
        let t = (s.stack.len() - 1) as nat;
        assert forall|p: Pos| #[trigger] ocode(s2, p) implies ocode(s, p) && cf_at(s2, p) == cf_at(s, p) by {}
        assert forall|q: Pos| #[trigger] ocode(s, q) && !ocode(s2, q) implies !nonempty(cf_at(s, q).slots)
            && !holds_fresh(s, cf_at(s, q)) by {
            assert(q == Pos::Stk(t));
        }
        lemma_b_subset(prog, s, s2);
    }
}

/// Clearing the continuation of a good frame keeps it good.
pub proof fn lemma_good_clear_k(prog: Prog, s: State, s2: State, f: CFrame, full: bool, abort: bool)
    requires
        frame_good(prog, s, f, full, abort),
        s2.res == s.res,
    ensures
        frame_good(prog, s2, CFrame { k: None, ..f }, full, abort),
{
    let f2 = CFrame { k: None, ..f };
    assert(ss_of(prog, f2) == ss_of(prog, f));
}

pub proof fn lemma_b_unwind_drop(prog: Prog, s: State, s2: State)
    requires
        inv_b(prog, s),
        step_unwind_drop(s, s2),
    ensures
        inv_b(prog, s2),
{
    let f = pf(s);
    let l = (s.pending.len() - 1) as nat;
    let kid = f.k->0;
    let kf = s.konts[kid].frames;
    let ptop = Pos::Pnd(l);
    let f1 = CFrame { k: None, ..f };
    assert(ocode(s, ptop));
    assert(holdsk(s, ptop, kid));
    lemma_b_pos_facts(prog, s);
    assert forall|i: int| 0 <= i < l implies s2.pending[i] == s.pending[i] by {}
    assert(s2.pending[l as int] == Frame::Code(f1));
    assert forall|m: int| 0 <= m < kf.len() implies s2.pending[l + 1 + m] == kf[m] by {}
    let bk = |p: Pos|
        match p {
            Pos::Pnd(i) => if i > l {
                Pos::Knt(kid, (i - l - 1) as nat)
            } else {
                p
            },
            _ => p,
        };
    let fw = |q: Pos|
        match q {
            Pos::Knt(k, m) => if k == kid {
                Pos::Pnd(l + 1 + m)
            } else {
                q
            },
            _ => q,
        };
    assert forall|k: KId| #[trigger] fresh_once(s2, k) && s.konts.contains_key(k) implies fresh_once(s, k) by {}
    assert forall|p: Pos| #[trigger] ocode(s2, p) && p != ptop implies ocode(s, bk(p)) && cf_at(s2, p) == cf_at(
        s,
        bk(p),
    ) && bk(p) != ptop by {
        match p {
            Pos::Pnd(i) => {
                if i > l {
                    assert(s2.pending[i as int] == kf[i - l - 1]);
                }
            },
            _ => {},
        }
    }
    assert(ocode(s2, ptop) && cf_at(s2, ptop) == f1);
    assert forall|q: Pos| #[trigger] ocode(s, q) && q != ptop implies ocode(s2, fw(q)) && cf_at(s2, fw(q)) == cf_at(
        s,
        q,
    ) && fw(q) != ptop by {
        match q {
            Pos::Knt(k, m) => {
                if k != kid {
                    assert(fresh_once(s2, k));
                } else {
                    assert(s2.pending[(l + 1 + m) as int] == kf[m as int]);
                }
            },
            _ => {},
        }
    }
    assert forall|p: Pos, q: Pos| #[trigger] ocode(s2, p) && #[trigger] ocode(s2, q) && p != q implies bk(p) != bk(q) by {
        if p != ptop && q != ptop {
            assert(fw(bk(p)) == p) by {
                match p {
                    Pos::Pnd(i) => {},
                    _ => {},
                }
            }
            assert(fw(bk(q)) == q) by {
                match q {
                    Pos::Pnd(i) => {},
                    _ => {},
                }
            }
        }
    }
    lemma_b_corr(s, s2, bk, fw, false, ptop, 0);
    assert forall|p: Pos| #[trigger] ocode(s2, p) implies pos_ok(prog, s2, p) by {
        if p == ptop {
            assert(pos_ok(prog, s, ptop));
            lemma_good_clear_k(prog, s, s2, f, false, true);
        } else {
            let q = bk(p);
            assert(pos_ok(prog, s, q));
            let g = cf_at(s, q);
            if q is Knt && q->Knt_0 == kid {
                lemma_no_self_hold(s, kid, q->Knt_1);
            } else {
                lemma_sole_holder(s, kid, ptop, q);
            }
            lemma_keeps_used(s, s2, kid, g);
            lemma_good_move(prog, s, s2, g, g, !(q is Pnd), !(q is Stk), !(p is Pnd), !(p is Stk));
        }
    }
    lemma_order_mono(s, s2);
}

pub proof fn lemma_b_cancel(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
        step_cancel(prog, s, s2),
    ensures
        inv_b(prog, s2),
{
    let f = tf(s);
    let st = s.stack;
    let t = (st.len() - 1) as nat;
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    match instr_at(prog, f) {
        Instr::Perform { cap, op } => {
            let j = choose|j: int| #[trigger] perform_ok_dyn(prog, s, cap, op, j) && s2 == do_cancel(s, j);
            lemma_capture_rules(prog, s, cap, op, j);
            lemma_captured_index(s, j);
            assert(is_handler(st[j], f.env[cap as int]));
            assert(st[t as int] is Code);
            assert(s2.pending == captured(s, j));
            lemma_b_pos_facts(prog, s);
            let bk = |p: Pos|
                match p {
                    Pos::Pnd(m) => Pos::Stk((j + m) as nat),
                    _ => p,
                };
            let fw = |q: Pos|
                match q {
                    Pos::Stk(i) => if i >= j {
                        Pos::Pnd((i - j) as nat)
                    } else {
                        q
                    },
                    _ => q,
                };
            assert forall|p: Pos| #[trigger] ocode(s2, p) implies ocode(s, bk(p)) && same_hold(
                prog,
                cf_at(s, bk(p)),
                cf_at(s2, p),
            ) && fw(bk(p)) == p by {
                match p {
                    Pos::Pnd(m) => {
                        if m < t - j {
                            assert(cf_at(s2, p) == cf_at(s, bk(p)));
                            assert(frame_ok(prog, s, st[j + m]));
                        } else {
                            assert(cf_at(s2, p) == adv(f));
                        }
                    },
                    Pos::Stk(i) => {
                        assert(frame_ok(prog, s, st[i as int]));
                    },
                    Pos::Knt(k, m) => {
                        assert(kont_ok(prog, s, s.konts[k]));
                        assert(frame_ok(prog, s, s.konts[k].frames[m as int]));
                    },
                }
            }
            assert forall|q: Pos| #[trigger] ocode(s, q) implies ocode(s2, fw(q)) && same_hold(
                prog,
                cf_at(s, q),
                cf_at(s2, fw(q)),
            ) by {
                match q {
                    Pos::Stk(i) => {
                        assert(frame_ok(prog, s, st[i as int]));
                        if i >= j && i < t {
                            assert(s2.pending[i - j] == st[i as int]);
                        } else if i == t {
                            assert(s2.pending[t - j] == Frame::Code(adv(f)));
                        }
                    },
                    Pos::Knt(k, m) => {
                        assert(kont_ok(prog, s, s.konts[k]));
                        assert(frame_ok(prog, s, s.konts[k].frames[m as int]));
                    },
                    _ => {},
                }
            }
            assert forall|p: Pos, q: Pos| #[trigger] ocode(s2, p) && #[trigger] ocode(s2, q) && p != q implies bk(p)
                != bk(q) by {}
            lemma_b_corr(s, s2, bk, fw, false, Pos::Stk(0), 0);
            assert forall|p: Pos| #[trigger] ocode(s2, p) implies pos_ok(prog, s2, p) by {
                let q = bk(p);
                assert(pos_ok(prog, s, q));
                let g = cf_at(s, q);
                if p is Pnd {
                    let i = q->Stk_0 as int;
                    assert(st[i] is Code);
                    assert(i > j);
                    assert(all_abortable(ss_of(prog, g)));
                    assert(frame_good(prog, s, g, true, true));
                    lemma_good_move(prog, s, s2, g, cf_at(s2, p), true, true, false, true);
                } else {
                    lemma_good_move(prog, s, s2, g, cf_at(s2, p), !(q is Pnd), !(q is Stk), !(p is Pnd), !(p is Stk));
                }
            }
            lemma_order_mono(s, s2);
            lemma_multi_mono(prog, s, s2);
        },
        _ => {},
    }
}

/// A frame of `s` at an owning position is well formed (from `inv_a`).
pub proof fn lemma_owning_cf_ok(prog: Prog, s: State, q: Pos)
    requires
        inv_a(prog, s),
        ocode(s, q),
        !(q is Pnd),
    ensures
        cf_ok(prog, s, cf_at(s, q)),
{
    match q {
        Pos::Stk(i) => {
            assert(frame_ok(prog, s, s.stack[i as int]));
        },
        Pos::Knt(k, m) => {
            assert(kont_ok(prog, s, s.konts[k]));
            assert(frame_ok(prog, s, s.konts[k].frames[m as int]));
        },
        _ => {},
    }
}

/// A frame under the multi rule holds nothing and is clean.
pub proof fn lemma_many_clean(prog: Prog, s: State, s2: State, g: CFrame)
    requires
        frame_good(prog, s, g, true, false),
        cf_ok(prog, s, g),
        all_many(sig_of(prog, g), ss_of(prog, g)),
        forall|k: KId| #[trigger] s.konts.contains_key(k) ==> s2.konts.contains_key(k) && s2.konts[k] == s.konts[k],
    ensures
        clean(prog, s2, g),
        !nonempty(g.slots),
        !holds_fresh(s, g),
{
    assert forall|sl: Slot| !#[trigger] g.slots.contains_key(sl) by {
        if g.slots.contains_key(sl) {
            assert(ss_of(prog, g).lin.contains_key(sl));
        }
    }
    if g.k is Some {
        let kid = g.k->0;
        assert(k_link(prog, s, g));
        assert(s.konts.contains_key(kid));
        assert(s2.konts[kid] == s.konts[kid]);
        assert(sig_of(prog, g).kmode is Some);
        if !s.konts[kid].multi {
            assert(sig_of(prog, g).kmode != Some(Mode::Multi));
            assert(sig_of(prog, g).kmode == Some(Mode::Once));
            assert(!ss_of(prog, g).k);
            assert(k_sync(prog, s, g));
            assert(s.konts[kid].used);
        }
    }
}

pub proof fn lemma_b_perform_at(prog: Prog, s: State, cap: nat, op: nat, j: int)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
        at_instr(prog, s),
        instr_at(prog, tf(s)) == (Instr::Perform { cap, op }),
        perform_ok_dyn(prog, s, cap, op, j),
    ensures
        inv_b(prog, do_perform(prog, s, tf(s).env[cap as int], op, j)),
{
    let f = tf(s);
    let st = s.stack;
    let t = (st.len() - 1) as nat;
    let c = f.env[cap as int];
    let kn = s.next_k;
    let s2 = do_perform(prog, s, c, op, j);
    let mode = op_mode(prog, s, c, op);
    let multi = mode == Mode::Multi;
    let kf = captured(s, j);
    let cl = clause_frame(s, c, op, kn);
    let pn = Pos::Stk(j as nat);
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    lemma_capture_rules(prog, s, cap, op, j);
    lemma_captured_index(s, j);
    lemma_b_pos_facts(prog, s);
    assert(is_handler(st[j], c));
    assert(st[t as int] is Code);
    assert(j >= 1) by {
        assert(st[0] is Code);
    }
    assert(!s.konts.contains_key(kn));
    assert(s2.konts[kn] == Kont { frames: kf, multi, used: false });
    assert(s2.stack[j] == Frame::Code(cl));
    assert(forall|i: int| 0 <= i < j ==> #[trigger] s2.stack[i] == st[i]);
    // the clause frame
    let hi = s.hinfo[c];
    assert(hinfo_ok(prog, s, hi));
    assert(clause_ok(prog, s, hi, op as int));
    assert(block_ok(prog, cl.block));
    assert(ss_of(prog, cl) == entry(sig_of(prog, cl)));
    assert(frame_good(prog, s2, cl, true, false));
    // the captured frames
    assert forall|i: int| j < i <= t && #[trigger] st[i] is Code implies {
        let g = st[i]->Code_0;
        &&& frame_good(prog, s, g, true, false)
        &&& cf_ok(prog, s, g)
        &&& (multi ==> all_many(sig_of(prog, g), ss_of(prog, g)))
        &&& (!multi ==> all_abortable(ss_of(prog, g)))
    } by {
        assert(ocode(s, Pos::Stk(i as nat)));
        assert(pos_ok(prog, s, Pos::Stk(i as nat)));
        lemma_owning_cf_ok(prog, s, Pos::Stk(i as nat));
    }
    let bk = |p: Pos|
        match p {
            Pos::Knt(k, m) => if k == kn {
                Pos::Stk((j + m) as nat)
            } else {
                p
            },
            _ => p,
        };
    let fw = |q: Pos|
        match q {
            Pos::Stk(i) => if i >= j && !multi {
                Pos::Knt(kn, (i - j) as nat)
            } else {
                q
            },
            _ => q,
        };
    assert forall|k: KId| #[trigger] fresh_once(s2, k) && s.konts.contains_key(k) implies fresh_once(s, k) by {}
    assert forall|k: KId| #[trigger] fresh_once(s2, k) && !s.konts.contains_key(k) implies !multi && k == kn by {}
    // positions of s2
    assert forall|p: Pos| #[trigger] ocode(s2, p) && p != pn implies ocode(s, bk(p)) && same_hold(
        prog,
        cf_at(s, bk(p)),
        cf_at(s2, p),
    ) && fw(bk(p)) == p && (p is Knt && p->Knt_0 == kn ==> bk(p)->Stk_0 > j) by {
        match p {
            Pos::Stk(i) => {
                assert(frame_ok(prog, s, st[i as int]));
            },
            Pos::Knt(k, m) => {
                if k == kn {
                    if m < t - j {
                        assert(kf[m as int] == st[j + m]);
                        assert(frame_ok(prog, s, st[j + m]));
                    } else {
                        assert(kf[m as int] == Frame::Code(adv(f)));
                    }
                } else {
                    assert(kont_ok(prog, s, s.konts[k]));
                    assert(frame_ok(prog, s, s.konts[k].frames[m as int]));
                }
            },
            _ => {},
        }
    }
    assert forall|q: Pos| #[trigger] ocode(s, q) && (nonempty(cf_at(s, q).slots) || holds_fresh(s, cf_at(s, q)))
        implies ocode(s2, fw(q)) && fw(q) != pn && same_hold(prog, cf_at(s, q), cf_at(s2, fw(q))) by {
        match q {
            Pos::Stk(i) => {
                assert(frame_ok(prog, s, st[i as int]));
                if i >= j {
                    assert(i > j);
                    let g = st[i as int]->Code_0;
                    if multi {
                        lemma_many_clean(prog, s, s2, g);
                    }
                    if i < t {
                        assert(kf[i - j] == st[i as int]);
                    } else {
                        assert(kf[i - j] == Frame::Code(adv(f)));
                    }
                }
            },
            Pos::Knt(k, m) => {
                assert(kont_ok(prog, s, s.konts[k]));
                assert(frame_ok(prog, s, s.konts[k].frames[m as int]));
            },
            _ => {},
        }
    }
    assert forall|p: Pos, q: Pos| #[trigger] ocode(s2, p) && #[trigger] ocode(s2, q) && p != q implies bk(p) != bk(q) by {
        if p != pn && q != pn {
            assert(fw(bk(p)) == p);
            assert(fw(bk(q)) == q);
        } else if p == pn {
            if q is Knt && q->Knt_0 == kn {
                assert(bk(q)->Stk_0 > j);
            }
        } else {
            if p is Knt && p->Knt_0 == kn {
                assert(bk(p)->Stk_0 > j);
            }
        }
    }
    assert(hollow(s2, pn) || !multi);
    lemma_b_corr(s, s2, bk, fw, !multi, pn, kn);
    // b_pos
    assert forall|p: Pos| #[trigger] ocode(s2, p) implies pos_ok(prog, s2, p) by {
        if p == pn {
        } else {
            let q = bk(p);
            assert(pos_ok(prog, s, q));
            let g = cf_at(s, q);
            if p is Knt && p->Knt_0 == kn {
                let i = q->Stk_0 as int;
                assert(st[i] is Code);
                assert(frame_good(prog, s, g, true, true));
                lemma_good_move(prog, s, s2, g, cf_at(s2, p), true, true, true, true);
            } else {
                lemma_good_move(prog, s, s2, g, cf_at(s2, p), !(q is Pnd), !(q is Stk), !(p is Pnd), !(p is Stk));
            }
        }
    }
    // b_order
    assert forall|k2: KId, i: nat, kid: KId| #[trigger] holdsk(s2, Pos::Knt(k2, i), kid) && fresh_once(s2, kid) implies kid
        < k2 by {
        let p = Pos::Knt(k2, i);
        assert(ocode(s2, p));
        assert(p != pn);
        let q = bk(p);
        assert(k_known(s, cf_at(s, q)));
        if k2 != kn {
            assert(holdsk(s, p, kid));
        }
    }
    // b_multi
    if multi {
        assert forall|i: int| 0 <= i < kf.len() && #[trigger] kf[i] is Code implies clean(prog, s2, kf[i]->Code_0) by {
            assert(i > 0);
            if i < t - j {
                assert(kf[i] == st[j + i]);
                lemma_many_clean(prog, s, s2, st[j + i]->Code_0);
            } else {
                assert(kf[i] == Frame::Code(adv(f)));
                lemma_many_clean(prog, s, s2, f);
            }
        }
    }
    lemma_multi_mono(prog, s, s2);
}

pub proof fn lemma_b_perform(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
        step_perform(prog, s, s2),
    ensures
        inv_b(prog, s2),
{
    match instr_at(prog, tf(s)) {
        Instr::Perform { cap, op } => {
            let j = choose|j: int|
                #[trigger] perform_ok_dyn(prog, s, cap, op, j) && s2 == do_perform(
                    prog,
                    s,
                    tf(s).env[cap as int],
                    op,
                    j,
                );
            lemma_b_perform_at(prog, s, cap, op, j);
        },
        _ => {},
    }
}

pub proof fn lemma_b_resume(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
        step_resume(prog, s, s2),
    ensures
        inv_b(prog, s2),
{
    let f = tf(s);
    let st = s.stack;
    let t = (st.len() - 1) as nat;
    let kid = f.k->0;
    let kt = s.konts[kid];
    let kf = kt.frames;
    let once = !kt.multi;
    let ptop = Pos::Stk(t);
    let f2 = adv(f);
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    lemma_b_pos_facts(prog, s);
    assert(ocode(s, ptop));
    assert(pos_ok(prog, s, ptop));
    assert(kont_ok(prog, s, kt));
    assert(s2.stack.len() == st.len() + kf.len());
    assert(forall|i: int| 0 <= i < t ==> #[trigger] s2.stack[i] == st[i]);
    assert(s2.stack[t as int] == Frame::Code(f2));
    assert(forall|m: int| 0 <= m < kf.len() ==> s2.stack[t + 1 + m] == kf[m]);
    if once {
        assert(holdsk(s, ptop, kid));
    }
    // the frames of a multi continuation are clean
    assert forall|m: int| 0 <= m < kf.len() && #[trigger] kf[m] is Code && !once implies {
        let g = kf[m]->Code_0;
        &&& clean(prog, s, g)
        &&& cf_ok(prog, s, g)
    } by {
        assert(s.konts.contains_key(kid) && s.konts[kid].multi);
        assert(all_clean(prog, s, kf));
        assert(frame_ok(prog, s, kf[m]));
    }
    let bk = |p: Pos|
        match p {
            Pos::Stk(i) => if i > t && once {
                Pos::Knt(kid, (i - t - 1) as nat)
            } else {
                p
            },
            _ => p,
        };
    let fw = |q: Pos|
        match q {
            Pos::Knt(k, m) => if k == kid && once {
                Pos::Stk(t + 1 + m)
            } else {
                q
            },
            _ => q,
        };
    assert forall|k: KId| #[trigger] fresh_once(s2, k) && s.konts.contains_key(k) implies fresh_once(s, k) by {}
    assert forall|p: Pos| #[trigger] ocode(s2, p) && !hollow(s2, p) && p != ptop implies ocode(s, bk(p)) && cf_at(
        s2,
        p,
    ) == cf_at(s, bk(p)) && fw(bk(p)) == p by {
        match p {
            Pos::Stk(i) => {
                if i > t && !once {
                    let g = kf[i - t - 1]->Code_0;
                    assert(clean(prog, s, g));
                    assert(!nonempty(g.slots));
                    if g.k is Some {
                        assert(k_link(prog, s, g));
                    }
                    assert(hollow(s2, p));
                }
            },
            _ => {},
        }
    }
    assert(cf_at(s2, ptop) == f2);
    assert forall|q: Pos| #[trigger] ocode(s, q) && q != ptop implies ocode(s2, fw(q)) && cf_at(s2, fw(q)) == cf_at(
        s,
        q,
    ) && fw(q) != ptop by {
        match q {
            Pos::Knt(k, m) => {
                if k != kid || !once {
                    assert(fresh_once(s2, k));
                }
            },
            _ => {},
        }
    }
    assert forall|p: Pos, q: Pos| #[trigger] ocode(s2, p) && #[trigger] ocode(s2, q) && p != q implies bk(p) != bk(q) by {
        match p {
            Pos::Stk(i) => {},
            _ => {},
        }
    }
    lemma_b_corr(s, s2, bk, fw, false, ptop, 0);
    // b_pos
    assert forall|p: Pos| #[trigger] ocode(s2, p) implies pos_ok(prog, s2, p) by {
        if p == ptop {
            assert(ss_of(prog, f2).lin == ss_of(prog, f).lin);
            assert forall|sl: Slot| #[trigger] f2.slots.contains_key(sl) implies ss_of(prog, f2).lin.contains_key(sl)
                && live(s2, f2.slots[sl]) && s2.res[f2.slots[sl]].on_abort == ss_of(prog, f2).lin[sl] by {
                assert(f.slots.contains_key(sl));
            }
            if once {
                assert(sig_of(prog, f).kmode == Some(Mode::Once));
            }
            assert(frame_good(prog, s2, f2, true, false));
        } else if p is Stk && p->Stk_0 > t && !once {
            let g = cf_at(s2, p);
            let m = p->Stk_0 - t - 1;
            assert(g == kf[m as int]->Code_0);
            assert(clean(prog, s, g));
            assert(cf_ok(prog, s, g));
            if g.k is Some {
                assert(k_link(prog, s, g));
            }
            assert(frame_good(prog, s2, g, true, false));
        } else {
            let q = bk(p);
            assert(ocode(s, q));
            assert(pos_ok(prog, s, q));
            let g = cf_at(s, q);
            if once {
                if q is Knt && q->Knt_0 == kid {
                    lemma_no_self_hold(s, kid, q->Knt_1);
                } else {
                    lemma_sole_holder(s, kid, ptop, q);
                }
                lemma_keeps_used(s, s2, kid, g);
            }
            lemma_good_move(prog, s, s2, g, g, !(q is Pnd), !(q is Stk), !(p is Pnd), !(p is Stk));
        }
    }
    lemma_order_mono(s, s2);
    lemma_multi_mono(prog, s, s2);
}

/// Every step keeps `inv_b`.
pub proof fn lemma_b_step(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        inv_b(prog, s),
        step(prog, s, s2),
    ensures
        inv_b(prog, s2),
{
    if step_pop(s, s2) {
        lemma_b_pop(prog, s, s2);
    } else if step_acquire(prog, s, s2) {
        lemma_b_acquire(prog, s, s2);
    } else if step_consume(prog, s, s2) {
        lemma_b_consume(prog, s, s2);
    } else if step_call(prog, s, s2) {
        lemma_b_call(prog, s, s2);
    } else if step_handle(prog, s, s2) {
        lemma_b_handle(prog, s, s2);
    } else if step_perform(prog, s, s2) {
        lemma_b_perform(prog, s, s2);
    } else if step_cancel(prog, s, s2) {
        lemma_b_cancel(prog, s, s2);
    } else if step_resume(prog, s, s2) {
        lemma_b_resume(prog, s, s2);
    } else if step_return(prog, s, s2) {
        lemma_b_return(prog, s, s2);
    } else if step_unwind_pop(s, s2) {
        lemma_b_unwind_pop(prog, s, s2);
    } else if step_unwind_drop(s, s2) {
        lemma_b_unwind_drop(prog, s, s2);
    } else {
        lemma_b_unwind_abort(prog, s, s2);
    }
}

} // verus!
