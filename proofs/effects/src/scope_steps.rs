//! # Preservation of `inv_a` by each step

use vstd::prelude::*;
use crate::model::*;
use crate::checker::*;
use crate::scope::*;

verus! {

// ---------------------------------------------------------------------------
// Facts from the checker
// ---------------------------------------------------------------------------

/// The checker accepted the instruction of a frame.
pub proof fn lemma_instr_ok(prog: Prog, f: CFrame)
    requires
        check(prog),
        code_ok(prog, f),
    ensures
        instr_ok(prog, sig_of(prog, f), ss_of(prog, f), instr_at(prog, f)),
        block_ok(prog, f.block),
        !(instr_at(prog, f) is Return) ==> f.pc + 1 < prog.blocks[f.block].code.len(),
        ss_of(prog, adv(f)) == post(prog, sig_of(prog, f), ss_of(prog, f), instr_at(prog, f)),
{
    assert(block_ok(prog, f.block));
    let blk = prog.blocks[f.block];
    assert(instr_ok(prog, blk.sig, ss_at(prog, f.block, f.pc), blk.code[f.pc as int]));
    if f.pc + 1 == blk.code.len() {
        assert(blk.code[f.pc as int] == blk.code.last());
    }
}

/// The checker state of a suspended frame is the state after its suspension point.
pub proof fn lemma_susp_ss(prog: Prog, f: CFrame)
    requires
        check(prog),
        suspended(prog, f),
    ensures
        ss_of(prog, f) == post(
            prog,
            sig_of(prog, f),
            ss_at(prog, f.block, (f.pc - 1) as nat),
            susp_instr(prog, f),
        ),
        instr_ok(prog, sig_of(prog, f), ss_at(prog, f.block, (f.pc - 1) as nat), susp_instr(prog, f)),
{
    assert(block_ok(prog, f.block));
    let blk = prog.blocks[f.block];
    let pc0 = (f.pc - 1) as nat;
    assert(instr_ok(prog, blk.sig, ss_at(prog, f.block, pc0), blk.code[pc0 as int]));
}

/// A handler frame of `h` on `st` has a topmost one.
pub proof fn lemma_topmost_exists(st: Seq<Frame>, h: HId) -> (j: int)
    requires
        on_stack(st, h),
    ensures
        topmost(st, h, j),
    decreases st.len(),
{
    if is_handler(st.last(), h) {
        (st.len() - 1) as int
    } else {
        let st2 = st.drop_last();
        let m = choose|m: int| 0 <= m < st.len() && #[trigger] is_handler(st[m], h);
        assert(m < st.len() - 1);
        assert(is_handler(st2[m], h));
        let j = lemma_topmost_exists(st2, h);
        assert forall|j2: int| j < j2 < st.len() implies !#[trigger] is_handler(st[j2], h) by {
            if j2 < st.len() - 1 {
                assert(st[j2] == st2[j2]);
            }
        }
        j
    }
}

/// The topmost handler frame of `h` is unique.
pub proof fn lemma_topmost_unique(st: Seq<Frame>, h: HId, j1: int, j2: int)
    requires
        topmost(st, h, j1),
        topmost(st, h, j2),
    ensures
        j1 == j2,
{
    if j1 < j2 {
        assert(!is_handler(st[j2], h));
    } else if j2 < j1 {
        assert(!is_handler(st[j1], h));
    }
}

/// The top frame of a good stack in a good state.
pub proof fn lemma_top_ok(prog: Prog, s: State)
    requires
        inv_a(prog, s),
        top_code(s),
    ensures
        cf_ok(prog, s, tf(s)),
        reaches(s, s.stack.last(), 0) == tf(s).env.contains(0),
{
    assert(frame_ok(prog, s, s.stack[s.stack.len() - 1]));
}

// ---------------------------------------------------------------------------
// Steps that only shorten the stack, or do not touch it
// ---------------------------------------------------------------------------

/// `inv_a` for `s2` when the stack of `s2` is a prefix of the stack of `s`.
pub proof fn lemma_a_prefix(prog: Prog, s: State, s2: State, n: int)
    requires
        inv_a(prog, s),
        agree(s, s2),
        0 <= n <= s.stack.len(),
        s2.stack == s.stack.subrange(0, n),
        s2.konts.dom() == s.konts.dom(),
        s2.hinfo == s.hinfo,
        s2.next_k == s.next_k,
        s2.next_h == s.next_h,
        s2.res == s.res,
        s2.next_res == s.next_res,
    ensures
        inv_a(prog, s2),
{
    lemma_stack_prefix(prog, s, s.stack, n);
    lemma_stack_seq_agree(prog, s, s2, s.stack.subrange(0, n));
    lemma_rest_agree(prog, s, s2);
}

/// `kid` marked used: the state agrees with the old one.
pub proof fn lemma_agree_used(s: State, kid: KId)
    requires
        s.konts.contains_key(kid),
    ensures
        agree(s, State { konts: s.konts.insert(kid, Kont { used: true, ..s.konts[kid] }), ..s }),
        s.konts.insert(kid, Kont { used: true, ..s.konts[kid] }).dom() == s.konts.dom(),
{
    let k2 = s.konts.insert(kid, Kont { used: true, ..s.konts[kid] });
    assert(k2.dom() =~= s.konts.dom());
}

pub proof fn lemma_a_pop(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        step_pop(s, s2),
    ensures
        inv_a(prog, s2),
{
    assert(s.stack.drop_last() == s.stack.subrange(0, s.stack.len() - 1));
    lemma_a_prefix(prog, s, s2, s.stack.len() - 1);
}

pub proof fn lemma_a_return(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        step_return(prog, s, s2),
    ensures
        inv_a(prog, s2),
{
    let f = tf(s);
    assert(s.stack.drop_last() == s.stack.subrange(0, s.stack.len() - 1));
    if holds_fresh(s, f) {
        lemma_agree_used(s, f.k->0);
        let s1 = State { konts: s.konts.insert(f.k->0, Kont { used: true, ..s.konts[f.k->0] }), ..s };
        assert(agree(s1, s2));
        assert(agree(s, s2));
    }
    lemma_a_prefix(prog, s, s2, s.stack.len() - 1);
}

pub proof fn lemma_a_cancel(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        step_cancel(prog, s, s2),
    ensures
        inv_a(prog, s2),
{
    let f = tf(s);
    match instr_at(prog, f) {
        Instr::Perform { cap, op } => {
            let j = choose|j: int| #[trigger] perform_ok_dyn(prog, s, cap, op, j) && s2 == do_cancel(s, j);
            lemma_a_prefix(prog, s, s2, j);
        },
        _ => {},
    }
}

pub proof fn lemma_a_unwind(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        step_unwind_pop(s, s2) || step_unwind_drop(s, s2) || step_unwind_abort(s, s2),
    ensures
        inv_a(prog, s2),
{
    assert(s.stack.subrange(0, s.stack.len() as int) == s.stack);
    if step_unwind_drop(s, s2) {
        lemma_agree_used(s, pf(s).k->0);
        lemma_a_prefix(prog, s, s2, s.stack.len() as int);
    } else if step_unwind_pop(s, s2) {
        lemma_a_prefix(prog, s, s2, s.stack.len() as int);
    } else {
        let sl = choose|sl: Slot|
            #[trigger] max_slot(pf(s).slots, sl) && slot_live(s, pf(s), sl)
                && s.res[pf(s).slots[sl]].on_abort && s2 == do_abort(s, sl);
        let s1 = State { res: s.res, ..s2 };
        lemma_a_prefix(prog, s, s1, s.stack.len() as int);
        let r = pf(s).slots[sl];
        assert(s2.res.dom() =~= s.res.dom());
        lemma_stack_seq_agree(prog, s1, s2, s2.stack);
        lemma_rest_agree(prog, s1, s2);
    }
}

// ---------------------------------------------------------------------------
// Steps that change only the top frame
// ---------------------------------------------------------------------------

/// `f2` is `f` one instruction later, with the same environment and continuation.
pub proof fn lemma_cf_next(prog: Prog, s: State, f: CFrame, f2: CFrame)
    requires
        check(prog),
        cf_ok(prog, s, f),
        !(instr_at(prog, f) is Return),
        f2.block == f.block,
        f2.pc == f.pc + 1,
        f2.env == f.env,
        f2.k == f.k,
        post(prog, sig_of(prog, f), ss_of(prog, f), instr_at(prog, f)).env == ss_of(prog, f).env,
    ensures
        cf_ok(prog, s, f2),
{
    lemma_instr_ok(prog, f);
    assert(ss_of(prog, f2) == ss_of(prog, adv(f)));
}

pub proof fn lemma_a_local(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        step_acquire(prog, s, s2) || step_consume(prog, s, s2),
    ensures
        inv_a(prog, s2),
{
    let f = tf(s);
    lemma_top_ok(prog, s);
    let f2 = s2.stack.last()->Code_0;
    let ext = Seq::<Frame>::empty();
    match instr_at(prog, f) {
        Instr::Acquire { slot, on_abort } => {
            assert(f2 == CFrame { slots: f.slots.insert(slot, s.next_res), ..adv(f) });
        },
        Instr::Consume { slot } => {
            assert(f2 == CFrame { slots: f.slots.remove(slot), ..adv(f) });
        },
        _ => {},
    }
    lemma_cf_next(prog, s, f, f2);
    assert(same_set(f2.env, f.env));
    assert(ext_ok(prog, s, f2, ext));
    assert(s2.stack == s.stack.update(s.stack.len() - 1, Frame::Code(f2)) + ext);
    lemma_push_ext(prog, s, s.stack, f2, ext);
    let s1 = State { stack: s2.stack, ..s };
    lemma_stack_seq_agree(prog, s, s1, s2.stack);
    lemma_rest_agree(prog, s, s1);
    assert(agree(s1, s2));
    lemma_stack_seq_agree(prog, s1, s2, s2.stack);
    lemma_rest_agree(prog, s1, s2);
    assert forall|r: ResId| #[trigger] s2.res.contains_key(r) implies r < s2.next_res by {
        if s.res.contains_key(r) {
        }
    }
}

// ---------------------------------------------------------------------------
// Steps that push frames
// ---------------------------------------------------------------------------

/// Turn `stack_seq_ok` and the other parts in `s` into `inv_a` of `s2` when
/// only the stack, the hinfo map (new entries) and the counters differ.
pub proof fn lemma_a_finish(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        agree(s, s2),
        stack_seq_ok(prog, s2, s2.stack),
        s2.konts.dom() == s.konts.dom(),
        s2.next_k == s.next_k,
        s2.res == s.res,
        s2.next_res == s.next_res,
        s2.next_h >= s.next_h,
        forall|h: HId| #[trigger] s2.hinfo.contains_key(h) && !s.hinfo.contains_key(h) ==> h < s2.next_h
            && hinfo_ok(prog, s2, s2.hinfo[h]),
    ensures
        inv_a(prog, s2),
{
    assert forall|k: KId| #[trigger] s2.konts.contains_key(k) implies k < s2.next_k && kont_ok(
        prog,
        s2,
        s2.konts[k],
    ) by {
        assert(s.konts.contains_key(k));
        lemma_kont_agree(prog, s, s2, s.konts[k]);
    }
    assert forall|h: HId| #[trigger] s2.hinfo.contains_key(h) implies h < s2.next_h && hinfo_ok(
        prog,
        s2,
        s2.hinfo[h],
    ) by {
        if s.hinfo.contains_key(h) {
            lemma_hinfo_agree(prog, s, s2, s.hinfo[h]);
        }
    }
}

pub proof fn lemma_a_call(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        step_call(prog, s, s2),
    ensures
        inv_a(prog, s2),
{
    let f = tf(s);
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    match instr_at(prog, f) {
        Instr::Call { block, caps } => {
            let ss = ss_of(prog, f);
            let cs = prog.blocks[block].sig;
            let f2 = CFrame { env: f.env + call_rets(prog, f.env, block, caps), ..adv(f) };
            let callee = CFrame {
                block,
                pc: 0,
                env: call_env(f.env, caps),
                slots: Map::empty(),
                k: None,
            };
            let ext = seq![Frame::Code(callee)];
            assert(s2.stack == s.stack.update(s.stack.len() - 1, Frame::Code(f2)) + ext);
            // f2
            let ss2 = ss_of(prog, f2);
            assert(ss2 == ss_of(prog, adv(f)));
            assert(ss2.env == ss.env + call_ret_effs(prog, ss.env, block, caps));
            assert(block_ok(prog, block));
            assert forall|m: int| 0 <= m < f2.env.len() implies s.hinfo.contains_key(#[trigger] f2.env[m])
                && s.hinfo[f2.env[m]].eff == ss2.env[m] by {
                if m >= f.env.len() {
                    let jj = m - f.env.len();
                    assert(cs.rets[jj] < cs.caps.len());
                    assert(caps[cs.rets[jj] as int] < ss.env.len());
                    assert(f2.env[m] == f.env[caps[cs.rets[jj] as int] as int]);
                }
            }
            assert(env_typed(s, f2.env, ss2.env));
            assert forall|h: HId| f2.env.contains(h) implies #[trigger] f.env.contains(h) by {
                let m = choose|m: int| 0 <= m < f2.env.len() && f2.env[m] == h;
                if m >= f.env.len() {
                    let jj = m - f.env.len();
                    assert(cs.rets[jj] < cs.caps.len());
                    assert(f.env[caps[cs.rets[jj] as int] as int] == h);
                } else {
                    assert(f.env[m] == h);
                }
            }
            assert forall|h: HId| f.env.contains(h) implies #[trigger] f2.env.contains(h) by {
                let m = choose|m: int| 0 <= m < f.env.len() && f.env[m] == h;
                assert(f2.env[m] == h);
            }
            assert(same_set(f2.env, f.env));
            if f.k is Some {
                assert(k_link(prog, s, f2));
            }
            assert(cf_ok(prog, s, f2));
            // callee
            assert(ss_of(prog, callee) == entry(cs));
            assert(env_typed(s, callee.env, cs.caps));
            assert(cf_ok(prog, s, callee));
            assert(susp_instr(prog, f2) == instr_at(prog, f));
            assert forall|h: HId| #[trigger] up_has(prog, f2, h) implies f.env.contains(h) by {
                let jj = choose|jj: int| 0 <= jj < caps.len() && f2.env[#[trigger] caps[jj] as int] == h;
                assert(f2.env[caps[jj] as int] == f.env[caps[jj] as int]);
            }
            // ext
            assert(frame_ok(prog, s, ext[0]));
            assert(frames_ok(prog, s, ext));
            assert forall|m: int, h: HId| 0 <= m < ext.len() && #[trigger] reaches(s, ext[m], h) implies hid_in(
                ext,
                0,
                m,
                h,
            ) || up_has(prog, f2, h) by {
                let jj = choose|jj: int| 0 <= jj < callee.env.len() && callee.env[jj] == h;
                assert(f2.env[caps[jj] as int] == h);
            }
            assert(scoped(prog, s, ext));
            assert(below_h(prog, s, ext));
            assert(ext_ok(prog, s, f2, ext));
            lemma_push_ext(prog, s, s.stack, f2, ext);
            lemma_stack_seq_agree(prog, s, s2, s2.stack);
            lemma_a_finish(prog, s, s2);
        },
        _ => {},
    }
}

pub proof fn lemma_a_handle(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        step_handle(prog, s, s2),
    ensures
        inv_a(prog, s2),
{
    let f = tf(s);
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    match instr_at(prog, f) {
        Instr::Handle { eff, clauses, body } => {
            let ss = ss_of(prog, f);
            let bs = prog.blocks[body].sig;
            let c = s.next_h;
            let benv = f.env.push(c);
            let f2 = CFrame { env: f.env + handle_rets(prog, benv, body), ..adv(f) };
            let b = CFrame { block: body, pc: 0, env: benv, slots: Map::empty(), k: None };
            let ext = seq![Frame::Handler(c), Frame::Code(b)];
            assert(s2.stack == s.stack.update(s.stack.len() - 1, Frame::Code(f2)) + ext);
            assert(!s.hinfo.contains_key(c));
            assert(agree(s, s2));
            // f2 (rule d keeps the new capability out of f2)
            let ss2 = ss_of(prog, f2);
            assert(ss2 == ss_of(prog, adv(f)));
            assert(ss2.env == ss.env + handle_ret_effs(prog, ss.env, eff, body));
            assert forall|m: int| 0 <= m < f2.env.len() implies s2.hinfo.contains_key(#[trigger] f2.env[m])
                && s2.hinfo[f2.env[m]].eff == ss2.env[m] by {
                if m >= f.env.len() {
                    let jj = m - f.env.len();
                    assert(bs.rets[jj] < ss.env.len());
                    assert(f2.env[m] == f.env[bs.rets[jj] as int]);
                } else {
                    assert(s.hinfo.contains_key(f.env[m]));
                }
            }
            assert(env_typed(s2, f2.env, ss2.env));
            assert forall|h: HId| f2.env.contains(h) implies #[trigger] f.env.contains(h) by {
                let m = choose|m: int| 0 <= m < f2.env.len() && f2.env[m] == h;
                if m >= f.env.len() {
                    let jj = m - f.env.len();
                    assert(bs.rets[jj] < ss.env.len());
                    assert(f.env[bs.rets[jj] as int] == h);
                } else {
                    assert(f.env[m] == h);
                }
            }
            assert forall|h: HId| f.env.contains(h) implies #[trigger] f2.env.contains(h) by {
                let m = choose|m: int| 0 <= m < f.env.len() && f.env[m] == h;
                assert(f2.env[m] == h);
            }
            assert(same_set(f2.env, f.env));
            lemma_cf_ok_agree(prog, s, s2, f);
            if f.k is Some {
                assert(k_link(prog, s2, f2));
            }
            assert(cf_ok(prog, s2, f2));
            // the handler instance
            let hi = HInfo { eff, clauses, env: f.env };
            assert(s2.hinfo[c] == hi);
            lemma_env_typed_agree(s, s2, f.env, ss.env);
            assert forall|o: int| 0 <= o < hi.clauses.len() implies #[trigger] clause_ok(prog, s2, hi, o) by {
                assert(prog.blocks.contains_key(clauses[o]));
            }
            assert(hinfo_ok(prog, s2, hi));
            // the body frame
            assert(block_ok(prog, body));
            assert(ss_of(prog, b) == entry(bs));
            assert forall|m: int| 0 <= m < benv.len() implies s2.hinfo.contains_key(#[trigger] benv[m])
                && s2.hinfo[benv[m]].eff == bs.caps[m] by {
                if m < f.env.len() {
                    assert(s.hinfo.contains_key(f.env[m]));
                }
            }
            assert(cf_ok(prog, s2, b));
            // ext
            assert(susp_instr(prog, f2) == instr_at(prog, f));
            assert forall|i: int| 0 <= i < ext.len() implies #[trigger] frame_ok(prog, s2, ext[i]) by {}
            assert forall|m: int, h: HId| 0 <= m < ext.len() && #[trigger] reaches(s2, ext[m], h) implies hid_in(
                ext,
                0,
                m,
                h,
            ) || up_has(prog, f2, h) by {
                if m == 1 && h == c {
                    assert(is_handler(ext[0], c));
                } else if m == 1 {
                    let mm = choose|mm: int| 0 <= mm < benv.len() && benv[mm] == h;
                    assert(f.env[mm] == h);
                    assert(f.env.contains(h));
                } else {
                    assert(f.env.contains(h));
                }
            }
            assert(scoped(prog, s2, ext));
            assert(below_h(prog, s2, ext));
            assert(ext_ok(prog, s2, f2, ext));
            lemma_stack_seq_agree(prog, s, s2, s.stack);
            lemma_push_ext(prog, s2, s.stack, f2, ext);
            lemma_a_finish(prog, s, s2);
        },
        _ => {},
    }
}

pub proof fn lemma_a_resume(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        step_resume(prog, s, s2),
    ensures
        inv_a(prog, s2),
{
    let f = tf(s);
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    let kid = f.k->0;
    let kt = s.konts[kid];
    let f2 = adv(f);
    let ext = kt.frames;
    assert(s.stack.update(s.stack.len() - 1, Frame::Code(f2)) == upd_top(s, f2));
    lemma_cf_next(prog, s, f, f2);
    assert(kont_ok(prog, s, kt));
    let h0 = ext[0]->Handler_0;
    assert(susp_instr(prog, f2) == instr_at(prog, f));
    assert forall|m: int, h: HId| 0 <= m < ext.len() && #[trigger] reaches(s, ext[m], h) implies hid_in(
        ext,
        0,
        m,
        h,
    ) || up_has(prog, f2, h) by {
        if !hid_in(ext, 0, m, h) {
            assert(reaches(s, ext[0], h));
            assert(s.hinfo[h0].env.contains(h));
        }
    }
    assert forall|h: HId| #[trigger] up_has(prog, f2, h) implies reaches(s, ext[0], h) by {
        assert(f.env.contains(h));
    }
    assert(ext_ok(prog, s, f2, ext));
    lemma_push_ext(prog, s, s.stack, f2, ext);
    if !kt.multi {
        lemma_agree_used(s, kid);
    }
    assert(agree(s, s2));
    lemma_stack_seq_agree(prog, s, s2, s2.stack);
    lemma_a_finish(prog, s, s2);
}

// ---------------------------------------------------------------------------
// Perform
// ---------------------------------------------------------------------------

/// Index facts about the captured frames.
pub proof fn lemma_captured_index(s: State, j: int)
    requires
        top_code(s),
        0 <= j < s.stack.len() - 1,
    ensures
        captured(s, j).len() == s.stack.len() - j,
        forall|m: int| 0 <= m < s.stack.len() - 1 - j ==> #[trigger] captured(s, j)[m] == s.stack[j + m],
        captured(s, j)[s.stack.len() - 1 - j] == Frame::Code(adv(tf(s))),
{
}

/// A perform keeps `inv_a`.
pub proof fn lemma_a_perform_at(prog: Prog, s: State, cap: nat, op: nat, j: int)
    requires
        check(prog),
        inv_a(prog, s),
        at_instr(prog, s),
        instr_at(prog, tf(s)) == (Instr::Perform { cap, op }),
        perform_ok_dyn(prog, s, cap, op, j),
    ensures
        inv_a(prog, do_perform(prog, s, tf(s).env[cap as int], op, j)),
{
    let f = tf(s);
    let st = s.stack;
    let t = st.len() - 1;
    let c = f.env[cap as int];
    let kn = s.next_k;
    let s2 = do_perform(prog, s, c, op, j);
    let kf = captured(s, j);
    let kt = Kont { frames: kf, multi: op_mode(prog, s, c, op) == Mode::Multi, used: false };
    let cl = clause_frame(s, c, op, kn);
    let st2 = st.subrange(0, j).push(Frame::Code(cl));
    lemma_top_ok(prog, s);
    lemma_instr_ok(prog, f);
    // shape
    assert(st[t] is Code);
    assert(is_handler(st[j], c));
    assert(j < t);
    assert(j >= 1);
    lemma_captured_index(s, j);
    assert(!s.konts.contains_key(kn));
    assert(agree(s, s2));
    assert(s2.konts[kn] == kt);
    lemma_stack_seq_agree(prog, s, s2, st);
    lemma_frames_agree(prog, s, s2, st);
    // the captured top frame
    lemma_cf_ok_agree(prog, s, s2, f);
    lemma_cf_next(prog, s2, f, adv(f));
    assert(susp_instr(prog, adv(f)) == instr_at(prog, f));
    assert(reaches(s2, kf[t - j], 0) == f.env.contains(0));
    assert forall|h: HId| #[trigger] reaches(s2, kf[t - j], h) == reaches(s2, st[t], h) by {}
    // the new continuation
    assert forall|i: int| 0 <= i < kf.len() implies #[trigger] frame_ok(prog, s2, kf[i]) by {
        if i < t - j {
            assert(frame_ok(prog, s2, st[j + i]));
        }
    }
    assert forall|i: int| 0 <= i < kf.len() implies #[trigger] code_susp(prog, kf, i) by {
        if i < t - j {
            assert(code_susp(prog, st, j + i));
        }
    }
    assert forall|i: int, i2: int| 0 <= i < i2 < kf.len() && kf[i] is Code implies #[trigger] scope_at(
        prog,
        s2,
        kf,
        i,
        i2,
    ) by {
        assert(kf[i] == st[j + i]);
        assert(scope_at(prog, s2, st, j + i, j + i2));
        assert forall|h: HId| #[trigger] reaches(s2, kf[i2], h) implies hid_in(kf, i + 1, i2, h)
            || up_has(prog, kf[i]->Code_0, h) by {
            assert(reaches(s2, st[j + i2], h));
            if hid_in(st, j + i + 1, j + i2, h) {
                lemma_hid_in_shift(st, kf, j + i + 1, j + i2, -j, h);
            }
        }
    }
    assert(below_ok(prog, s2, st, j)) by {
        assert(hframe(st, j));
    }
    assert(st[j - 1] is Code);
    assert forall|m: int, h: HId| 0 <= m < kf.len() && #[trigger] reaches(s2, kf[m], h) implies hid_in(
        kf,
        0,
        m,
        h,
    ) || reaches(s2, kf[0], h) by {
        if m > 0 {
            assert(scope_at(prog, s2, st, j - 1, j + m));
            assert(reaches(s2, st[j + m], h));
            if hid_in(st, j, j + m, h) {
                lemma_hid_in_shift(st, kf, j, j + m, -j, h);
            } else {
                assert(up_has(prog, st[j - 1]->Code_0, h));
            }
        }
    }
    assert forall|mm: int| 1 <= mm < kf.len() && #[trigger] hframe(kf, mm) implies below_ok(prog, s2, kf, mm) by {
        assert(mm < t - j);
        assert(hframe(st, j + mm));
        assert(below_ok(prog, s2, st, j + mm));
        assert(kf[mm - 1] == st[j + mm - 1]);
    }
    assert(kont_ok(prog, s2, kt));
    // the clause frame
    let hi = s.hinfo[c];
    assert(s.hinfo.contains_key(c));
    assert(hinfo_ok(prog, s, hi));
    assert(clause_ok(prog, s, hi, op as int));
    lemma_env_typed_agree(s, s2, hi.env, prog.blocks[hi.clauses[op as int]].sig.caps);
    assert(block_ok(prog, hi.clauses[op as int]));
    assert(ss_of(prog, cl) == entry(sig_of(prog, cl)));
    assert(k_link(prog, s2, cl));
    assert(cf_ok(prog, s2, cl));
    // the new stack
    assert forall|m: int| 0 <= m < j implies st2[m] == st[m] by {}
    assert(st2[j] == Frame::Code(cl));
    assert forall|h: HId| #[trigger] reaches(s2, st2[j], h) == reaches(s2, st[j], h) by {}
    assert forall|i: int| 0 <= i < st2.len() implies #[trigger] frame_ok(prog, s2, st2[i]) by {
        if i < j {
            assert(frame_ok(prog, s2, st[i]));
        }
    }
    assert forall|i: int| 0 <= i < st2.len() - 1 implies #[trigger] code_susp(prog, st2, i) by {
        assert(code_susp(prog, st, i));
    }
    assert forall|i: int, i2: int| 0 <= i < i2 < st2.len() && st2[i] is Code implies #[trigger] scope_at(
        prog,
        s2,
        st2,
        i,
        i2,
    ) by {
        assert(scope_at(prog, s2, st, i, i2));
        assert forall|h: HId| #[trigger] reaches(s2, st2[i2], h) implies hid_in(st2, i + 1, i2, h)
            || up_has(prog, st2[i]->Code_0, h) by {
            assert(reaches(s2, st[i2], h));
            if hid_in(st, i + 1, i2, h) {
                lemma_hid_in_shift(st, st2, i + 1, i2, 0, h);
            }
        }
    }
    assert forall|m: int, h: HId| 0 <= m < st2.len() && #[trigger] reaches(s2, st2[m], h) implies hid_in(
        st2,
        0,
        m,
        h,
    ) by {
        assert(reaches(s2, st[m], h));
        lemma_hid_in_shift(st, st2, 0, m, 0, h);
    }
    assert forall|jj: int| 1 <= jj < st2.len() && #[trigger] hframe(st2, jj) implies below_ok(prog, s2, st2, jj) by {
        assert(hframe(st, jj));
        assert(below_ok(prog, s2, st, jj));
    }
    assert(stack_seq_ok(prog, s2, st2));
    // the rest
    assert forall|k: KId| #[trigger] s2.konts.contains_key(k) implies k < s2.next_k && kont_ok(
        prog,
        s2,
        s2.konts[k],
    ) by {
        if k != kn {
            assert(s.konts.contains_key(k));
            lemma_kont_agree(prog, s, s2, s.konts[k]);
        }
    }
    assert forall|h: HId| #[trigger] s2.hinfo.contains_key(h) implies h < s2.next_h && hinfo_ok(
        prog,
        s2,
        s2.hinfo[h],
    ) by {
        lemma_hinfo_agree(prog, s, s2, s.hinfo[h]);
    }
}

pub proof fn lemma_a_perform(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        step_perform(prog, s, s2),
    ensures
        inv_a(prog, s2),
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
            lemma_a_perform_at(prog, s, cap, op, j);
        },
        _ => {},
    }
}

/// Every step keeps `inv_a`.
pub proof fn lemma_a_step(prog: Prog, s: State, s2: State)
    requires
        check(prog),
        inv_a(prog, s),
        step(prog, s, s2),
    ensures
        inv_a(prog, s2),
{
    if step_pop(s, s2) {
        lemma_a_pop(prog, s, s2);
    } else if step_acquire(prog, s, s2) || step_consume(prog, s, s2) {
        lemma_a_local(prog, s, s2);
    } else if step_call(prog, s, s2) {
        lemma_a_call(prog, s, s2);
    } else if step_handle(prog, s, s2) {
        lemma_a_handle(prog, s, s2);
    } else if step_perform(prog, s, s2) {
        lemma_a_perform(prog, s, s2);
    } else if step_cancel(prog, s, s2) {
        lemma_a_cancel(prog, s, s2);
    } else if step_resume(prog, s, s2) {
        lemma_a_resume(prog, s, s2);
    } else if step_return(prog, s, s2) {
        lemma_a_return(prog, s, s2);
    } else {
        lemma_a_unwind(prog, s, s2);
    }
}

/// The initial state satisfies `inv_a`.
pub proof fn lemma_a_init(prog: Prog)
    requires
        check(prog),
    ensures
        inv_a(prog, init(prog)),
{
    let s = init(prog);
    let f = s.stack[0]->Code_0;
    assert(block_ok(prog, prog.main));
    assert(ss_of(prog, f) == entry(prog.blocks[prog.main].sig));
    assert(cf_ok(prog, s, f));
    assert(frames_ok(prog, s, s.stack));
    assert forall|m: int, h: HId| 0 <= m < s.stack.len() && #[trigger] reaches(s, s.stack[m], h) implies hid_in(
        s.stack,
        0,
        m,
        h,
    ) by {
        assert(!f.env.contains(h));
    }
}

} // verus!
