//! # The structural invariant (`inv_a`)
//!
//! `inv_a` says that every frame is well typed and that capabilities are
//! lexically scoped:
//! * `based`: each capability that a stack frame can use has its handler
//!   frame below that frame (so the handler is live).
//! * `scoped`: for frames `i < i2`, a capability that frame `i2` can use and
//!   whose handler is below `i` was passed up by frame `i`.
//! * `below_h`: the frame below a handler frame passes up only capabilities
//!   that the clauses of that handler can use.
//! Continuations satisfy the same rules, relative to their clause frame.

use vstd::prelude::*;
use crate::model::*;
use crate::checker::*;

verus! {

// ---------------------------------------------------------------------------
// Definitions
// ---------------------------------------------------------------------------

/// The signature of the block of `f`.
pub open spec fn sig_of(prog: Prog, f: CFrame) -> Sig {
    prog.blocks[f.block].sig
}

/// The checker state of `f` at its pc.
pub open spec fn ss_of(prog: Prog, f: CFrame) -> SS {
    ss_at(prog, f.block, f.pc)
}

/// Frame `fr` can use capability `h`. A handler frame uses the capabilities
/// of its clauses.
pub open spec fn reaches(s: State, fr: Frame, h: HId) -> bool {
    match fr {
        Frame::Code(c) => c.env.contains(h),
        Frame::Handler(id) => s.hinfo[id].env.contains(h),
    }
}

/// A handler frame of `h` is at an index in `[a, b)` of `fr`.
pub open spec fn hid_in(fr: Seq<Frame>, a: int, b: int, h: HId) -> bool {
    exists|m: int| a <= m < b && 0 <= m < fr.len() && #[trigger] is_handler(fr[m], h)
}

/// The instruction that suspended `f` (the one before its pc).
pub open spec fn susp_instr(prog: Prog, f: CFrame) -> Instr {
    prog.blocks[f.block].code[f.pc - 1]
}

/// `i` is a suspension point.
pub open spec fn is_susp(i: Instr) -> bool {
    i is Call || i is Handle || i is Resume || i is Perform
}

/// `f` is suspended at a call, a handle, a resume or a perform.
pub open spec fn suspended(prog: Prog, f: CFrame) -> bool {
    code_ok(prog, f) && f.pc >= 1 && is_susp(susp_instr(prog, f))
}

/// Frame `i` of `fr`, if it is a code frame, is suspended.
pub open spec fn code_susp(prog: Prog, fr: Seq<Frame>, i: int) -> bool {
    fr[i] is Code ==> suspended(prog, fr[i]->Code_0)
}

/// The suspension point of `f` passes capability `h` up.
pub open spec fn up_has(prog: Prog, f: CFrame, h: HId) -> bool {
    match susp_instr(prog, f) {
        Instr::Call { caps, .. } => exists|j: int|
            0 <= j < caps.len() && f.env[#[trigger] caps[j] as int] == h,
        Instr::Handle { .. } => f.env.contains(h),
        Instr::Resume => f.env.contains(h),
        _ => false,
    }
}

/// Frames `i < i2` of `fr`: a capability of frame `i2` is a handler between
/// them, or frame `i` passes it up.
pub open spec fn scope_at(prog: Prog, s: State, fr: Seq<Frame>, i: int, i2: int) -> bool {
    forall|h: HId|
        #[trigger] reaches(s, fr[i2], h) ==> hid_in(fr, i + 1, i2, h) || up_has(
            prog,
            fr[i]->Code_0,
            h,
        )
}

/// Every pair of frames of `fr` is scoped.
pub open spec fn scoped(prog: Prog, s: State, fr: Seq<Frame>) -> bool {
    forall|i: int, i2: int|
        0 <= i < i2 < fr.len() && fr[i] is Code ==> #[trigger] scope_at(prog, s, fr, i, i2)
}

/// Every capability of a frame of `fr` has a handler frame below it.
pub open spec fn based(s: State, fr: Seq<Frame>) -> bool {
    forall|m: int, h: HId| 0 <= m < fr.len() && #[trigger] reaches(s, fr[m], h) ==> hid_in(fr, 0, m, h)
}

/// For a continuation: every capability of a frame is a handler inside it,
/// or the clauses of its handler (frame 0) can use it.
pub open spec fn based_k(s: State, fr: Seq<Frame>) -> bool {
    forall|m: int, h: HId|
        0 <= m < fr.len() && #[trigger] reaches(s, fr[m], h) ==> hid_in(fr, 0, m, h) || reaches(
            s,
            fr[0],
            h,
        )
}

/// Frame `j` of `fr` is a handler frame.
pub open spec fn hframe(fr: Seq<Frame>, j: int) -> bool {
    fr[j] is Handler
}

/// The frame below handler frame `j` pushed it (at a handle or a resume), and
/// passes up only capabilities that the clauses of the handler can use.
pub open spec fn below_ok(prog: Prog, s: State, fr: Seq<Frame>, j: int) -> bool {
    &&& fr[j - 1] is Code
    &&& suspended(prog, fr[j - 1]->Code_0)
    &&& (susp_instr(prog, fr[j - 1]->Code_0) is Handle || susp_instr(prog, fr[j - 1]->Code_0) is Resume)
    &&& forall|h: HId| #[trigger] up_has(prog, fr[j - 1]->Code_0, h) ==> reaches(s, fr[j], h)
}

/// `below_ok` for every handler frame of `fr` above index 0.
pub open spec fn below_h(prog: Prog, s: State, fr: Seq<Frame>) -> bool {
    forall|j: int| 1 <= j < fr.len() && #[trigger] hframe(fr, j) ==> below_ok(prog, s, fr, j)
}

/// The handler ids in `env` have the effects `effs`.
pub open spec fn env_typed(s: State, env: Seq<HId>, effs: Seq<EffId>) -> bool {
    &&& env.len() == effs.len()
    &&& forall|m: int|
        0 <= m < env.len() ==> s.hinfo.contains_key(#[trigger] env[m]) && s.hinfo[env[m]].eff
            == effs[m]
}

/// `a` and `b` hold the same handler ids.
pub open spec fn same_set(a: Seq<HId>, b: Seq<HId>) -> bool {
    forall|h: HId| #![trigger a.contains(h)] #![trigger b.contains(h)] a.contains(h) <==> b.contains(h)
}

/// The continuation of clause frame `f`: it exists, its mode matches the
/// block, frame 0 is a handler frame, and `f` uses the capabilities of that
/// handler's clauses.
pub open spec fn k_link(prog: Prog, s: State, f: CFrame) -> bool {
    let kid = f.k->0;
    &&& s.konts.contains_key(kid)
    &&& s.konts[kid].multi == (sig_of(prog, f).kmode == Some(Mode::Multi))
    &&& s.konts[kid].frames.len() > 0
    &&& s.konts[kid].frames[0] is Handler
    &&& s.hinfo.contains_key(s.konts[kid].frames[0]->Handler_0)
    &&& same_set(f.env, s.hinfo[s.konts[kid].frames[0]->Handler_0].env)
}

/// A well-formed code frame.
pub open spec fn cf_ok(prog: Prog, s: State, f: CFrame) -> bool {
    &&& code_ok(prog, f)
    &&& env_typed(s, f.env, ss_of(prog, f).env)
    &&& (f.k is Some <==> sig_of(prog, f).kmode is Some)
    &&& (f.k is Some ==> k_link(prog, s, f))
}

/// A well-formed frame.
pub open spec fn frame_ok(prog: Prog, s: State, fr: Frame) -> bool {
    match fr {
        Frame::Code(c) => cf_ok(prog, s, c),
        Frame::Handler(id) => s.hinfo.contains_key(id),
    }
}

/// Every frame of `fr` is well formed.
pub open spec fn frames_ok(prog: Prog, s: State, fr: Seq<Frame>) -> bool {
    forall|i: int| 0 <= i < fr.len() ==> #[trigger] frame_ok(prog, s, fr[i])
}

/// The invariant of a stack `st`.
pub open spec fn stack_seq_ok(prog: Prog, s: State, st: Seq<Frame>) -> bool {
    &&& frames_ok(prog, s, st)
    &&& forall|i: int| 0 <= i < st.len() - 1 ==> #[trigger] code_susp(prog, st, i)
    &&& st.len() > 0 ==> st[0] is Code
    &&& scoped(prog, s, st)
    &&& based(s, st)
    &&& below_h(prog, s, st)
}

/// The invariant of a continuation.
pub open spec fn kont_ok(prog: Prog, s: State, kt: Kont) -> bool {
    let fr = kt.frames;
    &&& fr.len() >= 2
    &&& fr[0] is Handler
    &&& frames_ok(prog, s, fr)
    &&& forall|i: int| 0 <= i < fr.len() ==> #[trigger] code_susp(prog, fr, i)
    &&& scoped(prog, s, fr)
    &&& based_k(s, fr)
    &&& below_h(prog, s, fr)
}

/// Clause `o` of a handler instance has the signature the checker asked for.
pub open spec fn clause_ok(prog: Prog, s: State, hi: HInfo, o: int) -> bool {
    let b = hi.clauses[o];
    &&& prog.blocks.contains_key(b)
    &&& env_typed(s, hi.env, prog.blocks[b].sig.caps)
    &&& prog.blocks[b].sig.rets.len() == 0
    &&& prog.blocks[b].sig.kmode == Some(prog.effs[hi.eff][o])
}

/// A well-formed handler instance.
pub open spec fn hinfo_ok(prog: Prog, s: State, hi: HInfo) -> bool {
    &&& prog.effs.contains_key(hi.eff)
    &&& hi.clauses.len() == prog.effs[hi.eff].len()
    &&& forall|o: int| 0 <= o < hi.clauses.len() ==> #[trigger] clause_ok(prog, s, hi, o)
}

/// The structural invariant.
pub open spec fn inv_a(prog: Prog, s: State) -> bool {
    &&& stack_seq_ok(prog, s, s.stack)
    &&& forall|k: KId| #[trigger] s.konts.contains_key(k) ==> k < s.next_k && kont_ok(prog, s, s.konts[k])
    &&& forall|h: HId| #[trigger] s.hinfo.contains_key(h) ==> h < s.next_h && hinfo_ok(prog, s, s.hinfo[h])
    &&& forall|r: ResId| #[trigger] s.res.contains_key(r) ==> r < s.next_res
}

/// `s2` keeps every handler instance and the frames and mode of every
/// continuation of `s`.
pub open spec fn agree(s: State, s2: State) -> bool {
    &&& forall|h: HId| #[trigger] s.hinfo.contains_key(h) ==> s2.hinfo.contains_key(h) && s2.hinfo[h] == s.hinfo[h]
    &&& forall|k: KId|
        #[trigger] s.konts.contains_key(k) ==> s2.konts.contains_key(k) && s2.konts[k].frames
            == s.konts[k].frames && s2.konts[k].multi == s.konts[k].multi
}

// ---------------------------------------------------------------------------
// Stability under `agree`
// ---------------------------------------------------------------------------

pub proof fn lemma_reaches_agree(s: State, s2: State, fr: Frame, h: HId)
    requires
        agree(s, s2),
        fr is Handler ==> s.hinfo.contains_key(fr->Handler_0),
    ensures
        reaches(s, fr, h) == reaches(s2, fr, h),
{
}

pub proof fn lemma_env_typed_agree(s: State, s2: State, env: Seq<HId>, effs: Seq<EffId>)
    requires
        agree(s, s2),
        env_typed(s, env, effs),
    ensures
        env_typed(s2, env, effs),
{
    assert forall|m: int| 0 <= m < env.len() implies s2.hinfo.contains_key(#[trigger] env[m])
        && s2.hinfo[env[m]].eff == effs[m] by {
        assert(s.hinfo.contains_key(env[m]));
    }
}

pub proof fn lemma_cf_ok_agree(prog: Prog, s: State, s2: State, f: CFrame)
    requires
        agree(s, s2),
        cf_ok(prog, s, f),
    ensures
        cf_ok(prog, s2, f),
{
    lemma_env_typed_agree(s, s2, f.env, ss_of(prog, f).env);
    if f.k is Some {
        let kid = f.k->0;
        assert(s.konts.contains_key(kid));
        let h0 = s.konts[kid].frames[0]->Handler_0;
        assert(s2.konts[kid].frames == s.konts[kid].frames);
        assert(s2.hinfo[h0] == s.hinfo[h0]);
    }
}

pub proof fn lemma_frames_agree(prog: Prog, s: State, s2: State, fr: Seq<Frame>)
    requires
        agree(s, s2),
        frames_ok(prog, s, fr),
    ensures
        frames_ok(prog, s2, fr),
        forall|i: int, h: HId|
            0 <= i < fr.len() ==> reaches(s, fr[i], h) == #[trigger] reaches(s2, fr[i], h),
{
    assert forall|i: int| 0 <= i < fr.len() implies #[trigger] frame_ok(prog, s2, fr[i]) by {
        assert(frame_ok(prog, s, fr[i]));
        match fr[i] {
            Frame::Code(c) => lemma_cf_ok_agree(prog, s, s2, c),
            Frame::Handler(_) => {},
        }
    }
    assert forall|i: int, h: HId| 0 <= i < fr.len() implies reaches(s, fr[i], h) == #[trigger] reaches(
        s2,
        fr[i],
        h,
    ) by {
        assert(frame_ok(prog, s, fr[i]));
    }
}

pub proof fn lemma_scoped_agree(prog: Prog, s: State, s2: State, fr: Seq<Frame>)
    requires
        agree(s, s2),
        frames_ok(prog, s, fr),
        scoped(prog, s, fr),
    ensures
        scoped(prog, s2, fr),
{
    lemma_frames_agree(prog, s, s2, fr);
    assert forall|i: int, i2: int| 0 <= i < i2 < fr.len() && fr[i] is Code implies #[trigger] scope_at(
        prog,
        s2,
        fr,
        i,
        i2,
    ) by {
        assert(scope_at(prog, s, fr, i, i2));
        assert forall|h: HId| #[trigger] reaches(s2, fr[i2], h) implies hid_in(fr, i + 1, i2, h)
            || up_has(prog, fr[i]->Code_0, h) by {
            assert(reaches(s, fr[i2], h));
        }
    }
}

pub proof fn lemma_based_agree(prog: Prog, s: State, s2: State, fr: Seq<Frame>)
    requires
        agree(s, s2),
        frames_ok(prog, s, fr),
        based(s, fr),
    ensures
        based(s2, fr),
{
    lemma_frames_agree(prog, s, s2, fr);
    assert forall|m: int, h: HId| 0 <= m < fr.len() && #[trigger] reaches(s2, fr[m], h) implies hid_in(
        fr,
        0,
        m,
        h,
    ) by {
        assert(reaches(s, fr[m], h));
    }
}

pub proof fn lemma_based_k_agree(prog: Prog, s: State, s2: State, fr: Seq<Frame>)
    requires
        agree(s, s2),
        frames_ok(prog, s, fr),
        fr.len() > 0,
        based_k(s, fr),
    ensures
        based_k(s2, fr),
{
    lemma_frames_agree(prog, s, s2, fr);
    assert forall|m: int, h: HId| 0 <= m < fr.len() && #[trigger] reaches(s2, fr[m], h) implies hid_in(
        fr,
        0,
        m,
        h,
    ) || reaches(s2, fr[0], h) by {
        assert(reaches(s, fr[m], h));
        assert(reaches(s, fr[0], h) == reaches(s2, fr[0], h));
    }
}

pub proof fn lemma_below_h_agree(prog: Prog, s: State, s2: State, fr: Seq<Frame>)
    requires
        agree(s, s2),
        frames_ok(prog, s, fr),
        below_h(prog, s, fr),
    ensures
        below_h(prog, s2, fr),
{
    lemma_frames_agree(prog, s, s2, fr);
    assert forall|j: int| 1 <= j < fr.len() && #[trigger] hframe(fr, j) implies below_ok(prog, s2, fr, j) by {
        assert(below_ok(prog, s, fr, j));
        assert forall|h: HId| #[trigger] up_has(prog, fr[j - 1]->Code_0, h) implies reaches(s2, fr[j], h) by {
            assert(reaches(s, fr[j], h));
        }
    }
}

pub proof fn lemma_stack_seq_agree(prog: Prog, s: State, s2: State, st: Seq<Frame>)
    requires
        agree(s, s2),
        stack_seq_ok(prog, s, st),
    ensures
        stack_seq_ok(prog, s2, st),
{
    lemma_frames_agree(prog, s, s2, st);
    lemma_scoped_agree(prog, s, s2, st);
    lemma_based_agree(prog, s, s2, st);
    lemma_below_h_agree(prog, s, s2, st);
}

pub proof fn lemma_kont_agree(prog: Prog, s: State, s2: State, kt: Kont)
    requires
        agree(s, s2),
        kont_ok(prog, s, kt),
    ensures
        kont_ok(prog, s2, kt),
{
    lemma_frames_agree(prog, s, s2, kt.frames);
    lemma_scoped_agree(prog, s, s2, kt.frames);
    lemma_based_k_agree(prog, s, s2, kt.frames);
    lemma_below_h_agree(prog, s, s2, kt.frames);
}

pub proof fn lemma_hinfo_agree(prog: Prog, s: State, s2: State, hi: HInfo)
    requires
        agree(s, s2),
        hinfo_ok(prog, s, hi),
    ensures
        hinfo_ok(prog, s2, hi),
{
    assert forall|o: int| 0 <= o < hi.clauses.len() implies #[trigger] clause_ok(prog, s2, hi, o) by {
        assert(clause_ok(prog, s, hi, o));
        lemma_env_typed_agree(s, s2, hi.env, prog.blocks[hi.clauses[o]].sig.caps);
    }
}

/// The parts of `inv_a` other than the stack carry over to `s2` when `s2`
/// agrees with `s`, keeps every continuation and only adds new ones.
pub proof fn lemma_rest_agree(prog: Prog, s: State, s2: State)
    requires
        inv_a(prog, s),
        agree(s, s2),
        s2.konts.dom() == s.konts.dom(),
        s2.hinfo == s.hinfo,
        s2.next_k == s.next_k,
        s2.next_h == s.next_h,
        s2.res.dom() == s.res.dom(),
        s2.next_res == s.next_res,
    ensures
        forall|k: KId| #[trigger] s2.konts.contains_key(k) ==> k < s2.next_k && kont_ok(prog, s2, s2.konts[k]),
        forall|h: HId| #[trigger] s2.hinfo.contains_key(h) ==> h < s2.next_h && hinfo_ok(prog, s2, s2.hinfo[h]),
        forall|r: ResId| #[trigger] s2.res.contains_key(r) ==> r < s2.next_res,
{
    assert forall|k: KId| #[trigger] s2.konts.contains_key(k) implies k < s2.next_k && kont_ok(
        prog,
        s2,
        s2.konts[k],
    ) by {
        assert(s.konts.contains_key(k));
        lemma_kont_agree(prog, s, s2, s.konts[k]);
        assert(s2.konts[k].frames == s.konts[k].frames);
    }
    assert forall|h: HId| #[trigger] s2.hinfo.contains_key(h) implies h < s2.next_h && hinfo_ok(
        prog,
        s2,
        s2.hinfo[h],
    ) by {
        lemma_hinfo_agree(prog, s, s2, s.hinfo[h]);
    }
    assert forall|r: ResId| #[trigger] s2.res.contains_key(r) implies r < s2.next_res by {
        assert(s.res.contains_key(r));
    }
}

// ---------------------------------------------------------------------------
// Stack shapes
// ---------------------------------------------------------------------------

/// Handler frames move with their indices shifted by `d`.
pub proof fn lemma_hid_in_shift(fr: Seq<Frame>, fr2: Seq<Frame>, a: int, b: int, d: int, h: HId)
    requires
        hid_in(fr, a, b, h),
        forall|m: int| a <= m < b && 0 <= m < fr.len() ==> 0 <= m + d < fr2.len() && fr2[m + d] == fr[m],
    ensures
        hid_in(fr2, a + d, b + d, h),
{
    let m = choose|m: int| a <= m < b && 0 <= m < fr.len() && #[trigger] is_handler(fr[m], h);
    assert(is_handler(fr2[m + d], h));
}

/// A wider range holds every handler frame of a narrower one.
pub proof fn lemma_hid_in_widen(fr: Seq<Frame>, a: int, b: int, a2: int, b2: int, h: HId)
    requires
        hid_in(fr, a, b, h),
        a2 <= a,
        b <= b2,
    ensures
        hid_in(fr, a2, b2, h),
{
    let m = choose|m: int| a <= m < b && 0 <= m < fr.len() && #[trigger] is_handler(fr[m], h);
    assert(is_handler(fr[m], h));
}

/// A prefix of a good stack is a good stack.
pub proof fn lemma_stack_prefix(prog: Prog, s: State, st: Seq<Frame>, n: int)
    requires
        stack_seq_ok(prog, s, st),
        0 <= n <= st.len(),
    ensures
        stack_seq_ok(prog, s, st.subrange(0, n)),
{
    let st2 = st.subrange(0, n);
    assert forall|i: int| 0 <= i < st2.len() implies #[trigger] frame_ok(prog, s, st2[i]) by {
        assert(frame_ok(prog, s, st[i]));
    }
    assert forall|i: int| 0 <= i < st2.len() - 1 implies #[trigger] code_susp(prog, st2, i) by {
        assert(code_susp(prog, st, i));
    }
    assert forall|i: int, i2: int| 0 <= i < i2 < st2.len() && st2[i] is Code implies #[trigger] scope_at(
        prog,
        s,
        st2,
        i,
        i2,
    ) by {
        assert(scope_at(prog, s, st, i, i2));
        assert forall|h: HId| #[trigger] reaches(s, st2[i2], h) implies hid_in(st2, i + 1, i2, h)
            || up_has(prog, st2[i]->Code_0, h) by {
            assert(reaches(s, st[i2], h));
            if hid_in(st, i + 1, i2, h) {
                lemma_hid_in_shift(st, st2, i + 1, i2, 0, h);
            }
        }
    }
    assert forall|m: int, h: HId| 0 <= m < st2.len() && #[trigger] reaches(s, st2[m], h) implies hid_in(
        st2,
        0,
        m,
        h,
    ) by {
        assert(reaches(s, st[m], h));
        lemma_hid_in_shift(st, st2, 0, m, 0, h);
    }
    assert forall|j: int| 1 <= j < st2.len() && #[trigger] hframe(st2, j) implies below_ok(prog, s, st2, j) by {
        assert(hframe(st, j));
        assert(below_ok(prog, s, st, j));
        assert(st2[j - 1] == st[j - 1]);
    }
}

/// The conditions on the frames `ext` that a suspension point of `f2` pushes.
pub open spec fn ext_ok(prog: Prog, s: State, f2: CFrame, ext: Seq<Frame>) -> bool {
    &&& frames_ok(prog, s, ext)
    &&& forall|i: int| 0 <= i < ext.len() - 1 ==> #[trigger] code_susp(prog, ext, i)
    &&& scoped(prog, s, ext)
    &&& below_h(prog, s, ext)
    &&& forall|m: int, h: HId|
        0 <= m < ext.len() && #[trigger] reaches(s, ext[m], h) ==> hid_in(ext, 0, m, h) || up_has(
            prog,
            f2,
            h,
        )
    &&& ext.len() > 0 ==> suspended(prog, f2)
    &&& ext.len() > 0 && ext[0] is Handler ==> {
        &&& (susp_instr(prog, f2) is Handle || susp_instr(prog, f2) is Resume)
        &&& forall|h: HId| #[trigger] up_has(prog, f2, h) ==> reaches(s, ext[0], h)
    }
}

/// Replace the top frame `f` by `f2` (same capabilities), then push `ext`.
pub proof fn lemma_push_ext(prog: Prog, s: State, st: Seq<Frame>, f2: CFrame, ext: Seq<Frame>)
    requires
        stack_seq_ok(prog, s, st),
        st.len() > 0,
        st.last() is Code,
        cf_ok(prog, s, f2),
        same_set(f2.env, st.last()->Code_0.env),
        forall|h: HId| #[trigger] up_has(prog, f2, h) ==> st.last()->Code_0.env.contains(h),
        ext_ok(prog, s, f2, ext),
    ensures
        stack_seq_ok(prog, s, st.update(st.len() - 1, Frame::Code(f2)) + ext),
{
    let t = st.len() - 1;
    let f = st.last()->Code_0;
    let up = st.update(t, Frame::Code(f2));
    let st2 = up + ext;
    assert forall|m: int| 0 <= m < t implies st2[m] == st[m] by {}
    assert(st2[t] == Frame::Code(f2));
    assert forall|m: int| 0 <= m < ext.len() implies st2[t + 1 + m] == ext[m] by {}
    // frames
    assert forall|i: int| 0 <= i < st2.len() implies #[trigger] frame_ok(prog, s, st2[i]) by {
        if i < t {
            assert(frame_ok(prog, s, st[i]));
        } else if i > t {
            assert(frame_ok(prog, s, ext[i - t - 1]));
        }
    }
    assert forall|i: int| 0 <= i < st2.len() - 1 implies #[trigger] code_susp(prog, st2, i) by {
        if i < t {
            assert(code_susp(prog, st, i));
        } else if i > t {
            assert(code_susp(prog, ext, i - t - 1));
        }
    }
    // reach of the new top equals the reach of the old top
    assert forall|h: HId| #[trigger] reaches(s, st2[t], h) implies reaches(s, st[t], h) by {}
    // scoped
    assert forall|i: int, i2: int| 0 <= i < i2 < st2.len() && st2[i] is Code implies #[trigger] scope_at(
        prog,
        s,
        st2,
        i,
        i2,
    ) by {
        assert forall|h: HId| #[trigger] reaches(s, st2[i2], h) implies hid_in(st2, i + 1, i2, h)
            || up_has(prog, st2[i]->Code_0, h) by {
            if i2 < t {
                assert(scope_at(prog, s, st, i, i2));
                assert(reaches(s, st[i2], h));
                if hid_in(st, i + 1, i2, h) {
                    lemma_hid_in_shift(st, st2, i + 1, i2, 0, h);
                }
            } else if i2 == t {
                assert(scope_at(prog, s, st, i, t));
                assert(reaches(s, st[t], h));
                if hid_in(st, i + 1, t, h) {
                    lemma_hid_in_shift(st, st2, i + 1, t, 0, h);
                }
            } else {
                let m = i2 - t - 1;
                assert(reaches(s, ext[m], h));
                if i > t {
                    let mi = i - t - 1;
                    assert(scope_at(prog, s, ext, mi, m));
                    if hid_in(ext, mi + 1, m, h) {
                        lemma_hid_in_shift(ext, st2, mi + 1, m, t + 1, h);
                    }
                } else if hid_in(ext, 0, m, h) {
                    lemma_hid_in_shift(ext, st2, 0, m, t + 1, h);
                    lemma_hid_in_widen(st2, t + 1, i2, i + 1, i2, h);
                } else if i < t {
                    assert(up_has(prog, f2, h));
                    assert(reaches(s, st[t], h));
                    assert(scope_at(prog, s, st, i, t));
                    if hid_in(st, i + 1, t, h) {
                        lemma_hid_in_shift(st, st2, i + 1, t, 0, h);
                        lemma_hid_in_widen(st2, i + 1, t, i + 1, i2, h);
                    }
                }
            }
        }
    }
    // based
    assert forall|m: int, h: HId| 0 <= m < st2.len() && #[trigger] reaches(s, st2[m], h) implies hid_in(
        st2,
        0,
        m,
        h,
    ) by {
        if m <= t {
            assert(reaches(s, st[m], h));
            lemma_hid_in_shift(st, st2, 0, m, 0, h);
        } else {
            let mm = m - t - 1;
            assert(reaches(s, ext[mm], h));
            if hid_in(ext, 0, mm, h) {
                lemma_hid_in_shift(ext, st2, 0, mm, t + 1, h);
                lemma_hid_in_widen(st2, t + 1, m, 0, m, h);
            } else {
                assert(up_has(prog, f2, h));
                assert(reaches(s, st[t], h));
                lemma_hid_in_shift(st, st2, 0, t, 0, h);
                lemma_hid_in_widen(st2, 0, t, 0, m, h);
            }
        }
    }
    // below_h
    assert forall|j: int| 1 <= j < st2.len() && #[trigger] hframe(st2, j) implies below_ok(prog, s, st2, j) by {
        if j < t {
            assert(hframe(st, j));
            assert(below_ok(prog, s, st, j));
        } else if j == t + 1 {
            assert(ext[0] is Handler);
        } else {
            let mj = j - t - 1;
            assert(mj >= 1);
            assert(hframe(ext, mj));
            assert(below_ok(prog, s, ext, mj));
            assert(st2[j - 1] == ext[mj - 1]);
        }
    }
}

} // verus!
