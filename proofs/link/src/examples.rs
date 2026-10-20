//! # Examples: the hypotheses hold, and each gap is real
//!
//! * Places: rule 3 and the model agree on a typed place pair. Split steps
//!   break the plain exact link (`ex_split_alias_not_in_model`). The coarse
//!   link of split places holds, and it spares only the other side of the
//!   same split (`ex_split_coarse`). A run of the B3 example `en_ok` meets
//!   each hypothesis of `thm_rule3_layout_sound_from_start`
//!   (`ex_rule3_layout_applies`).
//! * Dataflow: a CFG with a borrow, a child reference, a mutating call and a
//!   read meets the static hypotheses of `thm_w0301_no_ub` (`ex_accepted`),
//!   and a concrete run meets the run hypotheses (`ex_accepted_run`). A loop
//!   with a rebind meets the static hypotheses too (`ex_loop_accepted`).
//!   W0301 and every model annotation reject the variant that reads the
//!   child reference after the call. A B1 call that both invalidates and
//!   rebinds a reference shows why `thm_dataflow_exact` needs `no_gen_kill`.
//! * Lifecycle: a double resume of a `once` continuation fails in exec where
//!   the model reaches `err_resume_used`. A fresh `multi` continuation shows
//!   the abort difference of `drop_now`, and the failed resume after it
//!   (`ex_multi_dropped_resume`). A linear value runs through
//!   acquire, consume and a consume from a duplicated frame
//!   (`err_consumed_twice`). An unwind runs `on abort` once and then finds a
//!   dead value (`err_unwind_dead`).

use vstd::prelude::*;
use crate::places::{Step, StepKind, spec_invalidates, spec_step_alias};
use crate::layout::{lkills, flat, unstable, PStep, LPlace, LState, lpost, lss_at, lkilled, lsurvivors, linitial, is_ltrace, wf_schema, lwf, lub, lstep, lcheck};
use crate::layout_examples::{
    wsc, lss0, en_ok, en_bad, en_prefix, at, Fd, Vr, RW, RS, PA, W, example_en_ok, example_en_rejected,
    example_layout_soundness_applies,
};
use crate::places_link::*;
use crate::dataflow_link::*;
use crate::dataflow::{spec_closed, spec_edge, spec_in_lfp, lemma_step_sound};
use crate::layout::linstr_ok;
use crate::model::{Instr, SState, Group, Var, Ret, DState, post, instr_ok, killed, strict_child, arg_groups, owns, wf, step, kid_at, ptr_to, ub};
use crate::soundness::inv;
use crate::cfg::{Cfg, Node, cfg_check, sub_state, is_cfg_trace};
use crate::lifecycle::{Continuation, ContState, Linear, LinState, LinError};
use crate::lifecycle_link::*;
use crate::effects_model as em;

verus! {

// ---------------------------------------------------------------------------
// Places
// ---------------------------------------------------------------------------

pub open spec fn st_fld(id: u32) -> Step {
    Step { kind: StepKind::Field { id }, unstable: false }
}

pub open spec fn st_elem() -> Step {
    Step { kind: StepKind::Elem, unstable: true }
}

pub open spec fn st_var(id: u32) -> Step {
    Step { kind: StepKind::Variant { id }, unstable: true }
}

pub open spec fn st_seg(split: u32, hi: bool) -> Step {
    Step { kind: StepKind::Seg { split, hi }, unstable: true }
}

/// The stability that sema gives a collection with unstable elements.
pub open spec fn canonical_stab() -> spec_fn(Seq<Step>, StepKind) -> bool {
    |pre: Seq<Step>, k: StepKind| !(k is Field)
}

/// `mut(world.entities)` kills `&world.entities[]` in exec and in the model.
/// The places meet the hypotheses of `thm_invalidates_exact_typed`.
pub proof fn ex_push_kills_element_refs()
    ensures
        spec_invalidates(seq![st_fld(0)], seq![st_fld(0), st_elem()]),
        lkills(lplace(7, seq![st_fld(0)]), lplace(7, seq![st_fld(0), st_elem()])),
        !spec_invalidates(seq![st_fld(0), st_elem()], seq![st_fld(0), st_elem()]),
        !lkills(lplace(7, seq![st_fld(0), st_elem()]), lplace(7, seq![st_fld(0), st_elem()])),
{
    let m = seq![st_fld(0)];
    let p = seq![st_fld(0), st_elem()];
    assert(typed_by(canonical_stab(), m));
    assert(typed_by(canonical_stab(), p));
    assert(no_seg(m));
    assert(no_seg(p));
    assert(spec_step_alias(m[0], p[0]));
    assert(p[1].unstable);
    thm_invalidates_exact_typed(canonical_stab(), 7, m, 7, p);
    thm_invalidates_exact_typed(canonical_stab(), 7, p, 7, p);
}

/// **Gap witness.** `mut(v[..i])` can overlap `v[j..]`, so rule 3 kills a
/// reference into a payload in `v[j..]`. The model has no split steps: the
/// embedding gives the two sides different labels, and the model does not
/// kill. Thus split places are outside the exact link.
pub proof fn ex_split_alias_not_in_model()
    ensures
        spec_invalidates(seq![st_fld(0), st_seg(1, false)], seq![st_fld(0), st_seg(2, true), st_var(0)]),
        !lkills(lplace(7, seq![st_fld(0), st_seg(1, false)]), lplace(7, seq![st_fld(0), st_seg(2, true), st_var(0)])),
        !alias_exact(seq![st_fld(0), st_seg(1, false)], seq![st_fld(0), st_seg(2, true), st_var(0)]),
{
    let m = seq![st_fld(0), st_seg(1, false)];
    let p = seq![st_fld(0), st_seg(2, true), st_var(0)];
    assert(spec_step_alias(m[0], p[0]));
    assert(spec_step_alias(m[1], p[1]));
    assert(p[2].unstable);
    lemma_flat_lplace(7, m);
    lemma_flat_lplace(7, p);
    let fm = emb_path(m);
    let fp = emb_path(p);
    assert(fm[1] != fp[1]);
    assert(fp.subrange(0, 2)[1] == fp[1]);
    assert(!(fm =~= fp.subrange(0, fm.len() as int)));
    assert(m.subrange(0, 1) =~= p.subrange(0, 1));
    assert(m[1] != p[1]);
}

/// **Split places in the coarse model.** The model kills both coarse
/// references after the coarse `mut(v[..i])`. Rule 3 kills the reference
/// into `v[j..]` of another split. It spares the reference into the other
/// side `v[i..]` of the same split. The pairs meet the hypotheses of
/// `thm_split_exact_typed`.
pub proof fn ex_split_coarse()
    ensures
        lkills(lplace(7, coarse(seq![st_fld(0), st_seg(1, false)])), lplace(7, coarse(seq![st_fld(0), st_seg(2, true), st_var(0)]))),
        spec_invalidates(seq![st_fld(0), st_seg(1, false)], seq![st_fld(0), st_seg(2, true), st_var(0)]),
        lkills(lplace(7, coarse(seq![st_fld(0), st_seg(1, false)])), lplace(7, coarse(seq![st_fld(0), st_seg(1, true), st_var(0)]))),
        !spec_invalidates(seq![st_fld(0), st_seg(1, false)], seq![st_fld(0), st_seg(1, true), st_var(0)]),
        !no_opposite(seq![st_fld(0), st_seg(1, false)], seq![st_fld(0), st_seg(1, true), st_var(0)]),
{
    let m = seq![st_fld(0), st_seg(1, false)];
    let p2 = seq![st_fld(0), st_seg(2, true), st_var(0)];
    let p1 = seq![st_fld(0), st_seg(1, true), st_var(0)];
    lemma_coarse(m);
    lemma_coarse(p2);
    lemma_coarse(p1);
    assert(coarse(m) =~= seq![st_fld(0), st_elem()]);
    assert(coarse(p2) =~= seq![st_fld(0), st_elem(), st_var(0)]);
    assert(coarse(p1) =~= seq![st_fld(0), st_elem(), st_var(0)]);
    let cm = coarse(m);
    let cp = coarse(p1);
    assert(typed_by(canonical_stab(), cm));
    assert(typed_by(canonical_stab(), cp));
    assert(no_seg(cm));
    assert(no_seg(cp));
    // The coarse model kills: rule 3 holds on the coarse places.
    assert(spec_step_alias(cm[0], cp[0]));
    assert(spec_step_alias(cm[1], cp[1]));
    assert(cp[2].unstable);
    assert(spec_invalidates(cm, cp));
    thm_invalidates_exact_typed(canonical_stab(), 7, cm, 7, cp);
    // Rule 3 on the split places.
    assert(spec_step_alias(m[0], p2[0]));
    assert(spec_step_alias(m[1], p2[1]));
    assert(p2[2].unstable);
    assert(spec_invalidates(m, p2));
    assert(opposite_sides(m[1], p1[1]));
    assert(!spec_step_alias(m[1], p1[1]));
    thm_split_exact_typed(canonical_stab(), 7, m, 7, p1);
}

// ---------------------------------------------------------------------------
// Rule 3 as the kill rule of the B3 checker
// ---------------------------------------------------------------------------

/// The flat path of an inline place is its tail.
pub proof fn lemma_flat_inline(t: Seq<PStep>)
    ensures
        flat(at(t)) == t,
{
    assert(flat(at(t)) =~= t);
}

/// On the B3 example `en_ok` (`rw = &w; rs = &rw.state; pa = &payload of
/// Pair; set_state(mut rs); read rw.score`), rule 3 and `lkills` kill the
/// same references. Thus the two checkers have the same states.
pub proof fn lemma_en_rss(d: spec_fn(PStep) -> Step, ss0: crate::layout::LSState)
    requires
        keeps_stab(d),
        ss0.vars == Map::<Var, LPlace>::empty(),
    ensures
        forall|k: nat| k <= 5 ==> #[trigger] rss_at(d, ss0, en_ok(), k) == lss_at(ss0, en_ok(), k),
{
    let p = en_ok();
    assert(p[0] == crate::layout::LInstr::Borrow { dst: RW(), x: W() });
    assert(p[1] == crate::layout::LInstr::Field { dst: RS(), src: RW(), f: 3 });
    assert(p[2] == crate::layout::LInstr::Variant { dst: PA(), src: RS(), v: 0 });
    assert(p[3] == crate::layout::LInstr::Call { args: seq![(RS(), true)] });
    let s1 = lpost(ss0, p[0]);
    let s2 = lpost(s1, p[1]);
    let s3 = lpost(s2, p[2]);
    let s4 = lpost(s3, p[3]);
    assert(Seq::<PStep>::empty().push(Fd(3)) =~= seq![Fd(3)]);
    assert(seq![Fd(3)].push(Vr(0)) =~= seq![Fd(3), Vr(0)]);
    assert(s1.vars =~= map![RW() => at(seq![])]);
    assert(s2.vars =~= map![RW() => at(seq![]), RS() => at(seq![Fd(3)])]);
    assert(s3.vars =~= map![RW() => at(seq![]), RS() => at(seq![Fd(3)]), PA() => at(seq![Fd(3), Vr(0)])]);
    let args = seq![(RS(), true)];
    let m = at(seq![Fd(3)]);
    assert(s3.vars[args[0].0] == m);
    lemma_flat_inline(seq![]);
    lemma_flat_inline(seq![Fd(3)]);
    lemma_flat_inline(seq![Fd(3), Vr(0)]);
    // The mutation of `w.state` keeps `rw` and `rs`, and kills `pa`.
    assert forall|q: LPlace|
        #![trigger lkilled(s3, args, q)]
        #![trigger rkilled(d, s3, args, q)]
        q == at(seq![]) || q == m implies !lkilled(s3, args, q) && !rkilled(d, s3, args, q) by {
        assert forall|k: int| #![trigger args[k]] 0 <= k < args.len() && args[k].1 implies !lkills(s3.vars[args[k].0], q) && !rkills(
            d,
            s3.vars[args[k].0],
            q,
        ) by {
            assert(k == 0);
            assert(dpath(d, flat(q)).len() == flat(q).len());
            assert(dpath(d, flat(m)).len() == 1);
        }
    }
    let pa = at(seq![Fd(3), Vr(0)]);
    assert(seq![Fd(3)] =~= flat(pa).subrange(0, 1));
    assert(unstable(flat(pa)[1]));
    assert(lkills(m, pa));
    lemma_lkills_rkills(d, m, pa);
    assert(lkilled(s3, args, pa));
    assert(rkilled(d, s3, args, pa));
    assert(rsurvivors(d, s3, args) =~= lsurvivors(s3, args));
    assert(rss_at(d, ss0, p, 0) == ss0);
    assert(lss_at(ss0, p, 0) == ss0);
    assert(rss_at(d, ss0, p, 1) == s1);
    assert(lss_at(ss0, p, 1) == s1);
    assert(rss_at(d, ss0, p, 2) == s2);
    assert(lss_at(ss0, p, 2) == s2);
    assert(rss_at(d, ss0, p, 3) == s3);
    assert(lss_at(ss0, p, 3) == s3);
    assert(rss_at(d, ss0, p, 4) == s4);
    assert(lss_at(ss0, p, 4) == s4);
    assert(rss_at(d, ss0, p, 5) == lpost(s4, p[4]));
    assert(lss_at(ss0, p, 5) == lpost(s4, p[4]));
}

/// **Vacuity guard for the B3 link.** A run of `en_ok` meets every
/// hypothesis of `thm_rule3_layout_sound_from_start`, for each decoding that
/// keeps the stability. The mutable call in `en_ok` kills a reference.
pub proof fn ex_rule3_layout_applies(d: spec_fn(PStep) -> Step)
    requires
        keeps_stab(d),
    ensures
        rcheck(d, wsc(), lss0(), en_ok()),
        exists|trace: Seq<LState>|
            #![trigger is_ltrace(wsc(), en_ok(), trace)]
            {
                &&& is_ltrace(wsc(), en_ok(), trace)
                &&& wf_schema(wsc())
                &&& lwf(wsc(), trace[0])
                &&& rcheck(d, wsc(), linitial(trace[0]), en_ok())
                &&& trace.len() == 6
            },
{
    hide(lstep);
    hide(lub);
    hide(wf_schema);
    hide(lwf);
    example_en_ok();
    example_layout_soundness_applies();
    let trace = choose|trace: Seq<LState>|
        #![trigger is_ltrace(wsc(), en_ok(), trace)]
        {
            &&& is_ltrace(wsc(), en_ok(), trace)
            &&& wf_schema(wsc())
            &&& lwf(wsc(), trace[0])
            &&& lcheck(wsc(), linitial(trace[0]), en_ok())
            &&& trace.len() == 6
            &&& forall|k: int| 0 <= k < 5 ==> !#[trigger] lub(wsc(), trace[k], en_ok()[k])
        };
    let ssi = linitial(trace[0]);
    assert(ssi.vars =~= Map::<Var, LPlace>::empty());
    lemma_en_rss(d, ssi);
    lemma_en_rss(d, lss0());
    assert(lss0().vars =~= Map::<Var, LPlace>::empty());
    assert forall|k: nat| k < en_ok().len() implies #[trigger] linstr_ok(wsc(), rss_at(d, ssi, en_ok(), k), en_ok()[k as int]) by {
        assert(rss_at(d, ssi, en_ok(), k) == lss_at(ssi, en_ok(), k));
    }
    assert forall|k: nat| k < en_ok().len() implies #[trigger] linstr_ok(wsc(), rss_at(d, lss0(), en_ok(), k), en_ok()[k as int]) by {
        assert(rss_at(d, lss0(), en_ok(), k) == lss_at(lss0(), en_ok(), k));
    }
    assert(rcheck(d, wsc(), ssi, en_ok()));
    thm_rule3_layout_sound_from_start(d, wsc(), en_ok(), trace);
}

/// **Rejection agrees on B3.** The B3 checker with rule 3 rejects `en_bad`
/// (a read through `pa` after `set_state(mut rs)`), for each decoding that
/// keeps the stability.
pub proof fn ex_rule3_layout_rejects(d: spec_fn(PStep) -> Step)
    requires
        keeps_stab(d),
    ensures
        !rcheck(d, wsc(), lss0(), en_bad()),
{
    example_en_rejected();
    if rcheck(d, wsc(), lss0(), en_bad()) {
        thm_rcheck_lcheck(d, wsc(), lss0(), en_bad());
    }
}

// ---------------------------------------------------------------------------
// Dataflow
// ---------------------------------------------------------------------------

/// `r = &w; e = &r.items[i]; f(mut r); <last>`, with `w` = local 0, `r` =
/// variable 0, `e` = variable 1, `items` = label 5.
pub open spec fn ex_cfg(last: Instr) -> Cfg {
    seq![
        Node { instr: Instr::Borrow { dst: 0, x: 0 }, succs: seq![1nat] },
        Node { instr: Instr::Child { dst: 1, src: 0, label: 5 }, succs: seq![2nat] },
        Node { instr: Instr::Call { args: seq![(0nat, true)], ret: None }, succs: seq![3nat] },
        Node { instr: last, succs: Seq::<nat>::empty() },
    ]
}

/// The CFG that W0301 accepts: the last node reads `r`.
pub open spec fn ex_ok() -> Cfg {
    ex_cfg(Instr::Read { src: 0, field: 0 })
}

/// The CFG that W0301 rejects: the last node reads `e` after the call.
pub open spec fn ex_bad() -> Cfg {
    ex_cfg(Instr::Read { src: 1, field: 0 })
}

pub open spec fn ex_g() -> Map<Var, Group> {
    Map::empty().insert(0nat, Group { root: 0, path: Seq::empty() }).insert(1nat, Group { root: 0, path: seq![5nat] })
}

pub open spec fn ex_ss0() -> SState {
    SState { locals: Set::empty().insert(0nat), vars: Map::empty(), clos: Map::empty() }
}

/// `r` can be unbound at node 0, `e` at nodes 0 and 1.
pub open spec fn ex_unb() -> spec_fn(Var, int) -> bool {
    |v: Var, n: int| (v == 0 && n == 0) || (v == 1 && (n == 0 || n == 1))
}

/// The call invalidates `e` and not `r`.
pub proof fn lemma_ex_gen(last: Instr)
    requires
        last is Read,
    ensures
        forall|n: int| 0 <= n < 4 && n != 2 ==> !(#[trigger] invalidated_at(ex_cfg(last)[n].instr, ex_g(), 0)),
        !invalidated_at(ex_cfg(last)[2].instr, ex_g(), 0),
        invalidated_at(ex_cfg(last)[2].instr, ex_g(), 1),
        !binds(ex_cfg(last)[2].instr, 1),
{
    let g = ex_g();
    let args = seq![(0nat, true)];
    assert(gsteps(g[0].path).len() == 0);
    assert(!grp_invalidates(g[0], g[0]));
    assert(!call_invalidates(args, g, 0)) by {
        assert forall|k: int| 0 <= k < args.len() implies !(args[k].1 && #[trigger] grp_invalidates(g[args[k].0], g[0])) by {
            assert(k == 0);
        }
    }
    assert(fits(g[0].path));
    assert(fits(g[1].path));
    lemma_grp_invalidates(g[0], g[1]);
    assert(g[1].path.subrange(0, 0) =~= g[0].path);
    assert(strict_child(g[1], g[0]));
    assert(grp_invalidates(g[args[0].0], g[1]));
    assert(call_invalidates(args, g, 1));
}

/// The static facts of the example hold.
pub proof fn lemma_ex_facts(last: Instr)
    requires
        last == (Instr::Read { src: 0, field: 0 }) || last == (Instr::Read { src: 1, field: 0 }),
    ensures
        facts_ok(ex_cfg(last), ex_ss0(), ex_g()),
{
    let cfg = ex_cfg(last);
    let g = ex_g();
    assert(g[0nat].path.push(5nat) =~= seq![5nat]);
    assert forall|n: int| 0 <= n < cfg.len() implies #[trigger] instr_groups_ok(cfg[n].instr, g) by {
        if n == 2 {
            let args = seq![(0nat, true)];
            assert forall|k: int| 0 <= k < args.len() implies g.contains_key(#[trigger] args[k].0) by {
                assert(k == 0);
            }
        }
    }
    assert forall|v: Var| #[trigger] g.contains_key(v) implies fits(g[v].path) by {
        assert(v == 0 || v == 1);
    }
}

/// `r` is never invalid: the empty set is closed for `r`.
pub proof fn lemma_ex_r_valid(last: Instr, n: int)
    requires
        last is Read,
    ensures
        !lfp(ex_cfg(last), ex_g(), 0, n),
{
    let cfg = ex_cfg(last);
    let s = Set::<int>::empty();
    lemma_ex_gen(last);
    let gen = gen_seq(cfg, ex_g(), 0);
    assert forall|p: int| 0 <= p < gen.len() implies !#[trigger] gen[p] by {
        assert(gen[p] == invalidated_at(cfg[p].instr, ex_g(), 0));
    }
    assert(spec_closed(cfg_succ(cfg), gen, kill_seq(cfg, 0), s));
}

/// The bound-before-use hypothesis of the example holds.
pub proof fn lemma_ex_bound(last: Instr)
    requires
        last == (Instr::Read { src: 0, field: 0 }) || last == (Instr::Read { src: 1, field: 0 }),
    ensures
        last == (Instr::Read { src: 0, field: 0 }) ==> bound_before_use(ex_cfg(last), ex_ss0(), ex_g(), ex_unb()),
{
    let cfg = ex_cfg(last);
    let g = ex_g();
    let unb = ex_unb();
    assert forall|v: Var| g.contains_key(v) && !(ex_ss0().vars.contains_key(v) && ex_ss0().vars[v] == g[v]) implies #[trigger] unb(
        v,
        0,
    ) by {
        assert(v == 0 || v == 1);
    }
    assert forall|v: Var, n: int, j: int|
        #![trigger unb(v, n), cfg[n].succs[j]]
        0 <= n < cfg.len() && 0 <= j < cfg[n].succs.len() && unb(v, n) && !binds(cfg[n].instr, v) implies unb(
        v,
        cfg[n].succs[j] as int,
    ) by {
        assert(n == 0 || n == 1);
        assert(j == 0);
    }
    if last == (Instr::Read { src: 0, field: 0 }) {
        assert forall|n: int, v: Var| 0 <= n < cfg.len() && #[trigger] uses(cfg[n].instr, v) implies !unb(v, n) by {
            if n == 2 {
                let args = seq![(0nat, true)];
                let k = choose|k: int| 0 <= k < args.len() && #[trigger] args[k].0 == v;
                assert(k == 0);
            }
        }
    }
}

/// **Vacuity guard.** The accepted example meets every hypothesis of
/// `thm_w0301_no_ub`. Its annotation passes `cfg_check`, and `e` is invalid
/// after the call.
pub proof fn ex_accepted()
    ensures
        facts_ok(ex_ok(), ex_ss0(), ex_g()),
        w0301_ok(ex_ok(), ex_g()),
        bound_before_use(ex_ok(), ex_ss0(), ex_g(), ex_unb()),
        cfg_check(ex_ok(), ex_ss0(), lfp_ann(ex_ok(), ex_ss0(), ex_g(), ex_unb())),
        lfp(ex_ok(), ex_g(), 1, 3),
        !lfp_ann(ex_ok(), ex_ss0(), ex_g(), ex_unb())[3].vars.contains_key(1),
{
    let cfg = ex_ok();
    let g = ex_g();
    let last = Instr::Read { src: 0, field: 0 };
    lemma_ex_facts(last);
    lemma_ex_bound(last);
    lemma_ex_gen(last);
    assert forall|n: int, v: Var| 0 <= n < cfg.len() && #[trigger] uses(cfg[n].instr, v) implies !lfp(cfg, g, v, n) by {
        if n == 2 {
            let args = seq![(0nat, true)];
            let k = choose|k: int| 0 <= k < args.len() && #[trigger] args[k].0 == v;
            assert(k == 0);
        }
        assert(v == 0);
        lemma_ex_r_valid(last, n);
    }
    thm_lfp_annotation_checks(cfg, ex_ss0(), g, ex_unb());
    lemma_lfp_step(cfg, g, 1, 2, 0);
    lemma_ann_vars(cfg, g, ex_unb(), 3);
}

/// The heap of the run: local 0 owns allocation 0, and allocation 0 owns
/// allocation 1 through a kid with label 5.
pub open spec fn ex_heap() -> crate::model::Heap {
    Map::empty().insert(
        0nat,
        crate::model::Obj { stamp: 0, ty: 0, data: seq![1int], kids: seq![(5nat, 1nat)] },
    ).insert(1nat, crate::model::Obj { stamp: 1, ty: 0, data: seq![1int], kids: Seq::empty() })
}

/// The start state of the run.
pub open spec fn ex_d0() -> DState {
    DState { heap: ex_heap(), locals: Map::empty().insert(0nat, 0nat), vars: Map::empty(), clos: Map::empty(), next_stamp: 2 }
}

/// The state after `r = &w`.
pub open spec fn ex_d1() -> DState {
    DState { vars: ex_d0().vars.insert(0nat, ptr_to(ex_heap(), 0)), ..ex_d0() }
}

/// The state after `e = &r.items[i]`.
pub open spec fn ex_d2() -> DState {
    DState { vars: ex_d1().vars.insert(1nat, ptr_to(ex_heap(), 1)), ..ex_d1() }
}

/// **Vacuity guard with a run.** A concrete run of the accepted example up
/// to the call meets the run hypotheses of `thm_w0301_no_ub` (`inv` at the
/// start and `is_cfg_trace`). Thus all its hypotheses hold together, and
/// the theorem gives that the call does not get a dangling argument.
pub proof fn ex_accepted_run()
    ensures
        inv(ex_d0(), ex_ss0()),
        is_cfg_trace(ex_ok(), seq![0nat, 1nat, 2nat], seq![ex_d0(), ex_d1(), ex_d2()]),
        !ub(ex_d2(), ex_ok()[2].instr),
{
    let h = ex_heap();
    let d0 = ex_d0();
    let path = seq![0nat, 1nat, 2nat];
    let trace = seq![ex_d0(), ex_d1(), ex_d2()];
    let cfg = ex_ok();
    // The start state is well formed.
    assert forall|b1: crate::model::Addr, i1: int, b2: crate::model::Addr, i2: int, c: crate::model::Addr|
        #[trigger] owns(h, b1, i1, c) && #[trigger] owns(h, b2, i2, c) implies b1 == b2 && i1 == i2 by {
        assert(b1 == 0 || b1 == 1);
        assert(b2 == 0 || b2 == 1);
    }
    assert forall|b: crate::model::Addr, i: int| !#[trigger] owns(h, b, i, 0nat) by {
        if owns(h, b, i, 0nat) {
            assert(b == 0 || b == 1);
        }
    }
    assert forall|a: crate::model::Addr, b: crate::model::Addr|
        h.contains_key(a) && h.contains_key(b) && #[trigger] h[a].stamp == #[trigger] h[b].stamp implies a == b by {
        assert(a == 0 || a == 1);
        assert(b == 0 || b == 1);
    }
    assert forall|b: crate::model::Addr, i: int|
        h.contains_key(b) && 0 <= i < h[b].kids.len() implies h.contains_key(#[trigger] h[b].kids[i].1) by {
        assert(b == 0 || b == 1);
    }
    assert(wf(d0));
    assert(ex_ss0().locals =~= d0.locals.dom());
    assert(inv(d0, ex_ss0()));
    // The run follows the CFG edges.
    assert(step(ex_d0(), cfg[0].instr, ex_d1()));
    assert(kid_at(h, ex_d1().vars[0nat].addr, (5nat, 0nat)) == Some(1nat));
    assert(step(ex_d1(), cfg[1].instr, ex_d2()));
    assert(cfg[0].succs.contains(1nat)) by {
        assert(cfg[0].succs[0] == 1nat);
    }
    assert(cfg[1].succs.contains(2nat)) by {
        assert(cfg[1].succs[0] == 2nat);
    }
    assert(is_cfg_trace(cfg, path, trace));
    // The theorem applies.
    ex_accepted();
    thm_w0301_no_ub(cfg, ex_ss0(), ex_g(), ex_unb(), path, trace);
    assert(trace[2] == ex_d2());
    assert(path[2] == 2);
}

/// **Rejection agrees.** W0301 rejects the bad example, and no model
/// annotation with the static groups passes `cfg_check` for it.
pub proof fn ex_rejected(a: Seq<SState>)
    requires
        agrees(a, ex_g()),
    ensures
        uses(ex_bad()[3].instr, 1) && lfp(ex_bad(), ex_g(), 1, 3),
        !cfg_check(ex_bad(), ex_ss0(), a),
{
    let cfg = ex_bad();
    let g = ex_g();
    let last = Instr::Read { src: 1, field: 0 };
    lemma_ex_facts(last);
    lemma_ex_gen(last);
    lemma_lfp_step(cfg, g, 1, 2, 0);
    let gen = gen_eff_seq(cfg, g, 1);
    let kill = kill_seq(cfg, 1);
    lemma_cfg_succ(cfg, gen, kill);
    assert(gen[2]);
    lemma_step_sound(cfg_succ(cfg), gen, kill, 2, 0);
    assert(cfg_succ(cfg)[2][0] as int == 3);
    if cfg_check(cfg, ex_ss0(), a) {
        thm_model_invalid_contains_lfp(cfg, ex_ss0(), g, a, 1, 3);
        assert(instr_ok(a[3], cfg[3].instr));
    }
}

/// A loop: `0: r = &w; 1: e = &r.items[i]; 2: read e; 3: f(mut r)`, then
/// back to 1 or on to `4: read r`. The call invalidates `e`, and node 1
/// rebinds `e` before the read.
pub open spec fn lp_cfg() -> Cfg {
    seq![
        Node { instr: Instr::Borrow { dst: 0, x: 0 }, succs: seq![1nat] },
        Node { instr: Instr::Child { dst: 1, src: 0, label: 5 }, succs: seq![2nat] },
        Node { instr: Instr::Read { src: 1, field: 0 }, succs: seq![3nat] },
        Node { instr: Instr::Call { args: seq![(0nat, true)], ret: None }, succs: seq![1nat, 4nat] },
        Node { instr: Instr::Read { src: 0, field: 0 }, succs: Seq::<nat>::empty() },
    ]
}

/// A closed set for `e` in the loop: nodes 1 and 4.
pub open spec fn lp_e_set() -> Set<int> {
    Set::empty().insert(1int).insert(4int)
}

/// **Vacuity guard with a back edge and a rebind.** The loop meets the
/// static hypotheses of `thm_w0301_no_ub`. The fixpoint for `e` holds the
/// rebind node 1 and the exit node 4. It does not hold the read at node 2:
/// the rebind at node 1 stops the propagation.
pub proof fn ex_loop_accepted()
    ensures
        facts_ok(lp_cfg(), ex_ss0(), ex_g()),
        w0301_ok(lp_cfg(), ex_g()),
        bound_before_use(lp_cfg(), ex_ss0(), ex_g(), ex_unb()),
        cfg_check(lp_cfg(), ex_ss0(), lfp_ann(lp_cfg(), ex_ss0(), ex_g(), ex_unb())),
        lfp(lp_cfg(), ex_g(), 1, 1),
        lfp(lp_cfg(), ex_g(), 1, 4),
        !lfp(lp_cfg(), ex_g(), 1, 2),
{
    let cfg = lp_cfg();
    let g = ex_g();
    let unb = ex_unb();
    let args = seq![(0nat, true)];
    // facts_ok
    assert(g[0nat].path.push(5nat) =~= seq![5nat]);
    assert forall|n: int| 0 <= n < cfg.len() implies #[trigger] instr_groups_ok(cfg[n].instr, g) by {
        if n == 3 {
            assert forall|k: int| 0 <= k < args.len() implies g.contains_key(#[trigger] args[k].0) by {
                assert(k == 0);
            }
        }
    }
    assert forall|v: Var| #[trigger] g.contains_key(v) implies fits(g[v].path) by {
        assert(v == 0 || v == 1);
    }
    assert(facts_ok(cfg, ex_ss0(), g));
    // gen and kill
    assert(!grp_invalidates(g[0], g[0]));
    assert(!call_invalidates(args, g, 0)) by {
        assert forall|k: int| 0 <= k < args.len() implies !(args[k].1 && #[trigger] grp_invalidates(g[args[k].0], g[0])) by {
            assert(k == 0);
        }
    }
    lemma_grp_invalidates(g[0], g[1]);
    assert(g[1].path.subrange(0, 0) =~= g[0].path);
    assert(grp_invalidates(g[args[0].0], g[1]));
    assert(call_invalidates(args, g, 1));
    // `r` is never invalid.
    let gen0 = gen_seq(cfg, g, 0);
    assert forall|p: int| 0 <= p < gen0.len() implies !#[trigger] gen0[p] by {
        assert(gen0[p] == invalidated_at(cfg[p].instr, g, 0));
    }
    assert(spec_closed(cfg_succ(cfg), gen0, kill_seq(cfg, 0), Set::<int>::empty()));
    // `e`: the set {1, 4} is closed.
    let gen1 = gen_seq(cfg, g, 1);
    let kill1 = kill_seq(cfg, 1);
    lemma_cfg_succ(cfg, gen1, kill1);
    let s = lp_e_set();
    assert forall|p: int, q: int| 0 <= p < gen1.len() && gen1[p] && #[trigger] spec_edge(cfg_succ(cfg), p, q) implies s.contains(q) by {
        assert(gen1[p] == invalidated_at(cfg[p].instr, g, 1));
        assert(p == 3);
        let j = choose|j: int| 0 <= j < cfg_succ(cfg)[p].len() && cfg_succ(cfg)[p][j] as int == q;
        assert(cfg_succ(cfg)[p][j] as int == cfg[p].succs[j] as int);
    }
    assert forall|p: int, q: int| 0 <= p < kill1.len() && s.contains(p) && !kill1[p] && #[trigger] spec_edge(cfg_succ(cfg), p, q) implies s.contains(q) by {
        assert(p == 1 || p == 4);
        assert(kill1[1]);
        assert(p == 4);
        assert(cfg_succ(cfg)[4].len() == 0);
    }
    assert(spec_closed(cfg_succ(cfg), gen1, kill1, s));
    assert(!s.contains(2));
    // w0301_ok
    assert forall|n: int, v: Var| 0 <= n < cfg.len() && #[trigger] uses(cfg[n].instr, v) implies !lfp(cfg, g, v, n) by {
        if n == 3 {
            let k = choose|k: int| 0 <= k < args.len() && #[trigger] args[k].0 == v;
            assert(k == 0);
        }
        if v == 1 {
            assert(n == 2);
        } else {
            assert(v == 0);
        }
    }
    // bound_before_use
    assert forall|v: Var| g.contains_key(v) && !(ex_ss0().vars.contains_key(v) && ex_ss0().vars[v] == g[v]) implies #[trigger] unb(v, 0) by {
        assert(v == 0 || v == 1);
    }
    assert forall|v: Var, n: int, j: int|
        #![trigger unb(v, n), cfg[n].succs[j]]
        0 <= n < cfg.len() && 0 <= j < cfg[n].succs.len() && unb(v, n) && !binds(cfg[n].instr, v) implies unb(v, cfg[n].succs[j] as int) by {
        assert(n == 0 || n == 1);
        assert(j == 0);
    }
    assert forall|n: int, v: Var| 0 <= n < cfg.len() && #[trigger] uses(cfg[n].instr, v) implies !unb(v, n) by {
        if n == 3 {
            let k = choose|k: int| 0 <= k < args.len() && #[trigger] args[k].0 == v;
            assert(k == 0);
        }
    }
    thm_lfp_annotation_checks(cfg, ex_ss0(), g, unb);
    lemma_lfp_step(cfg, g, 1, 3, 0);
    lemma_lfp_step(cfg, g, 1, 3, 1);
}

/// `r = &w; e = f(mut r) returning &r.items[i]; read e`, in B1 form: the call
/// binds `e` in the same node.
pub open spec fn ex_ret() -> Cfg {
    seq![
        Node { instr: Instr::Borrow { dst: 0, x: 0 }, succs: seq![1nat] },
        Node {
            instr: Instr::Call { args: seq![(0nat, true)], ret: Some(Ret { dst: 1, arg: 0, path: seq![5nat] }) },
            succs: seq![2nat],
        },
        Node { instr: Instr::Read { src: 1, field: 0 }, succs: Seq::<nat>::empty() },
    ]
}

/// An annotation for `ex_ret` that keeps `e` valid after the call.
pub open spec fn ex_ret_ann() -> Seq<SState> {
    let l = ex_ss0().locals;
    let g = ex_g();
    seq![
        SState { locals: l, vars: Map::empty(), clos: Map::empty() },
        SState { locals: l, vars: Map::empty().insert(0nat, g[0nat]), clos: Map::empty() },
        SState { locals: l, vars: Map::empty().insert(0nat, g[0nat]).insert(1nat, g[1nat]), clos: Map::empty() },
    ]
}

/// **Gap witness.** A B1 call that mutates `r` and returns `e` into `r`
/// both invalidates and rebinds `e`. The checker marks `e` invalid after the
/// node, but a model annotation keeps `e` valid there. Thus the fixpoint is
/// a strict superset of the model must-invalid set on such nodes. Sema
/// binds the result of a call at a separate `let` node, so its CFGs do not
/// have this shape.
pub proof fn ex_gen_and_kill()
    ensures
        invalidated_at(ex_ret()[1].instr, ex_g(), 1) && binds(ex_ret()[1].instr, 1),
        lfp(ex_ret(), ex_g(), 1, 2),
        cfg_check(ex_ret(), ex_ss0(), ex_ret_ann()),
        ex_ret_ann()[2].vars.contains_key(1),
{
    let cfg = ex_ret();
    let g = ex_g();
    let a = ex_ret_ann();
    let args = seq![(0nat, true)];
    let ret = Some(Ret { dst: 1, arg: 0, path: seq![5nat] });
    // Rule 3 at node 1.
    assert(fits(g[0].path));
    assert(fits(g[1].path));
    lemma_grp_invalidates(g[0], g[1]);
    assert(g[1].path.subrange(0, 0) =~= g[0].path);
    assert(grp_invalidates(g[args[0].0], g[1]));
    assert(call_invalidates(args, g, 1));
    assert(cfg_wf(cfg));
    lemma_lfp_step(cfg, g, 1, 1, 0);
    // The annotation passes the B1 checker.
    let gs = arg_groups(a[1], args);
    assert(gs[0] == (g[0nat], true));
    assert(!strict_child(g[0nat], g[0nat]));
    assert(!killed(gs, gs[0].0)) by {
        assert forall|k: int| 0 <= k < gs.len() implies !(gs[k].1 && #[trigger] strict_child(gs[0].0, gs[k].0)) by {
            assert(k == 0);
        }
    }
    assert(!killed(gs, g[0nat]));
    assert(instr_ok(a[1], cfg[1].instr));
    assert(sub_state(a[0], ex_ss0()));
    let p0 = post(a[0], cfg[0].instr);
    assert(sub_state(a[1], p0));
    let p1 = post(a[1], cfg[1].instr);
    assert(g[0nat].path + seq![5nat] =~= g[1nat].path);
    assert(p1.vars.contains_key(0nat) && p1.vars[0nat] == g[0nat]);
    assert(p1.vars.contains_key(1nat) && p1.vars[1nat] == g[1nat]);
    assert(a[2].vars.submap_of(p1.vars));
    assert(sub_state(a[2], p1));
    assert forall|n: int| 0 <= n < cfg.len() implies #[trigger] instr_ok(a[n], cfg[n].instr) by {}
    assert forall|n: int, j: int| 0 <= n < cfg.len() && 0 <= j < cfg[n].succs.len() implies #[trigger] cfg[n].succs[j]
        < cfg.len() && sub_state(a[cfg[n].succs[j] as int], post(a[n], cfg[n].instr)) by {
        assert(j == 0);
    }
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

/// A program whose block 0 is a clause with the code `code`.
pub open spec fn ex_prog(code: Seq<em::Instr>, mode: em::Mode) -> em::Prog {
    em::Prog {
        effs: Map::empty(),
        blocks: Map::empty().insert(
            0nat,
            em::Block { sig: em::Sig { caps: Seq::empty(), rets: Seq::empty(), kmode: Some(mode) }, code },
        ),
        main: 0,
    }
}

/// A state that runs the clause frame of continuation 0 at `pc`.
pub open spec fn ex_state(pc: nat, multi: bool) -> em::State {
    em::State {
        stack: seq![
            em::Frame::Code(
                em::CFrame { block: 0, pc, env: Seq::empty(), slots: Map::empty(), k: Some(0nat) },
            ),
        ],
        pending: Seq::empty(),
        res: Map::empty(),
        konts: Map::empty().insert(0nat, em::Kont { frames: Seq::empty(), multi, used: false }),
        hinfo: Map::empty(),
        next_res: 0,
        next_k: 1,
        next_h: 0,
    }
}

/// **Vacuity guard and E2 link.** A clause resumes a `once` continuation
/// twice. The first exec resume is the model step. The second exec resume
/// fails, and the model state is `err_resume_used` there.
pub fn ex_double_resume() {
    let ghost prog = ex_prog(seq![em::Instr::Resume, em::Instr::Resume], em::Mode::Once);
    let ghost s = ex_state(0, false);
    let mut k = Continuation::new(false);
    proof {
        assert(em::tf(s).k == Some(0nat));
        assert(em::at_instr(prog, s));
        assert(em::resume_ok_dyn(s, em::tf(s)));
    }
    let r1 = resume_linked(&mut k, Ghost(prog), Ghost(s));
    assert(r1 is Ok);
    let ghost s2 = em::do_resume(s);
    proof {
        assert(s2.stack =~= seq![em::Frame::Code(em::adv(em::tf(s)))]);
        assert(em::tf(s2) == em::adv(em::tf(s)));
        assert(em::at_instr(prog, s2));
        assert(s2.konts[0nat].used);
        assert(em::err_resume_used(prog, s2));
    }
    let r2 = resume_linked(&mut k, Ghost(prog), Ghost(s2));
    assert(r2 is Err);
}

/// **The `multi` drop difference.** A clause returns without a resume of a
/// fresh `multi` continuation. The exec reports an abort. The model does not
/// unwind (`holds_fresh` is false), and its record does not change.
pub fn ex_multi_drop() {
    let ghost prog = ex_prog(seq![em::Instr::Return], em::Mode::Multi);
    let ghost s = ex_state(0, true);
    let mut k = Continuation::new(true);
    proof {
        assert(em::at_instr(prog, s));
        assert(!em::nonempty(em::tf(s).slots));
    }
    let aborts = return_linked(&mut k, Ghost(prog), Ghost(s));
    assert(aborts);
    assert(!em::holds_fresh(s, em::tf(s)));
}

/// **Gap witness: a resume after the `multi` abort.** A clause returns
/// without a resume of a fresh `multi` continuation: the exec record is
/// `Dropped`. Another copy of the clause frame then resumes. The model
/// record did not change, and the model allows the resume. The exec resume
/// fails.
pub fn ex_multi_dropped_resume() {
    let ghost prog = ex_prog(seq![em::Instr::Return, em::Instr::Resume], em::Mode::Multi);
    let ghost s = ex_state(0, true);
    let mut k = Continuation::new(true);
    proof {
        assert(em::at_instr(prog, s));
        assert(!em::nonempty(em::tf(s).slots));
    }
    let aborts = return_linked(&mut k, Ghost(prog), Ghost(s));
    assert(aborts);
    assert(k.state == ContState::Dropped);
    let ghost s2 = ex_state(1, true);
    proof {
        assert(em::do_return(s).konts[0nat] == s.konts[0nat]);
        assert(em::at_instr(prog, s2));
        assert(em::resume_ok_dyn(s2, em::tf(s2)));
        assert(kont_rel(k, s2.konts[0nat]));
    }
    let r = resume_linked(&mut k, Ghost(prog), Ghost(s2));
    assert(r is Err);
    assert(em::resume_ok_dyn(s2, em::tf(s2)));
}

/// A fresh `once` continuation dropped at a return aborts in exec and in the model.
pub fn ex_once_drop() {
    let ghost prog = ex_prog(seq![em::Instr::Return], em::Mode::Once);
    let ghost s = ex_state(0, false);
    let mut k = Continuation::new(false);
    proof {
        assert(em::at_instr(prog, s));
        assert(!em::nonempty(em::tf(s).slots));
        assert(em::holds_fresh(s, em::tf(s)));
    }
    let aborts = return_linked(&mut k, Ghost(prog), Ghost(s));
    assert(aborts);
    assert(k.state == ContState::Dropped);
}

/// A frame of block 0 at `pc` with the slots `slots`.
pub open spec fn ex_frame(pc: nat, slots: Map<em::Slot, em::ResId>) -> em::CFrame {
    em::CFrame { block: 0, pc, env: Seq::empty(), slots, k: None }
}

/// A state that runs the frame `f`, with the resources `res`.
pub open spec fn ex_lin_state(f: em::CFrame, res: Map<em::ResId, em::Res>, next_res: nat) -> em::State {
    em::State {
        stack: seq![em::Frame::Code(f)],
        pending: Seq::empty(),
        res,
        konts: Map::empty(),
        hinfo: Map::empty(),
        next_res,
        next_k: 0,
        next_h: 0,
    }
}

/// **Vacuity guard for the linear link.** The code is `acquire 0; consume 0`.
/// The exec acquire and the first exec consume are the model steps. Then a
/// duplicated frame (for example, a copy that a `multi` continuation makes)
/// holds slot 0 again, with the resource consumed. The model state is
/// `err_consumed_twice` there, and the exec consume fails.
pub fn ex_consume_twice() {
    let ghost prog = ex_prog(
        seq![em::Instr::Acquire { slot: 0, on_abort: true }, em::Instr::Consume { slot: 0 }],
        em::Mode::Once,
    );
    let ghost s0 = ex_lin_state(ex_frame(0, Map::empty()), Map::empty(), 0);
    proof {
        assert(em::at_instr(prog, s0));
    }
    let mut l = acquire_linked(Ghost(prog), Ghost(s0), Ghost(0nat), true);
    assert(em::step_acquire(prog, s0, em::do_acquire(s0, 0, true)));
    let ghost s1 = em::do_acquire(s0, 0, true);
    proof {
        assert(s1.stack =~= seq![em::Frame::Code(ex_frame(1, Map::empty().insert(0nat, 0nat)))]);
        assert(em::tf(s1) == ex_frame(1, Map::empty().insert(0nat, 0nat)));
        assert(em::at_instr(prog, s1));
        assert(em::slot_live(s1, em::tf(s1), 0));
    }
    let r1 = consume_linked(&mut l, Ghost(prog), Ghost(s1), Ghost(0nat));
    assert(r1 is Ok);
    assert(em::step_consume(prog, s1, em::do_consume(s1, 0)));
    assert(l.state == LinState::Consumed);
    // A duplicated frame still holds slot 0. The resource is consumed.
    let ghost s2 = em::State { res: em::do_consume(s1, 0).res, ..s1 };
    proof {
        assert(em::tf(s2) == em::tf(s1));
        assert(em::at_instr(prog, s2));
        assert(s2.res[0nat].st == em::RState::Consumed);
        assert(em::err_consumed_twice(prog, s2));
    }
    let r2 = consume_linked(&mut l, Ghost(prog), Ghost(s2), Ghost(0nat));
    assert(r2 is Err);
    assert(l.state == LinState::Consumed);
}

/// A state whose unwinder has one pending frame that holds slot 0. The
/// resource has the state `st`, and `on_abort` tells if its type has
/// `on abort`.
pub open spec fn ex_unwind_state(st: em::RState, on_abort: bool) -> em::State {
    em::State {
        stack: Seq::empty(),
        pending: seq![em::Frame::Code(ex_frame(0, Map::empty().insert(0nat, 0nat)))],
        res: Map::empty().insert(0nat, em::Res { st, on_abort }),
        konts: Map::empty(),
        hinfo: Map::empty(),
        next_res: 1,
        next_k: 0,
        next_h: 0,
    }
}

/// **Vacuity guard for the unwind link.** The unwinder runs `on abort` for a
/// live value: the exec unwind is the model step `step_unwind_abort`. A
/// duplicated pending frame then finds the aborted value: the model state
/// is `err_unwind_dead`, and the exec unwind does not run `on abort` again.
pub fn ex_unwind_once() {
    let ghost s = ex_unwind_state(em::RState::Live, true);
    let mut l = Linear::new(true);
    proof {
        assert(em::pf(s) == ex_frame(0, Map::empty().insert(0nat, 0nat)));
        assert(em::max_slot(em::pf(s).slots, 0));
    }
    let run1 = unwind_linked(&mut l, Ghost(s), Ghost(0nat));
    assert(run1 == Ok::<bool, LinError>(true));
    assert(em::step_unwind_abort(s, em::do_abort(s, 0)));
    assert(l.state == LinState::Aborted);
    let ghost s2 = ex_unwind_state(em::RState::Aborted, true);
    proof {
        assert(em::pf(s2) == ex_frame(0, Map::empty().insert(0nat, 0nat)));
        assert(em::max_slot(em::pf(s2).slots, 0));
        assert(em::err_unwind_dead(s2));
    }
    let run2 = unwind_linked(&mut l, Ghost(s2), Ghost(0nat));
    assert(run2 == Ok::<bool, LinError>(false));
    assert(l.state == LinState::Aborted);
}

/// **Vacuity guard for E3.** The unwinder finds a live value whose type has
/// no `on abort`. The model state is `err_no_on_abort`. The exec unwind
/// fails and does not change the record.
pub fn ex_unwind_no_on_abort() {
    let ghost s = ex_unwind_state(em::RState::Live, false);
    let mut l = Linear::new(false);
    proof {
        assert(em::pf(s) == ex_frame(0, Map::empty().insert(0nat, 0nat)));
        assert(em::max_slot(em::pf(s).slots, 0));
    }
    let r = unwind_linked(&mut l, Ghost(s), Ghost(0nat));
    assert(r is Err);
    assert(em::err_no_on_abort(s));
    assert(l.state == LinState::Live);
}

} // verus!
