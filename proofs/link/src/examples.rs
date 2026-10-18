//! # Examples: the hypotheses hold, and each gap is real
//!
//! * Places: rule 3 and the model agree on a typed place pair. Split steps
//!   break the exact link (`ex_split_alias_not_in_model`).
//! * Dataflow: a CFG with a borrow, a child reference, a mutating call and a
//!   read meets every hypothesis of `thm_w0301_no_ub`. The variant that reads
//!   the child reference after the call is rejected by W0301 and by every
//!   model annotation. A B1 call that both invalidates and rebinds a
//!   reference shows why `thm_dataflow_exact` needs `no_gen_kill`.
//! * Lifecycle: a double resume of a `once` continuation fails in exec where
//!   the model reaches `err_resume_used`. A fresh `multi` continuation shows
//!   the abort difference of `drop_now`.

use vstd::prelude::*;
use crate::places::{Step, StepKind, spec_invalidates, spec_step_alias};
use crate::layout::{lkills, flat};
use crate::places_link::*;
use crate::dataflow_link::*;
use crate::dataflow::{spec_closed, spec_in_lfp, lemma_step_sound};
use crate::model::{Instr, SState, Group, Var, Ret, post, instr_ok, killed, strict_child, arg_groups};
use crate::cfg::{Cfg, Node, cfg_check, sub_state};
use crate::lifecycle::{Continuation, ContState};
use crate::lifecycle_link::*;
use crate::effects_model as em;

verus! {

// ---------------------------------------------------------------------------
// Places
// ---------------------------------------------------------------------------

pub open spec fn fld(id: u32) -> Step {
    Step { kind: StepKind::Field { id }, unstable: false }
}

pub open spec fn elem() -> Step {
    Step { kind: StepKind::Elem, unstable: true }
}

pub open spec fn var(id: u32) -> Step {
    Step { kind: StepKind::Variant { id }, unstable: true }
}

pub open spec fn seg(split: u32, hi: bool) -> Step {
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
        spec_invalidates(seq![fld(0)], seq![fld(0), elem()]),
        lkills(lplace(7, seq![fld(0)]), lplace(7, seq![fld(0), elem()])),
        !spec_invalidates(seq![fld(0), elem()], seq![fld(0), elem()]),
        !lkills(lplace(7, seq![fld(0), elem()]), lplace(7, seq![fld(0), elem()])),
{
    let m = seq![fld(0)];
    let p = seq![fld(0), elem()];
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
        spec_invalidates(seq![fld(0), seg(1, false)], seq![fld(0), seg(2, true), var(0)]),
        !lkills(lplace(7, seq![fld(0), seg(1, false)]), lplace(7, seq![fld(0), seg(2, true), var(0)])),
        !alias_exact(seq![fld(0), seg(1, false)], seq![fld(0), seg(2, true), var(0)]),
{
    let m = seq![fld(0), seg(1, false)];
    let p = seq![fld(0), seg(2, true), var(0)];
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

} // verus!
