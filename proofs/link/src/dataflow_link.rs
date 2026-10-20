//! # L2. Dataflow: `propagate` and the B1 CFG model
//!
//! The checker computes W0301 for one reference `v` with the verified
//! `propagate` (`crates/weft-verified/src/dataflow.rs`): `gen` marks the nodes
//! that invalidate `v` (rule 3), `kill` marks the nodes that rebind `v`. The
//! result is the least fixpoint `spec_in_lfp`.
//!
//! The B1 model (`proofs/borrowing/src/cfg.rs`) accepts a CFG with any
//! annotation `ann` that passes `cfg_check`. The model treats `v` as invalid
//! at node `n` if `v` is not in `ann[n].vars`.
//!
//! This file reads the facts of the checker off a B1 CFG (`binds`, `uses`,
//! `invalidated_at`) and proves:
//!
//! * `thm_lfp_annotation_checks` (soundness): if W0301 accepts, the
//!   annotation that keeps `v` valid exactly outside the fixpoint (and
//!   outside the nodes where `v` can be unbound) passes `cfg_check`.
//! * `thm_w0301_no_ub`: with `cfg_soundness`, no run of such a CFG has UB.
//! * `thm_model_invalid_contains_lfp` (minimality): each annotation that
//!   passes `cfg_check` marks `v` invalid at each node of the fixpoint of
//!   `gen` minus `kill`.
//! * `thm_must_invalid_in_lfp` (the soundness direction as sets): if W0301
//!   accepts, each node where every accepted annotation marks `v` invalid
//!   is in the fixpoint or in `unb`.
//! * `thm_dataflow_exact`: if no node both invalidates and rebinds `v`, the
//!   fixpoint is inside the set of nodes where every accepted annotation
//!   marks `v` invalid. With the result above, the two sets are equal
//!   outside `unb`.
//! * `invalid_at`: the exec `propagate` returns this fixpoint.
//!
//! The direction. Let `must` be the set of nodes where each accepted model
//! annotation with the static groups marks `v` invalid.
//!
//! * Soundness needs `must` inside the checker set. This holds outside
//!   `unb`, if `facts_ok`, `w0301_ok` and `bound_before_use` hold
//!   (`thm_must_invalid_in_lfp`, from `thm_lfp_annotation_checks`).
//!   `facts_ok` excludes closures.
//! * The fixpoint of `gen` minus `kill` is inside `must` for each B1 CFG
//!   (`thm_model_invalid_contains_lfp`). That fixpoint is inside the checker
//!   fixpoint (`lemma_lfp_contains_eff`).
//! * If no node both invalidates and rebinds `v`, the two fixpoints are
//!   equal. At a node that does both, the checker marks `v` invalid after the
//!   node, but the model keeps the new value of `v` valid (`ex_gen_and_kill`).

use vstd::prelude::*;
use crate::dataflow::{spec_edge, spec_closed, spec_in_lfp, spec_well_formed, spec_view, propagate, lemma_step_sound};
use crate::model::{Instr, SState, Group, Var, Label, DState, strict_child, killed, arg_groups, post, instr_ok, ret_ok, ub};
use crate::cfg::{Cfg, cfg_check, sub_state, is_cfg_trace, cfg_soundness};
use crate::soundness::inv;
use crate::places::{Step, StepKind, spec_invalidates, spec_step_alias};

verus! {

// ---------------------------------------------------------------------------
// Groups as weft places
// ---------------------------------------------------------------------------

/// The field step for the child-group label `l`.
pub open spec fn label_step(l: Label) -> Step {
    Step { kind: StepKind::Field { id: l as u32 }, unstable: false }
}

/// The element step of a child group. It is unstable.
pub open spec fn elem_step() -> Step {
    Step { kind: StepKind::Elem, unstable: true }
}

/// The weft path of a group path: each label `l` becomes `.l[]`, the field
/// that holds the group and then its elements (for example `d.rings[]`).
pub open spec fn gsteps(path: Seq<Label>) -> Seq<Step> {
    Seq::new(2 * path.len(), |i: int| if i % 2 == 0 { label_step(path[i / 2]) } else { elem_step() })
}

/// Rule 3 on two groups, as the checker computes it: the same root, then `spec_invalidates`.
pub open spec fn grp_invalidates(m: Group, p: Group) -> bool {
    m.root == p.root && spec_invalidates(gsteps(m.path), gsteps(p.path))
}

/// Each label of the path fits into a step id.
pub open spec fn fits(path: Seq<Label>) -> bool {
    forall|i: int| 0 <= i < path.len() ==> #[trigger] path[i] <= u32::MAX
}

/// **Rule 3 is the B1 kill rule.** On groups whose labels fit, rule 3 kills
/// `p` after a mutation of `m` iff `p` is a strict child group of `m`.
pub proof fn lemma_grp_invalidates(m: Group, p: Group)
    requires
        fits(m.path),
        fits(p.path),
    ensures
        grp_invalidates(m, p) == strict_child(p, m),
{
    let gm = gsteps(m.path);
    let gp = gsteps(p.path);
    if grp_invalidates(m, p) {
        assert(m.path.len() < p.path.len());
        assert forall|k: int| 0 <= k < m.path.len() implies #[trigger] p.path.subrange(0, m.path.len() as int)[k]
            == m.path[k] by {
            assert(gm[2 * k] == label_step(m.path[k]));
            assert(gp[2 * k] == label_step(p.path[k]));
            assert(spec_step_alias(gm[2 * k], gp[2 * k]));
        }
        assert(p.path.subrange(0, m.path.len() as int) =~= m.path);
    }
    if strict_child(p, m) {
        assert forall|i: int|
            #![trigger gm[i]]
            #![trigger gp[i]]
            0 <= i < gm.len() implies spec_step_alias(gm[i], gp[i]) by {
            if i % 2 == 0 {
                assert(p.path.subrange(0, m.path.len() as int)[i / 2] == p.path[i / 2]);
            }
        }
        let j: int = 2 * m.path.len() as int + 1;
        assert(gp[j] == elem_step());
        assert(gp[j].unstable);
    }
}

// ---------------------------------------------------------------------------
// The facts of a B1 CFG
// ---------------------------------------------------------------------------

/// The CFG is well formed for `propagate`.
pub open spec fn cfg_wf(cfg: Cfg) -> bool {
    &&& 0 < cfg.len() <= usize::MAX
    &&& forall|n: int, j: int|
        0 <= n < cfg.len() && 0 <= j < cfg[n].succs.len() ==> #[trigger] cfg[n].succs[j] < cfg.len()
}

/// The successor lists of a CFG in the form that `propagate` takes.
pub open spec fn cfg_succ(cfg: Cfg) -> Seq<Seq<usize>> {
    Seq::new(cfg.len(), |n: int| Seq::new(cfg[n].succs.len(), |j: int| cfg[n].succs[j] as usize))
}

/// `rebound_at(v, n)`: the instruction gives `v` a new value.
pub open spec fn binds(i: Instr, v: Var) -> bool {
    match i {
        Instr::Borrow { dst, .. } => dst == v,
        Instr::Child { dst, .. } => dst == v,
        Instr::Copy { dst, .. } => dst == v,
        Instr::Call { ret, .. } => ret is Some && ret->0.dst == v,
        Instr::Invoke { ret, .. } => ret is Some && ret->0.dst == v,
        _ => false,
    }
}

/// `uses(v, n)`: the instruction reads the reference `v`.
pub open spec fn uses(i: Instr, v: Var) -> bool {
    match i {
        Instr::Child { src, .. } => src == v,
        Instr::Copy { src, .. } => src == v,
        Instr::Read { src, .. } => src == v,
        Instr::Write { src, .. } => src == v,
        Instr::Call { args, .. } => arg_uses(args, v),
        _ => false,
    }
}

/// `v` is an argument. A separate function, for the same reason as `call_invalidates`.
pub open spec fn arg_uses(args: Seq<(Var, bool)>, v: Var) -> bool {
    exists|k: int| 0 <= k < args.len() && #[trigger] args[k].0 == v
}

/// `invalidated_at(v, n)`: a mutable argument of the call invalidates the
/// place of `v` (rule 3, `grp_invalidates`).
pub open spec fn invalidated_at(i: Instr, g: Map<Var, Group>, v: Var) -> bool {
    match i {
        Instr::Call { args, .. } => call_invalidates(args, g, v),
        _ => false,
    }
}

/// A mutable argument invalidates the place of `v`. This is a separate
/// function: then a proof can give a witness for a `Call` that it builds.
pub open spec fn call_invalidates(args: Seq<(Var, bool)>, g: Map<Var, Group>, v: Var) -> bool {
    exists|k: int| 0 <= k < args.len() && args[k].1 && #[trigger] grp_invalidates(g[args[k].0], g[v])
}

/// The `gen` vector of the checker for `v`.
pub open spec fn gen_seq(cfg: Cfg, g: Map<Var, Group>, v: Var) -> Seq<bool> {
    Seq::new(cfg.len(), |n: int| invalidated_at(cfg[n].instr, g, v))
}

/// The `kill` vector of the checker for `v`.
pub open spec fn kill_seq(cfg: Cfg, v: Var) -> Seq<bool> {
    Seq::new(cfg.len(), |n: int| binds(cfg[n].instr, v))
}

/// The nodes that invalidate `v` and do not rebind it.
pub open spec fn gen_eff_seq(cfg: Cfg, g: Map<Var, Group>, v: Var) -> Seq<bool> {
    Seq::new(cfg.len(), |n: int| invalidated_at(cfg[n].instr, g, v) && !binds(cfg[n].instr, v))
}

/// `invalid(v, n)` of the checker: the least fixpoint that `propagate` computes.
pub open spec fn lfp(cfg: Cfg, g: Map<Var, Group>, v: Var, n: int) -> bool {
    spec_in_lfp(cfg_succ(cfg), gen_seq(cfg, g, v), kill_seq(cfg, v), n)
}

/// The groups of the arguments, from the static group map.
pub open spec fn sarg_groups(g: Map<Var, Group>, args: Seq<(Var, bool)>) -> Seq<(Group, bool)> {
    Seq::new(args.len(), |k: int| (g[args[k].0], args[k].1))
}

// ---------------------------------------------------------------------------
// Hypotheses: what sema gives
// ---------------------------------------------------------------------------

/// The static group of each binding is the group that the model gives it.
/// Only the instructions without closures are in this fragment.
pub open spec fn instr_groups_ok(i: Instr, g: Map<Var, Group>) -> bool {
    match i {
        Instr::Borrow { dst, x } => g.contains_key(dst) && g[dst] == Group { root: x, path: Seq::empty() },
        Instr::Child { dst, src, label } => g.contains_key(dst) && g.contains_key(src) && g[dst] == Group {
            root: g[src].root,
            path: g[src].path.push(label),
        },
        Instr::Copy { dst, src } => g.contains_key(dst) && g.contains_key(src) && g[dst] == g[src],
        Instr::Read { src, .. } => g.contains_key(src),
        Instr::Write { src, .. } => g.contains_key(src),
        Instr::Call { args, ret } => {
            &&& forall|k: int| 0 <= k < args.len() ==> g.contains_key(#[trigger] args[k].0)
            &&& ret_ok(sarg_groups(g, args), ret)
            &&& match ret {
                None => true,
                Some(r) => r.arg < args.len() && g.contains_key(r.dst) && g[r.dst] == Group {
                    root: g[args[r.arg as int].0].root,
                    path: g[args[r.arg as int].0].path + r.path,
                },
            }
        },
        _ => false,
    }
}

/// The static facts of the CFG: one group per reference (`points_into`),
/// consistent with each binding; labels that fit; borrowed locals that exist.
pub open spec fn facts_ok(cfg: Cfg, ss0: SState, g: Map<Var, Group>) -> bool {
    &&& cfg_wf(cfg)
    &&& forall|n: int| 0 <= n < cfg.len() ==> #[trigger] instr_groups_ok(cfg[n].instr, g)
    &&& forall|v: Var| #[trigger] g.contains_key(v) ==> fits(g[v].path)
    &&& forall|n: int| 0 <= n < cfg.len() && #[trigger] cfg[n].instr is Borrow ==> ss0.locals.contains(cfg[n].instr->x)
}

/// W0301 accepts the CFG: no node uses a reference in the fixpoint.
pub open spec fn w0301_ok(cfg: Cfg, g: Map<Var, Group>) -> bool {
    forall|n: int, v: Var| 0 <= n < cfg.len() && #[trigger] uses(cfg[n].instr, v) ==> !lfp(cfg, g, v, n)
}

/// `unb(v, n)` covers each node where `v` can be unbound: the entry, if the
/// start state does not hold `v` with its group, and each successor of such
/// a node that does not bind `v`. No node uses `v` where `unb` holds. Sema
/// gives this through lexical scope.
pub open spec fn bound_before_use(cfg: Cfg, ss0: SState, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool) -> bool {
    &&& forall|v: Var|
        g.contains_key(v) && !(ss0.vars.contains_key(v) && ss0.vars[v] == g[v]) ==> #[trigger] unb(v, 0)
    &&& forall|v: Var, n: int, j: int|
        #![trigger unb(v, n), cfg[n].succs[j]]
        0 <= n < cfg.len() && 0 <= j < cfg[n].succs.len() && unb(v, n) && !binds(cfg[n].instr, v) ==> unb(
            v,
            cfg[n].succs[j] as int,
        )
    &&& forall|n: int, v: Var| 0 <= n < cfg.len() && #[trigger] uses(cfg[n].instr, v) ==> !unb(v, n)
}

// ---------------------------------------------------------------------------
// The annotation that the checker result gives
// ---------------------------------------------------------------------------

/// The checker treats `v` as valid at `n`.
pub open spec fn valid_at(cfg: Cfg, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool, v: Var, n: int) -> bool {
    g.contains_key(v) && !lfp(cfg, g, v, n) && !unb(v, n)
}

/// The valid references at `n`, with their static groups.
pub open spec fn ann_vars(cfg: Cfg, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool, n: int) -> Map<Var, Group> {
    Map::new(g.dom().filter(|v: Var| valid_at(cfg, g, unb, v, n)), |v: Var| g[v])
}

/// The annotation of the checker result.
pub open spec fn lfp_ann(cfg: Cfg, ss0: SState, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool) -> Seq<SState> {
    Seq::new(
        cfg.len(),
        |n: int| SState { locals: ss0.locals, vars: ann_vars(cfg, g, unb, n), clos: Map::empty() },
    )
}

/// The groups of the annotation `a` are the static groups.
pub open spec fn agrees(a: Seq<SState>, g: Map<Var, Group>) -> bool {
    forall|n: int, v: Var|
        0 <= n < a.len() && #[trigger] a[n].vars.contains_key(v) ==> g.contains_key(v) && a[n].vars[v] == g[v]
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// The successor lists are well formed, and their edges are the CFG edges.
pub proof fn lemma_cfg_succ(cfg: Cfg, gen: Seq<bool>, kill: Seq<bool>)
    requires
        cfg_wf(cfg),
        gen.len() == cfg.len(),
        kill.len() == cfg.len(),
    ensures
        spec_well_formed(cfg_succ(cfg), gen, kill),
        cfg_succ(cfg).len() == cfg.len(),
        forall|n: int, j: int|
            0 <= n < cfg.len() && 0 <= j < cfg[n].succs.len() ==> cfg_succ(cfg)[n].len() == cfg[n].succs.len()
                && #[trigger] cfg_succ(cfg)[n][j] as int == cfg[n].succs[j] as int,
{
    let s = cfg_succ(cfg);
    assert forall|p: int, j: int| 0 <= p < s.len() && 0 <= j < s[p].len() implies (#[trigger] s[p][j]) < s.len() by {
        assert(cfg[p].succs[j] < cfg.len());
    }
    assert forall|n: int, j: int| 0 <= n < cfg.len() && 0 <= j < cfg[n].succs.len() implies cfg_succ(cfg)[n].len()
        == cfg[n].succs.len() && #[trigger] cfg_succ(cfg)[n][j] as int == cfg[n].succs[j] as int by {
        assert(cfg[n].succs[j] < cfg.len());
    }
}

/// The fixpoint is closed: the successors of a `gen` node, and of a node of
/// the fixpoint that does not rebind `v`, are in the fixpoint.
pub proof fn lemma_lfp_step(cfg: Cfg, g: Map<Var, Group>, v: Var, n: int, j: int)
    requires
        cfg_wf(cfg),
        0 <= n < cfg.len(),
        0 <= j < cfg[n].succs.len(),
        invalidated_at(cfg[n].instr, g, v) || (lfp(cfg, g, v, n) && !binds(cfg[n].instr, v)),
    ensures
        lfp(cfg, g, v, cfg[n].succs[j] as int),
{
    let gen = gen_seq(cfg, g, v);
    let kill = kill_seq(cfg, v);
    lemma_cfg_succ(cfg, gen, kill);
    lemma_step_sound(cfg_succ(cfg), gen, kill, n, j);
    assert(cfg_succ(cfg)[n][j] as int == cfg[n].succs[j] as int);
}

/// A reference that is valid after an edge, at a node that does not rebind
/// it, was valid before the edge, and the node did not invalidate it.
pub proof fn lemma_valid_pred(cfg: Cfg, ss0: SState, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool, v: Var, n: int, j: int)
    requires
        cfg_wf(cfg),
        bound_before_use(cfg, ss0, g, unb),
        0 <= n < cfg.len(),
        0 <= j < cfg[n].succs.len(),
        valid_at(cfg, g, unb, v, cfg[n].succs[j] as int),
        !binds(cfg[n].instr, v),
    ensures
        valid_at(cfg, g, unb, v, n),
        !invalidated_at(cfg[n].instr, g, v),
{
    if invalidated_at(cfg[n].instr, g, v) || lfp(cfg, g, v, n) {
        lemma_lfp_step(cfg, g, v, n, j);
    }
    if unb(v, n) {
        assert(unb(v, cfg[n].succs[j] as int));
    }
}

/// The valid references of the annotation.
pub proof fn lemma_ann_vars(cfg: Cfg, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool, n: int)
    ensures
        forall|v: Var| #[trigger] ann_vars(cfg, g, unb, n).contains_key(v) == valid_at(cfg, g, unb, v, n),
        forall|v: Var| #[trigger] ann_vars(cfg, g, unb, n).contains_key(v) ==> ann_vars(cfg, g, unb, n)[v] == g[v],
{
}

/// The argument groups of a call are the static groups when every argument is valid.
pub proof fn lemma_arg_groups(ss: SState, g: Map<Var, Group>, args: Seq<(Var, bool)>)
    requires
        forall|k: int|
            0 <= k < args.len() ==> ss.vars.contains_key(#[trigger] args[k].0) && ss.vars[args[k].0] == g[args[k].0],
    ensures
        arg_groups(ss, args) == sarg_groups(g, args),
{
    assert(arg_groups(ss, args) =~= sarg_groups(g, args));
}

/// `invalidated_at` is the B1 kill rule on the static argument groups.
pub proof fn lemma_invalidated_is_killed(g: Map<Var, Group>, args: Seq<(Var, bool)>, v: Var, ret: Option<crate::model::Ret>)
    requires
        forall|w: Var| #[trigger] g.contains_key(w) ==> fits(g[w].path),
        forall|k: int| 0 <= k < args.len() ==> g.contains_key(#[trigger] args[k].0),
        g.contains_key(v),
    ensures
        invalidated_at(Instr::Call { args, ret }, g, v) == killed(sarg_groups(g, args), g[v]),
{
    let gs = sarg_groups(g, args);
    if invalidated_at(Instr::Call { args, ret }, g, v) {
        let k = choose|k: int| 0 <= k < args.len() && args[k].1 && #[trigger] grp_invalidates(g[args[k].0], g[v]);
        lemma_grp_invalidates(g[args[k].0], g[v]);
        assert(gs[k] == (g[args[k].0], args[k].1));
        assert(strict_child(g[v], gs[k].0));
    }
    if killed(gs, g[v]) {
        let k = choose|k: int| 0 <= k < gs.len() && gs[k].1 && #[trigger] strict_child(g[v], gs[k].0);
        assert(gs[k] == (g[args[k].0], args[k].1));
        lemma_grp_invalidates(g[args[k].0], g[v]);
        assert(args[k].1);
        assert(grp_invalidates(g[args[k].0], g[v]));
    }
}

// ---------------------------------------------------------------------------
// Soundness: the checker result is an accepted model annotation
// ---------------------------------------------------------------------------

/// The annotation passes the edge condition of `cfg_check` on the edge `n -> succs[j]`.
pub proof fn lemma_edge(cfg: Cfg, ss0: SState, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool, n: int, j: int)
    requires
        facts_ok(cfg, ss0, g),
        w0301_ok(cfg, g),
        bound_before_use(cfg, ss0, g, unb),
        0 <= n < cfg.len(),
        0 <= j < cfg[n].succs.len(),
    ensures
        sub_state(
            lfp_ann(cfg, ss0, g, unb)[cfg[n].succs[j] as int],
            post(lfp_ann(cfg, ss0, g, unb)[n], cfg[n].instr),
        ),
{
    let a = lfp_ann(cfg, ss0, g, unb);
    let m = cfg[n].succs[j] as int;
    let i = cfg[n].instr;
    let an = a[n];
    let p = post(an, i);
    assert(m < cfg.len());
    lemma_ann_vars(cfg, g, unb, n);
    lemma_ann_vars(cfg, g, unb, m);
    assert(instr_groups_ok(i, g));
    assert forall|v: Var| #[trigger] a[m].vars.dom().contains(v) implies p.vars.dom().contains(v) && a[m].vars[v]
        == p.vars[v] by {
        assert(a[m].vars.contains_key(v));
        assert(valid_at(cfg, g, unb, v, m));
        if !binds(i, v) {
            lemma_valid_pred(cfg, ss0, g, unb, v, n, j);
            assert(an.vars.contains_key(v));
        }
        match i {
            Instr::Borrow { dst, x } => {},
            Instr::Child { dst, src, label } => {
                if binds(i, v) {
                    assert(uses(i, src));
                    assert(valid_at(cfg, g, unb, src, n));
                }
            },
            Instr::Copy { dst, src } => {
                assert(uses(i, src));
                assert(valid_at(cfg, g, unb, src, n));
            },
            Instr::Read { .. } => {},
            Instr::Write { .. } => {},
            Instr::Call { args, ret } => {
                assert forall|k: int| 0 <= k < args.len() implies an.vars.contains_key(#[trigger] args[k].0)
                    && an.vars[args[k].0] == g[args[k].0] by {
                    assert(uses(i, args[k].0));
                    assert(valid_at(cfg, g, unb, args[k].0, n));
                }
                lemma_arg_groups(an, g, args);
                let gs = arg_groups(an, args);
                if !binds(i, v) {
                    lemma_invalidated_is_killed(g, args, v, ret);
                    assert(!killed(gs, an.vars[v]));
                }
            },
            _ => {},
        }
    }
    assert(a[m].vars.submap_of(p.vars));
    assert(a[m].clos.submap_of(p.clos));
}

/// The annotation passes `instr_ok` at node `n`.
pub proof fn lemma_node_ok(cfg: Cfg, ss0: SState, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool, n: int)
    requires
        facts_ok(cfg, ss0, g),
        w0301_ok(cfg, g),
        bound_before_use(cfg, ss0, g, unb),
        0 <= n < cfg.len(),
    ensures
        instr_ok(lfp_ann(cfg, ss0, g, unb)[n], cfg[n].instr),
{
    let a = lfp_ann(cfg, ss0, g, unb);
    let i = cfg[n].instr;
    lemma_ann_vars(cfg, g, unb, n);
    assert(instr_groups_ok(i, g));
    match i {
        Instr::Child { src, .. } => {
            assert(uses(i, src));
        },
        Instr::Read { src, .. } => {
            assert(uses(i, src));
        },
        Instr::Write { src, .. } => {
            assert(uses(i, src));
        },
        Instr::Call { args, ret } => {
            assert forall|k: int| 0 <= k < args.len() implies a[n].vars.contains_key(#[trigger] args[k].0)
                && a[n].vars[args[k].0] == g[args[k].0] by {
                assert(uses(i, args[k].0));
            }
            lemma_arg_groups(a[n], g, args);
        },
        _ => {},
    }
}

/// **Soundness of the fixpoint.** If the static facts hold, W0301 accepts
/// and each reference is bound before each use, then the annotation of the
/// checker result passes the B1 checker.
pub proof fn thm_lfp_annotation_checks(cfg: Cfg, ss0: SState, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool)
    requires
        facts_ok(cfg, ss0, g),
        w0301_ok(cfg, g),
        bound_before_use(cfg, ss0, g, unb),
    ensures
        cfg_check(cfg, ss0, lfp_ann(cfg, ss0, g, unb)),
{
    let a = lfp_ann(cfg, ss0, g, unb);
    lemma_ann_vars(cfg, g, unb, 0);
    assert forall|v: Var| #[trigger] a[0].vars.dom().contains(v) implies ss0.vars.dom().contains(v) && a[0].vars[v]
        == ss0.vars[v] by {
        assert(a[0].vars.contains_key(v));
        assert(!unb(v, 0));
    }
    assert(sub_state(a[0], ss0));
    assert forall|n: int| 0 <= n < cfg.len() implies #[trigger] instr_ok(a[n], cfg[n].instr) by {
        lemma_node_ok(cfg, ss0, g, unb, n);
    }
    assert forall|n: int, j: int| 0 <= n < cfg.len() && 0 <= j < cfg[n].succs.len() implies #[trigger] cfg[n].succs[j]
        < cfg.len() && sub_state(a[cfg[n].succs[j] as int], post(a[n], cfg[n].instr)) by {
        lemma_edge(cfg, ss0, g, unb, n, j);
    }
}

/// **W0301 is sound on B1 CFGs.** If the checker accepts, then no run that
/// follows the CFG edges has UB (by `cfg_soundness`).
pub proof fn thm_w0301_no_ub(
    cfg: Cfg,
    ss0: SState,
    g: Map<Var, Group>,
    unb: spec_fn(Var, int) -> bool,
    path: Seq<nat>,
    trace: Seq<DState>,
)
    requires
        facts_ok(cfg, ss0, g),
        w0301_ok(cfg, g),
        bound_before_use(cfg, ss0, g, unb),
        inv(trace[0], ss0),
        is_cfg_trace(cfg, path, trace),
    ensures
        forall|k: int| 0 <= k < trace.len() ==> !#[trigger] ub(trace[k], cfg[path[k] as int].instr),
{
    thm_lfp_annotation_checks(cfg, ss0, g, unb);
    cfg_soundness(cfg, ss0, lfp_ann(cfg, ss0, g, unb), path, trace);
}

// ---------------------------------------------------------------------------
// Minimality: each model annotation marks at least the fixpoint invalid
// ---------------------------------------------------------------------------

/// The nodes where the annotation `a` does not hold `v`.
pub open spec fn invalid_set(a: Seq<SState>, v: Var) -> Set<int> {
    vstd::set_lib::set_int_range(0, a.len() as int).filter(|n: int| !a[n].vars.contains_key(v))
}

/// A node that does not rebind `v` does not add `v`.
pub proof fn lemma_post_no_bind(ss: SState, i: Instr, v: Var)
    requires
        !ss.vars.contains_key(v),
        !binds(i, v),
    ensures
        !post(ss, i).vars.contains_key(v),
{
}

/// The invalid set of an accepted annotation is closed under the rules for
/// `gen` minus `kill`.
pub proof fn lemma_invalid_set_closed(cfg: Cfg, ss0: SState, g: Map<Var, Group>, a: Seq<SState>, v: Var)
    requires
        cfg_wf(cfg),
        cfg_check(cfg, ss0, a),
        agrees(a, g),
        forall|w: Var| #[trigger] g.contains_key(w) ==> fits(g[w].path),
    ensures
        spec_closed(cfg_succ(cfg), gen_eff_seq(cfg, g, v), kill_seq(cfg, v), invalid_set(a, v)),
{
    let s = invalid_set(a, v);
    let succ = cfg_succ(cfg);
    let gen = gen_eff_seq(cfg, g, v);
    let kill = kill_seq(cfg, v);
    lemma_cfg_succ(cfg, gen, kill);
    vstd::set_lib::lemma_int_range(0, a.len() as int);
    assert forall|p: int, q: int| 0 <= p < gen.len() && gen[p] && #[trigger] spec_edge(succ, p, q) implies s.contains(
        q,
    ) by {
        let j = choose|j: int| 0 <= j < succ[p].len() && succ[p][j] as int == q;
        assert(cfg[p].succs[j] as int == q);
        let i = cfg[p].instr;
        assert(cfg_check(cfg, ss0, a));
        assert(instr_ok(a[p], i));
        assert(sub_state(a[q], post(a[p], i)));
        match i {
            Instr::Call { args, ret } => {
                assert forall|k: int| 0 <= k < args.len() implies a[p].vars.contains_key(#[trigger] args[k].0)
                    && a[p].vars[args[k].0] == g[args[k].0] && g.contains_key(args[k].0) by {}
                if a[p].vars.contains_key(v) {
                    lemma_arg_groups(a[p], g, args);
                    lemma_invalidated_is_killed(g, args, v, ret);
                    assert(killed(arg_groups(a[p], args), a[p].vars[v]));
                    assert(!post(a[p], i).vars.contains_key(v));
                } else {
                    lemma_post_no_bind(a[p], i, v);
                }
            },
            _ => {},
        }
        assert(!a[q].vars.contains_key(v));
    }
    assert forall|p: int, q: int|
        0 <= p < kill.len() && s.contains(p) && !kill[p] && #[trigger] spec_edge(succ, p, q) implies s.contains(q) by {
        let j = choose|j: int| 0 <= j < succ[p].len() && succ[p][j] as int == q;
        assert(cfg[p].succs[j] as int == q);
        let i = cfg[p].instr;
        assert(sub_state(a[q], post(a[p], i)));
        lemma_post_no_bind(a[p], i, v);
        assert(!a[q].vars.contains_key(v));
    }
}

/// **Minimality.** Each accepted model annotation whose groups are the
/// static groups marks `v` invalid at each node of the fixpoint of `gen`
/// minus `kill`. This holds for each B1 CFG, also with closures.
pub proof fn thm_model_invalid_contains_lfp(cfg: Cfg, ss0: SState, g: Map<Var, Group>, a: Seq<SState>, v: Var, n: int)
    requires
        cfg_wf(cfg),
        cfg_check(cfg, ss0, a),
        agrees(a, g),
        forall|w: Var| #[trigger] g.contains_key(w) ==> fits(g[w].path),
        0 <= n < cfg.len(),
        spec_in_lfp(cfg_succ(cfg), gen_eff_seq(cfg, g, v), kill_seq(cfg, v), n),
    ensures
        !a[n].vars.contains_key(v),
{
    lemma_invalid_set_closed(cfg, ss0, g, a, v);
    vstd::set_lib::lemma_int_range(0, a.len() as int);
    assert(invalid_set(a, v).contains(n));
}

/// The fixpoint grows with `gen`.
pub proof fn lemma_lfp_monotone(succ: Seq<Seq<usize>>, gen1: Seq<bool>, gen2: Seq<bool>, kill: Seq<bool>, n: int)
    requires
        gen1.len() == gen2.len(),
        forall|p: int| 0 <= p < gen1.len() && #[trigger] gen1[p] ==> gen2[p],
        spec_in_lfp(succ, gen1, kill, n),
    ensures
        spec_in_lfp(succ, gen2, kill, n),
{
    assert forall|s: Set<int>| #[trigger] spec_closed(succ, gen2, kill, s) implies s.contains(n) by {
        assert(spec_closed(succ, gen1, kill, s));
    }
}

/// The checker fixpoint (with all of `gen`) contains the fixpoint of `gen`
/// minus `kill`. `thm_model_invalid_contains_lfp` puts the second fixpoint
/// inside the model must-invalid set.
pub proof fn lemma_lfp_contains_eff(cfg: Cfg, g: Map<Var, Group>, v: Var, n: int)
    requires
        spec_in_lfp(cfg_succ(cfg), gen_eff_seq(cfg, g, v), kill_seq(cfg, v), n),
    ensures
        lfp(cfg, g, v, n),
{
    lemma_lfp_monotone(cfg_succ(cfg), gen_eff_seq(cfg, g, v), gen_seq(cfg, g, v), kill_seq(cfg, v), n);
}

/// The annotation of the checker result has the static groups.
pub proof fn lemma_lfp_ann_agrees(cfg: Cfg, ss0: SState, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool)
    ensures
        agrees(lfp_ann(cfg, ss0, g, unb), g),
{
    let la = lfp_ann(cfg, ss0, g, unb);
    assert forall|k: int, w: Var| 0 <= k < la.len() && #[trigger] la[k].vars.contains_key(w) implies g.contains_key(w)
        && la[k].vars[w] == g[w] by {
        lemma_ann_vars(cfg, g, unb, k);
    }
}

/// **The soundness direction as sets.** If the static facts hold, W0301
/// accepts and each reference is bound before each use: each node where
/// every accepted annotation with the static groups marks `v` invalid is in
/// the checker fixpoint or in `unb`.
pub proof fn thm_must_invalid_in_lfp(cfg: Cfg, ss0: SState, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool, v: Var, n: int)
    requires
        facts_ok(cfg, ss0, g),
        w0301_ok(cfg, g),
        bound_before_use(cfg, ss0, g, unb),
        0 <= n < cfg.len(),
        g.contains_key(v),
        forall|a: Seq<SState>| cfg_check(cfg, ss0, a) && agrees(a, g) ==> !(#[trigger] a[n].vars.contains_key(v)),
    ensures
        lfp(cfg, g, v, n) || unb(v, n),
{
    thm_lfp_annotation_checks(cfg, ss0, g, unb);
    lemma_lfp_ann_agrees(cfg, ss0, g, unb);
    lemma_ann_vars(cfg, g, unb, n);
    let la = lfp_ann(cfg, ss0, g, unb);
    assert(!la[n].vars.contains_key(v));
}

/// No node both invalidates and rebinds `v`.
pub open spec fn no_gen_kill(cfg: Cfg, g: Map<Var, Group>, v: Var) -> bool {
    forall|n: int| 0 <= n < cfg.len() ==> !(#[trigger] invalidated_at(cfg[n].instr, g, v) && binds(cfg[n].instr, v))
}

/// **Exactness.** If no node both invalidates and rebinds `v`: the
/// annotation of the checker result passes `cfg_check`, it holds `v` exactly
/// outside the fixpoint and `unb`, and each accepted annotation with the
/// static groups marks `v` invalid on the whole fixpoint. Thus the fixpoint
/// is the least invalid set that the B1 model allows, outside `unb`.
pub proof fn thm_dataflow_exact(cfg: Cfg, ss0: SState, g: Map<Var, Group>, unb: spec_fn(Var, int) -> bool, v: Var, n: int)
    requires
        facts_ok(cfg, ss0, g),
        w0301_ok(cfg, g),
        bound_before_use(cfg, ss0, g, unb),
        no_gen_kill(cfg, g, v),
        0 <= n < cfg.len(),
    ensures
        cfg_check(cfg, ss0, lfp_ann(cfg, ss0, g, unb)),
        agrees(lfp_ann(cfg, ss0, g, unb), g),
        lfp_ann(cfg, ss0, g, unb)[n].vars.contains_key(v) == (g.contains_key(v) && !lfp(cfg, g, v, n) && !unb(v, n)),
        forall|a: Seq<SState>|
            cfg_check(cfg, ss0, a) && agrees(a, g) && lfp(cfg, g, v, n) ==> !(#[trigger] a[n].vars.contains_key(v)),
{
    thm_lfp_annotation_checks(cfg, ss0, g, unb);
    lemma_lfp_ann_agrees(cfg, ss0, g, unb);
    lemma_ann_vars(cfg, g, unb, n);
    assert(gen_eff_seq(cfg, g, v) =~= gen_seq(cfg, g, v));
    assert forall|a: Seq<SState>|
        cfg_check(cfg, ss0, a) && agrees(a, g) && lfp(cfg, g, v, n) implies !(#[trigger] a[n].vars.contains_key(v)) by {
        thm_model_invalid_contains_lfp(cfg, ss0, g, a, v, n);
    }
}

// ---------------------------------------------------------------------------
// The exec function
// ---------------------------------------------------------------------------

/// The W0301 analysis of the checker for one reference `v`: `propagate` on
/// the CFG edges, with the `gen` and `kill` vectors of `v`. The result is the
/// fixpoint that the theorems above use. The proof uses only the
/// postcondition of `propagate`.
pub fn invalid_at(
    succ: &[Vec<usize>],
    gen: &[bool],
    kill: &[bool],
    Ghost(cfg): Ghost<Cfg>,
    Ghost(g): Ghost<Map<Var, Group>>,
    Ghost(v): Ghost<Var>,
) -> (out: Vec<bool>)
    requires
        cfg_wf(cfg),
        spec_view(succ) == cfg_succ(cfg),
        gen@ == gen_seq(cfg, g, v),
        kill@ == kill_seq(cfg, v),
    ensures
        out.len() == cfg.len(),
        forall|n: int| 0 <= n < cfg.len() ==> #[trigger] out[n] == lfp(cfg, g, v, n),
{
    proof {
        lemma_cfg_succ(cfg, gen@, kill@);
        assert(succ.len() == spec_view(succ).len());
    }
    propagate(succ, gen, kill)
}

} // verus!
