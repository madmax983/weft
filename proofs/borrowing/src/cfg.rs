//! # B1. Branches and loops
//!
//! A program is a control-flow graph (CFG). Each node holds one instruction and a list
//! of successor nodes. Node 0 is the entry. The model does not evaluate branch
//! conditions: an execution can take any successor edge. Thus one CFG covers each
//! `if`, `match` and loop.
//!
//! The checker gives each node an entry state (`ann`). The state at a node must be
//! `sub_state` of the state after each predecessor. Thus a reference is valid at a node only
//! if it is valid, with the same group, at the end of each incoming edge. This is the
//! intersection join (`join`). It is the Weft rule
//! `invalid(R,Q) :- invalid(R,P), cfg_edge(P,Q), !rebound_at(R,P)`.
//!
//! Main theorem: `cfg_soundness`.

use vstd::prelude::*;
use crate::model::*;
use crate::soundness::*;

verus! {

// ---------------------------------------------------------------------------
// Programs as CFGs
// ---------------------------------------------------------------------------

/// One CFG node: an instruction and the nodes that can run next.
/// A node with no successors is an exit.
pub struct Node {
    pub instr: Instr,
    pub succs: Seq<nat>,
}

/// A CFG. Node 0 is the entry.
pub type Cfg = Seq<Node>;

/// An execution that follows CFG edges. Node `path[k]` runs in state `trace[k]`.
/// The trace can stop at any point (for example at a safe abort).
pub open spec fn is_cfg_trace(cfg: Cfg, path: Seq<nat>, trace: Seq<DState>) -> bool {
    &&& 1 <= trace.len()
    &&& path.len() == trace.len()
    &&& path[0] == 0
    &&& forall|k: int| 0 <= k < path.len() ==> #[trigger] path[k] < cfg.len()
    &&& forall|k: int|
        0 <= k < trace.len() - 1 ==> step(#[trigger] trace[k], cfg[path[k] as int].instr, trace[k + 1])
            && cfg[path[k] as int].succs.contains(path[k + 1])
}

// ---------------------------------------------------------------------------
// The checker at joins
// ---------------------------------------------------------------------------

/// State `a` keeps some of the valid references and closure values of `b`,
/// with the same groups, and the same locals.
pub open spec fn sub_state(a: SState, b: SState) -> bool {
    &&& a.locals == b.locals
    &&& a.vars.submap_of(b.vars)
    &&& a.clos.submap_of(b.clos)
}

/// The join of two checker states: the references and closure values that
/// are valid in both, with the same groups.
pub open spec fn join(a: SState, b: SState) -> SState {
    SState {
        locals: a.locals,
        vars: Map::new(
            a.vars.dom().filter(|v: Var| b.vars.contains_key(v) && a.vars[v] == b.vars[v]),
            |v: Var| a.vars[v],
        ),
        clos: Map::new(
            a.clos.dom().filter(|c: CVar| b.clos.contains_key(c) && a.clos[c] == b.clos[c]),
            |c: CVar| a.clos[c],
        ),
    }
}

/// The checker accepts the CFG with the entry states `ann`:
/// each instruction is accepted in its entry state, and each edge `n -> m`
/// gives `sub_state(ann[m], post(ann[n], instr))`. The greatest such `ann` is the
/// fixpoint of the intersection join; the checker can use any such `ann`.
pub open spec fn cfg_check(cfg: Cfg, ss0: SState, ann: Seq<SState>) -> bool {
    &&& 0 < cfg.len()
    &&& ann.len() == cfg.len()
    &&& sub_state(ann[0], ss0)
    &&& forall|n: int| 0 <= n < cfg.len() ==> #[trigger] instr_ok(ann[n], cfg[n].instr)
    &&& forall|n: int, j: int|
        0 <= n < cfg.len() && 0 <= j < cfg[n].succs.len() ==> #[trigger] cfg[n].succs[j] < cfg.len()
            && sub_state(ann[cfg[n].succs[j] as int], post(ann[n], cfg[n].instr))
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// **Key lemma.** The invariant holds for each subset of the valid references
/// (and closure values).
pub proof fn lemma_inv_sub(s: DState, ss: SState, ss2: SState)
    requires
        inv(s, ss),
        sub_state(ss2, ss),
    ensures
        inv(s, ss2),
{
    assert forall|v: Var| #[trigger] ss2.vars.contains_key(v) implies ref_ok(s, ss2.vars[v], v) by {
        assert(ss2.vars.dom().contains(v));
        assert(ss.vars.contains_key(v));
    }
    assert forall|c: CVar| #[trigger] ss2.clos.contains_key(c) implies s.clos.contains_key(c) && args_ok(s, ss2.clos[c], s.clos[c]) by {
        assert(ss2.clos.dom().contains(c));
        assert(ss.clos.contains_key(c));
    }
}

/// The join is `sub_state` of both inputs.
pub proof fn lemma_join_sub(a: SState, b: SState)
    requires
        a.locals == b.locals,
    ensures
        sub_state(join(a, b), a),
        sub_state(join(a, b), b),
{
}

/// The join is the greatest state that is `sub_state` of both inputs: it is the intersection.
pub proof fn lemma_join_greatest(a: SState, b: SState, c: SState)
    requires
        sub_state(c, a),
        sub_state(c, b),
    ensures
        sub_state(c, join(a, b)),
{
    assert forall|v: Var| #[trigger] c.vars.dom().contains(v) implies join(a, b).vars.dom().contains(v)
        && c.vars[v] == join(a, b).vars[v] by {
        assert(a.vars.dom().contains(v));
        assert(b.vars.dom().contains(v));
    }
    assert forall|x: CVar| #[trigger] c.clos.dom().contains(x) implies join(a, b).clos.dom().contains(x)
        && c.clos[x] == join(a, b).clos[x] by {
        assert(a.clos.dom().contains(x));
        assert(b.clos.dom().contains(x));
    }
}

/// The invariant holds at each point of an accepted CFG run.
pub proof fn lemma_cfg_inv_along(cfg: Cfg, ss0: SState, ann: Seq<SState>, path: Seq<nat>, trace: Seq<DState>, k: nat)
    requires
        inv(trace[0], ss0),
        cfg_check(cfg, ss0, ann),
        is_cfg_trace(cfg, path, trace),
        k < trace.len(),
    ensures
        inv(trace[k as int], ann[path[k as int] as int]),
    decreases k,
{
    if k == 0 {
        lemma_inv_sub(trace[0], ss0, ann[0]);
    } else {
        let km = (k - 1) as int;
        lemma_cfg_inv_along(cfg, ss0, ann, path, trace, km as nat);
        let n = path[km] as int;
        assert(path[km] < cfg.len());
        assert(instr_ok(ann[n], cfg[n].instr));
        assert(step(trace[km], cfg[n].instr, trace[km + 1]));
        lemma_preserve(trace[km], ann[n], cfg[n].instr, trace[km + 1]);
        assert(cfg[n].succs.contains(path[km + 1]));
        let j = choose|j: int| 0 <= j < cfg[n].succs.len() && cfg[n].succs[j] == path[km + 1];
        assert(sub_state(ann[cfg[n].succs[j] as int], post(ann[n], cfg[n].instr)));
        lemma_inv_sub(trace[k as int], post(ann[n], cfg[n].instr), ann[path[k as int] as int]);
    }
}

// ---------------------------------------------------------------------------
// Main theorem
// ---------------------------------------------------------------------------

/// **Soundness for branches and loops.** If the checker accepts the CFG, then
/// no execution that follows CFG edges has UB.
pub proof fn cfg_soundness(cfg: Cfg, ss0: SState, ann: Seq<SState>, path: Seq<nat>, trace: Seq<DState>)
    requires
        inv(trace[0], ss0),
        cfg_check(cfg, ss0, ann),
        is_cfg_trace(cfg, path, trace),
    ensures
        forall|k: int| 0 <= k < trace.len() ==> !#[trigger] ub(trace[k], cfg[path[k] as int].instr),
{
    assert forall|k: int| 0 <= k < trace.len() implies !#[trigger] ub(trace[k], cfg[path[k] as int].instr) by {
        lemma_cfg_inv_along(cfg, ss0, ann, path, trace, k as nat);
        let n = path[k] as int;
        assert(path[k] < cfg.len());
        assert(instr_ok(ann[n], cfg[n].instr));
        lemma_no_ub(trace[k], ann[n], cfg[n].instr);
    }
}

/// Soundness for CFGs from a fresh start: any well-formed heap, no references yet.
pub proof fn cfg_soundness_from_start(cfg: Cfg, ann: Seq<SState>, path: Seq<nat>, trace: Seq<DState>)
    requires
        wf(trace[0]),
        cfg_check(cfg, initial_sstate(trace[0]), ann),
        is_cfg_trace(cfg, path, trace),
    ensures
        forall|k: int| 0 <= k < trace.len() ==> !#[trigger] ub(trace[k], cfg[path[k] as int].instr),
{
    assert(inv(trace[0], initial_sstate(trace[0])));
    cfg_soundness(cfg, initial_sstate(trace[0]), ann, path, trace);
}

// ---------------------------------------------------------------------------
// Straight-line programs are a special case
// ---------------------------------------------------------------------------

/// The CFG of a straight-line program: node `k` runs `prog[k]` and goes to `k + 1`.
pub open spec fn linear_cfg(prog: Seq<Instr>) -> Cfg {
    Seq::new(
        prog.len(),
        |k: int| Node { instr: prog[k], succs: if k + 1 < prog.len() { seq![(k + 1) as nat] } else { seq![] } },
    )
}

/// The straight-line checker (`check`) is the CFG checker on `linear_cfg`.
pub proof fn lemma_linear_cfg_check(ss0: SState, prog: Seq<Instr>)
    requires
        0 < prog.len(),
        check(ss0, prog),
    ensures
        cfg_check(linear_cfg(prog), ss0, Seq::new(prog.len(), |k: int| ss_at(ss0, prog, k as nat))),
{
    let cfg = linear_cfg(prog);
    let ann = Seq::new(prog.len(), |k: int| ss_at(ss0, prog, k as nat));
    assert(ann[0] == ss0);
    assert forall|n: int| 0 <= n < cfg.len() implies #[trigger] instr_ok(ann[n], cfg[n].instr) by {
        assert(instr_ok(ss_at(ss0, prog, n as nat), prog[n]));
    }
    assert forall|n: int, j: int| 0 <= n < cfg.len() && 0 <= j < cfg[n].succs.len() implies #[trigger] cfg[n].succs[j]
        < cfg.len() && sub_state(ann[cfg[n].succs[j] as int], post(ann[n], cfg[n].instr)) by {
        assert(n + 1 < prog.len());
        assert(cfg[n].succs[j] == n + 1);
        assert(ann[n + 1] == post(ann[n], prog[n]));
    }
}

} // verus!
