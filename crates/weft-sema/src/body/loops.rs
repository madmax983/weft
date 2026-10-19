//! Loops: the lowering of a loop body until the values that it carries are stable.
//!
//! A loop iteration starts with the values that the iterations before it gave.
//! So the body is lowered again from the loop head with the joined values,
//! until a pass gives no new value (ADR 0003). Each pass starts from the state
//! at the head (`LoopHead`). A rewind costs as much as the pass, not as much
//! as the function so far.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use weft_facts::{CapId, FactMark, NodeId, PlaceId, StepKind, TaskId, VarId};
use weft_syntax::diag::Diagnostic;

use super::{
    BranchState, FnInfo, Frame, HandlerFrame, Jump, LoopFrame, Lower, PartHolder, Span, SumMark,
    Summary, Ty, Undo,
};
use crate::program::FnId;

/// The passes of a loop before the lowering widens the values that still change.
pub const LOOP_WIDEN_AFTER: usize = 8;

/// The passes of a loop with `outer` locals outside it before the root widening.
///
/// After them, the lowering widens a new place with no known place above it to
/// the wildcard place of its root. A chain of locals needs one pass for each
/// local, so a chain is complete before this widening.
pub const fn loop_roots_after(outer: usize) -> usize {
    outer.saturating_add(16)
}

/// Returns the most passes of the lowering of a loop with `outer` locals outside it.
///
/// After the widening of new places to wildcard places of roots, each pass that
/// is not the last adds a value that the head did not have, and the widened
/// values are finite. A loop that needs more passes shows a checker bug (W0707).
pub const fn loop_pass_bound(outer: usize) -> usize {
    loop_roots_after(outer).saturating_mul(2).saturating_add(32)
}

/// The value of a local outside a loop that an iteration passes to the next.
#[derive(Clone, Debug)]
struct Carried {
    refs: Vec<PlaceId>,
    summary: Option<usize>,
    fn_param: Option<(usize, usize)>,
    tasks: BTreeSet<TaskId>,
    bound: bool,
    uniq: bool,
    caps: BTreeSet<CapId>,
    sticky: BTreeSet<CapId>,
}

/// The state at the head of a loop pass. A rewind ([`Lower::rewind`]) goes back
/// to it.
///
/// [`Lower::loop_head`] and [`Lower::rewind`] name each field of [`Lower`], so a
/// new field needs a decision there. The kinds of fields:
/// - A table that stays from pass to pass, so that the values of the pass
///   before stay valid: roots, places and variables, closure summaries, the
///   inference table, and maps by root or by variable. A rewind keeps them.
/// - A list that a pass only extends: the length here. A rewind cuts it back.
/// - A map by node, task or capability: a pass adds entries above the numbers
///   at the head only. A rewind removes them.
/// - The locals: the old values of the locals that the pass changes
///   ([`super::Locals::begin`]). A rewind puts them back.
/// - Other small state: a copy.
struct LoopHead {
    facts: FactMark,
    nodes: usize,
    tasks: usize,
    caps: u32,
    diags: usize,
    /// The number of names of each open frame.
    frames: Vec<usize>,
    /// The depth of the summaries, and the sizes of each one.
    sums: Vec<SumMark>,
    handlers: Vec<HandlerFrame>,
    loops: Vec<LoopFrame>,
    jumps: Vec<Jump>,
    cur: Option<NodeId>,
    pend_uses: Vec<VarId>,
    pend_reads: Vec<PlaceId>,
    scopes: Vec<(usize, Vec<TaskId>)>,
    ret_ty: Ty,
    in_test: bool,
    library: bool,
    self_fn: Option<FnId>,
    cap_calls: usize,
    resumes: usize,
    match_moves: bool,
    match_deps: Vec<PlaceId>,
    stmt_temps: Vec<(usize, Vec<VarId>)>,
    rets: usize,
    op_args: usize,
    escaped: usize,
    reaches: usize,
    applied: usize,
    handled: usize,
    unknown_multi: bool,
    kept: usize,
    resumed: BTreeMap<CapId, BTreeSet<CapId>>,
    op_fn_args: usize,
    param_runs: BTreeMap<(usize, usize), (usize, bool)>,
    unset_places: usize,
    iter_uniq: bool,
    part_holders: Vec<PartHolder>,
    int_lits: usize,
    lit_span: Span,
    late_vars: usize,
    tentative: usize,
    frame_ids: usize,
    loop_jumps: Vec<(bool, BranchState, NodeId)>,
    last_loop: Option<(NodeId, NodeId)>,
    in_flight: Vec<(VarId, usize, usize)>,
    reach_runs: (usize, bool),
    op_results: BTreeMap<(CapId, Option<usize>), PlaceId>,
    resumed_refs: BTreeMap<(CapId, Option<usize>), Vec<PlaceId>>,
    env_root: Option<PlaceId>,
    caller_runs: usize,
    returned: usize,
    stored_behind: usize,
    resume_refs_pending: Vec<(CapId, Vec<PlaceId>)>,
    bind_caps: usize,
}

impl LoopHead {
    /// The number of values that the head copied: the entries of its lists and
    /// maps.
    fn size(&self) -> usize {
        self.frames.len()
            + self.sums.len()
            + self.handlers.len()
            + self.loops.len()
            + self.jumps.len()
            + self.pend_uses.len()
            + self.pend_reads.len()
            + self.scopes.len()
            + self.match_deps.len()
            + self.stmt_temps.len()
            + self.resumed.len()
            + self.param_runs.len()
            + self.part_holders.len()
            + self.loop_jumps.len()
            + self.in_flight.len()
            + self.op_results.len()
            + self.resumed_refs.len()
            + self.resume_refs_pending.len()
    }
}

impl Lower<'_> {
    /// Lowers one iteration of a loop with `pass` until the values of the locals
    /// from outside the loop are stable. An iteration starts with the values that
    /// the iterations before it gave: references, function values and tasks. So
    /// when the body gives a local a new value, the body is lowered again from
    /// the loop head, with the old and the new values joined. A chain of locals
    /// needs one more pass for each local.
    ///
    /// After [`LOOP_WIDEN_AFTER`] passes the join widens what still changes
    /// (`next_carry`), so that the values become stable. A loop that is not
    /// stable after [`loop_pass_bound`] passes gets W0707: the lowering never
    /// keeps the partial values of the last pass with no error.
    pub(super) fn lower_loop(&mut self, span: Span, pass: &mut dyn FnMut(&mut Self)) {
        let outer = self.locals.len();
        let made = (self.facts.roots.len(), self.facts.vars.len());
        let entry = self.branch_state();
        let bound = self.loop_bound.unwrap_or_else(|| loop_pass_bound(outer));
        let mut passes = 0;
        loop {
            let head = self.loop_head();
            let head_state = self.branch_state();
            self.locals.begin();
            let outer_jumps = std::mem::take(&mut self.loop_jumps);
            pass(self);
            let jumps = std::mem::replace(&mut self.loop_jumps, outer_jumps);
            let undo = self.locals.end();
            passes += 1;
            self.work.loop_passes += 1;
            self.work.loop_copies += head.size()
                + head_state.uniq.len()
                + head_state.holders.len()
                + undo.old.len()
                + undo.old_uniq.len();
            // The next pass starts with the states of the back edges: the end of
            // the body and each `continue`.
            let mut back = vec![head_state.clone()];
            back.extend(
                jumps
                    .iter()
                    .filter(|(b, ..)| !b)
                    .map(|(_, st, _)| st.clone()),
            );
            let end_state = self.cur.map(|_| self.branch_state());
            back.extend(end_state.clone());
            let mut next = Self::joined(&back);
            let (carry, stable) =
                self.next_carry(&undo, &head.part_holders, outer, made, &mut next, passes);
            if stable || passes >= bound {
                if !stable {
                    self.diags.push(
                        Diagnostic::error(
                            "W0707",
                            format!(
                                "the analysis of this loop stopped after {passes} passes before its values were stable"
                            ),
                            span,
                        )
                        .note("the facts of the loop can be incomplete; report the program as a checker bug"),
                    );
                }
                // The loop ends at its head, before a pass or after one, or at a `break`.
                let mut exits = back;
                exits.push(entry.clone());
                exits.extend(
                    jumps
                        .iter()
                        .filter(|(b, ..)| *b)
                        .map(|(_, st, _)| st.clone()),
                );
                let st = Self::joined(&exits);
                self.retire_loop_stale(&head_state, &entry, end_state.as_ref(), &jumps, &st);
                self.set_branch(&st);
                return;
            }
            self.rewind(head, undo);
            // The references that the parts of outer locals got in this pass are
            // there at the start of the next pass.
            for h in next.holders.iter().filter(|h| h.local < outer) {
                if !self.part_holders.iter().any(|x| x.var == h.var) {
                    for &p in &h.refs {
                        self.facts.points_into.push((h.var, p));
                    }
                    self.part_holders.push(h.clone());
                }
            }
            for (l, c) in carry {
                let var = self.locals[l].var;
                for &p in &c.refs {
                    if !self.locals[l].refs.contains(&p) {
                        self.facts.points_into.push((var, p));
                    }
                }
                let loc = self.locals.get_mut(l);
                loc.refs = c.refs;
                loc.summary = c.summary;
                loc.fn_param = c.fn_param;
                loc.tasks = c.tasks;
                loc.bound = c.bound;
                loc.caps = c.caps;
                loc.sticky = c.sticky;
                self.locals.set_uniq(l, c.uniq);
            }
        }
    }

    /// The values at the head of the next pass of a loop, for the locals from
    /// outside the loop that the pass changed: the locals of `undo`, and the
    /// locals with a new part holder in `next`. `head_holders` are the part
    /// holders at the head of the pass, and `next` the joined state of the back
    /// edges. The result has each such local with its value, and true if no key
    /// of a value changed: the loop is stable. Only the locals that the pass
    /// changed can change, so the other locals need no key.
    ///
    /// Each value is the join of the value at the head and the value at the end:
    /// the references of both, the function values of both (the end value already
    /// joins the head value), and the tasks of both. After [`LOOP_WIDEN_AFTER`]
    /// passes the join widens what still changes:
    /// - A new place below a place that the value had at the head becomes the
    ///   wildcard place of the deepest such place. After [`loop_roots_after`]
    ///   passes, another new place becomes the wildcard place of its root.
    /// - A function value that still changes becomes a function value that the
    ///   body does not know, which can also do what the value did.
    ///
    /// The new part holders of `next` get the same widening of their places.
    fn next_carry(
        &mut self,
        undo: &Undo,
        head_holders: &[PartHolder],
        outer: usize,
        made: (usize, usize),
        next: &mut BranchState,
        passes: usize,
    ) -> (Vec<(usize, Carried)>, bool) {
        let widen = passes >= LOOP_WIDEN_AFTER;
        let to_root = passes >= loop_roots_after(outer);
        let new_holder =
            |h: &PartHolder| h.local < outer && !head_holders.iter().any(|x| x.var == h.var);
        let mut changed: BTreeSet<usize> = undo
            .old
            .keys()
            .chain(undo.old_uniq.keys())
            .copied()
            .filter(|&l| l < outer)
            .collect();
        changed.extend(
            next.holders
                .iter()
                .filter(|h| new_holder(h))
                .map(|h| h.local),
        );
        if widen {
            for i in 0..next.holders.len() {
                if !new_holder(&next.holders[i]) {
                    continue;
                }
                let hl = next.holders[i].local;
                let known: BTreeSet<String> = head_holders
                    .iter()
                    .filter(|x| x.local == hl)
                    .flat_map(|x| &x.refs)
                    .map(|&p| self.place_key(p, made.0))
                    .collect();
                let refs = next.holders[i].refs.clone();
                let mut widened = Vec::with_capacity(refs.len());
                for p in refs {
                    let q = self.widen_place(p, &known, made.0, to_root);
                    if !widened.contains(&q) {
                        widened.push(q);
                    }
                }
                next.holders[i].refs = widened;
            }
        }
        let mut stable = true;
        let mut out = Vec::with_capacity(changed.len());
        for l in changed {
            let h = undo.old.get(&l).unwrap_or(&self.locals[l]).clone();
            let e = self.locals[l].clone();
            let mut refs = h.refs.clone();
            let known: BTreeSet<String> =
                h.refs.iter().map(|&p| self.place_key(p, made.0)).collect();
            for &p in e.refs.iter().filter(|p| !h.refs.contains(p)) {
                let q = if widen {
                    self.widen_place(p, &known, made.0, to_root)
                } else {
                    p
                };
                if !refs.contains(&q) {
                    refs.push(q);
                }
            }
            let mut c = Carried {
                refs,
                summary: e.summary,
                fn_param: e.fn_param,
                tasks: h.tasks.union(&e.tasks).copied().collect(),
                bound: e.bound,
                uniq: if l < next.len {
                    next.uniq.contains(&l)
                } else {
                    self.locals.is_uniq(l)
                },
                caps: e.caps.clone(),
                sticky: e.sticky.clone(),
            };
            let before = Carried {
                refs: h.refs.clone(),
                summary: h.summary,
                fn_param: h.fn_param,
                tasks: h.tasks.clone(),
                bound: h.bound,
                uniq: undo
                    .old_uniq
                    .get(&l)
                    .copied()
                    .unwrap_or_else(|| self.locals.is_uniq(l)),
                caps: h.caps.clone(),
                sticky: h.sticky.clone(),
            };
            if widen {
                let head_info = FnInfo {
                    summary: h.summary,
                    item: None,
                    param: h.fn_param,
                };
                let end_info = FnInfo {
                    summary: e.summary,
                    item: None,
                    param: e.fn_param,
                };
                if self.fn_key(&head_info, made) != self.fn_key(&end_info, made) {
                    let row = super::fn_row(&self.inf.shallow(&e.ty));
                    let mut m = Summary::default();
                    self.add_fn(&mut m, &end_info, row.as_deref());
                    m.unknown = true;
                    m.may_abort = true;
                    m.multi |= self.may_be_multi(row.as_deref());
                    m.row.extend(row.into_iter().flatten());
                    self.closures.push(m);
                    c.summary = Some(self.closures.len() - 1);
                }
            }
            if stable {
                let was = self.carry_key(l, &before, head_holders, made);
                stable = self.carry_key(l, &c, &next.holders, made) == was;
            }
            out.push((l, c));
        }
        (out, stable)
    }

    /// Widens place `p` for the head of the next pass of a loop. `known` has the
    /// keys of the places at the head. A place with a known key stays. A place
    /// below a known place becomes the wildcard place of the deepest one. Another
    /// place stays, or with `to_root` becomes the wildcard place of its root.
    fn widen_place(
        &mut self,
        p: PlaceId,
        known: &BTreeSet<String>,
        roots: usize,
        to_root: bool,
    ) -> PlaceId {
        if known.contains(&self.place_key(p, roots)) {
            return p;
        }
        let mut top = p;
        let mut at = self.facts.place(p).parent;
        while let Some(q) = at {
            if known.contains(&self.place_key(q, roots)) {
                return self.facts.wildcard(q);
            }
            top = q;
            at = self.facts.place(q).parent;
        }
        if to_root {
            self.facts.wildcard(top)
        } else {
            p
        }
    }

    /// The key of value `c` of local `l` outside a loop, with the part holders
    /// `holders`. The key is the same in each pass of the loop.
    fn carry_key(
        &self,
        l: usize,
        c: &Carried,
        holders: &[PartHolder],
        made: (usize, usize),
    ) -> BTreeSet<String> {
        let mut key: BTreeSet<String> = c
            .refs
            .iter()
            .map(|&p| format!("ref {}", self.place_key(p, made.0)))
            .collect();
        if c.uniq {
            key.insert("uniq".to_string());
        }
        for h in holders.iter().filter(|h| h.local == l) {
            key.extend(
                h.refs
                    .iter()
                    .map(|&p| format!("part ref {}", self.place_key(p, made.0))),
            );
        }
        key.extend(c.tasks.iter().map(|t| format!("task {t}")));
        key.extend(c.caps.iter().map(|c| format!("cap {}", c.0)));
        let info = FnInfo {
            summary: c.summary,
            item: None,
            param: c.fn_param,
        };
        key.extend(self.fn_key(&info, made));
        key
    }

    /// Retires the stale part holders on the edges into the head and the exit of
    /// the loop that `lower_loop` lowered last (`retire_stale`). The states are:
    /// - `head`: at the head in the last pass;
    /// - `entry`: before the loop;
    /// - `end`: at the end of the body;
    /// - `jumps`: at the `break`s and the `continue`s;
    /// - `exit`: after the loop.
    fn retire_loop_stale(
        &mut self,
        head: &BranchState,
        entry: &BranchState,
        end: Option<&BranchState>,
        jumps: &[(bool, BranchState, NodeId)],
        exit: &BranchState,
    ) {
        let Some((header, out)) = self.last_loop else {
            return;
        };
        // With no holder at the head or after the loop, no holder is stale.
        if head.holders.is_empty() && exit.holders.is_empty() {
            return;
        }
        let into_head: Vec<NodeId> = self
            .facts
            .cfg_edge
            .iter()
            .filter(|&&(_, b)| b == header)
            .map(|&(a, _)| a)
            .collect();
        for a in into_head {
            let state = if a.index() < header.index() {
                Some(entry)
            } else if let Some((_, st, _)) = jumps.iter().find(|(b, _, n)| !b && *n == a) {
                Some(st)
            } else if Some(a) == self.cur {
                end
            } else {
                None
            };
            if let Some(st) = state {
                self.retire_stale(a, header, st, head);
            }
        }
        let into_exit: Vec<NodeId> = self
            .facts
            .cfg_edge
            .iter()
            .filter(|&&(_, b)| b == out)
            .map(|&(a, _)| a)
            .collect();
        for a in into_exit {
            // The other edges leave the head: the loop condition.
            let st = jumps
                .iter()
                .find(|(b, _, n)| *b && *n == a)
                .map_or(head, |(_, st, _)| st);
            self.retire_stale(a, out, st, exit);
        }
    }

    /// A key of place `p` that is the same in each pass of a loop. A root that the
    /// loop makes (index `roots` or more) has its kind and name, and a split has its side.
    fn place_key(&self, p: PlaceId, roots: usize) -> String {
        let info = self.facts.place(p);
        let r = info.root.index();
        let mut key = if r < roots {
            format!("r{r}")
        } else {
            let root = &self.facts.roots[r];
            format!("{:?} {}", root.kind, root.name)
        };
        for s in &info.steps {
            let _ = match s.kind {
                StepKind::Seg { hi, .. } => write!(key, "/seg {hi} {}", s.unstable),
                // A pass makes new instances: they are the same place shape.
                _ if weft_facts::is_one_step(s) => write!(key, "/one"),
                k => write!(key, "/{k:?} {}", s.unstable),
            };
        }
        key
    }

    /// The keys of what a call of function value `info` does, the same in each pass of a loop.
    fn fn_key(&self, info: &FnInfo, made: (usize, usize)) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        out.extend(info.param.map(|p| format!("param {p:?}")));
        let Some(s) = info.summary else {
            return out;
        };
        let sum = &self.closures[s];
        let pk = |p: PlaceId| self.place_key(p, made.0);
        let vk = |v: VarId| {
            if v.index() < made.1 {
                format!("{v}")
            } else {
                self.facts.var(v).name.clone()
            }
        };
        for (tag, ps) in [
            ("mut", &sum.muts),
            ("read", &sum.reads),
            ("lend", &sum.lends),
        ] {
            out.extend(ps.iter().map(|&p| format!("{tag} {}", pk(p))));
        }
        out.extend(sum.ret_refs.iter().map(|&p| format!("ret {}", pk(p))));
        out.extend(
            sum.binds
                .iter()
                .map(|&(l, p)| format!("bind {l} {}", pk(p))),
        );
        out.extend(
            sum.escapes
                .iter()
                .chain(&sum.row)
                .map(|e| format!("effect {e}")),
        );
        out.extend(sum.performs.iter().map(|c| format!("cap {c}")));
        out.extend(sum.passthrough.iter().map(|p| format!("passthrough {p}")));
        out.extend(sum.items.iter().map(|f| format!("item {f}")));
        out.extend(sum.params.iter().map(|p| format!("param {p}")));
        out.extend(sum.stores.iter().map(|p| format!("stores {p}")));
        out.extend(sum.tasks.iter().map(|p| format!("tasks {p}")));
        out.extend(sum.spawns.iter().map(|t| format!("spawns {t}")));
        out.extend(sum.ret_spawns.iter().map(|t| format!("ret spawns {t}")));
        out.extend(sum.ret_caps.iter().map(|c| format!("ret cap {c}")));
        out.extend(sum.ret_tasks.iter().map(|t| format!("ret task {t}")));
        out.extend(sum.own_caps.iter().map(|c| format!("own cap {c}")));
        out.extend(sum.captures.iter().map(|&v| format!("capture {}", vk(v))));
        out.extend(
            sum.moved_captures
                .iter()
                .map(|&v| format!("moved {}", vk(v))),
        );
        out.extend(
            sum.param_roots
                .iter()
                .map(|(&r, k)| format!("root {k} {}", pk(r))),
        );
        out.extend(
            sum.op_args
                .iter()
                .map(|(c, op, pos, p)| format!("op {c} {op:?} {pos:?} {}", pk(*p))),
        );
        out.extend(
            sum.lent
                .iter()
                .map(|(f, pos, p)| format!("lent {f} {pos:?} {}", pk(*p))),
        );
        for (flag, on) in [
            ("abort", sum.may_abort),
            ("multi", sum.multi),
            ("unknown", sum.unknown),
            ("literal", sum.literal),
        ] {
            if on {
                out.insert(flag.to_string());
            }
        }
        out
    }

    /// Returns the state at the head of a loop pass ([`LoopHead`]).
    fn loop_head(&self) -> LoopHead {
        // Each field is named, so that a new field gets a decision here and in
        // `rewind`.
        let Self {
            // Fixed for the body.
            prog: _,
            sigs: _,
            b: _,
            module: _,
            has_place_fields: _,
            generic: _,
            loop_bound: _,
            // Tables that stay from pass to pass.
            inf: _,
            closures: _,
            groups: _,
            split: _,
            dep_places: _,
            var_local: _,
            root_local: _,
            maybe_linear: _,
            temp_refs: _,
            param_of_root: _,
            param_bases: _,
            held_roots: _,
            held_of: _,
            work: _,
            // `frames` keeps the names of `scope` (`restore_frames`).
            scope: _,
            // The changes of the locals (`Locals::begin`).
            locals: _,
            // Maps by node, task or capability: the numbers below.
            task_scope: _,
            root_caps: _,
            cap_effects: _,
            repeated: _,
            abort_ctx: _,
            facts,
            diags,
            frames,
            sums,
            handlers,
            loops,
            jumps,
            cur,
            pend_uses,
            pend_reads,
            scopes,
            ret_ty,
            in_test,
            library,
            self_fn,
            cap_calls,
            resumes,
            match_moves,
            match_deps,
            stmt_temps,
            rets,
            op_args,
            escaped,
            reaches,
            applied,
            handled,
            unknown_multi,
            kept,
            resumed,
            op_fn_args,
            param_runs,
            unset_places,
            iter_uniq,
            part_holders,
            int_lits,
            lit_span,
            late_vars,
            tentative,
            frame_ids,
            loop_jumps,
            last_loop,
            in_flight,
            reach_runs,
            op_results,
            resumed_refs,
            env_root,
            caller_runs,
            returned,
            stored_behind,
            resume_refs_pending,
            bind_caps,
        } = self;
        LoopHead {
            facts: facts.mark(),
            nodes: facts.nodes.len(),
            tasks: facts.tasks.len(),
            caps: facts.caps,
            diags: diags.len(),
            frames: frames.iter().map(|f| f.names.len()).collect(),
            sums: sums.iter().map(Summary::mark).collect(),
            handlers: handlers.clone(),
            loops: loops.clone(),
            jumps: jumps.clone(),
            cur: *cur,
            pend_uses: pend_uses.clone(),
            pend_reads: pend_reads.clone(),
            scopes: scopes.clone(),
            ret_ty: ret_ty.clone(),
            in_test: *in_test,
            library: *library,
            self_fn: *self_fn,
            cap_calls: cap_calls.len(),
            resumes: resumes.len(),
            match_moves: *match_moves,
            match_deps: match_deps.clone(),
            stmt_temps: stmt_temps.clone(),
            rets: rets.len(),
            op_args: op_args.len(),
            escaped: escaped.len(),
            reaches: reaches.len(),
            applied: applied.len(),
            handled: handled.len(),
            unknown_multi: *unknown_multi,
            kept: kept.len(),
            resumed: resumed.clone(),
            op_fn_args: op_fn_args.len(),
            param_runs: param_runs.clone(),
            unset_places: unset_places.len(),
            iter_uniq: *iter_uniq,
            part_holders: part_holders.clone(),
            int_lits: int_lits.len(),
            lit_span: *lit_span,
            late_vars: late_vars.len(),
            tentative: tentative.len(),
            frame_ids: *frame_ids,
            loop_jumps: loop_jumps.clone(),
            last_loop: *last_loop,
            in_flight: in_flight.clone(),
            reach_runs: *reach_runs,
            op_results: op_results.clone(),
            resumed_refs: resumed_refs.clone(),
            env_root: *env_root,
            caller_runs: caller_runs.len(),
            returned: returned.len(),
            stored_behind: stored_behind.len(),
            resume_refs_pending: resume_refs_pending.clone(),
            bind_caps: bind_caps.len(),
        }
    }

    /// Goes back to the state `head` at a loop head. `undo` has the changes of
    /// the locals in the pass. The tables stay, so that the values of the pass
    /// before stay valid.
    fn rewind(&mut self, head: LoopHead, undo: Undo) {
        let Self {
            prog: _,
            sigs: _,
            b: _,
            module: _,
            has_place_fields: _,
            generic: _,
            loop_bound: _,
            inf: _,
            closures: _,
            groups: _,
            split: _,
            dep_places: _,
            var_local: _,
            root_local: _,
            maybe_linear: _,
            temp_refs: _,
            param_of_root: _,
            param_bases: _,
            held_roots: _,
            held_of: _,
            work: _,
            scope,
            locals,
            task_scope,
            root_caps,
            cap_effects,
            repeated,
            abort_ctx,
            facts,
            diags,
            frames,
            sums,
            handlers,
            loops,
            jumps,
            cur,
            pend_uses,
            pend_reads,
            scopes,
            ret_ty,
            in_test,
            library,
            self_fn,
            cap_calls,
            resumes,
            match_moves,
            match_deps,
            stmt_temps,
            rets,
            op_args,
            escaped,
            reaches,
            applied,
            handled,
            unknown_multi,
            kept,
            resumed,
            op_fn_args,
            param_runs,
            unset_places,
            iter_uniq,
            part_holders,
            int_lits,
            lit_span,
            late_vars,
            tentative,
            frame_ids,
            loop_jumps,
            last_loop,
            in_flight,
            reach_runs,
            op_results,
            resumed_refs,
            env_root,
            caller_runs,
            returned,
            stored_behind,
            resume_refs_pending,
            bind_caps,
        } = self;
        facts.rewind(&head.facts);
        let node = NodeId(u32::try_from(head.nodes).unwrap_or(u32::MAX));
        let task = TaskId(u32::try_from(head.tasks).unwrap_or(u32::MAX));
        let _ = repeated.split_off(&node);
        let _ = abort_ctx.split_off(&node);
        let _ = task_scope.split_off(&task);
        let _ = root_caps.split_off(&CapId(head.caps));
        let _ = cap_effects.split_off(&CapId(head.caps));
        locals.restore(undo);
        restore_frames(frames, scope, &head.frames);
        diags.truncate(head.diags);
        sums.truncate(head.sums.len());
        for (s, m) in sums.iter_mut().zip(head.sums) {
            s.cut(m);
        }
        *handlers = head.handlers;
        *loops = head.loops;
        *jumps = head.jumps;
        *cur = head.cur;
        *pend_uses = head.pend_uses;
        *pend_reads = head.pend_reads;
        *scopes = head.scopes;
        *ret_ty = head.ret_ty;
        *in_test = head.in_test;
        *library = head.library;
        *self_fn = head.self_fn;
        cap_calls.truncate(head.cap_calls);
        resumes.truncate(head.resumes);
        *match_moves = head.match_moves;
        *match_deps = head.match_deps;
        *stmt_temps = head.stmt_temps;
        rets.truncate(head.rets);
        op_args.truncate(head.op_args);
        escaped.truncate(head.escaped);
        reaches.truncate(head.reaches);
        applied.truncate(head.applied);
        handled.truncate(head.handled);
        *unknown_multi = head.unknown_multi;
        kept.truncate(head.kept);
        *resumed = head.resumed;
        op_fn_args.truncate(head.op_fn_args);
        *param_runs = head.param_runs;
        unset_places.truncate(head.unset_places);
        *iter_uniq = head.iter_uniq;
        *part_holders = head.part_holders;
        int_lits.truncate(head.int_lits);
        *lit_span = head.lit_span;
        late_vars.truncate(head.late_vars);
        tentative.truncate(head.tentative);
        *frame_ids = head.frame_ids;
        *loop_jumps = head.loop_jumps;
        *last_loop = head.last_loop;
        *in_flight = head.in_flight;
        *reach_runs = head.reach_runs;
        *op_results = head.op_results;
        *resumed_refs = head.resumed_refs;
        *env_root = head.env_root;
        caller_runs.truncate(head.caller_runs);
        returned.truncate(head.returned);
        stored_behind.truncate(head.stored_behind);
        *resume_refs_pending = head.resume_refs_pending;
        bind_caps.truncate(head.bind_caps);
    }
}

/// Closes the frames that a pass opened, and removes the names that it added
/// to the open frames. `scope` loses the same names. `names` has the number of
/// names of each frame at the head.
fn restore_frames(
    frames: &mut Vec<Frame>,
    scope: &mut BTreeMap<String, Vec<usize>>,
    names: &[usize],
) {
    let mut drop_name = |name: &str| {
        if let Some(ls) = scope.get_mut(name) {
            ls.pop();
            if ls.is_empty() {
                scope.remove(name);
            }
        }
    };
    while frames.len() > names.len() {
        if let Some(f) = frames.pop() {
            for (name, _) in f.names.iter().rev() {
                drop_name(name);
            }
        }
    }
    for (f, &n) in frames.iter_mut().zip(names) {
        for (name, _) in f.names.drain(n.min(f.names.len())..).rev() {
            drop_name(&name);
        }
    }
}
