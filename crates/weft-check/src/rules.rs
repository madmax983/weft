//! The production checker: one specialized function per rule group of `spec/weft.dl`.
//!
//! Each forward or backward analysis calls the verified
//! [`propagate`](weft_verified::dataflow::propagate). Each place comparison calls the
//! verified place algebra.

use std::collections::{BTreeMap, BTreeSet};

use weft_facts::{FnFacts, HandlerId, NodeId, PlaceId, TaskId, TaskKind, VarId, Violations};
use weft_verified::dataflow::propagate;
use weft_verified::places;

/// Why a reference was invalidated: the evidence for one W0301 error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Invalidation {
    /// The reference holder.
    pub var: VarId,
    /// The place the reference points into.
    pub path: PlaceId,
    /// The node that mutates.
    pub at: NodeId,
    /// The mutated place.
    pub mutated: PlaceId,
    /// The use of the invalid reference.
    pub used_at: NodeId,
}

/// Evidence for one W0405 error: which footprints overlap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conflict {
    /// The running task.
    pub task: TaskId,
    /// The node that runs at the same time as the task.
    pub at: NodeId,
    /// The place in the task footprint.
    pub task_place: PlaceId,
    /// The place that the node accesses.
    pub node_place: PlaceId,
    /// True if the task writes `task_place`.
    pub task_writes: bool,
}

/// The checker result: violations plus the evidence for diagnostics.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Report {
    /// The violation relations.
    pub violations: Violations,
    /// Evidence for each `error(R, P)`.
    pub invalidations: Vec<Invalidation>,
    /// Evidence for each `task_conflict(T, P)`.
    pub conflicts: Vec<Conflict>,
}

/// The graph and fact indexes of one function.
struct Ctx<'a> {
    f: &'a FnFacts,
    succ: Vec<Vec<usize>>,
    pred: Vec<Vec<usize>>,
    /// `mutates_at`, with the footprint rule applied.
    muts: Vec<Vec<PlaceId>>,
    reads: Vec<Vec<PlaceId>>,
}

impl<'a> Ctx<'a> {
    fn new(f: &'a FnFacts) -> Self {
        let n = f.nodes.len();
        let mut succ = vec![Vec::new(); n];
        let mut pred = vec![Vec::new(); n];
        for &(p, q) in &f.cfg_edge {
            succ[p.index()].push(q.index());
            pred[q.index()].push(p.index());
        }
        let mut muts = vec![Vec::new(); n];
        for &(p, m) in &f.mutates_at {
            muts[p.index()].push(m);
        }
        let mut fp: BTreeMap<u32, Vec<PlaceId>> = BTreeMap::new();
        for &(c, m) in &f.footprint {
            fp.entry(c.0).or_default().push(m);
        }
        for &(p, c) in &f.performs_at {
            if let Some(ms) = fp.get(&c.0) {
                muts[p.index()].extend(ms.iter().copied());
            }
        }
        for m in &mut muts {
            m.sort();
            m.dedup();
        }
        let mut reads = vec![Vec::new(); n];
        for &(p, a) in &f.reads_at {
            reads[p.index()].push(a);
        }
        Self {
            f,
            succ,
            pred,
            muts,
            reads,
        }
    }

    fn n(&self) -> usize {
        self.f.nodes.len()
    }

    fn same_root(&self, a: PlaceId, b: PlaceId) -> bool {
        self.f.place(a).root == self.f.place(b).root
    }

    fn invalidates(&self, m: PlaceId, p: PlaceId) -> bool {
        self.same_root(m, p) && places::invalidates(&self.f.place(m).steps, &self.f.place(p).steps)
    }

    fn overlaps(&self, a: PlaceId, b: PlaceId) -> bool {
        self.same_root(a, b) && places::overlaps(&self.f.place(a).steps, &self.f.place(b).steps)
    }

    fn within(&self, p: PlaceId, d: PlaceId) -> bool {
        self.same_root(p, d) && places::within(&self.f.place(p).steps, &self.f.place(d).steps)
    }

    /// Forward propagation from `gen` nodes, stopped after `kill` nodes.
    fn forward(&self, gen: &[bool], kill: &[bool]) -> Vec<bool> {
        propagate(&self.succ, &gen.to_vec(), &kill.to_vec())
    }

    /// Backward propagation on the reversed graph.
    fn backward(&self, gen: &[bool], kill: &[bool]) -> Vec<bool> {
        propagate(&self.pred, &gen.to_vec(), &kill.to_vec())
    }

    fn mask(&self, nodes: impl IntoIterator<Item = NodeId>) -> Vec<bool> {
        let mut m = vec![false; self.n()];
        for x in nodes {
            m[x.index()] = true;
        }
        m
    }
}

/// Groups a `(var, node)` relation by variable.
fn by_var(rel: &[(VarId, NodeId)]) -> BTreeMap<VarId, Vec<NodeId>> {
    let mut m: BTreeMap<VarId, Vec<NodeId>> = BTreeMap::new();
    for &(v, n) in rel {
        m.entry(v).or_default().push(n);
    }
    m
}

/// Runs every rule of the spec on one function.
pub fn check(f: &FnFacts) -> Report {
    let cx = Ctx::new(f);
    let mut r = Report::default();
    let rebound = by_var(&f.rebound_at);
    let uses = by_var(&f.uses);
    let moved = by_var(&f.moved_at);

    invalidation(&cx, &rebound, &uses, &mut r);
    moves(&cx, &rebound, &uses, &moved, &mut r.violations);
    linear(&cx, &rebound, &moved, &mut r.violations);
    multi(&cx, &rebound, &uses, &mut r.violations);
    effects(&cx, &mut r.violations);
    tasks(&cx, &mut r);
    r
}

/// W0301: `error(R, P)`.
fn invalidation(
    cx: &Ctx<'_>,
    rebound: &BTreeMap<VarId, Vec<NodeId>>,
    uses: &BTreeMap<VarId, Vec<NodeId>>,
    r: &mut Report,
) {
    let f = cx.f;
    let mut paths: BTreeMap<VarId, Vec<PlaceId>> = BTreeMap::new();
    for &(v, p) in &f.points_into {
        paths.entry(v).or_default().push(p);
    }
    for (&v, ps) in &paths {
        let Some(used) = uses.get(&v) else { continue };
        // invalidated_at(R, P) with the first witness per node
        let mut gens: Vec<(NodeId, PlaceId, PlaceId)> = Vec::new();
        for (i, ms) in cx.muts.iter().enumerate() {
            let hit = ms
                .iter()
                .find_map(|&m| ps.iter().find(|&&p| cx.invalidates(m, p)).map(|&p| (m, p)));
            if let Some((m, p)) = hit {
                gens.push((NodeId(u32::try_from(i).unwrap_or(u32::MAX)), p, m));
            }
        }
        if gens.is_empty() {
            continue;
        }
        let kill = cx.mask(rebound.get(&v).cloned().unwrap_or_default());
        let gen = cx.mask(gens.iter().map(|g| g.0));
        let invalid = cx.forward(&gen, &kill);
        for &u in used {
            if !invalid[u.index()] {
                continue;
            }
            r.violations.error.insert((v, u));
            // Evidence: the first mutation that reaches this use on its own.
            for &(at, path, mutated) in &gens {
                let one = cx.mask([at]);
                if cx.forward(&one, &kill)[u.index()] {
                    r.invalidations.push(Invalidation {
                        var: v,
                        path,
                        at,
                        mutated,
                        used_at: u,
                    });
                    break;
                }
            }
        }
    }
}

/// W0302, W0501, W0502, W0604.
fn moves(
    cx: &Ctx<'_>,
    rebound: &BTreeMap<VarId, Vec<NodeId>>,
    uses: &BTreeMap<VarId, Vec<NodeId>>,
    moved: &BTreeMap<VarId, Vec<NodeId>>,
    out: &mut Violations,
) {
    for (&v, ms) in moved {
        if cx.f.var(v).immovable {
            for &m in ms {
                out.moved_immovable.insert((v, m));
            }
        }
        let Some(used) = uses.get(&v) else { continue };
        let gen = cx.mask(ms.iter().copied());
        let kill = cx.mask(rebound.get(&v).cloned().unwrap_or_default());
        let after = cx.forward(&gen, &kill);
        for &u in used {
            if after[u.index()] {
                out.use_after_move.insert((v, u));
            }
        }
    }
}

/// W0601, W0602.
fn linear(
    cx: &Ctx<'_>,
    rebound: &BTreeMap<VarId, Vec<NodeId>>,
    moved: &BTreeMap<VarId, Vec<NodeId>>,
    out: &mut Violations,
) {
    let f = cx.f;
    let ends = by_var(&f.scope_end);
    let aborts = cx.mask(f.may_abort.iter().copied());
    for (&v, binds) in rebound {
        let info = f.var(v);
        if !info.linear {
            continue;
        }
        let gen = cx.mask(binds.iter().copied());
        let kill = cx.mask(moved.get(&v).cloned().unwrap_or_default());
        let live = cx.forward(&gen, &kill);
        for &e in ends.get(&v).map_or(&[][..], Vec::as_slice) {
            if live[e.index()] {
                out.unconsumed.insert((v, e));
            }
        }
        for &b in binds {
            if live[b.index()] {
                out.overwritten.insert((v, b));
            }
        }
        if !info.has_on_abort {
            for (i, &l) in live.iter().enumerate() {
                if l && aborts[i] && !kill[i] {
                    out.abort_unhandled
                        .insert((v, NodeId(u32::try_from(i).unwrap_or(u32::MAX))));
                }
            }
        }
    }
}

/// W0503: `live_across_multi(V, P)`.
fn multi(
    cx: &Ctx<'_>,
    rebound: &BTreeMap<VarId, Vec<NodeId>>,
    uses: &BTreeMap<VarId, Vec<NodeId>>,
    out: &mut Violations,
) {
    let f = cx.f;
    if f.multi_at.is_empty() {
        return;
    }
    for (&v, us) in uses {
        if !f.var(v).once {
            continue;
        }
        let gen = cx.mask(us.iter().copied());
        let kill = cx.mask(rebound.get(&v).cloned().unwrap_or_default());
        let live_out = cx.backward(&gen, &kill);
        for &p in &f.multi_at {
            if live_out[p.index()] {
                out.live_across_multi.insert((v, p));
            }
        }
    }
}

/// W0702, W0703, W0402, W0312, W0801.
fn effects(cx: &Ctx<'_>, out: &mut Violations) {
    let f = cx.f;
    let declared: BTreeSet<&str> = f.declared_effect.iter().map(String::as_str).collect();
    for (i, ms) in cx.muts.iter().enumerate() {
        let node = NodeId(u32::try_from(i).unwrap_or(u32::MAX));
        for &m in ms {
            if f.has_signature
                && f.param_rooted(m)
                && !f.declared_mut.iter().any(|&d| cx.within(m, d))
            {
                out.unauthorized_mut.insert((node, m));
            }
            if f.shared_root.iter().any(|&s| cx.within(m, s)) {
                out.shared_mutation.insert((node, m));
            }
        }
    }
    if f.has_signature {
        for (p, e) in &f.escapes_at {
            if !declared.contains(e.as_str()) {
                out.unauthorized_effect.insert((*p, e.clone()));
            }
        }
    }
    for &(p, m, i) in &f.call_mut {
        for &(q, a, j) in &f.call_arg {
            if p == q && i != j && cx.overlaps(m, a) {
                out.alias_conflict.insert((p, m, a));
            }
        }
    }
    if f.library {
        // `std_effect(E)` is a property of the effect name.
        let std_names: BTreeSet<&str> = f
            .handlers
            .iter()
            .filter(|h| h.is_std)
            .map(|h| h.effect.as_str())
            .collect();
        for (i, h) in f.handlers.iter().enumerate() {
            if std_names.contains(h.effect.as_str()) && !h.forwards {
                out.root_handler_in_lib
                    .insert(HandlerId(u32::try_from(i).unwrap_or(u32::MAX)));
            }
        }
    }
}

/// W0405, W0401, W0403 and `stealable(T)`.
fn tasks(cx: &Ctx<'_>, r: &mut Report) {
    let f = cx.f;
    let mut writes: BTreeMap<TaskId, Vec<PlaceId>> = BTreeMap::new();
    let mut reads: BTreeMap<TaskId, Vec<PlaceId>> = BTreeMap::new();
    for &(t, m) in &f.task_writes {
        writes.entry(t).or_default().push(m);
    }
    for &(t, a) in &f.task_reads {
        reads.entry(t).or_default().push(a);
    }
    let mut spawned: BTreeMap<TaskId, Vec<NodeId>> = BTreeMap::new();
    let mut joined: BTreeMap<TaskId, Vec<NodeId>> = BTreeMap::new();
    for &(t, p) in &f.spawned_at {
        spawned.entry(t).or_default().push(p);
    }
    for &(t, p) in &f.joined_at {
        joined.entry(t).or_default().push(p);
    }
    let empty: Vec<PlaceId> = Vec::new();
    for (&t, sp) in &spawned {
        let gen = cx.mask(sp.iter().copied());
        let kill = cx.mask(joined.get(&t).cloned().unwrap_or_default());
        let active = cx.forward(&gen, &kill);
        let tw = writes.get(&t).unwrap_or(&empty);
        let tr = reads.get(&t).unwrap_or(&empty);
        for (i, &on) in active.iter().enumerate() {
            if !on {
                continue;
            }
            let node = NodeId(u32::try_from(i).unwrap_or(u32::MAX));
            let accesses = cx.reads[i].iter().chain(cx.muts[i].iter());
            let mut found = None;
            for &a in accesses {
                if let Some(&m) = tw.iter().find(|&&m| cx.overlaps(m, a)) {
                    found = Some((m, a, true));
                    break;
                }
            }
            if found.is_none() {
                for &m in &cx.muts[i] {
                    if let Some(&a) = tr.iter().find(|&&a| cx.overlaps(m, a)) {
                        found = Some((a, m, false));
                        break;
                    }
                }
            }
            if let Some((task_place, node_place, task_writes)) = found {
                r.violations.task_conflict.insert((t, node));
                r.conflicts.push(Conflict {
                    task: t,
                    at: node,
                    task_place,
                    node_place,
                    task_writes,
                });
            }
        }
    }

    let mut pinned: BTreeSet<TaskId> = BTreeSet::new();
    let mut_through: BTreeSet<(TaskId, VarId)> = f.mut_through.iter().copied().collect();
    for &(t, v) in &f.captures {
        let info = f.var(v);
        let shared_mut = mut_through.contains(&(t, v)) && !info.uniq;
        if info.nonportable || shared_mut {
            pinned.insert(t);
        }
        if f.tasks[t.index()].kind == TaskKind::Fork {
            if info.nonportable {
                r.violations.nonportable_capture.insert((t, v));
            }
            if shared_mut {
                r.violations.shared_mut_capture.insert((t, v));
            }
        }
    }
    for i in 0..f.tasks.len() {
        let t = TaskId(u32::try_from(i).unwrap_or(u32::MAX));
        if !pinned.contains(&t) {
            r.violations.stealable.insert(t);
        }
    }
}
