//! The production checker: one specialized function per rule group of `spec/weft.dl`.
//!
//! Each forward or backward analysis calls the verified [`propagate`]. Each
//! place comparison calls the verified place algebra.

use std::collections::{BTreeMap, BTreeSet};

use weft_facts::{FnFacts, HandlerId, NodeId, PlaceId, TaskId, TaskKind, VarId, Violations};
use weft_verified::dataflow::propagate;
use weft_verified::places;

/// What a node does that invalidates a reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Cause {
    /// The node mutates this place.
    Mutation(PlaceId),
    /// The node moves this owner of the place.
    Move(VarId),
    /// This owner of the place goes out of scope at the node.
    ScopeEnd(VarId),
    /// The node moves the value at this place out of its owner.
    MovePart(PlaceId),
    /// The node gives this place to a function value that can mutate through it.
    Lend(PlaceId),
}

/// Why a reference was invalidated: the evidence for one W0301 error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Invalidation {
    /// The reference holder.
    pub var: VarId,
    /// The place the reference points into.
    pub path: PlaceId,
    /// The node that invalidates.
    pub at: NodeId,
    /// What the node does.
    pub cause: Cause,
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
    /// The node frees `node_place`: a move or the end of its owner.
    pub free: Option<Cause>,
    /// The node gives `node_place` to a function value that can mutate through it.
    pub lends: bool,
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
    /// `lends_mut`.
    lends: Vec<Vec<PlaceId>>,
    /// `frees_at`, with the cause of each free.
    frees: Vec<Vec<(PlaceId, Cause)>>,
    /// `wild_at(P, B)` by place.
    bases: Vec<Vec<PlaceId>>,
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
        let mut lends = vec![Vec::new(); n];
        for &(p, m) in &f.lends_mut {
            lends[p.index()].push(m);
        }
        // A parent comes before its children.
        let mut bases: Vec<Vec<PlaceId>> = Vec::with_capacity(f.places.len());
        for p in &f.places {
            let mut b = p.parent.map_or_else(Vec::new, |q| bases[q.index()].clone());
            if let (true, Some(q)) = (p.is_wildcard(), p.parent) {
                b.push(q);
            }
            bases.push(b);
        }
        let mut cx = Self {
            f,
            succ,
            pred,
            muts,
            reads,
            lends,
            frees: vec![Vec::new(); n],
            bases,
        };
        cx.frees = cx.frees_at();
        cx
    }

    /// `frees_at(P, M)`: a move of a part frees the part; a move of the whole
    /// value or the end of the owner frees each root that it owns.
    fn frees_at(&self) -> Vec<Vec<(PlaceId, Cause)>> {
        let f = self.f;
        let mut out = vec![Vec::new(); self.n()];
        let mut owned: BTreeMap<VarId, Vec<PlaceId>> = BTreeMap::new();
        for &(rt, v) in &f.owner {
            owned.entry(v).or_default().push(rt);
        }
        let none: Vec<PlaceId> = Vec::new();
        for &(m, p) in &f.moved_part {
            out[p.index()].push((m, Cause::MovePart(m)));
        }
        for &(v, p) in &f.moved_at {
            let roots = owned.get(&v).unwrap_or(&none);
            // part_moved_at(V, P)
            let part = f
                .moved_part
                .iter()
                .any(|&(m, q)| q == p && roots.iter().any(|&rt| self.prefix(rt, m)));
            if !part {
                out[p.index()].extend(roots.iter().map(|&rt| (rt, Cause::Move(v))));
            }
        }
        for &(v, p) in &f.scope_end {
            let roots = owned.get(&v).unwrap_or(&none);
            out[p.index()].extend(roots.iter().map(|&rt| (rt, Cause::ScopeEnd(v))));
        }
        out
    }

    fn n(&self) -> usize {
        self.f.nodes.len()
    }

    fn same_root(&self, a: PlaceId, b: PlaceId) -> bool {
        self.f.place(a).root == self.f.place(b).root
    }

    fn prefix(&self, m: PlaceId, p: PlaceId) -> bool {
        self.same_root(m, p) && places::may_prefix(&self.f.place(m).steps, &self.f.place(p).steps)
    }

    fn invalidates(&self, m: PlaceId, p: PlaceId) -> bool {
        self.same_root(m, p) && places::invalidates(&self.f.place(m).steps, &self.f.place(p).steps)
    }

    /// `overlaps(P, Q)`. A wildcard place overlaps what its base overlaps.
    fn overlaps(&self, a: PlaceId, b: PlaceId) -> bool {
        (self.same_root(a, b) && places::overlaps(&self.f.place(a).steps, &self.f.place(b).steps))
            || self.bases[a.index()].iter().any(|&x| self.overlaps(x, b))
            || self.bases[b.index()].iter().any(|&y| self.overlaps(a, y))
    }

    /// `invalidated_at` by a mutation of `m`, for a reference into `p`.
    fn mutation_kills(&self, m: PlaceId, p: PlaceId) -> bool {
        self.invalidates(m, p)
            || self.bases[p.index()].iter().any(|&b| self.overlaps(m, b))
            || self.bases[m.index()].iter().any(|&b| self.prefix(b, p))
    }

    /// `invalidated_at` by a free of `m`, for a reference into `p`.
    fn free_kills(&self, m: PlaceId, p: PlaceId) -> bool {
        self.prefix(m, p) || self.bases[p.index()].iter().any(|&b| self.overlaps(m, b))
    }

    fn within(&self, p: PlaceId, d: PlaceId) -> bool {
        self.same_root(p, d) && places::within(&self.f.place(p).steps, &self.f.place(d).steps)
    }

    /// Forward propagation from `gen` nodes, stopped after `kill` nodes.
    fn forward(&self, gen: &[bool], kill: &[bool]) -> Vec<bool> {
        propagate(&self.succ, gen, kill)
    }

    /// Backward propagation on the reversed graph.
    fn backward(&self, gen: &[bool], kill: &[bool]) -> Vec<bool> {
        propagate(&self.pred, gen, kill)
    }

    fn mask(&self, nodes: impl IntoIterator<Item = NodeId>) -> Vec<bool> {
        let mut m = vec![false; self.n()];
        for x in nodes {
            m[x.index()] = true;
        }
        m
    }
}

/// Finds, for each node in `targets`, the first gen node that reaches it
/// alone. "Reaches" has the meaning of [`propagate`] with only that gen. The
/// result has the index in `gens` for each node. Only the entries of the
/// targets are exact.
///
/// First a backward search finds the nodes that can reach a target. A path
/// from a gen to a target goes only through these nodes. Then one search runs
/// from each gen, in order, in these nodes. A search marks each node that it
/// reaches and that no earlier search marked, and it stops at marked nodes.
/// When a search marks a node that is not a kill node, it marks the
/// successors too. Thus an earlier search reached all that a later search can
/// reach through a marked node. The cost is linear in the size of the graph.
pub(crate) fn first_reaching(
    succ: &[Vec<usize>],
    pred: &[Vec<usize>],
    gens: &[usize],
    kill: &[bool],
    targets: &[usize],
) -> Vec<Option<usize>> {
    // The nodes that reach a target: a predecessor of a target, or of a node
    // that reaches a target and is not a kill node.
    let mut is_target = vec![false; succ.len()];
    for &t in targets {
        is_target[t] = true;
    }
    let mut near = is_target.clone();
    let mut work: Vec<usize> = (0..succ.len()).filter(|&t| is_target[t]).collect();
    while let Some(q) = work.pop() {
        if kill[q] && !is_target[q] {
            continue;
        }
        for &p in &pred[q] {
            if !near[p] {
                near[p] = true;
                work.push(p);
            }
        }
    }
    let mut first = vec![None; succ.len()];
    for (k, &g) in gens.iter().enumerate() {
        if !near[g] {
            continue;
        }
        // A gen marks its successors, also when it is a kill node.
        let mut next = &succ[g];
        loop {
            for &q in next {
                if near[q] && first[q].is_none() {
                    first[q] = Some(k);
                    if !kill[q] {
                        work.push(q);
                    }
                }
            }
            let Some(p) = work.pop() else { break };
            next = &succ[p];
        }
    }
    first
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
    unset(&cx, &rebound, &uses, &mut r.violations);
    linear(&cx, &rebound, &moved, &mut r.violations);
    multi(&cx, &rebound, &uses, &mut r.violations);
    effects(&cx, &mut r.violations);
    tasks(&cx, &mut r);
    r
}

/// `invalidated_at(R, P)` for a reference that points into `ps`: each node
/// that invalidates it, with the first witness `(node, path, cause)`. A node
/// invalidates the reference if it mutates a place, gives a place to a function
/// value (`lends_mut`) or frees a place (`frees_at`). The result has one
/// witness for each node, in the order of the nodes: the witness with the least
/// cause.
fn invalidated_at(cx: &Ctx<'_>, ps: &[PlaceId]) -> Vec<(NodeId, PlaceId, Cause)> {
    let mut gens: Vec<(NodeId, PlaceId, Cause)> = Vec::new();
    // A mutation, or a place that the node gives to a function value.
    for (i, (ms, ls)) in cx.muts.iter().zip(&cx.lends).enumerate() {
        let changes = ms
            .iter()
            .map(|&m| (m, Cause::Mutation(m)))
            .chain(ls.iter().map(|&m| (m, Cause::Lend(m))));
        let mut hit = None;
        for (m, cause) in changes {
            if let Some(&p) = ps.iter().find(|&&p| cx.mutation_kills(m, p)) {
                hit = Some((p, cause));
                break;
            }
        }
        if let Some((p, cause)) = hit {
            gens.push((NodeId(u32::try_from(i).unwrap_or(u32::MAX)), p, cause));
        }
    }
    // A free of `M` with `prefix(M, Path)`.
    for (i, fs) in cx.frees.iter().enumerate() {
        let node = NodeId(u32::try_from(i).unwrap_or(u32::MAX));
        for &(m, cause) in fs {
            for &p in ps {
                if cx.free_kills(m, p) {
                    gens.push((node, p, cause));
                }
            }
        }
    }
    gens.sort_by_key(|g| (g.0, g.2));
    gens.dedup_by_key(|g| g.0);
    gens
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
    // References that point into the same places share their gens.
    let mut gens_of: BTreeMap<&[PlaceId], Vec<(NodeId, PlaceId, Cause)>> = BTreeMap::new();
    for (&v, ps) in &paths {
        let Some(used) = uses.get(&v) else { continue };
        let gens = gens_of
            .entry(ps.as_slice())
            .or_insert_with(|| invalidated_at(cx, ps));
        if gens.is_empty() {
            continue;
        }
        let kill = cx.mask(rebound.get(&v).cloned().unwrap_or_default());
        let gen = cx.mask(gens.iter().map(|g| g.0));
        let invalid = cx.forward(&gen, &kill);
        let errors: Vec<NodeId> = used
            .iter()
            .copied()
            .filter(|u| invalid[u.index()])
            .collect();
        // Evidence: the first invalidation that reaches each use on its own.
        let gen_nodes: Vec<usize> = gens.iter().map(|g| g.0.index()).collect();
        let targets: Vec<usize> = errors.iter().map(|u| u.index()).collect();
        let first = first_reaching(&cx.succ, &cx.pred, &gen_nodes, &kill, &targets);
        for u in errors {
            r.violations.error.insert((v, u));
            if let Some(&(at, path, cause)) = first[u.index()].and_then(|k| gens.get(k)) {
                r.invalidations.push(Invalidation {
                    var: v,
                    path,
                    at,
                    cause,
                    used_at: u,
                });
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

/// W0304: `use_before_set(V, P)`.
fn unset(
    cx: &Ctx<'_>,
    rebound: &BTreeMap<VarId, Vec<NodeId>>,
    uses: &BTreeMap<VarId, Vec<NodeId>>,
    out: &mut Violations,
) {
    for (v, ds) in by_var(&cx.f.unset_at) {
        let Some(used) = uses.get(&v) else { continue };
        let gen = cx.mask(ds);
        let kill = cx.mask(rebound.get(&v).cloned().unwrap_or_default());
        let after = cx.forward(&gen, &kill);
        for &u in used {
            if after[u.index()] {
                out.use_before_set.insert((v, u));
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
    let overwrites = by_var(&f.overwrites);
    let empty: BTreeSet<(VarId, NodeId)> = f.empty_at.iter().copied().collect();
    let aborts = cx.mask(f.may_abort.iter().copied());
    let vars: BTreeSet<VarId> = rebound.keys().chain(overwrites.keys()).copied().collect();
    for v in vars {
        let binds = rebound.get(&v).map_or(&[][..], Vec::as_slice);
        let info = f.var(v);
        if !info.linear {
            continue;
        }
        // A new value with no linear part has nothing to consume. A new value of
        // a part can give the variable a linear value.
        let parts = overwrites.get(&v).map_or(&[][..], Vec::as_slice);
        let gen = cx.mask(
            binds
                .iter()
                .copied()
                .filter(|&b| !empty.contains(&(v, b)))
                .chain(parts.iter().copied()),
        );
        let kill = cx.mask(moved.get(&v).cloned().unwrap_or_default());
        let live = cx.forward(&gen, &kill);
        for &e in ends.get(&v).map_or(&[][..], Vec::as_slice) {
            if live[e.index()] {
                out.unconsumed.insert((v, e));
            }
        }
        for &b in binds.iter().chain(parts) {
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
    // A node that runs a clause, and a resume, can resume more than once if the
    // clause or the handled computation can.
    let mut multi: BTreeSet<NodeId> = f.multi_at.iter().copied().collect();
    for &(p, c) in &f.performs_at {
        if f.clause_multi.contains(&c) {
            multi.insert(p);
        }
    }
    for &(p, c) in &f.resumes_at {
        if f.clause_multi.contains(&c) || f.body_multi.contains(&c) {
            multi.insert(p);
        }
    }
    if multi.is_empty() {
        return;
    }
    for (&v, us) in uses {
        if !f.var(v).once {
            continue;
        }
        let gen = cx.mask(us.iter().copied());
        let kill = cx.mask(rebound.get(&v).cloned().unwrap_or_default());
        let live_out = cx.backward(&gen, &kill);
        for &p in &multi {
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
    let mut args: BTreeMap<NodeId, Vec<(PlaceId, u32)>> = BTreeMap::new();
    for &(q, a, j) in &f.call_arg {
        args.entry(q).or_default().push((a, j));
    }
    for &(p, m, i) in &f.call_mut {
        for &(a, j) in args.get(&p).map_or(&[][..], Vec::as_slice) {
            if i != j && cx.overlaps(m, a) {
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
            let id = HandlerId(u32::try_from(i).unwrap_or(u32::MAX));
            // A clause that performs the effect again forwards it.
            let forwards = h.forwards
                || f.clause_performs
                    .iter()
                    .any(|(g, e)| *g == id && *e == h.effect);
            if std_names.contains(h.effect.as_str()) && !forwards {
                out.root_handler_in_lib.insert(id);
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
                    found = Some((m, a, true, None, false));
                    break;
                }
            }
            if found.is_none() {
                for &m in &cx.muts[i] {
                    if let Some(&a) = tr.iter().find(|&&a| cx.overlaps(m, a)) {
                        found = Some((a, m, false, None, false));
                        break;
                    }
                }
            }
            // A place that the node gives to a function value, which can mutate it.
            if found.is_none() {
                for &m in &cx.lends[i] {
                    let hit = tr
                        .iter()
                        .map(|&a| (a, false))
                        .chain(tw.iter().map(|&a| (a, true)))
                        .find(|&(a, _)| cx.overlaps(m, a));
                    if let Some((a, writes)) = hit {
                        found = Some((a, m, writes, None, true));
                        break;
                    }
                }
            }
            // A free of what the task reads or writes.
            if found.is_none() {
                for &(m, cause) in &cx.frees[i] {
                    let hit = tr
                        .iter()
                        .map(|&a| (a, false))
                        .chain(tw.iter().map(|&a| (a, true)))
                        .find(|&(a, _)| cx.overlaps(m, a));
                    if let Some((a, writes)) = hit {
                        found = Some((a, m, writes, Some(cause), false));
                        break;
                    }
                }
            }
            if let Some((task_place, node_place, task_writes, free, lends)) = found {
                r.violations.task_conflict.insert((t, node));
                r.conflicts.push(Conflict {
                    task: t,
                    at: node,
                    task_place,
                    node_place,
                    task_writes,
                    free,
                    lends,
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
