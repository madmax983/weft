//! The production checker: one specialized function per rule group of `spec/weft.dl`.
//!
//! Each forward or backward analysis calls the verified [`propagate`]. Each
//! place comparison calls the verified place algebra.

use std::collections::{BTreeMap, BTreeSet};

use weft_facts::{
    uniqueness, FnFacts, HandlerId, Modes, NodeId, PlaceId, RootId, TaskId, TaskKind, VarId,
    Violations, CROSSES_THREADS,
};
use weft_verified::dataflow::propagate;
use weft_verified::modes;
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
    /// An abort path leaves the scope of this owner of the place at the node.
    Unwound(VarId),
    /// The node moves the value at this place out of its owner.
    MovePart(PlaceId),
    /// The node gives this place to a function value that can mutate through it.
    Lend(PlaceId),
    /// The node can free the memory at this place (`releases_at`): a `resume`
    /// after the handled body changed a place above what a clause parameter
    /// points into.
    Release(PlaceId),
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

/// The work of one check. A test can put a limit on it, as a clock cannot be
/// stable on a loaded machine.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    /// The calls of `overlaps`, also the calls inside other place relations.
    pub overlaps: u64,
    /// The searches of the graph: each propagation and each evidence search.
    /// One search costs at most the size of the graph.
    pub searches: u64,
    /// The nodes in the parts of the graph that the searches of the uses saw
    /// (`part_of`). The cost of these searches grows with this count.
    pub part_nodes: u64,
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
    /// The outermost `B` of `wild_at(P, B)` by place. Each other `B` of `P` is
    /// below it, and the place relations are closed under prefixes, so the
    /// wildcard rules need only this one.
    outer: Vec<Option<PlaceId>>,
    /// The outermost one-place wildcard place `W` of `in_one(P, W)` by place.
    /// Two places have a `W` in common if and only if their outermost ones are
    /// equal, as both are on the path from the root to the common one.
    one: Vec<Option<PlaceId>>,
    /// The roots that a node mutates, gives to a function value or frees.
    changed: BTreeSet<RootId>,
    /// The calls of [`Ctx::overlaps`].
    overlaps_calls: std::cell::Cell<u64>,
    /// The searches of the graph (`Work::searches`).
    searches: std::cell::Cell<u64>,
    /// The nodes of the parts (`Work::part_nodes`).
    part_nodes: std::cell::Cell<u64>,
    /// The work space of [`part_of`].
    scratch: std::cell::RefCell<Scratch>,
}

/// The work space of [`part_of`]. Each search puts the arrays back as they
/// were, so a search costs as much as its part, not as much as the graph.
pub(crate) struct Scratch {
    /// The index of each node in the part, or [`NOT_IN_PART`].
    pub(crate) local: Vec<usize>,
    /// The kill nodes of the search.
    pub(crate) killed: Vec<bool>,
}

impl Scratch {
    /// The work space for a graph of `n` nodes.
    pub(crate) fn new(n: usize) -> Self {
        Self {
            local: vec![NOT_IN_PART; n],
            killed: vec![false; n],
        }
    }
}

/// The index of a node that is not in the part.
pub(crate) const NOT_IN_PART: usize = usize::MAX;

/// The part of the graph that can reach a target: the targets, and each node
/// with a path to a target whose inner nodes are not kill nodes.
///
/// A path of [`propagate`] from a gen node to a target has only such nodes.
/// So a propagation in the part gives the result of a propagation in the whole
/// graph at each target. Its cost grows with the size of the part.
pub(crate) struct Part {
    /// The node of each index of the part.
    pub(crate) nodes: Vec<usize>,
    /// The successors in the part, by index.
    pub(crate) succ: Vec<Vec<usize>>,
    /// The predecessors in the part, by index.
    pub(crate) pred: Vec<Vec<usize>>,
    /// The kill nodes, by index.
    pub(crate) kill: Vec<bool>,
    /// The index of each target, in the order of the targets.
    pub(crate) targets: Vec<usize>,
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
        let mut outer: Vec<Option<PlaceId>> = Vec::with_capacity(f.places.len());
        let mut one: Vec<Option<PlaceId>> = Vec::with_capacity(f.places.len());
        for (i, p) in f.places.iter().enumerate() {
            let above = p.parent.and_then(|q| outer[q.index()]);
            outer.push(above.or_else(|| p.parent.filter(|_| p.is_wildcard())));
            let id = PlaceId(u32::try_from(i).unwrap_or(u32::MAX));
            let one_above = p.parent.and_then(|q| one[q.index()]);
            let own = (p.is_one_place() && p.is_wildcard()).then_some(id);
            one.push(one_above.or(own));
        }
        let mut cx = Self {
            f,
            succ,
            pred,
            muts,
            reads,
            lends,
            frees: vec![Vec::new(); n],
            outer,
            one,
            changed: BTreeSet::new(),
            overlaps_calls: std::cell::Cell::new(0),
            searches: std::cell::Cell::new(0),
            part_nodes: std::cell::Cell::new(0),
            scratch: std::cell::RefCell::new(Scratch::new(n)),
        };
        cx.frees = cx.frees_at();
        let changes = cx.muts.iter().chain(&cx.lends).flatten().copied();
        let freed = cx.frees.iter().flatten().map(|&(m, _)| m);
        cx.changed = changes.chain(freed).map(|m| f.place(m).root).collect();
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
        for &(p, m) in &f.releases_at {
            out[p.index()].push((m, Cause::Release(m)));
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
        for &(v, p) in &f.unwound_at {
            let roots = owned.get(&v).unwrap_or(&none);
            out[p.index()].extend(roots.iter().map(|&rt| (rt, Cause::Unwound(v))));
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

    /// The outermost wildcard base of `p`, or `p` if it has none.
    fn outermost(&self, p: PlaceId) -> PlaceId {
        self.outer[p.index()].unwrap_or(p)
    }

    /// `overlaps(P, Q)`. A wildcard place overlaps what its base overlaps.
    ///
    /// The spec gives `overlaps(P, Q)` if some `A` in `P` and its bases and
    /// some `C` in `Q` and its bases overlap with no wildcard rule. Each such
    /// `A` has the outermost base of `P` as a prefix, and the relation is
    /// closed under prefixes. So the outermost bases decide it. Two places
    /// inside one one-place wildcard place use no wildcard rule (`same_one`):
    /// their steps decide.
    fn overlaps(&self, a: PlaceId, b: PlaceId) -> bool {
        self.overlaps_calls.set(self.overlaps_calls.get() + 1);
        // Inside one one-place wildcard place the steps decide, with no wildcard rule.
        if self.same_one(a, b) {
            return self.same_root(a, b)
                && places::overlaps(&self.f.place(a).steps, &self.f.place(b).steps);
        }
        let (a, b) = (self.outermost(a), self.outermost(b));
        self.same_root(a, b) && places::overlaps(&self.f.place(a).steps, &self.f.place(b).steps)
    }

    /// `strict_prefix(M, P)`: `m` can be a prefix of `p`, and `p` is longer.
    fn strict_prefix(&self, m: PlaceId, p: PlaceId) -> bool {
        self.f.place(m).steps.len() < self.f.place(p).steps.len() && self.prefix(m, p)
    }

    /// `same_one(M, P)`: `m` and `p` are inside one one-place wildcard place.
    fn same_one(&self, m: PlaceId, p: PlaceId) -> bool {
        self.one[m.index()].is_some() && self.one[m.index()] == self.one[p.index()]
    }

    /// `invalidated_at` by a mutation of `m`, for a reference into `p`.
    fn mutation_kills(&self, m: PlaceId, p: PlaceId) -> bool {
        self.invalidates(m, p)
            || (!self.same_one(m, p)
                && ((self.outer[p.index()].is_some() && self.overlaps(m, p))
                    || self.outer[m.index()].is_some_and(|b| self.strict_prefix(b, p))))
    }

    /// `invalidated_at` by a free of `m`, for a reference into `p`.
    fn free_kills(&self, m: PlaceId, p: PlaceId) -> bool {
        self.prefix(m, p)
            || (!self.same_one(m, p) && self.outer[p.index()].is_some() && self.overlaps(m, p))
    }

    fn within(&self, p: PlaceId, d: PlaceId) -> bool {
        self.same_root(p, d) && places::within(&self.f.place(p).steps, &self.f.place(d).steps)
    }

    /// `inside_stated(A, D)`: a reference into `a` is inside the stated place
    /// `d`. Below a plain place only stable steps follow. Below a wildcard
    /// place any step can follow.
    fn inside_stated(&self, a: PlaceId, d: PlaceId) -> bool {
        let (pa, pd) = (self.f.place(a), self.f.place(d));
        match (pd.is_wildcard(), pd.parent) {
            (true, Some(base)) => self.within(a, base),
            (true, None) => false,
            (false, _) => {
                self.within(a, d) && pa.steps.iter().skip(pd.steps.len()).all(|s| !s.unstable)
            }
        }
    }

    /// Forward propagation from `gen` nodes, stopped after `kill` nodes.
    fn forward(&self, gen: &[bool], kill: &[bool]) -> Vec<bool> {
        self.searches.set(self.searches.get() + 1);
        propagate(&self.succ, gen, kill)
    }

    /// Backward propagation on the reversed graph.
    fn backward(&self, gen: &[bool], kill: &[bool]) -> Vec<bool> {
        self.searches.set(self.searches.get() + 1);
        propagate(&self.pred, gen, kill)
    }

    /// The part of the graph that can reach `targets`, where `kill` has the
    /// kill nodes ([`Part`]). It is one backward search.
    fn part(&self, targets: &[NodeId], kill: &[NodeId]) -> Part {
        self.searches.set(self.searches.get() + 1);
        let targets: Vec<usize> = targets.iter().map(|t| t.index()).collect();
        let kill: Vec<usize> = kill.iter().map(|k| k.index()).collect();
        let part = part_of(
            &self.succ,
            &self.pred,
            &targets,
            &kill,
            &mut self.scratch.borrow_mut(),
        );
        let size = u64::try_from(part.nodes.len()).unwrap_or(u64::MAX);
        self.part_nodes
            .set(self.part_nodes.get().saturating_add(size));
        part
    }

    /// The targets of `part` that a gen node reaches ([`propagate`] in the
    /// part). `gen` has the gen nodes, by index of the part.
    fn reached(&self, part: &Part, gen: &[bool]) -> Vec<bool> {
        self.searches.set(self.searches.get() + 1);
        let out = propagate(&part.succ, gen, &part.kill);
        part.targets.iter().map(|&t| out[t]).collect()
    }

    fn mask(&self, nodes: impl IntoIterator<Item = NodeId>) -> Vec<bool> {
        let mut m = vec![false; self.n()];
        for x in nodes {
            m[x.index()] = true;
        }
        m
    }
}

/// The part of the graph `succ`, `pred` that can reach `targets`, where `kill`
/// has the kill nodes ([`Part`]). It is one backward search. `s` must have
/// `local` all [`NOT_IN_PART`] and `killed` all false, and it has them again
/// at the end.
pub(crate) fn part_of(
    succ: &[Vec<usize>],
    pred: &[Vec<usize>],
    targets: &[usize],
    kill: &[usize],
    s: &mut Scratch,
) -> Part {
    for &k in kill {
        s.killed[k] = true;
    }
    let mut nodes: Vec<usize> = Vec::new();
    let mut is_target: Vec<bool> = Vec::new();
    for &t in targets {
        if s.local[t] == NOT_IN_PART {
            s.local[t] = nodes.len();
            nodes.push(t);
            is_target.push(true);
        }
    }
    // A target propagates to its predecessors, also when it is a kill node.
    let mut work: Vec<usize> = (0..nodes.len()).collect();
    while let Some(i) = work.pop() {
        let q = nodes[i];
        if s.killed[q] && !is_target[i] {
            continue;
        }
        for &p in &pred[q] {
            if s.local[p] == NOT_IN_PART {
                s.local[p] = nodes.len();
                work.push(nodes.len());
                nodes.push(p);
                is_target.push(false);
            }
        }
    }
    let mut part_succ = vec![Vec::new(); nodes.len()];
    let mut part_pred = vec![Vec::new(); nodes.len()];
    for (i, &q) in nodes.iter().enumerate() {
        for &r in &succ[q] {
            let j = s.local[r];
            if j != NOT_IN_PART {
                part_succ[i].push(j);
                part_pred[j].push(i);
            }
        }
    }
    let part = Part {
        kill: nodes.iter().map(|&q| s.killed[q]).collect(),
        targets: targets.iter().map(|&t| s.local[t]).collect(),
        nodes,
        succ: part_succ,
        pred: part_pred,
    };
    for &q in &part.nodes {
        s.local[q] = NOT_IN_PART;
    }
    for &k in kill {
        s.killed[k] = false;
    }
    part
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
    check_counted(f).0
}

/// Runs every rule of the spec on one function, and counts the work.
pub fn check_counted(f: &FnFacts) -> (Report, Work) {
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
    args(&cx, &mut r.violations);
    root_bodies(&cx, &mut r.violations);
    tasks(&cx, &mut r);
    let work = Work {
        overlaps: cx.overlaps_calls.get(),
        searches: cx.searches.get(),
        part_nodes: cx.part_nodes.get(),
    };
    (r, work)
}

/// The witness of `invalidated_at(R, P)` at node `node` for a reference `R`
/// that points into the places `ps`, grouped by root: the place of `ps` and
/// the cause. A node invalidates the reference if it mutates a place, gives a
/// place to a function value (`lends_mut`) or frees a place (`frees_at`). Each
/// of these needs a place of `ps` with the same root. Of the mutations and of
/// the lends, the first change that invalidates counts, with the first place
/// of `ps` that it invalidates. Of all, the least cause is the witness. A
/// mutation at a node with `writes_via(P, R)` does not count (`via`).
fn witness(
    cx: &Ctx<'_>,
    node: usize,
    ps: &BTreeMap<RootId, Vec<PlaceId>>,
    via: Option<&BTreeSet<NodeId>>,
) -> Option<(PlaceId, Cause)> {
    let of_root = |m: PlaceId| ps.get(&cx.f.place(m).root).map_or(&[][..], Vec::as_slice);
    let mut best: Option<(PlaceId, Cause)> = None;
    let mut offer = |p: PlaceId, c: Cause| {
        if best.is_none_or(|(_, b)| c < b) {
            best = Some((p, c));
        }
    };
    let id = NodeId(u32::try_from(node).unwrap_or(u32::MAX));
    let via_here = via.is_some_and(|ns| ns.contains(&id));
    for (changes, cause, counts) in [
        (
            &cx.muts[node],
            Cause::Mutation as fn(PlaceId) -> Cause,
            !via_here,
        ),
        (&cx.lends[node], Cause::Lend as fn(PlaceId) -> Cause, true),
    ] {
        let hit = changes.iter().find_map(|&m| {
            of_root(m)
                .iter()
                .find(|&&p| cx.mutation_kills(m, p))
                .map(|&p| (p, m))
        });
        if let Some((p, m)) = hit.filter(|_| counts) {
            offer(p, cause(m));
        }
    }
    for &(m, cause) in &cx.frees[node] {
        for &p in of_root(m) {
            if cx.free_kills(m, p) {
                offer(p, cause);
            }
        }
    }
    best
}

/// W0301: `error(R, P)`.
///
/// Each reference has one search in the part of the graph that can reach its
/// uses ([`Ctx::part`]). Only the nodes of the part can be witnesses, so the
/// cost of a reference grows with its part, not with the function.
fn invalidation(
    cx: &Ctx<'_>,
    rebound: &BTreeMap<VarId, Vec<NodeId>>,
    uses: &BTreeMap<VarId, Vec<NodeId>>,
    r: &mut Report,
) {
    let f = cx.f;
    let mut paths: BTreeMap<VarId, BTreeMap<RootId, Vec<PlaceId>>> = BTreeMap::new();
    for &(v, p) in &f.points_into {
        let root = f.place(p).root;
        paths.entry(v).or_default().entry(root).or_default().push(p);
    }
    let mut via: BTreeMap<VarId, BTreeSet<NodeId>> = BTreeMap::new();
    for &(p, v) in &f.writes_via {
        via.entry(v).or_default().insert(p);
    }
    for (&v, ps) in &paths {
        let Some(used) = uses.get(&v) else { continue };
        if !ps.keys().any(|rt| cx.changed.contains(rt)) {
            continue;
        }
        let kill = rebound.get(&v).map_or(&[][..], Vec::as_slice);
        let part = cx.part(used, kill);
        // The witnesses in the part, in the order of the nodes.
        let mut gens: Vec<(usize, usize, PlaceId, Cause)> = part
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(i, &q)| witness(cx, q, ps, via.get(&v)).map(|(p, c)| (q, i, p, c)))
            .collect();
        if gens.is_empty() {
            continue;
        }
        gens.sort_unstable_by_key(|g| g.0);
        let mut gen = vec![false; part.nodes.len()];
        for g in &gens {
            gen[g.1] = true;
        }
        let invalid = cx.reached(&part, &gen);
        let errors: Vec<(NodeId, usize)> = used
            .iter()
            .zip(&part.targets)
            .zip(&invalid)
            .filter(|(_, &bad)| bad)
            .map(|((&u, &t), _)| (u, t))
            .collect();
        if errors.is_empty() {
            continue;
        }
        // Evidence: the first invalidation that reaches each use on its own.
        let gen_nodes: Vec<usize> = gens.iter().map(|g| g.1).collect();
        let targets: Vec<usize> = errors.iter().map(|e| e.1).collect();
        cx.searches.set(cx.searches.get() + 1);
        let first = first_reaching(&part.succ, &part.pred, &gen_nodes, &part.kill, &targets);
        for (u, t) in errors {
            r.violations.error.insert((v, u));
            if let Some(&(at, _, path, cause)) = first[t].and_then(|k| gens.get(k)) {
                r.invalidations.push(Invalidation {
                    var: v,
                    path,
                    at: NodeId(u32::try_from(at).unwrap_or(u32::MAX)),
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
        let kill = rebound.get(&v).map_or(&[][..], Vec::as_slice);
        for u in reached_uses(cx, ms, kill, used) {
            out.use_after_move.insert((v, u));
        }
    }
}

/// The uses that a gen node reaches, where `kill` has the kill nodes: a
/// propagation in the part of the graph that can reach the uses ([`Ctx::part`]).
fn reached_uses(cx: &Ctx<'_>, gens: &[NodeId], kill: &[NodeId], used: &[NodeId]) -> Vec<NodeId> {
    let gens: BTreeSet<usize> = gens.iter().map(|g| g.index()).collect();
    let part = cx.part(used, kill);
    let gen: Vec<bool> = part.nodes.iter().map(|q| gens.contains(q)).collect();
    if !gen.contains(&true) {
        return Vec::new();
    }
    let after = cx.reached(&part, &gen);
    used.iter()
        .zip(after)
        .filter(|&(_, on)| on)
        .map(|(&u, _)| u)
        .collect()
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
        let kill = rebound.get(&v).map_or(&[][..], Vec::as_slice);
        for u in reached_uses(cx, &ds, kill, used) {
            out.use_before_set.insert((v, u));
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
    let unwound = by_var(&f.unwound_at);
    let aborts = cx.mask(f.may_abort.iter().copied());
    let spared: BTreeSet<(VarId, NodeId)> = f.spared_at.iter().copied().collect();
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
        let moves = cx.mask(moved.get(&v).cloned().unwrap_or_default());
        // On an abort path the unwinder finishes the value.
        let kill = cx.mask(
            moved
                .get(&v)
                .into_iter()
                .chain(unwound.get(&v))
                .flatten()
                .copied(),
        );
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
                let node = NodeId(u32::try_from(i).unwrap_or(u32::MAX));
                if l && aborts[i] && !moves[i] && !spared.contains(&(v, node)) {
                    out.abort_unhandled.insert((v, node));
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
    let spared: BTreeSet<(VarId, NodeId)> = f.spared_at.iter().copied().collect();
    // The `!Move` variables, with their roots.
    let immovable: Vec<(PlaceId, VarId)> = f
        .owner
        .iter()
        .copied()
        .filter(|&(_, v)| f.var(v).immovable)
        .collect();
    // The `!Move` variables that place `a` can be inside.
    let inside = |a: PlaceId| -> Vec<VarId> {
        immovable
            .iter()
            .filter(|&&(rt, _)| cx.prefix(rt, a))
            .map(|&(_, v)| v)
            .collect()
    };
    for (&v, us) in uses {
        // once_var(V) :- immovable(V): a copy would give the value a new address.
        let once = f.var(v).once || f.var(v).immovable;
        // A reference into a `!Move` value uses the value.
        let into: BTreeSet<VarId> = if immovable.is_empty() {
            BTreeSet::new()
        } else {
            f.points_into
                .iter()
                .filter(|&&(r, _)| r == v)
                .flat_map(|&(_, a)| inside(a))
                .collect()
        };
        if !once && into.is_empty() {
            continue;
        }
        let gen = cx.mask(us.iter().copied());
        let kill = cx.mask(rebound.get(&v).cloned().unwrap_or_default());
        let live_out = cx.backward(&gen, &kill);
        for &p in &multi {
            if !live_out[p.index()] {
                continue;
            }
            for w in once.then_some(v).into_iter().chain(into.iter().copied()) {
                if !spared.contains(&(w, p)) {
                    out.live_across_multi.insert((w, p));
                }
            }
        }
    }
    // A reference argument into a `!Move` value uses it at the node.
    for &(p, a, _) in &f.call_arg {
        if !multi.contains(&p) {
            continue;
        }
        for w in inside(a) {
            if !spared.contains(&(w, p)) {
                out.live_across_multi.insert((w, p));
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
        let std_names: BTreeSet<&str> = f.std_effects.iter().map(String::as_str).collect();
        for (i, h) in f.handlers.iter().enumerate() {
            let id = HandlerId(u32::try_from(i).unwrap_or(u32::MAX));
            // A root handler of `sim.run` forwards its effect, and so does a
            // handler whose clause performs the effect again.
            let forwards = h.sim_root
                || f.clause_performs
                    .iter()
                    .any(|(g, e)| *g == id && *e == h.effect);
            if std_names.contains(h.effect.as_str()) && !forwards {
                out.root_handler_in_lib.insert(id);
            }
        }
    }
}

/// W0203, W0406, W0705: the arguments of calls. W0204, W0605: the references
/// that a returned value or a place field gets.
fn args(cx: &Ctx<'_>, out: &mut Violations) {
    let f = cx.f;
    // W0203: `arg_outside(P, I, A)`.
    let mut stated: BTreeMap<(NodeId, u32), Vec<PlaceId>> = BTreeMap::new();
    for &(p, i, d) in &f.param_in {
        stated.entry((p, i)).or_default().push(d);
    }
    for &(p, i, a) in &f.arg_at {
        let ds = stated.get(&(p, i)).map_or(&[][..], Vec::as_slice);
        if !ds.iter().any(|&d| cx.inside_stated(a, d)) {
            out.arg_outside.insert((p, i, a));
        }
    }
    // W0204, W0605: `ref_outside(P, A)`.
    let mut stated: BTreeMap<NodeId, Vec<PlaceId>> = BTreeMap::new();
    for &(p, d) in &f.ref_in {
        stated.entry(p).or_default().push(d);
    }
    for &(p, a) in &f.ref_at {
        let ds = stated.get(&p).map_or(&[][..], Vec::as_slice);
        if !ds.iter().any(|&d| cx.inside_stated(a, d)) {
            out.ref_outside.insert((p, a));
        }
    }
    // W0406: `not_uniq(P, I)`. The mode of the argument must be a submode of
    // the mode of the parameter.
    let aliased: BTreeSet<(NodeId, u32)> = f.arg_aliased.iter().copied().collect();
    for &(p, i) in &f.uniq_param {
        let arg = uniqueness(!aliased.contains(&(p, i)));
        if !modes::submode(&arg, &uniqueness(true)) {
            out.not_uniq.insert((p, i));
        }
    }
    // W0705: `arg_effect_outside(P, I, E)`.
    let allowed: BTreeSet<(NodeId, u32, &str)> = f
        .param_effect
        .iter()
        .map(|(p, i, e)| (*p, *i, e.as_str()))
        .collect();
    for (p, i, e) in &f.fn_arg_effect {
        if !allowed.contains(&(*p, *i, e.as_str())) {
            out.arg_effect_outside.insert((*p, *i, e.clone()));
        }
    }
}

/// W0802, W0805, W0803: `sim.run` in a library, and the effects that leave a
/// body that the runtime starts.
fn root_bodies(cx: &Ctx<'_>, out: &mut Violations) {
    let f = cx.f;
    if f.library {
        out.sim_in_lib.extend(f.sim_run_at.iter().copied());
    }
    if f.started {
        let std: BTreeSet<&str> = f.std_effects.iter().map(String::as_str).collect();
        for (p, e) in &f.escapes_at {
            if !std.contains(e.as_str()) {
                out.unhandled_effect.insert((*p, e.clone()));
            } else if f.no_runtime {
                out.embedded_effect.insert((*p, e.clone()));
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
    let kept: BTreeSet<(TaskId, PlaceId)> = f.kept.iter().copied().collect();
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
            // A free of what the task reads or writes. A task keeps the cell of
            // a copy variable that it captures (`kept`).
            if found.is_none() {
                for &(m, cause) in &cx.frees[i] {
                    if kept.contains(&(t, m)) {
                        continue;
                    }
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

    // The mode of a task is the join of the modes of its captures. A task
    // whose mode does not cross threads is pinned.
    let mut task_modes: BTreeMap<TaskId, Modes> = BTreeMap::new();
    let mut_through: BTreeSet<(TaskId, VarId)> = f.mut_through.iter().copied().collect();
    for &(t, v) in &f.captures {
        let info = f.var(v);
        let writes = mut_through.contains(&(t, v));
        let mode = task_modes.entry(t).or_insert_with(modes::bottom);
        *mode = modes::join(mode, &info.capture_mode(writes));
        if f.tasks[t.index()].kind == TaskKind::Fork {
            // W0401: the captured value crosses to another thread.
            let value = Modes {
                nonportable: info.nonportable,
                ..modes::bottom()
            };
            if !modes::submode(&value, &CROSSES_THREADS) {
                r.violations.nonportable_capture.insert((t, v));
            }
            // W0403: a write through a captured reference needs `uniq`.
            if writes && !modes::submode(&uniqueness(info.uniq), &uniqueness(true)) {
                r.violations.shared_mut_capture.insert((t, v));
            }
        }
    }
    let mut pinned: BTreeSet<TaskId> = task_modes
        .iter()
        .filter(|(_, m)| !modes::submode(m, &CROSSES_THREADS))
        .map(|(&t, _)| t)
        .collect();
    // A task that runs code that the function cannot check is pinned, and so
    // is a task that starts a pinned task (`spawns_in`).
    pinned.extend(f.opaque.iter().copied());
    loop {
        let more: Vec<TaskId> = f
            .spawns_in
            .iter()
            .filter(|(t, u)| pinned.contains(u) && !pinned.contains(t))
            .map(|&(t, _)| t)
            .collect();
        if more.is_empty() {
            break;
        }
        pinned.extend(more);
    }
    for i in 0..f.tasks.len() {
        let t = TaskId(u32::try_from(i).unwrap_or(u32::MAX));
        if !pinned.contains(&t) {
            r.violations.stealable.insert(t);
        }
    }
}
