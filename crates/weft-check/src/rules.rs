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
    /// The nodes that the searches of the uses saw: the nodes of each part of
    /// the graph (`part_of`), and all the nodes for each search of the whole
    /// graph that references share. The cost of these searches grows with
    /// this count.
    pub part_nodes: u64,
    /// The searches of the whole graph that references with the same witness
    /// nodes share (`Ctx::whole`).
    pub shared: u64,
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
    /// The nodes that mutate, give to a function value or free a place of
    /// each root, in the order of the nodes. Only these nodes can invalidate a
    /// reference into the root.
    changers: BTreeMap<RootId, Vec<usize>>,
    /// The rank of the strongly connected component of each node ([`ranks`]).
    rank: Vec<usize>,
    /// The calls of [`Ctx::overlaps`].
    overlaps_calls: std::cell::Cell<u64>,
    /// The searches of the graph (`Work::searches`).
    searches: std::cell::Cell<u64>,
    /// The nodes of the parts (`Work::part_nodes`).
    part_nodes: std::cell::Cell<u64>,
    /// The shared searches (`Work::shared`).
    shared: std::cell::Cell<u64>,
    /// The work space of [`part_of`].
    scratch: std::cell::RefCell<Scratch>,
}

/// The work space of [`part_of`]. Each search puts the arrays `local` and
/// `killed` back as they were, so a search costs as much as its part, not as
/// much as the graph. The next search uses the memory of the part again.
pub(crate) struct Scratch {
    /// The index of each node in the part, or [`NOT_IN_PART`].
    pub(crate) local: Vec<usize>,
    /// The kill nodes of the search.
    pub(crate) killed: Vec<bool>,
    /// The part of the last search.
    pub(crate) part: Part,
}

impl Scratch {
    /// The work space for a graph of `n` nodes.
    pub(crate) fn new(n: usize) -> Self {
        Self {
            local: vec![NOT_IN_PART; n],
            killed: vec![false; n],
            part: Part::default(),
        }
    }
}

/// The index of a node that is not in the part.
pub(crate) const NOT_IN_PART: usize = usize::MAX;

/// The part of the graph that can reach a target from a gen node: the targets,
/// and each node with a path to a target whose inner nodes are not kill nodes,
/// and with a rank that is not less than the least rank of a gen node
/// ([`ranks`]).
///
/// A path of [`propagate`] from a gen node to a target has only such nodes:
/// each node on the path has a rank that is not less than the rank of the gen
/// node. So a propagation in the part gives the result of a propagation in the
/// whole graph at each target. Its cost grows with the size of the part.
#[derive(Default)]
pub(crate) struct Part {
    /// The node of each index of the part.
    pub(crate) nodes: Vec<usize>,
    /// The successors in the part, by index. Only the first `nodes.len()`
    /// entries are of this part: the others keep their memory for a later one.
    succ: Vec<Vec<usize>>,
    /// The predecessors in the part, by index, as `succ`.
    pred: Vec<Vec<usize>>,
    /// The kill nodes, by index.
    pub(crate) kill: Vec<bool>,
    /// The index of each target, in the order of the targets.
    pub(crate) targets: Vec<usize>,
    /// The gen nodes in the part: the index of each in the list of the gen
    /// nodes and in the part, in the order of the list. A gen node outside the
    /// part reaches no target.
    pub(crate) gens: Vec<(usize, usize)>,
    /// The targets, by index.
    is_target: Vec<bool>,
}

impl Part {
    /// The successors in the part, by index.
    pub(crate) fn succ(&self) -> &[Vec<usize>] {
        &self.succ[..self.nodes.len()]
    }

    /// The predecessors in the part, by index.
    pub(crate) fn pred(&self) -> &[Vec<usize>] {
        &self.pred[..self.nodes.len()]
    }
}

/// The result of [`Ctx::whole`].
struct Whole {
    /// The nodes that a gen node reaches.
    reached: Vec<bool>,
    /// The first gen node that reaches each node alone.
    first: Vec<Option<usize>>,
}

/// The witnesses that a node gives for the references into one list of places
/// ([`witnesses`]).
#[derive(Clone, Copy)]
struct NodeWitness {
    /// The node.
    node: usize,
    /// The first mutation of the node that invalidates, with its place.
    mutation: Option<(PlaceId, Cause)>,
    /// The least other cause of the node, with its place: a lend or a free.
    other: Option<(PlaceId, Cause)>,
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
            changers: BTreeMap::new(),
            rank: Vec::new(),
            overlaps_calls: std::cell::Cell::new(0),
            searches: std::cell::Cell::new(0),
            part_nodes: std::cell::Cell::new(0),
            shared: std::cell::Cell::new(0),
            scratch: std::cell::RefCell::new(Scratch::new(n)),
        };
        cx.frees = cx.frees_at();
        cx.rank = ranks(&cx.succ, &cx.pred);
        for (i, ((ms, ls), fs)) in cx.muts.iter().zip(&cx.lends).zip(&cx.frees).enumerate() {
            let changes = ms.iter().chain(ls).copied();
            let freed = fs.iter().map(|&(m, _)| m);
            let roots: BTreeSet<RootId> = changes.chain(freed).map(|m| f.place(m).root).collect();
            for rt in roots {
                cx.changers.entry(rt).or_default().push(i);
            }
        }
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

    /// `invalidated_at` by a free of `m`, for a reference into `p`. A move of
    /// the part `m` leaves no value in it, so it also invalidates a reference to
    /// a place above it: each reference that overlaps it.
    fn free_kills(&self, m: PlaceId, p: PlaceId, cause: Cause) -> bool {
        self.prefix(m, p)
            || (!self.same_one(m, p) && self.outer[p.index()].is_some() && self.overlaps(m, p))
            || (matches!(cause, Cause::MovePart(_)) && self.overlaps(m, p))
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

    /// Finds the targets that a gen node reaches, where `kill` has the kill
    /// nodes. `gens` has the gen nodes in the order of the nodes. The result
    /// has, for each target in the order of `targets`, true if a gen node
    /// reaches it. With `evidence`, it also has the first gen node that
    /// reaches the target alone, as an index in `gens` ([`first_reaching`]).
    ///
    /// The search runs in the part of the graph that can reach the targets
    /// from a gen node ([`Part`]): one backward search, the verified
    /// [`propagate`] in the part, and the evidence search in the part.
    fn reach(
        &self,
        gens: &[usize],
        kill: &[NodeId],
        targets: &[NodeId],
        evidence: bool,
    ) -> Vec<(bool, Option<usize>)> {
        let low = self.low(gens);
        self.reach_from(gens, low, kill, targets, evidence)
    }

    /// [`Ctx::reach`], where `low` is the least rank of a gen node, or less.
    fn reach_from(
        &self,
        gens: &[usize],
        low: Option<usize>,
        kill: &[NodeId],
        targets: &[NodeId],
        evidence: bool,
    ) -> Vec<(bool, Option<usize>)> {
        let none = vec![(false, None); targets.len()];
        // A gen node reaches only the nodes with a rank that is not less than
        // its own rank.
        let top = targets.iter().map(|t| self.rank[t.index()]).max();
        let (Some(low), Some(top)) = (low, top) else {
            return none;
        };
        if low > top {
            return none;
        }
        self.searches.set(self.searches.get() + 1);
        let targets: Vec<usize> = targets.iter().map(|t| t.index()).collect();
        let kill: Vec<usize> = kill.iter().map(|k| k.index()).collect();
        let mut scratch = self.scratch.borrow_mut();
        part_of(
            &self.succ,
            &self.pred,
            &targets,
            &kill,
            gens,
            Some((&self.rank, low)),
            &mut scratch,
        );
        let part = &scratch.part;
        let size = u64::try_from(part.nodes.len()).unwrap_or(u64::MAX);
        self.part_nodes
            .set(self.part_nodes.get().saturating_add(size));
        // The gen nodes of the part, by index of the part, in the order of
        // `gens`, with their index in `gens`.
        let mut gen = vec![false; part.nodes.len()];
        let mut order: Vec<usize> = Vec::new();
        let mut from: Vec<usize> = Vec::new();
        for &(k, i) in &part.gens {
            gen[i] = true;
            order.push(i);
            from.push(k);
        }
        if order.is_empty() {
            return none;
        }
        self.searches.set(self.searches.get() + 1);
        let out = propagate(part.succ(), &gen, &part.kill);
        if !evidence {
            return part.targets.iter().map(|&t| (out[t], None)).collect();
        }
        let hit: Vec<usize> = part.targets.iter().copied().filter(|&t| out[t]).collect();
        if hit.is_empty() {
            return none;
        }
        self.searches.set(self.searches.get() + 1);
        let first = first_reaching(part.succ(), part.pred(), &order, &part.kill, &hit);
        part.targets
            .iter()
            .map(|&t| (out[t], first[t].map(|k| from[k])))
            .collect()
    }

    /// The least rank of a node of `gens`.
    fn low(&self, gens: &[usize]) -> Option<usize> {
        gens.iter().map(|&g| self.rank[g]).min()
    }

    /// The nodes that a gen node of `gens` reaches in the whole graph with no
    /// kill node, and the first gen node that reaches each node alone, as an
    /// index in `gens` ([`first_reaching`]). It costs as much as two searches
    /// of the graph.
    fn whole(&self, gens: &[usize]) -> Whole {
        self.searches.set(self.searches.get() + 2);
        self.shared.set(self.shared.get() + 1);
        let size = u64::try_from(self.n()).unwrap_or(u64::MAX);
        self.part_nodes
            .set(self.part_nodes.get().saturating_add(size));
        let none = vec![false; self.n()];
        let mut gen = none.clone();
        for &g in gens {
            gen[g] = true;
        }
        let all: Vec<usize> = (0..self.n()).collect();
        Whole {
            reached: propagate(&self.succ, &gen, &none),
            first: first_reaching(&self.succ, &self.pred, gens, &none, &all),
        }
    }

    fn mask(&self, nodes: impl IntoIterator<Item = NodeId>) -> Vec<bool> {
        let mut m = vec![false; self.n()];
        for x in nodes {
            m[x.index()] = true;
        }
        m
    }
}

/// Fills `s.part` with the part of the graph `succ`, `pred` that can reach
/// `targets` from a gen node, where `kill` has the kill nodes ([`Part`]). With
/// `floor` `Some((rank, low))`, the part has only the targets and the nodes
/// with a `rank` of `low` or more: `low` is the least rank of a gen node.
/// `gens` has the gen nodes in the order of the nodes, with no node two times,
/// and `s.part.gens` gets those in the part. It is one backward search. `s` must have `local` all [`NOT_IN_PART`] and `killed` all
/// false, and it has them again at the end.
pub(crate) fn part_of(
    succ: &[Vec<usize>],
    pred: &[Vec<usize>],
    targets: &[usize],
    kill: &[usize],
    gens: &[usize],
    floor: Option<(&[usize], usize)>,
    s: &mut Scratch,
) {
    let Scratch {
        local,
        killed,
        part,
    } = s;
    for &k in kill {
        killed[k] = true;
    }
    part.nodes.clear();
    part.is_target.clear();
    for &t in targets {
        if local[t] == NOT_IN_PART {
            local[t] = part.nodes.len();
            part.nodes.push(t);
            part.is_target.push(true);
        }
    }
    // A target propagates to its predecessors, also when it is a kill node.
    let mut work: Vec<usize> = (0..part.nodes.len()).collect();
    while let Some(i) = work.pop() {
        let q = part.nodes[i];
        if killed[q] && !part.is_target[i] {
            continue;
        }
        for &p in &pred[q] {
            let high = floor.is_none_or(|(rank, low)| rank[p] >= low);
            if local[p] == NOT_IN_PART && high {
                local[p] = part.nodes.len();
                work.push(part.nodes.len());
                part.nodes.push(p);
                part.is_target.push(false);
            }
        }
    }
    let m = part.nodes.len();
    if part.succ.len() < m {
        part.succ.resize_with(m, Vec::new);
        part.pred.resize_with(m, Vec::new);
    }
    for (a, b) in part.succ.iter_mut().zip(part.pred.iter_mut()).take(m) {
        a.clear();
        b.clear();
    }
    for (i, &q) in part.nodes.iter().enumerate() {
        for &r in &succ[q] {
            let j = local[r];
            if j != NOT_IN_PART {
                part.succ[i].push(j);
                part.pred[j].push(i);
            }
        }
    }
    part.kill.clear();
    part.kill.extend(part.nodes.iter().map(|&q| killed[q]));
    part.targets.clear();
    part.targets.extend(targets.iter().map(|&t| local[t]));
    // The gen nodes in the part: a look at each gen node, or a binary search
    // for each node of the part, whichever costs less.
    part.gens.clear();
    if gens.len() <= part.nodes.len() {
        for (k, &g) in gens.iter().enumerate() {
            if local[g] != NOT_IN_PART {
                part.gens.push((k, local[g]));
            }
        }
    } else {
        for (i, q) in part.nodes.iter().enumerate() {
            if let Ok(k) = gens.binary_search(q) {
                part.gens.push((k, i));
            }
        }
        part.gens.sort_unstable();
    }
    for &q in &part.nodes {
        local[q] = NOT_IN_PART;
    }
    for &k in kill {
        killed[k] = false;
    }
}

/// The rank of the strongly connected component of each node, in an order of
/// the components where each edge goes to a component of the same rank or a
/// higher one. So a node reaches only nodes with a rank that is not less than
/// its own rank. It is Kosaraju's algorithm: an order of the nodes by the end
/// of their depth-first search, then a search on the reversed graph in the
/// reverse of that order. The cost is linear in the size of the graph.
pub(crate) fn ranks(succ: &[Vec<usize>], pred: &[Vec<usize>]) -> Vec<usize> {
    let n = succ.len();
    // The nodes in the order of the end of their search.
    let mut done: Vec<usize> = Vec::with_capacity(n);
    let mut seen = vec![false; n];
    let mut stack: Vec<(usize, usize)> = Vec::new();
    for root in 0..n {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        stack.push((root, 0));
        while let Some((q, next)) = stack.pop() {
            if let Some(&r) = succ[q].get(next) {
                stack.push((q, next + 1));
                if !seen[r] {
                    seen[r] = true;
                    stack.push((r, 0));
                }
            } else {
                done.push(q);
            }
        }
    }
    // The component of a node that ends last has no edge from another
    // component that is not yet ranked: it gets the next rank.
    let mut rank = vec![usize::MAX; n];
    let mut next = 0;
    let mut work: Vec<usize> = Vec::new();
    for &root in done.iter().rev() {
        if rank[root] != usize::MAX {
            continue;
        }
        rank[root] = next;
        work.push(root);
        while let Some(q) = work.pop() {
            for &p in &pred[q] {
                if rank[p] == usize::MAX {
                    rank[p] = next;
                    work.push(p);
                }
            }
        }
        next += 1;
    }
    rank
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
        shared: cx.shared.get(),
    };
    (r, work)
}

/// The places of a reference, grouped by root, in the order of `points_into`.
type Paths = BTreeMap<RootId, Vec<PlaceId>>;

/// The witnesses of `invalidated_at(R, P)` for a reference `R` that points
/// into the places `ps`: each node that can invalidate the reference, in the
/// order of the nodes. A node invalidates the reference if it mutates a place,
/// gives a place to a function value (`lends_mut`) or frees a place
/// (`frees_at`). Each of these needs a place of `ps` with the same root, so
/// only the nodes that change a root of `ps` can be witnesses (`changers`).
/// Of the mutations and of the lends, the first change that invalidates
/// counts, with the first place of `ps` that it invalidates. Of the lend and
/// the frees, the least cause counts. A mutation is less than the other
/// causes, so it is the witness of the node, except at a node with
/// `writes_via(P, R)` ([`pick`]).
fn witnesses(cx: &Ctx<'_>, ps: &Paths) -> Vec<NodeWitness> {
    let of_root = |m: PlaceId| ps.get(&cx.f.place(m).root).map_or(&[][..], Vec::as_slice);
    let mut nodes: Vec<usize> = ps
        .keys()
        .filter_map(|rt| cx.changers.get(rt))
        .flatten()
        .copied()
        .collect();
    nodes.sort_unstable();
    nodes.dedup();
    let hit = |changes: &[PlaceId]| {
        changes.iter().find_map(|&m| {
            of_root(m)
                .iter()
                .find(|&&p| cx.mutation_kills(m, p))
                .map(|&p| (p, m))
        })
    };
    let mut out = Vec::new();
    for node in nodes {
        let mutation = hit(&cx.muts[node]).map(|(p, m)| (p, Cause::Mutation(m)));
        let mut other = hit(&cx.lends[node]).map(|(p, m)| (p, Cause::Lend(m)));
        for &(m, cause) in &cx.frees[node] {
            for &p in of_root(m) {
                if cx.free_kills(m, p, cause) && other.is_none_or(|(_, b)| cause < b) {
                    other = Some((p, cause));
                }
            }
        }
        if mutation.is_some() || other.is_some() {
            out.push(NodeWitness {
                node,
                mutation,
                other,
            });
        }
    }
    out
}

/// The witness of a node for a reference: its mutation, or its other cause at
/// a node in `via`, where a mutation does not count (`writes_via(P, R)`).
fn pick(w: &NodeWitness, via: Option<&BTreeSet<NodeId>>) -> Option<(PlaceId, Cause)> {
    let id = NodeId(u32::try_from(w.node).unwrap_or(u32::MAX));
    let counts = !via.is_some_and(|ns| ns.contains(&id));
    w.mutation.filter(|_| counts).or(w.other)
}

/// The gen nodes that some references share: the witness nodes of the
/// references into one list of places, or into more lists with the same
/// witness nodes.
struct GenSet {
    /// The gen nodes, in the order of the nodes.
    nodes: Vec<usize>,
    /// The least rank of a gen node.
    low: Option<usize>,
    /// The nodes of the parts of the searches of these gen nodes.
    spent: u64,
    /// The search of these gen nodes in the whole graph, with no kill node.
    whole: Option<Whole>,
}

/// W0301: `error(R, P)`.
///
/// References that point into the same places share their witnesses
/// ([`witnesses`]). Each reference with a witness has a search in the part of
/// the graph that can reach its uses from a witness ([`Ctx::reach`]).
///
/// References with the same witness nodes also share a search in the whole
/// graph with no kill node ([`Ctx::whole`]), when their parts have cost as
/// much as the graph. A reference with no kill node in the result has the
/// result of that search: a path from a gen node in the result has only nodes
/// in the result, so no kill node stops it. Thus the shared search costs at
/// most as much as the parts before it, and many references that a node
/// invalidates, with uses after it, cost about as much as one.
fn invalidation(
    cx: &Ctx<'_>,
    rebound: &BTreeMap<VarId, Vec<NodeId>>,
    uses: &BTreeMap<VarId, Vec<NodeId>>,
    r: &mut Report,
) {
    let f = cx.f;
    let mut paths: BTreeMap<VarId, Paths> = BTreeMap::new();
    for &(v, p) in &f.points_into {
        let root = f.place(p).root;
        paths.entry(v).or_default().entry(root).or_default().push(p);
    }
    let mut via: BTreeMap<VarId, BTreeSet<NodeId>> = BTreeMap::new();
    for &(p, v) in &f.writes_via {
        via.entry(v).or_default().insert(p);
    }
    let size = u64::try_from(cx.n()).unwrap_or(u64::MAX);
    // The witnesses of each list of places, with the index of their gen set.
    let mut shared: BTreeMap<&Paths, (Vec<NodeWitness>, usize)> = BTreeMap::new();
    let mut sets: Vec<GenSet> = Vec::new();
    let mut set_of: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
    for (&v, ps) in &paths {
        let Some(used) = uses.get(&v) else { continue };
        let (all, set) = shared.entry(ps).or_insert_with(|| {
            let all = witnesses(cx, ps);
            let nodes: Vec<usize> = all.iter().map(|w| w.node).collect();
            let set = *set_of.entry(nodes).or_insert_with_key(|nodes| {
                sets.push(GenSet {
                    low: cx.low(nodes),
                    nodes: nodes.clone(),
                    spent: 0,
                    whole: None,
                });
                sets.len() - 1
            });
            (all, set)
        });
        if all.is_empty() {
            continue;
        }
        let kill = rebound.get(&v).map_or(&[][..], Vec::as_slice);
        let via_v = via.get(&v);
        // A node in `via` with a mutation only is no gen node here.
        let skips = via_v.is_some_and(|ns| {
            ns.iter().any(|n| {
                let k = all.binary_search_by_key(&n.index(), |w| w.node);
                k.is_ok_and(|k| pick(&all[k], via_v).is_none())
            })
        });
        // The gen nodes of the reference: all the witnesses, or those that
        // count here.
        let own: Vec<NodeWitness> = if skips {
            all.iter()
                .copied()
                .filter(|w| pick(w, via_v).is_some())
                .collect()
        } else {
            Vec::new()
        };
        let gens: &[NodeWitness] = if skips { &own } else { all };
        let reached = if skips {
            let nodes: Vec<usize> = own.iter().map(|w| w.node).collect();
            cx.reach(&nodes, kill, used, true)
        } else {
            let gs = &mut sets[*set];
            let whole = gs
                .whole
                .as_ref()
                .filter(|w| kill.iter().all(|k| !w.reached[k.index()]));
            if let Some(w) = whole {
                used.iter()
                    .map(|u| (w.reached[u.index()], w.first[u.index()]))
                    .collect()
            } else {
                let before = cx.part_nodes.get();
                let reached = cx.reach_from(&gs.nodes, gs.low, kill, used, true);
                gs.spent = gs
                    .spent
                    .saturating_add(cx.part_nodes.get().saturating_sub(before));
                if gs.whole.is_none() && gs.spent >= size {
                    gs.whole = Some(cx.whole(&gs.nodes));
                }
                reached
            }
        };
        for (&u, &(bad, first)) in used.iter().zip(&reached) {
            if !bad {
                continue;
            }
            r.violations.error.insert((v, u));
            // Evidence: the first invalidation that reaches the use on its own.
            let first = first.and_then(|k| gens.get(k));
            if let Some((w, (path, cause))) = first.and_then(|w| pick(w, via_v).map(|c| (w, c))) {
                r.invalidations.push(Invalidation {
                    var: v,
                    path,
                    at: NodeId(u32::try_from(w.node).unwrap_or(u32::MAX)),
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

/// The uses that a gen node reaches, where `kill` has the kill nodes
/// ([`Ctx::reach`]).
fn reached_uses(cx: &Ctx<'_>, gens: &[NodeId], kill: &[NodeId], used: &[NodeId]) -> Vec<NodeId> {
    let mut gens: Vec<usize> = gens.iter().map(|g| g.index()).collect();
    gens.sort_unstable();
    gens.dedup();
    let reached = cx.reach(&gens, kill, used, false);
    used.iter()
        .zip(reached)
        .filter(|&(_, (on, _))| on)
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
    // A move of a part that leaves a linear part does not end the value.
    let rest: BTreeSet<(VarId, NodeId)> = f.rest_linear.iter().copied().collect();
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
        let ends_value: Vec<NodeId> = moved
            .get(&v)
            .into_iter()
            .flatten()
            .copied()
            .filter(|&n| !rest.contains(&(v, n)))
            .collect();
        let moves = cx.mask(ends_value.iter().copied());
        // On an abort path the unwinder finishes the value.
        let kill = cx.mask(
            ends_value
                .iter()
                .chain(unwound.get(&v).into_iter().flatten())
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
