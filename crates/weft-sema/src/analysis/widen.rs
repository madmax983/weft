//! Loops in the analysis (`docs/ir.md` 6.6): the loop heads, the blocks in
//! cycles, and the widening at a loop head.
//!
//! A loop is a cycle of the CFG of a body. The driver (`super::run`) visits
//! the blocks of the cycle again until the state at the head is stable. A
//! walk such as `cur = &cur.next[0]` gives a place one step deeper at each
//! visit, so with no widening the state never stops changing. The widening
//! rules are the rules of the loop passes of the old lowering
//! (`body/loops.rs`: `widen_deeper`, `widen_place`, `collapse_places`;
//! RR1, QA4, QA7, S101, S102), applied to the state at a loop head:
//!
//! 1. A place below a wildcard place `b..` (not a one-place instance) is one
//!    of the places of `b..`: it becomes `b..`.
//! 2. A new place below a place that an earlier visit of the head added (a
//!    place of the local at the head that the state before the loop did
//!    not have) becomes the wildcard place of the outermost such place. So
//!    a walk stops after two visits, and the number of places does not grow
//!    with each visit.
//! 3. More than [`PLACES_MAX`] places of one root in the value of one local
//!    become the wildcard place of their longest common prefix.
//! 4. After [`roots_after`] visits, a new place becomes the wildcard place
//!    of the deepest place of the local at the head above it, or of its
//!    root. The roots of a component are finite, so the state is stable
//!    after a finite number of visits.
//!
//! The places of each heap slot (a value stored behind a reference
//! parameter) widen with the same rules.
//!
//! Each rule gives a place at or above the old one, so the widened state
//! holds each place that the join holds (a sound result). The function
//! values of group B are items (a finite set): they need no widening (the
//! function sets of stage F12 do).
//!
//! [`Cycles`] gives the blocks that are in a cycle: a call there gets no
//! one-place instance of its result (`docs/ir.md` 6.6).

use std::collections::{BTreeMap, BTreeSet};

use weft_facts::{FnFacts, PlaceId};
use weft_ir::{BlockId, Body, BodyId, Program};

use super::domain::{Key, State};
use crate::factgen::alpha::Roots;

/// The most places of one root in the value of one local at a loop head.
pub const PLACES_MAX: usize = 16;

/// The visits of a loop head before rule 4, in a body with `locals` locals.
///
/// After them, rule 4 widens each new place to the wildcard place of a
/// root. A chain of locals needs one visit for each local (RR1), so a chain
/// is complete before it.
pub const fn roots_after(locals: usize) -> usize {
    locals.saturating_add(16)
}

/// The most visits of a loop head in a body with `locals` locals.
///
/// After [`roots_after`] visits, each visit that is not the last adds a
/// place of a root that the head did not have, and the roots are finite. A
/// loop that needs more visits shows a bug of the analysis.
pub const fn visit_bound(locals: usize) -> usize {
    roots_after(locals).saturating_mul(2).saturating_add(32)
}

/// The rank of each block of `b` in reverse post-order (`usize::MAX` for a
/// block that the entry does not reach).
pub fn ranks(b: &Body) -> Vec<usize> {
    let order = weft_ir::order::reverse_post_order(b);
    let mut rank = vec![usize::MAX; b.blocks.len()];
    for (i, blk) in order.iter().enumerate() {
        if let Some(r) = rank.get_mut(blk.index()) {
            *r = i;
        }
    }
    rank
}

/// The loop heads of `b`, by block index.
///
/// A loop head is the target of a back edge: an edge from a block that the
/// entry reaches to a block whose rank is not higher, normal or `unwind`.
/// `rank` is the result of [`ranks`].
pub fn heads(b: &Body, rank: &[usize]) -> Vec<bool> {
    let mut out = vec![false; b.blocks.len()];
    for (bi, blk) in b.blocks.iter().enumerate() {
        let from = rank.get(bi).copied().unwrap_or(usize::MAX);
        if from == usize::MAX {
            continue;
        }
        let succs = blk
            .term
            .kind
            .unwind()
            .into_iter()
            .chain(blk.term.kind.normal_successors());
        for to in succs {
            let r = rank.get(to.index()).copied().unwrap_or(usize::MAX);
            if r <= from {
                if let Some(h) = out.get_mut(to.index()) {
                    *h = true;
                }
            }
        }
    }
    out
}

/// The blocks of the bodies of a component that are in a cycle of the CFG
/// (normal and `unwind` edges).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Cycles {
    /// The blocks in a cycle.
    blocks: BTreeSet<(BodyId, BlockId)>,
}

impl Cycles {
    /// The blocks in a cycle of each body of `comp`.
    pub fn of(p: &Program, comp: &[BodyId]) -> Self {
        let mut out = Self::default();
        for &bid in comp {
            if let Some(b) = p.bodies.get(bid.index()) {
                for blk in cyclic_blocks(b) {
                    out.blocks.insert((bid, blk));
                }
            }
        }
        out
    }

    /// True if block `block` of body `body` is in a cycle.
    pub fn has(&self, body: BodyId, block: BlockId) -> bool {
        self.blocks.contains(&(body, block))
    }
}

/// The blocks of `b` that are in a cycle: in a strongly connected
/// component with more than one block, or with an edge to itself. An
/// iterative Tarjan walk: linear in the blocks and edges.
fn cyclic_blocks(b: &Body) -> Vec<BlockId> {
    let n = b.blocks.len();
    let succ = |i: usize| -> Vec<usize> {
        b.blocks.get(i).map_or_else(Vec::new, |blk| {
            blk.term
                .kind
                .unwind()
                .into_iter()
                .chain(blk.term.kind.normal_successors())
                .map(BlockId::index)
                .filter(|&j| j < n)
                .collect()
        })
    };
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next = 0usize;
    let mut out = Vec::new();
    for start in 0..n {
        if index.get(start).is_some_and(|&x| x != usize::MAX) {
            continue;
        }
        // The walk: each frame is a block and its successors still to see.
        let mut walk: Vec<(usize, Vec<usize>, usize)> = vec![(start, succ(start), 0)];
        if let (Some(i), Some(l), Some(o)) =
            (index.get_mut(start), low.get_mut(start), on.get_mut(start))
        {
            *i = next;
            *l = next;
            *o = true;
        }
        next += 1;
        stack.push(start);
        while let Some(top) = walk.last_mut() {
            let v = top.0;
            if let Some(&w) = top.1.get(top.2) {
                top.2 += 1;
                let wi = index.get(w).copied().unwrap_or(0);
                if wi == usize::MAX {
                    if let (Some(i), Some(l), Some(o)) =
                        (index.get_mut(w), low.get_mut(w), on.get_mut(w))
                    {
                        *i = next;
                        *l = next;
                        *o = true;
                    }
                    next += 1;
                    stack.push(w);
                    walk.push((w, succ(w), 0));
                } else if on.get(w).copied().unwrap_or(false) {
                    let lw = wi;
                    if let Some(lv) = low.get_mut(v) {
                        *lv = (*lv).min(lw);
                    }
                }
                continue;
            }
            // All successors seen: close the component of `v` if it is a
            // root, and give the low link to the parent.
            walk.pop();
            let lv = low.get(v).copied().unwrap_or(0);
            if let Some(parent) = walk.last() {
                if let Some(lp) = low.get_mut(parent.0) {
                    *lp = (*lp).min(lv);
                }
            }
            if index.get(v).copied() == Some(lv) {
                let mut comp = Vec::new();
                while let Some(w) = stack.pop() {
                    if let Some(o) = on.get_mut(w) {
                        *o = false;
                    }
                    comp.push(w);
                    if w == v {
                        break;
                    }
                }
                let self_edge = comp.len() == 1 && succ(v).contains(&v);
                if comp.len() > 1 || self_edge {
                    out.extend(
                        comp.into_iter()
                            .map(|i| BlockId(u32::try_from(i).unwrap_or(u32::MAX))),
                    );
                }
            }
        }
    }
    out.sort();
    out
}

/// What the driver keeps of one loop head.
#[derive(Clone, Debug, Default)]
pub struct Head {
    /// The places of each local in the first state at the head: the state
    /// before the loop.
    pub base: BTreeMap<Key, BTreeSet<PlaceId>>,
    /// The places of each heap slot in the first state at the head.
    pub base_behind: BTreeMap<PlaceId, BTreeSet<PlaceId>>,
    /// The number of joins into the head after the first state.
    pub visits: usize,
}

impl Head {
    /// The head with the first state `st`.
    pub fn new(st: &State) -> Self {
        Self {
            base: st.places(),
            base_behind: st.behind().clone(),
            visits: 0,
        }
    }
}

/// Widens the state `st` at a loop head (see the module comment).
///
/// `old` is the state at the head before the join, and `locals` the number
/// of locals of the body. Returns false if the head needs more visits than
/// [`visit_bound`].
pub fn widen(
    facts: &mut FnFacts,
    roots: &Roots,
    st: &mut State,
    old: &State,
    head: &mut Head,
    locals: usize,
) -> bool {
    head.visits += 1;
    if head.visits > visit_bound(locals) {
        return false;
    }
    let to_root = head.visits > roots_after(locals);
    let known = old.places();
    let empty = BTreeSet::new();
    for (k, _) in st.places() {
        let known_k = known.get(&k).unwrap_or(&empty);
        let before = head.base.get(&k).unwrap_or(&empty);
        st.map_refs(k, &mut |refs: &mut BTreeSet<PlaceId>| {
            let mut out: BTreeSet<PlaceId> = BTreeSet::new();
            for &p in refs.iter() {
                if known_k.contains(&p) {
                    out.insert(p);
                } else {
                    out.insert(widen_place(facts, p, known_k, before, to_root));
                }
            }
            let out = collapse(facts, roots, out, PLACES_MAX);
            if out == *refs {
                false
            } else {
                *refs = out;
                true
            }
        });
    }
    // The heap slots widen with the same rules: a loop can store a deeper
    // place behind a reference parameter at each visit.
    let known = old.behind().clone();
    let base = head.base_behind.clone();
    st.map_behind(&mut |q: PlaceId, refs: &mut BTreeSet<PlaceId>| {
        let known_q = known.get(&q).unwrap_or(&empty);
        let before = base.get(&q).unwrap_or(&empty);
        let mut out: BTreeSet<PlaceId> = BTreeSet::new();
        for &p in refs.iter() {
            if known_q.contains(&p) {
                out.insert(p);
            } else {
                out.insert(widen_place(facts, p, known_q, before, to_root));
            }
        }
        let out = collapse(facts, roots, out, PLACES_MAX);
        if out == *refs {
            false
        } else {
            *refs = out;
            true
        }
    });
    true
}

/// Widens the new place `p` of a local at a loop head: rules 1, 2 and 4 of
/// the module comment. `known` has the places of the local at the head
/// before the join, and `before` its places before the loop.
fn widen_place(
    facts: &mut FnFacts,
    p: PlaceId,
    known: &BTreeSet<PlaceId>,
    before: &BTreeSet<PlaceId>,
    to_root: bool,
) -> PlaceId {
    if let Some(w) = below_shared_wild(facts, p) {
        return w;
    }
    // The outermost place above `p` that an earlier visit added, and the
    // deepest known place above `p`.
    let mut added = None;
    let mut deepest = None;
    let mut top = p;
    let mut at = facts.place(p).parent;
    while let Some(q) = at {
        if known.contains(&q) {
            deepest.get_or_insert(q);
            if !before.contains(&q) {
                added = Some(q);
            }
        }
        top = q;
        at = facts.place(q).parent;
    }
    if let Some(q) = added {
        return facts.wildcard(q);
    }
    if to_root {
        return facts.wildcard(deepest.unwrap_or(top));
    }
    p
}

/// The wildcard place `b..` if `p` is a place below the shared wildcard
/// place `b..` (not a one-place instance, not `b..` itself).
fn below_shared_wild(facts: &mut FnFacts, p: PlaceId) -> Option<PlaceId> {
    let b = facts.wild_base(p)?;
    let depth = facts.place(b).steps.len();
    let info = facts.place(p);
    let shared = info
        .steps
        .get(depth)
        .is_some_and(|s| !weft_facts::is_one_step(s));
    (shared && info.steps.len() > depth + 1).then(|| facts.wildcard(p))
}

/// The places `refs` with no more than `max` places of one root: the places
/// of a root with more become the wildcard place of their longest common
/// prefix (rule 3). The handle places of `rc` groups stay.
fn collapse(
    facts: &mut FnFacts,
    roots: &Roots,
    refs: BTreeSet<PlaceId>,
    max: usize,
) -> BTreeSet<PlaceId> {
    let mut count: BTreeMap<weft_facts::RootId, usize> = BTreeMap::new();
    for &p in &refs {
        if !roots.is_handle(p) {
            *count.entry(facts.place(p).root).or_default() += 1;
        }
    }
    if count.values().all(|&c| c <= max) {
        return refs;
    }
    let mut out = BTreeSet::new();
    let mut prefix: BTreeMap<weft_facts::RootId, PlaceId> = BTreeMap::new();
    for p in refs {
        let root = facts.place(p).root;
        if roots.is_handle(p) || count.get(&root).is_none_or(|&c| c <= max) {
            out.insert(p);
            continue;
        }
        let common = match prefix.get(&root) {
            None => p,
            Some(&q) => common_prefix(facts, p, q),
        };
        prefix.insert(root, common);
    }
    for q in prefix.into_values() {
        out.insert(facts.wildcard(q));
    }
    out
}

/// The deepest place on the path of `q` that is also on the path of `p`.
fn common_prefix(facts: &FnFacts, p: PlaceId, q: PlaceId) -> PlaceId {
    let mut on_p = BTreeSet::new();
    let mut at = Some(p);
    while let Some(x) = at {
        on_p.insert(x);
        at = facts.place(x).parent;
    }
    let mut at = Some(q);
    while let Some(x) = at {
        if on_p.contains(&x) {
            return x;
        }
        at = facts.place(x).parent;
    }
    q
}
