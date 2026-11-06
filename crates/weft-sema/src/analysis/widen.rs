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
//! 5. A part of the value of a local deeper than [`DEPTH_MAX`] steps at a
//!    loop head becomes one summary part: the part at depth [`DEPTH_MAX`]
//!    is a leaf with the join of the part and of each part below it
//!    (`Tree::limit_depth`, stage R0c). A loop that builds a value of a
//!    recursive type (`l = Cons(i, l)`) gives a value one level deeper at
//!    each visit; with this rule the depth of the values is finite.
//!
//! The places of each heap slot (a value stored behind a reference
//! parameter) widen with the same rules.
//!
//! Each rule gives a place at or above the old one, so the widened state
//! holds each place that the join holds (a sound result). A summary part
//! holds each value of the parts that it replaces, and a read below it gets
//! the summary: it also holds each value that the join holds. The function
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

/// The most steps of a path of parts of the value of one local at a loop
/// head (rule 5). A level of an enum is two steps (the variant and the
/// field), so a list keeps four levels of its own parts.
pub const DEPTH_MAX: usize = 8;

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
///
/// A handled body, a scope body and a clause body run in a frame of their
/// own, at a block of their site (the `handle` or the `scope`). Each query
/// also reads the chain of sites: a body runs again when its site block is
/// in a cycle (gap G1 of stage C1.5: `while .. { handle .. in { g() } }`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Cycles {
    /// The blocks in a cycle.
    blocks: BTreeSet<(BodyId, BlockId)>,
    /// The blocks of `blocks` that only the re-entry edges after code of a
    /// caller put in a cycle ([`Self::add_code_rows_at`], issue #56).
    code: BTreeSet<(BodyId, BlockId)>,
    /// For each block, the run nodes of code of a caller
    /// ([`Self::add_code_rows_at`]) whose re-entry edges reach the block: a
    /// resume there runs the block again (hole C1-H1 of stage C1.1).
    code_from: BTreeMap<(BodyId, BlockId), BTreeSet<(BodyId, BlockId)>>,
    /// The site of each nested body of the component: the block whose
    /// terminator runs it (`Handle` for a handled body and its clauses,
    /// `Scope` for a scope body).
    site: BTreeMap<BodyId, (BodyId, BlockId)>,
    /// The nested bodies that each site block runs.
    opens: BTreeMap<(BodyId, BlockId), Vec<BodyId>>,
    /// The clause bodies of the component, with their handled body.
    clauses: BTreeMap<BodyId, BodyId>,
}

impl Cycles {
    /// The blocks in a cycle of each body of `comp`, and the sites of the
    /// nested bodies of `comp`. A nested body with no site in `comp` is in
    /// a cycle (a conservative result).
    pub fn of(p: &Program, comp: &[BodyId]) -> Self {
        let mut out = Self::default();
        let inside: BTreeSet<BodyId> = comp.iter().copied().collect();
        for &bid in comp {
            let Some(b) = p.bodies.get(bid.index()) else {
                continue;
            };
            for blk in cyclic_blocks(b) {
                out.insert((bid, blk), false);
            }
            for (i, blk) in b.blocks.iter().enumerate() {
                let at = (bid, BlockId(u32::try_from(i).unwrap_or(u32::MAX)));
                let nested: Vec<BodyId> = match &blk.term.kind {
                    weft_ir::TermKind::Handle { handler, .. } => {
                        p.handlers.get(handler.index()).map_or_else(Vec::new, |hd| {
                            for (_, c) in &hd.clauses {
                                out.clauses.insert(*c, hd.handled);
                            }
                            std::iter::once(hd.handled)
                                .chain(hd.clauses.iter().map(|(_, c)| *c))
                                .collect()
                        })
                    }
                    weft_ir::TermKind::Scope { scope, .. } => p
                        .scopes
                        .get(scope.index())
                        .map_or_else(Vec::new, |s| vec![s.body]),
                    _ => Vec::new(),
                };
                let nested: Vec<BodyId> =
                    nested.into_iter().filter(|n| inside.contains(n)).collect();
                for &n in &nested {
                    out.site.insert(n, at);
                }
                if !nested.is_empty() {
                    out.opens.insert(at, nested);
                }
            }
        }
        for &bid in comp {
            let Some(b) = p.bodies.get(bid.index()) else {
                continue;
            };
            let nested = matches!(
                b.kind,
                weft_ir::BodyKind::Handled(_)
                    | weft_ir::BodyKind::Scope(_)
                    | weft_ir::BodyKind::Clause(..)
            );
            if nested && !out.site.contains_key(&bid) {
                for i in 0..b.blocks.len() {
                    out.insert((bid, BlockId(u32::try_from(i).unwrap_or(u32::MAX))), false);
                }
            }
        }
        out
    }

    /// Adds the cycles of the re-entry edges of the facts (`docs/ir.md` 6.5,
    /// plan stage F16): each block of the handled body of a handler whose
    /// clause a `multi` resume can run more than once, and of the bodies that
    /// splice into it, and each block of the clauses of a handler whose
    /// clauses can run more than once (their code after `resume` runs at
    /// `Post`, in a cycle). One-place instances are off there (V097).
    pub fn add_handlers(
        &mut self,
        p: &Program,
        comp: &[BodyId],
        frames: &crate::factgen::frames::Frames,
    ) {
        for (i, hd) in p.handlers.iter().enumerate() {
            let h = weft_ir::HandlerId(u32::try_from(i).unwrap_or(u32::MAX));
            if !comp.contains(&hd.handled) {
                continue;
            }
            let multi = !frames.reentries(h).is_empty();
            let twice = multi || frames.runs_twice(h);
            if !twice {
                continue;
            }
            let roots: Vec<BodyId> = hd
                .clauses
                .iter()
                .map(|(_, c)| *c)
                .chain(multi.then_some(hd.handled))
                .collect();
            for &bid in comp {
                if !roots
                    .iter()
                    .any(|&r| crate::analysis::clause::inside(p, bid, r))
                {
                    continue;
                }
                if let Some(b) = p.bodies.get(bid.index()) {
                    for i in 0..b.blocks.len() {
                        self.insert((bid, BlockId(u32::try_from(i).unwrap_or(u32::MAX))), false);
                    }
                }
            }
        }
    }

    /// Adds the cycles of the re-entry edges after a node that can wait at a
    /// `multi` operation of a handler of a caller (OL-R2a, plan stage F16):
    /// each block of a body of `comp` that such a node of the body reaches,
    /// and each block of the handled bodies that splice into the body.
    pub fn add_rows(
        &mut self,
        p: &Program,
        tys: &weft_ir::TyTable,
        sums: &super::Summaries,
        comp: &[BodyId],
    ) {
        let rows: Vec<(BodyId, BlockId)> = comp
            .iter()
            .flat_map(|&bid| {
                crate::factgen::frames::row_multi_nodes(p, tys, sums, bid)
                    .into_iter()
                    .map(move |x| (bid, x))
            })
            .collect();
        self.add_rows_at(p, comp, &rows);
    }

    /// Adds the cycles after the performs of the closure bodies of `comp`
    /// through a captured capability whose handler can resume more than
    /// once (`crate::factgen::frames::captured_multi_nodes`, hole C1-H4).
    pub fn add_captured(&mut self, p: &Program, tys: &weft_ir::TyTable, comp: &[BodyId]) {
        let rows: Vec<(BodyId, BlockId)> = comp
            .iter()
            .flat_map(|&bid| {
                crate::factgen::frames::captured_multi_nodes(p, tys, bid)
                    .into_iter()
                    .map(move |x| (bid, x))
            })
            .collect();
        self.add_rows_at(p, comp, &rows);
    }

    /// [`Self::add_rows`] for the nodes `rows` (a body and a block).
    pub fn add_rows_at(&mut self, p: &Program, comp: &[BodyId], rows: &[(BodyId, BlockId)]) {
        self.rows_at(p, comp, rows, false);
    }

    /// [`Self::add_rows_at`] for run nodes that only code of a caller makes
    /// `multi` (a run of a value of the interface whose value the body does
    /// not know, issue #56). The blocks are in a cycle, but
    /// [`Self::has_strict`] does not count them: the caller gives the value
    /// and applies its `multi` part at its own node (exception E1 of stage
    /// C1.5, `docs/ir.md`).
    pub fn add_code_rows_at(&mut self, p: &Program, comp: &[BodyId], rows: &[(BodyId, BlockId)]) {
        self.rows_at(p, comp, rows, true);
    }

    /// Adds block `key` to the cycles. With `code`, only the re-entry edges
    /// after code of a caller put it there.
    fn insert(&mut self, key: (BodyId, BlockId), code: bool) {
        if code {
            if !self.blocks.contains(&key) {
                self.code.insert(key);
            }
        } else {
            self.code.remove(&key);
        }
        self.blocks.insert(key);
    }

    /// The successors of block `x` of body `b` in the spliced graph of the
    /// component (gap G2 of stage C1.5): the successors in the body; the
    /// entry of each body that the block runs (a `handle` or a `scope`, and
    /// the clauses of the handler); from a `Return` of a nested body, the
    /// normal successors of its site; from an `UnwindExit`, the `unwind`
    /// block of the site (with none, each `UnwindExit` of the site body);
    /// from a `resume`, the entry of the handled body of the clause (the
    /// continuation can be at each perform there).
    fn next_of(&self, p: &Program, (b, x): (BodyId, BlockId), out: &mut Vec<(BodyId, BlockId)>) {
        let Some(blk) = p
            .bodies
            .get(b.index())
            .and_then(|bd| bd.blocks.get(x.index()))
        else {
            return;
        };
        let kind = &blk.term.kind;
        out.extend(kind.successors().into_iter().map(|y| (b, y)));
        if let Some(ns) = self.opens.get(&(b, x)) {
            for &n in ns {
                if let Some(nb) = p.bodies.get(n.index()) {
                    out.push((n, nb.entry));
                }
            }
        }
        if matches!(kind, weft_ir::TermKind::Resume { .. }) {
            if let Some(h) = self.clause_of(b) {
                if let Some(hb) = p.bodies.get(h.index()) {
                    out.push((h, hb.entry));
                }
            }
        }
        let Some(&(sb, sx)) = self.site.get(&b) else {
            return;
        };
        let Some(site) = p.bodies.get(sb.index()) else {
            return;
        };
        let Some(st) = site.blocks.get(sx.index()).map(|k| &k.term.kind) else {
            return;
        };
        match kind {
            weft_ir::TermKind::Return => {
                out.extend(st.normal_successors().into_iter().map(|y| (sb, y)));
            }
            weft_ir::TermKind::UnwindExit => match st.unwind() {
                Some(u) => out.push((sb, u)),
                None => out.extend(
                    site.blocks
                        .iter()
                        .enumerate()
                        .filter(|(_, k)| matches!(k.term.kind, weft_ir::TermKind::UnwindExit))
                        .map(|(i, _)| (sb, BlockId(u32::try_from(i).unwrap_or(u32::MAX)))),
                ),
            },
            _ => {}
        }
    }

    /// The handled body of the clause that body `b` is, or is inside (up
    /// the chain of sites).
    fn clause_of(&self, b: BodyId) -> Option<BodyId> {
        let mut at = b;
        for _ in 0..=self.site.len() {
            if let Some(&h) = self.clauses.get(&at) {
                return Some(h);
            }
            at = self.site.get(&at)?.0;
        }
        None
    }

    /// The nodes (a body and a block) that the walk of the spliced graph
    /// ([`Self::next_of`]) reaches from the successors of the nodes
    /// `from`, in the bodies of `comp`; with `own`, the nodes `from` too.
    fn walk(
        &self,
        p: &Program,
        comp: &BTreeSet<BodyId>,
        from: &[(BodyId, BlockId)],
        own: bool,
    ) -> BTreeSet<(BodyId, BlockId)> {
        let mut seen: BTreeSet<(BodyId, BlockId)> = BTreeSet::new();
        let mut work: Vec<(BodyId, BlockId)> = Vec::new();
        if own {
            work.extend(from.iter().copied());
        } else {
            for &f in from {
                self.next_of(p, f, &mut work);
            }
        }
        let mut next = Vec::new();
        while let Some(n) = work.pop() {
            if !comp.contains(&n.0) || !seen.insert(n) {
                continue;
            }
            next.clear();
            self.next_of(p, n, &mut next);
            work.extend(next.iter().copied());
        }
        seen
    }

    /// The cycles of the re-entry edges after the nodes `rows`; `code` as in
    /// [`Self::insert`]. The re-entry runs the code after the node again:
    /// each node that the walk of the spliced graph reaches from the node,
    /// and each block of the bodies that splice into the body of the node.
    fn rows_at(&mut self, p: &Program, comp: &[BodyId], rows: &[(BodyId, BlockId)], code: bool) {
        if rows.is_empty() {
            return;
        }
        if code {
            for &row in rows {
                self.note_code_row(p, comp, row);
            }
        }
        let inside: BTreeSet<BodyId> = comp.iter().copied().collect();
        for key in self.walk(p, &inside, rows, true) {
            self.insert(key, code);
        }
        for key in Self::spliced_blocks(p, comp, rows) {
            self.insert(key, code);
        }
    }

    /// Each block of the bodies of `comp` that splice into the body of a
    /// node of `rows`.
    fn spliced_blocks(
        p: &Program,
        comp: &[BodyId],
        rows: &[(BodyId, BlockId)],
    ) -> Vec<(BodyId, BlockId)> {
        let bodies: BTreeSet<BodyId> = rows.iter().map(|r| r.0).collect();
        let mut out = Vec::new();
        for &other in comp {
            let root = crate::factgen::handlers::splice_root(p, other);
            if other == root || !bodies.contains(&root) {
                continue;
            }
            if let Some(ob) = p.bodies.get(other.index()) {
                for i in 0..ob.blocks.len() {
                    out.push((other, BlockId(u32::try_from(i).unwrap_or(u32::MAX))));
                }
            }
        }
        out
    }

    /// The run nodes of code of a caller (a body and a block) whose re-entry
    /// edges reach block `block` of body `body` ([`Self::add_code_rows_at`]),
    /// also through the sites of the body.
    pub fn code_from(&self, body: BodyId, block: BlockId) -> BTreeSet<(BodyId, BlockId)> {
        let mut out = BTreeSet::new();
        let mut at = (body, block);
        for _ in 0..=self.site.len() {
            if let Some(s) = self.code_from.get(&at) {
                out.extend(s.iter().copied());
            }
            match self.site.get(&at.0) {
                Some(&s) => at = s,
                None => break,
            }
        }
        out
    }

    /// Notes for each node that the re-entry edges after the run node `row`
    /// of code of a caller reach that the row reaches it ([`Self::code_from`]):
    /// the nodes that the walk of the spliced graph reaches from the
    /// successors of the row, and each block of the bodies that splice into
    /// the body of the row.
    fn note_code_row(&mut self, p: &Program, comp: &[BodyId], row: (BodyId, BlockId)) {
        let inside: BTreeSet<BodyId> = comp.iter().copied().collect();
        let mut keys = self.walk(p, &inside, &[row], false);
        keys.extend(Self::spliced_blocks(p, comp, &[row]));
        for key in keys {
            self.code_from.entry(key).or_default().insert(row);
        }
    }

    /// True if block `block` of body `body` is in a cycle, or a site of the
    /// body is.
    pub fn has(&self, body: BodyId, block: BlockId) -> bool {
        let mut at = (body, block);
        for _ in 0..=self.site.len() {
            if self.blocks.contains(&at) {
                return true;
            }
            match self.site.get(&at.0) {
                Some(&s) => at = s,
                None => return false,
            }
        }
        true
    }

    /// True if block `block` of body `body`, or a site of the body, is in a
    /// cycle for a reason other than the re-entry edges after code of a
    /// caller ([`Self::add_code_rows_at`]): a run of a value of the
    /// interface there runs the value more than once (part `runs`, issue
    /// #56; exception E2 of stage C1.5).
    pub fn has_strict(&self, body: BodyId, block: BlockId) -> bool {
        let mut at = (body, block);
        for _ in 0..=self.site.len() {
            if self.blocks.contains(&at) && !self.code.contains(&at) {
                return true;
            }
            match self.site.get(&at.0) {
                Some(&s) => at = s,
                None => return false,
            }
        }
        true
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
    // Rule 5: the depth of the values is finite.
    st.limit_depth(DEPTH_MAX);
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
