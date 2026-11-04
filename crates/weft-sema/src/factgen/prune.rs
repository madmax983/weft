//! The rows that no rule of the spec can read (plan stage C1.4, issue #62).
//!
//! The templates write the rows of a variable with no test of its flags: a
//! new value of a temporary of plain data gets `rebound_at` and `empty_at`,
//! its end gets `scope_end`, and each operand gets `uses`. Most of these rows
//! join no rule. [`prune`] removes them from the facts of the check, after the
//! fact generator, the summaries and the post-passes (`holders`, `handlers`,
//! `generic`) read them. The fact oracle (`docs/ir.md` 8.5) reads the facts
//! of [`super::emit_parts`], before this step.
//!
//! The test of a row reads only the flags of its variable and the rows of
//! `points_into`, `moved_at`, `unset_at` and `owner`, which stay. Each test
//! comes from the rules of `spec/weft.dl` that read the relation:
//!
//! | relation | rules | the row stays if its variable `V` |
//! | --- | --- | --- |
//! | `empty_at` | `live_linear` | is `linear` |
//! | `overwrites` | `live_linear`, `overwritten` | is `linear` |
//! | `rest_linear` | `ends_linear` (only in `live_linear`, `abort_unhandled`) | is `linear` |
//! | `spared_at` | `abort_unhandled`, `live_across_multi` | is `linear`, `once_var` or `immovable` |
//! | `scope_end`, `unwound_at` | `frees_at`, `unconsumed`, `live_linear` | has an `owner` row, or is `linear` |
//! | `rebound_at` | `invalid`, `moved`, `unset`, `live_linear`, `overwritten`, `live_in` | has a `points_into`, `moved_at` or `unset_at` row, or is `linear`, `once_var` or `immovable` |
//! | `uses` | `error`, `use_after_move`, `use_before_set`, `live_in` | as for `rebound_at` |
//!
//! Each fact of `live_linear(V, _)` needs `linear(V)`, each fact of
//! `invalid(R, _)` needs a `points_into(R, _)`, `moved(V, _)` needs a
//! `moved_at(V, _)` and `unset(V, _)` needs an `unset_at(V, _)`. A fact of
//! `live_in(V, _)` joins `live_across_multi` only through `once_var(V)` (also
//! from `immovable(V)`) or through `points_into(V, _)`. So a removed row
//! derives no fact of a violation relation, and the checker gives the same
//! violations.
//!
//! **Place trees.** The rules relate two places only inside one tree: the
//! places below one root place (`alias`, `prefix`, `overlaps`, `wild_at`,
//! `within` and the other place rules follow `parent`). A tree is *read* if
//! a place of it is in a `points_into`, `task_reads`, `task_writes` or
//! `call_arg` row, has `param_rooted`, or is a `shared_root`. The rows of
//! `mutates_at`, `reads_at`, `lends_mut` and `releases_at` at a place of a
//! tree that is not read join no rule that gives a violation:
//! `invalidated_at` needs the tree of a `points_into` row, `task_conflict`
//! the tree of a task access, `needs_decl` a `param_rooted` place, and
//! `shared_mutation` a `shared_root`. The `owner` rows of a variable go if
//! no root of the variable is in a tree that is read: then `frees_at` gives
//! no fact in a tree that is read, and `part_moved_at` of the variable
//! counts only for the `frees_at` of the variable (`live_across_multi`
//! reads `owner` only with a `points_into` or a `call_arg` row in the same
//! tree). The place table and the rows of `moved_part`, `footprint`,
//! `call_mut`, `kept` and the other relations stay. Then `scope_end` and
//! `unwound_at` follow the `owner` rows that stay.
//!
//! **Nodes with no fact.** Then a node with no row of a relation other than
//! `cfg_edge` (and no site of a diagnostic) leaves the graph if it has at
//! most one predecessor or at most one successor: each predecessor gets an
//! edge to each successor (`merge_free_nodes`). Each rule that follows
//! `cfg_edge` (`invalid`, `moved`, `unset`, `live_linear`, `live_in`,
//! `live_out`, `active`) stops or starts only at a node with a row of the
//! node, so a path through such a node and the path with no such node give
//! the same facts at each other node. A violation needs a row at its node.
//! The entry node and each `handler clause` node stay (the diagnostics
//! start a search there).
//!
//! **Places that no row names.** Last, a tree that is not read and whose
//! places no row names leaves the place table (`compact_places`): its
//! rows of `place`, `parent`, `unstable`, `wildcard`, `one_place`,
//! `step_alias` and `step_within` join only rows of places of the same tree.
//! The places that stay keep their order, with new ids.

use std::collections::{BTreeSet, HashSet};

use weft_facts::{FnFacts, NodeId, PlaceId, VarId};

/// The root place of the tree of each place of `facts` (through `parent`).
fn trees(facts: &FnFacts) -> Vec<usize> {
    let n = facts.places.len();
    let mut top: Vec<Option<usize>> = vec![None; n];
    for i in 0..n {
        // The places on the way up from `i` that have no root yet.
        let mut path = Vec::new();
        let mut at = i;
        let root = loop {
            if let Some(Some(t)) = top.get(at) {
                break *t;
            }
            path.push(at);
            match facts.places.get(at).and_then(|p| p.parent) {
                Some(q) if q.index() < n && path.len() <= n => at = q.index(),
                _ => break at,
            }
        };
        for x in path {
            if let Some(t) = top.get_mut(x) {
                *t = Some(root);
            }
        }
    }
    top.into_iter()
        .enumerate()
        .map(|(i, t)| t.unwrap_or(i))
        .collect()
}

/// Removes the rows of the places in trees that no rule reads (see the
/// module documentation).
fn prune_trees(facts: &mut FnFacts) {
    let top = trees(facts);
    let tree = |p: PlaceId| top.get(p.index()).copied().unwrap_or(usize::MAX);
    let mut read: HashSet<usize> = HashSet::new();
    let anchors = facts
        .points_into
        .iter()
        .map(|&(_, q)| q)
        .chain(facts.task_reads.iter().map(|&(_, q)| q))
        .chain(facts.task_writes.iter().map(|&(_, q)| q))
        .chain(facts.call_arg.iter().map(|&(_, q, _)| q))
        .chain(facts.shared_root.iter().copied());
    for q in anchors {
        read.insert(tree(q));
    }
    for i in 0..facts.places.len() {
        let id = PlaceId(u32::try_from(i).unwrap_or(u32::MAX));
        if facts.param_rooted(id) {
            read.insert(tree(id));
        }
    }
    // A place that is not in the table stays read.
    let is_read = |q: PlaceId| q.index() >= top.len() || read.contains(&tree(q));
    facts.mutates_at.retain(|&(_, q)| is_read(q));
    facts.reads_at.retain(|&(_, q)| is_read(q));
    facts.lends_mut.retain(|&(_, q)| is_read(q));
    facts.releases_at.retain(|&(_, q)| is_read(q));
    let kept: HashSet<VarId> = facts
        .owner
        .iter()
        .filter(|&&(r, _)| is_read(r))
        .map(|&(_, v)| v)
        .collect();
    facts.owner.retain(|(_, v)| kept.contains(v));
}

/// Removes the rows of `facts` that no rule of the spec can read (see the
/// module documentation).
pub fn prune(facts: &mut FnFacts) {
    prune_trees(facts);
    let points: HashSet<VarId> = facts.points_into.iter().map(|&(v, _)| v).collect();
    let moved: HashSet<VarId> = facts.moved_at.iter().map(|&(v, _)| v).collect();
    let unset: HashSet<VarId> = facts.unset_at.iter().map(|&(v, _)| v).collect();
    let owned: HashSet<VarId> = facts.owner.iter().map(|&(_, v)| v).collect();
    let n = facts.vars.len();
    let mut linear = vec![false; n];
    let mut multi = vec![false; n];
    let mut ends = vec![false; n];
    let mut flow = vec![false; n];
    for (i, info) in facts.vars.iter().enumerate() {
        let v = VarId(u32::try_from(i).unwrap_or(u32::MAX));
        let once = info.once || info.immovable;
        linear[i] = info.linear;
        multi[i] = info.linear || once;
        ends[i] = info.linear || owned.contains(&v);
        flow[i] =
            info.linear || once || points.contains(&v) || moved.contains(&v) || unset.contains(&v);
    }
    // A variable that is not in the table keeps its rows.
    let test = |flags: &[bool], v: VarId| flags.get(v.index()).copied().unwrap_or(true);
    facts.empty_at.retain(|&(v, _)| test(&linear, v));
    facts.overwrites.retain(|&(v, _)| test(&linear, v));
    facts.rest_linear.retain(|&(v, _)| test(&linear, v));
    facts.spared_at.retain(|&(v, _)| test(&multi, v));
    facts.scope_end.retain(|&(v, _)| test(&ends, v));
    facts.unwound_at.retain(|&(v, _)| test(&ends, v));
    facts.rebound_at.retain(|&(v, _)| test(&flow, v));
    facts.uses.retain(|&(v, _)| test(&flow, v));
    merge_free_nodes(facts);
    compact_places(facts);
}

/// Each place of a row of `facts` (not of the place table), once for each
/// row. Each field, so that a new relation cannot miss its places.
fn named_places(facts: &mut FnFacts, f: &mut dyn FnMut(&mut PlaceId)) {
    let FnFacts {
        name: _,
        roots: _,
        places: _,
        vars: _,
        nodes: _,
        tasks: _,
        handlers: _,
        by_value: _,
        arg_order: _,
        effect_names: _,
        hidden_effects: _,
        int_ops: _,
        arg_sites: _,
        ref_sites: _,
        caps: _,
        cfg_edge: _,
        points_into,
        mutates_at,
        reads_at,
        performs_at: _,
        footprint,
        rebound_at: _,
        uses: _,
        moved_at: _,
        scope_end: _,
        overwrites: _,
        unset_at: _,
        empty_at: _,
        unwound_at: _,
        owner,
        moved_part,
        rest_linear: _,
        releases_at,
        may_abort: _,
        multi_at: _,
        spared_at: _,
        clause_multi: _,
        body_multi: _,
        resumes_at: _,
        clause_performs: _,
        has_signature: _,
        declared_mut,
        declared_effect: _,
        escapes_at: _,
        shared_root,
        spawned_at: _,
        joined_at: _,
        task_reads,
        task_writes,
        captures: _,
        mut_through: _,
        kept,
        spawns_in: _,
        opaque: _,
        call_mut,
        call_arg,
        lends_mut,
        writes_via: _,
        arg_at,
        param_in,
        uniq_param: _,
        arg_aliased: _,
        fn_arg_effect: _,
        param_effect: _,
        sim_run_at: _,
        ref_at,
        ref_in,
        std_effects: _,
        library: _,
        started: _,
        no_runtime: _,
        place_index: _,
    } = facts;
    for x in points_into.iter_mut() {
        f(&mut x.1);
    }
    for x in mutates_at.iter_mut() {
        f(&mut x.1);
    }
    for x in reads_at.iter_mut() {
        f(&mut x.1);
    }
    for x in footprint.iter_mut() {
        f(&mut x.1);
    }
    for x in owner.iter_mut() {
        f(&mut x.0);
    }
    for x in moved_part.iter_mut() {
        f(&mut x.0);
    }
    for x in releases_at.iter_mut() {
        f(&mut x.1);
    }
    for x in declared_mut.iter_mut().chain(shared_root.iter_mut()) {
        f(x);
    }
    for x in task_reads.iter_mut() {
        f(&mut x.1);
    }
    for x in task_writes.iter_mut() {
        f(&mut x.1);
    }
    for x in kept.iter_mut() {
        f(&mut x.1);
    }
    for x in call_mut.iter_mut() {
        f(&mut x.1);
    }
    for x in call_arg.iter_mut() {
        f(&mut x.1);
    }
    for x in lends_mut.iter_mut() {
        f(&mut x.1);
    }
    for x in arg_at.iter_mut() {
        f(&mut x.2);
    }
    for x in param_in.iter_mut() {
        f(&mut x.2);
    }
    for x in ref_at.iter_mut() {
        f(&mut x.1);
    }
    for x in ref_in.iter_mut() {
        f(&mut x.1);
    }
}

/// Removes the trees of places that are not read and that no row names
/// (see the module documentation), and gives the other places new ids in
/// their order.
fn compact_places(facts: &mut FnFacts) {
    let top = trees(facts);
    let n = top.len();
    let mut used = vec![false; n];
    let mut outside = false;
    named_places(facts, &mut |q| match top.get(q.index()) {
        Some(&t) => {
            if let Some(u) = used.get_mut(t) {
                *u = true;
            }
        }
        None => outside = true,
    });
    for i in 0..n {
        let id = PlaceId(u32::try_from(i).unwrap_or(u32::MAX));
        if facts.param_rooted(id) {
            if let Some(u) = top.get(i).and_then(|&t| used.get_mut(t)) {
                *u = true;
            }
        }
    }
    // A row with a place that is not in the table: keep the table.
    if outside {
        return;
    }
    let keep: Vec<bool> = top
        .iter()
        .map(|&t| used.get(t).copied().unwrap_or(true))
        .collect();
    if keep.iter().all(|&k| k) {
        return;
    }
    let mut new_id: Vec<Option<PlaceId>> = vec![None; n];
    let mut next = 0u32;
    for (i, k) in keep.iter().enumerate() {
        if *k {
            if let Some(x) = new_id.get_mut(i) {
                *x = Some(PlaceId(next));
            }
            next += 1;
        }
    }
    let map = |q: PlaceId| new_id.get(q.index()).copied().flatten();
    // A kept place names only places of its own tree, which stays too.
    let places = std::mem::take(&mut facts.places);
    facts.places = places
        .into_iter()
        .zip(&keep)
        .filter(|(_, k)| **k)
        .map(|(mut info, _)| {
            info.parent = info.parent.and_then(map);
            info.wild_base = info.wild_base.and_then(map);
            info.one = info.one.and_then(map);
            info
        })
        .collect();
    let index = std::mem::take(&mut facts.place_index);
    facts.place_index = index
        .into_iter()
        .filter_map(|((parent, step), child)| Some(((map(parent)?, step), map(child)?)))
        .collect();
    named_places(facts, &mut |q| {
        if let Some(x) = map(*q) {
            *q = x;
        }
    });
}

/// The nodes of `facts` with a row of a relation other than `cfg_edge`, or
/// with a site of a diagnostic.
fn busy_nodes(facts: &FnFacts) -> HashSet<NodeId> {
    // Each field, so that a new relation of the facts cannot miss its
    // nodes.
    let FnFacts {
        name: _,
        roots: _,
        places: _,
        vars: _,
        nodes: _,
        tasks: _,
        handlers: _,
        by_value: _,
        arg_order: _,
        effect_names: _,
        hidden_effects: _,
        int_ops: _,
        arg_sites,
        ref_sites,
        caps: _,
        cfg_edge: _,
        points_into: _,
        mutates_at,
        reads_at,
        performs_at,
        footprint: _,
        rebound_at,
        uses,
        moved_at,
        scope_end,
        overwrites,
        unset_at,
        empty_at,
        unwound_at,
        owner: _,
        moved_part,
        rest_linear,
        releases_at,
        may_abort,
        multi_at,
        spared_at,
        clause_multi: _,
        body_multi: _,
        resumes_at,
        clause_performs: _,
        has_signature: _,
        declared_mut: _,
        declared_effect: _,
        escapes_at,
        shared_root: _,
        spawned_at,
        joined_at,
        task_reads: _,
        task_writes: _,
        captures: _,
        mut_through: _,
        kept: _,
        spawns_in: _,
        opaque: _,
        call_mut,
        call_arg,
        lends_mut,
        writes_via,
        arg_at,
        param_in,
        uniq_param,
        arg_aliased,
        fn_arg_effect,
        param_effect,
        sim_run_at,
        ref_at,
        ref_in,
        std_effects: _,
        library: _,
        started: _,
        no_runtime: _,
        place_index: _,
    } = facts;
    let mut out: HashSet<NodeId> = HashSet::new();
    out.extend(arg_sites.iter().map(|x| x.node));
    out.extend(ref_sites.iter().map(|x| x.node));
    out.extend(mutates_at.iter().map(|x| x.0));
    out.extend(reads_at.iter().map(|x| x.0));
    out.extend(performs_at.iter().map(|x| x.0));
    for rel in [
        rebound_at,
        uses,
        moved_at,
        scope_end,
        overwrites,
        unset_at,
        empty_at,
        unwound_at,
        rest_linear,
        spared_at,
    ] {
        out.extend(rel.iter().map(|x| x.1));
    }
    out.extend(moved_part.iter().map(|x| x.1));
    out.extend(releases_at.iter().map(|x| x.0));
    out.extend(may_abort.iter().copied());
    out.extend(multi_at.iter().copied());
    out.extend(resumes_at.iter().map(|x| x.0));
    out.extend(escapes_at.iter().map(|x| x.0));
    out.extend(spawned_at.iter().map(|x| x.1));
    out.extend(joined_at.iter().map(|x| x.1));
    out.extend(call_mut.iter().map(|x| x.0));
    out.extend(call_arg.iter().map(|x| x.0));
    out.extend(lends_mut.iter().map(|x| x.0));
    out.extend(writes_via.iter().map(|x| x.0));
    out.extend(arg_at.iter().map(|x| x.0));
    out.extend(param_in.iter().map(|x| x.0));
    out.extend(uniq_param.iter().map(|x| x.0));
    out.extend(arg_aliased.iter().map(|x| x.0));
    out.extend(fn_arg_effect.iter().map(|x| x.0));
    out.extend(param_effect.iter().map(|x| x.0));
    out.extend(sim_run_at.iter().copied());
    out.extend(ref_at.iter().map(|x| x.0));
    out.extend(ref_in.iter().map(|x| x.0));
    out
}

/// Takes each node with no row (see the module documentation) out of the
/// graph of `facts` if it has at most one predecessor or at most one
/// successor, and is not its own successor. The node stays in the node
/// table with no edge. The number of edges does not grow.
fn merge_free_nodes(facts: &mut FnFacts) {
    let mut busy = busy_nodes(facts);
    busy.insert(NodeId(0));
    for (i, n) in facts.nodes.iter().enumerate() {
        if n.label == "handler clause" {
            busy.insert(NodeId(u32::try_from(i).unwrap_or(u32::MAX)));
        }
    }
    let n = facts.nodes.len();
    let mut succ: Vec<BTreeSet<NodeId>> = vec![BTreeSet::new(); n];
    let mut pred: Vec<BTreeSet<NodeId>> = vec![BTreeSet::new(); n];
    for &(a, b) in &facts.cfg_edge {
        if a.index() >= n || b.index() >= n {
            // An edge out of the table: keep the graph as it is.
            return;
        }
        if let (Some(s), Some(p)) = (succ.get_mut(a.index()), pred.get_mut(b.index())) {
            s.insert(b);
            p.insert(a);
        }
    }
    for i in 0..n {
        let x = NodeId(u32::try_from(i).unwrap_or(u32::MAX));
        let (Some(ps), Some(ss)) = (pred.get(i), succ.get(i)) else {
            continue;
        };
        if busy.contains(&x) || ss.contains(&x) || (ps.len() > 1 && ss.len() > 1) {
            continue;
        }
        let ps = std::mem::take(&mut pred[i]);
        let ss = std::mem::take(&mut succ[i]);
        for &p in &ps {
            if let Some(s) = succ.get_mut(p.index()) {
                s.remove(&x);
                s.extend(ss.iter().copied());
            }
        }
        for &q in &ss {
            if let Some(p) = pred.get_mut(q.index()) {
                p.remove(&x);
                p.extend(ps.iter().copied());
            }
        }
    }
    facts.cfg_edge = succ
        .iter()
        .enumerate()
        .flat_map(|(i, s)| {
            let a = NodeId(u32::try_from(i).unwrap_or(u32::MAX));
            s.iter().map(move |&b| (a, b))
        })
        .collect();
}
