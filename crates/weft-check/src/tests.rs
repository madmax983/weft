//! Rule tests on hand-written facts. Each test names the spec rule it covers.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use weft_facts::{
    CapId, FnFacts, HandlerInfo, NodeId, PlaceId, RootKind, Span, Step, StepKind, TaskId, TaskKind,
    VarId, VarInfo, VarKind,
};

use crate::{bridge, Cause, Report};

/// Runs the production checker and asserts that the Datalog spec agrees.
fn check(f: &FnFacts) -> Report {
    let r = crate::check(f);
    let spec = bridge::check_spec(f).expect("spec evaluates");
    assert_eq!(
        r.violations, spec,
        "checker and spec disagree on {}",
        f.name
    );
    r
}

/// A small builder that keeps hand-written facts readable.
struct B {
    f: FnFacts,
    last: Option<NodeId>,
}

impl B {
    fn new() -> Self {
        Self {
            f: FnFacts {
                name: "t".into(),
                ..FnFacts::default()
            },
            last: None,
        }
    }
    fn param(&mut self, name: &str) -> PlaceId {
        self.f.add_root(name, RootKind::Param)
    }
    fn local(&mut self, name: &str) -> PlaceId {
        self.f.add_root(name, RootKind::Local)
    }
    fn field(&mut self, p: PlaceId, id: u32, name: &str) -> PlaceId {
        self.f.child(
            p,
            Step {
                kind: StepKind::Field { id },
                unstable: false,
            },
            &format!(".{name}"),
        )
    }
    fn elem(&mut self, p: PlaceId) -> PlaceId {
        self.f.child(
            p,
            Step {
                kind: StepKind::Elem,
                unstable: true,
            },
            "[]",
        )
    }
    fn seg(&mut self, p: PlaceId, hi: bool) -> PlaceId {
        let text = if hi { "[k..]" } else { "[..k]" };
        self.f.child(
            p,
            Step {
                kind: StepKind::Seg { split: 0, hi },
                unstable: true,
            },
            text,
        )
    }
    fn var(&mut self, name: &str) -> VarId {
        self.f
            .add_var(VarInfo::plain(name, VarKind::Local, Span::default(), "T"))
    }
    fn var_with(&mut self, name: &str, edit: impl FnOnce(&mut VarInfo)) -> VarId {
        let mut v = VarInfo::plain(name, VarKind::Local, Span::default(), "T");
        edit(&mut v);
        self.f.add_var(v)
    }
    /// Adds a node after the last node.
    fn node(&mut self, label: &str) -> NodeId {
        let n = self.f.add_node(Span::default(), label, "");
        if let Some(p) = self.last {
            self.f.cfg_edge.push((p, n));
        }
        self.last = Some(n);
        n
    }
    /// Adds a node with no incoming edge.
    fn start(&mut self, label: &str) -> NodeId {
        self.last = None;
        self.node(label)
    }
    fn edge(&mut self, a: NodeId, b: NodeId) {
        self.f.cfg_edge.push((a, b));
    }
    fn bind(&mut self, v: VarId, n: NodeId) {
        self.f.rebound_at.push((v, n));
    }
    fn use_(&mut self, v: VarId, n: NodeId) {
        self.f.uses.push((v, n));
    }
    fn mv(&mut self, v: VarId, n: NodeId) {
        self.f.uses.push((v, n));
        self.f.moved_at.push((v, n));
    }
}

/// The `bad` function of the design doc, as facts.
fn bad_facts() -> (B, VarId, NodeId) {
    let mut b = B::new();
    let world = b.param("world");
    let ents = b.field(world, 0, "entities");
    let elem = b.elem(ents);
    let first = b.var("first");
    let n0 = b.node("let first");
    b.bind(first, n0);
    b.f.points_into.push((first, elem));
    let n1 = b.node("push");
    b.f.mutates_at.push((n1, ents));
    let n2 = b.node("print");
    b.use_(first, n2);
    b.f.has_signature = true;
    b.f.declared_mut.push(ents);
    (b, first, n2)
}

#[test]
fn w0301_doc_bad_example_is_rejected() {
    let (b, first, n2) = bad_facts();
    let r = check(&b.f);
    assert_eq!(
        r.violations.error.iter().copied().collect::<Vec<_>>(),
        vec![(first, n2)]
    );
    assert_eq!(r.invalidations.len(), 1);
    assert_eq!(r.invalidations[0].at, NodeId(1));
    assert!(r.violations.unauthorized_mut.is_empty());
}

#[test]
fn w0301_element_mutation_keeps_element_refs() {
    let mut b = B::new();
    let world = b.param("world");
    let ents = b.field(world, 0, "entities");
    let elem = b.elem(ents);
    let score = b.field(world, 2, "score");
    let e = b.var("e");
    let n0 = b.node("for e");
    b.bind(e, n0);
    b.f.points_into.push((e, elem));
    let n1 = b.node("step");
    b.f.mutates_at.push((n1, elem));
    let n2 = b.node("score += 10");
    b.f.mutates_at.push((n2, score));
    let n3 = b.node("e.hp");
    b.use_(e, n3);
    assert!(check(&b.f).violations.is_clean());
}

/// `let v = ..; let r = &v.items; DROP(v); use r`, where DROP is a move or a scope end.
fn drop_facts(scope_end: bool) -> (B, VarId, VarId, NodeId, NodeId) {
    let mut b = B::new();
    let v_root = b.local("v");
    let items = b.field(v_root, 0, "items");
    let v = b.var("v");
    b.f.owner.push((v_root, v));
    let r = b.var("r");
    let n0 = b.node("let r");
    b.bind(r, n0);
    b.f.points_into.push((r, items));
    let n1 = b.node("drop v");
    if scope_end {
        b.f.scope_end.push((v, n1));
    } else {
        b.mv(v, n1);
    }
    let n2 = b.node("print(r)");
    b.use_(r, n2);
    (b, v, r, n1, n2)
}

#[test]
fn w0301_a_move_of_the_owner_invalidates_stable_parts() {
    // frees_at(P, Rt) :- owner(Rt, V), moved_at(V, P), !part_moved_at(V, P).
    // invalidated_at(R, P) :- points_into(R, Path), frees_at(P, M), prefix(M, Path).
    let (b, v, r, n1, n2) = drop_facts(false);
    let rep = check(&b.f);
    assert!(rep.violations.error.contains(&(r, n2)));
    assert_eq!(rep.invalidations[0].at, n1);
    assert_eq!(rep.invalidations[0].cause, Cause::Move(v));
}

#[test]
fn w0301_the_scope_end_of_the_owner_invalidates() {
    // frees_at(P, Rt) :- owner(Rt, V), scope_end(V, P).
    let (mut b, v, r, n1, n2) = drop_facts(true);
    let rep = check(&b.f);
    assert!(rep.violations.error.contains(&(r, n2)));
    assert_eq!(rep.invalidations[0].cause, Cause::ScopeEnd(v));
    // A reference into another root survives, and a rebind revives the reference.
    b.f.owner.clear();
    assert!(check(&b.f).violations.error.is_empty());
    let (mut b, _, r, _, n2) = drop_facts(true);
    let n3 = b.f.add_node(Span::default(), "r = &..", "");
    b.f.cfg_edge.retain(|&(p, q)| !(p == n1 && q == n2));
    b.edge(n1, n3);
    b.edge(n3, n2);
    b.bind(r, n3);
    assert!(check(&b.f).violations.error.is_empty());
}

#[test]
fn w0301_rebinding_revives_the_reference() {
    let (mut b, first, n2) = bad_facts();
    // Insert a rebind between the push and the use: n1 -> n3 -> n2.
    b.f.cfg_edge.retain(|&(p, q)| !(p == NodeId(1) && q == n2));
    let n3 = b.f.add_node(Span::default(), "first = &..", "");
    b.edge(NodeId(1), n3);
    b.edge(n3, n2);
    b.bind(first, n3);
    assert!(check(&b.f).violations.error.is_empty());
}

#[test]
fn w0301_invalid_on_one_branch_is_an_error_at_the_join() {
    let mut b = B::new();
    let v = b.local("v");
    let elem = b.elem(v);
    let r = b.var("r");
    let n0 = b.node("let r");
    b.bind(r, n0);
    b.f.points_into.push((r, elem));
    let then_ = b.node("push");
    b.f.mutates_at.push((then_, v));
    let join = b.node("use r");
    let else_ = b.f.add_node(Span::default(), "else", "");
    b.edge(n0, else_);
    b.edge(else_, join);
    b.use_(r, join);
    let out = check(&b.f);
    assert!(out.violations.error.contains(&(r, join)));
    // A local root needs no declaration.
    assert!(out.violations.unauthorized_mut.is_empty());
}

#[test]
fn w0301_perform_uses_the_handler_footprint() {
    let mut b = B::new();
    let lines = b.local("lines");
    let elem = b.elem(lines);
    let r = b.var("r");
    let n0 = b.node("let r");
    b.bind(r, n0);
    b.f.points_into.push((r, elem));
    let n1 = b.node("log");
    let cap = b.f.add_cap();
    b.f.performs_at.push((n1, cap));
    b.f.footprint.push((cap, lines));
    let n2 = b.node("print r");
    b.use_(r, n2);
    assert!(check(&b.f).violations.error.contains(&(r, n2)));
    // Without the footprint fact nothing is invalidated.
    b.f.footprint.clear();
    assert!(check(&b.f).violations.error.is_empty());
    let _ = CapId(0);
}

#[test]
fn w0302_use_after_move_and_reassignment() {
    let mut b = B::new();
    let x = b.var("x");
    let n0 = b.node("let x");
    b.bind(x, n0);
    let n1 = b.node("consume(x)");
    b.mv(x, n1);
    let n2 = b.node("use x");
    b.use_(x, n2);
    let n3 = b.node("x = new");
    b.bind(x, n3);
    let n4 = b.node("use x");
    b.use_(x, n4);
    let v = check(&b.f).violations;
    assert!(v.use_after_move.contains(&(x, n2)));
    assert!(!v.use_after_move.contains(&(x, n4)));
}

#[test]
fn w0501_once_continuation_resumed_twice() {
    let mut b = B::new();
    let k = b.var_with("resume", |v| {
        v.kind = VarKind::Continuation;
        v.once = true;
    });
    let n0 = b.start("clause");
    b.bind(k, n0);
    let n1 = b.node("resume");
    b.mv(k, n1);
    let n2 = b.node("resume");
    b.mv(k, n2);
    assert!(check(&b.f).violations.use_after_move.contains(&(k, n2)));
}

#[test]
fn w0604_immovable_value_cannot_move() {
    let mut b = B::new();
    let fr = b.var_with("frame", |v| v.immovable = true);
    let n0 = b.node("let frame");
    b.bind(fr, n0);
    let n1 = b.node("give(frame)");
    b.mv(fr, n1);
    assert!(check(&b.f).violations.moved_immovable.contains(&(fr, n1)));
}

fn linear_facts(consume: bool, on_abort: bool, abort_node: bool) -> (B, VarId) {
    let mut b = B::new();
    let tx = b.var_with("tx", |v| {
        v.linear = true;
        v.once = true;
        v.has_on_abort = on_abort;
    });
    let n0 = b.node("let tx");
    b.bind(tx, n0);
    let n1 = b.node("tx.debit");
    b.use_(tx, n1);
    if abort_node {
        b.f.may_abort.push(n1);
    }
    if consume {
        let n2 = b.node("tx.commit");
        b.mv(tx, n2);
    }
    let end = b.node("}");
    b.f.scope_end.push((tx, end));
    (b, tx)
}

#[test]
fn w0601_linear_value_must_be_consumed() {
    let (b, tx) = linear_facts(false, true, false);
    let v = check(&b.f).violations;
    assert_eq!(v.unconsumed.len(), 1);
    assert!(v.unconsumed.iter().all(|&(x, _)| x == tx));
    let (b, _) = linear_facts(true, true, false);
    assert!(check(&b.f).violations.is_clean());
}

#[test]
fn w0601_overwriting_a_live_linear_value() {
    let mut b = B::new();
    let tx = b.var_with("tx", |v| v.linear = true);
    let n0 = b.node("let tx");
    b.bind(tx, n0);
    let n1 = b.node("tx = other");
    b.bind(tx, n1);
    let n2 = b.node("commit");
    b.mv(tx, n2);
    assert!(check(&b.f).violations.overwritten.contains(&(tx, n1)));
}

#[test]
fn w0602_abort_needs_on_abort() {
    let (b, tx) = linear_facts(true, false, true);
    assert!(check(&b.f)
        .violations
        .abort_unhandled
        .contains(&(tx, NodeId(1))));
    let (b, _) = linear_facts(true, true, true);
    assert!(check(&b.f).violations.is_clean());
}

#[test]
fn w0503_linear_value_live_across_multi() {
    let mut b = B::new();
    let tx = b.var_with("tx", |v| {
        v.linear = true;
        v.once = true;
        v.has_on_abort = true;
    });
    let n0 = b.node("let tx");
    b.bind(tx, n0);
    let n1 = b.node("choose()");
    b.f.multi_at.push(n1);
    let n2 = b.node("commit");
    b.mv(tx, n2);
    assert!(check(&b.f).violations.live_across_multi.contains(&(tx, n1)));
    // A `many` value is fine.
    b.f.vars[tx.index()].once = false;
    b.f.vars[tx.index()].linear = false;
    assert!(check(&b.f).violations.live_across_multi.is_empty());
}

#[test]
fn w0703_mutation_must_be_covered_by_the_signature() {
    let mut b = B::new();
    let world = b.param("world");
    let ents = b.field(world, 0, "entities");
    let elem = b.elem(ents);
    let events = b.field(world, 1, "events");
    let n0 = b.node("step");
    b.f.mutates_at.push((n0, elem));
    let n1 = b.node("push");
    b.f.mutates_at.push((n1, events));
    b.f.has_signature = true;
    b.f.declared_mut.push(elem);
    let v = check(&b.f).violations;
    assert!(v.unauthorized_mut.contains(&(n1, events)));
    assert!(!v.unauthorized_mut.contains(&(n0, elem)));
    // `mut(world)` covers everything inside `world`.
    b.f.declared_mut.push(world);
    assert!(check(&b.f).violations.unauthorized_mut.is_empty());
    // No signature: the effect is inferred, nothing to check.
    b.f.declared_mut.clear();
    b.f.has_signature = false;
    assert!(check(&b.f).violations.unauthorized_mut.is_empty());
}

#[test]
fn w0702_effect_must_be_in_the_signature() {
    let mut b = B::new();
    let n0 = b.node("log");
    b.f.escapes_at.push((n0, "Log".into()));
    b.f.has_signature = true;
    assert!(check(&b.f)
        .violations
        .unauthorized_effect
        .contains(&(n0, "Log".into())));
    b.f.declared_effect.push("Log".into());
    assert!(check(&b.f).violations.is_clean());
}

#[test]
fn w0402_no_mutation_through_shared() {
    let mut b = B::new();
    let world = b.param("world");
    let score = b.field(world, 2, "score");
    b.f.shared_root.push(world);
    let n0 = b.node("score += 1");
    b.f.mutates_at.push((n0, score));
    assert!(check(&b.f)
        .violations
        .shared_mutation
        .contains(&(n0, score)));
}

#[test]
fn w0312_overlapping_arguments_to_a_mutating_callee() {
    let mut b = B::new();
    let v = b.local("v");
    let elem = b.elem(v);
    let n0 = b.node("f(v, &v[0])");
    b.f.call_mut.push((n0, v, 0));
    b.f.call_arg.push((n0, v, 0));
    b.f.call_arg.push((n0, elem, 1));
    let out = check(&b.f).violations;
    assert!(out.alias_conflict.contains(&(n0, v, elem)));
    assert!(!out.alias_conflict.contains(&(n0, v, v)));
}

/// The `ingest` example of the design doc: three spawns in one scope.
fn ingest_facts(third_reads_stats: bool) -> (B, TaskId, NodeId) {
    let mut b = B::new();
    let batch = b.param("batch");
    let stats = b.param("stats");
    let count = b.field(stats, 0, "count");
    let t1 = b.f.add_task(TaskKind::Spawn, Span::default());
    let t2 = b.f.add_task(TaskKind::Spawn, Span::default());
    let t3 = b.f.add_task(TaskKind::Spawn, Span::default());
    let s1 = b.node("spawn 1");
    b.f.spawned_at.push((t1, s1));
    b.f.task_writes.push((t1, count));
    b.f.mutates_at.push((s1, count));
    b.f.task_reads.push((t1, batch));
    b.f.reads_at.push((s1, batch));
    let s2 = b.node("spawn 2");
    b.f.spawned_at.push((t2, s2));
    b.f.task_reads.push((t2, batch));
    b.f.reads_at.push((s2, batch));
    let s3 = b.node("spawn 3");
    b.f.spawned_at.push((t3, s3));
    let read = if third_reads_stats { count } else { batch };
    b.f.task_reads.push((t3, read));
    b.f.reads_at.push((s3, read));
    let end = b.node("scope end");
    for t in [t1, t2, t3] {
        b.f.joined_at.push((t, end));
    }
    (b, t1, s3)
}

#[test]
fn w0405_doc_ingest_example_is_rejected() {
    let (b, t1, s3) = ingest_facts(true);
    let r = check(&b.f);
    assert_eq!(
        r.violations
            .task_conflict
            .iter()
            .copied()
            .collect::<Vec<_>>(),
        vec![(t1, s3)]
    );
    assert!(r.conflicts[0].task_writes);
    let (b, _, _) = ingest_facts(false);
    assert!(check(&b.f).violations.task_conflict.is_empty());
}

#[test]
fn w0405_join_ends_the_task() {
    let mut b = B::new();
    let s = b.local("stats");
    let t = b.f.add_task(TaskKind::Spawn, Span::default());
    let n0 = b.node("spawn");
    b.f.spawned_at.push((t, n0));
    b.f.task_writes.push((t, s));
    let n1 = b.node("join");
    b.f.joined_at.push((t, n1));
    let n2 = b.node("read stats");
    b.f.reads_at.push((n2, s));
    assert!(check(&b.f).violations.task_conflict.is_empty());
}

#[test]
fn w0301_a_partial_move_frees_the_part_only() {
    // frees_at(P, M) :- moved_part(M, P).
    let mut b = B::new();
    let p_root = b.local("p");
    let a = b.field(p_root, 0, "a");
    let other = b.field(p_root, 1, "b");
    let p = b.var("p");
    b.f.owner.push((p_root, p));
    let r = b.var("r");
    let q = b.var("q");
    let n0 = b.node("let r, q");
    b.bind(r, n0);
    b.bind(q, n0);
    b.f.points_into.push((r, a));
    b.f.points_into.push((q, other));
    let n1 = b.node("take(p.a)");
    b.mv(p, n1);
    b.f.moved_part.push((a, n1));
    let n2 = b.node("print(r, q)");
    b.use_(r, n2);
    b.use_(q, n2);
    let rep = check(&b.f);
    assert!(rep.violations.error.contains(&(r, n2)));
    assert!(!rep.violations.error.contains(&(q, n2)));
    assert_eq!(rep.invalidations[0].cause, Cause::MovePart(a));
}

#[test]
fn w0405_a_free_conflicts_with_a_task() {
    // task_conflict(T, P) :- active(T, P), task_accesses(T, A), frees_at(P, M), overlaps(M, A).
    let mut b = B::new();
    let v_root = b.local("v");
    let elem = b.elem(v_root);
    let v = b.var("v");
    b.f.owner.push((v_root, v));
    let t = b.f.add_task(TaskKind::Spawn, Span::default());
    let n0 = b.node("spawn");
    b.f.spawned_at.push((t, n0));
    b.f.task_reads.push((t, elem));
    let n1 = b.node("take(v)");
    b.mv(v, n1);
    let rep = check(&b.f);
    assert!(rep.violations.task_conflict.contains(&(t, n1)));
    assert_eq!(rep.conflicts[0].free, Some(Cause::Move(v)));
    // A free after the join is not a conflict.
    b.f.moved_at.clear();
    let n2 = b.node("join");
    b.f.joined_at.push((t, n2));
    let n3 = b.node("end of v");
    b.f.scope_end.push((v, n3));
    assert!(check(&b.f).violations.task_conflict.is_empty());
}

#[test]
fn w0405_a_reference_is_not_an_access_by_itself() {
    // A use of a holder is an access only through the reads that sema records.
    let mut b = B::new();
    let stats = b.param("stats");
    let count = b.field(stats, 0, "count");
    let name = b.field(stats, 1, "name");
    let r = b.var("r");
    b.f.points_into.push((r, stats));
    let t = b.f.add_task(TaskKind::Spawn, Span::default());
    b.f.captures.push((t, r));
    let n0 = b.node("spawn");
    b.f.spawned_at.push((t, n0));
    b.f.task_writes.push((t, count));
    let n1 = b.node("print(stats.name)");
    b.use_(r, n1);
    b.f.reads_at.push((n1, name));
    assert!(check(&b.f).violations.task_conflict.is_empty());
    b.f.reads_at.push((n1, count));
    assert!(check(&b.f).violations.task_conflict.contains(&(t, n1)));
}

#[test]
fn w0405_split_halves_are_disjoint() {
    let mut b = B::new();
    let world = b.param("world");
    let ents = b.field(world, 0, "entities");
    let lo = b.seg(ents, false);
    let hi = b.seg(ents, true);
    let t1 = b.f.add_task(TaskKind::Fork, Span::default());
    let t2 = b.f.add_task(TaskKind::Fork, Span::default());
    let a = b.node("fork 1");
    b.f.spawned_at.push((t1, a));
    b.f.task_writes.push((t1, lo));
    b.f.mutates_at.push((a, lo));
    let c = b.node("fork 2");
    b.f.spawned_at.push((t2, c));
    b.f.task_writes.push((t2, hi));
    b.f.mutates_at.push((c, hi));
    let j = b.node("join");
    b.f.joined_at.push((t1, j));
    b.f.joined_at.push((t2, j));
    assert!(check(&b.f).violations.task_conflict.is_empty());
    // Two writes to the whole element set conflict.
    let elem = b.elem(ents);
    b.f.task_writes.push((t2, elem));
    b.f.mutates_at.push((c, elem));
    assert!(!check(&b.f).violations.task_conflict.is_empty());
}

#[test]
fn w0401_w0403_fork_captures_and_stealable() {
    let mut b = B::new();
    let rc = b.var_with("node", |v| v.nonportable = true);
    let l = b.var_with("l", |v| v.uniq = true);
    let w = b.var("world");
    let tf = b.f.add_task(TaskKind::Fork, Span::default());
    let ts = b.f.add_task(TaskKind::Spawn, Span::default());
    let tp = b.f.add_task(TaskKind::Spawn, Span::default());
    b.f.captures.push((tf, rc));
    b.f.captures.push((tf, w));
    b.f.mut_through.push((tf, w));
    b.f.captures.push((tf, l));
    b.f.mut_through.push((tf, l));
    b.f.captures.push((ts, l));
    b.f.mut_through.push((ts, l));
    b.f.captures.push((tp, w));
    b.f.mut_through.push((tp, w));
    let v = check(&b.f).violations;
    assert!(v.nonportable_capture.contains(&(tf, rc)));
    assert!(v.shared_mut_capture.contains(&(tf, w)));
    assert!(!v.shared_mut_capture.contains(&(tf, l)));
    // A spawned task that mutates through an aliased reference is pinned, not rejected.
    assert!(v.stealable.contains(&ts));
    assert!(!v.stealable.contains(&tp));
    assert!(!v.stealable.contains(&tf));
}

#[test]
fn w0801_root_handler_in_library() {
    let mut b = B::new();
    b.f.library = true;
    b.f.handlers.push(HandlerInfo {
        effect: "Net".into(),
        is_std: true,
        forwards: false,
        span: Span::default(),
    });
    b.f.handlers.push(HandlerInfo {
        effect: "Net".into(),
        is_std: true,
        forwards: true,
        span: Span::default(),
    });
    b.f.handlers.push(HandlerInfo {
        effect: "Log".into(),
        is_std: false,
        forwards: false,
        span: Span::default(),
    });
    let v = check(&b.f).violations;
    assert_eq!(v.root_handler_in_lib.len(), 1);
    b.f.library = false;
    assert!(check(&b.f).violations.root_handler_in_lib.is_empty());
}

#[test]
fn w0301_a_wildcard_reference_is_invalid_after_an_overlapping_change() {
    // invalidated_at(R, P) :- points_into(R, Path), wild_at(Path, B), mutates_at(P, M), overlaps(M, B).
    let mut b = B::new();
    let world = b.param("world");
    let ents = b.field(world, 0, "entities");
    let score = b.field(world, 1, "score");
    let other = b.param("other");
    let any = b.f.wildcard(world);
    let r = b.var("r");
    let n0 = b.node("let r = f(world)");
    b.bind(r, n0);
    b.f.points_into.push((r, any));
    let n1 = b.node("other.clear()");
    b.f.mutates_at.push((n1, other));
    let n2 = b.node("world.entities.clear()");
    b.f.mutates_at.push((n2, ents));
    let n3 = b.node("print(r)");
    b.use_(r, n3);
    let rep = check(&b.f);
    assert!(rep.violations.error.contains(&(r, n3)));
    assert_eq!(rep.invalidations[0].at, n2);
    // overlaps(P, Q) :- wild_at(P, B), overlaps(B, Q): a wildcard place overlaps
    // every place inside its base, and nothing else.
    let n4 = b.node("call");
    b.f.call_mut.push((n4, score, 0));
    b.f.call_mut.push((n4, other, 0));
    b.f.call_arg.push((n4, any, 1));
    let rep = check(&b.f);
    assert!(rep.violations.alias_conflict.contains(&(n4, score, any)));
    assert!(!rep.violations.alias_conflict.contains(&(n4, other, any)));
}

#[test]
fn w0301_a_wildcard_mutation_invalidates_every_reference_below_its_base() {
    // invalidated_at(R, P) :- points_into(R, Path), mutates_at(P, M), wild_at(M, B), prefix(B, Path).
    let mut b = B::new();
    let world = b.param("world");
    let score = b.field(world, 1, "score");
    let any = b.f.wildcard(world);
    let r = b.var("r");
    let n0 = b.node("let r = &world.score");
    b.bind(r, n0);
    b.f.points_into.push((r, score));
    let n1 = b.node("e.hp += 1");
    let hp = b.field(any, 0, "hp");
    b.f.mutates_at.push((n1, hp));
    let n2 = b.node("print(r)");
    b.use_(r, n2);
    assert!(check(&b.f).violations.error.contains(&(r, n2)));
}

#[test]
fn w0301_a_wildcard_change_spares_a_reference_to_its_base() {
    // invalidated_at(R, P) :- points_into(R, Path), mutates_at(P, M), wild_at(M, B),
    //                         strict_prefix(B, Path), !same_one(M, Path).
    let mut b = B::new();
    let boxes = b.param("boxes");
    let any = b.f.wildcard(boxes);
    let items = b.field(any, 0, "items");
    let r = b.var("boxes");
    let n0 = b.node("entry");
    b.bind(r, n0);
    b.f.points_into.push((r, boxes));
    let s = b.var("s");
    b.bind(s, n0);
    let inner = b.elem(boxes);
    b.f.points_into.push((s, inner));
    let n1 = b.node("b.items.push(1)");
    b.f.mutates_at.push((n1, items));
    let n2 = b.node("print(boxes.len())");
    b.use_(r, n2);
    b.use_(s, n2);
    let v = check(&b.f).violations;
    assert!(!v.error.contains(&(r, n2)), "{v:?}");
    assert!(v.error.contains(&(s, n2)), "{v:?}");
}

#[test]
fn w0301_a_change_inside_one_call_result_follows_rule_3() {
    // same_one(M, P): a change and a reference inside one one-place wildcard
    // place compare by their steps. Another instance uses the wildcard rules.
    let mut b = B::new();
    let v = b.param("v");
    let e = b.f.wildcard_one(v, 1);
    let other = b.f.wildcard_one(v, 2);
    let hp = b.field(e, 0, "hp");
    let kids = b.field(e, 1, "kids");
    let kid = b.elem(kids);
    let r = b.var("e");
    let n0 = b.node("let e = find(v)");
    b.bind(r, n0);
    b.f.points_into.push((r, e));
    let k = b.var("k");
    let n1 = b.node("let k = &e.kids[0]");
    b.bind(k, n1);
    b.f.points_into.push((k, kid));
    let o = b.var("o");
    b.bind(o, n1);
    b.f.points_into.push((o, other));
    let n2 = b.node("e.hp -= 1");
    b.f.mutates_at.push((n2, hp));
    let n3 = b.node("print(e.hp, o.hp)");
    b.use_(r, n3);
    b.use_(o, n3);
    let v1 = check(&b.f).violations;
    assert!(!v1.error.contains(&(r, n3)), "{v1:?}");
    assert!(v1.error.contains(&(o, n3)), "{v1:?}");
    let n4 = b.node("e.kids.push(x)");
    b.f.mutates_at.push((n4, kids));
    let n5 = b.node("print(k.hp)");
    b.use_(k, n5);
    b.use_(r, n5);
    let v2 = check(&b.f).violations;
    assert!(v2.error.contains(&(k, n5)), "{v2:?}");
    assert!(!v2.error.contains(&(r, n5)), "{v2:?}");
}

#[test]
fn nested_wildcard_places_agree_with_the_spec() {
    // wild_at(P, B) for each wildcard step on the path of P. The checker uses
    // the outermost base only. Facts can still name nested wildcard places,
    // because `child` makes them, so the spec must agree on them.
    let mut b = B::new();
    let world = b.param("world");
    let ents = b.field(world, 0, "entities");
    let score = b.field(world, 1, "score");
    let other = b.param("other");
    let mut deep = b.f.wildcard(ents);
    for i in 0..12 {
        let x = b.field(deep, i % 2, "x");
        deep = b.f.child(x, weft_facts::WILD, "..");
    }
    assert_eq!(b.f.wildcard(deep), b.f.wildcard(ents), "the normal form");
    let r = b.var("r");
    let n0 = b.node("let r = f(world.entities)");
    b.bind(r, n0);
    b.f.points_into.push((r, deep));
    let n1 = b.node("world.score += 1");
    b.f.mutates_at.push((n1, score));
    let n2 = b.node("other.clear()");
    b.f.mutates_at.push((n2, other));
    let n3 = b.node("print(r)");
    b.use_(r, n3);
    let (rep, work) = crate::check_counted(&b.f);
    assert!(rep.violations.error.is_empty(), "{rep:?}");
    assert!(work.overlaps < 10, "{work:?}");
    check(&b.f);
    let n4 = b.node("world.entities.clear()");
    b.f.mutates_at.push((n4, ents));
    let n5 = b.node("print(r)");
    b.use_(r, n5);
    let rep = check(&b.f);
    assert!(rep.violations.error.contains(&(r, n5)));
    // A mutation of a nested wildcard place: every reference below its
    // outermost base.
    let s = b.var("s");
    let n6 = b.node("let s = &world.entities[0]");
    b.bind(s, n6);
    let el = b.elem(ents);
    b.f.points_into.push((s, el));
    let n7 = b.node("g(deep)");
    b.f.mutates_at.push((n7, deep));
    let n8 = b.node("print(s)");
    b.use_(s, n8);
    assert!(check(&b.f).violations.error.contains(&(s, n8)));
}

/// Returns the rendered diagnostics of a source.
fn rendered(src: &str) -> String {
    let checked = crate::check_source("t.wf", src, weft_sema::Options::default());
    let file = weft_syntax::SourceFile::new("t.wf", src);
    checked.diags.iter().map(|d| d.render(&file)).collect()
}

#[test]
fn w0301_says_why_the_owner_is_gone() {
    let out = rendered(
        "fn f() {
             let keep: Vec<u64> = Vec.new()
             let q = &keep
             let g = || { let v: Vec<u64> = Vec.new(); q = &v; 0 }
             let z = g()
             print(q)
         }
         struct C { items: Vec<u64> }
         fn h() {
             let a = Rc.new(C { items: Vec.new() })
             let r = &a.items
             a = Rc.new(C { items: Vec.new() })
             print(r)
         }",
    );
    assert!(
        out.contains("v : goes out of scope when `g` returns"),
        "{out}"
    );
    assert!(
        out.contains("r : &Vec<u64> through the `Rc` handle a"),
        "{out}"
    );
    assert!(out.contains("a : new value"), "{out}");
}

#[test]
fn an_ill_typed_return_gets_no_place_error() {
    let out =
        rendered("fn f() -> u64 { let v: Vec<u64> = Vec.new(); v.push(1); let r = &v[0]; r }");
    assert!(out.contains("W0102"), "{out}");
    assert!(!out.contains("W0204"), "{out}");
}

#[test]
fn inferred_places_keep_their_names() {
    let out = rendered(
        "struct Stats { count: u64, hist: Vec<u64> }
         struct Cell { v: Vec<u64> }
         fn priv_bump(s: &Stats) { s.count += 1 }
         fn shared_caller(s: &Stats @ shared) { priv_bump(s) }
         fn grow(c: &Cell) { c.v.push(1) }
         pub fn pub_grow(c: &Cell) { grow(c) }",
    );
    assert!(
        out.contains("`priv_bump` mutates `s.count` through a `@ shared` reference"),
        "{out}"
    );
    assert!(
        out.contains("must state its effects: `/ mut(c.v)`"),
        "{out}"
    );
}

#[test]
fn w0301_w0405_a_lent_place_can_change() {
    // `let first = &w.entities[0]; f(w); print(first)` with `f` a function parameter.
    let mut b = B::new();
    let w = b.param("w");
    let ents = b.field(w, 0, "entities");
    let elem = b.elem(ents);
    let first = b.var("first");
    let n0 = b.node("let first");
    b.bind(first, n0);
    b.f.points_into.push((first, elem));
    let n1 = b.node("f");
    b.f.lends_mut.push((n1, w));
    let n2 = b.node("print");
    b.use_(first, n2);
    // The signature does not state the mutation: the caller of `f` sees it.
    b.f.has_signature = true;
    let r = check(&b.f);
    assert!(r.violations.error.contains(&(first, n2)));
    assert_eq!(r.invalidations[0].cause, Cause::Lend(w));
    assert!(r.violations.unauthorized_mut.is_empty());
    assert!(r.violations.shared_mutation.is_empty());
    // A reference into the lent place itself survives.
    b.f.points_into.clear();
    b.f.points_into.push((first, w));
    assert!(check(&b.f).violations.error.is_empty());

    // A task that reads `w.entities` while the parent lends `w`.
    let mut b = B::new();
    let w = b.param("w");
    let ents = b.field(w, 0, "entities");
    let t = b.f.add_task(TaskKind::Spawn, Span::default());
    let s = b.node("spawn");
    b.f.spawned_at.push((t, s));
    b.f.task_reads.push((t, ents));
    let n1 = b.node("f");
    b.f.lends_mut.push((n1, w));
    let end = b.node("scope end");
    b.f.joined_at.push((t, end));
    let r = check(&b.f);
    assert!(r.violations.task_conflict.contains(&(t, n1)));
    assert!(r.conflicts[0].lends);
}

#[test]
fn w0312_a_lent_place_pairs_with_the_other_arguments() {
    // `f(w, &w.entities[0])` with `f` a function parameter: both places are lent.
    let mut b = B::new();
    let w = b.param("w");
    let ents = b.field(w, 0, "entities");
    let elem = b.elem(ents);
    let n = b.node("f");
    b.f.lends_mut.push((n, w));
    b.f.lends_mut.push((n, elem));
    b.f.call_mut.push((n, w, 0));
    b.f.call_mut.push((n, elem, 1));
    b.f.call_arg.push((n, w, 0));
    b.f.call_arg.push((n, elem, 1));
    let r = check(&b.f);
    // Each place pairs with the other one.
    assert!(r.violations.alias_conflict.contains(&(n, w, elem)));
    assert!(r.violations.alias_conflict.contains(&(n, elem, w)));
    // The diagnostics show one error for the call, with the outer place mutated.
    let ds = crate::diagnose::diagnose(&b.f, &r);
    let w0312: Vec<_> = ds.iter().filter(|d| d.code == "W0312").collect();
    assert_eq!(w0312.len(), 1);
    assert!(
        w0312[0].message.contains("mutates `w` while"),
        "{}",
        w0312[0].message
    );
}

/// The pairwise step facts are the pairs of one class: a wide struct gives
/// one `step_alias` and one `step_within` fact per field, quickly.
#[test]
fn step_facts_of_a_wide_struct_are_linear() {
    let mut b = B::new();
    let s = b.param("s");
    let n = 3200;
    for i in 0..n {
        b.field(s, i, &format!("f{i}"));
    }
    let v = b.local("v");
    let elem = b.elem(v);
    let lo = b.seg(v, false);
    let hi = b.seg(v, true);
    let start = std::time::Instant::now();
    let mut alias = Vec::new();
    let mut within = Vec::new();
    bridge::each_fact(&b.f, &mut |rel, args| {
        let pair = || format!("{args:?}");
        match rel {
            "step_alias" => alias.push(pair()),
            "step_within" => within.push(pair()),
            _ => {}
        }
    });
    let time = start.elapsed();
    let sym = |p: PlaceId| bridge::Arg::Sym(p.to_string());
    let field0 = PlaceId(1);
    assert!(alias.contains(&format!("{:?}", [sym(field0), sym(field0)])));
    // The three element places: each pair aliases, except the two sides.
    let n = n as usize;
    assert_eq!(alias.len(), n + 7, "{:?}", &alias[n..]);
    assert!(!alias.contains(&format!("{:?}", [sym(lo), sym(hi)])));
    assert!(within.contains(&format!("{:?}", [sym(lo), sym(elem)])));
    assert!(!within.contains(&format!("{:?}", [sym(elem), sym(lo)])));
    assert_eq!(within.len(), n + 5, "{:?}", &within[n..]);
    assert!(time.as_millis() < 500, "{time:?}");
}

#[test]
fn the_spec_parses() {
    let p = weft_datalog::parse_program_named("spec/weft.dl", bridge::SPEC_SRC);
    assert!(p.is_ok(), "{p:?}");
    assert_eq!(p.ok().as_ref(), Some(bridge::spec()));
    assert!(!bridge::spec().rules().is_empty());
}

/// A violation fact with a value that is not an id is an error, so that it
/// cannot hide a disagreement.
#[test]
fn a_violation_that_does_not_parse_is_an_error() {
    let p = weft_datalog::parse_program_named("t.dl", "error(x, n1).\nstealable(t2).")
        .expect("the program parses");
    let options = weft_datalog::EvalOptions { provenance: false };
    let out = weft_datalog::evaluate(&p, weft_datalog::Database::new(), options)
        .expect("the program evaluates");
    assert_eq!(
        bridge::violations(&out),
        Err(bridge::SpecError::BadTuple("error(x, n1)".into()))
    );
    let p = weft_datalog::parse_program_named("t.dl", "error(v0, n1).\nstealable(t2).")
        .expect("the program parses");
    let out = weft_datalog::evaluate(&p, weft_datalog::Database::new(), options)
        .expect("the program evaluates");
    let v = bridge::violations(&out).expect("the facts parse");
    assert!(v.error.contains(&(VarId(0), NodeId(1))));
    assert!(v.stealable.contains(&TaskId(2)));
}

proptest::proptest! {
    /// The search for W0301 evidence finds, for each target, the first gen
    /// that reaches it alone in the verified propagation.
    #[test]
    fn first_reaching_is_the_first_gen_that_reaches_alone(
        n in 1usize..12,
        edges in proptest::collection::vec((0usize..12, 0usize..12), 0..30),
        gens in proptest::collection::vec(0usize..12, 0..6),
        kills in proptest::collection::vec(proptest::bool::ANY, 12),
        targets in proptest::collection::vec(0usize..12, 0..6),
    ) {
        let mut succ = vec![Vec::new(); n];
        let mut pred = vec![Vec::new(); n];
        for (a, b) in edges {
            succ[a % n].push(b % n);
            pred[b % n].push(a % n);
        }
        let gens: Vec<usize> = gens.into_iter().map(|g| g % n).collect();
        let targets: Vec<usize> = targets.into_iter().map(|t| t % n).collect();
        let kill = kills[..n].to_vec();
        let first = crate::rules::first_reaching(&succ, &pred, &gens, &kill, &targets);
        for &t in &targets {
            let naive = gens.iter().position(|&g| {
                let mut one = vec![false; n];
                one[g] = true;
                weft_verified::dataflow::propagate(&succ, &one, &kill)[t]
            });
            proptest::prop_assert_eq!(first[t], naive, "target {}", t);
        }
    }
}

/// W0502 or W0302: the `callable` flag of the variable decides, not its type text.
#[test]
fn w0502_needs_a_callable_variable() {
    for (callable, code) in [(true, "W0502"), (false, "W0302")] {
        let mut b = B::new();
        let f = b.var_with("f", |v| {
            v.ty = "fn()".into();
            v.callable = callable;
        });
        let n0 = b.node("let f");
        b.bind(f, n0);
        let n1 = b.node("f");
        b.mv(f, n1);
        let n2 = b.node("f");
        b.mv(f, n2);
        let r = check(&b.f);
        let d = crate::diagnose::diagnose(&b.f, &r);
        let codes: Vec<&str> = d.iter().map(|d| d.code.as_str()).collect();
        assert_eq!(codes, [code], "callable: {callable}");
    }
    let closure = VarInfo::plain("c", VarKind::Closure, Span::default(), "T");
    assert!(closure.callable);
    // The type text does not decide: sema sets the flag from the resolved type.
    let param = VarInfo::plain("p", VarKind::Param, Span::default(), "fn() -> u64");
    assert!(!param.callable);
    let plain = VarInfo::plain("x", VarKind::Local, Span::default(), "u64");
    assert!(!plain.callable);
}

#[test]
fn w0702_names_the_effect_when_two_effects_have_one_name() {
    // `a.Note` is not the `Note` that `mixed` states, so the message names it.
    let src = "effect Note { fn note() }
effect Log { fn log(m: String) }
mod a {
    effect Note { fn note() }
    pub fn f() / Note { note() }
}
fn mixed() / Note {
    a.f()
}
fn other() / async {
    a.f()
}
fn std_log() / Log {
    log.info(\"x\")
}
";
    let c = crate::check_source("t.wf", src, weft_sema::Options::default());
    let msgs: Vec<&str> = c
        .diags
        .iter()
        .filter(|d| d.code == "W0702")
        .map(|d| d.message.as_str())
        .collect();
    assert!(
        msgs.iter().any(|m| m.contains("performs `main.a.Note`")),
        "{msgs:?}"
    );
    assert!(
        msgs.iter().any(|m| m.contains("`f` performs `Note`")),
        "{msgs:?}"
    );
    assert!(
        msgs.iter()
            .any(|m| m.contains("performs the standard effect `Log`")),
        "{msgs:?}"
    );
}
