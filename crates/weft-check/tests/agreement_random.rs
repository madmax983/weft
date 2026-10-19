//! Gate 1b, part 1: the production checker and the Datalog spec agree on random facts.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use proptest::prelude::*;
use weft_check::{bridge, check, Cause};
use weft_facts::{
    CapId, FnFacts, HandlerId, HandlerInfo, NodeId, PlaceId, RootKind, Span, Step, StepKind,
    TaskId, TaskKind, VarId, VarInfo, VarKind,
};

#[derive(Clone, Debug)]
struct Shape {
    nodes: usize,
    edges: Vec<(usize, usize)>,
    roots: Vec<u8>,
    places: Vec<(usize, u8, u8, bool)>,
    vars: Vec<[bool; 6]>,
    rels: Vec<(u8, usize, usize, usize)>,
    tasks: Vec<bool>,
    handlers: Vec<(bool, bool, u8)>,
    flags: (bool, bool),
}

fn step(kind: u8, id: u8, unstable: bool) -> Step {
    // Wildcard places, and one-place wildcard places of two instances.
    match kind % 9 {
        7 => return weft_facts::WILD,
        8 => return weft_facts::wild_one(u32::from(id % 2)),
        _ => {}
    }
    let id = u32::from(id % 3);
    let kind = match kind % 6 {
        0 => StepKind::Field { id },
        1 => StepKind::Variant { id },
        2 => StepKind::Elem,
        3 => StepKind::Seg {
            split: id % 2,
            hi: false,
        },
        4 => StepKind::Seg {
            split: id % 2,
            hi: true,
        },
        _ => StepKind::Deref,
    };
    Step { kind, unstable }
}

fn build(s: &Shape) -> FnFacts {
    let mut f = FnFacts {
        name: "random".into(),
        ..FnFacts::default()
    };
    for (i, k) in s.roots.iter().enumerate() {
        let kind = match k % 4 {
            0 => RootKind::Param,
            1 => RootKind::Local,
            2 => RootKind::Group,
            _ => RootKind::Arg,
        };
        f.add_root(format!("r{i}"), kind);
    }
    for &(parent, kind, id, unstable) in &s.places {
        let p = PlaceId(u32::try_from(parent % f.places.len()).unwrap());
        if f.place(p).steps.len() < 4 {
            f.child(p, step(kind, id, unstable), &format!(".s{kind}{id}"));
        }
    }
    for (i, flags) in s.vars.iter().enumerate() {
        let mut v = VarInfo::plain(format!("x{i}"), VarKind::Local, Span::default(), "T");
        v.linear = flags[0];
        v.has_on_abort = flags[1];
        v.once = flags[2];
        v.immovable = flags[3];
        v.nonportable = flags[4];
        v.uniq = flags[5];
        f.add_var(v);
    }
    for _ in 0..s.nodes {
        f.add_node(Span::default(), "n", "");
    }
    for (i, &fork) in s.tasks.iter().enumerate() {
        let _ = i;
        f.add_task(
            if fork {
                TaskKind::Fork
            } else {
                TaskKind::Spawn
            },
            Span::default(),
        );
    }
    for &(is_std, sim_root, e) in &s.handlers {
        f.handlers.push(HandlerInfo {
            effect: format!("E{}", e % 2),
            is_std,
            sim_root,
            span: Span::default(),
        });
    }
    let caps = 2u32;
    f.caps = caps;
    let n = |x: usize| NodeId(u32::try_from(x % s.nodes).unwrap());
    let np = f.places.len();
    let p = |x: usize| PlaceId(u32::try_from(x % np).unwrap());
    let nv = s.vars.len();
    let v = |x: usize| VarId(u32::try_from(x % nv).unwrap());
    let nt = s.tasks.len().max(1);
    let t = |x: usize| TaskId(u32::try_from(x % nt).unwrap());
    for &(a, b) in &s.edges {
        f.cfg_edge.push((n(a), n(b)));
    }
    let has_tasks = !s.tasks.is_empty();
    let nh = s.handlers.len();
    let cap = |x: usize| CapId(u32::try_from(x).unwrap() % caps);
    for &(rel, a, b, c) in &s.rels {
        match rel % 36 {
            0 => f.points_into.push((v(a), p(b))),
            1 => f.mutates_at.push((n(a), p(b))),
            2 => f.reads_at.push((n(a), p(b))),
            3 => f
                .performs_at
                .push((n(a), CapId(u32::try_from(b).unwrap() % caps))),
            4 => f
                .footprint
                .push((CapId(u32::try_from(a).unwrap() % caps), p(b))),
            5 => f.rebound_at.push((v(a), n(b))),
            6 => f.uses.push((v(a), n(b))),
            7 => {
                f.moved_at.push((v(a), n(b)));
                f.uses.push((v(a), n(b)));
            }
            8 => f.scope_end.push((v(a), n(b))),
            9 => f.may_abort.push(n(a)),
            10 => f.multi_at.push(n(a)),
            11 => f.declared_mut.push(p(a)),
            12 => f.escapes_at.push((n(a), format!("E{}", b % 2))),
            13 => f.declared_effect.push(format!("E{}", a % 2)),
            14 => f.shared_root.push(p(a)),
            15 if has_tasks => f.spawned_at.push((t(a), n(b))),
            16 if has_tasks => f.joined_at.push((t(a), n(b))),
            17 if has_tasks => f.task_reads.push((t(a), p(b))),
            18 if has_tasks => f.task_writes.push((t(a), p(b))),
            19 if has_tasks => {
                f.captures.push((t(a), v(b)));
                if c % 2 == 0 {
                    f.mut_through.push((t(a), v(b)));
                }
            }
            20 => f.call_mut.push((n(a), p(b), u32::try_from(c % 3).unwrap())),
            21 => f.call_arg.push((n(a), p(b), u32::try_from(c % 3).unwrap())),
            22 => f.owner.push((p(a), v(b))),
            23 => f.moved_part.push((p(a), n(b))),
            24 => f.lends_mut.push((n(a), p(b))),
            25 => f.clause_multi.push(cap(a)),
            26 => f.body_multi.push(cap(a)),
            27 => f.resumes_at.push((n(a), cap(b))),
            28 if nh > 0 => f.clause_performs.push((
                HandlerId(u32::try_from(a % nh).unwrap()),
                format!("E{}", b % 2),
            )),
            29 => f.overwrites.push((v(a), n(b))),
            30 => f.unset_at.push((v(a), n(b))),
            31 => f.empty_at.push((v(a), n(b))),
            32 => f.unwound_at.push((v(a), n(b))),
            33 => f.releases_at.push((n(a), p(b))),
            34 => f.writes_via.push((n(a), v(b))),
            35 => f.spared_at.push((v(a), n(b))),
            _ => {}
        }
    }
    f.has_signature = s.flags.0;
    f.library = s.flags.1;
    f.normalize();
    f
}

fn shape() -> impl Strategy<Value = Shape> {
    (
        1usize..10,
        prop::collection::vec((0usize..10, 0usize..10), 0..18),
        prop::collection::vec(any::<u8>(), 1..4),
        prop::collection::vec((0usize..20, any::<u8>(), any::<u8>(), any::<bool>()), 0..10),
        prop::collection::vec(any::<[bool; 6]>(), 1..5),
        prop::collection::vec((any::<u8>(), 0usize..20, 0usize..20, 0usize..6), 0..40),
        prop::collection::vec(any::<bool>(), 0..3),
        prop::collection::vec((any::<bool>(), any::<bool>(), any::<u8>()), 0..3),
        (any::<bool>(), any::<bool>()),
    )
        .prop_map(
            |(nodes, edges, roots, places, vars, rels, tasks, handlers, flags)| Shape {
                nodes,
                edges,
                roots,
                places,
                vars,
                rels,
                tasks,
                handlers,
                flags,
            },
        )
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("PROPTEST_CASES").ok().and_then(|v| v.parse().ok()).unwrap_or(512),
        ..ProptestConfig::default()
    })]

    #[test]
    fn checker_agrees_with_spec(s in shape()) {
        let f = build(&s);
        let fast = check(&f).violations;
        let spec = bridge::check_spec(&f).expect("spec evaluates");
        prop_assert_eq!(fast, spec);
    }

    /// Each W0301 error has one piece of evidence. Its node does what its cause
    /// says, and it reaches the use alone. The spec gives the nodes that
    /// invalidate the reference (`invalidated_at`). The evidence node is one of
    /// them, and no earlier one reaches the use alone.
    #[test]
    fn each_invalid_use_has_the_first_evidence(s in shape()) {
        let f = build(&s);
        let r = check(&f);
        let out = bridge::evaluate_spec(&f, false).expect("spec evaluates");
        let id = |v, prefix: char| -> u32 {
            let text = out.display_value(v);
            let text = text.trim_matches('"');
            text.strip_prefix(prefix)
                .and_then(|x| x.parse().ok())
                .unwrap_or_else(|| panic!("bad id {text}"))
        };
        let mut gens: Vec<(VarId, NodeId)> = out
            .tuples("invalidated_at")
            .iter()
            .map(|t| (VarId(id(t[0], 'v')), NodeId(id(t[1], 'n'))))
            .collect();
        gens.sort();
        gens.dedup();
        let n = f.nodes.len();
        let mut succ = vec![Vec::new(); n];
        for &(a, b) in &f.cfg_edge {
            succ[a.index()].push(b.index());
        }
        let reaches = |v: VarId, at: NodeId, u: NodeId| {
            let mut kill = vec![false; n];
            for &(x, q) in &f.rebound_at {
                if x == v {
                    kill[q.index()] = true;
                }
            }
            let mut one = vec![false; n];
            one[at.index()] = true;
            weft_verified::dataflow::propagate(&succ, &one, &kill)[u.index()]
        };
        for &(v, u) in &r.violations.error {
            let evidence: Vec<_> = r
                .invalidations
                .iter()
                .filter(|i| i.var == v && i.used_at == u)
                .collect();
            prop_assert_eq!(evidence.len(), 1, "error {:?}", (v, u));
            let inv = evidence[0];
            prop_assert!(f.points_into.contains(&(v, inv.path)));
            let at = inv.at;
            let done = match inv.cause {
                Cause::Mutation(m) => {
                    f.mutates_at.contains(&(at, m))
                        || f.performs_at.iter().any(|&(q, c)| {
                            q == at && f.footprint.contains(&(c, m))
                        })
                }
                Cause::Lend(m) => f.lends_mut.contains(&(at, m)),
                Cause::Move(o) => f.moved_at.contains(&(o, at)),
                Cause::ScopeEnd(o) => f.scope_end.contains(&(o, at)),
                Cause::Unwound(o) => f.unwound_at.contains(&(o, at)),
                Cause::MovePart(m) => f.moved_part.contains(&(m, at)),
                Cause::Release(m) => f.releases_at.contains(&(at, m)),
            };
            prop_assert!(done, "{:?}", inv);
            prop_assert!(reaches(v, at, u), "{:?}", inv);
            prop_assert!(gens.contains(&(v, at)), "{:?} is not a spec gen", inv);
            for &(_, p) in gens.iter().filter(|&&(x, p)| x == v && p < at) {
                prop_assert!(!reaches(v, p, u), "gen {:?} before {:?}", p, inv);
            }
        }
        prop_assert_eq!(r.invalidations.len(), r.violations.error.len());
    }
}
