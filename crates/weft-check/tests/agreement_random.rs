//! Gate 1b, part 1: the production checker and the Datalog spec agree on random facts.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use proptest::prelude::*;
use weft_check::{bridge, check};
use weft_facts::{
    CapId, FnFacts, HandlerInfo, NodeId, PlaceId, RootKind, Span, Step, StepKind, TaskId, TaskKind,
    VarId, VarInfo, VarKind,
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
        let kind = match k % 3 {
            0 => RootKind::Param,
            1 => RootKind::Local,
            _ => RootKind::Group,
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
    for &(is_std, forwards, e) in &s.handlers {
        f.handlers.push(HandlerInfo {
            effect: format!("E{}", e % 2),
            is_std,
            forwards,
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
    for &(rel, a, b, c) in &s.rels {
        match rel % 24 {
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
}
