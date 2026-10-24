//! Unit tests of the fact generator: the parts that do not need the
//! analysis (plan stage F2, `docs/ir.md` 6.1 to 6.3 and 6.7: the relation
//! table `RELS`, the nodes and phases, roots and α, and the variables), and
//! the templates of the statements and the simple terminators (stage F4,
//! `docs/ir.md` 6.4), and the phases of a call with the summary of its
//! callee (stage F5, `docs/ir.md` 6.4 and 6.7).

use std::collections::{BTreeMap, BTreeSet};

use weft_facts::{FnFacts, NodeId, PlaceId, StepKind, VarId};
use weft_ir::{
    BlockId, BodyId, CapOperand, Const, DerefKind, EffectId, HandlerId, LocalId, LocalKind, OpIdx,
    Operand, Place, Proj, ScopeId, Side, SpawnId, TermKind, TyTable,
};
use weft_ir::{Callee, CapArgs};
use weft_sema::factgen::alpha::{self, AlphaError, Roots};
use weft_sema::factgen::frames::Frames;
use weft_sema::factgen::nodes::{self, NodeKey, NodeTable, Phase, PAST};
use weft_sema::factgen::rels::{self, Part, Rel, Role, Source};
use weft_sema::factgen::vars::{VarKey, Vars};
use weft_sema::irbuild::{self, Built, Outcome};
use weft_sema::{analyze_source, Analysis, Options};

/// The id of item `i` of a table.
fn id(i: usize) -> u32 {
    u32::try_from(i).unwrap_or(u32::MAX)
}

// ----------------------------------------------------------------- RELS

/// Each input relation of the spec has a row, and each row names an input
/// relation of the spec.
#[test]
fn rows_match_the_spec() {
    let spec = rels::spec_inputs().unwrap_or_else(|e| panic!("the spec: {e}"));
    let rows: BTreeSet<String> = rels::ALL.iter().map(|r| r.name()).collect();
    let no_row: Vec<&String> = spec.difference(&rows).collect();
    let no_rel: Vec<&String> = rows.difference(&spec).collect();
    assert!(no_row.is_empty(), "spec relations with no row: {no_row:?}");
    assert!(
        no_rel.is_empty(),
        "rows that the spec does not have: {no_rel:?}"
    );
    assert!(spec.contains("rest_linear"));
    assert_eq!(rels::ALL.len(), spec.len());
}

/// Each node relation that can name an interface place or variable has a
/// summary part, or a stated reason.
#[test]
fn each_node_relation_has_a_part_or_a_reason() {
    for r in rels::ALL {
        let row = rels::row_of(*r);
        if let Err(why) = row.part {
            assert!(!why.is_empty(), "{} has no part and no reason", r.name());
        }
        if row.source == Source::Template && matches!(row.role, Role::Gen | Role::Both) {
            // A relation that names a place of the caller must reach the caller.
            let names_places = matches!(
                r,
                Rel::MutatesAt
                    | Rel::ReadsAt
                    | Rel::LendsMut
                    | Rel::ReleasesAt
                    | Rel::MovedPart
                    | Rel::CallMut
                    | Rel::CallArg
            );
            if names_places {
                assert!(row.part.is_ok(), "{} names caller places", r.name());
            }
        }
    }
    // `docs/ir.md` 6.7: `rebound_at` goes to the must part `rebinds`, and
    // `joined_at` to the part `tasks`.
    assert_eq!(rels::row_of(Rel::ReboundAt).part, Ok(Part::Rebinds));
    assert_eq!(rels::row_of(Rel::ReboundAt).role, Role::Kill);
    assert_eq!(rels::row_of(Rel::JoinedAt).part, Ok(Part::Tasks));
}

#[test]
fn the_parser_finds_the_input_relations_of_a_small_program() {
    let p = "a(X) :- b(X), !c(X).\nd(X) :- a(X), e(X). // f(X)\n";
    let got: Vec<String> = rels::inputs_of(p).into_iter().collect();
    assert_eq!(got, vec!["b", "c", "e"]);
}

/// The relations of each field of `FnFacts`. The destructure names each field,
/// so a new field of `FnFacts` needs a decision here (as `FnFacts::mark`).
fn field_rels(f: &FnFacts) -> Vec<(&'static str, Vec<Rel>)> {
    use Rel as R;
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
        points_into: _,
        mutates_at: _,
        reads_at: _,
        performs_at: _,
        footprint: _,
        rebound_at: _,
        uses: _,
        moved_at: _,
        scope_end: _,
        overwrites: _,
        unset_at: _,
        empty_at: _,
        unwound_at: _,
        owner: _,
        moved_part: _,
        rest_linear: _,
        releases_at: _,
        may_abort: _,
        multi_at: _,
        spared_at: _,
        clause_multi: _,
        body_multi: _,
        resumes_at: _,
        clause_performs: _,
        has_signature: _,
        declared_mut: _,
        declared_effect: _,
        escapes_at: _,
        shared_root: _,
        spawned_at: _,
        joined_at: _,
        task_reads: _,
        task_writes: _,
        captures: _,
        mut_through: _,
        kept: _,
        spawns_in: _,
        opaque: _,
        call_mut: _,
        call_arg: _,
        lends_mut: _,
        writes_via: _,
        arg_at: _,
        param_in: _,
        uniq_param: _,
        arg_aliased: _,
        fn_arg_effect: _,
        param_effect: _,
        sim_run_at: _,
        ref_at: _,
        ref_in: _,
        std_effects: _,
        library: _,
        started: _,
        no_runtime: _,
        place_index: _,
    } = f;
    vec![
        // Tables that are not relations: names, exports, diagnostics.
        ("name", vec![]),
        ("by_value", vec![]),
        ("arg_order", vec![]),
        ("effect_names", vec![]),
        ("hidden_effects", vec![]),
        ("int_ops", vec![]),
        ("arg_sites", vec![]),
        ("ref_sites", vec![]),
        ("caps", vec![]),
        ("nodes", vec![]),
        ("place_index", vec![]),
        // The place interner.
        ("roots", vec![R::ParamRooted]),
        (
            "places",
            vec![
                R::Place,
                R::Parent,
                R::Unstable,
                R::Wildcard,
                R::OnePlace,
                R::StepAlias,
                R::StepWithin,
                R::ParamRooted,
            ],
        ),
        // The flags of the variables.
        (
            "vars",
            vec![
                R::Linear,
                R::HasOnAbort,
                R::OnceVar,
                R::Immovable,
                R::Nonportable,
                R::Uniq,
            ],
        ),
        ("tasks", vec![R::Task, R::ForkTask]),
        ("handlers", vec![R::Handler, R::SimRoot]),
        ("cfg_edge", vec![R::CfgEdge]),
        ("points_into", vec![R::PointsInto]),
        ("mutates_at", vec![R::MutatesAt]),
        ("reads_at", vec![R::ReadsAt]),
        ("performs_at", vec![R::PerformsAt]),
        ("footprint", vec![R::Footprint]),
        ("rebound_at", vec![R::ReboundAt]),
        ("uses", vec![R::Uses]),
        ("moved_at", vec![R::MovedAt]),
        ("scope_end", vec![R::ScopeEnd]),
        ("overwrites", vec![R::Overwrites]),
        ("unset_at", vec![R::UnsetAt]),
        ("empty_at", vec![R::EmptyAt]),
        ("unwound_at", vec![R::UnwoundAt]),
        ("owner", vec![R::Owner]),
        ("moved_part", vec![R::MovedPart]),
        ("rest_linear", vec![R::RestLinear]),
        ("releases_at", vec![R::ReleasesAt]),
        ("may_abort", vec![R::MayAbort]),
        ("multi_at", vec![R::MultiAt]),
        ("spared_at", vec![R::SparedAt]),
        ("clause_multi", vec![R::ClauseMulti]),
        ("body_multi", vec![R::BodyMulti]),
        ("resumes_at", vec![R::ResumesAt]),
        ("clause_performs", vec![R::ClausePerforms]),
        ("has_signature", vec![R::HasSignature]),
        ("declared_mut", vec![R::DeclaredMut]),
        ("declared_effect", vec![R::DeclaredEffect]),
        ("escapes_at", vec![R::EscapesAt]),
        ("shared_root", vec![R::SharedRoot]),
        ("spawned_at", vec![R::SpawnedAt]),
        ("joined_at", vec![R::JoinedAt]),
        ("task_reads", vec![R::TaskReads]),
        ("task_writes", vec![R::TaskWrites]),
        ("captures", vec![R::Captures]),
        ("mut_through", vec![R::MutThrough]),
        ("kept", vec![R::Kept]),
        ("spawns_in", vec![R::SpawnsIn]),
        ("opaque", vec![R::Opaque]),
        ("call_mut", vec![R::CallMut]),
        ("call_arg", vec![R::CallArg]),
        ("lends_mut", vec![R::LendsMut]),
        ("writes_via", vec![R::WritesVia]),
        ("arg_at", vec![R::ArgAt]),
        ("param_in", vec![R::ParamIn]),
        ("uniq_param", vec![R::UniqParam]),
        ("arg_aliased", vec![R::ArgAliased]),
        ("fn_arg_effect", vec![R::FnArgEffect]),
        ("param_effect", vec![R::ParamEffect]),
        ("sim_run_at", vec![R::SimRunAt]),
        ("ref_at", vec![R::RefAt]),
        ("ref_in", vec![R::RefIn]),
        ("std_effects", vec![R::StdEffect]),
        ("library", vec![R::Library]),
        ("started", vec![R::Started]),
        ("no_runtime", vec![R::NoRuntime]),
    ]
}

/// Each relation of `RELS` has a field of `FnFacts`, and each field that
/// holds a relation maps to rows of `RELS`.
#[test]
fn each_field_of_the_facts_maps_to_rows() {
    let fields = field_rels(&FnFacts::default());
    let mapped: BTreeSet<Rel> = fields.iter().flat_map(|(_, rs)| rs.clone()).collect();
    let all: BTreeSet<Rel> = rels::ALL.iter().copied().collect();
    let missing: Vec<String> = all.difference(&mapped).map(|r| r.name()).collect();
    assert!(missing.is_empty(), "relations with no field: {missing:?}");
    let extra: Vec<String> = mapped.difference(&all).map(|r| r.name()).collect();
    assert!(
        extra.is_empty(),
        "fields of relations with no row: {extra:?}"
    );
    let names: BTreeSet<&str> = fields.iter().map(|(n, _)| *n).collect();
    assert_eq!(names.len(), fields.len(), "a field twice");
}

// --------------------------------------------------------------- nodes

/// A terminator of each kind.
fn all_terms() -> Vec<TermKind> {
    let b = BlockId(0);
    let place = || Place {
        local: LocalId(0),
        proj: vec![],
    };
    let o = || Operand::Const(Const::Unit);
    vec![
        TermKind::Goto(b),
        TermKind::Switch {
            on: o(),
            arms: vec![],
            otherwise: b,
        },
        TermKind::Return,
        TermKind::UnwindExit,
        TermKind::Unreachable,
        TermKind::Call {
            callee: Callee::Value(o()),
            args: vec![],
            dest: place(),
            caps: CapArgs::Root,
            next: Some(b),
            unwind: Some(b),
        },
        TermKind::Perform {
            cap: CapOperand::Row(EffectId(0)),
            op: OpIdx(0),
            args: vec![],
            dest: place(),
            next: b,
            unwind: Some(b),
        },
        TermKind::Resume {
            kont: place(),
            arg: o(),
            dest: place(),
            next: b,
            unwind: Some(b),
        },
        TermKind::Handle {
            handler: HandlerId(0),
            dest: place(),
            next: b,
            unwind: Some(b),
        },
        TermKind::Scope {
            scope: ScopeId(0),
            dest: place(),
            next: b,
            unwind: Some(b),
        },
        TermKind::ScopeWait {
            scope: place(),
            orphans: vec![],
            next: b,
            unwind: Some(b),
        },
        TermKind::Spawn {
            site: SpawnId(0),
            scope: o(),
            task: o(),
            dest: None,
            next: b,
        },
        TermKind::Join {
            task: o(),
            dest: place(),
            next: b,
            unwind: Some(b),
        },
        TermKind::Detach { task: o(), next: b },
        TermKind::Fork {
            sites: vec![],
            branches: vec![],
            dest: place(),
            next: b,
            unwind: Some(b),
        },
        TermKind::Assert {
            cond: o(),
            next: b,
            unwind: Some(b),
        },
        TermKind::IterNext {
            iter: place(),
            dest: place(),
            next: b,
            done: b,
        },
    ]
}

/// The phases of each terminator in the order of the table of `docs/ir.md`
/// 6.2: the normal path, the abort path with and without a value, and the
/// phase at the end of an abort to a handler.
#[test]
fn the_phases_of_each_terminator_follow_ir_6_2() {
    use Phase::{AbortValue, Exit, FrameEnd, Landing, Main, Post, Ret};
    let mut seen = Vec::new();
    for t in all_terms() {
        let name = nodes::term_name(&t);
        let normal = nodes::normal_phases(&t);
        let abort = nodes::abort_phases(&t, false);
        let valued = nodes::abort_phases(&t, true);
        let landing = nodes::landing_phases(&t);
        let want: (&[Phase], &[Phase], &[Phase], &[Phase]) = match name {
            "call" | "resume" => (
                &[Main, Ret, FrameEnd],
                &[Main, FrameEnd],
                &[Main, AbortValue, FrameEnd],
                &[],
            ),
            "perform" | "join" | "fork" => (&[Main, Ret], &[Main], &[Main, AbortValue], &[]),
            "handle" => (&[Main, Exit, Post], &[Main], &[Main], &[Landing]),
            "scope" => (&[Main, Exit, FrameEnd], &[Main], &[Main], &[]),
            "scope wait" => (&[Main], &[Main], &[Main, AbortValue], &[]),
            "assert" => (&[Main], &[Main], &[Main], &[]),
            _ => (&[Main], &[], &[], &[]),
        };
        assert_eq!(normal, want.0, "{name}: normal path");
        assert_eq!(abort, want.1, "{name}: abort path");
        assert_eq!(valued, want.2, "{name}: abort path with a value");
        assert_eq!(landing, want.3, "{name}: landing");
        seen.push(name);
    }
    assert_eq!(seen.len(), 17);
}

/// The analysis and the IR of `src`.
fn built(src: &str) -> (Analysis, Built) {
    let a = analyze_source(src, Options::default())
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let b = irbuild::build(&a);
    assert!(b.broken.is_empty(), "{:?}", b.broken);
    (a, b)
}

/// The body of the function or test `name`.
fn body_of(b: &Built, name: &str) -> BodyId {
    let e = b
        .entries
        .iter()
        .find(|e| e.name == name)
        .unwrap_or_else(|| panic!("no body `{name}`"));
    match e.outcome {
        Outcome::Built(id) => id,
        _ => panic!("`{name}` has no IR"),
    }
}

#[test]
fn the_node_table_links_the_phases_and_the_blocks() {
    let (_, b) = built("fn g(x: u64) -> u64 { x }\nfn f() -> u64 { let a = 1; g(a) }\n");
    let f = body_of(&b, "f");
    let body = &b.program.bodies[f.index()];
    let mut facts = FnFacts::default();
    let table = NodeTable::build(&b.program, f, &mut facts, &Frames::past(&b.program, f));
    let (cb, next, unwind) = body
        .blocks
        .iter()
        .enumerate()
        .find_map(|(i, blk)| match blk.term.kind {
            TermKind::Call {
                next: Some(n),
                unwind: Some(u),
                ..
            } => Some((BlockId(u32::try_from(i).unwrap_or(0)), n, u)),
            _ => None,
        })
        .expect("a call with an unwind block");
    let key = |block: BlockId, at: u32, phase: Phase, dest: u32| NodeKey {
        body: f,
        block,
        at,
        phase,
        dest,
    };
    let id = |k: NodeKey| table.get(k).unwrap_or_else(|| panic!("no node {k:?}"));
    let t = u32::MAX;
    let main = id(key(cb, t, Phase::Main, 0));
    let ret = id(key(cb, t, Phase::Ret, 0));
    let end = id(key(cb, t, Phase::FrameEnd, 0));
    let abort_end = id(key(cb, t, Phase::FrameEnd, PAST));
    let first_next = table.first(f, next, 0).expect("the next block has a node");
    let first_unwind = table.first(f, unwind, PAST).expect("the cleanup copy");
    let edges: BTreeSet<(u32, u32)> = facts.cfg_edge.iter().map(|(a, b)| (a.0, b.0)).collect();
    for (a, b, what) in [
        (main, ret, "Main to Ret"),
        (ret, end, "Ret to FrameEnd"),
        (end, first_next, "FrameEnd to the next block"),
        (main, abort_end, "Main to FrameEnd of the abort"),
        (
            abort_end,
            first_unwind,
            "FrameEnd of the abort to the cleanup copy",
        ),
    ] {
        assert!(edges.contains(&(a.0, b.0)), "no edge {what}");
    }
    // A cleanup block has no copy for the normal path.
    assert!(table.first(f, unwind, 0).is_none());
    // The statements of the entry block come before its terminator.
    let entry = body.entry;
    let first = table.first(f, entry, 0).expect("the entry has a node");
    let s0 = id(key(entry, 0, Phase::Main, 0));
    assert_eq!(first, s0);
    // Each node has the span of its origin.
    assert_eq!(facts.nodes.len(), table.len());
    assert!(facts.nodes.iter().all(|n| n.span.hi >= n.span.lo));
}

// -------------------------------------------------------------- roots and α

const PLACES: &str = "struct P { x: u64, y: (u64, bool) }
enum E { A(u64), B(u64, bool) }
struct Node { v: u64 }
fn f(p: P, e: E, v: Vec<u64>, a: [u64; 3], b: Box<P>, r: Rc<Node>, q: &P) {}
";

/// The parameter `name` of body `f`.
fn param(b: &Built, f: BodyId, name: &str) -> LocalId {
    let body = &b.program.bodies[f.index()];
    body.params
        .iter()
        .copied()
        .find(|l| body.locals[l.index()].name.as_deref() == Some(name))
        .unwrap_or_else(|| panic!("no parameter `{name}`"))
}

/// The place of local `l` with the projections `proj`.
const fn place(l: LocalId, proj: Vec<Proj>) -> Place {
    Place { local: l, proj }
}

/// The display text and the steps of a fact place.
fn show(facts: &FnFacts, p: PlaceId) -> (String, Vec<(StepKind, bool)>) {
    let info = facts.place(p);
    let steps = info.steps.iter().map(|s| (s.kind, s.unstable)).collect();
    (info.display.clone(), steps)
}

/// α of `place` in body `f`: the one place, its pointer places and its
/// handle places, as display texts.
fn alpha_of(
    b: &Built,
    f: BodyId,
    place: &Place,
) -> Result<(String, Vec<String>, Vec<String>), AlphaError> {
    let mut facts = FnFacts::default();
    let mut tys: TyTable = b.tys.clone();
    let mut roots = Roots::default();
    let a = alpha::alpha(&b.program, &mut tys, &mut facts, &mut roots, f, place)?;
    assert_eq!(a.places.len(), 1, "one place");
    let text = |ps: &[PlaceId]| ps.iter().map(|p| show(&facts, *p).0).collect();
    Ok((show(&facts, a.places[0]).0, text(&a.ptrs), text(&a.handles)))
}

#[test]
fn alpha_gives_the_steps_of_the_place_model() {
    use weft_ir::{FieldIdx, VariantIdx};
    let (_, b) = built(PLACES);
    let f = body_of(&b, "f");
    let at = |name: &str, proj: Vec<Proj>| alpha_of(&b, f, &place(param(&b, f, name), proj));
    let i = LocalId(0);
    // A field of a struct and of a tuple: stable steps.
    assert_eq!(
        at("p", vec![Proj::Field(FieldIdx(0))]).map(|x| x.0),
        Ok("p.x".into())
    );
    assert_eq!(
        at(
            "p",
            vec![Proj::Field(FieldIdx(1)), Proj::Field(FieldIdx(1))]
        )
        .map(|x| x.0),
        Ok("p.y.1".into())
    );
    // A variant payload: one unstable step; a payload of two fields has a
    // field step after it.
    assert_eq!(
        at("e", vec![Proj::Variant(VariantIdx(0))]).map(|x| x.0),
        Ok("e.A".into())
    );
    assert_eq!(
        at(
            "e",
            vec![Proj::Variant(VariantIdx(0)), Proj::Field(FieldIdx(0))]
        )
        .map(|x| x.0),
        Ok("e.A".into())
    );
    assert_eq!(
        at(
            "e",
            vec![Proj::Variant(VariantIdx(1)), Proj::Field(FieldIdx(1))]
        )
        .map(|x| x.0),
        Ok("e.B.1".into())
    );
    // An element of a `Vec` and of an array, and all elements.
    assert_eq!(at("v", vec![Proj::Index(i)]).map(|x| x.0), Ok("v[]".into()));
    assert_eq!(at("a", vec![Proj::Index(i)]).map(|x| x.0), Ok("a[]".into()));
    assert_eq!(at("v", vec![Proj::Elems]).map(|x| x.0), Ok("v[]".into()));
    // An element of the elements is the same place (a slice names its
    // elements).
    assert_eq!(
        at("v", vec![Proj::Elems, Proj::Index(i)]).map(|x| x.0),
        Ok("v[]".into())
    );
    // A split of the elements.
    assert_eq!(
        at(
            "v",
            vec![Proj::Elems, Proj::Split(weft_ir::SplitId(3), Side::Right)]
        )
        .map(|x| x.0),
        Ok("v[][k..]".into())
    );
    // A `Box`: a deref step, then the field. The box is a pointer place.
    assert_eq!(
        at(
            "b",
            vec![Proj::Deref(DerefKind::Box), Proj::Field(FieldIdx(0))]
        ),
        Ok(("b.x".into(), vec!["b".into()], vec![]))
    );
    // An `Rc`: the group root of the inner type; the handle place joins.
    assert_eq!(
        at(
            "r",
            vec![Proj::Deref(DerefKind::Rc), Proj::Field(FieldIdx(0))]
        ),
        Ok(("Node.v".into(), vec!["r".into()], vec!["r.*".into()]))
    );
    // A reference: the analysis gives the places (stage F3).
    assert!(matches!(
        at(
            "q",
            vec![Proj::Deref(DerefKind::Ref), Proj::Field(FieldIdx(0))]
        ),
        Err(AlphaError::NeedsValue { .. })
    ));
}

#[test]
fn alpha_gives_the_stability_of_each_step_from_the_type() {
    use weft_ir::{FieldIdx, VariantIdx};
    let (_, b) = built(PLACES);
    let f = body_of(&b, "f");
    let mut facts = FnFacts::default();
    let mut tys = b.tys.clone();
    let mut roots = Roots::default();
    let mut steps = |name: &str, proj: Vec<Proj>| {
        let pl = place(param(&b, f, name), proj);
        let a = alpha::alpha(&b.program, &mut tys, &mut facts, &mut roots, f, &pl)
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        show(&facts, a.places[0]).1
    };
    let i = LocalId(0);
    assert_eq!(
        steps("p", vec![Proj::Field(FieldIdx(0))]),
        [(StepKind::Field { id: 0 }, false)]
    );
    assert_eq!(
        steps("e", vec![Proj::Variant(VariantIdx(1))]),
        [(StepKind::Variant { id: 1 }, true)]
    );
    assert_eq!(steps("v", vec![Proj::Index(i)]), [(StepKind::Elem, true)]);
    assert_eq!(steps("a", vec![Proj::Index(i)]), [(StepKind::Elem, false)]);
    assert_eq!(steps("a", vec![Proj::Elems]), [(StepKind::Elem, false)]);
    assert_eq!(
        steps(
            "v",
            vec![Proj::Elems, Proj::Split(weft_ir::SplitId(2), Side::Left)]
        ),
        [
            (StepKind::Elem, true),
            (
                StepKind::Seg {
                    split: 2,
                    hi: false
                },
                true
            )
        ]
    );
    assert_eq!(
        steps("b", vec![Proj::Deref(DerefKind::Box)]),
        [(StepKind::Deref, true)]
    );
    // The group root has no step; the root is a group root.
    assert!(steps("r", vec![Proj::Deref(DerefKind::Rc)]).is_empty());
    // One root for each local, and one for each group.
    let names: Vec<&str> = facts.roots.iter().map(|r| r.name.as_str()).collect();
    assert_eq!(names, ["p", "e", "v", "a", "b", "r", "Node"]);
    assert_eq!(facts.roots[6].kind, weft_facts::RootKind::Group);
    assert_eq!(facts.roots[0].kind, weft_facts::RootKind::Local);
}

#[test]
fn an_upvar_local_has_the_root_of_its_site_local() {
    let src = "effect Log { fn log(m: u64) }
        fn f() { let n = 1; handle Log { fn log(m) { print(n); resume(()) } } in log(2) }";
    let (_, b) = built(src);
    let f = body_of(&b, "f");
    let p = &b.program;
    let (clause, up) = p
        .bodies
        .iter()
        .enumerate()
        .find_map(|(i, body)| {
            body.locals
                .iter()
                .position(|l| matches!(l.kind, LocalKind::Upvar(_)))
                .map(|l| (BodyId(id(i)), LocalId(id(l))))
        })
        .expect("an upvar local");
    let LocalKind::Upvar(site) = p.bodies[clause.index()].locals[up.index()].kind else {
        panic!("not an upvar");
    };
    let mut facts = FnFacts::default();
    let mut tys = b.tys.clone();
    let mut roots = Roots::default();
    let a = alpha::alpha(
        p,
        &mut tys,
        &mut facts,
        &mut roots,
        clause,
        &place(up, vec![]),
    )
    .expect("alpha");
    let s =
        alpha::alpha(p, &mut tys, &mut facts, &mut roots, f, &place(site, vec![])).expect("alpha");
    assert_eq!(a.places, s.places);
    assert_eq!(show(&facts, a.places[0]).0, "n");
}

// ------------------------------------------------------------ variables

#[test]
fn each_local_with_storage_has_an_owner_variable_with_its_flags() {
    let src = "linear struct Tx { id: u64 }
            on abort = undo
        fn undo(t: Tx) { let Tx(i) = t }
        fn mk() -> Tx { Tx { id: 1 } }
        fn f(n: u64) / async {
            let t = mk()
            undo(t)
            let x = 1
            let p = (&x, 2)
            p.0 = &n
            let k = Vec.new()
            k.push(1)
            let g = || print(k.len())
            g()
            scope { s => let h = s.spawn(|| 5); h.join() }
        }";
    let (_, b) = built(src);
    let f = body_of(&b, "f");
    let p = &b.program;
    let mut facts = FnFacts::default();
    let mut tys = b.tys.clone();
    let comp = weft_sema::factgen::component(&b, f);
    let vars = Vars::build(p, &mut tys, &mut facts, &comp);
    let body = &p.bodies[f.index()];
    let local = |name: &str| {
        let i = body
            .locals
            .iter()
            .position(|l| l.name.as_deref() == Some(name));
        let Some(i) = i else {
            panic!("no local `{name}`");
        };
        LocalId(id(i))
    };
    let var = |k: VarKey| {
        let Some(v) = vars.get(&k) else {
            panic!("no variable {k:?}");
        };
        facts.var(v).clone()
    };
    // S of each local; the flags come from the properties.
    let t = var(VarKey::S(f, local("t")));
    assert_eq!(t.name, "t");
    assert!(t.linear && t.has_on_abort && t.once);
    assert!(!var(VarKey::S(f, local("x"))).linear);
    assert_eq!(
        var(VarKey::S(f, body.params[0])).kind,
        weft_facts::VarKind::Param
    );
    // A part that the body assigns on its own and that can hold a reference
    // has an `H` variable.
    let pa = Place {
        local: local("p"),
        proj: vec![Proj::Field(weft_ir::FieldIdx(0))],
    };
    assert_eq!(var(VarKey::H(f, pa)).name, "value in `p.0`");
    // A local that a closure captures by reference has a cell variable.
    let (c, cap) = p
        .closures
        .iter()
        .flat_map(|c| c.captures.iter().map(move |cap| (c, cap)))
        .find(|(_, cap)| cap.mode == weft_ir::CaptureMode::ByRef)
        .expect("a capture by reference");
    assert_eq!(var(VarKey::C(c.maker, cap.source.local)).name, "k (cell)");
    // The task handle is `once`; the scope capability too.
    let scope_body = comp
        .iter()
        .copied()
        .find(|b| matches!(p.bodies[b.index()].kind, weft_ir::BodyKind::Scope(_)))
        .expect("a scope body");
    let sb = &p.bodies[scope_body.index()];
    let cap = sb.params[0];
    assert!(var(VarKey::S(scope_body, cap)).once);
    let h = sb
        .locals
        .iter()
        .position(|l| l.name.as_deref() == Some("h"))
        .map(|i| LocalId(id(i)))
        .expect("the handle `h`");
    let hv = var(VarKey::S(scope_body, h));
    assert!(hv.once);
    assert_eq!(hv.kind, weft_facts::VarKind::Task);
    // No variable for an upvar local or an environment.
    for (bi, body) in comp.iter().map(|b| (*b, &p.bodies[b.index()])) {
        for (li, l) in body.locals.iter().enumerate() {
            let k = VarKey::S(bi, LocalId(id(li)));
            let none = matches!(l.kind, LocalKind::Upvar(_) | LocalKind::Env);
            assert_eq!(vars.get(&k).is_none(), none, "{k:?}");
        }
    }
    assert_eq!(facts.vars.len(), vars.len());
}

#[test]
fn a_place_field_that_has_no_value_has_an_unset_variable() {
    let src = "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }
        fn make() -> Frame { Frame { buf: [0, 0, 0, 0] } }
        fn f() { let fr = make() }
        fn g() { let bx = Box.new(make()) }";
    let (_, b) = built(src);
    let f = body_of(&b, "f");
    let p = &b.program;
    let mut facts = FnFacts::default();
    let mut tys = b.tys.clone();
    let comp = weft_sema::factgen::component(&b, f);
    let vars = Vars::build(p, &mut tys, &mut facts, &comp);
    let unset: Vec<String> = vars
        .keys()
        .filter(|k| matches!(k, VarKey::U(..)))
        .map(|k| facts.var(vars.get(k).expect("a variable")).name.clone())
        .collect();
    assert!(!unset.is_empty(), "no `U` variable");
    assert!(
        unset.iter().all(|n| n.rsplit('.').next() == Some("cur")),
        "{unset:?}"
    );
    // A local keeps `!Move`; only a local that the builder builds for one
    // call, in place, loses the flag (`docs/ir.md` 5.36).
    let fr = p.bodies[f.index()]
        .locals
        .iter()
        .position(|l| l.name.as_deref() == Some("fr"))
        .map(|i| LocalId(id(i)))
        .expect("`fr`");
    let v = vars.get(&VarKey::S(f, fr)).expect("S(fr)");
    assert!(facts.var(v).immovable);
    let g = body_of(&b, "g");
    let comp = weft_sema::factgen::component(&b, g);
    let mut facts = FnFacts::default();
    let vars = Vars::build(p, &mut tys, &mut facts, &comp);
    let body = &p.bodies[g.index()];
    let arg = body
        .locals
        .iter()
        .position(|l| l.in_place)
        .map(|i| LocalId(id(i)))
        .expect("an in-place local");
    let v = vars
        .get(&VarKey::S(g, arg))
        .expect("S of the in-place local");
    assert!(!facts.var(v).immovable);
}

/// The places of the statements and terminators of a body.
fn places_of(body: &weft_ir::Body) -> Vec<Place> {
    use weft_ir::{Rvalue, StmtKind};
    let mut out = Vec::new();
    let op = |o: &Operand, out: &mut Vec<Place>| {
        if let Some(p) = o.place() {
            out.push(p.clone());
        }
    };
    for blk in &body.blocks {
        for s in &blk.stmts {
            match &s.kind {
                StmtKind::Assign(p, rv) => {
                    out.push(p.clone());
                    match rv {
                        Rvalue::Use(o) | Rvalue::Unary(_, _, o) => op(o, &mut out),
                        Rvalue::Binary(_, _, x, y) => {
                            op(x, &mut out);
                            op(y, &mut out);
                        }
                        Rvalue::Aggregate(_, os) | Rvalue::Concat(os) => {
                            for o in os {
                                op(o, &mut out);
                            }
                        }
                        Rvalue::Ref(p) | Rvalue::Len(p) | Rvalue::Discriminant(p) => {
                            out.push(p.clone());
                        }
                        Rvalue::Iter(_) => {}
                    }
                }
                StmtKind::Drop(p)
                | StmtKind::Consume(p)
                | StmtKind::Uninit(p)
                | StmtKind::Mention(p)
                | StmtKind::UnwindValue(p, _) => out.push(p.clone()),
                StmtKind::Bounds(p, o) => {
                    out.push(p.clone());
                    op(o, &mut out);
                }
                _ => {}
            }
        }
    }
    out
}

/// On each program of the corpus: α of each place of the IR has a result,
/// or needs a value (F3) or a later stage, and the nodes and the variables of
/// each component build. A place that does not fit its type is a bug.
#[test]
fn the_skeleton_runs_on_the_corpus() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("the corpus")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    files.sort();
    let mut bad = Vec::new();
    let (mut ok, mut later) = (0usize, 0usize);
    for f in &files {
        let src = std::fs::read_to_string(f).expect("read");
        let Ok(a) = analyze_source(&src, Options::default()) else {
            continue;
        };
        let b = irbuild::build(&a);
        for e in &b.entries {
            let Outcome::Built(entry) = e.outcome else {
                continue;
            };
            let comp = weft_sema::factgen::component(&b, entry);
            assert_eq!(comp.first(), Some(&entry), "{}", e.name);
            let mut facts = FnFacts::default();
            let mut tys = b.tys.clone();
            let vars = Vars::build(&b.program, &mut tys, &mut facts, &comp);
            assert_eq!(vars.len(), facts.vars.len());
            let mut roots = Roots::default();
            let mut table = NodeTable::default();
            for &body in &comp {
                table.add_body(
                    &b.program,
                    body,
                    &mut facts,
                    &Frames::past(&b.program, body),
                );
                for pl in places_of(&b.program.bodies[body.index()]) {
                    match alpha::alpha(&b.program, &mut tys, &mut facts, &mut roots, body, &pl) {
                        Ok(_) => ok += 1,
                        Err(AlphaError::NeedsValue { .. } | AlphaError::Later(_)) => later += 1,
                        Err(AlphaError::BadPlace(why)) => {
                            bad.push(format!("{}: {}: {pl:?}: {why}", f.display(), e.name));
                        }
                    }
                }
            }
            // Each edge joins two nodes of the table.
            let n = u32::try_from(table.len()).unwrap_or(u32::MAX);
            assert!(facts.cfg_edge.iter().all(|(x, y)| x.0 < n && y.0 < n));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    assert!(
        ok > 1000 && later > 0,
        "{ok} places, {later} for later stages"
    );
}

// ------------------------------------------------------- templates (F4)

/// Programs with no call: each statement kind of `docs/ir.md` 6.4 that a
/// body with no call can have.
const NO_CALLS: &str = "linear struct Tx { id: u64 }
struct P { a: u64, b: u64 }
struct H { o: Option<Tx> }

fn drop_behind(h: &H) / mut(h.o) {
    h.o = None
}

fn parts() {
    let p = (Tx { id: 1 }, Tx { id: 2 })
    let a = p.0
    let Tx(i) = a
    let Tx(j) = p.1
}

fn uninit_and_bounds(v: [u64; 3], i: usize) -> u64 {
    let x: u64
    x = v[i]
    x
}

fn holes() {
    let x = 1
    let y = 2
    let t = (&x, 1)
    t.0 = &y
    print(t.0)
    assert(x == 1)
}

fn reads() {
    let x = 1
    let r = &x
    print(r)
    x = 2
    let s = P { a: 1, b: 2 }
    s
}

fn shared(p: &P @ shared) / mut(p.a) {
    print(p.a)
}

fn logs() / log {
}

fn main() {
    let o = None
    match o {
        None => print(1),
        Some(t) => { let Tx(k) = t }
    }
}

struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }
struct Wrap { x: Frame, n: u64 }

fn built_in_place() {
    let w = Wrap { x: Frame { buf: [1, 2, 3, 4] }, n: 0 }
    w.x.cur = &w.x.buf[0]
    print(w.x.cur)
}

struct Two { a: Vec<u64>, b: Vec<u64> }

fn destructure(p: Two) {
    let Two(a, b) = p
}

fn two_lets(p: Two) {
    let a = p.a
    let b = p.b
}
";

/// The facts of body `name` of `src` from the `ir` pipeline.
fn ir_facts_with(src: &str, opts: Options, name: &str) -> FnFacts {
    let a = analyze_source(src, opts)
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let b = irbuild::build(&a);
    assert!(b.broken.is_empty(), "{:?}", b.broken);
    let i = b
        .entries
        .iter()
        .position(|e| e.name == name)
        .unwrap_or_else(|| panic!("no body `{name}`"));
    weft_sema::factgen::preview(&a, &b, i).unwrap_or_else(|u| panic!("`{name}`: {u}"))
}

/// The facts of body `name` of [`NO_CALLS`].
fn ir_facts(name: &str) -> FnFacts {
    ir_facts_with(NO_CALLS, Options::default(), name)
}

/// The node relations at each node: the name of each relation with the
/// node in it.
fn node_rels(f: &FnFacts) -> BTreeMap<NodeId, BTreeSet<&'static str>> {
    let mut m: BTreeMap<NodeId, BTreeSet<&'static str>> = BTreeMap::new();
    let mut add = |n: NodeId, r: &'static str| {
        m.entry(n).or_default().insert(r);
    };
    for &(a, _) in &f.cfg_edge {
        add(a, "cfg_edge");
    }
    for &(n, _) in &f.mutates_at {
        add(n, "mutates_at");
    }
    for &(n, _) in &f.reads_at {
        add(n, "reads_at");
    }
    for &(n, _) in &f.performs_at {
        add(n, "performs_at");
    }
    let vn: [(&'static str, &Vec<(VarId, NodeId)>); 10] = [
        ("rebound_at", &f.rebound_at),
        ("uses", &f.uses),
        ("moved_at", &f.moved_at),
        ("scope_end", &f.scope_end),
        ("overwrites", &f.overwrites),
        ("unset_at", &f.unset_at),
        ("empty_at", &f.empty_at),
        ("unwound_at", &f.unwound_at),
        ("rest_linear", &f.rest_linear),
        ("spared_at", &f.spared_at),
    ];
    for (name, rel) in vn {
        for &(v, n) in rel {
            // A version of a part binds again at each node where the part
            // does not hold its value (`factgen::holders`): not a fact of
            // the template of the node.
            if name == "rebound_at" && f.var(v).name.starts_with("value in `") {
                continue;
            }
            add(n, name);
        }
    }
    for &(n, _) in &f.writes_via {
        add(n, "writes_via");
    }
    for &(_, n) in &f.moved_part {
        add(n, "moved_part");
    }
    for &(n, _) in &f.releases_at {
        add(n, "releases_at");
    }
    for &n in &f.may_abort {
        add(n, "may_abort");
    }
    for &n in &f.multi_at {
        add(n, "multi_at");
    }
    for &n in &f.sim_run_at {
        add(n, "sim_run_at");
    }
    for &(n, _) in &f.ref_at {
        add(n, "ref_at");
    }
    for &(n, _) in &f.ref_in {
        add(n, "ref_in");
    }
    for &(n, _) in &f.lends_mut {
        add(n, "lends_mut");
    }
    for &(n, _, _) in f.call_mut.iter().chain(&f.call_arg) {
        add(n, "call");
    }
    for &(_, n) in f.spawned_at.iter().chain(&f.joined_at) {
        add(n, "task");
    }
    m
}

/// The relations that the template of each node label can emit
/// (`docs/ir.md` 6.4), and the relations that a cleanup path adds. `entry`
/// is the node where the parameters bind.
fn template_of(label: &str) -> Option<(&'static [&'static str], &'static [&'static str])> {
    Some(match label {
        "entry" => (&["cfg_edge", "rebound_at", "empty_at"], &[]),
        // `Live` of the temporary that the value of an assignment starts
        // with binds the `N` variables of the variant steps of the target
        // (stage F8d, `docs/ir.md` 6.3).
        "live" => (&["cfg_edge", "rebound_at"], &[]),
        "unwind continuation" | "goto" | "unreachable" | "unwind exit" => (&["cfg_edge"], &[]),
        "dead" => (&["cfg_edge", "scope_end"], &["unwound_at"]),
        "assign" => (
            &[
                "cfg_edge",
                "mutates_at",
                "reads_at",
                "rebound_at",
                "uses",
                "moved_at",
                "scope_end",
                "overwrites",
                "empty_at",
                "moved_part",
                "rest_linear",
                "writes_via",
                "sim_run_at",
                "ref_at",
                "ref_in",
                // A place field of a value built in place has no value in
                // its destination.
                "unset_at",
            ],
            &[],
        ),
        "drop" => (&["cfg_edge", "reads_at", "rebound_at", "uses"], &[]),
        // Not a use: a pattern moved the parts before it.
        "consume" => (&["cfg_edge", "moved_at", "moved_part", "rest_linear"], &[]),
        "uninit" => (&["cfg_edge", "unset_at"], &[]),
        "bounds" | "switch" | "print" => (&["cfg_edge", "reads_at", "uses"], &[]),
        "mention" => (&["cfg_edge", "uses"], &[]),
        // An `on abort` function: the summary of the function at the node,
        // with the root handlers (plan stage F7).
        "unwind value" => (
            &[
                "cfg_edge",
                "unwound_at",
                "reads_at",
                "mutates_at",
                "lends_mut",
            ],
            &[],
        ),
        "return" => (&["cfg_edge", "uses", "ref_at", "ref_in"], &[]),
        // The node with no edges of the W0605 check of an `Assign` or of a
        // struct literal (`ref_outside` reads it).
        "field" => (&["ref_at", "ref_in"], &[]),
        "assert" => (
            &["cfg_edge", "reads_at", "uses", "may_abort", "spared_at"],
            &[],
        ),
        // A call: the operands and the parts of the summary of the callee
        // (`docs/ir.md` 6.4); the callee frame root and a value that the
        // callee drops bind there.
        "call" => (
            &[
                "cfg_edge",
                "reads_at",
                "uses",
                "moved_at",
                "moved_part",
                "rest_linear",
                "mutates_at",
                "call",
                "lends_mut",
                "may_abort",
                "multi_at",
                "writes_via",
                "rebound_at",
                "overwrites",
            ],
            &[],
        ),
        // A perform through the capability of a caller (plan stage F6): the
        // operands, the places that the clause gets and can change, the
        // places of the callers, the effect, the abort.
        "perform" => (
            &[
                "cfg_edge",
                "reads_at",
                "uses",
                "moved_at",
                "moved_part",
                "rest_linear",
                "call",
                "lends_mut",
                "escapes_at",
                "may_abort",
                "multi_at",
                "overwrites",
            ],
            &[],
        ),
        // The result binds.
        "perform ret" => (
            &[
                "cfg_edge",
                "rebound_at",
                "empty_at",
                "uses",
                "moved_at",
                "moved_part",
                "rest_linear",
                "mutates_at",
                "reads_at",
                "overwrites",
                "writes_via",
            ],
            &[],
        ),
        // The result binds; a held argument moves; a value that the callee
        // drops ends.
        "call ret" => (
            &[
                "cfg_edge",
                "rebound_at",
                "empty_at",
                "uses",
                "moved_at",
                "moved_part",
                "rest_linear",
                "mutates_at",
                "reads_at",
                "overwrites",
                "writes_via",
                "scope_end",
            ],
            &[],
        ),
        "call frame end" => (&["cfg_edge", "scope_end"], &[]),
        "call frame end (abort)" => (&["cfg_edge", "scope_end", "unwound_at"], &[]),
        _ => return None,
    })
}

/// Checks that each node of `f` emits only the relations of the template of
/// its label. Returns the relations of each label.
fn check_templates(f: &FnFacts, what: &str) -> BTreeMap<String, BTreeSet<&'static str>> {
    let mut seen: BTreeMap<String, BTreeSet<&'static str>> = BTreeMap::new();
    for (n, rels) in node_rels(f) {
        let label = f.node(n).label.clone();
        let (normal, cleanup) =
            template_of(&label).unwrap_or_else(|| panic!("{what}: no template for `{label}`"));
        for r in &rels {
            assert!(
                normal.contains(r) || cleanup.contains(r),
                "{what}: `{label}` emits {r}"
            );
        }
        seen.entry(label).or_default().extend(rels);
    }
    seen
}

/// The variable named `name`.
fn var_named(f: &FnFacts, name: &str) -> VarId {
    let i = f
        .vars
        .iter()
        .position(|v| v.name == name)
        .unwrap_or_else(|| panic!("no variable `{name}`"));
    VarId(id(i))
}

/// The display texts of the places that variable `v` points into.
fn points(f: &FnFacts, v: VarId) -> BTreeSet<String> {
    f.points_into
        .iter()
        .filter(|(x, _)| *x == v)
        .map(|(_, p)| f.place(*p).display.clone())
        .collect()
}

/// The nodes with label `label`.
fn nodes_labelled(f: &FnFacts, label: &str) -> Vec<NodeId> {
    (0..f.nodes.len())
        .filter(|&i| f.nodes[i].label == label)
        .map(|i| NodeId(id(i)))
        .collect()
}

/// The display texts of the places that node `n` reads.
fn reads(f: &FnFacts, n: NodeId) -> BTreeSet<String> {
    f.reads_at
        .iter()
        .filter(|(x, _)| *x == n)
        .map(|(_, p)| f.place(*p).display.clone())
        .collect()
}

/// The display texts of the places that node `n` mutates.
fn mutates(f: &FnFacts, n: NodeId) -> BTreeSet<String> {
    f.mutates_at
        .iter()
        .filter(|(x, _)| *x == n)
        .map(|(_, p)| f.place(*p).display.clone())
        .collect()
}

/// True if the pair `(v, n)` is in `rel`.
fn has(rel: &[(VarId, NodeId)], v: VarId, n: NodeId) -> bool {
    rel.contains(&(v, n))
}

#[test]
fn each_statement_kind_emits_the_relations_of_its_template() {
    let mut seen: BTreeMap<String, BTreeSet<&'static str>> = BTreeMap::new();
    for name in [
        "drop_behind",
        "parts",
        "uninit_and_bounds",
        "holes",
        "reads",
        "shared",
        "logs",
        "main",
        "built_in_place",
        "destructure",
        "two_lets",
    ] {
        let f = ir_facts(name);
        for (l, rs) in check_templates(&f, name) {
            seen.entry(l).or_default().extend(rs);
        }
    }
    // Each statement kind of these bodies emits the relations that make it
    // what it is.
    for (label, rels) in [
        ("entry", &["rebound_at"][..]),
        ("dead", &["scope_end", "unwound_at"]),
        (
            "assign",
            &[
                "rebound_at",
                "uses",
                "reads_at",
                "moved_at",
                "moved_part",
                "rest_linear",
                "mutates_at",
                "empty_at",
                "scope_end",
                "unset_at",
            ],
        ),
        ("drop", &["rebound_at", "uses", "reads_at"]),
        ("consume", &["moved_at"]),
        ("uninit", &["unset_at"]),
        ("bounds", &["reads_at", "uses"]),
        ("print", &["reads_at", "uses"]),
        ("switch", &["reads_at", "uses"]),
        ("return", &["uses"]),
        ("assert", &["uses", "reads_at", "may_abort"]),
    ] {
        let have = seen.get(label).cloned().unwrap_or_default();
        for r in rels {
            assert!(have.contains(r), "no `{label}` node emits {r}: {have:?}");
        }
    }
}

#[test]
fn dead_ends_the_value_and_a_cleanup_path_unwinds_it() {
    let f = ir_facts("holes");
    let t = var_named(&f, "t");
    let deads = nodes_labelled(&f, "dead");
    let ends = deads.iter().filter(|&&n| has(&f.scope_end, t, n)).count();
    let unwinds: Vec<NodeId> = deads
        .iter()
        .copied()
        .filter(|&n| has(&f.unwound_at, t, n))
        .collect();
    assert_eq!(ends, 1, "`Dead(t)` on the normal path");
    assert_eq!(
        unwinds.len(),
        1,
        "`Dead(t)` on the cleanup path of `assert`"
    );
    // The cleanup path has no `scope_end`.
    assert!(!has(&f.scope_end, t, unwinds[0]));
    // A value that is not plain data ends at its `Dead` too.
    let f = ir_facts("parts");
    let a = var_named(&f, "a");
    assert!(nodes_labelled(&f, "dead")
        .iter()
        .any(|&n| has(&f.scope_end, a, n)));
}

#[test]
fn return_uses_the_result() {
    let f = ir_facts("uninit_and_bounds");
    let r = var_named(&f, "the result");
    let rets = nodes_labelled(&f, "return");
    assert!(
        rets.iter().any(|&n| has(&f.uses, r, n)),
        "`Return` uses `_0`"
    );
    // The value of the result binds where it is written.
    assert!(f.rebound_at.iter().any(|(v, _)| *v == r));
}

#[test]
fn a_part_move_moves_the_whole_local_and_leaves_its_linear_rest() {
    let f = ir_facts("parts");
    let p = var_named(&f, "p");
    let n = f
        .moved_part
        .iter()
        .find(|(m, _)| f.place(*m).display == "p.0")
        .map(|(_, n)| *n)
        .expect("a move of `p.0`");
    assert!(has(&f.moved_at, p, n), "moved_at of the whole local");
    assert!(has(&f.uses, p, n));
    assert!(has(&f.rest_linear, p, n), "`p.1` can hold a linear value");
    // `Consume(p.1)` of the pattern finishes the last part: no linear rest.
    let c = nodes_labelled(&f, "consume");
    let last = c
        .iter()
        .copied()
        .find(|&n| {
            f.moved_part
                .iter()
                .any(|(m, x)| *x == n && f.place(*m).display == "p.1")
        })
        .expect("a consume of `p.1`");
    assert!(has(&f.moved_at, p, last));
    assert!(!has(&f.rest_linear, p, last));
}

#[test]
fn a_drop_behind_a_reference_is_a_drop_pair_that_ends_at_the_assign() {
    let f = ir_facts("drop_behind");
    let drop = nodes_labelled(&f, "drop");
    assert_eq!(drop.len(), 1);
    let pair: Vec<VarId> = f
        .rebound_at
        .iter()
        .filter(|(_, n)| *n == drop[0])
        .map(|(v, _)| *v)
        .collect();
    assert_eq!(pair.len(), 1, "one drop pair variable");
    let d = pair[0];
    assert!(f.var(d).linear, "the old value can be linear");
    assert!(!f.empty_at.contains(&(d, drop[0])));
    // The pair ends at the `Assign` right after the `Drop`.
    let next = f
        .cfg_edge
        .iter()
        .find(|(a, _)| *a == drop[0])
        .map(|(_, b)| *b)
        .expect("an edge out of the drop");
    assert_eq!(f.node(next).label, "assign");
    assert!(has(&f.scope_end, d, next));
    // The `Assign` changes the place behind the reference.
    assert_eq!(mutates(&f, next), BTreeSet::from(["h.o".to_string()]));
    // The drop reads the reference.
    assert!(reads(&f, drop[0]).contains("h"));
}

#[test]
fn print_of_a_reference_reads_through_it() {
    let f = ir_facts("reads");
    let prints = nodes_labelled(&f, "print");
    assert_eq!(prints.len(), 1);
    let rd = reads(&f, prints[0]);
    assert!(rd.contains("x"), "reads the place behind `r`: {rd:?}");
    assert!(rd.contains("r"), "reads `r`: {rd:?}");
    assert!(has(&f.uses, var_named(&f, "r"), prints[0]));
}

#[test]
fn the_first_value_writes_nothing_and_an_overwrite_mutates_the_root() {
    let f = ir_facts("reads");
    let x = var_named(&f, "x");
    let binds: Vec<NodeId> = f
        .rebound_at
        .iter()
        .filter(|(v, _)| *v == x)
        .map(|(_, n)| *n)
        .collect();
    assert_eq!(binds.len(), 2, "`let x = 1` and `x = 2`");
    let muts: Vec<BTreeSet<String>> = binds.iter().map(|&n| mutates(&f, n)).collect();
    assert_eq!(
        muts.iter().filter(|m| m.is_empty()).count(),
        1,
        "the first value writes nothing: {muts:?}"
    );
    assert!(
        muts.iter().any(|m| m.contains("x")),
        "the overwrite mutates the root of `x`: {muts:?}"
    );
    // A temporary is not a source local: its value writes nothing.
    for (v, n) in &f.rebound_at {
        if f.var(*v).kind == weft_facts::VarKind::Temp {
            let m = mutates(&f, *n);
            assert!(m.is_empty(), "a temporary mutates {m:?}");
        }
    }
}

#[test]
fn a_new_value_of_a_part_with_a_variable_replaces_its_places() {
    let f = ir_facts("holes");
    let t = var_named(&f, "t");
    // Each value of the part has a version of the variable of the part
    // (`factgen::holders`): `(&x, 1)` and `&y`.
    let versions: Vec<VarId> = (0..f.vars.len())
        .map(|i| VarId(id(i)))
        .filter(|&v| f.var(v).name == "value in `t.0`")
        .collect();
    assert_eq!(versions.len(), 2, "{versions:?}");
    let of = |place: &str| {
        versions
            .iter()
            .copied()
            .find(|&v| points(&f, v) == BTreeSet::from([place.to_string()]))
            .unwrap_or_else(|| panic!("no version points into `{place}`"))
    };
    let (tx, ty) = (of("x"), of("y"));
    // The whole local holds no place of the part.
    assert!(points(&f, t).is_empty(), "{:?}", points(&f, t));
    // A new value of the whole and of the part rebinds each version.
    let assigns = nodes_labelled(&f, "assign");
    let whole = assigns
        .iter()
        .copied()
        .find(|&n| has(&f.rebound_at, t, n))
        .expect("the assignment of `t`");
    let part = assigns
        .iter()
        .copied()
        .find(|&n| mutates(&f, n) == BTreeSet::from(["t.0".to_string()]))
        .expect("the part assignment");
    for n in [whole, part] {
        assert!(has(&f.rebound_at, tx, n) && has(&f.rebound_at, ty, n));
    }
    // The part assignment uses the whole local.
    assert!(has(&f.uses, t, part));
    assert!(!has(&f.rebound_at, t, part));
    // A read of the part uses the whole local and the version of the value
    // that the part holds there. The old value binds again: its state does
    // not go on.
    let print = nodes_labelled(&f, "print");
    assert!(has(&f.uses, ty, print[0]) && has(&f.uses, t, print[0]));
    assert!(!has(&f.uses, tx, print[0]));
    assert!(has(&f.rebound_at, tx, print[0]));
}

#[test]
fn a_place_field_of_a_value_built_in_place_goes_with_the_value() {
    let f = ir_facts("built_in_place");
    // The `U` variable of `w.x.cur` (the `H` variable has the same name).
    let (cur, _) = *f
        .unset_at
        .iter()
        .find(|(v, _)| f.var(*v).name == "w.x.cur")
        .expect("an unset place field `w.x.cur`");
    // The construction of `w` gives `w.x.cur` no value.
    let unset: Vec<NodeId> = f
        .unset_at
        .iter()
        .filter(|(v, _)| *v == cur)
        .map(|(_, n)| *n)
        .collect();
    assert_eq!(unset.len(), 1);
    assert_eq!(f.node(unset[0]).label, "assign");
    assert!(!has(&f.rebound_at, cur, unset[0]));
    // The move of the frame into `w` reads no place field of the frame.
    let inner = var_named(&f, "operand temporary.cur");
    assert!(!f.uses.iter().any(|(v, _)| *v == inner));
    // The temporary is built in place: its move is not W0604.
    let moved_temps: Vec<VarId> = f
        .moved_at
        .iter()
        .map(|(v, _)| *v)
        .filter(|v| f.var(*v).kind == weft_facts::VarKind::Temp)
        .collect();
    assert!(moved_temps.iter().all(|v| !f.var(*v).immovable));
    // The new value of the field, then a read that uses it.
    assert!(f
        .rebound_at
        .iter()
        .any(|(v, n)| *v == cur && *n != unset[0]));
    let print = nodes_labelled(&f, "print");
    assert!(has(&f.uses, cur, print[0]));
}

#[test]
fn the_binds_of_one_pattern_move_the_value_once() {
    // `let Two(a, b) = p`: the first bind uses `p` and moves it; the
    // second bind is not a use after a move.
    let f = ir_facts("destructure");
    let p = var_named(&f, "p");
    let uses: BTreeSet<NodeId> = f
        .uses
        .iter()
        .filter(|(v, _)| *v == p)
        .map(|(_, n)| *n)
        .collect();
    let moves: BTreeSet<NodeId> = f
        .moved_at
        .iter()
        .filter(|(v, _)| *v == p)
        .map(|(_, n)| *n)
        .collect();
    assert_eq!(moves.len(), 2, "two part moves");
    assert_eq!(uses.len(), 1, "one use: {uses:?}");
    assert!(moves.contains(uses.iter().next().expect("a use")));
    // `let a = p.a; let b = p.b`: two statements, so the second is a use
    // after a move (W0302 keeps its meaning).
    let f = ir_facts("two_lets");
    let p = var_named(&f, "p");
    let uses = f.uses.iter().filter(|(v, _)| *v == p).count();
    assert_eq!(uses, 2);
}

#[test]
fn the_relations_with_no_node_come_from_the_declarations() {
    // `has_signature`, `declared_mut`, `shared_root`.
    let f = ir_facts("shared");
    assert!(f.has_signature);
    let dm: Vec<String> = f
        .declared_mut
        .iter()
        .map(|p| f.place(*p).display.clone())
        .collect();
    assert_eq!(dm, vec!["p.a".to_string()]);
    let sr: Vec<String> = f
        .shared_root
        .iter()
        .map(|p| f.place(*p).display.clone())
        .collect();
    assert_eq!(sr, vec!["p".to_string()]);
    assert!(f.param_rooted(f.declared_mut[0]));
    let plain = ir_facts("parts");
    assert!(!plain.has_signature && plain.declared_mut.is_empty());
    assert!(plain.shared_root.is_empty());
    // `declared_effect` and `std_effect`.
    let f = ir_facts("logs");
    assert!(f.declared_effect.contains(&"Log".to_string()));
    assert!(f.std_effects.contains(&"Log".to_string()));
    // `started` for `main`, `no_runtime` with the marker, `library` with the
    // marker.
    assert!(ir_facts("main").started);
    assert!(!ir_facts("parts").started);
    let src = format!("// weft: no-runtime\n{NO_CALLS}");
    let f = ir_facts_with(&src, Options::from_markers(&src), "main");
    assert!(f.no_runtime && f.started);
    let src = format!("// weft: library\n{NO_CALLS}");
    let f = ir_facts_with(&src, Options::from_markers(&src), "parts");
    assert!(f.library);
    assert!(!ir_facts("parts").library);
    // `task` and `fork_task`: one task for each spawn site and each branch
    // of a `fork`.
    let src = "fn work() -> u64 { 1 }
fn main() {
    let x = scope { s =>
        let h = s.spawn(|| work())
        h.join()
    }
    let (a, b) = fork(|| work(), || work())
}
";
    let (_, b) = built(src);
    let m = body_of(&b, "main");
    let comp = weft_sema::factgen::component(&b, m);
    let mut facts = FnFacts::default();
    let tasks = weft_sema::factgen::decls::tasks(&b.program, &comp, &mut facts);
    let kinds: Vec<weft_facts::TaskKind> = facts.tasks.iter().map(|t| t.kind).collect();
    assert_eq!(
        kinds,
        vec![
            weft_facts::TaskKind::Spawn,
            weft_facts::TaskKind::Fork,
            weft_facts::TaskKind::Fork
        ]
    );
    assert_eq!(tasks.len(), 3);
}

#[test]
fn writes_via_needs_one_place_at_or_above_each_change() {
    use weft_sema::factgen::kernel::{self, Access};
    let a = Access {
        vars: vec![VarId(0)],
        places: vec![PlaceId(5)],
        ptrs: vec![PlaceId(1)],
        root: None,
    };
    // The place 5 is below the place 4.
    let below = |m: PlaceId, d: PlaceId| m == d || (m == PlaceId(5) && d == PlaceId(4));
    let f = kernel::write_through(&a, Some((VarId(0), PlaceId(4))), &below);
    assert_eq!(f.writes_via, vec![VarId(0)]);
    assert_eq!(f.mutates, vec![PlaceId(5)]);
    assert_eq!(f.uses, vec![VarId(0)]);
    assert_eq!(f.reads, vec![PlaceId(1)]);
    // A change outside the place: no `writes_via`.
    let f = kernel::write_through(&a, Some((VarId(0), PlaceId(7))), &below);
    assert!(f.writes_via.is_empty());
    // The reference does not hold one place.
    let f = kernel::write_through(&a, None, &below);
    assert!(f.writes_via.is_empty());
    // A borrow uses the variables, reads the pointers, and gives the places.
    let (f, refs) = kernel::borrow(&a, &[PlaceId(9)]);
    assert_eq!(refs, vec![PlaceId(5), PlaceId(9)]);
    assert_eq!(f.reads, vec![PlaceId(1)]);
    assert!(f.mutates.is_empty());
    // A copy of a reference points into its places.
    let f = kernel::copy_ref(&[VarId(2)], &[PlaceId(5)]);
    assert_eq!(f.points_into, vec![(VarId(2), PlaceId(5))]);
}

/// On each program of the corpus: each body with no call gets the facts of
/// the templates, and no other relation.
#[test]
fn the_templates_run_on_the_bodies_with_no_call_of_the_corpus() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("the corpus")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wf"))
        .collect();
    files.sort();
    let (mut ok, mut later) = (0usize, 0usize);
    for f in &files {
        let src = std::fs::read_to_string(f).expect("read");
        let Ok(a) = analyze_source(&src, Options::from_markers(&src)) else {
            continue;
        };
        let b = irbuild::build(&a);
        for (i, e) in b.entries.iter().enumerate() {
            if !matches!(e.outcome, Outcome::Built(_)) {
                continue;
            }
            match weft_sema::factgen::preview(&a, &b, i) {
                Ok(facts) => {
                    ok += 1;
                    check_templates(&facts, &format!("{}: {}", f.display(), e.name));
                }
                Err(_) => later += 1,
            }
        }
    }
    eprintln!("{ok} bodies with facts, {later} for later stages");
    assert!(
        ok > 100 && later > 0,
        "{ok} bodies, {later} for later stages"
    );
}

// ---------------------------------------------------------- calls (F5)

/// Programs with calls of functions whose summary comes from a signature:
/// the prelude, an extern function, a function with a stated row.
const CALLS: &str = "linear struct Tx { id: u64 }
struct Entity { hp: i32 }
struct World { entities: Vec<Entity> }

fn vec_calls() {
    let v = Vec.new()
    v.push(1)
    let n = v.len()
    v.clear()
    print(n)
}

fn invalidates(world: &World) / mut(world.entities) {
    let first = &world.entities[0]
    world.entities.push(Entity { hp: 10 })
    print(first.hp)
}

fn via(v: &Vec<u64>) / mut(v) {
    v.push(1)
}

extern fn keep<T>(x: T) / log

fn holds(t: Tx) / log {
    keep(t)
}

extern fn mk() -> u64

fn frame() {
    let a = mk()
    print(a)
}

fn extend(dst: &Vec<&Entity>, src: &Vec<&Entity>) / mut(dst) {
    dst.push(src[0])
}

fn typed_flow(x: &Entity) {
    let all = Vec.new()
    let some = Vec.new()
    some.push(x)
    extend(&all, &some)
    print(all.len())
}

fn keeps_ref(rs: &Vec<&u64>) / mut(rs) {
    let x = 1
    rs.push(&x)
}
";

/// The facts of body `name` of [`CALLS`].
fn call_facts(name: &str) -> FnFacts {
    ir_facts_with(CALLS, Options::default(), name)
}

/// The node with label `label` on the line of the first node with label
/// `call` whose span starts at or after `from`.
fn call_phase(f: &FnFacts, label: &str, nth: usize) -> NodeId {
    let nodes = nodes_labelled(f, label);
    *nodes
        .get(nth)
        .unwrap_or_else(|| panic!("no node `{label}` number {nth}: {nodes:?}"))
}

#[test]
fn the_prelude_calls_of_a_vec_give_the_changes_and_reads_of_their_signatures() {
    let f = call_facts("vec_calls");
    check_templates(&f, "vec_calls");
    let calls = nodes_labelled(&f, "call");
    // `Vec.new`, `push`, `len`, `clear`.
    assert_eq!(calls.len(), 4, "{calls:?}");
    let v: BTreeSet<String> = std::iter::once("v".to_string()).collect();
    assert!(mutates(&f, calls[0]).is_empty());
    assert_eq!(mutates(&f, calls[1]), v, "`push` changes `v`");
    assert!(mutates(&f, calls[2]).is_empty(), "`len` changes nothing");
    assert_eq!(mutates(&f, calls[3]), v, "`clear` changes `v`");
    for &n in &calls[1..] {
        assert!(reads(&f, n).contains("v"), "a method reads its receiver");
        assert!(f
            .call_arg
            .iter()
            .any(|&(m, p, r)| m == n && r == 0 && f.place(p).display == "v"));
    }
    assert!(f
        .call_mut
        .iter()
        .any(|&(m, p, r)| m == calls[1] && r == 0 && f.place(p).display == "v"));
    // No prelude call of the body can abort.
    assert!(f.may_abort.is_empty());
}

#[test]
fn the_result_binds_at_ret() {
    let f = call_facts("vec_calls");
    let n = var_named(&f, "n");
    let rets = nodes_labelled(&f, "call ret");
    // The result of `len` binds `n` at its `Ret` node, not at `Main`.
    let len_ret = rets[2];
    assert!(has(&f.rebound_at, n, len_ret), "{:?}", f.rebound_at);
    assert!(has(&f.empty_at, n, len_ret));
    let main = call_phase(&f, "call", 2);
    assert!(!has(&f.rebound_at, n, main));
    assert!(f.cfg_edge.contains(&(main, len_ret)));
}

#[test]
fn a_change_of_a_place_invalidates_a_reference_into_it() {
    let f = call_facts("invalidates");
    let first = var_named(&f, "first");
    assert!(points(&f, first).contains("world.entities[]"));
    let push = call_phase(&f, "call", 0);
    assert_eq!(
        mutates(&f, push),
        std::iter::once("world.entities".to_string()).collect()
    );
}

#[test]
fn writes_via_at_a_method_call_through_one_reference() {
    let f = call_facts("via");
    let v = var_named(&f, "v");
    let push = call_phase(&f, "call", 0);
    assert!(f.writes_via.contains(&(push, v)), "{:?}", f.writes_via);
    // The body with a reference of a place that the call changes gets no
    // `writes_via` for a local that is not a reference.
    let g = call_facts("vec_calls");
    assert!(g.writes_via.is_empty(), "{:?}", g.writes_via);
}

#[test]
fn a_held_argument_moves_at_ret() {
    let f = call_facts("holds");
    let t = var_named(&f, "t");
    let main = call_phase(&f, "call", 0);
    let ret = call_phase(&f, "call ret", 0);
    assert!(has(&f.uses, t, main), "the call reads its argument");
    assert!(
        !has(&f.moved_at, t, main),
        "a held argument stays live at `Main`"
    );
    assert!(has(&f.moved_at, t, ret), "{:?}", f.moved_at);
    // The callee can abort (`log`), so the value is live across an abort.
    assert!(f.may_abort.contains(&main));
    assert!(f.escapes_at.iter().any(|(n, e)| *n == main && e == "Log"));
    // `keep` can drop a value of its type parameter: a linear type argument
    // goes away at the call (W0601).
    let dropped: Vec<VarId> = (0..f.vars.len())
        .filter(|&i| f.vars[i].kind == weft_facts::VarKind::Dropped)
        .map(|i| VarId(id(i)))
        .collect();
    assert_eq!(dropped.len(), 1, "{:?}", f.vars);
    assert!(has(&f.rebound_at, dropped[0], main));
    assert!(has(&f.scope_end, dropped[0], ret));
}

#[test]
fn a_callee_frame_place_in_a_result_ends_at_frame_end() {
    use weft_sema::analysis::summary::{IPlace, IRoot};
    let a = analyze_source(CALLS, Options::default())
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let b = irbuild::build(&a);
    let i = b
        .entries
        .iter()
        .position(|e| e.name == "frame")
        .unwrap_or_else(|| panic!("no body `frame`"));
    let Outcome::Built(entry) = b.entries[i].outcome else {
        panic!("`frame` has no IR");
    };
    // A summary of `mk` whose result points into a local of `mk`.
    let mut sums = weft_sema::factgen::summaries(&a, &b);
    let mk = b
        .program
        .fns
        .iter()
        .position(|d| d.name.ends_with("mk"))
        .unwrap_or_else(|| panic!("no function `mk`"));
    let mk = weft_ir::FnId(id(mk));
    let mut s = sums.get(mk).cloned().unwrap_or_else(|e| panic!("{e}"));
    s.ret.places.push(IPlace::root(IRoot::Frame));
    sums.insert(mk, Ok(s));
    let mut f = FnFacts::default();
    weft_sema::factgen::emit_body(&a, &b, &sums, i, entry, &mut f)
        .unwrap_or_else(|u| panic!("{u}"));
    let main = call_phase(&f, "call", 0);
    let fe = call_phase(&f, "call frame end", 0);
    let frame = (0..f.vars.len())
        .find(|&i| f.vars[i].name.starts_with("a local of"))
        .map_or_else(
            || panic!("no frame variable: {:?}", f.vars),
            |i| VarId(id(i)),
        );
    assert!(has(&f.rebound_at, frame, main));
    assert!(has(&f.scope_end, frame, fe));
    let x = var_named(&f, "a");
    assert!(
        points(&f, x).iter().any(|p| p.starts_with("a local of")),
        "{:?}",
        points(&f, x)
    );
}

#[test]
fn a_changed_argument_keeps_only_the_references_that_its_type_can_hold() {
    // R3RT6: `extend(&all, &some)` gives `all` the references in `some`, not
    // a reference into `some`.
    let f = call_facts("typed_flow");
    let all = var_named(&f, "all");
    let p = points(&f, all);
    assert!(!p.iter().any(|x| x.starts_with("some")), "{p:?}");
    assert!(p.contains("x"), "{p:?}");
    // `rs.push(&x)` (ADR 0003): a vector of references keeps the reference.
    let g = call_facts("keeps_ref");
    let push = call_phase(&g, "call", 0);
    assert!(mutates(&g, push).contains("rs"));
}

#[test]
fn a_reference_into_a_local_behind_a_reference_parameter_is_w0204() {
    let src = "fn keeps_ref(rs: &Vec<&u64>) / mut(rs) {
    let x = 1
    rs.push(&x)
}
";
    let a = analyze_source(
        src,
        Options {
            facts: weft_sema::FactGen::Ir,
            ir_groups: weft_sema::Groups::of(weft_sema::Group::A),
            ..Options::default()
        },
    )
    .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let w0204: Vec<String> = a
        .diags
        .iter()
        .filter(|d| d.code == weft_syntax::diag::Code::W0204)
        .map(|d| d.message.clone())
        .collect();
    // The `ir` pipeline checks the program: the old lowering does not give
    // the diagnostic.
    assert!(
        a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope),
        "{:?}",
        a.ir_scope
    );
    assert_eq!(w0204.len(), 1, "{w0204:?}");
    assert!(
        w0204[0].contains("keeps_ref") && w0204[0].contains("`x`"),
        "{w0204:?}"
    );
}

/// R3RT2: a read through a reference uses the variables of the places that
/// it reads through and of the references that it copies out.
const THROUGH: &str = "struct Entity { hp: i32 }
struct World { entities: Vec<Entity> }
struct Wrap<T> { x: T }

fn ref_to_option(world: &World) / mut(world.entities) {
    let o = Some(&world.entities[0])
    let p = &o
    world.entities.clear()
    match p { Some(e) => print(e.hp), None => {} }
}

fn control_field(world: &World) / mut(world.entities) {
    let w = Wrap { x: &world.entities[0] }
    let p = &w
    world.entities.clear()
    print(p.x.hp)
}

fn nested_ref() {
    let v: Vec<u64> = Vec.new()
    v.push(1)
    let t = (&v[0], 1)
    let rt = &t
    v.clear()
    let (a, b) = rt
    print(a)
}
";

#[test]
fn a_read_through_a_reference_uses_the_variables_of_what_it_reads() {
    // `print(p.x.hp)` reads through the reference in `w.x`: it uses `w`.
    let f = ir_facts_with(THROUGH, Options::default(), "control_field");
    let w = var_named(&f, "w");
    let print = nodes_labelled(&f, "print");
    assert!(print.iter().any(|&n| has(&f.uses, w, n)), "{:?}", f.uses);
    // `e = copy ((*p) as Some).0` copies the reference that `o` holds: it
    // uses `o`, whose places the call changed.
    let g = ir_facts_with(THROUGH, Options::default(), "ref_to_option");
    let o = var_named(&g, "o");
    let e = var_named(&g, "e");
    let bind = (0..g.nodes.len())
        .map(|i| NodeId(id(i)))
        .find(|&n| has(&g.rebound_at, e, n))
        .unwrap_or_else(|| panic!("no bind of `e`"));
    assert!(has(&g.uses, o, bind), "{:?}", g.uses);
    // `let (a, b) = rt` binds `a` by reference: `a = &(*rt).0` borrows a
    // reference that `t` holds, and uses `t`.
    let h = ir_facts_with(THROUGH, Options::default(), "nested_ref");
    let t = var_named(&h, "t");
    let a = var_named(&h, "a");
    let bind = (0..h.nodes.len())
        .map(|i| NodeId(id(i)))
        .find(|&n| has(&h.rebound_at, a, n))
        .unwrap_or_else(|| panic!("no bind of `a`"));
    assert!(has(&h.uses, t, bind), "{:?}", h.uses);
}

#[test]
fn an_argument_reaches_the_places_of_the_references_behind_it() {
    // R3RT3: `clear_then(&o, world)` gives the callee the places that the
    // reference in `o` points into, with the root of its parameter.
    let src = "struct Entity { hp: i32 }
struct World { entities: Vec<Entity> }
fn clear_then(o: &Option<&Entity>, w: &World) / mut(w.entities) {
    w.entities.clear()
}
fn callee_side(world: &World) / mut(world.entities) {
    let o = Some(&world.entities[0])
    clear_then(&o, world)
}
";
    let f = ir_facts_with(src, Options::default(), "callee_side");
    let call = nodes_labelled(&f, "call")[0];
    let args: BTreeSet<(String, u32)> = f
        .call_arg
        .iter()
        .filter(|(n, _, _)| *n == call)
        .map(|&(_, p, r)| (f.place(p).display.clone(), r))
        .collect();
    assert!(args.contains(&("o".to_string(), 0)), "{args:?}");
    assert!(
        args.contains(&("world.entities[]".to_string(), 0)),
        "{args:?}"
    );
    assert!(
        f.call_mut
            .iter()
            .any(|&(n, p, r)| n == call && r == 1 && f.place(p).display == "world.entities"),
        "{:?}",
        f.call_mut
    );
}

#[test]
fn a_value_that_a_call_builds_in_place_does_not_read_its_place_fields() {
    // `Box.new(Frame { .. })`: the call result goes into `h` with its place
    // field `cur` that has no value (`docs/ir.md` 5.17, 5.36); the move of
    // the result into the literal does not read it. W0304 comes at the read
    // of `h.b.cur`, as in the old pipeline.
    let src = "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }
struct Hold { b: Box<Frame> }
fn one_box() {
    let h = Hold { b: Box.new(Frame { buf: [1, 2, 3, 4] }) }
    print(h.b.cur)
}
";
    let f = ir_facts_with(src, Options::default(), "one_box");
    let unset: BTreeSet<VarId> = f.unset_at.iter().map(|&(v, _)| v).collect();
    let read: Vec<(String, String)> = f
        .uses
        .iter()
        .filter(|&&(v, _)| unset.contains(&v))
        .map(|&(v, n)| (f.var(v).name.clone(), f.node(n).label.clone()))
        .collect();
    // Only the `print` reads a place field with no value: `h.b.cur`.
    assert!(
        read.iter().all(|(v, l)| l == "print" && v == "h.b.cur"),
        "{read:?}"
    );
    assert!(read.iter().any(|(v, _)| v == "h.b.cur"), "{read:?}");
}

#[test]
fn a_store_through_a_box_gives_its_place_field_a_value() {
    // `docs/ir.md` 5.8: the place fields of a boxed value are paths through
    // `Deref(Box)`. A read of `b.buf[0]` does not read `b.cur`, and a store
    // into `b.cur` gives it a value.
    let src = "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }
fn boxed_in_place() {
    let b = Box.new(Frame { buf: [1, 2, 3, 4] })
    b.cur = &b.buf[0]
    print(b.cur)
}
";
    let f = ir_facts_with(src, Options::default(), "boxed_in_place");
    let cur = (0..f.vars.len())
        .find(|&i| f.vars[i].name == "b.cur")
        .map_or_else(
            || panic!("no variable `b.cur`: {:?}", f.vars),
            |i| VarId(id(i)),
        );
    let store = (0..f.nodes.len())
        .map(|i| NodeId(id(i)))
        .find(|&n| f.node(n).label == "assign" && has(&f.rebound_at, cur, n));
    let store = store.unwrap_or_else(|| panic!("no store gives `b.cur` a value"));
    // The store reads `b.buf[0]` and not `b.cur`.
    assert!(!has(&f.uses, cur, store), "{:?}", f.uses);
}

#[test]
fn a_value_that_a_call_argument_moves_keeps_its_place() {
    // A `Vec` moves its elements when its buffer grows: a `!Move` literal
    // that goes to `push` moves (W0604), as in the old pipeline. `Box.new`
    // builds its argument in place.
    let src = "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }
fn in_vec() {
    let v = Vec.new()
    v.push(Frame { buf: [1, 2, 3, 4] })
}
fn in_box() {
    let b = Box.new(Frame { buf: [1, 2, 3, 4] })
}
";
    let frames = |f: &FnFacts| -> Vec<VarId> {
        (0..f.vars.len())
            .filter(|&i| f.vars[i].ty == "Frame")
            .map(|i| VarId(id(i)))
            .collect()
    };
    let f = ir_facts_with(src, Options::default(), "in_vec");
    let push = nodes_labelled(&f, "call")[1];
    let moved: Vec<VarId> = frames(&f)
        .into_iter()
        .filter(|&v| has(&f.moved_at, v, push))
        .collect();
    assert_eq!(moved.len(), 1, "{:?}", f.vars);
    assert!(f.var(moved[0]).immovable, "{:?}", f.var(moved[0]));
    let g = ir_facts_with(src, Options::default(), "in_box");
    assert!(
        frames(&g).iter().all(|&v| !g.var(v).immovable),
        "{:?}",
        g.vars
    );
}

#[test]
fn a_type_argument_that_is_a_reference_gives_the_places_behind_it() {
    // `rss.push(&rs)`: `T` is `&Vec<&Counter>`, so `rss` gets the places
    // behind `rs` too, and `mut(rss..)` changes them (`verify/s5/diff/p/v4a`).
    let src = "struct Counter { items: Vec<u64> }
fn grow2(rss: &Vec<&Vec<&Counter>>) / mut(rss..) {
    let rs = rss[0]
    let c = rs[0]
    c.items.clear()
}
fn two_levels() {
    let c = Counter { items: Vec.new() }
    let rs = Vec.new()
    rs.push(&c)
    let rss = Vec.new()
    rss.push(&rs)
    grow2(&rss)
}
";
    let f = ir_facts_with(src, Options::default(), "two_levels");
    let rss = var_named(&f, "rss");
    assert!(points(&f, rss).contains("c"), "{:?}", points(&f, rss));
    let grow = *nodes_labelled(&f, "call")
        .last()
        .unwrap_or_else(|| panic!("no call"));
    assert!(
        mutates(&f, grow).iter().any(|m| m.starts_with('c')),
        "{:?}",
        mutates(&f, grow)
    );
}

// ------------------------------------------- aborts past the function (F7)

/// The summary of the function `name` of the program of `a`.
fn summary_named(a: &Analysis, b: &Built, name: &str) -> weft_sema::analysis::Summary {
    let sema = a
        .program
        .fns
        .iter()
        .position(|f| f.name == name && !f.is_std)
        .unwrap_or_else(|| panic!("no function `{name}`"));
    let f = b
        .fns
        .iter()
        .find_map(|(s, f)| (s.index() == sema).then_some(*f))
        .unwrap_or_else(|| panic!("`{name}` has no function of the IR"));
    let sums = weft_sema::factgen::summaries(a, b);
    sums.get(f)
        .unwrap_or_else(|why| panic!("`{name}` has no summary: {why}"))
        .clone()
}

/// The nodes that an edge from `n` reaches.
fn succs(f: &FnFacts, n: NodeId) -> Vec<NodeId> {
    f.cfg_edge
        .iter()
        .filter(|(a, _)| *a == n)
        .map(|(_, b)| *b)
        .collect()
}

/// True if node `n` is a node of a cleanup block (its detail names a block
/// that is a cleanup block of body `body`) or an abort phase.
fn on_cleanup(f: &FnFacts, b: &Built, n: NodeId) -> bool {
    let node = f.node(n);
    if node.label.ends_with("(abort)") {
        return true;
    }
    let mut parts = node.detail.split_whitespace();
    let (Some(body), Some(block)) = (parts.next(), parts.next()) else {
        return false;
    };
    let (Ok(body), Ok(block)) = (
        body.trim_start_matches('b').parse::<usize>(),
        block.trim_start_matches("bb").parse::<usize>(),
    ) else {
        return false;
    };
    b.program.bodies[body].blocks[block].cleanup
}

const ABORTS: &str = "fn work() / fail { fail(\"x\") }
fn quiet(x: u64) -> u64 { x }
fn run() / fail {
    let a = quiet(1)
    work()
    print(a)
}
";

#[test]
fn a_call_keeps_its_abort_edge_only_if_its_callee_can_abort() {
    let f = ir_facts_with(ABORTS, Options::default(), "run");
    check_templates(&f, "run");
    let calls = nodes_labelled(&f, "call");
    assert_eq!(calls.len(), 2, "{calls:?}");
    let (quiet, work) = (calls[0], calls[1]);
    assert!(!f.may_abort.contains(&quiet), "`quiet` cannot abort");
    assert!(f.may_abort.contains(&work), "`work` can fail");
    let aborts = nodes_labelled(&f, "call frame end (abort)");
    assert_eq!(aborts.len(), 1, "one abort path: {aborts:?}");
    assert!(succs(&f, work).contains(&aborts[0]));
    let (_, b) = built(ABORTS);
    for n in succs(&f, quiet) {
        assert!(!on_cleanup(&f, &b, n), "`quiet` has an abort edge");
    }
}

const P25: &str = "linear struct Lk { id: u64 }
fn done(l: Lk) { let Lk(i) = l; print(\"done\", i) }
fn main() {
    let l = Lk { id: 1 }
    let x = 3
    assert x == 4
    done(l)
}
";

const P27: &str = "linear struct Lk { id: u64 }
fn done(l: Lk) { let Lk(i) = l; print(\"done\", i) }
fn check(x: u64) { assert x == 4 }
fn main() {
    let l = Lk { id: 1 }
    check(3)
    done(l)
}
";

#[test]
fn an_assert_aborts_past_the_function_also_in_a_callee() {
    use weft_sema::analysis::summary::Abort;
    // `tests/gate/probes/ir/probes/p25_assert_abort.wf`.
    let (_, b) = built(P25);
    let f = ir_facts_with(P25, Options::default(), "main");
    let assert = nodes_labelled(&f, "assert");
    assert_eq!(assert.len(), 1);
    assert!(f.may_abort.contains(&assert[0]));
    assert!(
        succs(&f, assert[0]).iter().any(|&n| on_cleanup(&f, &b, n)),
        "the assert has an abort edge"
    );
    // `p27_assert_callee.wf`: the summary of `check` has the abort of its
    // `assert`, so the call of `check` keeps its abort edge.
    let (a, b) = built(P27);
    let sum = summary_named(&a, &b, "check");
    assert!(sum.aborts.contains(&Abort::Assert), "{:?}", sum.aborts);
    let f = ir_facts_with(P27, Options::default(), "main");
    let call = nodes_labelled(&f, "call")[0];
    assert!(f.may_abort.contains(&call));
    assert_eq!(nodes_labelled(&f, "call frame end (abort)").len(), 1);
}

#[test]
fn unwound_at_holds_only_on_the_cleanup_nodes() {
    for (src, names) in [
        (ABORTS, &["run", "work", "quiet"][..]),
        (P25, &["main", "done"][..]),
        (P27, &["main", "check"][..]),
        (CALLS, &["holds", "vec_calls", "frame"][..]),
        (ON_ABORT, &["holder", "main", "undo"][..]),
    ] {
        let (_, b) = built(src);
        for name in names {
            let f = ir_facts_with(src, Options::default(), name);
            for &(_, n) in &f.unwound_at {
                assert!(
                    on_cleanup(&f, &b, n),
                    "{name}: unwound_at at {:?}",
                    f.node(n)
                );
            }
            for &(_, n) in &f.scope_end {
                assert!(
                    !on_cleanup(&f, &b, n),
                    "{name}: scope_end at {:?}",
                    f.node(n)
                );
            }
        }
    }
}

/// F3-1: `undo` changes a place through the reference in its value.
const ON_ABORT: &str = "linear struct R { o: Option<&Vec<u64>> }
    on abort = undo
fn undo(r: R) {
    let R(o) = r
    match o {
        Some(v) => v.push(7),
        None => {},
    }
}
fn holder(v: &Vec<u64>) {
    let r = R { o: Some(v) }
    assert v.len() == 0
    let R(x) = r
}
fn main() {
    let v = Vec.new()
    v.push(1)
    let first = &v[0]
    holder(&v)
    print(first)
}
";

#[test]
fn an_on_abort_function_applies_its_summary_at_the_unwind_value() {
    use weft_sema::analysis::summary::IRoot;
    let f = ir_facts_with(ON_ABORT, Options::default(), "holder");
    check_templates(&f, "holder");
    let unwind = nodes_labelled(&f, "unwind value");
    assert_eq!(unwind.len(), 1, "{unwind:?}");
    let v: BTreeSet<String> = std::iter::once("v".to_string()).collect();
    assert_eq!(
        mutates(&f, unwind[0]),
        v,
        "`undo` changes what `r` points into"
    );
    // The change goes into the summary of `holder`, so it shows at the
    // caller (F3-1).
    let (a, b) = built(ON_ABORT);
    let sum = summary_named(&a, &b, "holder");
    assert!(
        sum.muts.iter().any(|(m, _)| m.root == IRoot::Param(0)),
        "{:?}",
        sum.muts
    );
    let g = ir_facts_with(ON_ABORT, Options::default(), "main");
    let call = *nodes_labelled(&g, "call")
        .last()
        .unwrap_or_else(|| panic!("no call"));
    assert_eq!(mutates(&g, call), v);
}

#[test]
fn w0118_is_a_query_over_the_summary_of_the_on_abort_function() {
    let (a, b) = built(ON_ABORT);
    let sums = weft_sema::factgen::summaries(&a, &b);
    let ds = weft_sema::factgen::checks::on_abort_rows(&a, &b, &sums, false);
    let texts: Vec<&str> = ds.iter().map(|d| d.message.as_str()).collect();
    assert_eq!(
        texts,
        vec!["`on abort` function `undo` changes `r`, a place outside the value that it gets"],
        "{ds:?}"
    );
    assert!(ds.iter().all(|d| d.code == weft_syntax::diag::Code::W0118));
    // A change of the value itself is local: no W0118.
    let local = "linear struct H { items: Vec<u64> }
    on abort = undo_local
fn undo_local(h: H) {
    let H(items) = h
    items.push(1)
}
";
    let (a, b) = built(local);
    let sums = weft_sema::factgen::summaries(&a, &b);
    let ds = weft_sema::factgen::checks::on_abort_rows(&a, &b, &sums, false);
    assert!(ds.is_empty(), "{ds:?}");
}

/// A child failure inside a local `handle Fail`, and with no local handler.
const TASKS: &str = "fn quick() -> u64 { 5 }
fn local() {
    let r = handle Fail { fn fail(m) { 0 } } in {
        scope { s =>
            let t = s.spawn(|| quick())
            let (a, b) = fork(|| quick(), || quick())
            t.join() + a + b
        }
    }
    print(r)
}
fn past() {
    let r = scope { s =>
        let t = s.spawn(|| quick())
        let (a, b) = fork(|| quick(), || quick())
        t.join() + a + b
    }
    print(r)
}
";

#[test]
fn a_child_failure_aborts_to_the_local_fail_handler_and_a_cancel_past_the_function() {
    use weft_sema::factgen::frames::{self, Dest};
    let (a, b) = built(TASKS);
    let sums = weft_sema::factgen::summaries(&a, &b);
    let p = &b.program;
    // The scope body of the function `f`: its site is `f`, or the handled
    // body of a `handle` of `f`.
    let scope_body = |f: BodyId| -> BodyId {
        let in_f =
            |site: BodyId| site == f || p.handlers.iter().any(|h| h.handled == site && h.site == f);
        let s = p.scopes.iter().find(|s| in_f(s.site));
        s.unwrap_or_else(|| panic!("no scope in {f:?}")).body
    };
    let kinds = |body: BodyId| -> Vec<(&'static str, Vec<Dest>)> {
        p.bodies[body.index()]
            .blocks
            .iter()
            .filter(|blk| {
                matches!(
                    blk.term.kind,
                    TermKind::Join { .. } | TermKind::Fork { .. } | TermKind::ScopeWait { .. }
                )
            })
            .map(|blk| {
                (
                    nodes::term_name(&blk.term.kind),
                    frames::destinations(p, &b.tys, &sums, body, &blk.term.kind),
                )
            })
            .collect()
    };
    let h = HandlerId(0);
    let local = kinds(scope_body(body_of(&b, "local")));
    assert_eq!(local.len(), 3, "{local:?}");
    for (name, ds) in &local {
        assert!(ds.contains(&Dest::Past), "{name}: a cancel aborts past");
        assert!(
            ds.contains(&Dest::Handler {
                handler: h,
                value: true
            }),
            "{name}: a child failure goes to the `Fail` handler: {ds:?}"
        );
    }
    let past = kinds(scope_body(body_of(&b, "past")));
    assert_eq!(past.len(), 3, "{past:?}");
    for (name, ds) in &past {
        assert_eq!(ds, &vec![Dest::Past], "{name}");
    }
    // The node table: an abort to the handler binds the value of the clause
    // (`AbortValue`) and goes to the cleanup copy for the handler.
    let body = scope_body(body_of(&b, "local"));
    let fr = Frames::of_body(p, &b.tys, &sums, body);
    let mut facts = FnFacts::default();
    let table = NodeTable::build(p, body, &mut facts, &fr);
    let d = Dest::Handler {
        handler: h,
        value: true,
    }
    .id();
    for (bi, blk) in p.bodies[body.index()].blocks.iter().enumerate() {
        let (TermKind::Join {
            unwind: Some(u), ..
        }
        | TermKind::Fork {
            unwind: Some(u), ..
        }
        | TermKind::ScopeWait {
            unwind: Some(u), ..
        }) = blk.term.kind
        else {
            continue;
        };
        let key = NodeKey {
            body,
            block: BlockId(id(bi)),
            at: u32::MAX,
            phase: Phase::AbortValue,
            dest: d,
        };
        let av = table
            .get(key)
            .unwrap_or_else(|| panic!("no abort value node: {key:?}"));
        let copy = table
            .first(body, u, d)
            .expect("a cleanup copy for the handler");
        assert!(facts.cfg_edge.contains(&(av, copy)));
        assert!(
            table.first(body, u, PAST).is_some(),
            "and one past the function"
        );
    }
}
