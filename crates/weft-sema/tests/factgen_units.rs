//! Unit tests of the parts of the fact generator that do not need the
//! analysis (plan stage F2, `docs/ir.md` 6.1 to 6.3 and 6.7): the relation
//! table `RELS`, the nodes and phases, roots and α, and the variables.

use std::collections::BTreeSet;

use weft_facts::{FnFacts, PlaceId, StepKind};
use weft_ir::{
    BlockId, BodyId, CapOperand, Const, DerefKind, EffectId, HandlerId, LocalId, LocalKind, OpIdx,
    Operand, Place, Proj, ScopeId, Side, SpawnId, TermKind, TyTable,
};
use weft_ir::{Callee, CapArgs};
use weft_sema::factgen::alpha::{self, AlphaError, Roots};
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
    let table = NodeTable::build(&b.program, f, &mut facts, &[PAST]);
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
    assert_eq!(var(VarKey::H(f, pa)).name, "p.0");
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
                table.add_body(&b.program, body, &mut facts, &[PAST]);
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
