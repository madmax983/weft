//! Unit tests of the analysis (plan stage F3, `docs/ir.md` 6.6) on
//! hand-built IR: the domain, the transfer functions of the statements, and
//! the joins of the driver.

use std::collections::BTreeSet;

use weft_facts::{FnFacts, PlaceId};
use weft_ir::ty::{AdtDecl, AdtKind, FieldDecl, VariantDecl};
use weft_ir::{
    AggKind, Block, BlockId, Body, BodyId, BodyKind, CapEnvId, Const, DerefKind, FieldIdx, FnDecl,
    FnId, IntTy, LocalDecl, LocalId, LocalKind, Operand, Origin, Place, Program, Proj, Props,
    Rvalue, Span, Stmt, StmtKind, Term, TermKind, Ty, TyId, TyTable, VariantIdx,
};
use weft_sema::analysis::{self, AbsVal, Cx, PathStep, State, Summaries, Tree};
use weft_sema::factgen::alpha::Roots;

/// The types of the tests.
struct Tys {
    table: TyTable,
    unit: TyId,
    u64: TyId,
    ref_u64: TyId,
    pair: TyId,
    s: TyId,
    tx: TyId,
    opt: TyId,
    ref_ref: TyId,
}

/// A definition with no flags.
fn adt(name: &str, kind: AdtKind, linear: bool) -> AdtDecl {
    AdtDecl {
        name: name.to_string(),
        generics: 0,
        kind,
        lang: None,
        linear,
        on_abort: None,
        has_on_abort: false,
        immovable: false,
        copy: false,
        nonportable: false,
        props: Default::default(),
    }
}

/// `u64`, `&u64`, `(&u64, &u64)`, `struct S { a: &u64, b: u64 }`,
/// `linear struct Tx { id: u64 }`, `enum Opt { None, Some(Tx) }`, `&&u64`.
fn tys() -> Tys {
    let mut t = TyTable::new();
    let unit = t.unit();
    let u64 = t.intern(Ty::Int(IntTy::U64));
    let ref_u64 = t.intern(Ty::Ref(u64));
    let pair = t.intern(Ty::Tuple(vec![ref_u64, ref_u64]));
    let field = |name: &str, ty| FieldDecl {
        name: name.to_string(),
        ty,
        place: false,
    };
    let s = t.push_adt(adt(
        "S",
        AdtKind::Struct(vec![field("a", ref_u64), field("b", u64)]),
        false,
    ));
    let s = t.intern(Ty::Adt(s, vec![]));
    let tx = t.push_adt(adt("Tx", AdtKind::Struct(vec![field("id", u64)]), true));
    let tx = t.intern(Ty::Adt(tx, vec![]));
    let opt = t.push_adt(adt(
        "Opt",
        AdtKind::Enum(vec![
            VariantDecl {
                name: "None".to_string(),
                fields: vec![],
            },
            VariantDecl {
                name: "Some".to_string(),
                fields: vec![tx],
            },
        ]),
        false,
    ));
    let opt = t.intern(Ty::Adt(opt, vec![]));
    let ref_ref = t.intern(Ty::Ref(ref_u64));
    Tys {
        table: t,
        unit,
        u64,
        ref_u64,
        pair,
        s,
        tx,
        opt,
        ref_ref,
    }
}

/// The origin of a hand-built statement.
const fn origin() -> Origin {
    Origin {
        span: Span {
            unit: 0,
            lo: 0,
            hi: 0,
        },
        expr: None,
    }
}

/// A body under construction.
struct Hand {
    locals: Vec<LocalDecl>,
    blocks: Vec<Block>,
    params: Vec<LocalId>,
}

impl Hand {
    /// A body with `_0: ()`.
    fn new(t: &Tys) -> Self {
        let mut h = Self {
            locals: Vec::new(),
            blocks: Vec::new(),
            params: Vec::new(),
        };
        h.local(t.unit, LocalKind::Return, None, Props::default());
        h
    }

    /// Adds a local.
    fn local(&mut self, ty: TyId, kind: LocalKind, name: Option<&str>, props: Props) -> LocalId {
        let id = LocalId(u32::try_from(self.locals.len()).unwrap_or(u32::MAX));
        self.locals.push(LocalDecl {
            ty,
            kind,
            name: name.map(str::to_string),
            props,
            in_place: false,
            origin: origin(),
        });
        if matches!(kind, LocalKind::Param(_)) {
            self.params.push(id);
        }
        id
    }

    /// A user local.
    fn user(&mut self, ty: TyId, name: &str) -> LocalId {
        self.local(ty, LocalKind::User, Some(name), Props::default())
    }

    /// Adds a block.
    fn block(&mut self, stmts: Vec<StmtKind>, term: TermKind) -> BlockId {
        let id = BlockId(u32::try_from(self.blocks.len()).unwrap_or(u32::MAX));
        self.blocks.push(Block {
            stmts: stmts
                .into_iter()
                .map(|kind| Stmt {
                    kind,
                    origin: origin(),
                })
                .collect(),
            term: Term {
                kind: term,
                origin: origin(),
            },
            cleanup: false,
        });
        id
    }

    /// The program with this body as its one function `f`.
    fn program(self, t: &Tys) -> Program {
        let body = Body {
            kind: BodyKind::Fn(FnId(0)),
            parent: None,
            locals: self.locals,
            ret: LocalId(0),
            params: self.params,
            caps: Vec::new(),
            kont: None,
            blocks: self.blocks,
            entry: BlockId(0),
            unwind_exit: BlockId(0),
            cap_env: CapEnvId(0),
            origin: origin(),
        };
        Program {
            bodies: vec![body],
            fns: vec![FnDecl {
                name: "f".to_string(),
                body: Some(BodyId(0)),
                params: Vec::new(),
                ret: t.unit,
                generics: 0,
                stated_row: Some(Vec::new()),
                intrinsic: None,
            }],
            ..Program::default()
        }
    }
}

const B: BodyId = BodyId(0);

/// A place with no projection.
const fn at(l: LocalId) -> Place {
    Place::local(l)
}

/// A place with projections.
const fn proj(l: LocalId, proj: Vec<Proj>) -> Place {
    Place { local: l, proj }
}

/// `p = rv`.
const fn assign(p: Place, rv: Rvalue) -> StmtKind {
    StmtKind::Assign(p, rv)
}

/// `const 1u64`.
const fn one() -> Operand {
    Operand::Const(Const::Int(1, IntTy::U64))
}

/// The result of an analysis: the state at the entry of each block, and the
/// facts with the places.
struct Run {
    states: analysis::States,
    facts: FnFacts,
    roots: Roots,
    p: Program,
    tys: TyTable,
}

impl Run {
    /// The state at the entry of block `b`.
    fn at(&self, b: BlockId) -> &State {
        self.states
            .at(b)
            .unwrap_or_else(|| panic!("no state at bb{}", b.0))
    }

    /// The display texts of a set of places.
    fn texts(&self, ps: &BTreeSet<PlaceId>) -> Vec<String> {
        let mut v: Vec<String> = ps
            .iter()
            .map(|p| self.facts.place(*p).display.clone())
            .collect();
        v.sort();
        v
    }

    /// The places that the value of local `l` at path `path` points into, at
    /// the entry of block `b`.
    fn refs(&self, b: BlockId, l: LocalId, path: &[PathStep]) -> Vec<String> {
        self.texts(&self.at(b).value((B, l), path).flat().refs)
    }
}

/// Runs the analysis of body 0 of `p` from `init`.
fn run_with(p: Program, t: &Tys, init: State) -> Run {
    let mut facts = FnFacts::default();
    let mut roots = Roots::default();
    let mut tys = t.table.clone();
    let states = {
        let mut cx = Cx {
            p: &p,
            tys: &mut tys,
            facts: &mut facts,
            roots: &mut roots,
            sums: &Summaries::default(),
        };
        analysis::run_all(&mut cx, B, init).unwrap_or_else(|e| panic!("the analysis: {e:?}"))
    };
    Run {
        states,
        facts,
        roots,
        p,
        tys,
    }
}

/// Runs the analysis of body 0 of `p` from the empty state.
fn run(p: Program, t: &Tys) -> Run {
    run_with(p, t, State::new())
}

#[test]
fn a_borrow_gives_the_places_of_alpha() {
    let t = tys();
    let mut h = Hand::new(&t);
    let x = h.user(t.u64, "x");
    let r = h.user(t.ref_u64, "r");
    let s = h.user(t.s, "s");
    let bb1 = BlockId(1);
    h.block(
        vec![
            assign(at(x), Rvalue::Use(one())),
            assign(
                at(s),
                Rvalue::Aggregate(AggKind::Struct(t.s), vec![Operand::Copy(at(r)), one()]),
            ),
            assign(at(r), Rvalue::Ref(at(x))),
        ],
        TermKind::Goto(bb1),
    );
    h.block(
        vec![assign(
            at(r),
            Rvalue::Ref(proj(s, vec![Proj::Field(FieldIdx(1))])),
        )],
        TermKind::Goto(BlockId(2)),
    );
    h.block(vec![], TermKind::Return);
    let out = run(h.program(&t), &t);
    assert_eq!(out.refs(bb1, r, &[]), vec!["x"]);
    // A new value of `r` replaces its places.
    assert_eq!(out.refs(BlockId(2), r, &[]), vec!["s.b"]);
    // A reference is not `@ uniq`.
    assert!(!out.at(bb1).value((B, r), &[]).flat().uniq);
}

#[test]
fn a_copy_of_a_reference_copies_its_places() {
    let t = tys();
    let mut h = Hand::new(&t);
    let x = h.user(t.u64, "x");
    let r = h.user(t.ref_u64, "r");
    let q = h.user(t.ref_u64, "q");
    h.block(
        vec![
            assign(at(x), Rvalue::Use(one())),
            assign(at(r), Rvalue::Ref(at(x))),
            assign(at(q), Rvalue::Use(Operand::Copy(at(r)))),
        ],
        TermKind::Goto(BlockId(1)),
    );
    h.block(vec![], TermKind::Return);
    let out = run(h.program(&t), &t);
    assert_eq!(out.refs(BlockId(1), q, &[]), vec!["x"]);
    // A copy leaves the value where it is.
    assert_eq!(out.refs(BlockId(1), r, &[]), vec!["x"]);
}

#[test]
fn an_aggregate_keeps_the_structure_of_the_move_paths() {
    let t = tys();
    let mut h = Hand::new(&t);
    let x = h.user(t.u64, "x");
    let y = h.user(t.u64, "y");
    let r = h.user(t.ref_u64, "r");
    let pair = h.user(t.pair, "pair");
    let s = h.user(t.s, "s");
    let bb1 = BlockId(1);
    h.block(
        vec![
            assign(at(x), Rvalue::Use(one())),
            assign(at(y), Rvalue::Use(one())),
            assign(at(r), Rvalue::Ref(at(x))),
            // A tuple of two references.
            assign(
                at(pair),
                Rvalue::Aggregate(
                    AggKind::Tuple,
                    vec![Operand::Copy(at(r)), Operand::Copy(at(r))],
                ),
            ),
            assign(
                proj(pair, vec![Proj::Field(FieldIdx(1))]),
                Rvalue::Ref(at(y)),
            ),
            // A struct with a reference field.
            assign(
                at(s),
                Rvalue::Aggregate(AggKind::Struct(t.s), vec![Operand::Copy(at(r)), one()]),
            ),
        ],
        TermKind::Goto(bb1),
    );
    h.block(vec![], TermKind::Return);
    let out = run(h.program(&t), &t);
    let f = |i| PathStep::Field(i);
    assert_eq!(out.refs(bb1, pair, &[f(0)]), vec!["x"]);
    // A new value of a part replaces the places of that part only.
    assert_eq!(out.refs(bb1, pair, &[f(1)]), vec!["y"]);
    assert_eq!(out.refs(bb1, pair, &[]), vec!["x", "y"]);
    assert_eq!(out.refs(bb1, s, &[f(0)]), vec!["x"]);
    assert!(out.refs(bb1, s, &[f(1)]).is_empty());
}

#[test]
fn a_join_is_a_union_of_the_may_parts_and_an_intersection_of_the_must_parts() {
    let t = tys();
    let mut h = Hand::new(&t);
    let x = h.user(t.u64, "x");
    let y = h.user(t.u64, "y");
    let c = h.user(t.u64, "c");
    let r = h.user(t.ref_u64, "r");
    let once = h.user(t.u64, "once");
    let (then, other, join) = (BlockId(1), BlockId(2), BlockId(3));
    h.block(
        vec![
            assign(at(x), Rvalue::Use(one())),
            assign(at(y), Rvalue::Use(one())),
            assign(at(c), Rvalue::Use(one())),
        ],
        TermKind::Switch {
            on: Operand::Copy(at(c)),
            arms: vec![(1, then)],
            otherwise: other,
        },
    );
    h.block(
        vec![
            assign(at(r), Rvalue::Ref(at(x))),
            assign(at(once), Rvalue::Use(one())),
        ],
        TermKind::Goto(join),
    );
    h.block(
        vec![assign(at(r), Rvalue::Ref(at(y)))],
        TermKind::Goto(join),
    );
    h.block(vec![], TermKind::Return);
    let out = run(h.program(&t), &t);
    let st = out.at(join);
    assert_eq!(out.refs(join, r, &[]), vec!["x", "y"]);
    // Both paths give `r` a value; only one gives `once` a value.
    assert!(st.must_hold((B, r), &[]));
    assert!(st.may_hold((B, once)));
    assert!(!st.must_hold((B, once), &[]));
    // The must part of the values: `empty` holds on both paths.
    assert!(st.value((B, r), &[]).flat().empty);

    // The join of the domain itself.
    let mut a = AbsVal::refs([PlaceId(1)]);
    a.linear = false;
    a.empty = true;
    a.uniq = true;
    let mut b = AbsVal::refs([PlaceId(2)]);
    b.linear = true;
    b.empty = false;
    b.uniq = true;
    let j = a.clone().joined(&b);
    assert_eq!(j.refs, [PlaceId(1), PlaceId(2)].into_iter().collect());
    assert!(j.linear, "linear is a may part");
    assert!(!j.empty, "empty is a must part");
    assert!(j.uniq);
    // `none` is the identity of the join.
    assert_eq!(a.clone().joined(&AbsVal::none()), a);
}

#[test]
fn uniq_is_the_meet() {
    let t = tys();
    let mut h = Hand::new(&t);
    let p = h.local(
        t.ref_u64,
        LocalKind::Param(0),
        Some("p"),
        Props {
            uniq: true,
            ..Props::default()
        },
    );
    let x = h.user(t.u64, "x");
    let c = h.user(t.u64, "c");
    let both = h.user(t.ref_u64, "both");
    let one_of = h.user(t.ref_u64, "one_of");
    let (then, other, join) = (BlockId(1), BlockId(2), BlockId(3));
    h.block(
        vec![
            assign(at(x), Rvalue::Use(one())),
            assign(at(c), Rvalue::Use(one())),
        ],
        TermKind::Switch {
            on: Operand::Copy(at(c)),
            arms: vec![(1, then)],
            otherwise: other,
        },
    );
    h.block(
        vec![
            assign(at(both), Rvalue::Use(Operand::Copy(at(p)))),
            assign(at(one_of), Rvalue::Use(Operand::Copy(at(p)))),
        ],
        TermKind::Goto(join),
    );
    h.block(
        vec![
            assign(at(both), Rvalue::Use(Operand::Copy(at(p)))),
            assign(at(one_of), Rvalue::Ref(at(x))),
        ],
        TermKind::Goto(join),
    );
    h.block(vec![], TermKind::Return);
    let prog = h.program(&t);
    // The parameter is `@ uniq` at the entry.
    let mut init = State::new();
    let mut v = AbsVal::refs([]);
    v.uniq = true;
    init.write((B, p), &[], Tree::leaf(v));
    let out = run_with(prog, &t, init);
    let st = out.at(join);
    assert!(st.value((B, both), &[]).flat().uniq);
    assert!(!st.value((B, one_of), &[]).flat().uniq);
}

#[test]
fn a_value_with_no_linear_part_is_empty() {
    let t = tys();
    let mut h = Hand::new(&t);
    let tx = h.user(t.tx, "tx");
    let none = h.user(t.opt, "none");
    let some = h.user(t.opt, "some");
    let bb1 = BlockId(1);
    h.block(
        vec![
            assign(
                at(tx),
                Rvalue::Aggregate(AggKind::Struct(t.tx), vec![one()]),
            ),
            assign(
                at(none),
                Rvalue::Aggregate(AggKind::Variant(t.opt, VariantIdx(0)), vec![]),
            ),
            assign(
                at(some),
                Rvalue::Aggregate(
                    AggKind::Variant(t.opt, VariantIdx(1)),
                    vec![Operand::Move(at(tx))],
                ),
            ),
        ],
        TermKind::Goto(bb1),
    );
    h.block(vec![], TermKind::Return);
    let out = run(h.program(&t), &t);
    let st = out.at(bb1);
    let n = st.value((B, none), &[]).flat();
    assert!(n.empty && !n.linear, "`None` holds nothing linear");
    let s = st.value((B, some), &[]).flat();
    assert!(s.linear && !s.empty, "`Some(tx)` holds a linear value");
    // The payload is a move path below the variant.
    let payload = st.value((B, some), &[PathStep::Variant(1), PathStep::Field(0)]);
    assert!(payload.flat().linear);
    // The move left no value in `tx`.
    assert!(!st.may_hold((B, tx)));
    assert!(st.value((B, tx), &[]).flat().empty);
}

#[test]
fn alpha_of_a_dereference_reads_the_state() {
    let t = tys();
    let mut h = Hand::new(&t);
    let x = h.user(t.u64, "x");
    let y = h.user(t.u64, "y");
    let r = h.user(t.ref_u64, "r");
    let rr = h.user(t.ref_ref, "rr");
    let pair = h.user(t.pair, "pair");
    let a = h.user(t.ref_u64, "a");
    let b = h.user(t.ref_u64, "b");
    let c = h.user(t.ref_u64, "c");
    let bb1 = BlockId(1);
    let deref = |l: LocalId, mut more: Vec<Proj>| {
        more.push(Proj::Deref(DerefKind::Ref));
        proj(l, more)
    };
    h.block(
        vec![
            assign(at(x), Rvalue::Use(one())),
            assign(at(y), Rvalue::Use(one())),
            assign(at(r), Rvalue::Ref(at(x))),
            assign(at(rr), Rvalue::Ref(at(r))),
            assign(
                at(pair),
                Rvalue::Aggregate(AggKind::Tuple, vec![Operand::Copy(at(r)), one()]),
            ),
            assign(
                proj(pair, vec![Proj::Field(FieldIdx(1))]),
                Rvalue::Ref(at(y)),
            ),
            // `&*r`: the places of `r`.
            assign(at(a), Rvalue::Ref(deref(r, vec![]))),
            // `&**rr`: through the value of `rr`, then the value of `r`.
            assign(
                at(b),
                Rvalue::Ref(proj(
                    rr,
                    vec![Proj::Deref(DerefKind::Ref), Proj::Deref(DerefKind::Ref)],
                )),
            ),
            // `&*pair.1`: the value of the part.
            assign(
                at(c),
                Rvalue::Ref(deref(pair, vec![Proj::Field(FieldIdx(1))])),
            ),
        ],
        TermKind::Goto(bb1),
    );
    h.block(vec![], TermKind::Return);
    let mut out = run(h.program(&t), &t);
    assert_eq!(out.refs(bb1, a, &[]), vec!["x"]);
    assert_eq!(out.refs(bb1, b, &[]), vec!["x"]);
    assert_eq!(out.refs(bb1, c, &[]), vec!["y"]);
    // α with the state of the entry of bb1: `(*r)` is `x`.
    let st = out.at(bb1).clone();
    let sums = Summaries::default();
    let mut cx = Cx {
        p: &out.p,
        tys: &mut out.tys,
        facts: &mut out.facts,
        roots: &mut out.roots,
        sums: &sums,
    };
    let al = analysis::transfer::alpha(&mut cx, B, &st, &deref(r, vec![]))
        .unwrap_or_else(|e| panic!("α: {e:?}"));
    let texts: Vec<String> = al
        .places
        .iter()
        .map(|p| out.facts.place(*p).display.clone())
        .collect();
    assert_eq!(texts, vec!["x"]);
    // The pointer place is the root of `r`: an access reads it.
    let ptrs: Vec<String> = al
        .ptrs
        .iter()
        .map(|p| out.facts.place(*p).display.clone())
        .collect();
    assert_eq!(ptrs, vec!["r"]);
}

#[test]
fn an_empty_state_gives_no_value() {
    let st = State::new();
    let v = st.value((B, LocalId(1)), &[PathStep::Field(0)]).flat();
    assert_eq!(v, AbsVal::none());
    assert!(!st.may_hold((B, LocalId(1))));
}

#[test]
fn a_move_of_a_part_leaves_a_hole_and_the_hole_goes_with_the_value() {
    let t = tys();
    let mut h = Hand::new(&t);
    let x = h.user(t.u64, "x");
    let pair = h.user(t.pair, "pair");
    let a = h.user(t.ref_u64, "a");
    let other = h.user(t.pair, "other");
    let bb1 = BlockId(1);
    h.block(
        vec![
            assign(at(x), Rvalue::Use(one())),
            assign(
                at(pair),
                Rvalue::Aggregate(AggKind::Tuple, vec![one(), one()]),
            ),
            assign(
                at(a),
                Rvalue::Use(Operand::Move(proj(pair, vec![Proj::Field(FieldIdx(0))]))),
            ),
            assign(at(other), Rvalue::Use(Operand::Move(at(pair)))),
        ],
        TermKind::Goto(bb1),
    );
    h.block(vec![], TermKind::Return);
    let out = run(h.program(&t), &t);
    let st = out.at(bb1);
    let f = |i| PathStep::Field(i);
    // The other part still holds its value; the moved part does not.
    assert!(st.must_hold((B, other), &[f(1)]));
    assert!(!st.must_hold((B, other), &[f(0)]));
    assert!(!st.must_hold((B, other), &[]));
    // The local that moved holds nothing.
    assert!(!st.may_hold((B, pair)));
}

// ------------------------------------------------------ summaries (F5)

/// The summary of the function of the IR whose path ends with `name`, from
/// its signature, in the program `src`.
fn summary_of(src: &str, name: &str) -> weft_sema::analysis::Summary {
    let a = weft_sema::analyze_source(src, weft_sema::Options::default())
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let b = weft_sema::irbuild::build(&a);
    let sums = weft_sema::factgen::summaries(&a, &b);
    let f = b
        .program
        .fns
        .iter()
        .position(|d| d.name.ends_with(name))
        .unwrap_or_else(|| panic!("no function `{name}` in {:?}", b.program.fns));
    sums.get(FnId(u32::try_from(f).unwrap_or(u32::MAX)))
        .cloned()
        .unwrap_or_else(|e| panic!("`{name}`: {e}"))
}

/// A program that calls the prelude functions of the tests.
const PRELUDE_CALLS: &str = "fn f(e: &Env) / fs {
    let v = Vec.new()
    v.push(1)
    let n = v.len()
    let r = v.get(0)
    v.clear()
    let s = e.fs.read(\"a\")
}
";

#[test]
fn a_signature_gives_the_parts_of_a_summary() {
    use weft_sema::analysis::summary::{Abort, Flow, IPlace, IRoot, IStep};
    use weft_sema::factgen::rels::Part;
    // `push(self, x: T) / mut(self)`.
    let push = summary_of(PRELUDE_CALLS, "push");
    assert_eq!(push.muts, vec![(IPlace::root(IRoot::Param(0)), 0)]);
    assert_eq!(
        push.reads,
        vec![IPlace::root(IRoot::Param(0)), IPlace::root(IRoot::Param(1))]
    );
    assert!(push.only_self, "each change is below `self`");
    assert!(!push.can_abort());
    assert!(push.performs.is_empty());
    // The receiver can keep the value of the argument (R3RT6: the run node
    // checks the types).
    assert_eq!(push.stores.len(), 1);
    assert_eq!(push.stores[0].into, 0);
    assert_eq!(push.stores[0].flows, vec![Flow::Held(1), Flow::Value(1)]);
    // `len(self) -> usize` changes nothing.
    let len = summary_of(PRELUDE_CALLS, "len");
    assert!(len.muts.is_empty());
    assert!(!len.has(Part::Ret));
    // `clear(self) / mut(self)` drops the values of its type parameter.
    let clear = summary_of(PRELUDE_CALLS, "clear");
    assert_eq!(clear.drops.iter().copied().collect::<Vec<_>>(), vec![0]);
    assert!(clear.has(Part::Drops));
    // `get(self, i: usize) -> &T in self[]`: the stated place of the result.
    let get = summary_of(PRELUDE_CALLS, "get");
    assert_eq!(get.ret.places.len(), 1);
    assert_eq!(get.ret.places[0].root, IRoot::Param(0));
    assert!(matches!(
        get.ret.places[0].steps.as_slice(),
        [IStep::Step(..)]
    ));
    // `read(self, path: String) -> String / fs`: an effect of the row
    // escapes and can abort; a read of a file can fail too.
    let read = summary_of(PRELUDE_CALLS, "read");
    assert!(
        read.performs.iter().any(|p| p.effect == "Fs"),
        "{:?}",
        read.performs
    );
    assert!(read.aborts.contains(&Abort::Raises));
    assert!(read.has(Part::Performs) && read.has(Part::Aborts));
    assert!(!read.only_self);
}

#[test]
fn rels_names_a_part_of_the_summary_for_each_relation_that_a_summary_carries() {
    use weft_sema::factgen::rels::{self, Part};
    // Each part that `RELS` gives a relation is a part of the summary
    // (`Summary::has` matches each part), and the summaries of a signature
    // fill the parts of the relations that a signature states.
    let parts: std::collections::BTreeSet<String> = rels::ALL
        .iter()
        .filter_map(|r| rels::row_of(*r).part.ok())
        .map(|p| format!("{p:?}"))
        .collect();
    let push = summary_of(PRELUDE_CALLS, "push");
    for p in [
        Part::Muts,
        Part::Reads,
        Part::Frees,
        Part::Lends,
        Part::Performs,
        Part::Aborts,
        Part::Multi,
        Part::Runs,
        Part::Tasks,
        Part::Ret,
        Part::Stores,
        Part::Drops,
        Part::Holds,
        Part::UsesMoves,
        Part::Rebinds,
        Part::UniqNeeds,
        Part::OnlySelf,
    ] {
        let _ = push.has(p);
        let named = parts.contains(&format!("{p:?}"));
        let summary_only = matches!(p, Part::Drops | Part::Holds | Part::Stores);
        assert!(
            named || summary_only,
            "`RELS` names no relation of part {p:?}"
        );
    }
    // `mutates_at` and `call_mut` go to `muts`, `reads_at` and `call_arg` to
    // `reads`, `writes_via` to `only_self`.
    assert_eq!(rels::row_of(rels::Rel::MutatesAt).part, Ok(Part::Muts));
    assert_eq!(rels::row_of(rels::Rel::CallArg).part, Ok(Part::Reads));
    assert_eq!(rels::row_of(rels::Rel::WritesVia).part, Ok(Part::OnlySelf));
    assert!(push.has(Part::Muts) && push.has(Part::Reads) && push.has(Part::OnlySelf));
}

#[test]
fn a_place_of_a_summary_is_cut_at_eight_steps() {
    use weft_sema::analysis::summary::{IPlace, IRoot, IStep, SIG_PLACE_STEPS};
    let step = IStep::Seg {
        label: 1,
        hi: true,
        unstable: false,
    };
    let p = IPlace::cut(IRoot::Param(0), vec![step.clone(); 12]);
    assert_eq!(p.steps.len(), SIG_PLACE_STEPS + 1);
    assert_eq!(p.steps.last(), Some(&IStep::Wild));
    let q = IPlace::cut(IRoot::Param(0), vec![step; 3]);
    assert_eq!(q.steps.len(), 3);
}

// ------------------------------------------ summaries of bodies (F6)

/// The analysis of `src` with both pipelines and group A on.
fn both_a(src: &str) -> weft_sema::Analysis {
    let opts = weft_sema::Options {
        facts: weft_sema::FactGen::Both,
        ir_groups: weft_sema::Groups::parse("A").unwrap_or(weft_sema::Groups::NONE),
        ..weft_sema::Options::default()
    };
    weft_sema::analyze_source(src, opts)
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message))
}

/// The function of the program of `a` with the name `name`.
fn sema_fn(a: &weft_sema::Analysis, name: &str) -> weft_sema::FnId {
    a.program
        .fn_ids()
        .find(|&f| a.program.fns[f].name == name)
        .unwrap_or_else(|| panic!("no function `{name}`"))
}

/// A signature as the gate compares it: each part, and each `mut` place with
/// no text.
fn sig_key(e: &weft_sema::program::EffectSig) -> String {
    let mut c = e.clone();
    for m in &mut c.muts {
        m.text.clear();
        for s in &mut m.steps {
            if let weft_sema::program::SigStep::Step(_, t) = s {
                t.clear();
            }
        }
    }
    c.muts
        .sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
    format!("{c:?}")
}

/// A recursive pair: `ping` and `pong` call each other; only `pong` changes
/// the vector and performs `Note`.
const PAIR: &str = "effect Note { fn note(x: u64) }

fn ping(v: &Vec<u64>, n: u64) {
    if n > 0 {
        pong(v, n - 1)
    }
}

fn pong(v: &Vec<u64>, n: u64) {
    if n > 0 {
        ping(v, n - 1)
    } else {
        v.push(1)
        note(n)
    }
}
";

#[test]
fn a_recursive_pair_of_functions_reaches_a_fixpoint() {
    use weft_sema::analysis::summary::{IPlace, IRoot};
    let a = both_a(PAIR);
    let b = weft_sema::irbuild::build(&a);
    let inf = weft_sema::analysis::callgraph::infer(&a, &b, None);
    assert!(inf.diags.is_empty(), "{:?}", inf.diags);
    for name in ["ping", "pong"] {
        let f = b
            .program
            .fns
            .iter()
            .position(|d| d.name.ends_with(name))
            .unwrap_or_else(|| panic!("no `{name}`"));
        let s = inf
            .sums
            .get(FnId(u32::try_from(f).unwrap_or(u32::MAX)))
            .unwrap_or_else(|e| panic!("`{name}`: {e}"));
        // Each function of the pair changes what `v` points into and
        // performs `Note` through the capability of its caller.
        assert_eq!(s.muts, vec![(IPlace::root(IRoot::Param(0)), 0)], "`{name}`");
        assert!(
            s.performs.iter().any(|p| p.effect == "main.Note"),
            "`{name}`: {:?}",
            s.performs
        );
        assert!(s.can_abort(), "`{name}`");
    }
    // The pair needs more than one round for each function: the first
    // round of `ping` sees an empty summary of `pong`.
    assert!(inf.rounds > 2, "{} rounds", inf.rounds);
    // The `EffectSig` of each function is the one of the old inference.
    let ir = a.ir_facts.as_ref().expect("the program is in scope");
    for name in ["ping", "pong"] {
        let f = sema_fn(&a, name);
        assert_eq!(
            sig_key(&ir.sigs[f.index()].effects),
            sig_key(&a.sigs[f.index()].effects),
            "`{name}`"
        );
    }
}

#[test]
fn a_row_only_grows() {
    use weft_facts::{Step, StepKind};
    use weft_sema::analysis::sig::Inferred;
    use weft_sema::analysis::summary::{IPlace, IRoot, IStep};
    let field = IStep::Step(
        Step {
            kind: StepKind::Field { id: 0 },
            unstable: false,
        },
        ".x".to_string(),
    );
    let v = IPlace::root(IRoot::Param(0));
    let vx = IPlace::cut(IRoot::Param(0), vec![field]);
    let row = |muts: Vec<IPlace>, named: &[&str]| Inferred {
        muts: muts.into_iter().map(|m| (m, 0)).collect(),
        named: named.iter().map(|n| (*n).to_string()).collect(),
        ..Inferred::default()
    };
    let mut r = row(vec![vx.clone()], &["main.A"]);
    // A place that covers the changed place replaces it.
    assert!(r.join(&row(vec![v.clone()], &[])));
    assert_eq!(r.muts, vec![(v.clone(), 0)]);
    // A place that the row covers adds nothing; the row does not shrink.
    assert!(!r.join(&row(vec![vx], &[])));
    assert!(!r.join(&Inferred::default()));
    assert_eq!(r.muts, vec![(v, 0)]);
    assert_eq!(r.named.len(), 1);
    // A new effect and `raises` grow the row.
    assert!(r.join(&row(Vec::new(), &["main.B"])));
    assert!(r.join(&Inferred {
        raises: true,
        ..Inferred::default()
    }));
    assert!(r.raises && r.named.len() == 2);
}

#[test]
fn the_guard_w0706_stops_a_fixpoint_that_grows_past_its_limit() {
    let a = both_a(PAIR);
    let b = weft_sema::irbuild::build(&a);
    let inf = weft_sema::analysis::callgraph::infer(&a, &b, Some(0));
    let mut codes: Vec<String> = inf
        .diags
        .iter()
        .map(|d| format!("{:?} {}", d.code, d.message))
        .collect();
    codes.sort();
    assert_eq!(codes.len(), 2, "{codes:?}");
    assert!(codes.iter().all(|c| c.starts_with("W0706")), "{codes:?}");
    assert!(codes.iter().any(|c| c.contains("`ping`")), "{codes:?}");
}

/// The source of `tests/gate/probes/ir/work/map/opres.wf` (map N1).
const OPRES: &str = include_str!("../../../tests/gate/probes/ir/work/map/opres.wf");

#[test]
fn a_perform_through_the_row_points_into_the_arguments_and_the_callers() {
    let a = both_a(OPRES);
    let b = weft_sema::irbuild::build(&a);
    let i = b
        .entries
        .iter()
        .position(|e| e.name == "body")
        .expect("a body `body`");
    let f = weft_sema::factgen::preview(&a, &b, i).unwrap_or_else(|u| panic!("{u}"));
    let n = f
        .escapes_at
        .iter()
        .find(|(_, e)| e == "main.Pick")
        .map(|(n, _)| *n)
        .expect("the perform escapes");
    assert!(f.may_abort.contains(&n));
    let root_name = |p: PlaceId| f.roots[f.place(p).root.index()].name.clone();
    // The perform lends the argument and the places of the callers.
    let lent: Vec<String> = f
        .lends_mut
        .iter()
        .filter(|(m, _)| *m == n)
        .map(|(_, p)| f.place(*p).display.clone())
        .collect();
    assert!(lent.iter().any(|d| d == "v"), "{lent:?}");
    assert!(
        f.lends_mut
            .iter()
            .any(|&(m, p)| m == n && root_name(p) == "a place of a caller"),
        "{lent:?}"
    );
    // `r` points into each place of `v` and into the places of the
    // callers.
    let r = f
        .vars
        .iter()
        .position(|v| v.name == "r")
        .map(|i| weft_facts::VarId(u32::try_from(i).unwrap_or(u32::MAX)))
        .expect("a variable `r`");
    let into: Vec<PlaceId> = f
        .points_into
        .iter()
        .filter(|(v, _)| *v == r)
        .map(|(_, p)| *p)
        .collect();
    assert!(
        into.iter()
            .any(|&p| f.place(p).display.starts_with('v') && f.place(p).is_wildcard()),
        "{:?}",
        into.iter()
            .map(|&p| f.place(p).display.clone())
            .collect::<Vec<_>>()
    );
    assert!(into.iter().any(|&p| root_name(p) == "a place of a caller"));
}

#[test]
fn a_function_with_no_stated_row_gets_the_summary_of_its_body() {
    // `grow` states no row: its summary comes from its body, so a call of
    // it is no longer a construct of a later stage.
    let src = "fn grow(v: &Vec<u64>) {
    v.push(1)
}

fn main() {
    let v = Vec.new()
    grow(&v)
    print(v.len())
}
";
    let a = both_a(src);
    let scope = a.ir_scope.as_ref().expect("a scope");
    assert!(scope.in_scope(), "{:?}", scope.fallback);
    let ir = a.ir_facts.as_ref().expect("the facts of the ir pipeline");
    let f = sema_fn(&a, "grow");
    assert_eq!(ir.sigs[f.index()].effects.muts.len(), 1);
    assert_eq!(ir.sigs[f.index()].effects.muts[0].text, "v");
    assert_eq!(
        sig_key(&ir.sigs[f.index()].effects),
        sig_key(&a.sigs[f.index()].effects)
    );
}

#[test]
fn a_public_function_with_no_stated_row_gets_w0701_from_its_summary() {
    let src = "effect Note { fn note(x: u64) }

pub fn tell(v: &Vec<u64>) {
    v.push(1)
    note(2)
}
";
    let mut opts = weft_sema::Options::from_markers("// weft: library\n");
    opts.facts = weft_sema::FactGen::Both;
    opts.ir_groups = weft_sema::Groups::parse("A").unwrap_or(weft_sema::Groups::NONE);
    let a = weft_sema::analyze_source(src, opts)
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let ir = a.ir_facts.as_ref().expect("the program is in scope");
    let msg = |ds: &[weft_syntax::diag::Diagnostic]| -> Vec<String> {
        ds.iter()
            .filter(|d| format!("{:?}", d.code) == "W0701")
            .map(|d| d.message.clone())
            .collect()
    };
    let old = msg(&a.diags);
    assert_eq!(old.len(), 1, "{:?}", a.diags);
    assert_eq!(msg(&ir.diags), old);
}

#[test]
fn the_effect_sig_of_each_corpus_function_of_group_a_is_the_one_of_the_old_inference() {
    // The signature diff of the gate (`weft-gate sigdiff`, class `sig` of
    // the ledger) on the corpus: no difference.
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .map(|d| {
            d.filter_map(Result::ok)
                .map(|e| e.path())
                .filter(|p| p.extension().is_some_and(|x| x == "wf"))
                .collect()
        })
        .unwrap_or_default();
    files.sort();
    let (mut programs, mut fns) = (0usize, 0usize);
    let mut bad = Vec::new();
    for f in &files {
        let Ok(src) = std::fs::read_to_string(f) else {
            continue;
        };
        let mut opts = weft_sema::Options::from_markers(&src);
        opts.facts = weft_sema::FactGen::Both;
        opts.ir_groups = weft_sema::Groups::parse("A").unwrap_or(weft_sema::Groups::NONE);
        let Ok(a) = weft_sema::analyze_source(&src, opts) else {
            continue;
        };
        let Some(ir) = a.ir_facts.as_ref() else {
            continue;
        };
        programs += 1;
        for g in a.program.fn_ids() {
            let def = &a.program.fns[g];
            if def.is_std || def.decl.body.is_none() {
                continue;
            }
            fns += 1;
            let (old, new) = (&a.sigs[g.index()].effects, &ir.sigs[g.index()].effects);
            let same_text = old.muts.iter().map(|m| &m.text).collect::<BTreeSet<_>>()
                == new.muts.iter().map(|m| &m.text).collect::<BTreeSet<_>>();
            if sig_key(old) != sig_key(new) || !same_text {
                bad.push(format!("{}: `{}`", f.display(), def.path));
            }
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    assert!(
        programs >= 10 && fns >= 40,
        "{programs} programs, {fns} functions"
    );
}

#[test]
fn a_change_of_a_by_value_parameter_is_in_the_row_as_the_old_inference_says() {
    // `tests/gate/probes/partb/p/bv.wf`: the old inference names a change of
    // a by-value parameter with no reference in the row (`mut(v)`), so W0701
    // asks for it. The `EffectSig` of the summary is the same.
    let src = "pub fn f(v: Vec<u64>) { v.push(1) }
fn k(v: Vec<u64>) { v.push(1) }
fn m(v: Vec<u64>) { k(v) }
";
    let a = both_a(src);
    let ir = a.ir_facts.as_ref().expect("the program is in scope");
    for name in ["f", "k", "m"] {
        let f = sema_fn(&a, name);
        assert_eq!(
            sig_key(&ir.sigs[f.index()].effects),
            sig_key(&a.sigs[f.index()].effects),
            "`{name}`"
        );
    }
    assert_eq!(ir.sigs[sema_fn(&a, "k").index()].effects.muts.len(), 1);
    assert!(ir.sigs[sema_fn(&a, "m").index()].effects.muts.is_empty());
    let w0701 = |ds: &[weft_syntax::diag::Diagnostic]| {
        ds.iter()
            .filter(|d| format!("{:?}", d.code) == "W0701")
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(w0701(&ir.diags), w0701(&a.diags));
    assert_eq!(w0701(&ir.diags).len(), 1);
}
