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
use weft_sema::analysis::widen::{self, Cycles, Head};
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
            cycles: &Cycles::default(),
            hx: &mut analysis::clause::Handlers::default(),
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
        cycles: &Cycles::default(),
        hx: &mut analysis::clause::Handlers::default(),
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

// ------------------------------------------------------------ loops (F10)

/// `bool`.
fn bool_ty(t: &mut TyTable) -> TyId {
    t.intern(Ty::Bool)
}

#[test]
fn a_loop_head_joins_the_value_of_each_iteration() {
    // bb0: r = &x; goto bb1. bb1 (head): switch c [1: bb2, else bb3].
    // bb2: r = &y; goto bb1 (a back edge). bb3: return. The head holds the
    // place of the first iteration and of the later ones, and the cycle is
    // bb1 and bb2.
    let mut t = tys();
    let b = bool_ty(&mut t.table);
    let mut h = Hand::new(&t);
    let x = h.user(t.u64, "x");
    let y = h.user(t.u64, "y");
    let r = h.user(t.ref_u64, "r");
    let c = h.user(b, "c");
    let (bb1, bb2, bb3) = (BlockId(1), BlockId(2), BlockId(3));
    h.block(
        vec![
            assign(at(x), Rvalue::Use(one())),
            assign(at(y), Rvalue::Use(one())),
            assign(at(r), Rvalue::Ref(at(x))),
        ],
        TermKind::Goto(bb1),
    );
    h.block(
        vec![],
        TermKind::Switch {
            on: Operand::Copy(at(c)),
            arms: vec![(1, bb2)],
            otherwise: bb3,
        },
    );
    h.block(vec![assign(at(r), Rvalue::Ref(at(y)))], TermKind::Goto(bb1));
    h.block(vec![], TermKind::Return);
    let p = h.program(&t);
    let cycles = Cycles::of(&p, &[B]);
    assert!(!cycles.has(B, BlockId(0)));
    assert!(cycles.has(B, bb1) && cycles.has(B, bb2));
    assert!(!cycles.has(B, bb3));
    let rank = widen::ranks(&p.bodies[0]);
    assert_eq!(
        widen::heads(&p.bodies[0], &rank),
        vec![false, true, false, false]
    );
    let out = run(p, &t);
    assert_eq!(out.refs(bb1, r, &[]), vec!["x", "y"]);
    assert_eq!(out.refs(bb3, r, &[]), vec!["x", "y"]);
}

/// A chain of `n` field steps below `p` in `facts`, with the field `id`.
fn deeper(facts: &mut FnFacts, p: PlaceId, n: usize, id: u32) -> PlaceId {
    let step = weft_facts::Step {
        kind: weft_facts::StepKind::Field { id },
        unstable: false,
    };
    (0..n).fold(p, |q, _| facts.child(q, step, ".next"))
}

/// The state where local `l` points into `refs`.
fn points(l: LocalId, refs: &[PlaceId]) -> State {
    let mut st = State::new();
    st.write((B, l), &[], Tree::leaf(AbsVal::refs(refs.iter().copied())));
    st
}

/// The display texts of the places of local `l` in `st`.
fn texts_of(facts: &FnFacts, st: &State, l: LocalId) -> Vec<String> {
    let mut v: Vec<String> = st
        .value((B, l), &[])
        .flat()
        .refs
        .iter()
        .map(|p| facts.place(*p).display.clone())
        .collect();
    v.sort();
    v
}

#[test]
fn a_place_below_a_place_that_the_loop_added_widens_to_a_wildcard_place() {
    // A walk `cur = &cur.next`: the head has `l` before the loop. The first
    // back edge adds `l.next` (below a place from before the loop: it
    // stays). The second adds `l.next.next`, below `l.next` that the loop
    // added: it becomes `l.next..`. A place below `l.next..` is `l.next..`,
    // so the state is stable.
    let mut facts = FnFacts::default();
    let roots = Roots::default();
    let l = facts.add_root("l", weft_facts::RootKind::Local);
    let cur = LocalId(1);
    let n1 = deeper(&mut facts, l, 1, 0);
    let n2 = deeper(&mut facts, l, 2, 0);
    let first = points(cur, &[l]);
    let mut head = Head::new(&first);
    let mut st = points(cur, &[l, n1]);
    assert!(widen::widen(
        &mut facts, &roots, &mut st, &first, &mut head, 4
    ));
    assert_eq!(texts_of(&facts, &st, cur), vec!["l", "l.next"]);
    let old = st.clone();
    let mut st = points(cur, &[l, n1, n2]);
    assert!(widen::widen(
        &mut facts, &roots, &mut st, &old, &mut head, 4
    ));
    assert_eq!(texts_of(&facts, &st, cur), vec!["l", "l.next", "l.next.."]);
    let w = facts.wildcard(n1);
    let below = deeper(&mut facts, w, 3, 0);
    let old = st.clone();
    let mut again = points(cur, &[l, n1, w, below]);
    assert!(widen::widen(
        &mut facts, &roots, &mut again, &old, &mut head, 4
    ));
    assert_eq!(again, old, "the state at the head is stable");
}

#[test]
fn a_place_ten_steps_deeper_widens_at_the_outermost_new_place() {
    // Each iteration goes ten steps deeper: after two visits the place is
    // the wildcard place of the outermost place that the loop added.
    let mut facts = FnFacts::default();
    let roots = Roots::default();
    let l = facts.add_root("l", weft_facts::RootKind::Local);
    let cur = LocalId(1);
    let d10 = deeper(&mut facts, l, 10, 0);
    let d20 = deeper(&mut facts, l, 20, 0);
    let first = points(cur, &[l]);
    let mut head = Head::new(&first);
    let mut st = points(cur, &[l, d10]);
    assert!(widen::widen(
        &mut facts, &roots, &mut st, &first, &mut head, 4
    ));
    let old = st.clone();
    let mut st = points(cur, &[l, d10, d20]);
    assert!(widen::widen(
        &mut facts, &roots, &mut st, &old, &mut head, 4
    ));
    let w = facts.wildcard(d10);
    let got = st.value((B, cur), &[]).flat().refs;
    assert!(got.contains(&w), "{:?}", texts_of(&facts, &st, cur));
    assert!(!got.contains(&d20));
}

#[test]
fn too_many_places_of_one_root_become_the_wildcard_place_of_their_prefix() {
    // Seventeen fields of `w.a` in one value: more than `PLACES_MAX`.
    let mut facts = FnFacts::default();
    let roots = Roots::default();
    let w = facts.add_root("w", weft_facts::RootKind::Local);
    let a = deeper(&mut facts, w, 1, 0);
    let r = LocalId(1);
    let many: Vec<PlaceId> = (1..=17).map(|i| deeper(&mut facts, a, 1, i)).collect();
    let first = points(r, &[]);
    let mut head = Head::new(&first);
    let mut st = points(r, &many);
    assert!(widen::widen(
        &mut facts, &roots, &mut st, &first, &mut head, 4
    ));
    let wa = facts.wildcard(a);
    assert_eq!(
        st.value((B, r), &[]).flat().refs,
        std::iter::once(wa).collect::<BTreeSet<_>>()
    );
    const { assert!(widen::PLACES_MAX < 17) };
}

#[test]
fn after_the_root_visits_a_new_place_widens_to_its_root_and_the_bound_ends_the_loop() {
    // After `roots_after(locals)` visits, a new place becomes the wildcard
    // place of the deepest known place above it, or of its root. A head
    // that needs more than `visit_bound(locals)` visits is an error.
    let mut facts = FnFacts::default();
    let roots = Roots::default();
    let w = facts.add_root("w", weft_facts::RootKind::Local);
    let a = deeper(&mut facts, w, 3, 0);
    let r = LocalId(1);
    let first = points(r, &[]);
    let mut head = Head::new(&first);
    head.visits = widen::roots_after(4);
    let mut st = points(r, &[a]);
    assert!(widen::widen(
        &mut facts, &roots, &mut st, &first, &mut head, 4
    ));
    let ww = facts.wildcard(w);
    assert_eq!(
        texts_of(&facts, &st, r),
        vec![facts.place(ww).display.clone()]
    );
    head.visits = widen::visit_bound(4);
    let mut st = points(r, &[a]);
    assert!(!widen::widen(
        &mut facts, &roots, &mut st, &first, &mut head, 4
    ));
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
            // A function whose body has no IR has the worst case of its
            // declaration (plan stage R0i), as `weft-gate sigdiff` says.
            if def.is_std || def.decl.body.is_none() || ir.no_ir.contains(&g) {
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

/// The W0118 lines "calls a function value that it does not know" of each
/// source.
fn reaches_lines(src: &str) -> usize {
    let a = weft_sema::analyze_source(src, weft_sema::Options::from_markers(src))
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    a.diags
        .iter()
        .filter(|d| {
            d.message
                .contains("calls a function value that it does not know")
        })
        .count()
}

#[test]
fn an_on_abort_function_that_runs_an_unknown_value_is_w0118() {
    // Part `reaches` of W0118 from the summary (plan stage R0i fix): a task
    // run of a value of the parameter under a local `Fail` handler, a call
    // of an extern result in a program with no `multi` operation, also
    // through a callee.
    for src in [
        include_str!("../../../tests/gate/probes/fixes/r0i/r31_many_field_task_caught.wf"),
        include_str!("../../../tests/gate/probes/fixes/r0i/r34_many_field_spawn_direct.wf"),
        include_str!("../../../tests/gate/probes/fixes/r0i/r40_callee_caught_task.wf"),
        include_str!("../../../tests/gate/probes/fixes/r0i/r16_extern_all_caught.wf"),
        include_str!("../../../tests/gate/probes/fixes/r0i/r05_extern_result.wf"),
        include_str!("../../../tests/gate/probes/fixes/r0i/r18_extern_callee.wf"),
        // A run of an unknown value in a closure or a clause of the
        // function, or through an item that they call (plan stage R0i-b).
        include_str!("../../../tests/gate/probes/fixes/r0i/u06_clause_runs_extern.wf"),
        include_str!("../../../tests/gate/probes/fixes/r0i/u13_closure_caught_inside.wf"),
        include_str!("../../../tests/gate/probes/fixes/r0i/u14_task_closure_caught_inside.wf"),
        include_str!("../../../tests/gate/probes/fixes/r0i/u18_clause_calls_item.wf"),
        include_str!("../../../tests/gate/probes/fixes/r0i/u19_closure_calls_item.wf"),
        include_str!("../../../tests/gate/probes/fixes/r0i/u20_task_calls_item.wf"),
    ] {
        assert_eq!(reaches_lines(src), 1, "{src}");
    }
    // A task that gives back a value of a type parameter runs no value of a
    // caller (`verify/s5/R3x/p1/c14_task.wf`), and the worst case of a
    // callee with no IR runs no value.
    let task = "linear struct G<T> { x: T }\n    on abort = undo_g\n\
                fn undo_g<T>(g: G<T>) / async {\n    let G(x) = g\n    \
                scope { s =>\n        let t = s.spawn(|| x)\n        t.detach()\n    }\n}\n\
                fn main() / async { let g = G { x: 1 }\n let G(y) = g }\n";
    assert_eq!(reaches_lines(task), 0);
    assert_eq!(
        reaches_lines(include_str!(
            "../../../tests/gate/probes/fixes/r0i/r28_onabort_calls_noir.wf"
        )),
        0
    );
}

/// The codes and lines of the errors of the `ir` pipeline for `src`, and
/// the messages of W0303 and W0502 (plan stage R0i-b).
fn ir_errors(src: &str) -> Vec<(String, String)> {
    let a = weft_sema::analyze_source(src, weft_sema::Options::from_markers(src))
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    a.diags
        .iter()
        .filter(|d| matches!(format!("{:?}", d.code).as_str(), "W0303" | "W0502"))
        .map(|d| (format!("{:?}", d.code), d.message.clone()))
        .collect()
}

#[test]
fn the_builder_gives_w0303_and_w0502_of_a_once_closure() {
    // W0502 from the IR (`irbuild::values::once_into_plain`): a `once`
    // closure in a field of a stated function type, and in a `Vec` of a
    // stated type; not in a `Vec` whose type the closure gives, and not a
    // linear closure (W0601 is the error there).
    let head = "struct Buf { items: Vec<u64> }\nfn eat(b: Buf) {}\nstruct H { f: fn() }\n\
                linear struct Tx { id: u64 }\nfn commit(t: Tx) { let Tx(i) = t }\n";
    let field = format!("{head}fn main() {{ let b = Buf {{ items: Vec.new() }}\n let h = H {{ f: || eat(b) }}\n }}\n");
    let stated = format!("{head}fn main() {{ let b = Buf {{ items: Vec.new() }}\n let v: Vec<fn()> = Vec.new()\n v.push(|| eat(b))\n }}\n");
    let inferred = format!("{head}fn main() {{ let b = Buf {{ items: Vec.new() }}\n let v = Vec.new()\n v.push(|| eat(b))\n let g = v[0]\n g() }}\n");
    let linear = format!("{head}fn main() {{ let t = Tx {{ id: 1 }}\n let h = H {{ f: || commit(t) }}\n let g = h.f\n g() }}\n");
    let w0502 = |src: &str| ir_errors(src).iter().filter(|(c, _)| c == "W0502").count();
    assert_eq!(w0502(&field), 1, "{:?}", ir_errors(&field));
    assert_eq!(w0502(&stated), 1, "{:?}", ir_errors(&stated));
    assert_eq!(w0502(&inferred), 0, "{:?}", ir_errors(&inferred));
    assert_eq!(w0502(&linear), 0, "{:?}", ir_errors(&linear));
    // W0303 from the builder: each move through a reference of a body.
    let two = "struct Buf { items: Vec<u64> }\nfn eat(b: Buf) {}\n\
               fn f(r: &Buf, s: &Buf) {\n    let x = r.items\n    let y = s.items\n}\n";
    let e = ir_errors(two);
    assert_eq!(e.len(), 2, "{e:?}");
    assert!(
        e.iter()
            .all(|(c, m)| c == "W0303" && m.contains("`Vec<u64>`")),
        "{e:?}"
    );
}

#[test]
fn the_values_of_the_bindings_come_from_the_ir() {
    // `irbuild::values` (plan stage R0i-b): the properties of a binding of a
    // function type that the type does not show.
    let src = "struct Buf { items: Vec<u64> }\nfn eat(b: Buf) {}\n\
               linear struct Tx { id: u64 }\nfn commit(t: Tx) { let Tx(i) = t }\n\
               struct Holder { cb: fn() }\n\
               fn mk(f: fn()) -> fn() { f }\n\
               fn main() {\n    let b = Buf { items: Vec.new() }\n    let c = || eat(b)\n\
               let g = mk(c)\n    let t = Tx { id: 1 }\n    let l = || commit(t)\n\
               let k = l\n    let t2 = Tx { id: 2 }\n    let h = Holder { cb: || commit(t2) }\n\
               let m = || { let Holder(cb) = h\n cb() }\n    g()\n    k()\n    m()\n}\n";
    let a = weft_sema::analyze_source(src, weft_sema::Options::default())
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let built = weft_sema::irbuild::build(&a);
    let main = a.thir.len() - 1;
    let value = |name: &str| {
        let t = &a.thir[main];
        let (k, _) = t
            .bindings
            .iter()
            .enumerate()
            .find(|(_, b)| b.name == name)
            .unwrap_or_else(|| panic!("no binding {name}"));
        let id = weft_sema::thir::BindingId(u32::try_from(k).unwrap_or(u32::MAX));
        built.binding_values[main]
            .get(&id)
            .copied()
            .unwrap_or_default()
    };
    // The result of `mk(c)` is the argument: a `once` closure.
    assert!(value("g").once);
    // A struct of a type with no type argument whose field holds a linear
    // closure holds a linear value (the type has a function part in a field:
    // `props::ir_has_fns`, not `TyTable::mentions_fn`, which sees only the
    // type arguments).
    assert!(value("h").linear);
    // A copy of a linear closure is linear.
    assert!(value("k").linear);
    assert!(!value("g").linear);
}

#[test]
fn a_linear_closure_from_a_task_a_fork_or_resume_is_linear() {
    // The blockers of the review of R0i-b, round 1 (plan stage R0i-b fix):
    // the value flow of the IR gives a `join`, a `fork` and `resume` the
    // value of the task, of the branches and of the handled body. So the
    // local that gets a linear closure there is linear, and the cleanup
    // runs the `on abort` of its capture on an abort.
    for (src, name) in [
        (
            include_str!("../../../tests/gate/probes/fixes/r0i/rb/a16_task_join.wf"),
            "f",
        ),
        (
            include_str!("../../../tests/gate/probes/fixes/r0i/rb/a21_task_makes_closure.wf"),
            "f",
        ),
        (
            include_str!("../../../tests/gate/probes/fixes/r0i/rb/a22_join_in_scope_abort.wf"),
            "f",
        ),
        (
            include_str!("../../../tests/gate/probes/fixes/r0i/rb/a23_fork_result.wf"),
            "f",
        ),
        (
            include_str!("../../../tests/gate/probes/fixes/r0i/rb/a28_resume_dest.wf"),
            "g",
        ),
    ] {
        let a = weft_sema::analyze_source(src, weft_sema::Options::default())
            .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
        let built = weft_sema::irbuild::build(&a);
        let linear = a.thir.iter().enumerate().any(|(i, t)| {
            t.bindings.iter().enumerate().any(|(k, b)| {
                let id = weft_sema::thir::BindingId(u32::try_from(k).unwrap_or(u32::MAX));
                b.name == name
                    && built
                        .binding_values
                        .get(i)
                        .and_then(|m| m.get(&id))
                        .is_some_and(|v| v.linear)
            })
        });
        assert!(linear, "`{name}` is not linear in {src}");
    }
}

#[test]
fn a_spawn_on_one_of_nested_scopes_ends_its_task_at_the_outer_scope() {
    // Plan stage R0j: the scope operand of the spawn can be the capability
    // of `a` or of `t`. The two scopes are live at the spawn, so they are
    // nested, and the task ends at or before the end of the outer scope `a`.
    use weft_sema::analysis::tasks::SiteScope;
    let src = "fn main() / async {
        let b = true
        scope { a =>
            scope { t =>
                let x = if b { a } else { t }
                x.spawn(|| print(1))
            }
        }
        scope { u => u.spawn(|| print(2)) }
    }";
    let a = weft_sema::analyze_source(src, weft_sema::Options::default())
        .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
    let p = weft_sema::irbuild::build(&a).program;
    assert_eq!(p.scopes.len(), 3, "three scopes");
    let depth = |k: usize| {
        let mut at = p.scopes[k].body;
        let mut d = 0;
        while let Some(up) = p.bodies[at.index()].parent {
            at = up;
            d += 1;
        }
        d
    };
    // `t`: the deepest scope. `a`: the scope whose body holds the body of
    // `t`. `u`: the scope after them.
    let inner = (0..3).max_by_key(|&k| depth(k)).expect("a scope");
    let holds = |outer: usize| {
        let mut at = p.scopes[inner].body;
        while let Some(up) = p.bodies[at.index()].parent {
            if up == p.scopes[outer].body {
                return true;
            }
            at = up;
        }
        false
    };
    let outer = (0..3)
        .find(|&k| k != inner && holds(k))
        .expect("the outer scope");
    let other = (0..3)
        .find(|&k| k != inner && k != outer)
        .expect("the third scope");
    let id = |k: usize| weft_ir::ScopeId(u32::try_from(k).unwrap_or(u32::MAX));
    let nested = SiteScope {
        scopes: [id(inner), id(outer)].into_iter().collect(),
        other: false,
    };
    assert_eq!(nested.one(), None);
    assert_eq!(nested.end(&p), Some(id(outer)));
    // One scope: that scope.
    let one = SiteScope {
        scopes: std::iter::once(id(inner)).collect(),
        other: false,
    };
    assert_eq!(one.end(&p), Some(id(inner)));
    // Scopes that are not nested, or an operand that can be another value:
    // no scope (the pending rule).
    let apart = SiteScope {
        scopes: [id(inner), id(other)].into_iter().collect(),
        other: false,
    };
    assert_eq!(apart.end(&p), None);
    let open = SiteScope {
        scopes: [id(inner), id(outer)].into_iter().collect(),
        other: true,
    };
    assert_eq!(open.end(&p), None);
}

/// The copies of the callees at their calls (plan stage R0k-a,
/// `weft_sema::factgen::instantiate`), on programs from source.
mod copies {
    #[allow(unused_imports)]
    use weft_ir::Stmt;
    use weft_ir::{BodyKind, CapOperand, LocalKind, Program, Rvalue, StmtKind, TermKind};
    use weft_sema::factgen::instantiate::{instantiate, instantiate_with, Bounds};
    use weft_sema::irbuild::Built;

    /// The IR of `src`.
    fn built(src: &str) -> (weft_sema::Analysis, Built) {
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::default());
        let b = weft_sema::irbuild::build(&a);
        (a, b)
    }

    /// The handled bodies of `p`.
    fn handled(p: &Program) -> Vec<&weft_ir::Body> {
        p.bodies
            .iter()
            .filter(|b| matches!(b.kind, BodyKind::Handled(_)))
            .collect()
    }

    /// The function of the program named `name`.
    fn fn_id(p: &Program, name: &str) -> weft_ir::FnId {
        let i = p
            .fns
            .iter()
            .position(|f| f.name == name)
            .expect("the function");
        weft_ir::FnId(u32::try_from(i).expect("an id"))
    }

    /// True if body `b` calls function `f`.
    fn calls(b: &weft_ir::Body, f: weft_ir::FnId) -> bool {
        b.blocks.iter().any(|k| {
            matches!(&k.term.kind, TermKind::Call { callee: weft_ir::Callee::Fn(g, _), .. } if *g == f)
        })
    }

    const C2: &str = "effect Run { fn run(g: fn()) }\n\
        fn f(g: fn()) -> u64 / Run { run(g)\n 7 }\n\
        fn main() {\n\
        let x = handle Run { fn run(g) { g()\n resume(()) } } in { f(|| print(1)) }\n\
        print(x)\n\
        }\n";

    #[test]
    fn a_copy_binds_the_parameters_and_gives_the_result_to_the_destination() {
        let (_, b) = built(C2);
        let inst = instantiate(&b).expect("a copy");
        assert_eq!(inst.calls, 1);
        let p = &inst.built.program;
        let f = fn_id(p, "f");
        let h = handled(p);
        let hb = h.first().expect("a handled body");
        assert!(!calls(hb, f), "the call of `f` is gone");
        // The parameter `g` of `f` is a variable of the handled body, and it
        // gets the operand of the call.
        let g = hb
            .locals
            .iter()
            .position(|d| d.name.as_deref() == Some("g") && d.kind == LocalKind::User)
            .expect("the parameter of the copy");
        let binds = hb.blocks.iter().flat_map(|k| &k.stmts).any(|s| {
            matches!(&s.kind, StmtKind::Assign(q, Rvalue::Use(_)) if q.local.index() == g && q.proj.is_empty())
        });
        assert!(binds, "the parameter gets the operand");
        // `_0` of the copy is a temporary that moves into the destination.
        let gives = hb.blocks.iter().flat_map(|k| &k.stmts).any(|s| {
            matches!(&s.kind, StmtKind::Assign(q, Rvalue::Use(weft_ir::Operand::Move(r)))
                if q.local == hb.ret && matches!(hb.local(r.local).map(|d| d.kind), Some(LocalKind::Temp(_))))
        });
        assert!(gives, "the result goes to the destination of the call");
    }

    #[test]
    fn a_copy_goes_to_the_cleanup_block_of_the_call_on_an_abort() {
        let (_, b) = built(C2);
        let inst = instantiate(&b).expect("a copy");
        for hb in handled(&inst.built.program) {
            let exits = hb
                .blocks
                .iter()
                .filter(|k| matches!(k.term.kind, TermKind::UnwindExit))
                .count();
            assert_eq!(exits, 1, "only the frame of the handled body leaves");
        }
    }

    #[test]
    fn a_perform_through_the_row_of_the_copy_goes_to_the_local_capability() {
        let (_, b) = built(C2);
        let inst = instantiate(&b).expect("a copy");
        let p = &inst.built.program;
        let hb = handled(p).into_iter().next().expect("a handled body");
        let mut locals = 0;
        for k in &hb.blocks {
            match &k.term.kind {
                TermKind::Perform {
                    cap: CapOperand::Row(_),
                    ..
                } => panic!("a perform through the row stays"),
                TermKind::Perform {
                    cap: CapOperand::Local(q),
                    ..
                } => {
                    assert!(matches!(
                        hb.local(q.local).map(|d| d.kind),
                        Some(LocalKind::Cap(_))
                    ));
                    locals += 1;
                }
                _ => {}
            }
        }
        assert_eq!(locals, 1);
        assert!(weft_ir::verify::verify_program(p, &inst.built.tys)
            .iter()
            .all(|x| x.rule == weft_ir::verify::Rule::UnwindOrder));
    }

    #[test]
    fn a_callee_of_a_copied_callee_gets_a_copy_too() {
        let src = "effect Get { fn get() -> fn() }\n\
            fn inner() / Get { let g = get()\n g() }\n\
            fn outer() / Get { inner() }\n\
            fn main() {\n\
            handle Get { fn get() { resume(|| print(1)) } } in { outer() }\n\
            }\n";
        let (_, b) = built(src);
        let inst = instantiate(&b).expect("a copy");
        assert_eq!(inst.calls, 2);
        let p = &inst.built.program;
        let hb = handled(p).into_iter().next().expect("a handled body");
        assert!(!calls(hb, fn_id(p, "outer")) && !calls(hb, fn_id(p, "inner")));
    }

    #[test]
    fn a_closure_of_a_copy_gets_a_new_declaration_with_the_site_as_its_maker() {
        let src = "struct C { v: Vec<u64> }\n\
            effect Get { fn get() -> fn() }\n\
            fn run_ref(c: &C) / Get {\n\
            let k = || { let g = get()\n g() }\n\
            k()\n\
            }\n\
            fn main() {\n\
            let c = C { v: Vec.new() }\n\
            handle Get { fn get() { resume(|| print(1)) } } in { run_ref(&c) }\n\
            }\n";
        let (_, b) = built(src);
        let before = b.program.closures.len();
        let inst = instantiate(&b).expect("a copy");
        let p = &inst.built.program;
        assert_eq!(p.closures.len(), before + 1);
        let new = p.closures.last().expect("the new closure");
        let maker = p.body(new.maker).expect("the maker");
        assert!(matches!(maker.kind, BodyKind::Handled(_)));
        let id = weft_ir::ClosureId(u32::try_from(before).expect("an id"));
        assert_eq!(
            p.body(new.body).map(|x| x.kind),
            Some(BodyKind::Closure(id))
        );
        // The closure performs through the capability of the site: a new
        // `Cap` capture.
        assert!(new
            .captures
            .iter()
            .any(|c| c.mode == weft_ir::CaptureMode::Cap));
    }

    #[test]
    fn a_recursive_callee_gets_no_copy() {
        let src = "effect Run { fn run(g: fn()) }\n\
            fn f(n: u64, g: fn()) / Run { if n > 0 { f(n - 1, g) } else { run(g) } }\n\
            fn main() {\n\
            handle Run { fn run(g) { g()\n resume(()) } } in { f(2, || print(1)) }\n\
            }\n";
        let (_, b) = built(src);
        assert!(instantiate(&b).is_none());
    }

    #[test]
    fn a_callee_over_the_bound_gets_no_copy() {
        let (_, b) = built(C2);
        let small = Bounds {
            blocks: 2,
            ..Bounds::default()
        };
        assert!(instantiate_with(&b, small).is_none());
        let shallow = Bounds {
            depth: 0,
            ..Bounds::default()
        };
        assert!(instantiate_with(&b, shallow).is_none());
    }

    /// The invariant of the weak form (`Instantiated::weak_ok`): no call that
    /// a local handler serves applies a summary with the weak form. With the
    /// weak form on and no copies, the call of `f` in the handled body of
    /// `main` applies such a summary, and the guard
    /// (`analysis::transfer::note_weak_call`) keeps the program out of scope.
    #[test]
    fn a_served_call_of_a_summary_with_the_weak_form_keeps_the_old_pipeline() {
        let src = "effect Run { fn run(g: fn()) }\n\
            fn f(g: fn()) / Run { run(g) }\n\
            fn main() {\n\
            let v = Vec.new()\n\
            v.push(1)\n\
            let r = &v[0]\n\
            handle Run { fn run(g) { g()\n resume(()) } } in { f(|| v.clear()) }\n\
            print(r)\n\
            }\n";
        let (a, b) = built(src);
        let first = weft_sema::factgen::components(&a, &b);
        assert!(first.is_err(), "C2 without the weak form");
        let weak = weft_sema::analysis::transfer::WeakRowOps::enter();
        let Err(u) = weft_sema::factgen::components(&a, &b) else {
            panic!("the guard does not refuse the program");
        };
        assert_eq!(u.reason, weft_sema::analysis::transfer::OP_KEPT);
        drop(weak);
        // With the copies the program is in scope.
        let inst = instantiate(&b).expect("a copy");
        assert!(inst.weak_ok);
        let _weak = weft_sema::analysis::transfer::WeakRowOps::enter();
        assert!(weft_sema::factgen::components(&a, &inst.built).is_ok());
    }

    /// A probe of `tests/gate/probes/fixes/r0k2`.
    fn r0k2(name: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0k2")
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    }

    /// The calls in body `b` of a function value that is a local that a
    /// closure literal of `b` gives a value, or a copy of one.
    fn value_calls(b: &weft_ir::Body) -> usize {
        let mut made: std::collections::BTreeSet<weft_ir::LocalId> =
            std::collections::BTreeSet::new();
        for _ in 0..3 {
            for st in b.blocks.iter().flat_map(|k| &k.stmts) {
                match &st.kind {
                    StmtKind::Assign(q, Rvalue::Aggregate(weft_ir::AggKind::Closure(_), _)) => {
                        made.insert(q.local);
                    }
                    StmtKind::Assign(q, Rvalue::Use(weft_ir::Operand::Copy(r)))
                        if made.contains(&r.local) =>
                    {
                        made.insert(q.local);
                    }
                    _ => {}
                }
            }
        }
        b.blocks
            .iter()
            .filter(|k| {
                matches!(&k.term.kind, TermKind::Call {
                        callee: weft_ir::Callee::Value(weft_ir::Operand::Copy(q)),
                        ..
                    } if made.contains(&q.local))
            })
            .count()
    }

    /// Stage R0k-a2, the static closure copy: a closure that the handled body
    /// makes and runs gets a copy of its body at the run. A `Kept` capture is
    /// its source, a `ByRef` capture a new borrow of its source, a `Cap`
    /// capture the capability of the site; the copy mentions the closure
    /// value, so its references live up to the run.
    #[test]
    fn a_closure_that_the_body_makes_and_runs_gets_a_copy_at_the_run() {
        for name in ["a01_kept_bad.wf", "a02_byref_bad.wf", "a03_cap_bad.wf"] {
            let (_, b) = built(&r0k2(name));
            let before: usize = handled(&b.program).iter().map(|x| value_calls(x)).sum();
            let inst = instantiate(&b).unwrap_or_else(|| panic!("{name}: no copy"));
            assert_eq!(inst.closure_calls, 1, "{name}");
            let p = &inst.built.program;
            let hb = handled(p).into_iter().next().expect("a handled body");
            assert_eq!(before, 1, "{name}");
            assert_eq!(value_calls(hb), 0, "{name}: the run is gone");
            let stmts: Vec<&StmtKind> = hb
                .blocks
                .iter()
                .flat_map(|k| &k.stmts)
                .map(|s| &s.kind)
                .collect();
            assert!(
                stmts.iter().any(|k| matches!(k, StmtKind::Mention(_))),
                "{name}"
            );
            if name.starts_with("a02") {
                assert!(
                    stmts
                        .iter()
                        .any(|k| matches!(k, StmtKind::Assign(_, Rvalue::Ref(_)))),
                    "{name}: the borrow of the `ByRef` capture"
                );
            }
            // A perform through the capability of the closure is a perform of
            // the local handler now.
            let local = hb.blocks.iter().any(|k| {
                matches!(&k.term.kind, TermKind::Perform { cap: CapOperand::Local(q), .. }
                    if matches!(hb.local(q.local).map(|d| d.kind), Some(LocalKind::Cap(_))))
            });
            assert!(local, "{name}");
            assert!(weft_ir::verify::verify_program(p, &inst.built.tys)
                .iter()
                .all(|x| x.rule == weft_ir::verify::Rule::UnwindOrder));
        }
    }

    /// The refusal of the static closure copy: the local can hold one of two
    /// closures. It keeps the call of the closure value. (A local that gets
    /// its closure from a block, `a06_ends`, gets a copy region from stage
    /// R0k-b2 on: the copy reads the capture whose source ends through the
    /// environment local of the region, `copy_env`. A `once` closure with a
    /// `ByMove` capture, `a05_by_value`, gets one from plan stage R0z Z3 on:
    /// `a_once_closure_gets_a_copy_that_moves_its_value`.) From plan stage
    /// R0z Z6 the run gets a dispatch instead (a copy of each closure after a
    /// test of the closure, `r0z6::`), and no copy that is not an arm of it.
    #[test]
    fn a_closure_copy_is_refused_for_two_closures() {
        let (_, b) = built(&r0k2("a04_two_closures_bad.wf"));
        assert!(instantiate(&b).is_none_or(|i| i.closure_calls
            == i.built
                .program
                .dispatches
                .iter()
                .flat_map(|d| d.arms.iter())
                .filter(|a| a.region.is_some())
                .count()));
    }

    /// A `once` closure (plan stage R0z Z3, parts d and e): the run moves the
    /// value, so the copy moves it into a new local first, and the region
    /// reads the `ByMove` capture through its environment local. The block of
    /// the run ends with the move and a jump to the region, and each exit of
    /// the region ends the new local.
    #[test]
    fn a_once_closure_gets_a_copy_that_moves_its_value() {
        let (a, b) = built(&r0k2("a05_by_value_bad.wf"));
        let inst = instantiate(&b).expect("a copy");
        let p = &inst.built.program;
        let r = p.regions.first().expect("a region");
        assert!(r.env_local.is_some());
        let body = &p.bodies[r.body.index()];
        let t = r.value.local;
        assert!(matches!(body.local_kind(t), Some(LocalKind::Temp(_))));
        let moved = body.blocks.iter().any(|blk| {
            blk.stmts.iter().any(|st| {
                matches!(&st.kind, StmtKind::Assign(q, Rvalue::Use(weft_ir::Operand::Move(_)))
                    if q.local == t && q.proj.is_empty())
            }) && matches!(blk.term.kind, TermKind::Goto(k) if k == r.entry)
        });
        assert!(moved, "the move of the value before the region");
        let ends = r
            .blocks
            .iter()
            .filter(|k| {
                body.blocks[k.index()]
                    .stmts
                    .iter()
                    .any(|st| st.kind == StmtKind::Dead(t))
            })
            .count();
        assert!(ends >= 2, "a normal exit and a cleanup exit");
        assert!(weft_ir::verify::verify_program(p, &inst.built.tys)
            .iter()
            .all(|x| x.rule == weft_ir::verify::Rule::UnwindOrder
                || x.rule == weft_ir::verify::Rule::KontNotFirst));
        let _weak = inst
            .weak_ok
            .then(weft_sema::analysis::transfer::WeakRowOps::enter);
        assert!(weft_sema::factgen::components(&a, &inst.built).is_ok());
    }

    /// A source that ends between the closure and the run: a `Dead` of the
    /// source of the `Kept` capture before the run (built by hand: the source
    /// language gives no such program). The copy cannot name the source
    /// there, so (from stage R0k-b2 on) it is a copy region that reads the
    /// capture through its environment local, a cell of the closure value.
    #[test]
    fn a_source_that_ends_before_the_run_is_read_through_the_environment_local() {
        let (_, mut b) = built(&r0k2("a01_kept_bad.wf"));
        assert!(instantiate(&b).is_some_and(|i| i.closure_calls == 1));
        let p = &mut b.program;
        let (ci, src) = p
            .closures
            .iter()
            .enumerate()
            .find_map(|(i, d)| {
                d.captures
                    .iter()
                    .find(|c| c.mode == weft_ir::CaptureMode::Kept)
                    .map(|c| (i, c.source.local))
            })
            .expect("a kept capture");
        let maker = p.closures[ci].maker;
        let body = &mut p.bodies[maker.index()];
        // The block of the run: the first call of a function value.
        let run = body
            .blocks
            .iter()
            .position(|k| {
                matches!(
                    k.term.kind,
                    TermKind::Call {
                        callee: weft_ir::Callee::Value(_),
                        ..
                    }
                )
            })
            .expect("a run");
        let at = body.blocks[run].stmts.len();
        body.blocks[run].stmts.insert(
            at,
            weft_ir::Stmt {
                kind: StmtKind::Dead(src),
                origin: weft_ir::Origin::default(),
            },
        );
        let inst = instantiate(&b).expect("a copy");
        assert_eq!(inst.closure_calls, 1);
        let p = &inst.built.program;
        let r = p.regions.first().expect("a copy region");
        let e = r.env_local.expect("an environment local");
        assert_eq!(
            p.bodies[r.body.index()].local_kind(e),
            Some(LocalKind::CopyEnv(r.closure))
        );
    }

    /// Stage R0k-a2, a generic callee: each call gets a copy under its own type
    /// arguments, and no local of a copy names a type parameter.
    #[test]
    fn a_generic_callee_gets_a_copy_under_the_type_arguments_of_the_call() {
        let (_, b) = built(&r0k2("c09_generic_two_bad.wf"));
        let inst = instantiate(&b).expect("a copy");
        assert_eq!(inst.calls, 2);
        let p = &inst.built.program;
        for hb in handled(p) {
            assert!(!calls(hb, fn_id(p, "run_ref")));
            for d in &hb.locals {
                assert!(!inst.built.tys.mentions_param(d.ty), "{:?}", d.name);
            }
        }
        assert!(weft_ir::verify::verify_program(p, &inst.built.tys)
            .iter()
            .all(|x| x.rule == weft_ir::verify::Rule::UnwindOrder));
    }

    /// Stage R0k-a2, the closure guard (D): the structural check of
    /// `weak_ok` is not on the way here. With the weak form on and no copy,
    /// the run of a closure whose summary uses the weak form (a perform
    /// through a captured capability with a function value) where the local
    /// handler serves the operation is refused by the analysis
    /// (`transfer::note_weak_call`); with the copy of the closure body the
    /// program is in scope.
    #[test]
    fn a_served_run_of_a_closure_with_the_weak_form_keeps_the_old_pipeline() {
        let (a, b) = built(&r0k2("a03_cap_bad.wf"));
        assert!(weft_sema::factgen::components(&a, &b).is_err());
        let weak = weft_sema::analysis::transfer::WeakRowOps::enter();
        let Err(u) = weft_sema::factgen::components(&a, &b) else {
            panic!("the guard does not refuse the run of the closure");
        };
        assert_eq!(u.reason, weft_sema::analysis::transfer::OP_KEPT);
        drop(weak);
        let inst = instantiate(&b).expect("a copy");
        assert!(inst.weak_ok);
        let _weak = weft_sema::analysis::transfer::WeakRowOps::enter();
        assert!(weft_sema::factgen::components(&a, &inst.built).is_ok());
    }

    /// The review of R0k-a2: a body inside the owner of the local (a scope
    /// task, a scope body, a nested handled body, a clause) gives the local
    /// another closure through an upvar, so the run of the local gets no
    /// copy of the first closure. From plan stage R0z Z6 a scope body, a nested
    /// handled body and a clause give the run a dispatch (`r0z6::`): each
    /// copy is an arm of it. A task keeps no copy.
    #[test]
    fn a_closure_copy_is_refused_when_a_nested_body_writes_the_local() {
        for name in [
            "u03_callee_reassigns_via_clause.wf",
            "u04_task_reassigns.wf",
            "u05_scope_body.wf",
            "u06_handled_body.wf",
            "u08_task_join.wf",
            "u09_fork.wf",
            "u10_clause_of_inner.wf",
            "u11_clause_harmless_then.wf",
        ] {
            let (_, b) = built(&r0k2(name));
            let task = ["u04", "u08", "u09"].iter().any(|t| name.starts_with(t));
            assert!(
                instantiate(&b).is_none_or(|i| {
                    let arms = i
                        .built
                        .program
                        .dispatches
                        .iter()
                        .flat_map(|d| d.arms.iter())
                        .filter(|a| a.region.is_some())
                        .count();
                    i.closure_calls == arms && (arms > 0) != task
                }),
                "{name}: a copy that is not an arm of a dispatch"
            );
        }
    }

    /// The order of the weak guard (the review of R0k-a2): the analysis runs
    /// `apply` before `main`, the maker of the closure with the weak form,
    /// and the guard refuses the call of `apply` that gives it the closure
    /// where the local handler serves the operation. From plan stage R0z Z3
    /// (part g) the call gets a copy of `apply`: the run of the closure is in
    /// `main`, where it gets a copy of its body, and the program has full
    /// facts.
    #[test]
    fn a_weak_value_given_to_a_callee_gets_a_copy_of_the_callee() {
        let (a, b) = built(&r0k2("g26_weak_run_in_callee_bad.wf"));
        let weak = weft_sema::analysis::transfer::WeakRowOps::enter();
        let Err(u) = weft_sema::factgen::components(&a, &b) else {
            panic!("the guard does not refuse the call");
        };
        assert_eq!(u.reason, weft_sema::analysis::transfer::OP_KEPT);
        drop(weak);
        let inst = instantiate(&b).expect("a copy of `apply`");
        assert_eq!((inst.calls, inst.closure_calls), (1, 1));
        let _weak = inst
            .weak_ok
            .then(weft_sema::analysis::transfer::WeakRowOps::enter);
        assert!(weft_sema::factgen::components(&a, &inst.built).is_ok());
    }

    /// The text of probe `name` of `dir` in `tests/gate/probes`.
    fn probe(dir: &str, name: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes")
            .join(dir)
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    }

    /// The blocks of the copy region `r` of `p` and their body.
    fn region_blocks<'p>(
        p: &'p Program,
        r: &weft_ir::CopyRegion,
    ) -> (&'p weft_ir::Body, Vec<&'p weft_ir::Block>) {
        let body = &p.bodies[r.body.index()];
        let blocks = r.blocks.iter().map(|k| &body.blocks[k.index()]).collect();
        (body, blocks)
    }

    /// A copy region (plan stage R0k-b1'): the closure `c` is made in the
    /// handled body of H and runs in the handled body of H2, an inner
    /// handler of the same effect. The run gets a copy of the closure body
    /// in the handled body of H2. Its environment is the one where `c` is
    /// made, not the one of H2, and its perform goes to the capability of H
    /// through an upvar local. No other code reads `c`: the region is the
    /// only run of the closure (`sole`).
    #[test]
    fn a_closure_of_a_body_around_the_run_node_gets_a_copy_region() {
        let (_, b) = built(&probe("fixes/r0kb1", "n01_nested_run_ok.wf"));
        let inst = instantiate(&b).expect("a copy");
        assert_eq!(inst.regions, 1);
        let p = &inst.built.program;
        let r = p.regions.first().expect("a region");
        let (body, blocks) = region_blocks(p, r);
        assert!(matches!(body.kind, BodyKind::Handled(_)));
        assert_eq!(r.env, p.closures[r.closure.index()].cap_env);
        assert_ne!(r.env, body.cap_env);
        let cap = blocks
            .iter()
            .find_map(|k| match &k.term.kind {
                TermKind::Perform {
                    cap: CapOperand::Local(q),
                    ..
                } => Some(q.clone()),
                _ => None,
            })
            .expect("a perform");
        assert!(matches!(
            body.local_kind(cap.local),
            Some(LocalKind::Upvar(_))
        ));
        assert!(r.sole);
        // The entry reads the closure value first: the interpreter takes its
        // handlers there.
        let entry = &body.blocks[r.entry.index()];
        assert!(matches!(
            entry.stmts.first().map(|x| &x.kind),
            Some(StmtKind::Mention(q)) if *q == r.value
        ));
    }

    /// The pass-on form of a copy region (plan stage R0k-b1',
    /// `b2_call.reg_closure_param`): the closure is made where no local
    /// handler handles `Reg` and runs in the handled body of a local `Reg`
    /// handler. In the region the perform stays a perform through the row:
    /// it goes past the function, as at run time, although the body binds
    /// the effect.
    #[test]
    fn a_row_perform_of_a_copy_region_goes_past_the_function() {
        let (_, b) = built(&probe("partb/s3fix/p", "b2_call.wf"));
        let inst = instantiate(&b).expect("a copy");
        let p = &inst.built.program;
        let found = p.regions.iter().any(|r| {
            let (body, blocks) = region_blocks(p, r);
            blocks.iter().any(|k| {
                matches!(&k.term.kind, TermKind::Perform { cap: CapOperand::Row(e), .. }
                    if p.cap_envs[body.cap_env.index()].adds.iter().any(|(x, _)| x == e))
            })
        });
        assert!(found, "no region with a perform through the row");
        let broken = weft_ir::verify::verify_program(p, &inst.built.tys);
        assert!(
            !broken
                .iter()
                .any(|x| x.rule == weft_ir::verify::Rule::BadCap
                    || x.rule == weft_ir::verify::Rule::BadRegion),
            "{broken:?}"
        );
    }

    /// A copy region in a clause (plan stage R0k-b1'): the handled body of
    /// `Reg` gives a closure to `reg`, and the clause runs its parameter. The
    /// one perform that can run the clause gives the closure, so the run in
    /// the clause gets a copy of the closure body.
    #[test]
    fn a_clause_that_runs_its_parameter_gets_a_copy_region() {
        let (_, b) = built(&probe("fixes/r0kb1", "n03_clause_runs_ok.wf"));
        let inst = instantiate(&b).expect("a copy");
        let p = &inst.built.program;
        assert!(p
            .regions
            .iter()
            .any(|r| matches!(p.bodies[r.body.index()].kind, BodyKind::Clause(..))));
    }

    /// A copy region of a closure that a callee makes and gives back (plan
    /// stage R0k-b1', `fixes/r0k3/h02`): the closure of `mk` has no capture,
    /// so its body can run at the call site. Its environment is the one of
    /// the call of `mk`, not the one of the local handler where it runs.
    #[test]
    fn a_closure_that_a_callee_makes_with_no_capture_gets_a_copy_region() {
        let (_, b) = built(&probe("fixes/r0k3", "h02_made_closure_row.wf"));
        let inst = instantiate(&b).expect("a copy");
        let p = &inst.built.program;
        let r = p.regions.first().expect("a region");
        let outer = fn_id(p, "outer");
        let ob = p.fns[outer.index()].body.expect("a body");
        let call_env = p.bodies[ob.index()]
            .blocks
            .iter()
            .find_map(|k| match &k.term.kind {
                TermKind::Call {
                    caps: weft_ir::CapArgs::Lexical(e),
                    callee: weft_ir::Callee::Fn(f, _),
                    ..
                } if p.fns[f.index()].name == "mk" => Some(*e),
                _ => None,
            });
        assert_eq!(Some(r.env), call_env);
        assert_ne!(r.env, p.bodies[r.body.index()].cap_env);
    }

    /// The refusals of a copy region (plan stage R0k-b1'). The extent rule:
    /// a closure that leaves the handled body of its handler (`n04`, `c11`:
    /// a new instance of the handler in a loop), a closure that the clause
    /// of its own handler runs (the clause runs outside the handled body).
    /// The agreement rule: a closure with a `scope`, run where `Fail` goes to
    /// another handler (`n05`). (A closure that a callee makes with a
    /// capture, `c10`, `c14` and `h03`, gets a region from stage R0k-b2 on:
    /// the copy reads the capture through the environment local of the
    /// region. The `scope` of `c14` is in a callee of the closure, whose call
    /// gets the environment of the region.)
    #[test]
    fn a_copy_region_is_refused_by_the_extent_and_the_agreement_rules() {
        let own = "effect Reg {\n fn reg(f: fn())\n fn ping()\n }\n\
            fn main() {\n\
            handle Reg { fn reg(g) { g()\n resume(()) }\n fn ping() { resume(()) } } in reg(|| ping())\n\
            }\n";
        let mut srcs = vec![("own".to_string(), own.to_string())];
        for name in [
            "n04_loop_instance_bad.wf",
            "n05_scope_fail_bad.wf",
            "c11_c2_loop_instance_bad.wf",
        ] {
            srcs.push((name.to_string(), probe("fixes/r0kb1", name)));
        }
        for (name, src) in srcs {
            let (_, b) = built(&src);
            assert!(
                instantiate(&b).is_none_or(|i| i.regions == 0),
                "{name}: a copy region"
            );
        }
    }
}

/// The environment local of a copy region (plan stage R0k-b2,
/// `instantiate::Inst::env_capture_ok`): a copy reads a capture that it cannot
/// name through a place of the site as a cell of the closure value.
mod copy_env {
    use weft_ir::{LocalKind, Operand, Program, Proj, TermKind};
    use weft_sema::factgen::instantiate::instantiate;
    use weft_sema::irbuild::Built;

    /// The IR of `src`.
    fn built(src: &str) -> Built {
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::default());
        weft_sema::irbuild::build(&a)
    }

    /// The text of probe `name` of `tests/gate/probes/dir`.
    fn probe(dir: &str, name: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes")
            .join(dir)
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    }

    /// The region of `p` with an environment local, and each operand of a
    /// terminator of the region that is a field of that local.
    fn env_region(p: &Program) -> (&weft_ir::CopyRegion, Vec<Operand>) {
        let r = p
            .regions
            .iter()
            .find(|r| r.env_local.is_some())
            .expect("a region with an environment local");
        let e = r.env_local.expect("an environment local");
        let body = &p.bodies[r.body.index()];
        assert_eq!(body.local_kind(e), Some(LocalKind::CopyEnv(r.closure)));
        let mut ops = Vec::new();
        for k in &r.blocks {
            match &body.blocks[k.index()].term.kind {
                TermKind::Perform { args, .. } | TermKind::Call { args, .. } => {
                    for a in args {
                        if a.place().is_some_and(|q| q.local == e) {
                            ops.push(a.clone());
                        }
                    }
                }
                _ => {}
            }
        }
        (r, ops)
    }

    /// Asserts that `p` breaks no rule of the verifier but V16, the order of
    /// a cleanup chain, which does not hold across a copy (`instantiate`).
    fn verifies(b: &Built) {
        let broken = weft_ir::verify::verify_program(&b.program, &b.tys);
        assert!(
            broken
                .iter()
                .all(|x| x.rule == weft_ir::verify::Rule::UnwindOrder),
            "{broken:?}"
        );
    }

    /// Form 2 with a capture: the closure of `mk` keeps its parameter `h`.
    /// The frame of `mk` ends before the run, so the copy at the run reads
    /// `h` as `copy e.0`, a cell of the closure value. The region has the
    /// environment of the call of `mk`.
    #[test]
    fn a_capture_of_a_closure_that_a_callee_makes_is_a_cell_of_the_value() {
        for (dir, name) in [
            ("fixes/r0kb2", "e01_callee_capture_bad.wf"),
            ("fixes/r0kb1", "c10_c2_mk_in_H_run_in_H2_bad.wf"),
            ("fixes/r0k3", "h03_made_closure_keep_bad.wf"),
        ] {
            let inst = instantiate(&built(&probe(dir, name))).expect("a copy");
            let p = &inst.built.program;
            let (r, ops) = env_region(p);
            assert!(
                ops.iter().any(|o| matches!(o, Operand::Copy(q)
                    if q.proj == vec![Proj::Field(weft_ir::FieldIdx(0))])),
                "{name}: {ops:?}"
            );
            // The entry reads the closure value first.
            let body = &p.bodies[r.body.index()];
            assert!(matches!(
                body.blocks[r.entry.index()].stmts.first().map(|x| &x.kind),
                Some(weft_ir::StmtKind::Mention(q)) if *q == r.value
            ));
            verifies(&inst.built);
        }
    }

    /// A source that ends before the run (`e03`): the closure keeps `x`, a
    /// local of a block that ends before the run. The cell stays alive
    /// through the closure value, so the copy reads it through the
    /// environment local. The copy is a region in the body of its maker.
    #[test]
    fn a_capture_whose_source_ends_before_the_run_is_a_cell_of_the_value() {
        let inst =
            instantiate(&built(&probe("fixes/r0kb2", "e03_source_ends_bad.wf"))).expect("a copy");
        let p = &inst.built.program;
        let (r, _) = env_region(p);
        assert_eq!(p.closures[r.closure.index()].maker, r.body);
        verifies(&inst.built);
    }

    /// Form 3: a closure in a field of a struct (`e04`, `c18`) and in the
    /// payload of an `Option` (`e05`) that a callee gives back. The site
    /// reads the part into a local and runs it: the run gets a region.
    #[test]
    fn a_closure_in_a_field_or_a_variant_gets_a_copy_region() {
        for (dir, name) in [
            ("fixes/r0kb2", "e04_field_bad.wf"),
            ("fixes/r0kb2", "e05_option_bad.wf"),
            ("fixes/r0kb1", "c18_c2_field_bad.wf"),
        ] {
            let inst = instantiate(&built(&probe(dir, name))).expect("a copy");
            let (r, _) = env_region(&inst.built.program);
            assert!(r.sole, "{name}: the region is not the only run");
            verifies(&inst.built);
        }
    }

    /// The refusals: a closure that a callee gives back on one of two paths
    /// (`a01`), a closure in a `Vec` (`a02`), a field that a callee can write
    /// through a borrow (`a03`), a local that a scope body, a clause or a
    /// task writes (`u12` to `u14`), a `once` closure (`o01`), and a closure
    /// that writes its capture. Each run keeps the summary of the closure.
    #[test]
    fn a_capture_cell_that_can_change_or_an_unknown_closure_gets_no_copy() {
        let writes = "effect Get { fn get() -> fn() }
            fn main() {
            let v = Vec.new()
            v.push(1)
            handle Get { fn get() { resume(|| v.clear()) } } in {
            let r = &v[0]
            let k = { let x = 7
            || { let g = get()
            g()
            x = x + 1
            print(x) } }
            k()
            print(r)
            }
            }
";
        let mut srcs = vec![("writes".to_string(), writes.to_string())];
        // From plan stage R0z Z3, `u12` and `u13` (a second write with a copy
        // of the same closure) and `o01` (a `once` closure) get a copy:
        // `a_second_write_with_a_copy_of_the_same_closure_gets_a_region`. From
        // plan stage R0z Z6, `a01` gets a dispatch (`r0z6::`).
        for name in [
            "a02_vec_same_id_bad.wf",
            "a03_put_fns_bad.wf",
            "u14_task_bad.wf",
        ] {
            srcs.push((name.to_string(), probe("fixes/r0kb2", name)));
        }
        for (name, src) in srcs {
            let b = built(&src);
            assert!(
                instantiate(&b).is_none_or(|i| i
                    .built
                    .program
                    .regions
                    .iter()
                    .all(|r| r.env_local.is_none())),
                "{name}: a copy with an environment local"
            );
        }
    }
}

/// Plan stage R0z Z3: the small steps of the way of a closure value.
mod r0z3 {
    use weft_ir::{LocalKind, Program};
    use weft_sema::factgen::instantiate::instantiate;
    use weft_sema::irbuild::Built;

    /// The analysis of `src` and its IR.
    fn built(src: &str) -> (weft_sema::Analysis, Built) {
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::default());
        let b = weft_sema::irbuild::build(&a);
        (a, b)
    }

    /// The text of probe `name` of `dir` in `tests/gate/probes`.
    fn probe(dir: &str, name: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes")
            .join(dir)
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    }

    /// The facts of the program with the copies of `b`, with the weak form if
    /// the copies allow it.
    fn full(a: &weft_sema::Analysis, b: &Built) -> (Program, bool) {
        let inst = instantiate(b).expect("a copy");
        let _weak = inst
            .weak_ok
            .then(weft_sema::analysis::transfer::WeakRowOps::enter);
        let ok = weft_sema::factgen::components(a, &inst.built).is_ok();
        (inst.built.program, ok)
    }

    /// Part a: a scope body (`u12`) or a clause (`u13`) gives the local of
    /// the way a second closure of `mk`. After the copies of `mk` at its
    /// calls the two values are copies of one closure, so the run gets a copy
    /// region that names both and reads each capture but `Cap` through its
    /// environment local. The program has full facts.
    #[test]
    fn a_second_write_with_a_copy_of_the_same_closure_gets_a_region() {
        for name in ["u12_scope_body_bad.wf", "u13_clause_bad.wf"] {
            let (a, b) = built(&probe("fixes/r0kb2", name));
            let (p, ok) = full(&a, &b);
            let r = p
                .regions
                .iter()
                .find(|r| !r.also.is_empty())
                .unwrap_or_else(|| panic!("{name}: no region with two closures"));
            assert!(r.env_local.is_some() && !r.sole, "{name}");
            let d = &p.closures[r.closure.index()];
            for c in &r.also {
                assert_eq!(p.closures[c.index()].captures.len(), d.captures.len());
            }
            assert!(ok, "{name}: no full facts");
        }
    }

    /// Part a, the refusals: the second value is a closure of another
    /// function (`a1`), or a task writes the local through the environment of
    /// its closure (`a4`). No region names two closures.
    #[test]
    fn a_second_write_of_another_closure_or_by_a_task_gets_no_region() {
        for name in ["a1_other_maker_bad.wf", "a4_task_writes_bad.wf"] {
            let (_, b) = built(&probe("fixes/r0z3", name));
            assert!(
                instantiate(&b).is_none_or(|i| i
                    .built
                    .program
                    .regions
                    .iter()
                    .all(|r| r.also.is_empty())),
                "{name}"
            );
        }
    }

    /// Fix 2 of the review of Z3: the local of the way gets two closures of
    /// `mk`, and each one runs (`n1`, `n2`), so the clause of `Run` runs at two
    /// nodes and its facts would join the two values: no region names two
    /// closures. With one run (`p1`) the region names both.
    #[test]
    fn a_region_with_two_closures_is_refused_if_its_clause_runs_at_two_nodes() {
        for name in ["n1_two_runs_keep_ok.wf", "n2_two_runs_field_ok.wf"] {
            let (_, b) = built(&probe("fixes/r0z3", name));
            assert!(
                instantiate(&b).is_none_or(|i| i
                    .built
                    .program
                    .regions
                    .iter()
                    .all(|r| r.also.is_empty())),
                "{name}"
            );
        }
        let (a, b) = built(&probe("fixes/r0z3", "p1_first_value_gone_ok.wf"));
        let (p, ok) = full(&a, &b);
        assert!(p.regions.iter().any(|r| !r.also.is_empty()));
        assert!(ok);
    }

    /// Fix 3 of the review of Z3: a clause gives the local of the way its
    /// second closure, but a callee performs the operation (`w1`), or the
    /// clause writes after its `resume` (`w2`): no region names two closures.
    /// The form of `u13` (one direct perform before the run, the write before
    /// the `resume`) keeps its region
    /// (`a_second_write_with_a_copy_of_the_same_closure_gets_a_region`).
    #[test]
    fn a_clause_write_of_another_form_than_u13_gets_no_region() {
        for name in ["w1_clause_callee_ok.wf", "w2_after_resume_ok.wf"] {
            let (_, b) = built(&probe("fixes/r0z3", name));
            assert!(
                instantiate(&b).is_none_or(|i| i
                    .built
                    .program
                    .regions
                    .iter()
                    .all(|r| r.also.is_empty())),
                "{name}"
            );
        }
    }

    /// Part d: the two runs of the `once` closure of `o01` each get a copy
    /// region whose value is a new local; the second move of the closure value
    /// is the W0502 of the facts.
    #[test]
    fn each_run_of_a_once_closure_gets_a_region_on_a_new_local() {
        let (a, b) = built(&probe("fixes/r0kb2", "o01_once_two_runs_bad.wf"));
        let (p, ok) = full(&a, &b);
        assert_eq!(p.regions.len(), 2);
        for r in &p.regions {
            assert!(matches!(
                p.bodies[r.body.index()].local_kind(r.value.local),
                Some(LocalKind::Temp(_))
            ));
        }
        assert!(ok);
    }

    /// Part c: the site reads `b.n`, a part with no function type, so the
    /// region of `e04b` is the only run of the closure (`sole`), and the
    /// program has full facts. A read of a part with a function type (`c1`)
    /// is a use that can run the closure: no `sole`.
    #[test]
    fn a_read_of_a_part_with_no_function_type_keeps_the_region_sole() {
        let (a, b) = built(&probe("fixes/r0kb2", "e04b_field_read_bad.wf"));
        let (p, ok) = full(&a, &b);
        assert!(p.regions.iter().any(|r| r.sole));
        assert!(ok);
        let (_, b) = built(&probe("fixes/r0z3", "c1_fn_field_read_bad.wf"));
        let inst = instantiate(&b).expect("a copy");
        assert!(inst.built.program.regions.iter().all(|r| !r.sole));
    }

    /// Part f: `n03_clause_runs_ok` has only the pending reason of a perform
    /// whose rest of the handled body the facts do not find. With the copies
    /// the clause runs a copy of the closure body, and the facts are full.
    #[test]
    fn a_program_whose_only_reason_is_rest_not_found_gets_the_copies() {
        let (a, b) = built(&probe("fixes/r0kb1", "n03_clause_runs_ok.wf"));
        let Err(u) = weft_sema::factgen::components(&a, &b) else {
            panic!("no pending reason");
        };
        assert_eq!(u.reason, weft_sema::factgen::handlers::REST_NOT_FOUND);
        let (_, ok) = full(&a, &b);
        assert!(ok);
    }
}

/// The dispatches of plan stage R0z Z6 (`docs/ir.md` 6.1, "As built (plan
/// stage R0z Z6)"): a run whose value can be closures of two or more origins
/// gets a test of the closure and one arm for each group.
mod r0z6 {
    use weft_ir::verify::{verify_program, Rule};
    use weft_ir::{Program, Rvalue, StmtKind, TermKind};
    use weft_sema::factgen::instantiate::instantiate;
    use weft_sema::factgen::{nodes, DISPATCH_MISS};
    use weft_sema::irbuild::Built;

    /// The analysis of `src` and its IR.
    fn built(src: &str) -> (weft_sema::Analysis, Built) {
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::default());
        let b = weft_sema::irbuild::build(&a);
        (a, b)
    }

    /// The text of probe `name` of `dir` in `tests/gate/probes`.
    fn probe(dir: &str, name: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes")
            .join(dir)
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    }

    /// The components of the program `b` (with the weak form if `weak`).
    fn comps(
        a: &weft_sema::Analysis,
        b: &Built,
        weak: bool,
    ) -> Result<Vec<weft_sema::factgen::Component>, weft_sema::factgen::Unsupported> {
        let _weak = weak.then(weft_sema::analysis::transfer::WeakRowOps::enter);
        weft_sema::factgen::components(a, b)
    }

    /// The program of probe `dir/name` with the copies, and its weak form.
    fn copied(dir: &str, name: &str) -> (weft_sema::Analysis, Built, bool) {
        let (a, b) = built(&probe(dir, name));
        let inst = instantiate(&b).unwrap_or_else(|| panic!("{name}: no copy"));
        (a, inst.built, inst.weak_ok)
    }

    /// The targets of the stage: the value set of the run has two origins, so
    /// the run gets a dispatch with two arms. Each arm with a region copies the
    /// closures of its group, the program is well formed, and its facts are
    /// full.
    #[test]
    fn a_run_with_closures_of_two_origins_gets_a_dispatch() {
        for (dir, name) in [
            ("fixes/r0k2", "u03_callee_reassigns_via_clause.wf"),
            ("fixes/r0k2", "u05_scope_body.wf"),
            ("fixes/r0k2", "u06_handled_body.wf"),
            ("fixes/r0k2", "u07_if_branch.wf"),
            ("fixes/r0k2", "u11_clause_harmless_then.wf"),
            ("fixes/r0kb2", "a01_two_paths_bad.wf"),
            ("fixes/r0k2", "a04_two_closures_bad.wf"),
            ("fixes/r0z3", "a1_other_maker_bad.wf"),
        ] {
            let (a, b, weak) = copied(dir, name);
            let p = &b.program;
            assert_eq!(p.dispatches.len(), 1, "{name}");
            let d = &p.dispatches[0];
            assert_eq!(d.arms.len(), 2, "{name}");
            for arm in &d.arms {
                if let Some(i) = arm.region {
                    let r = &p.regions[i];
                    let mut cs: Vec<_> = r.closures().collect();
                    cs.sort();
                    let mut want = arm.closures.clone();
                    want.sort();
                    assert_eq!(cs, want, "{name}");
                }
            }
            // The order rules of a cleanup chain do not hold across a copy
            // (`instantiate` lets them go); V19 and V20 hold.
            assert!(
                !verify_program(p, &b.tys)
                    .iter()
                    .any(|x| matches!(x.rule, Rule::BadDispatch | Rule::BadRegion)),
                "{name}"
            );
            assert!(comps(&a, &b, weak).is_ok(), "{name}: no full facts");
        }
    }

    /// A closure that needs no copy (no served operation) is a plain arm: the
    /// call stays, and the analysis gives it only the closures of its group.
    /// The region of the other closure of `a01` stays `sole`: the test and the
    /// plain arm do not run it.
    #[test]
    fn a_closure_that_needs_no_copy_is_a_plain_arm() {
        for (dir, name) in [
            ("fixes/r0k2", "u11_clause_harmless_then.wf"),
            ("fixes/r0kb2", "a01_two_paths_ok.wf"),
        ] {
            let (_, b, _) = copied(dir, name);
            let d = &b.program.dispatches[0];
            assert!(d.arms.iter().any(|x| x.region.is_none()), "{name}");
            assert!(d.arms.iter().any(|x| x.region.is_some()), "{name}");
        }
        let (_, b, _) = copied("fixes/r0kb2", "a01_two_paths_bad.wf");
        assert!(b.program.regions.iter().any(|r| r.sole));
    }

    /// The refusals: a value that the walk does not know (a parameter), a
    /// value from a field with two values, a heap slot, a dispatch in a clause
    /// of a program with a `multi` operation (R-ROW), a dispatch in a copy
    /// region, a closure that a recursive callee gives back (the form `h1` of
    /// the review, in the source of the test).
    #[test]
    fn a_dispatch_is_refused_for_the_forms_that_the_walk_does_not_take() {
        for name in [
            "t08_unknown_bad.wf",
            "t12_field_bad.wf",
            "t13_vec_bad.wf",
            "t09b_clause_row_bad.wf",
            "t14_nested_region_bad.wf",
        ] {
            let (_, b) = built(&probe("fixes/r0z6", name));
            assert!(
                instantiate(&b).is_none_or(|i| i.built.program.dispatches.is_empty()),
                "{name}"
            );
        }
        // The form `h1` of the review: `k` gets the closure of the recursive `mk`
        // from two calls, under two handlers of `Run`. A recursive maker gets no
        // copy at its calls, so both values have one closure id; the walk takes
        // no closure that a callee gives back, so no dispatch.
        let (_, b) = built(TWO_CALLS_ONE_ID);
        assert!(instantiate(&b).is_none_or(|i| i.built.program.dispatches.is_empty()));
    }

    /// The refusals of the review of Z6: R-JOIN (two dispatches one after the
    /// other give values to the clause of one operation; a run of a value that
    /// the walk does not know, `rev2_b05`), and R-ROW for a run in the handled
    /// body of a local handler of a `multi` operation. No dispatch. The targets keep theirs
    /// (`a_run_with_closures_of_two_origins_gets_a_dispatch`).
    #[test]
    fn a_dispatch_is_refused_for_the_forms_of_the_review() {
        for name in [
            "rev1_fp_d06_unrolled_j3_ok.wf",
            "rev1_r01_local_multi_bad.wf",
            "rev1_r11_resume_ref_ok.wf",
            "rev1_r14_outer_first_bad.wf",
            "rev2_b05_mkff_callee_ok.wf",
        ] {
            let (_, b) = built(&probe("fixes/r0z6", name));
            assert!(
                instantiate(&b).is_none_or(|i| i.built.program.dispatches.is_empty()),
                "{name}"
            );
        }
    }

    /// The root fix of round 3 of the review of Z6: a run of a function value
    /// that holds a reference, and that runs no clause, gives nothing to the
    /// parameters of a clause (`clause::call_landings` takes the handlers of
    /// `clause::run_handlers`). So the forms that rounds 1 and 2 refused (R-REF)
    /// get a dispatch with full facts (`weft-check`, `ir_handlers.rs`: no error
    /// there, and none in the forms with one value, where main gave a false
    /// W0301).
    #[test]
    fn a_run_that_runs_no_clause_gives_nothing_to_the_clause_parameters() {
        for name in [
            "rev1_fp_m6_dispatch_ok.wf",
            "rev1_fp_v1_ff_outer_ok.wf",
            "rev2_b01_ff_before_handle_ok.wf",
            "rev2_b19_param_cond_ok.wf",
            "rev3_h1_ff_in_arm_ok.wf",
            "rev3_h4_ff_in_other_arm_ok.wf",
        ] {
            let (a, b, weak) = copied("fixes/r0z6", name);
            assert_eq!(b.program.dispatches.len(), 1, "{name}");
            assert!(comps(&a, &b, weak).is_ok(), "{name}: no full facts");
        }
    }

    /// The form `h1` of the review of Z6.
    const TWO_CALLS_ONE_ID: &str = "effect Run { fn run(g: fn()) }
fn mk(n: u64) -> fn() / Run {
    if n > 0 { mk(n - 1) } else { || run(|| print(1)) }
}
fn main() {
    let t = true
    handle Run { fn run(g) { print(7)
        resume(()) } } in {
        let k = mk(1)
        handle Run { fn run(g) { print(9)
            resume(()) } } in {
            if t { k = mk(0) }
            k()
        }
    }
}
";

    /// A dead arm: the scope body of `t15_first_gone_ok` gives `k` its second
    /// value on each path, so the analysis finds the arm of the first value
    /// dead, the static check allows it, and the facts have no edge into the
    /// arm. In the bad twin the scope body writes only if `t`: the arm is
    /// live, and its edge stays.
    #[test]
    fn the_arm_of_a_value_that_each_path_replaces_is_dead() {
        for (name, dead) in [
            ("t15_first_gone_ok.wf", true),
            ("t15_first_gone_bad.wf", false),
        ] {
            let (a, b, weak) = copied("fixes/r0z6", name);
            let d = b.program.dispatches[0].clone();
            let cs = comps(&a, &b, weak).unwrap_or_else(|u| panic!("{name}: {u}"));
            let arm = &d.arms[0];
            assert!(arm.killable, "{name}");
            let c = cs
                .iter()
                .find(|c| {
                    c.emitted
                        .table
                        .first(d.body, arm.entry, nodes::NORMAL)
                        .is_some()
                })
                .unwrap_or_else(|| panic!("{name}: no component"));
            let n = c.emitted.table.first(d.body, arm.entry, nodes::NORMAL);
            let has_edge = c.facts.cfg_edge.iter().any(|&(_, to)| Some(to) == n);
            assert_eq!(has_edge, !dead, "{name}");
        }
    }

    /// The static check and the analysis disagree: an arm that the analysis
    /// finds dead and that the static check does not allow (made by hand),
    /// and a dispatch whose tests do not know a closure that the analysis
    /// finds at the run (made by hand): `DISPATCH_MISS`, the program keeps
    /// its fallback.
    #[test]
    fn a_dispatch_that_the_analysis_does_not_agree_with_is_a_miss() {
        let (a, mut b, weak) = copied("fixes/r0z6", "t15_first_gone_ok.wf");
        for arm in &mut b.program.dispatches[0].arms {
            arm.killable = false;
        }
        let err = comps(&a, &b, weak).err().map(|u| u.reason);
        assert_eq!(err.as_deref(), Some(DISPATCH_MISS));
        let (a, mut b, weak) = copied("fixes/r0k2", "u07_if_branch.wf");
        // The second test names another closure (the inner closure of the
        // first arm): the value of the run can be a closure that no test knows.
        let d = b.program.dispatches[0].clone();
        let other = b
            .program
            .closures
            .iter()
            .position(|c| c.maker == b.program.closures[d.arms[0].closures[0].index()].body)
            .map(|i| weft_ir::ClosureId(u32::try_from(i).unwrap_or(0)))
            .expect("an inner closure");
        b.program.dispatches[0].arms[1].closures = vec![other];
        let test = d.arms[1].test;
        let body = &mut b.program.bodies[d.body.index()];
        if let Some(StmtKind::Assign(_, Rvalue::ClosureIs(_, cs))) = body.blocks[test.index()]
            .stmts
            .last_mut()
            .map(|s| &mut s.kind)
        {
            *cs = vec![other];
        }
        let err = comps(&a, &b, weak).err().map(|u| u.reason);
        assert_eq!(err.as_deref(), Some(DISPATCH_MISS));
    }

    /// V20: a `ClosureIs` that is not the test of a dispatch, a miss block that
    /// is not `Unreachable`, and a region whose closures are not those of its
    /// arm break the rule.
    #[test]
    fn a_dispatch_that_is_not_well_formed_breaks_v20() {
        let (_, b, _) = copied("fixes/r0k2", "u07_if_branch.wf");
        let bad = |p: &Program| {
            verify_program(p, &b.tys)
                .iter()
                .any(|x| x.rule == Rule::BadDispatch)
        };
        assert!(!bad(&b.program));
        let d = b.program.dispatches[0].clone();
        let mut p = b.program.clone();
        p.bodies[d.body.index()].blocks[d.miss.index()].term.kind = TermKind::Return;
        assert!(bad(&p));
        let mut p = b.program.clone();
        p.dispatches.clear();
        assert!(bad(&p));
        let mut p = b.program.clone();
        let other = p.dispatches[0].arms[1].closures.clone();
        p.dispatches[0].arms[0].closures.clone_from(&other);
        assert!(bad(&p));
    }

    /// Part B: the clause of `Sw` gives `k` its second closure, and a callee
    /// performs `sw` (`u10`). The pre-scan gives the call of the callee a copy,
    /// so the clause has one direct perform (the form of `u13`), and the run
    /// gets a dispatch.
    #[test]
    fn a_callee_that_runs_the_clause_of_a_write_gets_a_copy() {
        let (a, b) = built(&probe("fixes/r0k2", "u10_clause_of_inner.wf"));
        let inst = instantiate(&b).expect("a copy");
        assert!(inst.calls >= 1);
        assert_eq!(inst.built.program.dispatches.len(), 1);
        assert!(comps(&a, &inst.built, inst.weak_ok).is_ok());
    }
}

/// The copies of a closure that resumes the continuation of its clause
/// (stage R0k-c1, `instantiate::instantiate_kont`). Each refusal is a hard
/// rule (`docs/ir.md` 6.1, "As built (plan stage R0k-c1)").
mod kont_copies {
    use weft_ir::{BodyKind, LocalKind, Program, Rvalue, StmtKind, TermKind};
    use weft_sema::factgen::instantiate::{instantiate_kont, Instantiated};

    /// The analysis of `src` and its IR.
    fn built(src: &str) -> (weft_sema::Analysis, weft_sema::irbuild::Built) {
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::default());
        let b = weft_sema::irbuild::build(&a);
        (a, b)
    }

    /// The source of probe `name` of `tests/gate/probes/fixes/r0kc`.
    fn probe(name: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0kc")
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    }

    /// The copies of the program of `src`, if a closure got one.
    fn copies(src: &str) -> Option<Instantiated> {
        let (_, b) = built(src);
        instantiate_kont(&b).filter(|i| !i.covered.is_empty())
    }

    /// The clause bodies of `p`.
    fn clauses(p: &Program) -> Vec<&weft_ir::Body> {
        p.bodies
            .iter()
            .filter(|b| matches!(b.kind, BodyKind::Clause(..)))
            .collect()
    }

    /// True if a clause of `p` makes closure `c`.
    fn makes(p: &Program, c: weft_ir::ClosureId) -> bool {
        clauses(p).iter().any(|b| {
            b.blocks.iter().flat_map(|k| &k.stmts).any(|s| {
                matches!(&s.kind, StmtKind::Assign(_, Rvalue::Aggregate(weft_ir::AggKind::Closure(x), _)) if *x == c)
            })
        })
    }

    /// True if a clause of `p` resumes its own continuation local.
    fn resumes_own(p: &Program) -> bool {
        clauses(p).iter().any(|b| {
            b.blocks.iter().any(|k| match &k.term.kind {
                TermKind::Resume { kont, .. } => {
                    kont.is_local() && matches!(b.local_kind(kont.local), Some(LocalKind::Kont(_)))
                }
                _ => false,
            })
        })
    }

    /// A `once` continuation moves into the closure: the run gets a copy
    /// that resumes the continuation of the clause, and the make goes.
    #[test]
    fn a_once_continuation_closure_gets_a_copy_and_its_make_goes() {
        let inst = copies(&probe("c01_once_ok.wf")).expect("a copy");
        assert_eq!(inst.closure_calls, 1);
        let c = *inst.covered.iter().next().expect("a closure");
        assert!(!makes(&inst.built.program, c), "the make stays");
        assert!(resumes_own(&inst.built.program), "no resume of the clause");
    }

    /// A `multi` continuation is captured by copy: the copy reads it, and
    /// the make stays.
    #[test]
    fn a_multi_continuation_closure_keeps_its_make() {
        let inst = copies(&probe("c02_multi_ok.wf")).expect("a copy");
        assert_eq!(inst.closure_calls, 1);
        let c = *inst.covered.iter().next().expect("a closure");
        assert!(makes(&inst.built.program, c), "the make goes");
        assert!(resumes_own(&inst.built.program), "no resume of the clause");
    }

    /// D1c: the callee that gets the closure gets a copy at the call, then
    /// the run in that copy gets a copy of the closure body.
    #[test]
    fn a_closure_given_to_a_callee_gets_a_copy_in_the_copy_of_the_callee() {
        let inst = copies(&probe("c04_callee_ok.wf")).expect("a copy");
        assert_eq!(inst.calls, 1);
        assert_eq!(inst.closure_calls, 1);
        assert!(resumes_own(&inst.built.program), "no resume of the clause");
    }

    /// The refusal probes of stage R0k-c1. Two runs, a perform between the
    /// make and the run, a call that can abort between them, a borrow of the
    /// closure value and a field on the chain get a kont region from plan
    /// stage R0z Z4 (`r0z4::`). A make and a run in a handled body inside the
    /// clause get no copy (a resume point in a handled body inside the clause
    /// is not built).
    #[test]
    fn the_probes_of_a_refusal_get_no_copy() {
        for name in ["c08_nested_ok.wf", "c08_nested_bad.wf"] {
            assert!(copies(&probe(name)).is_none(), "{name}: a copy");
        }
        for name in [
            "c03_two_runs_ok.wf",
            "c05_perform_between_ok.wf",
            "c06_call_between_ok.wf",
            "c07_use_after_ok.wf",
            "c09_field_ok.wf",
        ] {
            let inst = copies(&probe(name)).unwrap_or_else(|| panic!("{name}: no copy"));
            assert!(
                inst.built.program.regions.iter().any(|r| r.kont.is_some()),
                "{name}: no kont region"
            );
        }
    }

    /// The continuation is named again after the make (a `resume` of the
    /// clause after the run): no copy of stage R0k-c1.
    #[test]
    fn a_continuation_named_after_the_make_refuses_the_copy() {
        let src = "effect Tick { multi fn tick() }
fn main() {
    handle Tick { fn tick() {
        let k = || resume(())
        k()
        resume(())
    } } in { tick() }
}
";
        // No copy of stage R0k-c1; the run gets a kont region of plan stage
        // R0z Z4 (the `resume` of the clause is another resume point).
        assert!(copies(src).is_some_and(|i| i
            .built
            .program
            .regions
            .iter()
            .all(|r| r.kont.is_some())));
    }

    /// A body inside the clause names a local of the chain (it runs the
    /// closure again): no copy.
    #[test]
    fn a_body_inside_the_clause_that_names_the_chain_refuses_the_copy() {
        let src = "effect Tick { multi fn tick() }
effect Other { fn other() }
fn main() {
    handle Tick { fn tick() {
        let k = || resume(())
        k()
        handle Other { fn other() { resume(()) } } in { k() }
    } } in { tick() }
}
";
        assert!(copies(src).is_none());
    }

    /// A task runs the closure: a spawn is no call, so no copy.
    #[test]
    fn a_spawn_of_the_closure_gets_no_copy() {
        let src = "effect Tick { fn tick() }
fn main() / async {
    handle Tick { fn tick() {
        let k = || resume(())
        scope { s => s.spawn(k) }
    } } in { tick() }
}
";
        assert!(copies(src).is_none());
    }

    /// A path from the make that does not reach the run (a branch): no copy
    /// of stage R0k-c1.
    #[test]
    fn a_path_from_the_make_that_misses_the_run_refuses_the_copy() {
        let src = "effect Tick { fn tick(b: bool) }
fn main() {
    handle Tick { fn tick(b) {
        let k = || resume(())
        if b { k() }
    } } in { tick(true) }
}
";
        // No copy of stage R0k-c1 (its make would go); the run gets a kont
        // region of plan stage R0z Z4, which keeps the make.
        let inst = copies(src).expect("a kont region");
        assert!(inst.built.program.regions.iter().all(|r| r.kont.is_some()));
    }

    /// The program with the copies is the view that the check takes if the
    /// facts without them find no error (`factgen::Pending::copy`).
    #[test]
    fn a_pending_program_with_copies_gets_the_view_of_the_copies() {
        let (a, _) = built(&probe("c01_once_ok.wf"));
        let p = a
            .ir_scope
            .as_ref()
            .and_then(|s| s.pending.as_ref())
            .expect("pending");
        assert!(p.copy.is_some(), "no view of the copies");
        let (a, _) = built(&probe("c08_nested_ok.wf"));
        let p = a
            .ir_scope
            .as_ref()
            .and_then(|s| s.pending.as_ref())
            .expect("pending");
        assert!(p.copy.is_none(), "a view of the copies");
    }
}

/// Plan stage R0z Z4: a run of a closure that resumes the continuation of the
/// clause that made it gets a kont region (`instantiate::Inst::kont_region`),
/// a copy region that reads the `Kont` capture through its environment local.
mod r0z4 {
    use weft_ir::verify::{verify_program, Rule};
    use weft_ir::{LocalKind, TermKind};
    use weft_sema::factgen::instantiate::{instantiate_kont, Instantiated};

    /// The analysis of `src` and its IR.
    fn built(src: &str) -> (weft_sema::Analysis, weft_sema::irbuild::Built) {
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::default());
        let b = weft_sema::irbuild::build(&a);
        (a, b)
    }

    /// The text of probe `name` of `tests/gate/probes/fixes/dir`.
    fn probe(dir: &str, name: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes")
            .join(dir)
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    }

    /// The copies of the kont mode of `src`, if a closure got one.
    fn copies(src: &str) -> Option<Instantiated> {
        let (_, b) = built(src);
        instantiate_kont(&b).filter(|i| !i.covered.is_empty())
    }

    /// True if the program of `src` has a kont region.
    fn has_region(src: &str) -> bool {
        copies(src).is_some_and(|i| i.built.program.regions.iter().any(|r| r.kont.is_some()))
    }

    /// True if the old pipeline checks the clean program `src`: the scope of
    /// the `ir` pipeline has a fallback, or a pending construct with no view
    /// of the copies (`factgen::Pending::copy`).
    fn falls_back(src: &str) -> bool {
        let (a, _) = built(src);
        a.ir_scope.as_ref().is_none_or(|s| {
            s.fallback.is_some() || s.pending.as_ref().is_some_and(|p| p.copy.is_none())
        })
    }

    /// The forms of the targets: two runs, a perform or a call between the
    /// make and the run, a borrow of the value, a field, a path with no run,
    /// code around the `resume`. Each run gets a kont region whose `Resume`
    /// reads field `kont` of the environment local, the program verifies, and
    /// the `ir` pipeline checks the program.
    #[test]
    fn a_run_of_a_continuation_closure_gets_a_kont_region() {
        let mut names: Vec<(&str, &str)> = Vec::new();
        for n in [
            "c03_two_runs",
            "c05_perform_between",
            "c06_call_between",
            "c07_use_after",
            "c09_field",
        ] {
            names.push(("r0kc", n));
        }
        for n in [
            "t01_abort_between",
            "t03_branch",
            "t05_post_code",
            "t06_clause_ref",
        ] {
            names.push(("r0z4", n));
        }
        for (dir, n) in names {
            for twin in ["ok", "bad"] {
                let name = format!("{n}_{twin}.wf");
                let src = probe(dir, &name);
                let inst = copies(&src).unwrap_or_else(|| panic!("{name}: no copy"));
                let p = &inst.built.program;
                let regions: Vec<_> = p.regions.iter().filter(|r| r.kont.is_some()).collect();
                assert!(!regions.is_empty(), "{name}: no kont region");
                for r in &regions {
                    let e = r
                        .env_local
                        .unwrap_or_else(|| panic!("{name}: no environment local"));
                    let body = p.body(r.body).unwrap_or_else(|| panic!("no body"));
                    assert_eq!(body.local_kind(e), Some(LocalKind::CopyEnv(r.closure)));
                    let resumes = r.blocks.iter().filter(|k| {
                        matches!(&body.blocks[k.index()].term.kind,
                            TermKind::Resume { kont, .. } if kont.local == e)
                    });
                    assert!(resumes.count() > 0, "{name}: no resume of the environment");
                }
                // V16 does not hold for a cleanup chain that starts in a block
                // of a copy in a clause (stage R0k-c1, `finish_inst`).
                assert!(
                    verify_program(p, &inst.built.tys)
                        .iter()
                        .all(|x| x.rule == Rule::UnwindOrder || x.rule == Rule::KontNotFirst),
                    "{name}: {:?}",
                    verify_program(p, &inst.built.tys)
                );
                if twin == "ok" {
                    assert!(!falls_back(&src), "{name}");
                }
            }
        }
    }

    /// V21: a `Resume` of a field of the environment local of a region that
    /// is not a kont region breaks `BadKont`.
    #[test]
    fn a_resume_of_the_environment_of_another_region_breaks_bad_kont() {
        let inst = copies(&probe("r0kc", "c05_perform_between_ok.wf")).expect("a copy");
        let mut p = inst.built.program.clone();
        for r in &mut p.regions {
            r.kont = None;
        }
        assert!(verify_program(&p, &inst.built.tys)
            .iter()
            .any(|x| x.rule == Rule::BadKont));
    }

    /// Each refusal keeps the fallback: R-WAY (a value through a parameter of
    /// the clause, a `Vec`, two origins), R-MAKER (the maker is a closure
    /// inside the clause), R-NESTED (a body inside the closure resumes),
    /// R-ROW-K (another handler of a `multi` operation: in the clause, in the
    /// rest of the handled body, through a callee, through a closure with a
    /// captured capability, and an outer handler of the same effect), R-A5 (a
    /// `multi` continuation and another handler), R-SITE (a second instance
    /// of the same handler by recursion: the review of Z4, round 1), R-MAKER
    /// in a scope body of the clause (the review of Z4, round 2), R-AFTER
    /// (a `once` closure that moves a capture after its `resume`).
    #[test]
    fn the_refusals_of_a_kont_region_keep_the_fallback() {
        for name in [
            "rev_w01_vec_ok.wf",
            "rev_w03_two_origins_ok.wf",
            "rev_w04_resume_value_param_ok.wf",
            "rev_m01_maker_closure_ok.wf",
            "rev_n01_nested_closure_ok.wf",
            "rev_n02_nested_handle_ok.wf",
            "rev_r01_clause_multi_ok.wf",
            "rev_r02_rest_multi_ok.wf",
            "rev_r04_rest_callee_row_ok.wf",
            "rev_r05_cap_closure_multi_ok.wf",
            "rev_r05_cap_closure_multi_bad.wf",
            "rev_r06_same_effect_outer_ok.wf",
            "rev_j2_rest_ref_outer_op_ok.wf",
            "t02_multi_row_ok.wf",
            "t07_once_capture_after_ok.wf",
            "rev1_r03_recursive_rest_ok.wf",
            "rev1_r03_recursive_rest_bad.wf",
            "rev1_r04_recursive_a5_ok.wf",
            "rev2_oc09_scope_run_ok.wf",
            "rev2_oc10_scope_make_ok.wf",
            "rev2_sc_k_scope_then_run_ok.wf",
        ] {
            let src = probe("r0z4", name);
            // In `m01`, `n01` and `n02` the copy of stage R0k-c1 of the outer
            // closure can put a make and a run into the clause, and that run
            // can get a kont region; the program keeps the fallback (the body
            // of the outer closure is not covered).
            // In `rev2_sc_k` the second run is in the clause body and gets a
            // region; the run in the scope body gets none, so the program
            // keeps the fallback.
            let via_copy = ["rev_m01", "rev_n01", "rev_n02", "rev2_sc_k"]
                .iter()
                .any(|x| name.starts_with(x));
            assert!(via_copy || !has_region(&src), "{name}: a kont region");
            if name.ends_with("_ok.wf") {
                assert!(falls_back(&src), "{name}: no fallback");
            }
        }
    }

    /// R-REC (the review of Z4, round 3, and the check of 29b6877): a `once`
    /// handler whose `handle` is in a function that runs again while it runs:
    /// a direct recursion (`rev3_*`), a function value that names it (`v1`),
    /// a callee that runs a function value of it (`v2`), a closure that calls
    /// it (`v3`). The clause of an inner instance performs the
    /// effect of the handler, which goes to the outer instance; the clause
    /// oracle A5 fails there (issue #97). No kont region, and the clean
    /// programs keep the fallback.
    #[test]
    fn a_handle_in_a_recursive_function_gets_no_kont_region() {
        for name in [
            "rev3_o03_once_rec_region_ok.wf",
            "rev3_o03_once_rec_region_bad.wf",
            "rev3_o06_once_rec_outer_n2_ok.wf",
            "rev3_o06_once_rec_outer_n2_bad.wf",
            "rev3_o09_rec_n3_ok.wf",
            "rev4_v1_fnval_ok.wf",
            "rev4_v1_fnval_bad.wf",
            "rev4_v2_helper_ok.wf",
            "rev4_v2_helper_bad.wf",
            "rev4_v3_closure_ok.wf",
        ] {
            let src = probe("r0z4", name);
            assert!(!has_region(&src), "{name}: a kont region");
            if name.ends_with("_ok.wf") {
                assert!(falls_back(&src), "{name}: no fallback");
            }
        }
    }

    /// R-SITE in a library (the review of Z4, round 2): code outside the
    /// program can run the `main` of a library many times, so its `handle`
    /// can have two live instances. The marker `// weft: library` keeps the
    /// fallback.
    #[test]
    fn a_handle_in_the_main_of_a_library_gets_no_kont_region() {
        let src = probe("r0z4", "rev2_l01_library_main_ok.wf");
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(&src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::from_markers(&src));
        let s = a.ir_scope.as_ref().expect("a scope");
        assert!(s.fallback.is_some() || s.pending.as_ref().is_some_and(|p| p.copy.is_none()));
    }

    /// R-SITE with no direct recursion (the review of Z4, round 1): `install`
    /// holds the handler, and it runs inside the handled body of another run
    /// of `install` through a function value. No kont region (the program is
    /// rejected with W0314 by both pipelines).
    #[test]
    fn a_handle_that_can_run_again_while_it_runs_gets_no_kont_region() {
        let src = probe("r0z4", "rev1_r05_nested_install_ok.wf");
        assert!(!has_region(&src));
    }

    /// A `multi` continuation whose clause is the only handler, and whose
    /// second activation resumes while the first waits (`q3`): the `multi`
    /// operations of the handler of the clause do not copy the clause frame,
    /// so the region is not refused.
    #[test]
    fn the_own_multi_operations_of_the_handler_do_not_refuse_the_region() {
        let src = probe("r0z4", "rev_q3_own_multi_ok.wf");
        assert!(has_region(&src));
        assert!(!falls_back(&src));
    }
}

/// Stage R0k-d1: a run of a clause outside its handled body (A) is pending
/// with a weak form, and a strong update after a `resume` of a `once`
/// continuation (D4).
mod r0kd1 {
    /// The scope of the `ir` pipeline for the probe `name` of
    /// `tests/gate/probes/fixes/r0kd1`: the reason of the fallback and of
    /// the pending construct.
    fn scope(name: &str) -> (Option<String>, Option<String>) {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0kd1")
            .join(name);
        let src =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(&src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::default());
        let s = a.ir_scope.expect("a scope");
        (s.fallback, s.pending.map(|p| p.reason))
    }

    /// A: the run of the clause maps to no node of the handled body. The
    /// program is not a fallback of the fact generator: it is pending, and
    /// the check decides (the `ir` pipeline rejects it: W0313).
    #[test]
    fn a_run_of_a_clause_outside_its_handled_body_is_pending() {
        let (fallback, pending) = scope("a01_escape_bad.wf");
        assert!(fallback.is_none(), "{fallback:?}");
        assert!(
            pending
                .as_deref()
                .is_some_and(|r| r.contains(weft_sema::factgen::handlers::REST_NOT_FOUND)),
            "{pending:?}"
        );
    }

    /// D4: a `once` continuation and a whole write of `f` on each path of
    /// the rest of the handled body: after the `resume`, `f` has only that
    /// value, so no escape is pending and the program is in scope.
    #[test]
    fn a_must_written_local_gets_a_strong_update_after_a_once_resume() {
        assert_eq!(scope("d01_strong_ok.wf"), (None, None));
    }

    /// D4: a `multi` continuation gets the strong update too (plan stage
    /// R0z Z8): no escape is pending and the program is in scope.
    #[test]
    fn a_multi_continuation_gets_the_strong_update_too() {
        assert_eq!(scope("d02_multi_weak.wf"), (None, None));
        assert_eq!(scope("d02_multi_ok.wf"), (None, None));
    }
}

/// Plan stage R0z Z8: the handler environment leftovers. (a) A closure that
/// a clause of an inner handler makes performs to the outer handler; (b) the
/// strong update after a `resume` of a `multi` continuation; (c) a closure
/// that runs a closure of its maker that performs through a capability that
/// both capture.
mod r0z8 {
    /// The analysis of probe `name` of `tests/gate/probes/fixes/r0z8`: the
    /// reason of the fallback, the reason of the pending construct, and the
    /// codes of the errors.
    fn check(name: &str) -> (Option<String>, Option<String>, Vec<String>) {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0z8")
            .join(name);
        let src =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let a = weft_sema::analyze_source(&src, weft_sema::Options::from_markers(&src))
            .unwrap_or_else(|d| panic!("{name}: {}", d.message));
        let s = a.ir_scope.clone().expect("a scope");
        let codes = a.diags.iter().map(|d| format!("{:?}", d.code)).collect();
        (s.fallback, s.pending.map(|p| p.reason), codes)
    }

    /// The clean probes of the three parts are in scope with no error.
    #[test]
    fn the_clean_forms_are_in_scope_with_no_error() {
        for name in [
            "a01_lexical_ok.wf",
            "a04_get_again_ok.wf",
            "a09_vec_ok.wf",
            "a10_lib_ok.wf",
            "b03_between_ok.wf",
            "b06_loop_ok.wf",
            "b07_two_runs_ok.wf",
            "b08_callee_ok.wf",
            "b11_closure_run_ok.wf",
            "c01_vec_ok.wf",
            "c05_callee_ok.wf",
            "c07_nested_ok.wf",
            "c08_dead_ok.wf",
            "c11_multi_ok.wf",
            "c13_plain_ok.wf",
            "c17_field_ok.wf",
            "c18_deep_ok.wf",
        ] {
            assert_eq!(check(name), (None, None, Vec::new()), "{name}");
        }
    }

    /// The bad twins: the `ir` pipeline rejects each one with W0313 (the
    /// closure leaves its handler).
    #[test]
    fn the_bad_twins_are_rejected() {
        for name in [
            "a01_lexical_bad.wf",
            "b02_multi_weak_bad.wf",
            "b06_loop_bad.wf",
            "b07_two_runs_bad.wf",
            "b08_callee_bad.wf",
            "b09_nested_bad.wf",
            "c01_vec_bad.wf",
            "c04_ret_bad.wf",
            "c10_two_bad.wf",
            "c18_deep_bad.wf",
        ] {
            let (fallback, _, codes) = check(name);
            assert!(fallback.is_none(), "{name}: {fallback:?}");
            assert!(codes.iter().any(|c| c == "W0313"), "{name}: {codes:?}");
        }
    }

    /// The refusals of the stage keep the fallback: (a) a closure of the
    /// clause with a capture of a local of the clause (the summary oracle A3
    /// fails at its run); (b) a `multi` continuation in a program with
    /// another local handler (the clause oracle A5 fails, issue #95).
    #[test]
    fn the_refusals_keep_the_fallback() {
        for name in ["a03_capture_ok.wf", "b09_nested_ok.wf"] {
            let (fallback, pending, codes) = check(name);
            assert!(codes.is_empty(), "{name}: {codes:?}");
            assert!(fallback.is_some() || pending.is_some(), "{name}");
        }
    }

    /// R-DEAD (the review of Z8, round 2): a closure that no code runs and
    /// that runs a closure of its maker keeps the pending escape of main.
    /// With the first rule of part (c) its run mapped to no node of the
    /// handled body (`REST_NOT_FOUND`), and the view of `c25_dead_closure_bad`
    /// with the copies of the callees went to the fallback (the old pipeline
    /// misses its fault). `c26`: a closure that other code runs captures the
    /// dead closure. The bad twin is in scope and rejected (W0314 of the
    /// analysis; the check adds W0301, as main); the clean twin keeps the
    /// fallback, as main.
    #[test]
    fn a_dead_closure_keeps_the_pending_escape() {
        for name in ["c25_dead_closure_bad.wf", "c26_dead_capture_bad.wf"] {
            let (fallback, _, codes) = check(name);
            assert!(fallback.is_none(), "{name}: {fallback:?}");
            assert!(codes.iter().any(|c| c == "W0314"), "{name}: {codes:?}");
        }
        let (fallback, pending, codes) = check("c25_dead_closure_ok.wf");
        assert!(codes.is_empty(), "{codes:?}");
        assert!(
            pending
                .as_deref()
                .is_some_and(|r| r.contains("a capability that leaves its handler")),
            "{fallback:?} {pending:?}"
        );
    }

    /// (a) A `multi` operation that gives the closure back keeps the
    /// fallback: the run of the clause stops at its first `resume`.
    #[test]
    fn a_multi_operation_that_gives_a_closure_back_keeps_the_fallback() {
        let (fallback, _, _) = check("a05_multi_ok.wf");
        assert!(
            fallback
                .as_deref()
                .is_some_and(|r| r.contains(weft_sema::analysis::clause::GIVES_BACK)),
            "{fallback:?}"
        );
    }
}

/// Stage R0k-d2: a task that runs a shared function variable is late
/// (`TASK_LATE`, pending) only if a write of the variable lies in the window
/// of the task: from the spawn to the `join` of its handle, in the scope body
/// of the spawn.
mod r0kd2 {
    /// The reason of the fallback and of the pending construct of probe
    /// `name` of `tests/gate/probes/fixes/r0kd2`.
    fn scope(name: &str) -> (Option<String>, Option<String>) {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0kd2")
            .join(name);
        let src =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(&src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::default());
        let s = a.ir_scope.expect("a scope");
        (s.fallback, s.pending.map(|p| p.reason))
    }

    /// True if the pending reason is the late task.
    fn late(p: Option<&str>) -> bool {
        p.is_some_and(|r| r.contains("a task that runs a function variable that gets a new value"))
    }

    /// A write before the spawn (two paths) or after the `join`: the program
    /// is in scope.
    #[test]
    fn a_write_out_of_the_window_of_the_task_is_not_late() {
        assert_eq!(scope("s1_before_spawn_ok.wf"), (None, None));
        assert_eq!(scope("s2_after_join_ok.wf"), (None, None));
    }

    /// A write between the spawn and the `join` is late.
    #[test]
    fn a_write_in_the_window_of_the_task_is_late() {
        let (_, pending) = scope("s2_in_window_bad.wf");
        assert!(late(pending.as_deref()), "{pending:?}");
    }

    /// A spawn in a closure on the scope of the body around it (stage R0z
    /// Z9b): the writes of the function around the scope before the scope
    /// are out of the window, so the program is in scope. The bad twin gives
    /// `f` a new value in the scope body: it stays late.
    #[test]
    fn a_spawn_in_a_closure_on_an_outer_scope_has_a_window() {
        assert_eq!(scope("s4_spawn_in_closure_ok.wf"), (None, None));
        let (_, pending) = scope("s4_spawn_in_closure_bad.wf");
        assert!(late(pending.as_deref()), "{pending:?}");
    }
}

/// Stage R0z Z9b: the window of a spawn in a body inside a scope body on the
/// scope of that body (a closure, a task, a clause). The task can outlive the
/// body of the spawn, up to the end of the scope. A write counts if it is in
/// the scope body, in a body inside it, in another body, or in the function
/// around the scope on a path from the end of the scope (a closure can go out
/// of the scope). The writes of that function before the scope do not count.
mod r0z9b {
    /// The analysis of probe `name` of `tests/gate/probes/fixes/r0z9b`: the
    /// reason of the fallback, the reason of the pending construct, and the
    /// codes of the errors.
    fn check(name: &str) -> (Option<String>, Option<String>, Vec<String>) {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0z9b")
            .join(name);
        let src =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let a = weft_sema::analyze_source(&src, weft_sema::Options::from_markers(&src))
            .unwrap_or_else(|d| panic!("{name}: {}", d.message));
        let s = a.ir_scope.clone().expect("a scope");
        let codes = a.diags.iter().map(|d| format!("{:?}", d.code)).collect();
        (s.fallback, s.pending.map(|p| p.reason), codes)
    }

    /// True if the pending reason is the late task.
    fn late(p: Option<&str>) -> bool {
        p.is_some_and(|r| r.contains("a task that runs a function variable that gets a new value"))
    }

    /// The clean forms with no write in the window are in scope with no
    /// error.
    #[test]
    fn the_clean_forms_are_in_scope_with_no_error() {
        for name in [
            "w01_twice_ok.wf",
            "w03_stored_ok.wf",
            "w05_in_task_ok.wf",
            "w06_callee_ok.wf",
            "w07_nested_ok.wf",
            "w11_clause_spawn_ok.wf",
            "w12_sim_ok.wf",
            "w13_timeout_ok.wf",
            "w14_rec_ok.wf",
            "w16_task_spawns_ok.wf",
        ] {
            assert_eq!(check(name), (None, None, Vec::new()), "{name}");
        }
    }

    /// The bad twins have a write in the window: the task stays late (the
    /// check gives W0405: the probes of the gate).
    #[test]
    fn a_write_in_the_window_is_late() {
        for name in [
            "w01_twice_bad.wf",
            "w03_stored_bad.wf",
            "w04_escape_bad.wf",
            "w05_in_task_bad.wf",
            "w06_callee_bad.wf",
            "w07_nested_bad.wf",
            "w09_join_inside_bad.wf",
            "w10_clause_scope_bad.wf",
            "w11_clause_spawn_bad.wf",
            "w12_sim_bad.wf",
            "w13_timeout_bad.wf",
            "w15_task_scope_bad.wf",
            "w16_task_spawns_bad.wf",
            "w18_loop_bad.wf",
            "w19_inner_closure_bad.wf",
        ] {
            let (_, pending, _) = check(name);
            assert!(late(pending.as_deref()), "{name}: {pending:?}");
        }
    }

    /// R-ESCAPE (review round 2): a function value can leave the function
    /// around the scope (its result, a field of its result, a `Vec`
    /// parameter). A closure that spawns on the scope can then run after the
    /// function returns, and its task runs in the caller, where the facts of
    /// the function do not follow it. The old rule stays: two writes of `f`,
    /// so the task is late (the pending rule; the old pipeline rejects the bad
    /// probes). The clean twin returns a function value that does not spawn:
    /// it keeps the fallback too.
    #[test]
    fn a_function_value_that_can_leave_the_parent_keeps_the_old_rule() {
        for name in [
            "x01_return_escape_bad.wf",
            "x01_return_fn_ok.wf",
            "x02_struct_return_bad.wf",
            "x03_vec_param_bad.wf",
        ] {
            let (_, pending, _) = check(name);
            assert!(late(pending.as_deref()), "{name}: {pending:?}");
        }
    }

    /// The refusals: the window is not exact, so the old rule stays (two
    /// writes: late). A write in the scope body before the closure; a
    /// `join` in another body; a scope in a clause or in a closure; a write
    /// in a loop after the scope.
    #[test]
    fn the_refusals_keep_the_old_rule() {
        for name in [
            "w02_before_make_ok.wf",
            "w09_join_outside_ok.wf",
            "w10_clause_scope_ok.wf",
            "w15_task_scope_ok.wf",
            "w17_closure_maker_ok.wf",
            "w20_loop_after_scope_ok.wf",
        ] {
            let (_, pending, codes) = check(name);
            assert!(codes.is_empty(), "{name}: {codes:?}");
            assert!(late(pending.as_deref()), "{name}: {pending:?}");
        }
    }
}

/// Stage R0k-c2: the re-entry of a clause frame after a `multi` operation of
/// a handler of a caller (D5) or of a local handler (C8).
mod r0kc2 {
    use weft_facts::{FnFacts, NodeId, VarId};

    /// The source of probe `name` of `tests/gate/probes/fixes/<dir>`.
    fn probe(dir: &str, name: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes")
            .join(dir)
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    }

    /// The scope of `src` (the fallback and the pending construct) and the
    /// facts of the component of function `f`.
    fn facts(src: &str, f: &str) -> (Option<String>, Option<String>, FnFacts) {
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::default());
        let s = a.ir_scope.clone().expect("a scope");
        let b = weft_sema::irbuild::build(&a);
        let comps = weft_sema::factgen::components(&a, &b).unwrap_or_else(|e| panic!("{e}"));
        let c = comps
            .into_iter()
            .find(|c| c.facts.name == f)
            .unwrap_or_else(|| panic!("no component `{f}`"));
        (s.fallback, s.pending.map(|p| p.reason), c.facts)
    }

    /// The nodes of `f` whose kind is `kind`.
    fn nodes(f: &FnFacts, kind: &str) -> Vec<NodeId> {
        f.nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.kind == kind)
            .map(|(i, _)| NodeId(u32::try_from(i).unwrap_or(u32::MAX)))
            .collect()
    }

    /// The variables of `f` named `name`.
    fn vars(f: &FnFacts, name: &str) -> Vec<VarId> {
        f.vars
            .iter()
            .enumerate()
            .filter(|(_, v)| v.name == name)
            .map(|(i, _)| VarId(u32::try_from(i).unwrap_or(u32::MAX)))
            .collect()
    }

    /// The `Copy` node of the `perform` of `choose` in the clause: the node
    /// with an edge to the `Ret` node of the perform.
    fn row_copy(f: &FnFacts) -> NodeId {
        let rets: Vec<NodeId> = nodes(f, "perform ret")
            .into_iter()
            .filter(|n| f.node(*n).label == "choose")
            .collect();
        nodes(f, "perform copy")
            .into_iter()
            .find(|c| f.cfg_edge.iter().any(|(a, b)| a == c && rets.contains(b)))
            .expect("a copy node of the row")
    }

    /// The seed of the clause after the row: the clause of `Pick` performs
    /// `choose` of `main`; the facts of `run` have an edge from each
    /// `Return` of `run` to the `Copy` node of the perform, then to its `Ret`
    /// node, and the node of the handled body that runs the clause (the call
    /// of `body`) gets a `Copy` node too. The program is in scope.
    #[test]
    fn a_row_of_a_clause_gets_a_reentry_edge_from_the_returns_of_the_function() {
        let (fallback, pending, f) = facts(&probe("r0kc2", "m3_run_local_after_handle.wf"), "run");
        assert_eq!((fallback, pending), (None, None));
        let c = row_copy(&f);
        let returns = nodes(&f, "return");
        assert!(
            f.cfg_edge
                .iter()
                .any(|(a, b)| *b == c && returns.contains(a)),
            "no edge from a `Return` to the copy"
        );
        let call_copy = nodes(&f, "call copy");
        assert!(
            call_copy.iter().any(|c| f
                .cfg_edge
                .iter()
                .any(|(a, b)| b == c && returns.contains(a))),
            "the call of `body` has no re-entry"
        );
    }

    /// E5: the `Copy` node of the row binds again the reference into a
    /// local of `run` (a place that the copied frames own: `m3`), and does
    /// not bind again the reference into a vector of `main` (a shared place:
    /// `fixes/r0kc2c/p25_op_arg_mutref_bad`; the reference into an `rc`
    /// object of `m7` is pending from stage R0k-c2 fix 1).
    #[test]
    fn the_copy_of_a_row_of_a_clause_binds_only_the_owned_references_again() {
        let (_, _, f) = facts(&probe("r0kc2", "m3_run_local_after_handle.wf"), "run");
        let c = row_copy(&f);
        let r = vars(&f, "r");
        assert!(
            r.iter().any(|v| f.rebound_at.contains(&(*v, c))),
            "the owned reference is not bound again"
        );
        let (fallback, pending, f) = facts(&probe("r0kc2c", "p25_op_arg_mutref_bad.wf"), "run");
        assert_eq!((fallback, pending), (None, None));
        let c = row_copy(&f);
        let r = vars(&f, "r");
        assert!(!r.is_empty());
        assert!(
            r.iter().all(|v| !f.rebound_at.contains(&(*v, c))),
            "the shared reference is bound again"
        );
    }

    /// E7: a linear value of the clause that is live across the row gets
    /// its copy at the `Copy` node with no `empty_at` (the copy is linear),
    /// and the row is a `multi` point: W0503. A value that ends before the
    /// row is not live there.
    #[test]
    fn a_linear_value_of_the_clause_across_the_row_is_not_emptied_by_the_copy() {
        let (fallback, pending, f) = facts(&probe("r0kc2b", "b06_once_across_bad.wf"), "run");
        assert_eq!(fallback, None);
        let _ = pending;
        let c = row_copy(&f);
        let l: Vec<VarId> = vars(&f, "l")
            .into_iter()
            .filter(|v| f.var(*v).linear)
            .collect();
        assert!(!l.is_empty());
        assert!(l.iter().any(|v| f.rebound_at.contains(&(*v, c))));
        assert!(l.iter().all(|v| !f.empty_at.contains(&(*v, c))));
        let rows: Vec<NodeId> = nodes(&f, "perform")
            .into_iter()
            .filter(|n| f.node(*n).label == "choose")
            .collect();
        assert!(rows.iter().any(|n| f.multi_at.contains(n)));
        let (fallback, pending, _) = facts(&probe("r0kc2b", "b06_once_across_ok.wf"), "run");
        assert_eq!((fallback, pending), (None, None));
    }

    /// The shadow variables of the variables `r` of `f` (stage R0k-c2 fix 1,
    /// `handlers::arg_shadow_name`).
    fn shadows(f: &FnFacts) -> Vec<VarId> {
        vars(f, &weft_sema::factgen::handlers::arg_shadow_name("r"))
    }

    /// The places that the variables `vs` of `f` point into (by display).
    fn points(f: &FnFacts, vs: &[VarId]) -> Vec<String> {
        let mut out: Vec<String> = f
            .points_into
            .iter()
            .filter(|(v, _)| vs.contains(v))
            .map(|(_, q)| f.place(*q).display.clone())
            .collect();
        out.sort();
        out.dedup();
        out
    }

    /// The nodes of `f` that change, free or lend a place that a variable of
    /// `vs` points into (the same root), by label.
    fn changed_at(f: &FnFacts, vs: &[VarId]) -> Vec<String> {
        let roots: Vec<_> = f
            .points_into
            .iter()
            .filter(|(v, _)| vs.contains(v))
            .map(|(_, q)| f.place(*q).root)
            .collect();
        let mut out: Vec<String> = f
            .mutates_at
            .iter()
            .chain(&f.releases_at)
            .chain(&f.lends_mut)
            .filter(|(_, q)| roots.contains(&f.place(*q).root))
            .map(|(n, _)| f.node(*n).label.clone())
            .collect();
        out.sort();
        out.dedup();
        out
    }

    /// True if a variable `r` of `f` gets a new value at a `perform` of
    /// operation `op`.
    fn r_bound_at_perform(f: &FnFacts, op: &str) -> bool {
        let r = vars(f, "r");
        let at: Vec<NodeId> = nodes(f, "perform")
            .into_iter()
            .filter(|n| f.node(*n).label == op)
            .collect();
        f.rebound_at
            .iter()
            .any(|(v, n)| r.contains(v) && at.contains(n))
    }

    /// Stage R0k-c2 fix 1 (D5): the parameter `r` of the clause of `Pick`
    /// points into the vector `v` of `main` (the argument, through the
    /// parameter of `run`), a place that the copies share. Its shadow
    /// variable points into the argument, the `clear` after the `perform`
    /// changes it, and it is used where `r` is used after the row. The
    /// `perform` does not bind `r` again. The program is in scope.
    #[test]
    fn a_clause_parameter_across_a_row_has_a_shadow_variable_for_its_argument() {
        let (fallback, pending, f) = facts(&probe("r0kc2c", "p25_op_arg_mutref_bad.wf"), "run");
        assert_eq!((fallback, pending), (None, None));
        let w = shadows(&f);
        assert_eq!(w.len(), 1);
        let ps = points(&f, &w);
        assert!(ps.iter().any(|q| q.starts_with('v')), "{ps:?}");
        assert!(changed_at(&f, &w).contains(&"clear".to_string()));
        assert!(f.uses.iter().any(|(v, _)| w.contains(v)));
        assert!(!r_bound_at_perform(&f, "pick"));
        let c = row_copy(&f);
        assert!(w.iter().all(|v| !f.rebound_at.iter().any(|(x, _)| x == v)));
        assert!(vars(&f, "r")
            .iter()
            .all(|v| !f.rebound_at.contains(&(*v, c))));
    }

    /// Stage R0k-c2 fix 1 (C8): the parameter `r` of the clause of `Ask`
    /// (inside the handled body of the local `multi` handler `Pick`) has a
    /// shadow variable into `v[]` of `main`; in the clean twin no node
    /// changes its places.
    #[test]
    fn a_clause_parameter_across_a_local_multi_operation_has_a_shadow_variable() {
        let (fallback, pending, f) =
            facts(&probe("r0kc2c", "p30_c8_op_arg_between_bad.wf"), "main");
        assert_eq!((fallback, pending), (None, None));
        let w = shadows(&f);
        assert!(points(&f, &w).iter().any(|q| q == "v[]"));
        assert!(!changed_at(&f, &w).is_empty());
        let (fallback, pending, f) = facts(&probe("r0kc2c", "p30_c8_op_arg_between_ok.wf"), "main");
        assert_eq!((fallback, pending), (None, None));
        let w = shadows(&f);
        assert!(points(&f, &w).iter().any(|q| q == "v[]"));
        assert!(changed_at(&f, &w).is_empty(), "{:?}", changed_at(&f, &w));
    }

    /// Stage R0k-c2 fix 1, the clean twin: the argument of `r` is a place of
    /// a local of `run`, which the copy copies (an owned place). So `r` gets
    /// no shadow variable.
    #[test]
    fn a_clause_parameter_into_a_copied_place_has_no_shadow_variable() {
        let (fallback, pending, f) = facts(&probe("r0kc2c", "p32_d5_op_arg_owned_ok.wf"), "run");
        assert_eq!((fallback, pending), (None, None));
        assert!(shadows(&f).is_empty());
        assert!(points(&f, &vars(&f, "r"))
            .iter()
            .all(|q| q.starts_with('r')));
    }

    /// Stage R0k-c2 fix 1, the second review: only a change that a node that
    /// runs the clause reaches counts. The `push` before the `handle`
    /// (`f11`) does not change the shadow places; the `clear` between two
    /// runs (`n05`) does, and the second run does not bind `r` again, so the
    /// change after the first run stays.
    #[test]
    fn only_a_change_after_a_run_of_the_clause_changes_the_shadow_places() {
        let (fallback, pending, f) = facts(&probe("r0kc2c", "f11_d5_loop_ok.wf"), "run");
        assert_eq!((fallback, pending), (None, None));
        let w = shadows(&f);
        assert!(!w.is_empty());
        assert!(changed_at(&f, &w).is_empty(), "{:?}", changed_at(&f, &w));
        let (fallback, pending, f) = facts(&probe("r0kc2c", "n05_two_runs_rebind_bad.wf"), "run");
        assert_eq!((fallback, pending), (None, None));
        let w = shadows(&f);
        assert!(changed_at(&f, &w).contains(&"clear".to_string()));
        assert!(!r_bound_at_perform(&f, "pick"));
    }

    /// The probe `name` of plan stage R0z Z2 (`fixes/r0z2`).
    fn z2(name: &str) -> String {
        probe("r0z2", name)
    }

    /// True if variable `v` of `f` points into an `rc` group.
    fn into_group(f: &FnFacts, v: VarId) -> bool {
        f.points_into.iter().any(|(w, q)| {
            *w == v && f.roots[f.place(*q).root.index()].kind == weft_facts::RootKind::Group
        })
    }

    /// True if variable `v` of `f` points into a shadow root of an `rc`
    /// group: a root of kind `Arg` with the name of a group (plan stage R0z
    /// Z2, fix 1).
    fn into_group_shadow(f: &FnFacts, v: VarId) -> bool {
        let groups: Vec<&str> = f
            .roots
            .iter()
            .filter(|r| r.kind == weft_facts::RootKind::Group)
            .map(|r| r.name.as_str())
            .collect();
        f.points_into.iter().any(|(w, q)| {
            let r = &f.roots[f.place(*q).root.index()];
            *w == v && r.kind == weft_facts::RootKind::Arg && groups.contains(&r.name.as_str())
        })
    }

    /// Plan stage R0z Z2 (the open-old entry `R0k2C-RC-BETWEEN` before the
    /// stage): a copied frame holds a reference into the `rc` object of
    /// `main` across the row `choose`, and the clause of `main` clears the
    /// object through another handle between two `resume`s. The programs
    /// are in scope (the pending rule `RC_ACROSS_ROW` goes): the variable
    /// "the copy of the frame" of the call of `run` in `main` points into
    /// the group of the object (a shadow root of the group, fix 1), which
    /// the frame of `run` holds a reference into across the row. So the
    /// change of the clause makes it invalid at the `Copy` node.
    #[test]
    fn the_copy_of_the_frame_of_a_call_points_into_the_rc_groups_that_it_reaches() {
        for src in [
            probe("r0kc2c", "p08_rc_between_param_bad.wf"),
            probe("r0kc2c", "n19_rc_param_arg_bad.wf"),
            probe("r0kc2c", "n18_rc_handled_frame_bad.wf"),
            z2("z01_root_between_bad.wf"),
            z2("z02_root_moved_bad.wf"),
        ] {
            let (fallback, pending, f) = facts(&src, "main");
            assert_eq!((fallback, pending), (None, None), "{src}");
            let copy: Vec<VarId> = f
                .vars
                .iter()
                .enumerate()
                .filter(|(_, v)| v.name.starts_with("copy of the frame that `run`"))
                .map(|(i, _)| VarId(u32::try_from(i).unwrap_or(u32::MAX)))
                .collect();
            assert!(copy.iter().any(|&v| into_group_shadow(&f, v)), "{src}");
        }
    }

    /// Plan stage R0z Z2: a reference through an `Rc` handle of a copied
    /// frame (`r = &b.v[0]` with `b: Rc<B>` a local of `run`) is valid in
    /// the copy: the `Copy` node of `choose` binds `r` again, and the shadow
    /// variable of its group part points into the group and keeps its state
    /// there.
    #[test]
    fn a_reference_through_a_copied_rc_handle_is_bound_again_with_a_shadow_of_its_group() {
        let (fallback, pending, f) = facts(&z2("z03_root_handle_ok.wf"), "run");
        assert_eq!((fallback, pending), (None, None));
        let copies: Vec<NodeId> = f
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.kind.ends_with(" copy") && n.label == "choose")
            .map(|(i, _)| NodeId(u32::try_from(i).unwrap_or(u32::MAX)))
            .collect();
        assert!(!copies.is_empty());
        let r = vars(&f, "r");
        assert!(r.iter().any(|v| f
            .rebound_at
            .iter()
            .any(|(w, n)| w == v && copies.contains(n))));
        let g = vars(&f, &weft_sema::factgen::handlers::rc_shadow_name("r"));
        assert_eq!(g.len(), 1, "{g:?}");
        assert!(into_group(&f, g[0]));
        assert!(!f
            .rebound_at
            .iter()
            .any(|(w, n)| *w == g[0] && copies.contains(n)));
        assert!(f.uses.iter().any(|(w, _)| *w == g[0]));
    }

    /// C8: a node of the clause of `Ask` (inside the handled body of the
    /// local `multi` handler `Pick`) that runs the clause of `Pick` gets a
    /// `Copy` node with an edge from `Post` of the `handle` of `Pick`. The
    /// program is in scope.
    #[test]
    fn a_node_of_a_clause_inside_a_multi_handled_body_gets_a_reentry_edge_from_post() {
        let (fallback, pending, f) = facts(&probe("r0kc2b", "b05_c8_pre_ok.wf"), "main");
        assert_eq!((fallback, pending), (None, None));
        let posts = nodes(&f, "handle post");
        let copies = nodes(&f, "perform copy");
        assert!(copies.iter().any(|c| {
            f.node(*c).label == "pick"
                && f.cfg_edge.iter().any(|(a, b)| b == c && posts.contains(a))
        }));
    }

    /// Plan stage R0z Z7: the clause of `Run` runs `g`, and `g` performs the
    /// `multi` operation `pick` of a handler of a caller of `f` (a row that
    /// only the analysis finds). The perform of `run` in the handled body
    /// runs the clause, so it gets a `Copy` node with an edge from each
    /// `Return` of `f`. The program is in scope.
    #[test]
    fn a_run_of_a_value_that_resumes_more_than_once_in_a_clause_gets_the_reentry() {
        for name in ["d1_value_multi_bad.wf", "d1_value_multi_ok.wf"] {
            let (fallback, pending, f) = facts(&probe("r0z7", name), "f");
            assert_eq!((fallback, pending), (None, None), "{name}");
            let returns = nodes(&f, "return");
            let copies: Vec<NodeId> = nodes(&f, "perform copy")
                .into_iter()
                .filter(|c| f.node(*c).label == "run")
                .collect();
            assert!(
                copies.iter().any(|c| f
                    .cfg_edge
                    .iter()
                    .any(|(a, b)| b == c && returns.contains(a))),
                "{name}: the perform of `run` has no re-entry"
            );
        }
    }

    /// Plan stage R0z Z7: a row after the `resume` of the clause (the run of
    /// `g` after `resume`): the `handle` gets a `Copy` node of copy `ROW`
    /// with an edge from each `Return` of `f`.
    #[test]
    fn a_run_of_a_value_after_the_resume_gives_the_handle_a_row_copy() {
        let (fallback, pending, f) = facts(&probe("r0z7", "d2_post_multi_ok.wf"), "f");
        assert_eq!((fallback, pending), (None, None));
        let returns = nodes(&f, "return");
        let copies = nodes(&f, "handle row copy");
        assert!(
            copies.iter().any(|c| f
                .cfg_edge
                .iter()
                .any(|(a, b)| b == c && returns.contains(a))),
            "the `handle` has no row copy"
        );
    }

    /// Plan stage R0z Z7: the clause runs its parameter `f`, and the value
    /// that the perform gives cannot resume more than once. The run of the
    /// function runs the clause with that value and finds no row, so the
    /// run of `f` in the clause is no row and no `multi` point: the program
    /// is in scope, and no node of `main` is a `multi` point.
    #[test]
    fn a_run_of_a_parameter_of_a_clause_that_does_not_resume_twice_is_no_row() {
        let (fallback, pending, f) = facts(&probe("r0z7", "p1_param_ok.wf"), "main");
        assert_eq!((fallback, pending), (None, None));
        assert!(f.multi_at.is_empty(), "{:?}", f.multi_at);
    }

    /// Plan stage R0z Z7, the reviews of Z7: a row that only the analysis
    /// finds stays pending when a clause on the way has a reference
    /// parameter and the function can wait at a `multi` operation of a
    /// handler of a caller by itself (`factgen::arg_shadow_gap`), or when
    /// the environment of the value that the node runs can hold references
    /// (`analysis::env_can_hold_refs`, round 3): the shadow variable of the
    /// parameter or the copy of the frame of the value would give a false
    /// W0301. The program keeps the fallback, as before the stage.
    #[test]
    fn a_dynamic_row_with_a_reference_parameter_and_a_row_of_the_function_stays_pending() {
        for name in [
            "z1_reentry_assign_ok.wf",
            "z3_value_noreentry_ok.wf",
            "g1_splice_closure_ok.wf",
            "g3_closure_outside_ok.wf",
            "c4_capture_outer_bad.wf",
            "t3_capture_v_push_after_ok.wf",
            "s5_capture_known_ok.wf",
        ] {
            let src = probe("r0z7", name);
            let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
            let file = weft_syntax::parse_file(&src).unwrap_or_else(|e| panic!("{}", e.message));
            let units = vec![
                prelude,
                weft_sema::Unit {
                    name: String::new(),
                    file,
                    is_std: false,
                },
            ];
            let a = weft_sema::analyze(&units, weft_sema::Options::default());
            let s = a.ir_scope.clone().expect("a scope");
            let why = s
                .fallback
                .or_else(|| s.pending.map(|p| p.reason))
                .unwrap_or_default();
            assert!(
                why.contains("a `multi` operation of a handler of a caller in a clause"),
                "{name}: {why}"
            );
        }
    }
}

/// Plan stage R0z Z9a (E2): a task that runs a value more than once. The
/// spawn has a second node of the run (`NodeTable::again_nodes`): the run
/// happens at `Main` and again at that node, and the task starts after it.
/// The codes of the checker (W0502 and W0301 at the spawn) are in the corpus
/// program `tests/programs/208_task_runs_again.wf` and in the probes of the
/// gate.
mod r0z9a {
    /// The analysis of the probe at `path` of `tests/gate/probes`.
    fn analysis(path: &str) -> weft_sema::Analysis {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes")
            .join(path);
        let src = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
        weft_sema::analyze_source(&src, weft_sema::Options::from_markers(&src))
            .unwrap_or_else(|d| panic!("{path}: {}", d.message))
    }

    /// The reason of the fallback and the reason of the pending construct of
    /// the probe at `path`.
    fn check(path: &str) -> (Option<String>, Option<String>) {
        let s = analysis(path).ir_scope.expect("a scope");
        (s.fallback, s.pending.map(|p| p.reason))
    }

    /// True if the pending reason is the task that runs a value again.
    fn again(p: Option<&str>) -> bool {
        p.is_some_and(|r| r.contains("a task that runs a callback more than once"))
    }

    /// The clean forms, and the rows of the census of R0z, have full facts
    /// (on main each one is pending with `TASK_AGAIN`), and the bad twins
    /// too: the checker rejects them (the gate).
    #[test]
    fn the_forms_have_full_facts() {
        let mut names: Vec<String> = [
            "r3/oracle/probes/s8_steal_fnparam.wf",
            "r3/oracle/probes/i9_kept_write.wf",
            "r3/oracle/probes/s9_steal_stored.wf",
        ]
        .iter()
        .map(ToString::to_string)
        .collect();
        for form in [
            "e01_loop_once",
            "e02_twice_once",
            "e04_ref_end",
            "e05_kept",
            "e06_stored",
            "e07_both_same",
            "e08_loop_spawn",
            "e10_clause",
            "e11_linear",
            "e12_join",
            "e13_param",
            "e14_write_twice",
            "e15_clause_outer",
            "e16_closure_outer",
            "e17_loop_join",
            "g01_param_twice_ref",
            "g02_param_loop_ref",
            "g03_method_param_ref",
            "g04_sim_param_ref",
            "g06_seq_tasks_ref",
            "h01_branch_task_or_direct",
            "h03_match_once_task",
        ] {
            for twin in ["ok", "bad"] {
                names.push(format!("fixes/r0z9a/{form}_{twin}.wf"));
            }
        }
        for name in &names {
            assert_eq!(check(name), (None, None), "{name}");
        }
    }

    /// The spawn of `main` has the second node of the run (kind `spawn
    /// task`), and the task starts there, not at `Main`.
    #[test]
    fn the_task_starts_at_the_second_node_of_the_run() {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0z9a/e02_twice_once_ok.wf");
        let src = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
        let opts = weft_sema::Options {
            facts: weft_sema::FactGen::Ir,
            ..weft_sema::Options::from_markers(&src)
        };
        // The `ir` view: the facts of the IR are the facts of the bodies.
        let a = weft_sema::analyze_source(&src, opts)
            .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
        assert!(a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
        let kind = |f: &weft_facts::FnFacts, n: weft_facts::NodeId| f.node(n).kind.clone();
        let mut starts = Vec::new();
        for b in &a.bodies {
            for &(_, n) in &b.facts.spawned_at {
                starts.push(kind(&b.facts, n));
            }
        }
        assert_eq!(starts, ["spawn task"]);
    }

    /// The facts of the `ir` view of the probe at `path` of `fixes/r0z9a`.
    fn ir_bodies(path: &str) -> Vec<weft_sema::BodyFacts> {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0z9a")
            .join(path);
        let src = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
        let opts = weft_sema::Options {
            facts: weft_sema::FactGen::Ir,
            ..weft_sema::Options::from_markers(&src)
        };
        let a = weft_sema::analyze_source(&src, opts)
            .unwrap_or_else(|d| panic!("the source does not parse: {}", d.message));
        assert!(a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope));
        a.bodies
    }

    /// Review round 1 (B1): a callee runs its parameter two times in one task
    /// (`Run::many`). The caller applies the run at the first task node and
    /// again at the second one, and the task of the call starts at the
    /// second task node, after both runs (with one run, at the first one).
    #[test]
    fn a_caller_applies_a_task_run_of_a_callee_two_times() {
        let bodies = ir_bodies("g01_param_twice_ref_ok.wf");
        let mut starts = 0;
        for b in &bodies {
            let f = &b.facts;
            for &(_, n) in &f.spawned_at {
                if f.node(n).kind != "call task" {
                    continue;
                }
                starts += 1;
                let after_task = f
                    .cfg_edge
                    .iter()
                    .any(|&(m, x)| x == n && f.node(m).kind == "call task");
                assert!(
                    after_task,
                    "the task of the call starts at its first task node"
                );
            }
        }
        assert_eq!(starts, 1);
    }

    /// Review round 2: a value that a body runs on each of two exclusive
    /// paths runs at most one time (`Run::seq`, `Applied::seq`). The task of
    /// the call of `mid` (`if c { spawn(|| f()) } else { f() }`) starts at its
    /// first task node, and the spawn of `h03_match_once_task_ok` (a `once`
    /// closure in each arm of a `match` in the task) has one node: the task
    /// starts at `Main`.
    #[test]
    fn a_run_on_each_of_two_exclusive_paths_is_one_run() {
        for b in &ir_bodies("h01_branch_task_or_direct_ok.wf") {
            let f = &b.facts;
            for &(_, n) in &f.spawned_at {
                if f.node(n).kind != "call task" {
                    continue;
                }
                let after_task = f
                    .cfg_edge
                    .iter()
                    .any(|&(m, x)| x == n && f.node(m).kind == "call task");
                assert!(
                    !after_task,
                    "the task of the call starts at its second task node"
                );
            }
        }
        let mut starts = Vec::new();
        for b in &ir_bodies("h03_match_once_task_ok.wf") {
            for &(_, n) in &b.facts.spawned_at {
                starts.push(b.facts.node(n).kind.clone());
            }
        }
        assert_eq!(starts, ["spawn"]);
    }

    /// Review round 3: the refusals R-CODE (code of a caller that gets a
    /// value of the body runs it again on the task: `g(f)`, also the census
    /// rows `j01_again_ok` and `c09_cc_during_ok`), R-ORDER (a value that runs
    /// one time beside a run again) and R-MULTI (a run again that only the
    /// re-entry of a `multi` operation makes) keep the rule of R0j.
    #[test]
    fn the_refusals_of_review_round_3_keep_the_rule_of_r0j() {
        for name in [
            "fixes/r0j/j01_again_ok.wf",
            "fixes/r0f/c09_cc_during_ok.wf",
            "fixes/r0z9a/e03_param_g_ok.wf",
            "fixes/r0z9a/g05_param_code_ref_ok.wf",
            "fixes/r0z9a/i01_code_ref_across_param_ok.wf",
            "fixes/r0z9a/i03_task_multi_after_ok.wf",
            "fixes/r0z9a/i04_once_beside_twice_ok.wf",
        ] {
            let (fallback, pending) = check(name);
            assert_eq!(fallback, None, "{name}");
            assert!(again(pending.as_deref()), "{name}: {pending:?}");
        }
    }

    /// Review round 3 (R-MULTI at a call): a run before a perform of a local
    /// `multi` operation is no run again (`Run::seq_loop`): the task of the
    /// call of `mid` starts at its first task node, as on main.
    #[test]
    fn a_run_before_a_multi_perform_is_one_task_run_at_the_caller() {
        for b in &ir_bodies("i02_multi_spawn_before_ok.wf") {
            let f = &b.facts;
            for &(_, n) in &f.spawned_at {
                if f.node(n).kind != "call task" {
                    continue;
                }
                let after_task = f
                    .cfg_edge
                    .iter()
                    .any(|&(m, x)| x == n && f.node(m).kind == "call task");
                assert!(
                    !after_task,
                    "the task of the call starts at its second task node"
                );
            }
        }
    }

    /// Review round 2 (R-REBIND): a loop in the task runs a `once` `f`, then
    /// gives `f` a new closure; the rule of R0j stays.
    #[test]
    fn a_once_value_that_the_task_gives_a_new_value_keeps_the_rule_of_r0j() {
        let (fallback, pending) = check("fixes/r0z9a/h04_reassign_loop_ok.wf");
        assert_eq!(fallback, None);
        assert!(again(pending.as_deref()), "{pending:?}");
    }

    /// Review round 1 (B2, R-ONCE): the task body reads a `once` element of a
    /// captured `Vec` and runs it again; the facts do not move the element,
    /// so the rule of R0j stays. The twin with a callback that is not `once`
    /// (`e06_stored_ok`) is in scope (`the_forms_have_full_facts`).
    #[test]
    fn a_once_element_that_the_task_runs_again_keeps_the_rule_of_r0j() {
        for name in ["g07_stored_once_bad.wf", "g08_stored_once_twice_bad.wf"] {
            let (fallback, pending) = check(&format!("fixes/r0z9a/{name}"));
            assert_eq!(fallback, None, "{name}");
            assert!(again(pending.as_deref()), "{name}: {pending:?}");
        }
    }

    /// The refusals keep the rule of R0j (pending, `TASK_AGAIN`): a branch of
    /// a `fork` (R-FORK: no second node) and a run that starts a task in a
    /// scope of the maker (R-INNER).
    #[test]
    fn the_refusals_keep_the_rule_of_r0j() {
        for name in ["r01_fork_ok.wf", "r02_inner_task_ok.wf"] {
            let (fallback, pending) = check(&format!("fixes/r0z9a/{name}"));
            assert_eq!(fallback, None, "{name}");
            assert!(again(pending.as_deref()), "{name}: {pending:?}");
        }
    }

    /// A closure body whose spawn runs a value again: the call of the
    /// closure runs the capture as a task at a late slot (plan stage R0z
    /// Z9c-B, part 1), so `e09_closure_body_ok` has full facts. The bad
    /// twin moves the `once` value into the closure (`ByMove`, R-VMOVE):
    /// it keeps the reason of Z9c, not `TASK_AGAIN`.
    #[test]
    fn a_spawn_in_a_closure_body_keeps_only_the_reason_of_z9c() {
        assert_eq!(
            check("fixes/r0z9a/e09_closure_body_ok.wf"),
            (None, None),
            "e09_closure_body_ok"
        );
        let (_, pending) = check("fixes/r0z9a/e09_closure_body_bad.wf");
        let p = pending.unwrap_or_default();
        assert!(p.contains("runs a value of its arguments as a task"), "{p}");
    }
}

/// Plan stage R0z Z9c-A (C1): the `with` of a task of a call slot keeps the
/// values of the interface that run while the task runs.
mod r0z9c {
    use weft_facts::{FnFacts, NodeId};

    /// The facts of `main` of the probe `name` of
    /// `tests/gate/probes/fixes/r0z9c`. The probe is in scope.
    fn main_facts(name: &str) -> FnFacts {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0z9c")
            .join(name);
        let src = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
        let opts = weft_sema::Options {
            facts: weft_sema::FactGen::Ir,
            ..weft_sema::Options::from_markers(&src)
        };
        let a = weft_sema::analyze_source(&src, opts)
            .unwrap_or_else(|d| panic!("{name}: the source does not parse: {}", d.message));
        assert!(
            a.ir_scope.as_ref().is_some_and(weft_sema::Scope::in_scope),
            "{name}: {:?}",
            a.ir_scope
        );
        a.bodies
            .into_iter()
            .find(|b| b.facts.name == "main")
            .map_or_else(|| panic!("{name}: no `main`"), |b| b.facts)
    }

    /// For the tasks of the call slots of `f`: the number of accesses at the
    /// node of the code that runs with a task (the node before the end of
    /// the task, if it does not start the task), and the number of tasks
    /// that start at two task nodes (`twice`).
    fn slot_with(f: &FnFacts) -> (usize, usize) {
        let task_node = |n: NodeId| f.node(n).kind == "call task";
        let mut at_x = 0;
        let mut twice = 0;
        for &(t, e) in &f.joined_at {
            if !task_node(e) {
                continue;
            }
            // The facts drop a task node with no facts: with no code that
            // runs with the task, the start (or the second start) of the
            // task is the node before its end.
            let starts_t = |n: NodeId| f.spawned_at.contains(&(t, n));
            for &(x, _) in f
                .cfg_edge
                .iter()
                .filter(|&&(x, b)| b == e && task_node(x) && !starts_t(x))
            {
                at_x += f.reads_at.iter().filter(|&&(n, _)| n == x).count();
                at_x += f.lends_mut.iter().filter(|&&(n, _)| n == x).count();
            }
            let starts = f
                .spawned_at
                .iter()
                .filter(|&&(u, n)| u == t && task_node(n))
                .count();
            if starts > 1 {
                twice += 1;
            }
        }
        (at_x, twice)
    }

    /// The bad probes: the callee of a function of `main` runs another value
    /// of the interface with a task of a call slot (a parameter as plain
    /// code, a second task), a clause of a local handler runs one in the
    /// window of a task of the body, or the same value runs again. The caller gets the places of that value at the node of the
    /// code that runs with the task, or a second start of the task. With C1
    /// off (main before Z9c-A) there are none, and the checker accepts the
    /// race.
    #[test]
    fn a_value_that_runs_with_a_slot_task_reaches_the_caller() {
        for name in [
            "a01_item_with_param_bad.wf",
            "a04_item_two_tasks_bad.wf",
            "a12_same_param_twice_bad.wf",
            "a13_task_with_self_plain_bad.wf",
            "a14_direct_clause_bad.wf",
            "a16_nested_twice_bad.wf",
            "a17_value_call_bad.wf",
        ] {
            let (at_x, twice) = slot_with(&main_facts(name));
            assert!(at_x > 0 || twice > 0, "{name}: {at_x} {twice}");
        }
    }

    /// The clean probes with runs on exclusive paths or in sequence: the
    /// summary has no `with`, so the caller gets no places at the node of the
    /// code that runs with the task and no second start.
    #[test]
    fn runs_on_exclusive_paths_or_in_sequence_add_nothing() {
        for name in [
            "b01_exclusive_ok.wf",
            "b02_sequence_ok.wf",
            "b03_two_tasks_sequence_ok.wf",
            "b04_clause_before_task_ok.wf",
            "b05_clause_after_task_ok.wf",
            "b08_exclusive_two_tasks_ok.wf",
            "a14_direct_clause_ok.wf",
        ] {
            assert_eq!(slot_with(&main_facts(name)), (0, 0), "{name}");
        }
    }

    /// Review round 1 of Z9c-A (B1): a clause of a local handler of the body
    /// that runs at a call while a task of a call slot can run adds nothing.
    /// The part `waits` of the callee names an effect, not the task or the
    /// operation, so a first form that gave each slot task the clause runs
    /// had false positives: the callee waits only while another task runs
    /// (`c01`), before the spawn (`c09`, `c24`), or while a task of its own
    /// runs (`c14`, `c27`). The forms `a10` and `a15` stay open (an old hole
    /// of main).
    #[test]
    fn a_clause_at_a_call_with_a_slot_task_adds_nothing() {
        for name in [
            "c01_waits_other_task_ok.wf",
            "c09_clause_before_spawn_param_ok.wf",
            "c14_waits_one_task_with_scope_ok.wf",
            "c24_waits_same_effect_before_ok.wf",
            "c27_waits_internal_task_realistic_ok.wf",
            "a10_item_clause_ok.wf",
        ] {
            assert_eq!(slot_with(&main_facts(name)), (0, 0), "{name}");
        }
    }

    /// Review round 2 of Z9c-A (B2): a clause of a local handler that runs a
    /// value of the interface at a call in the window of a task of the body
    /// adds no `with` row. The facts give a run at the call for each clause
    /// of the handler whose effect the callee can perform, not for the
    /// operation: in `c39` and `c43` the callee performs only another
    /// operation. A clause run at a perform in the window still counts
    /// (`a14_direct_clause_bad`).
    #[test]
    fn a_clause_at_a_call_node_adds_no_with_row() {
        for name in [
            "c39_other_op_via_callee_ok.wf",
            "c43_log_helper_realistic_ok.wf",
        ] {
            assert_eq!(slot_with(&main_facts(name)), (0, 0), "{name}");
        }
        let (at_x, _) = slot_with(&main_facts("a14_direct_clause_bad.wf"));
        assert!(at_x > 0);
    }

    /// Review round 3 of Z9c-A (B3): the code after the resume of a clause
    /// runs at the `Post` node of the `handle`. The facts give a `Post` run
    /// for each clause of the handler, so the run counts for the `with` of a
    /// task only if the handled body performs the operation of the clause:
    /// in the clean probes it does not (`d01`: only `note`, and the code
    /// after the resume of `ping` runs `k`; `d11`: nothing). (`d20` has
    /// accesses at its slot nodes from its two known tasks, as on main.) In
    /// the bad twin
    /// of `d01` the body performs `ping` in the window of the task, and the
    /// caller gets the places of `k`.
    #[test]
    fn a_post_run_counts_only_for_a_clause_that_the_body_performs() {
        for name in [
            "d01_post_other_op_ok.wf",
            "d03_log_post_realistic_ok.wf",
            "d11_post_same_value_ok.wf",
            "d16_post_loop_ok.wf",
            "d27_post_callee_other_op_ok.wf",
        ] {
            assert_eq!(slot_with(&main_facts(name)), (0, 0), "{name}");
        }
        let (at_x, _) = slot_with(&main_facts("d01_post_other_op_bad.wf"));
        assert!(at_x > 0);
    }

    /// `analysis::tasks::add_with`: a row of another value adds it to
    /// `with`, a row of the value itself sets `twice`, a row of the other
    /// kind or of another task adds nothing, and the old how stays.
    #[test]
    fn add_with_keeps_the_old_how_and_adds_the_rows() {
        use weft_facts::TaskId;
        use weft_sema::analysis::tasks::{add_with, RawHow};
        let t = TaskId(0);
        let runs = [(t, 0, false, false)];
        let mut hows = vec![RawHow {
            param: 0,
            thread: true,
            with: std::iter::once(3).collect(),
            ..RawHow::default()
        }];
        add_with(
            &mut hows,
            &runs,
            &[(t, 1, false), (t, 2, true), (TaskId(1), 4, false)],
        );
        let h = &hows[0];
        assert!(h.thread && !h.twice);
        assert_eq!(h.with.iter().copied().collect::<Vec<_>>(), [1, 3]);
        add_with(&mut hows, &runs, &[(t, 0, false)]);
        assert!(hows[0].twice);
    }
}

/// Plan stage R0z Z9c-B (S1 and part 1): the capture slots of a call. A
/// call of a closure that runs one of its captures as a task gets a late
/// slot: four task nodes of kind `call task late` before `Ret`, made after
/// the last run of the analysis. On main each form is pending with
/// `VALUE_TASKS`.
mod r0z9cb {
    use weft_facts::FnFacts;

    /// The analysis of the probe `path` of `tests/gate/probes`, with the
    /// facts of the `ir` pipeline.
    fn analysis(path: &str) -> weft_sema::Analysis {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes")
            .join(path);
        let src = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
        let opts = weft_sema::Options {
            facts: weft_sema::FactGen::Ir,
            ..weft_sema::Options::from_markers(&src)
        };
        weft_sema::analyze_source(&src, opts).unwrap_or_else(|d| panic!("{path}: {}", d.message))
    }

    /// The reason of the fallback and the reason of the pending construct.
    fn check(path: &str) -> (Option<String>, Option<String>) {
        let s = analysis(path).ir_scope.expect("a scope");
        (s.fallback, s.pending.map(|p| p.reason))
    }

    /// The facts of `main` of the probe `path`.
    fn main_facts(path: &str) -> FnFacts {
        analysis(path)
            .bodies
            .into_iter()
            .find(|b| b.facts.name == "main")
            .map_or_else(|| panic!("{path}: no `main`"), |b| b.facts)
    }

    /// The tasks that start at a node of a late slot.
    fn late_tasks(f: &FnFacts) -> Vec<weft_facts::TaskId> {
        let late = |n: weft_facts::NodeId| f.node(n).kind == weft_sema::factgen::nodes::LATE_KIND;
        let mut ts: Vec<_> = f
            .spawned_at
            .iter()
            .filter(|&&(_, n)| late(n))
            .map(|&(t, _)| t)
            .collect();
        ts.sort();
        ts.dedup();
        ts
    }

    /// The rows of the census (tier 1) and the clean probes have full facts,
    /// and so do the bad twins: the checker rejects them.
    #[test]
    fn the_capture_slots_have_full_facts() {
        let mut paths: Vec<String> = [
            "fixes/r0j/j04_value_ok.wf",
            "fixes/r0j/j04_value_bad.wf",
            "fixes/r0kd2/s3_nested_closure_ok.wf",
            "fixes/r0z9a/e09_closure_body_ok.wf",
        ]
        .iter()
        .map(ToString::to_string)
        .collect();
        for form in [
            "b01_cap_plain_known",
            "b03_cap_through_callee",
            "b07_cap_ref_across",
            "b08_cap_fork_rc",
            "b09_cap_fork_write",
        ] {
            for twin in ["ok", "bad"] {
                paths.push(format!("fixes/r0z9cb/{form}_{twin}.wf"));
            }
        }
        // The bad twins of `b11` and `b12` store a reference into a capture
        // (R-VSTORE, review round 4): only the clean twins have a slot.
        for form in [
            "b11_cap_known_task_then_plain",
            "b12_cap_known_plain_then_task",
        ] {
            paths.push(format!("fixes/r0z9cb/{form}_ok.wf"));
        }
        for path in &paths {
            assert_eq!(check(path), (None, None), "{path}");
        }
    }

    /// The task of a capture slot starts and ends at the late nodes, and it
    /// has the footprint of the capture: `j04_value_ok` reads `c.k` in two
    /// tasks at once (`twice`: two starts), once at each of the two calls.
    #[test]
    fn a_capture_slot_starts_and_ends_its_task_at_the_late_nodes() {
        let f = main_facts("fixes/r0j/j04_value_ok.wf");
        let ts = late_tasks(&f);
        assert_eq!(ts.len(), 2, "{ts:?}");
        let late = |n: weft_facts::NodeId| f.node(n).kind == weft_sema::factgen::nodes::LATE_KIND;
        for t in ts {
            let starts = f.spawned_at.iter().filter(|&&(u, _)| u == t).count();
            assert_eq!(starts, 2, "{t:?}: the second start of `twice`");
            assert!(
                f.joined_at.iter().any(|&(u, n)| u == t && late(n)),
                "{t:?}: no end at a late node"
            );
            let reads: Vec<String> = f
                .task_reads
                .iter()
                .filter(|(u, _)| *u == t)
                .map(|&(_, q)| f.place(q).display.clone())
                .collect();
            assert!(reads.iter().any(|r| r == "c.k"), "{t:?}: {reads:?}");
        }
    }

    /// A call with no capture task has no late node: the facts of the
    /// probes of Z9c-A do not change.
    #[test]
    fn a_call_with_no_capture_task_has_no_late_node() {
        for name in ["a01_item_with_param_bad.wf", "c01_waits_other_task_ok.wf"] {
            let f = main_facts(&format!("fixes/r0z9c/{name}"));
            assert!(
                !f.nodes
                    .iter()
                    .any(|n| n.kind == weft_sema::factgen::nodes::LATE_KIND),
                "{name}"
            );
        }
    }

    /// The refusals keep `VALUE_TASKS` (the rule of main): a `once` value
    /// that the closure moves into itself (`ByMove`, R-VMOVE), a closure that
    /// also runs a value of an argument (R-VARG), a clause of a local handler
    /// at the call (R-VCLAUSE), and a value of the interface that the closure
    /// runs as a task and then again as plain code (`b10`).
    #[test]
    fn the_refusals_keep_the_reason_of_main() {
        for path in [
            "fixes/r0z9cb/b02_cap_two_calls_once_ok.wf",
            "fixes/r0z9cb/b02_cap_two_calls_once_bad.wf",
            "fixes/r0z9cb/b04_cap_and_arg_ok.wf",
            "fixes/r0z9cb/b04_cap_and_arg_bad.wf",
            "fixes/r0z9cb/b05_cap_local_clause_ok.wf",
            "fixes/r0z9cb/b05_cap_local_clause_bad.wf",
            "fixes/r0z9cb/b10_cap_task_then_plain_ok.wf",
            "fixes/r0z9cb/b10_cap_task_then_plain_bad.wf",
            "fixes/r0z9a/e09_closure_body_bad.wf",
        ] {
            let (fallback, pending) = check(path);
            assert_eq!(fallback, None, "{path}");
            let p = pending.unwrap_or_default();
            assert!(
                p.contains("runs a value of its arguments as a task"),
                "{path}: {p}"
            );
        }
    }

    /// Review round 3 of Z9c-B (R-VIFACE, B5 and B6): a closure whose task
    /// runs a value of the interface of the body keeps `VALUE_TASKS`, also a
    /// known wrapper that runs one (`b24`), a getter of a type parameter
    /// (`b22`, `b23`, `b27`) and an `rc` handle (`b25`, `b26`). The review
    /// probes of Z9c-A and of round 1 with values of the interface (`a03`,
    /// `b13`) keep it too. With no refusal each bad twin was a HOLE, and the
    /// task cover failed on `b25` and `b26`.
    #[test]
    fn a_value_of_the_interface_gets_no_capture_slot() {
        for form in [
            "b22_cap_generic_getter_held",
            "b23_cap_generic_held_in_caller_of_closure",
            "b24_cap_generic_known_task_wrapper",
            "b25_cap_rc_iface_ref_held",
            "b26_cap_rc_iface_closure_ref",
            "b27_cap_generic_caller_task_race",
            "b13_cap_iface_ref_param",
        ] {
            for twin in ["ok", "bad"] {
                let path = format!("fixes/r0z9cb/{form}_{twin}.wf");
                let (fallback, pending) = check(&path);
                assert_eq!(fallback, None, "{path}");
                let p = pending.unwrap_or_default();
                assert!(
                    p.contains("runs a value of its arguments as a task"),
                    "{path}: {p}"
                );
            }
        }
    }

    /// Review round 4 of Z9c-B (R-VSTORE, B7): the closure stores a
    /// reference (or a function value) into a capture before its task
    /// starts. The facts apply the store at `Ret`, after the late slot nodes
    /// (issue #104), so each bad probe was a HOLE; the call keeps
    /// `VALUE_TASKS`.
    #[test]
    fn a_store_into_a_capture_that_can_hold_a_reference_keeps_the_fallback() {
        for path in [
            "fixes/r0z9cb/b28_cap_assign_captured_ref_bad.wf",
            "fixes/r0z9cb/b28_cap_assign_captured_ref_ok.wf",
            "fixes/r0z9cb/b29_cap_assign_option_ref_bad.wf",
            "fixes/r0z9cb/b29_cap_assign_option_ref_ok.wf",
            "fixes/r0z9cb/b30_cap_assign_tuple_ref_bad.wf",
            "fixes/r0z9cb/b30_cap_assign_tuple_ref_ok.wf",
            "fixes/r0z9cb/b31_cap_assign_ref_from_callee_bad.wf",
            "fixes/r0z9cb/b31_cap_assign_ref_from_callee_ok.wf",
            "fixes/r0z9cb/b32_cap_assign_ref_two_calls_bad.wf",
            "fixes/r0z9cb/b33_cap_store_in_maker_fn_bad.wf",
            "fixes/r0z9cb/b34_cap_store_reader_made_inside_bad.wf",
            "fixes/r0z9cb/b34_cap_store_reader_made_inside_ok.wf",
            "fixes/r0z9cb/b35_cap_store_reader_closure_param_body_bad.wf",
            "fixes/r0z9cb/b36_cap_method_store_ref_bad.wf",
        ] {
            let (fallback, pending) = check(path);
            assert_eq!(fallback, None, "{path}");
            let p = pending.unwrap_or_default();
            assert!(
                p.contains("runs a value of its arguments as a task"),
                "{path}: {p}"
            );
        }
    }

    /// `transfer::ref_free` is a whitelist: plain data, tuples, arrays,
    /// structs and enums of plain data, `Vec` and `String` of plain data, and
    /// function types of plain data are ref-free; a reference, a type
    /// parameter, an `rc` handle, a struct with a reference field, and a
    /// function type with a reference in its signature are not.
    #[test]
    fn ref_free_is_a_whitelist() {
        use weft_ir::ty::{AdtDecl, AdtKind, FieldDecl, FnTy, IntTy, Lang, Ty, TyTable};
        use weft_sema::analysis::transfer::ref_free;
        let mut t = TyTable::new();
        let unit = t.unit();
        let u64 = t.intern(Ty::Int(IntTy::U64));
        let r = t.intern(Ty::Ref(u64));
        let param = t.intern(Ty::Param(0));
        let decl = |name: &str, kind, lang, generics| AdtDecl {
            name: name.to_string(),
            generics,
            kind,
            lang,
            linear: false,
            on_abort: None,
            has_on_abort: false,
            immovable: false,
            copy: false,
            nonportable: false,
            props: Default::default(),
        };
        let field = |ty| FieldDecl {
            name: "f".to_string(),
            ty,
            place: false,
        };
        let plain = t.push_adt(decl("P", AdtKind::Struct(vec![field(u64)]), None, 0));
        let plain = t.intern(Ty::Adt(plain, vec![]));
        let with_ref = t.push_adt(decl("R", AdtKind::Struct(vec![field(r)]), None, 0));
        let with_ref = t.intern(Ty::Adt(with_ref, vec![]));
        let holder = t.push_adt(decl("H", AdtKind::Struct(vec![field(param)]), None, 1));
        let holds_u64 = t.intern(Ty::Adt(holder, vec![u64]));
        let holds_ref = t.intern(Ty::Adt(holder, vec![r]));
        let ext = AdtKind::Extern {
            elem_unstable: None,
            deref: None,
        };
        let vec = t.push_adt(decl("Vec", ext.clone(), Some(Lang::Vec), 1));
        let vec_u64 = t.intern(Ty::Adt(vec, vec![u64]));
        let rc = t.push_adt(decl("Rc", ext, Some(Lang::Rc), 1));
        let rc_plain = t.intern(Ty::Adt(rc, vec![plain]));
        let tuple = t.intern(Ty::Tuple(vec![u64, plain]));
        let fn_ty = |t: &mut TyTable, params: Vec<_>, ret| {
            t.intern(Ty::Fn(FnTy {
                params,
                ret,
                row: None,
            }))
        };
        let f_plain = fn_ty(&mut t, vec![u64], unit);
        let f_ref = fn_ty(&mut t, vec![], r);
        let f_param = fn_ty(&mut t, vec![], param);
        for (ty, want, what) in [
            (unit, true, "()"),
            (u64, true, "u64"),
            (plain, true, "struct of u64"),
            (holds_u64, true, "H<u64>"),
            (vec_u64, true, "Vec<u64>"),
            (tuple, true, "(u64, P)"),
            (f_plain, true, "fn(u64)"),
            (r, false, "&u64"),
            (param, false, "a type parameter"),
            (with_ref, false, "struct with a reference"),
            (holds_ref, false, "H<&u64>"),
            (rc_plain, false, "Rc<P>"),
            (f_ref, false, "fn() -> &u64"),
            (f_param, false, "fn() -> T"),
        ] {
            assert_eq!(ref_free(&t, ty), want, "{what}");
        }
    }

    /// Review round 2 of Z9c-B (R-VREF, B3 and B4): an argument of the call
    /// that can hold a reference (`b16`, `b18`, `b19`, `b21`), and a
    /// parameter of the body of a type parameter (`b17`, `b20`) keep
    /// `VALUE_TASKS`. With no refusal, each bad twin lost W0312 (HOLE).
    #[test]
    fn the_refusals_of_review_round_2_keep_the_reason_of_main() {
        for form in [
            "b16_cap_closure_ref_arg_known",
            "b17_cap_generic_ref_iface",
            "b18_cap_w0312_closure_two_args",
            "b19_cap_closure_option_ref_arg",
            "b20_cap_generic_plain_ref",
            "b21_cap_getter_closure_arg",
        ] {
            for twin in ["ok", "bad"] {
                let path = format!("fixes/r0z9cb/{form}_{twin}.wf");
                let (fallback, pending) = check(&path);
                assert_eq!(fallback, None, "{path}");
                let p = pending.unwrap_or_default();
                assert!(
                    p.contains("runs a value of its arguments as a task"),
                    "{path}: {p}"
                );
            }
        }
    }

    /// Review round 1 of Z9c-B: a task of a value of the interface while
    /// the body holds a reference parameter (R-VREF, B1: W0312 at the call of
    /// the body), and a local handler in the closure whose clause runs at a
    /// call of the closure body (R-VCLAUSE, B2) keep `VALUE_TASKS`. With no
    /// refusal, `b13_bad` and `b14_bad` lost W0312, and `b15_bad` was
    /// accepted (HOLE).
    #[test]
    fn the_refusals_of_review_round_1_keep_the_reason_of_main() {
        for path in [
            "fixes/r0z9cb/b13_cap_iface_ref_param_ok.wf",
            "fixes/r0z9cb/b13_cap_iface_ref_param_bad.wf",
            "fixes/r0z9cb/b14_cap_iface_ref_read_ok.wf",
            "fixes/r0z9cb/b14_cap_iface_ref_read_bad.wf",
            "fixes/r0z9cb/b15_cap_inner_handler_call_ok.wf",
            "fixes/r0z9cb/b15_cap_inner_handler_call_bad.wf",
        ] {
            let (fallback, pending) = check(path);
            assert_eq!(fallback, None, "{path}");
            let p = pending.unwrap_or_default();
            assert!(
                p.contains("runs a value of its arguments as a task"),
                "{path}: {p}"
            );
        }
    }
}

/// Plan stage R0z Z9c-C: the nested slots of a call (part 2, F18), and the
/// probes of review rounds 1 and 2 of the stage.
mod r0z9cc {
    use weft_facts::FnFacts;

    /// The source of the probe `path` of `tests/gate/probes`.
    fn source(path: &str) -> String {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes")
            .join(path);
        std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
    }

    /// The analysis of the probe `path`, with the facts of the `ir`
    /// pipeline.
    fn analysis(path: &str) -> weft_sema::Analysis {
        let src = source(path);
        let opts = weft_sema::Options {
            facts: weft_sema::FactGen::Ir,
            ..weft_sema::Options::from_markers(&src)
        };
        weft_sema::analyze_source(&src, opts).unwrap_or_else(|d| panic!("{path}: {}", d.message))
    }

    /// The reason of the fallback and the reason of the pending construct.
    fn check(path: &str) -> (Option<String>, Option<String>) {
        let s = analysis(path).ir_scope.expect("a scope");
        (s.fallback, s.pending.map(|p| p.reason))
    }

    /// The facts of the function `name` of the probe `path`.
    fn facts_of(path: &str, name: &str) -> FnFacts {
        analysis(path)
            .bodies
            .into_iter()
            .find(|b| b.facts.name == name)
            .map_or_else(|| panic!("{path}: no `{name}`"), |b| b.facts)
    }

    /// The inferred summary of the function `name` of the probe `path`.
    fn summary(path: &str, name: &str) -> weft_sema::analysis::Summary {
        let a = analysis(path);
        let b = weft_sema::irbuild::build(&a);
        let sums = weft_sema::factgen::summaries(&a, &b);
        let f = b
            .program
            .fns
            .iter()
            .position(|d| d.name == name)
            .unwrap_or_else(|| panic!("{path}: no function `{name}`"));
        sums.get(weft_ir::FnId(u32::try_from(f).unwrap_or(u32::MAX)))
            .cloned()
            .unwrap_or_else(|e| panic!("`{name}`: {e}"))
    }

    /// The rows of the census (tier 1: `a13_ok`, `j07_run_ok`) and the
    /// probes of the forms in scope have full facts. With the fix off (main),
    /// each one is pending (`NESTED_TASK_RUN`), or stops with `TASK_RUN` in
    /// `main`.
    #[test]
    fn the_nested_slots_have_full_facts() {
        let mut paths: Vec<String> = [
            "fixes/r0e/a13_ok.wf",
            "fixes/r0j/j07_run_ok.wf",
            "fixes/r0j/j07_run_bad.wf",
        ]
        .iter()
        .map(ToString::to_string)
        .collect();
        for form in [
            "c01_sim_ref_across",
            "c02_sim_caller_task",
            "c03_timeout_ref",
            "c04_detach",
            "c05_timeout_abort",
            "c06_join_in_block",
            "c07_once_two_calls",
        ] {
            for twin in ["ok", "bad"] {
                paths.push(format!("fixes/r0z9cc/{form}_{twin}.wf"));
            }
        }
        for path in &paths {
            assert_eq!(check(path), (None, None), "{path}");
        }
    }

    /// The nested slot of `sim.run` in `param_in_sim`: one task starts at a
    /// late node and ends at a late node, and it is opaque (code of a
    /// caller: the task runs a parameter).
    #[test]
    fn a_nested_slot_starts_and_ends_its_task_at_the_late_nodes() {
        let f = facts_of("fixes/r0e/a13_ok.wf", "param_in_sim");
        let late = |n: weft_facts::NodeId| {
            f.node(n)
                .kind
                .ends_with(weft_sema::factgen::nodes::LATE_KIND_SUFFIX)
        };
        let mut ts: Vec<_> = f
            .spawned_at
            .iter()
            .filter(|&&(_, n)| late(n))
            .map(|&(t, _)| t)
            .collect();
        ts.sort();
        ts.dedup();
        assert_eq!(ts.len(), 1, "{ts:?}");
        let t = ts[0];
        assert!(
            f.joined_at.iter().any(|&(u, n)| u == t && late(n)),
            "{t:?}: no end at a late node"
        );
        assert!(f.opaque.contains(&t), "{t:?}: not opaque");
    }

    /// The summary of `param_in_sim` runs its parameter as a task in the
    /// how of the window of the slot, not in the worst way (with the fix
    /// off, `TaskHow::foreign` and `thread`).
    #[test]
    fn the_summary_runs_the_parameter_in_the_how_of_the_slot() {
        let s = summary("fixes/r0j/j07_run_ok.wf", "param_in_sim");
        let run = s
            .runs
            .iter()
            .find(|r| r.param == 0 && !r.capture)
            .unwrap_or_else(|| panic!("no run of the parameter: {:?}", s.runs));
        assert!(run.task, "{run:?}");
        assert!(
            !run.how.foreign && !run.how.thread && !run.how.twice,
            "{run:?}"
        );
    }

    /// The reasons of the program `path` (`check --reasons`).
    fn reasons(path: &str) -> Vec<String> {
        let src = source(path);
        let opts = weft_sema::Options {
            facts: weft_sema::FactGen::Old,
            ..weft_sema::Options::from_markers(&src)
        };
        let a = weft_sema::analyze_source(&src, opts)
            .unwrap_or_else(|d| panic!("{path}: {}", d.message));
        weft_sema::factgen::reasons(&a, opts.ir_groups, opts.no_runtime)
    }

    /// Review round 1 of Z9c-C. H1 and H2: a run of a parameter in a value
    /// that code of a caller runs keeps `NESTED_TASK_RUN` (part 4 is out: the
    /// form of c10 lost a race of the code itself, H1, and fix (b) skipped
    /// the W0502 of rule E, H2). F1 (R-NONE): a `once` parameter at nested
    /// slots on exclusive paths keeps it too (a slot gave a false W0502).
    /// Each probe fails with the fix off (in scope with no reason).
    #[test]
    fn the_probes_of_review_round_1_keep_the_reason_of_main() {
        let mut paths = vec![
            "verify/review_core/Core_S2/probes/crash/c10.wf".to_string(),
            "fixes/r0z9cc/c08_rec_ref_bad.wf".to_string(),
            "fixes/r0z9cc/c08_rec_ref_ok.wf".to_string(),
            "fixes/r0z9cc/c09_code_spawns_ok.wf".to_string(),
        ];
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0z9cc");
        let mut names: Vec<String> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
            .filter_map(Result::ok)
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .filter(|n| n.starts_with("h1_") || n.starts_with("h2_") || n.starts_with("f1_"))
            .collect();
        names.sort();
        assert_eq!(names.len(), 25, "{names:?}");
        paths.extend(names.into_iter().map(|n| format!("fixes/r0z9cc/{n}")));
        for path in &paths {
            let list = reasons(path);
            assert!(
                list.iter().any(|r| r.contains("with no nested slot")),
                "{path}: {list:?}"
            );
        }
    }

    /// Review round 2 of Z9c-C. B1 (R-NREF of the locals of the body and of
    /// the callee): an `rc` handle or a reference from the result of an
    /// operation (a lost race, a failure of the task cover, a false W0301).
    /// B2 and B3 (R-NONE by value flow): an alias of a `once` parameter that
    /// the body gives back (a lost W0502) or runs on an exclusive path (a
    /// false W0502). Each probe keeps `NESTED_TASK_RUN`; each one fails with
    /// the fix off (the build of review round 1 has a slot for it).
    #[test]
    fn the_probes_of_review_round_2_keep_the_reason_of_main() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes/fixes/r0z9cc");
        let mut names: Vec<String> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
            .filter_map(Result::ok)
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .filter(|n| {
                (n.starts_with("b1_") || n.starts_with("b2_") || n.starts_with("b3_"))
                    && !n.contains("_noalias_")
            })
            .collect();
        names.sort();
        assert_eq!(names.len(), 29, "{names:?}");
        for n in &names {
            let path = format!("fixes/r0z9cc/{n}");
            let list = reasons(&path);
            assert!(
                list.iter().any(|r| r.contains("with no nested slot")),
                "{path}: {list:?}"
            );
        }
    }

    /// The refusals keep `NESTED_TASK_RUN` (the rule of main): R-NREF (a
    /// reference parameter, a type parameter, a getter, an `rc` handle),
    /// R-NBUSY (a plain run of another value with the task, a perform of the
    /// block), R-NMULTI (two tasks), R-NCLAUSE (a clause of a local handler),
    /// R-NITEM (a closure body, a result of a parameter), R-AGAIN (two values
    /// of F, two spawns), and code of a caller that runs the value while it
    /// changes a place (`busy`, B1 of the review of R0f). The direct forms of
    /// R-NREF are holes of main (`weft-work/z9cc/p/d02` to `d05`).
    #[test]
    fn the_refusals_keep_the_reason_of_main() {
        let mut paths = vec![
            "fixes/r0z9cc/c09_code_spawns_bad.wf".to_string(),
            "fixes/r0z9cc/b2_r12n_noalias_returned_once_bad.wf".to_string(),
        ];
        for form in [
            "n01_ref_param",
            "n02_generic",
            "n03_getter",
            "n04_rc",
            "n05_with_plain",
            "n06_two_tasks",
            "n07_local_clause",
            "n08_caller_clause",
            "n09_closure_body",
            "n10_result",
            "n11_two_params",
            "n12_twice",
        ] {
            for twin in ["ok", "bad"] {
                paths.push(format!("fixes/r0z9cc/{form}_{twin}.wf"));
            }
        }
        for path in &paths {
            let list = reasons(path);
            assert!(
                list.iter().any(|r| r.contains("with no nested slot")),
                "{path}: {list:?}"
            );
        }
    }
}

/// Plan stage R0z Z9d (part 3 of the design of Z9c): the nested slot of a
/// value that the run node knows (a closure, an item), and of a value that
/// the callee gives to the closure (`FnVal::Unknown`). The probes are in
/// `tests/gate/probes/fixes/r0z9d`: `p*` are in scope, `n*` are refusals.
mod r0z9d {
    use weft_facts::FnFacts;

    /// The source of the probe `path` of `tests/gate/probes`.
    fn source(path: &str) -> String {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes")
            .join(path);
        std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
    }

    /// The analysis of the probe `path`, with the facts of the `ir`
    /// pipeline.
    fn analysis(path: &str) -> weft_sema::Analysis {
        let src = source(path);
        let opts = weft_sema::Options {
            facts: weft_sema::FactGen::Ir,
            ..weft_sema::Options::from_markers(&src)
        };
        weft_sema::analyze_source(&src, opts).unwrap_or_else(|d| panic!("{path}: {}", d.message))
    }

    /// The reason of the fallback and the reason of the pending construct.
    fn check(path: &str) -> (Option<String>, Option<String>) {
        let s = analysis(path).ir_scope.expect("a scope");
        (s.fallback, s.pending.map(|p| p.reason))
    }

    /// The facts of the function `name` of the probe `path`.
    fn facts_of(path: &str, name: &str) -> FnFacts {
        analysis(path)
            .bodies
            .into_iter()
            .find(|b| b.facts.name == name)
            .map_or_else(|| panic!("{path}: no `{name}`"), |b| b.facts)
    }

    /// The four late slot nodes of the facts `f` (one slot), in their order:
    /// the start, the second start, the node of the code that runs with the
    /// task, the end.
    fn late_nodes(f: &FnFacts) -> Vec<weft_facts::NodeId> {
        let mut out: Vec<weft_facts::NodeId> = (0..f.nodes.len())
            .map(|i| weft_facts::NodeId(u32::try_from(i).unwrap_or(u32::MAX)))
            .filter(|&n| {
                f.node(n)
                    .kind
                    .ends_with(weft_sema::factgen::nodes::LATE_KIND_SUFFIX)
            })
            .collect();
        out.sort();
        out
    }

    /// The text of each place that the facts `f` lend at node `n`.
    fn lent_at(f: &FnFacts, n: weft_facts::NodeId) -> Vec<String> {
        f.lends_mut
            .iter()
            .filter(|&&(m, _)| m == n)
            .map(|&(_, q)| f.place(q).display.clone())
            .collect()
    }

    /// The reasons of the program `path` (`check --reasons`).
    fn reasons(path: &str) -> Vec<String> {
        let src = source(path);
        let opts = weft_sema::Options {
            facts: weft_sema::FactGen::Old,
            ..weft_sema::Options::from_markers(&src)
        };
        let a = weft_sema::analyze_source(&src, opts)
            .unwrap_or_else(|d| panic!("{path}: {}", d.message));
        weft_sema::factgen::reasons(&a, opts.ir_groups, opts.no_runtime)
    }

    /// Row 99 of tier 1 of the census (`j03_nested_ok`, a value of the
    /// callee) and the probes of the forms in scope have full facts. With the
    /// fix off (main), each one is pending (`NESTED_TASK_RUN`).
    #[test]
    fn the_nested_slots_of_part_3_have_full_facts() {
        let mut paths = vec![
            "fixes/r0j/j03_nested_ok.wf".to_string(),
            "fixes/r0j/j03_nested_bad.wf".to_string(),
            "fixes/r0z9d/p03_unknown_scalar_ok.wf".to_string(),
            "fixes/r0z9d/p08_item_value_ok.wf".to_string(),
            "fixes/r0z9d/p09_timeout_field_ok.wf".to_string(),
        ];
        for form in [
            "p01_unknown_busy",
            "p02_unknown_fields",
            "p04_field_writer",
            "p05_field_reader",
            "p06_sim_field",
            "p07_item_slot_in_g",
        ] {
            for twin in ["ok", "bad"] {
                paths.push(format!("fixes/r0z9d/{form}_{twin}.wf"));
            }
        }
        for path in &paths {
            assert_eq!(check(path), (None, None), "{path}");
        }
    }

    /// The slot of a value that the run node knows has the footprint of the
    /// value: its task starts at the first late node of `main` and writes
    /// `c.k` there, and it ends at the last late node. With the fix off, the
    /// node has no late nodes.
    #[test]
    fn a_known_value_gives_its_footprint_to_the_slot() {
        let f = facts_of("fixes/r0z9d/p04_field_writer_ok.wf", "main");
        let late = late_nodes(&f);
        assert_eq!(late.len(), 4, "{late:?}");
        let (s, e) = (late[0], late[3]);
        let ts: Vec<_> = f
            .spawned_at
            .iter()
            .filter(|&&(_, n)| n == s)
            .map(|&(t, _)| t)
            .collect();
        let [t] = ts[..] else {
            panic!("one task at the start node: {ts:?}");
        };
        assert!(f.joined_at.contains(&(t, e)), "{t:?}: no end at {e:?}");
        let writes: Vec<String> = f
            .task_writes
            .iter()
            .filter(|&&(u, _)| u == t)
            .map(|&(_, q)| f.place(q).display.clone())
            .collect();
        assert!(writes.iter().any(|w| w == "c.k"), "{writes:?}");
    }

    /// One view of the code of the closure (question Q6 of the design review
    /// of Z9c): for a value that the run node knows, the closure body checks
    /// its code with the task (the spawn there has the footprint), so the
    /// node of that code in the slot lends no place, and the conflict gives
    /// one W0405, not two. A value of the callee has no footprint in the
    /// closure body, so its slot has the code of the closure (`c.k` of
    /// `j03_nested_ok`). With the fix off, the nodes are not there; with the
    /// code of the closure in the slot of a known value, `p04` lends `c.k`
    /// at the node too.
    #[test]
    fn the_slot_of_a_known_value_leaves_the_code_of_the_closure_to_the_closure_body() {
        let f = facts_of("fixes/r0z9d/p04_field_writer_bad.wf", "main");
        let late = late_nodes(&f);
        assert_eq!(late.len(), 4, "{late:?}");
        assert_eq!(lent_at(&f, late[2]), Vec::<String>::new());
        let f = facts_of("fixes/r0j/j03_nested_ok.wf", "main");
        let late = late_nodes(&f);
        assert_eq!(late.len(), 4, "{late:?}");
        let lent = lent_at(&f, late[2]);
        assert!(lent.iter().any(|w| w == "c.k"), "{lent:?}");
    }

    /// The refusals of part 3 keep `NESTED_TASK_RUN` (the rule of main):
    /// R-NKNOWN (the value runs another closure, or gives a scalar of main a
    /// new value), R-NITEM (a node in a scope body of `main`, a value of the
    /// interface of the body), R-AGAIN (two spawns, a callee that runs the
    /// closure two times, a value of the callee spawned two times), R-NREF of
    /// the locals (the reference temporary of a method call: the rows 28, 29
    /// and 31 of tier 2 of the census), R-OUTER-TASK (a callee that runs
    /// another value as a task while it runs the closure), R-NMULTI (a `once`
    /// value that the value of the closure holds: the callee can run it
    /// too), and R-NONE (a closure that a callee made: its local gets the
    /// result of the call).
    #[test]
    fn the_refusals_of_part_3_keep_the_reason_of_main() {
        let mut paths = vec![
            "fixes/r0z9d/n12_once_one_ok.wf".to_string(),
            "fixes/r0z9d/n12_once_twice_bad.wf".to_string(),
            "fixes/r0z9d/n13_made_ok.wf".to_string(),
            "fixes/r0z9d/n14_unknown_twice_bad.wf".to_string(),
            "fixes/r0z9d/n15_timeout_linear_bad.wf".to_string(),
        ];
        for form in [
            "n01_runs_other",
            "n02_rebind",
            "n04_scope_body",
            "n05_twice",
            "n06_callee_twice",
            "n07_method_ref",
            "n08_apply_cap",
            "n09_writer_main_task",
            "n10_callee_task",
            "n11_iface_value",
        ] {
            for twin in ["ok", "bad"] {
                paths.push(format!("fixes/r0z9d/{form}_{twin}.wf"));
            }
        }
        for path in &paths {
            let list = reasons(path);
            assert!(
                list.iter().any(|r| r.contains("with no nested slot")),
                "{path}: {list:?}"
            );
        }
    }
}

/// Plan stage R0z Z10: a chain of function values deeper than 64. The memo
/// of the walk of a run node (`transfer::Apps::reach`) gives the result of
/// each level one time, so the depth bound of stage F12 (64) is only a
/// limit of the resources now (1024 levels, and 4096 values that one run
/// node of a deeper chain asks for).
mod r0z10 {
    use weft_facts::FnFacts;

    /// The source of the probe `path` of `tests/gate/probes`.
    fn source(path: &str) -> String {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes")
            .join(path);
        std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
    }

    /// The analysis of the probe `path`, with the facts of the `ir`
    /// pipeline.
    fn analysis(path: &str) -> weft_sema::Analysis {
        let src = source(path);
        let opts = weft_sema::Options {
            facts: weft_sema::FactGen::Ir,
            ..weft_sema::Options::from_markers(&src)
        };
        weft_sema::analyze_source(&src, opts).unwrap_or_else(|d| panic!("{path}: {}", d.message))
    }

    /// The reason of the fallback and the reason of the pending construct.
    fn check(path: &str) -> (Option<String>, Option<String>) {
        let s = analysis(path).ir_scope.expect("a scope");
        (s.fallback, s.pending.map(|p| p.reason))
    }

    /// The facts of the function `name` of the probe `path`, with the facts
    /// of the `ir` pipeline (the program is in scope).
    fn facts_of(path: &str, name: &str) -> FnFacts {
        let a = analysis(path);
        let fallback = a.ir_scope.as_ref().and_then(|s| s.fallback.clone());
        assert_eq!(fallback, None, "{path}");
        a.bodies
            .into_iter()
            .find(|b| b.facts.name == name)
            .map_or_else(|| panic!("{path}: no `{name}`"), |b| b.facts)
    }

    /// The chain probes of `fixes/r0z10` with a run of a chain of 100
    /// levels (a write at the bottom, a task at the top, a value with two
    /// arguments, a level in a field, a clause, a callee, the form of the
    /// census rows, a `once` level at the top), and two of 200 levels, have
    /// full facts. With the fix off (the bound 64), each one keeps the
    /// fallback.
    #[test]
    fn a_chain_deeper_than_64_has_full_facts() {
        let mut paths = vec![
            "fixes/r0z10/a_ref_top_200_bad.wf".to_string(),
            "fixes/r0z10/k_fn_form_200_ok.wf".to_string(),
        ];
        for form in [
            "a_ref_top",
            "b_task_top",
            "d_shared_args",
            "e_field",
            "h_clause",
            "i_callee",
            "k_fn_form",
            "l_once_top",
        ] {
            for twin in ["ok", "bad"] {
                paths.push(format!("fixes/r0z10/{form}_100_{twin}.wf"));
            }
        }
        for path in &paths {
            assert_eq!(check(path), (None, None), "{path}");
        }
    }

    /// The places that the facts of `main` of the probe `path` change at
    /// the node of the line `line` (the run of the top of the chain).
    fn changed_at(path: &str, line: &str) -> Vec<String> {
        let src = source(path);
        let lo = src
            .find(line)
            .unwrap_or_else(|| panic!("{path}: no `{line}`"));
        let hi = lo + line.len();
        let f = facts_of(path, "main");
        let mut out: Vec<String> = f
            .mutates_at
            .iter()
            .filter(|&&(n, _)| {
                let s = f.node(n).span;
                (lo..hi).contains(&(s.lo as usize))
            })
            .map(|&(_, q)| f.place(q).display.clone())
            .collect();
        out.sort();
        out.dedup();
        out
    }

    /// The write at the bottom of a chain of 200 closures (`w.v.push(1)`)
    /// is a change of `w.v` at the run node of the top in `main`, and a
    /// value that a level runs two times with two arguments changes the
    /// place of each argument (`w.a` and `w.b`), not only the place of the
    /// first one: the memo is of the walk of each value with its places.
    #[test]
    fn the_write_at_the_bottom_is_a_change_at_the_top() {
        let ps = changed_at("fixes/r0z10/a_ref_top_200_bad.wf", "\n    c199()\n");
        assert!(ps.iter().any(|p| p == "w.v"), "{ps:?}");
        let ps = changed_at("fixes/r0z10/d_shared_args_200_bad.wf", "\n    c199()\n");
        assert!(ps.iter().any(|p| p == "w.a"), "{ps:?}");
        assert!(ps.iter().any(|p| p == "w.b"), "{ps:?}");
        assert!(!ps.iter().any(|p| p == "w.c"), "{ps:?}");
    }

    /// A chain of closures that hold each other in their values (`once`
    /// closures capture the level below by a move) asks for each deeper
    /// value at each level: a run node of a chain deeper than 64 that asks
    /// for more than 4096 values keeps the old pipeline (the limit of the
    /// resources). A level that spawns the rest of the chain keeps the
    /// reason of main (`NESTED_TASK_RUN`).
    #[test]
    fn the_limits_of_the_resources_keep_the_old_pipeline() {
        for path in [
            "fixes/r0z10/f_once_100_bad.wf",
            "fixes/r0z10/f_once_200_ok.wf",
            "fixes/r0z10/g_once_mid_200_bad.wf",
        ] {
            let (fallback, _) = check(path);
            let text = fallback.unwrap_or_default();
            assert!(text.contains("more than 4096 values"), "{path}: {text}");
        }
        // The task of the level is a pending construct: the `ir` pipeline
        // checks the program only if it rejects it (the rule of stage R0g).
        let (fallback, pending) = check("fixes/r0z10/c_task_mid_200_ok.wf");
        assert_eq!(fallback, None);
        let text = pending.unwrap_or_default();
        assert!(text.contains("as a task"), "{text}");
    }
}

/// The runtime runs of `sim.run` and `with_timeout` (plan stage R0z Z4b,
/// `docs/ir.md` 6.1, "As built (plan stage R0z Z4b)"): a call whose block
/// resumes the continuation of the clause is a runtime resume node.
mod r0z4b {
    use weft_facts::FnFacts;
    use weft_ir::verify::{verify_program, Rule};
    use weft_sema::factgen::instantiate::{instantiate_kont, Instantiated};

    /// The source of the probe `path` of `tests/gate/probes`.
    fn source(path: &str) -> String {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/gate/probes")
            .join(path);
        std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
    }

    /// The analysis of `src` and its IR.
    fn built(src: &str) -> (weft_sema::Analysis, weft_sema::irbuild::Built) {
        let prelude = weft_sema::prelude_unit().unwrap_or_else(|e| panic!("{}", e.message));
        let file = weft_syntax::parse_file(src).unwrap_or_else(|e| panic!("{}", e.message));
        let units = vec![
            prelude,
            weft_sema::Unit {
                name: String::new(),
                file,
                is_std: false,
            },
        ];
        let a = weft_sema::analyze(&units, weft_sema::Options::default());
        let b = weft_sema::irbuild::build(&a);
        (a, b)
    }

    /// The program of the kont mode of `src`, if it has a copy or a runtime
    /// resume node.
    fn kont(src: &str) -> Option<Instantiated> {
        let (_, b) = built(src);
        instantiate_kont(&b)
    }

    /// The runtime resume nodes of the kont mode of `src`.
    fn runs(src: &str) -> usize {
        kont(src).map_or(0, |i| i.built.program.resume_runs.len())
    }

    /// True if the old pipeline checks the program `src`: the scope of the
    /// `ir` pipeline has a fallback, or a pending construct with no view of
    /// the copies.
    fn falls_back(src: &str) -> bool {
        let (a, _) = built(src);
        a.ir_scope.as_ref().is_none_or(|s| {
            s.fallback.is_some() || s.pending.as_ref().is_some_and(|p| p.copy.is_none())
        })
    }

    /// The rows 88 and 89 of the census and the forms of the probes (a
    /// reference of the clause across the block, the value of the block, a
    /// second activation, a change in the rest, the code of the clause
    /// after the block) get a runtime resume node. The program verifies (V22)
    /// and the `ir` pipeline checks it. With the fix off, each one keeps the
    /// fallback.
    #[test]
    fn the_rows_of_the_census_get_a_runtime_resume_node() {
        let r2c = "verify/s5/R2c: effects, continuations, on abort and drops/p";
        let mut paths = vec![
            format!("{r2c}/rr3_v19_sim_run_closure.wf"),
            format!("{r2c}/rr3_v20_with_timeout.wf"),
        ];
        for n in [
            "t01_ref_rest_frees",
            "s01_ref_rest_frees",
            "r01_again",
            "m01_move_rest",
            "n01_nested_sim_rest",
            "v01_value",
            "p01_post_part",
            "t04_cut_linear",
            "n03_two_runtime",
            "x01_rest_value",
            "x02_rest_push",
        ] {
            for twin in ["ok", "bad"] {
                paths.push(format!("fixes/r0z4b/{n}_{twin}.wf"));
            }
        }
        for path in &paths {
            let src = source(path);
            let inst = kont(&src).unwrap_or_else(|| panic!("{path}: no kont mode"));
            let p = &inst.built.program;
            assert!(!p.resume_runs.is_empty(), "{path}: no runtime resume node");
            assert!(
                verify_program(p, &inst.built.tys)
                    .iter()
                    .all(|x| x.rule != Rule::BadResumeRun),
                "{path}: {:?}",
                verify_program(p, &inst.built.tys)
            );
            if path.ends_with("_ok.wf") || path.starts_with("verify") {
                assert!(!falls_back(&src), "{path}: a fallback");
            }
        }
        // An `on abort` function that does not wait keeps the node
        // (R-RT-UNWIND is by the effects of the code).
        let src = source("fixes/r0z4b/u01c_onabort_nosleep_ok.wf");
        assert!(runs(&src) > 0, "u01c: no runtime resume node");
        assert!(!falls_back(&src), "u01c: a fallback");
    }

    /// The code of the clause after the node starts from the state at the end
    /// of the handled body (`clause::rest_exit`): the rest gives the site local
    /// `f` a closure that pushes to `w`, so the run of `f` after the block
    /// changes `w` in the facts of `main`.
    #[test]
    fn the_code_after_the_node_sees_the_values_of_the_rest() {
        let f = facts_of("fixes/r0z4b/x01_rest_value_bad.wf");
        let changes = f
            .mutates_at
            .iter()
            .any(|&(n, q)| f.node(n).label == "f" && f.place(q).display.starts_with('w'));
        assert!(changes, "the run of `f` changes no place of `w`");
    }

    /// The facts of `main` of the probe `path` in the program of the kont
    /// mode (`Pending::copy`: the facts of the `ir` pipeline that check the
    /// program).
    fn facts_of(path: &str) -> FnFacts {
        let src = source(path);
        let opts = weft_sema::Options {
            facts: weft_sema::FactGen::Ir,
            ..weft_sema::Options::from_markers(&src)
        };
        let a = weft_sema::analyze_source(&src, opts)
            .unwrap_or_else(|d| panic!("{path}: {}", d.message));
        let copy = a
            .ir_scope
            .and_then(|s| s.pending)
            .and_then(|p| p.copy)
            .unwrap_or_else(|| panic!("{path}: no facts of the kont mode"));
        copy.bodies
            .into_iter()
            .find(|b| b.facts.name == "main")
            .map_or_else(|| panic!("{path}: no `main`"), |b| b.facts)
    }

    /// The call of a runtime resume node is a resume point of the clause: its
    /// `Main` node has `resumes_at`, and the region of the rest of the handled
    /// body (the rest frees `w`: a `releases_at` there). The block applies no
    /// summary: no node of the block is a node of `main`.
    #[test]
    fn a_runtime_resume_node_is_a_resume_point_in_the_facts() {
        for (path, label) in [
            ("fixes/r0z4b/t01_ref_rest_frees_bad.wf", "with_timeout"),
            ("fixes/r0z4b/s01_ref_rest_frees_bad.wf", "run"),
        ] {
            let f = facts_of(path);
            let calls: Vec<weft_facts::NodeId> = f
                .resumes_at
                .iter()
                .map(|&(n, _)| n)
                .filter(|&n| f.node(n).kind == "call" && f.node(n).label == label)
                .collect();
            assert!(
                !calls.is_empty(),
                "{path}: no resumes_at at the call: {:?}",
                f.resumes_at
                    .iter()
                    .map(|&(n, _)| (f.node(n).kind.clone(), f.node(n).label.clone()))
                    .collect::<Vec<_>>()
            );
            let frees: Vec<String> = f
                .releases_at
                .iter()
                .filter(|(n, _)| calls.contains(n))
                .map(|&(_, q)| f.place(q).display.clone())
                .collect();
            assert!(
                frees.iter().any(|q| q.starts_with('w')),
                "{path}: {frees:?}"
            );
        }
    }

    /// Each refusal keeps the fallback (the reason of main): R-RT-MULTI (a
    /// `multi` operation), R-RESUMER (the block changes or reads a place
    /// outside its frame, runs a closure, has a block inside it, calls a
    /// function, resumes two times), R-RT-TASK (the rest starts a task in a
    /// scope), R-RT-FORM and R-RT-FAIL (the call is in a handled body of a
    /// local `Fail` handler inside the clause), R-RT-FAIL (a local `Fail`
    /// handler around the `handle`), R-RT-CLOCK (`sim.clock.advance` moves
    /// the clock with no wait: the late timeout at a later `resume`),
    /// R-RT-UNWIND (an `on abort` function that can wait: the cut at the end
    /// of the unwinding).
    #[test]
    fn the_refusals_keep_the_fallback() {
        for path in [
            "fixes/r0z4b/k01_multi_ok.wf",
            "fixes/r0z4b/k01_multi_bad.wf",
            "fixes/r0z4b/b01_block_mut_ok.wf",
            "fixes/r0z4b/c01_closure_in_block_ok.wf",
            "fixes/r0z4b/c01_closure_in_block_bad.wf",
            "fixes/r0z4b/n02_nested_blocks_ok.wf",
            "fixes/r0z4b/n02_nested_blocks_bad.wf",
            "fixes/r0z4b/s02_twice_in_block_bad.wf",
            "fixes/r0z4b/f01_outer_fail_ok.wf",
            "fixes/r0z4b/c02_advance_late_ok.wf",
            "fixes/r0z4b/c02_advance_late_bad.wf",
            "fixes/r0z4b/u01_onabort_sleep_ok.wf",
            "fixes/r0z4b/u01_onabort_sleep_bad.wf",
            "fixes/r0z4b/u01e_onabort_short_ok.wf",
            "fixes/r0z4/rev_z01_timeout_spawn_ok.wf",
            "fixes/r0z4/rev_z02_block_calls_ok.wf",
            "fixes/r0z4/rev_z04_timeout_local_fail_ok.wf",
            "fixes/r0z4/rev_z05_timeout_cut_ref_bad.wf",
            "fixes/r0z4/rev_z06_sim_task_ok.wf",
        ] {
            let src = source(path);
            assert_eq!(runs(&src), 0, "{path}: a runtime resume node");
            if path.ends_with("_ok.wf") {
                assert!(falls_back(&src), "{path}: no fallback");
            }
        }
    }

    /// V22: a record of a runtime resume node that names another closure, or
    /// a block with no call of `sim.run` or `with_timeout`, breaks
    /// `BadResumeRun`.
    #[test]
    fn a_wrong_record_breaks_v22() {
        let src = source("fixes/r0z4b/t01_ref_rest_frees_ok.wf");
        let inst = kont(&src).expect("a kont mode");
        let tys = &inst.built.tys;
        let mut p = inst.built.program.clone();
        assert!(verify_program(&p, tys)
            .iter()
            .all(|x| x.rule != Rule::BadResumeRun));
        let mut wrong = p.resume_runs[0].clone();
        wrong.closure = weft_ir::ClosureId(wrong.closure.0 + 1);
        p.resume_runs = vec![wrong];
        assert!(verify_program(&p, tys)
            .iter()
            .any(|x| x.rule == Rule::BadResumeRun));
        let mut p = inst.built.program.clone();
        let mut moved = p.resume_runs[0].clone();
        moved.block = weft_ir::BlockId(moved.block.0 + 1);
        p.resume_runs = vec![moved];
        assert!(verify_program(&p, tys)
            .iter()
            .any(|x| x.rule == Rule::BadResumeRun));
        // A `multi` continuation of the clause.
        let mut p = inst.built.program.clone();
        let b = p.resume_runs[0].body;
        if let Some(x) = p.bodies.get_mut(b.index()).and_then(|x| x.kont.as_mut()) {
            x.1 = true;
        }
        assert!(verify_program(&p, tys)
            .iter()
            .any(|x| x.rule == Rule::BadResumeRun));
    }
}
