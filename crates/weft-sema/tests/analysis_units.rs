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

    /// The refusals of the static closure copy: the local can hold one of two
    /// closures, the closure moves a capture into its value (`ByMove`, a
    /// `once` closure). Each one keeps the call of the closure value. (A local
    /// that gets its closure from a block, `a06_ends`, gets a copy region from
    /// stage R0k-b2 on: the copy reads the capture whose source ends through
    /// the environment local of the region, `copy_env`.)
    #[test]
    fn a_closure_copy_is_refused_for_two_closures_a_move_and_another_value() {
        for name in ["a04_two_closures_bad.wf", "a05_by_value_bad.wf"] {
            let (_, b) = built(&r0k2(name));
            assert!(
                instantiate(&b).is_none_or(|i| i.closure_calls == 0),
                "{name}: a copy"
            );
        }
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
    /// copy of the first closure.
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
            assert!(
                instantiate(&b).is_none_or(|i| i.closure_calls == 0),
                "{name}: a copy"
            );
        }
    }

    /// The order of the weak guard (the review of R0k-a2): the analysis runs
    /// `apply` before `main`, the maker of the closure with the weak form,
    /// and the guard still refuses the call of `apply` that gives it the
    /// closure where the local handler serves the operation, also with the
    /// copies (`apply` gets no copy).
    #[test]
    fn the_weak_guard_refuses_a_value_given_to_a_body_analyzed_before_its_maker() {
        let (a, b) = built(&r0k2("g26_weak_run_in_callee_bad.wf"));
        let weak = weft_sema::analysis::transfer::WeakRowOps::enter();
        let Err(u) = weft_sema::factgen::components(&a, &b) else {
            panic!("the guard does not refuse the call");
        };
        assert_eq!(u.reason, weft_sema::analysis::transfer::OP_KEPT);
        drop(weak);
        if let Some(inst) = instantiate(&b) {
            let _weak = weft_sema::analysis::transfer::WeakRowOps::enter();
            assert!(weft_sema::factgen::components(&a, &inst.built).is_err());
        }
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
        for name in [
            "a01_two_paths_bad.wf",
            "a02_vec_same_id_bad.wf",
            "a03_put_fns_bad.wf",
            "u12_scope_body_bad.wf",
            "u13_clause_bad.wf",
            "u14_task_bad.wf",
            "o01_once_two_runs_bad.wf",
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

    /// Each refusal of the probes: two runs, a perform between the make and
    /// the run, a call that can abort between them, a borrow of the closure
    /// value, a make in a body inside the clause, a field on the chain.
    #[test]
    fn the_probes_of_a_refusal_get_no_copy() {
        for name in [
            "c03_two_runs_ok.wf",
            "c05_perform_between_ok.wf",
            "c06_call_between_ok.wf",
            "c07_use_after_ok.wf",
            "c08_nested_ok.wf",
            "c09_field_ok.wf",
        ] {
            assert!(copies(&probe(name)).is_none(), "{name}: a copy");
        }
    }

    /// The continuation is named again after the make (a `resume` of the
    /// clause after the run): no copy.
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
        assert!(copies(src).is_none());
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

    /// A path from the make that does not reach the run (a branch): no copy.
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
        assert!(copies(src).is_none());
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
        let (a, _) = built(&probe("c03_two_runs_ok.wf"));
        let p = a
            .ir_scope
            .as_ref()
            .and_then(|s| s.pending.as_ref())
            .expect("pending");
        assert!(p.copy.is_none(), "a view of the copies");
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

    /// D4: a `multi` continuation keeps the weak update, so the escape of
    /// the closure in `f` stays pending (the program falls back).
    #[test]
    fn a_multi_continuation_keeps_the_weak_update() {
        let (_, pending) = scope("d02_multi_weak.wf");
        assert!(
            pending
                .as_deref()
                .is_some_and(|r| r.contains("a capability that leaves its handler")),
            "{pending:?}"
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

    /// A spawn in a closure on the scope of the body around it: the task can
    /// outlive the closure body, so each other write counts.
    #[test]
    fn a_spawn_in_a_closure_on_an_outer_scope_stays_conservative() {
        let (_, pending) = scope("s4_spawn_in_closure_ok.wf");
        assert!(late(pending.as_deref()), "{pending:?}");
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

    /// The scope of the program `src` (its fallback and the reason of its
    /// pending construct).
    fn scope_of(src: &str) -> (Option<String>, String) {
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
        let s = a.ir_scope.expect("a scope");
        (s.fallback, s.pending.map(|p| p.reason).unwrap_or_default())
    }

    /// Stage R0k-c2 fix 1: a reference of a clause frame into an `rc` group
    /// across a `multi` operation of a handler of a caller makes the program
    /// pending (the clause of the caller can change the group through
    /// another handle): a reference that the clause takes (`p08`), a
    /// parameter whose argument is in the group (`n19`), and a reference of
    /// the frame of the function (`n18`).
    #[test]
    fn a_clause_reference_into_an_rc_group_across_a_row_is_pending() {
        for name in [
            "p08_rc_between_param_bad.wf",
            "n19_rc_param_arg_bad.wf",
            "n18_rc_handled_frame_bad.wf",
        ] {
            let (fallback, pending) = scope_of(&probe("r0kc2c", name));
            assert_eq!(fallback, None, "{name}");
            assert!(
                pending.contains(weft_sema::factgen::handlers::RC_ACROSS_ROW),
                "{name}: {pending}"
            );
        }
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
}
