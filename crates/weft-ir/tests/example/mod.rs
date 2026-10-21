//! Hand-built programs of the design (from the sketch `example.rs`, `docs/ir-sketch`).
//!
//! The program of probe m8 (finding M3):
//!
//! ```weft
//! effect Pick { fn pick(v: &Vec<u64>) -> &u64 }
//!
//! fn main() {
//!     let r = handle Pick {
//!         fn pick(v) { &v[0] }
//!     } in {
//!         let w = Vec.new()
//!         w.push(3)
//!         pick(&w)
//!     }
//!     print(r)
//! }
//! ```
//!
//! The sketch gives each local the type id 0. Here each local has its final type, so
//! that the type rules of the verifier (V8, V9) can check the bodies.

#![allow(dead_code)]

use weft_ir::ty::{AdtDecl, AdtKind, EffectDecl, Lang, OpDecl};
use weft_ir::*;

/// The types of the example programs.
pub struct Tys {
    /// The table.
    pub table: TyTable,
    /// `()`.
    pub unit: TyId,
    /// `u64`.
    pub u64: TyId,
    /// `usize`.
    pub usize: TyId,
    /// `Vec<u64>`.
    pub vec_u64: TyId,
    /// `&Vec<u64>`.
    pub ref_vec: TyId,
    /// `&u64`.
    pub ref_u64: TyId,
    /// `Cap<Pick>`.
    pub cap_pick: TyId,
    /// The continuation of `pick`.
    pub kont: TyId,
    /// The type parameter `T0`.
    pub param0: TyId,
    /// `Vec<T0>`.
    pub vec_t: TyId,
    /// `&Vec<T0>`.
    pub ref_vec_t: TyId,
    /// The effect `Pick`.
    pub pick: EffectId,
}

/// Returns a definition with no flags.
pub fn adt(name: &str, generics: u32, kind: AdtKind, lang: Option<Lang>) -> AdtDecl {
    AdtDecl {
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
    }
}

/// Makes the type table of the M3 program.
pub fn m3_tys() -> Tys {
    let mut t = TyTable::new();
    let unit = t.unit();
    let u64 = t.intern(Ty::Int(IntTy::U64));
    let usize = t.intern(Ty::Int(IntTy::Usize));
    let vec = t.push_adt(adt(
        "Vec",
        1,
        AdtKind::Extern {
            elem_unstable: Some(true),
            deref: None,
        },
        Some(Lang::Vec),
    ));
    let vec_u64 = t.intern(Ty::Adt(vec, vec![u64]));
    let ref_vec = t.intern(Ty::Ref(vec_u64));
    let ref_u64 = t.intern(Ty::Ref(u64));
    let pick = t.push_effect(EffectDecl {
        name: "Pick".to_string(),
        identity: "Pick".to_string(),
        ops: vec![OpDecl {
            name: "pick".to_string(),
            params: vec![ref_vec],
            ret: ref_u64,
            multi: false,
        }],
    });
    let cap_pick = t.intern(Ty::Cap(pick));
    let kont = t.intern(Ty::Cont(ref_u64, ref_u64));
    let param0 = t.intern(Ty::Param(0));
    let vec_t = t.intern(Ty::Adt(vec, vec![param0]));
    let ref_vec_t = t.intern(Ty::Ref(vec_t));
    Tys {
        table: t,
        unit,
        u64,
        usize,
        vec_u64,
        ref_vec,
        ref_u64,
        cap_pick,
        kont,
        param0,
        vec_t,
        ref_vec_t,
        pick,
    }
}

/// The origin of each item of the examples: no source.
pub const fn origin() -> Origin {
    Origin {
        span: Span {
            unit: 0,
            lo: 0,
            hi: 0,
        },
        expr: None,
    }
}

/// A local of type `ty`. `copy` is the copy property of the type.
pub fn local(kind: LocalKind, name: Option<&str>, ty: TyId, copy: bool) -> LocalDecl {
    LocalDecl {
        ty,
        kind,
        name: name.map(String::from),
        props: Props {
            copy,
            ..Props::default()
        },
        in_place: false,
        origin: origin(),
    }
}

/// A statement with no source.
pub const fn s(kind: StmtKind) -> Stmt {
    Stmt {
        kind,
        origin: origin(),
    }
}

/// A block with no source.
pub fn blk(stmts: Vec<StmtKind>, term: TermKind, cleanup: bool) -> Block {
    Block {
        stmts: stmts.into_iter().map(s).collect(),
        term: Term {
            kind: term,
            origin: origin(),
        },
        cleanup,
    }
}

/// The whole local `_l`.
pub const fn pl(l: u32) -> Place {
    Place::local(LocalId(l))
}

/// `(*_l)` and more projections.
pub fn deref(l: u32, more: Vec<Proj>) -> Place {
    let mut proj = vec![Proj::Deref(DerefKind::Ref)];
    proj.extend(more);
    Place {
        local: LocalId(l),
        proj,
    }
}

/// `main`: the `handle` and the use of its value. No environment operands: the
/// handled body and the clause name the locals of `main` as upvar locals (here they
/// name none).
pub fn main_body(t: &Tys) -> Body {
    use StmtKind::*;
    let locals = vec![
        local(LocalKind::Return, None, t.unit, true),
        local(LocalKind::User, Some("r"), t.ref_u64, true),
    ];
    let blocks = vec![
        // bb0
        blk(
            vec![Live(LocalId(1))],
            TermKind::Handle {
                handler: HandlerId(0),
                dest: pl(1),
                next: BlockId(1),
                unwind: Some(BlockId(2)),
            },
            false,
        ),
        // bb1: print(r); the frame end: the value goes to `_0`, then `r` ends
        blk(
            vec![
                Print(vec![Operand::Copy(pl(1))]),
                Assign(pl(0), Rvalue::Use(Operand::Const(Const::Unit))),
                Dead(LocalId(1)),
            ],
            TermKind::Return,
            false,
        ),
        // bb2: cleanup of the frame: `r` has a cell, no value
        blk(
            vec![Dead(LocalId(1)), Dead(LocalId(0))],
            TermKind::Goto(BlockId(3)),
            true,
        ),
        // bb3: unwind exit
        blk(vec![], TermKind::UnwindExit, true),
    ];
    Body {
        kind: BodyKind::Fn(FnId(0)),
        parent: None,
        locals,
        ret: LocalId(0),
        params: vec![],
        caps: vec![],
        kont: None,
        blocks,
        entry: BlockId(0),
        unwind_exit: BlockId(3),
        cap_env: CapEnvId(0),
        origin: origin(),
    }
}

/// The handled body: `let w = Vec.new(); w.push(3); pick(&w)`.
pub fn handled_body(t: &Tys) -> Body {
    use StmtKind::*;
    let locals = vec![
        local(LocalKind::Return, None, t.ref_u64, true),
        local(LocalKind::Cap(t.pick), Some("Pick"), t.cap_pick, true),
        local(LocalKind::User, Some("w"), t.vec_u64, false),
        local(LocalKind::Temp(TempKind::Receiver), None, t.ref_vec, true),
        local(LocalKind::Temp(TempKind::Discarded), None, t.unit, true),
        local(LocalKind::Temp(TempKind::Operand), None, t.ref_vec, true),
    ];
    let blocks = vec![
        // bb0: let w = Vec.new()
        blk(
            vec![Live(LocalId(2))],
            TermKind::Call {
                callee: Callee::Fn(FnId(1), vec![t.u64]),
                args: vec![],
                dest: pl(2),
                caps: CapArgs::Lexical(CapEnvId(1)),
                next: Some(BlockId(1)),
                unwind: None,
            },
            false,
        ),
        // bb1: w.push(3)
        blk(
            vec![
                Live(LocalId(3)),
                Assign(pl(3), Rvalue::Ref(pl(2))),
                Live(LocalId(4)),
            ],
            TermKind::Call {
                callee: Callee::Fn(FnId(2), vec![t.u64]),
                args: vec![
                    Operand::Move(pl(3)),
                    Operand::Const(Const::Int(3, IntTy::U64)),
                ],
                dest: pl(4),
                caps: CapArgs::Lexical(CapEnvId(1)),
                next: Some(BlockId(2)),
                unwind: None,
            },
            false,
        ),
        // bb2: the end of the statement; then the tail `pick(&w)` into `_0`
        blk(
            vec![
                Dead(LocalId(4)),
                Dead(LocalId(3)),
                Live(LocalId(5)),
                Assign(pl(5), Rvalue::Ref(pl(2))),
            ],
            TermKind::Perform {
                cap: CapOperand::Local(pl(1)),
                op: OpIdx(0),
                args: vec![Operand::Move(pl(5))],
                dest: pl(0),
                next: BlockId(3),
                unwind: Some(BlockId(4)),
            },
            false,
        ),
        // bb3: the value is in `_0`; then the locals end, then the tail temporaries,
        // then the capability parameter (the frame-end order of the interpreter)
        blk(
            vec![Dead(LocalId(2)), Dead(LocalId(5)), Dead(LocalId(1))],
            TermKind::Return,
            false,
        ),
        // bb4: cleanup of the frame: temporaries newest first, then locals from the
        // highest index, then `_0` (no value yet), then the capability (V16)
        blk(
            vec![
                Dead(LocalId(5)),
                UnwindValue(pl(2), UnwindAction::Drop),
                Dead(LocalId(2)),
                Dead(LocalId(0)),
                Dead(LocalId(1)),
            ],
            TermKind::Goto(BlockId(5)),
            true,
        ),
        // bb5: unwind exit
        blk(vec![], TermKind::UnwindExit, true),
    ];
    Body {
        kind: BodyKind::Handled(HandlerId(0)),
        parent: Some(BodyId(0)),
        locals,
        ret: LocalId(0),
        params: vec![],
        caps: vec![(t.pick, LocalId(1))],
        kont: None,
        blocks,
        entry: BlockId(0),
        unwind_exit: BlockId(5),
        cap_env: CapEnvId(1),
        origin: origin(),
    }
}

/// The clause: `fn pick(v) { &v[0] }`. It does not resume, so the `Dead` of its fresh
/// continuation at the frame end drops the continuation (the handled body unwinds
/// after the clause returns, as `do_return` of the effects model). On a cleanup path
/// the continuation goes first (`UnwindKont`, as `step_unwind_drop`).
pub fn clause_body(t: &Tys) -> Body {
    use StmtKind::*;
    let locals = vec![
        local(LocalKind::Return, None, t.ref_u64, true),
        local(LocalKind::Param(0), Some("v"), t.ref_vec, true),
        local(LocalKind::Kont(false), Some("resume"), t.kont, false),
        local(LocalKind::Temp(TempKind::Operand), None, t.usize, true),
    ];
    let blocks = vec![
        blk(
            vec![
                Live(LocalId(3)),
                Assign(
                    pl(3),
                    Rvalue::Use(Operand::Const(Const::Int(0, IntTy::Usize))),
                ),
                Bounds(deref(1, vec![]), Operand::Copy(pl(3))),
                Assign(pl(0), Rvalue::Ref(deref(1, vec![Proj::Index(LocalId(3))]))),
                Dead(LocalId(3)),
                Dead(LocalId(2)),
                Dead(LocalId(1)),
            ],
            TermKind::Return,
            false,
        ),
        blk(
            vec![
                UnwindKont(LocalId(2)),
                Dead(LocalId(2)),
                Dead(LocalId(0)),
                Dead(LocalId(1)),
            ],
            TermKind::Goto(BlockId(2)),
            true,
        ),
        blk(vec![], TermKind::UnwindExit, true),
    ];
    Body {
        kind: BodyKind::Clause(HandlerId(0), OpIdx(0)),
        parent: Some(BodyId(0)),
        locals,
        ret: LocalId(0),
        params: vec![LocalId(1)],
        caps: vec![],
        kont: Some((LocalId(2), false)),
        blocks,
        entry: BlockId(0),
        unwind_exit: BlockId(2),
        cap_env: CapEnvId(0),
        origin: origin(),
    }
}

/// The program of probe m8 (finding M3): three bodies, one handler, two capability
/// environments. The sketch has no function declarations; here `main` and the two
/// extern functions of `Vec` are declared, so that the calls name declarations.
pub fn m3_program(t: &Tys) -> Program {
    Program {
        bodies: vec![main_body(t), handled_body(t), clause_body(t)],
        fns: vec![
            FnDecl {
                name: "main".to_string(),
                body: Some(BodyId(0)),
                params: vec![],
                ret: t.unit,
                generics: 0,
                stated_row: None,
                intrinsic: None,
            },
            FnDecl {
                name: "Vec.new".to_string(),
                body: None,
                params: vec![],
                ret: t.vec_t,
                generics: 1,
                stated_row: Some(vec![]),
                intrinsic: None,
            },
            FnDecl {
                name: "Vec.push".to_string(),
                body: None,
                params: vec![t.ref_vec_t, t.param0],
                ret: t.unit,
                generics: 1,
                stated_row: Some(vec![]),
                intrinsic: None,
            },
        ],
        closures: vec![],
        handlers: vec![HandlerDecl {
            effect: t.pick,
            clauses: vec![(OpIdx(0), BodyId(2))],
            handled: BodyId(1),
            site: BodyId(0),
            multi: false,
        }],
        scopes: vec![],
        spawns: vec![],
        cap_envs: vec![
            CapEnv {
                parent: None,
                adds: vec![],
            },
            CapEnv {
                parent: Some(CapEnvId(0)),
                adds: vec![(t.pick, pl(1))],
            },
        ],
        tests: vec![],
    }
}
