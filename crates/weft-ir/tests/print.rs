//! Tests of the text form of the IR (`docs/ir.md` 3.3).

mod example;

use example::{blk, deref, local, m3_program, m3_tys, pl, Tys};
use weft_ir::print::{print_program, Printer};
use weft_ir::ty::{AdtKind, FieldDecl, VariantDecl};
use weft_ir::*;

/// The M3 program prints to the golden file.
#[test]
fn m3_prints_to_the_golden_file() {
    let t = m3_tys();
    let p = m3_program(&t);
    let text = print_program(&p, &t.table);
    let want = include_str!("data/m3.ir");
    assert_eq!(text, want, "the printed text:\n{text}");
}

/// A program with a declaration of each kind, for the table test.
fn table_program(t: &mut Tys) -> (Program, Body, TyId, TyId) {
    let point = t.table.push_adt(example::adt(
        "Point",
        0,
        AdtKind::Struct(vec![
            FieldDecl {
                name: "x".to_string(),
                ty: t.u64,
                place: false,
            },
            FieldDecl {
                name: "y".to_string(),
                ty: t.u64,
                place: false,
            },
        ]),
        None,
    ));
    let point = t.table.intern(Ty::Adt(point, vec![]));
    let opt = t.table.push_adt(example::adt(
        "Opt",
        0,
        AdtKind::Enum(vec![
            VariantDecl {
                name: "None".to_string(),
                fields: vec![],
            },
            VariantDecl {
                name: "Some".to_string(),
                fields: vec![t.u64],
            },
        ]),
        None,
    ));
    let opt = t.table.intern(Ty::Adt(opt, vec![]));
    let mut p = m3_program(t);
    p.fns.push(FnDecl {
        name: "close".to_string(),
        body: None,
        params: vec![point],
        ret: t.unit,
        generics: 0,
        stated_row: Some(vec![]),
        intrinsic: None,
    });
    let locals = vec![
        local(LocalKind::Return, None, t.unit, true),
        local(LocalKind::Param(0), Some("v"), t.ref_vec, true),
        local(LocalKind::User, Some("a"), t.u64, true),
        local(LocalKind::Temp(TempKind::Value), None, point, true),
        local(LocalKind::User, Some("o"), opt, true),
        local(LocalKind::Kont(true), Some("k"), t.kont, false),
        local(LocalKind::Cap(t.pick), Some("Pick"), t.cap_pick, true),
        local(LocalKind::Upvar(LocalId(1)), Some("r"), t.ref_u64, true),
    ];
    let body = Body {
        kind: BodyKind::Fn(FnId(0)),
        parent: None,
        locals,
        ret: LocalId(0),
        params: vec![LocalId(1)],
        caps: vec![],
        kont: None,
        blocks: vec![blk(vec![], TermKind::Return, false)],
        entry: BlockId(0),
        unwind_exit: BlockId(0),
        cap_env: CapEnvId(0),
        origin: example::origin(),
    };
    (p, body, point, opt)
}

/// Each statement kind, each right side and each terminator kind prints once.
#[test]
fn each_statement_and_terminator_kind_prints() {
    let mut t = m3_tys();
    let (p, body, point, opt) = table_program(&mut t);
    let pr = Printer::new(&p, &t.table);
    let a = || Operand::Copy(pl(2));
    let m = |l: u32| Operand::Move(pl(l));
    let field = Place {
        local: LocalId(3),
        proj: vec![Proj::Field(FieldIdx(1))],
    };
    let variant = Place {
        local: LocalId(4),
        proj: vec![Proj::Variant(VariantIdx(1)), Proj::Field(FieldIdx(0))],
    };
    let split = Place {
        local: LocalId(1),
        proj: vec![
            Proj::Deref(DerefKind::Ref),
            Proj::Elems,
            Proj::Split(SplitId(0), Side::Left),
        ],
    };
    let split_r = Place {
        local: LocalId(1),
        proj: vec![
            Proj::Deref(DerefKind::Ref),
            Proj::Elems,
            Proj::Split(SplitId(2), Side::Right),
        ],
    };
    let index = Place {
        local: LocalId(1),
        proj: vec![
            Proj::Deref(DerefKind::Ref),
            Proj::Field(FieldIdx(0)),
            Proj::Index(LocalId(2)),
        ],
    };
    let stmts: Vec<(StmtKind, &str)> = vec![
        (StmtKind::Live(LocalId(2)), "Live(_2)"),
        (StmtKind::Dead(LocalId(2)), "Dead(_2)"),
        (StmtKind::Assign(pl(2), Rvalue::Use(a())), "_2 = copy _2"),
        (StmtKind::Drop(deref(1, vec![])), "Drop((*_1))"),
        (StmtKind::Consume(pl(4)), "Consume(_4)"),
        (StmtKind::Uninit(field), "Uninit(_3.1)"),
        (
            StmtKind::Bounds(deref(1, vec![]), a()),
            "Bounds((*_1), copy _2)",
        ),
        (StmtKind::Mention(variant), "Mention((_4 as #1).0)"),
        (StmtKind::Print(vec![a(), m(3)]), "Print(copy _2, move _3)"),
        (StmtKind::Print(vec![]), "Print()"),
        (
            StmtKind::UnwindValue(pl(3), UnwindAction::OnAbort(FnId(3))),
            "UnwindValue(_3, OnAbort(close))",
        ),
        (
            StmtKind::UnwindValue(pl(3), UnwindAction::Drop),
            "UnwindValue(_3, Drop)",
        ),
        (
            StmtKind::UnwindValue(pl(3), UnwindAction::Fault),
            "UnwindValue(_3, Fault)",
        ),
        (StmtKind::UnwindKont(LocalId(5)), "UnwindKont(_5)"),
    ];
    for (k, want) in &stmts {
        assert_eq!(pr.stmt(k), *want);
    }
    let int = |v: i128, i: IntTy| Operand::Const(Const::Int(v, i));
    let rvalues: Vec<(Rvalue, &str)> = vec![
        (Rvalue::Use(m(3)), "move _3"),
        (Rvalue::Use(Operand::Const(Const::Unit)), "const ()"),
        (Rvalue::Use(Operand::Const(Const::Bool(true))), "const true"),
        (Rvalue::Use(int(-7, IntTy::I64)), "const -7i64"),
        (
            Rvalue::Use(Operand::Const(Const::Str("a\"b\n".to_string()))),
            "const \"a\\\"b\\n\"",
        ),
        (
            Rvalue::Use(Operand::Const(Const::Duration(250))),
            "const 250ms",
        ),
        (
            Rvalue::Use(Operand::Const(Const::Fn(FnId(1), vec![t.u64]))),
            "const Vec.new<u64>",
        ),
        (
            Rvalue::Use(Operand::Const(Const::Fn(FnId(0), vec![]))),
            "const main",
        ),
        (Rvalue::Ref(index), "&(*_1).0[_2]"),
        (Rvalue::Ref(split), "&(*_1)[][..s0]"),
        (Rvalue::Ref(split_r), "&(*_1)[][s2..]"),
        (
            Rvalue::Binary(BinOp::Add, Some(IntTy::U64), a(), int(1, IntTy::U64)),
            "Add<u64>(copy _2, const 1u64)",
        ),
        (
            Rvalue::Binary(BinOp::Sub, Some(IntTy::U8), a(), a()),
            "Sub<u8>(copy _2, copy _2)",
        ),
        (
            Rvalue::Binary(BinOp::Mul, Some(IntTy::U16), a(), a()),
            "Mul<u16>(copy _2, copy _2)",
        ),
        (
            Rvalue::Binary(BinOp::Div, Some(IntTy::U32), a(), a()),
            "Div<u32>(copy _2, copy _2)",
        ),
        (
            Rvalue::Binary(BinOp::Rem, Some(IntTy::Usize), a(), a()),
            "Rem<usize>(copy _2, copy _2)",
        ),
        (
            Rvalue::Binary(BinOp::Eq, None, a(), a()),
            "Eq(copy _2, copy _2)",
        ),
        (
            Rvalue::Binary(BinOp::Ne, None, a(), a()),
            "Ne(copy _2, copy _2)",
        ),
        (
            Rvalue::Binary(BinOp::Lt, None, a(), a()),
            "Lt(copy _2, copy _2)",
        ),
        (
            Rvalue::Binary(BinOp::Le, None, a(), a()),
            "Le(copy _2, copy _2)",
        ),
        (
            Rvalue::Binary(BinOp::Gt, None, a(), a()),
            "Gt(copy _2, copy _2)",
        ),
        (
            Rvalue::Binary(BinOp::Ge, None, a(), a()),
            "Ge(copy _2, copy _2)",
        ),
        (
            Rvalue::Unary(UnOp::Neg, Some(IntTy::I32), a()),
            "Neg<i32>(copy _2)",
        ),
        (Rvalue::Unary(UnOp::Not, None, a()), "Not(copy _2)"),
        (Rvalue::Aggregate(AggKind::Tuple, vec![]), "()"),
        (Rvalue::Aggregate(AggKind::Tuple, vec![a()]), "(copy _2,)"),
        (
            Rvalue::Aggregate(AggKind::Tuple, vec![a(), m(3)]),
            "(copy _2, move _3)",
        ),
        (
            Rvalue::Aggregate(AggKind::Array, vec![a(), a()]),
            "[copy _2, copy _2]",
        ),
        (Rvalue::Aggregate(AggKind::Vec, vec![a()]), "vec[copy _2]"),
        (
            Rvalue::Aggregate(AggKind::Struct(point), vec![a(), int(2, IntTy::U64)]),
            "Point { copy _2, const 2u64 }",
        ),
        (
            Rvalue::Aggregate(AggKind::Variant(opt, VariantIdx(1)), vec![a()]),
            "Opt::Some(copy _2)",
        ),
        (
            Rvalue::Aggregate(AggKind::Variant(opt, VariantIdx(0)), vec![]),
            "Opt::None()",
        ),
        (
            Rvalue::Aggregate(AggKind::Closure(ClosureId(0)), vec![m(3)]),
            "closure c0(move _3)",
        ),
        (Rvalue::Len(deref(1, vec![])), "Len((*_1))"),
        (Rvalue::Discriminant(pl(4)), "Discriminant(_4)"),
        (
            Rvalue::Concat(vec![Operand::Const(Const::Str("n=".to_string())), a()]),
            "Concat(const \"n=\", copy _2)",
        ),
        (
            Rvalue::Iter(IterSource::Elems(deref(1, vec![]))),
            "Iter(elems (*_1))",
        ),
        (
            Rvalue::Iter(IterSource::Range(int(0, IntTy::Usize), a())),
            "Iter(const 0usize..copy _2)",
        ),
    ];
    for (r, want) in &rvalues {
        assert_eq!(pr.rvalue(r), *want);
    }
    let b = BlockId;
    let terms: Vec<(TermKind, &str)> = vec![
        (TermKind::Goto(b(3)), "Goto(bb3)"),
        (
            TermKind::Switch {
                on: a(),
                arms: vec![(0, b(1)), (1, b(2))],
                otherwise: b(3),
            },
            "switch copy _2 -> [0: bb1, 1: bb2, otherwise: bb3]",
        ),
        (TermKind::Return, "Return"),
        (TermKind::UnwindExit, "UnwindExit"),
        (TermKind::Unreachable, "Unreachable"),
        (
            TermKind::Call {
                callee: Callee::Fn(FnId(2), vec![t.u64]),
                args: vec![m(1), int(3, IntTy::U64)],
                dest: pl(0),
                caps: CapArgs::Lexical(CapEnvId(1)),
                next: Some(b(1)),
                unwind: Some(b(4)),
            },
            "_0 = call Vec.push<u64>(move _1, const 3u64) / e1 -> [bb1, unwind: bb4]",
        ),
        (
            TermKind::Call {
                callee: Callee::Value(a()),
                args: vec![],
                dest: pl(0),
                caps: CapArgs::Root,
                next: None,
                unwind: Some(b(4)),
            },
            "_0 = call (copy _2)() / root -> [unwind: bb4]",
        ),
        (
            TermKind::Call {
                callee: Callee::Fn(FnId(0), vec![]),
                args: vec![],
                dest: pl(0),
                caps: CapArgs::Root,
                next: Some(b(2)),
                unwind: None,
            },
            "_0 = call main() / root -> [bb2]",
        ),
        (
            TermKind::Perform {
                cap: CapOperand::Local(pl(6)),
                op: OpIdx(0),
                args: vec![m(1)],
                dest: pl(7),
                next: b(1),
                unwind: Some(b(2)),
            },
            "_7 = perform Local(_6).pick(move _1) -> [bb1, unwind: bb2]",
        ),
        (
            TermKind::Perform {
                cap: CapOperand::Row(t.pick),
                op: OpIdx(0),
                args: vec![],
                dest: pl(7),
                next: b(1),
                unwind: None,
            },
            "_7 = perform Row(Pick).pick() -> [bb1]",
        ),
        (
            TermKind::Resume {
                kont: pl(5),
                arg: Operand::Copy(pl(7)),
                dest: pl(7),
                next: b(1),
                unwind: Some(b(2)),
            },
            "_7 = resume _5(copy _7) -> [bb1, unwind: bb2]",
        ),
        (
            TermKind::Handle {
                handler: HandlerId(0),
                dest: pl(7),
                next: b(1),
                unwind: Some(b(2)),
            },
            "_7 = handle h0 -> [bb1, unwind: bb2]",
        ),
        (
            TermKind::Scope {
                scope: ScopeId(0),
                dest: pl(2),
                next: b(1),
                unwind: Some(b(2)),
            },
            "_2 = scope s0 -> [bb1, unwind: bb2]",
        ),
        (
            TermKind::ScopeWait {
                scope: pl(1),
                orphans: vec![LocalId(4), LocalId(5)],
                next: b(1),
                unwind: Some(b(2)),
            },
            "scope_wait _1, orphans [_4, _5] -> [bb1, unwind: bb2]",
        ),
        (
            TermKind::ScopeWait {
                scope: pl(1),
                orphans: vec![],
                next: b(1),
                unwind: Some(b(2)),
            },
            "scope_wait _1 -> [bb1, unwind: bb2]",
        ),
        (
            TermKind::Spawn {
                site: SpawnId(0),
                scope: Operand::Copy(pl(1)),
                task: m(3),
                dest: Some(pl(4)),
                next: b(1),
            },
            "_4 = spawn sp0(copy _1, move _3) -> [bb1]",
        ),
        (
            TermKind::Spawn {
                site: SpawnId(1),
                scope: Operand::Copy(pl(1)),
                task: m(3),
                dest: None,
                next: b(1),
            },
            "spawn sp1(copy _1, move _3) -> [bb1]",
        ),
        (
            TermKind::Join {
                task: m(4),
                dest: pl(2),
                next: b(1),
                unwind: Some(b(2)),
            },
            "_2 = join move _4 -> [bb1, unwind: bb2]",
        ),
        (
            TermKind::Detach {
                task: m(4),
                next: b(1),
            },
            "detach move _4 -> [bb1]",
        ),
        (
            TermKind::Fork {
                sites: vec![SpawnId(0), SpawnId(1)],
                branches: vec![m(3), m(4)],
                dest: pl(2),
                next: b(1),
                unwind: Some(b(2)),
            },
            "_2 = fork [sp0: move _3, sp1: move _4] -> [bb1, unwind: bb2]",
        ),
        (
            TermKind::Assert {
                cond: a(),
                next: b(1),
                unwind: Some(b(2)),
            },
            "assert copy _2 -> [bb1, unwind: bb2]",
        ),
        (
            TermKind::IterNext {
                iter: pl(3),
                dest: pl(2),
                next: b(1),
                done: b(5),
            },
            "_2 = next _3 -> [bb1, done: bb5]",
        ),
    ];
    for (k, want) in &terms {
        assert_eq!(pr.term(&body, k), *want);
    }
    // The kind, the type and the name of each local.
    let locals = [
        "_0: () (Return)",
        "_1: &Vec<u64> (Param(0) `v`)",
        "_2: u64 (User `a`)",
        "_3: Point (Temp(Value))",
        "_4: Opt (User `o`)",
        "_5: resume(&u64) -> &u64 (Kont(multi) `k`)",
        "_6: Cap<Pick> (Cap(Pick) `Pick`)",
        "_7: &u64 (Upvar(_1) `r`)",
    ];
    for (l, want) in body.local_ids().zip(locals) {
        assert_eq!(pr.local(&body, l), want);
    }
}
