//! A worked example (design sketch): the IR of probe m8, built by hand.
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

use crate::*;
use std::fmt::Write as _;

fn origin() -> Origin {
    Origin { span: Span { unit: 0, lo: 0, hi: 0 }, expr: None }
}

fn local(kind: LocalKind, name: Option<&str>) -> LocalDecl {
    LocalDecl { ty: TyId(0), kind, name: name.map(String::from), props: Props::default(), in_place: false, origin: origin() }
}

fn s(kind: StmtKind) -> Stmt {
    Stmt { kind, origin: origin() }
}

fn blk(stmts: Vec<StmtKind>, term: TermKind, cleanup: bool) -> Block {
    Block { stmts: stmts.into_iter().map(s).collect(), term: Term { kind: term, origin: origin() }, cleanup }
}

fn pl(l: u32) -> Place {
    Place { local: LocalId(l), proj: vec![] }
}

fn deref(l: u32, more: Vec<Proj>) -> Place {
    let mut proj = vec![Proj::Deref(DerefKind::Ref)];
    proj.extend(more);
    Place { local: LocalId(l), proj }
}

/// `main`: the `handle` and the use of its value. No environment operands: the
/// handled body and the clause name the locals of `main` as upvar locals (here they
/// name none).
pub fn main_body() -> Body {
    use StmtKind::*;
    let locals = vec![local(LocalKind::Return, None), local(LocalKind::User, Some("r"))];
    let blocks = vec![
        // bb0
        blk(
            vec![Live(LocalId(1))],
            TermKind::Handle { handler: HandlerId(0), dest: pl(1), next: BlockId(1), unwind: Some(BlockId(2)) },
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
        blk(vec![Dead(LocalId(1)), Dead(LocalId(0))], TermKind::Goto(BlockId(3)), true),
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
pub fn handled_body() -> Body {
    use StmtKind::*;
    let locals = vec![
        local(LocalKind::Return, None),
        local(LocalKind::Cap(EffectId(0)), Some("Pick")),
        local(LocalKind::User, Some("w")),
        local(LocalKind::Temp(TempKind::Receiver), None),
        local(LocalKind::Temp(TempKind::Discarded), None),
        local(LocalKind::Temp(TempKind::Operand), None),
    ];
    let blocks = vec![
        // bb0: let w = Vec.new()
        blk(
            vec![Live(LocalId(2))],
            TermKind::Call {
                callee: Callee::Fn(FnId(1), vec![TyId(1)]),
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
            vec![Live(LocalId(3)), Assign(pl(3), Rvalue::Ref(pl(2))), Live(LocalId(4))],
            TermKind::Call {
                callee: Callee::Fn(FnId(2), vec![TyId(1)]),
                args: vec![Operand::Move(pl(3)), Operand::Const(Const::Int(3, IntTy::U64))],
                dest: pl(4),
                caps: CapArgs::Lexical(CapEnvId(1)),
                next: Some(BlockId(2)),
                unwind: None,
            },
            false,
        ),
        // bb2: the end of the statement; then the tail `pick(&w)` into `_0`
        blk(
            vec![Dead(LocalId(4)), Dead(LocalId(3)), Live(LocalId(5)), Assign(pl(5), Rvalue::Ref(pl(2)))],
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
        blk(vec![Dead(LocalId(2)), Dead(LocalId(5)), Dead(LocalId(1))], TermKind::Return, false),
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
        caps: vec![(EffectId(0), LocalId(1))],
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
pub fn clause_body() -> Body {
    use StmtKind::*;
    let locals = vec![
        local(LocalKind::Return, None),
        local(LocalKind::Param(0), Some("v")),
        local(LocalKind::Kont(false), Some("resume")),
        local(LocalKind::Temp(TempKind::Operand), None),
    ];
    let blocks = vec![
        blk(
            vec![
                Live(LocalId(3)),
                Assign(pl(3), Rvalue::Use(Operand::Const(Const::Int(0, IntTy::Usize)))),
                Bounds(deref(1, vec![]), Operand::Copy(pl(3))),
                Assign(pl(0), Rvalue::Ref(deref(1, vec![Proj::Index(LocalId(3))]))),
                Dead(LocalId(3)),
                Dead(LocalId(2)),
                Dead(LocalId(1)),
            ],
            TermKind::Return,
            false,
        ),
        blk(vec![UnwindKont(LocalId(2)), Dead(LocalId(2)), Dead(LocalId(0)), Dead(LocalId(1))], TermKind::Goto(BlockId(2)), true),
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
/// environments.
pub fn m3_program() -> Program {
    Program {
        bodies: vec![main_body(), handled_body(), clause_body()],
        fns: vec![],
        closures: vec![],
        handlers: vec![HandlerDecl {
            effect: EffectId(0),
            clauses: vec![(OpIdx(0), BodyId(2))],
            handled: BodyId(1),
            site: BodyId(0),
            multi: false,
        }],
        scopes: vec![],
        spawns: vec![],
        cap_envs: vec![
            CapEnv { parent: None, adds: vec![] },
            CapEnv { parent: Some(CapEnvId(0)), adds: vec![(EffectId(0), pl(1))] },
        ],
    }
}

/// Probe J5d of the soundness judge: a maker returns a closure that borrows a
/// captured plain struct (`|| print(norm(&p))`). Rule CAPTURE gives `ByRef`, so the
/// closure points into the cell of `p` and W0204 rejects the return. With
/// `kept: true` the sketch builds the wrong form (`Kept` with a borrow), which
/// verifier rule V13 rejects.
pub fn j5d_program(kept: bool) -> Program {
    use StmtKind::*;
    let mode = if kept { CaptureMode::Kept } else { CaptureMode::ByRef };
    // fn make(a: u64) -> fn() { let p = Point { x: a, y: 2 }; || print(norm(&p)) }
    let field_op = if kept { Operand::Copy(pl(2)) } else { Operand::Move(pl(4)) };
    let mut make_stmts = vec![
        Live(LocalId(2)),
        Assign(
            pl(2),
            Rvalue::Aggregate(
                AggKind::Struct(TyId(5)),
                vec![Operand::Copy(pl(1)), Operand::Const(Const::Int(2, IntTy::U64))],
            ),
        ),
        Live(LocalId(3)),
    ];
    if !kept {
        make_stmts.push(Live(LocalId(4)));
        make_stmts.push(Assign(pl(4), Rvalue::Ref(pl(2))));
    }
    make_stmts.push(Assign(pl(3), Rvalue::Aggregate(AggKind::Closure(ClosureId(0)), vec![field_op])));
    if !kept {
        make_stmts.push(Dead(LocalId(4)));
    }
    make_stmts.extend([Assign(pl(0), Rvalue::Use(Operand::Move(pl(3)))), Dead(LocalId(2)), Dead(LocalId(3)), Dead(LocalId(1))]);
    let make = Body {
        kind: BodyKind::Fn(FnId(0)),
        parent: None,
        locals: vec![
            local(LocalKind::Return, None),
            local(LocalKind::Param(0), Some("a")),
            local(LocalKind::User, Some("p")),
            local(LocalKind::Temp(TempKind::Value), None),
            local(LocalKind::Temp(TempKind::Operand), None),
        ],
        ret: LocalId(0),
        params: vec![LocalId(1)],
        caps: vec![],
        kont: None,
        blocks: vec![
            blk(make_stmts, TermKind::Return, false),
            blk(vec![], TermKind::UnwindExit, true),
        ],
        entry: BlockId(0),
        unwind_exit: BlockId(1),
        cap_env: CapEnvId(0),
        origin: origin(),
    };
    // the closure body: `print(norm(&p))`; `p` is `(*env.0)` for ByRef and `env.0` for Kept
    let p_place = if kept {
        Place { local: LocalId(1), proj: vec![Proj::Field(FieldIdx(0))] }
    } else {
        Place { local: LocalId(1), proj: vec![Proj::Field(FieldIdx(0)), Proj::Deref(DerefKind::Ref)] }
    };
    let clo = Body {
        kind: BodyKind::Closure(ClosureId(0)),
        parent: Some(BodyId(0)),
        locals: vec![
            local(LocalKind::Return, None),
            local(LocalKind::Env, None),
            local(LocalKind::Temp(TempKind::Operand), None),
            local(LocalKind::Temp(TempKind::Operand), None),
        ],
        ret: LocalId(0),
        params: vec![LocalId(1)],
        caps: vec![],
        kont: None,
        blocks: vec![
            blk(
                vec![Live(LocalId(2)), Assign(pl(2), Rvalue::Ref(p_place)), Live(LocalId(3))],
                TermKind::Call {
                    callee: Callee::Fn(FnId(1), vec![]),
                    args: vec![Operand::Move(pl(2))],
                    dest: pl(3),
                    caps: CapArgs::Lexical(CapEnvId(0)),
                    next: Some(BlockId(1)),
                    unwind: None,
                },
                false,
            ),
            blk(
                vec![
                    Print(vec![Operand::Copy(pl(3))]),
                    Dead(LocalId(3)),
                    Dead(LocalId(2)),
                    Assign(pl(0), Rvalue::Use(Operand::Const(Const::Unit))),
                ],
                TermKind::Return,
                false,
            ),
            blk(vec![], TermKind::UnwindExit, true),
        ],
        entry: BlockId(0),
        unwind_exit: BlockId(2),
        cap_env: CapEnvId(0),
        origin: origin(),
    };
    Program {
        bodies: vec![make, clo],
        fns: vec![],
        closures: vec![ClosureDecl {
            body: BodyId(1),
            maker: BodyId(0),
            captures: vec![Capture { source: LocalId(2), mode }],
            once: false,
            cap_env: CapEnvId(0),
        }],
        handlers: vec![],
        scopes: vec![],
        spawns: vec![],
        cap_envs: vec![CapEnv { parent: None, adds: vec![] }],
    }
}

fn place_text(p: &Place) -> String {
    let mut t = format!("_{}", p.local.0);
    for pr in &p.proj {
        t = match pr {
            Proj::Deref(_) => format!("(*{t})"),
            Proj::Field(f) => format!("{t}.{}", f.0),
            Proj::Variant(v) => format!("({t} as #{})", v.0),
            Proj::Index(i) => format!("{t}[_{}]", i.0),
            Proj::Elems => format!("{t}[]"),
            Proj::Split(s, side) => format!("{t}[{side:?} of split {}]", s.0),
        };
    }
    t
}

fn op_text(o: &Operand) -> String {
    match o {
        Operand::Copy(p) => format!("copy {}", place_text(p)),
        Operand::Move(p) => format!("move {}", place_text(p)),
        Operand::Const(c) => format!("const {c:?}"),
    }
}

fn rv_text(r: &Rvalue) -> String {
    match r {
        Rvalue::Use(o) => op_text(o),
        Rvalue::Ref(p) => format!("&{}", place_text(p)),
        Rvalue::Aggregate(k, ops) => {
            let a: Vec<String> = ops.iter().map(op_text).collect();
            format!("{k:?}({})", a.join(", "))
        }
        other => format!("{other:?}"),
    }
}

/// Prints a body in the text form of the design.
pub fn print(name: &str, b: &Body) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "body {name} ({:?})", b.kind);
    for (i, l) in b.locals.iter().enumerate() {
        let _ = writeln!(out, "    let _{i}: {:?}{}", l.kind, l.name.as_ref().map(|n| format!(" `{n}`")).unwrap_or_default());
    }
    for (i, blk) in b.blocks.iter().enumerate() {
        let tag = if blk.cleanup { " (cleanup)" } else { "" };
        let _ = writeln!(out, "  bb{i}{tag}:");
        for st in &blk.stmts {
            let t = match &st.kind {
                StmtKind::Live(l) => format!("Live(_{})", l.0),
                StmtKind::Dead(l) => format!("Dead(_{})", l.0),
                StmtKind::Assign(p, r) => format!("{} = {}", place_text(p), rv_text(r)),
                StmtKind::Drop(p) => format!("Drop({})", place_text(p)),
                StmtKind::Bounds(p, o) => format!("Bounds({}, {})", place_text(p), op_text(o)),
                StmtKind::Print(ops) => format!("Print({})", ops.iter().map(op_text).collect::<Vec<_>>().join(", ")),
                StmtKind::UnwindValue(p, a) => format!("UnwindValue({}, {a:?})", place_text(p)),
                StmtKind::UnwindKont(l) => format!("UnwindKont(_{})", l.0),
                other => format!("{other:?}"),
            };
            let _ = writeln!(out, "    {t}");
        }
        let t = match &blk.term.kind {
            TermKind::Call { callee, args, dest, next, unwind, .. } => format!(
                "{} = call {:?}({}) -> [next: {:?}, unwind: {:?}]",
                place_text(dest),
                callee,
                args.iter().map(op_text).collect::<Vec<_>>().join(", "),
                next.map(|b| b.0),
                unwind.map(|b| b.0)
            ),
            TermKind::Perform { cap, op, args, dest, next, unwind } => format!(
                "{} = perform {:?}.{}({}) -> [next: bb{}, unwind: {:?}]",
                place_text(dest),
                cap,
                op.0,
                args.iter().map(op_text).collect::<Vec<_>>().join(", "),
                next.0,
                unwind.map(|b| b.0)
            ),
            TermKind::Handle { handler, dest, next, unwind } => format!(
                "{} = handle h{} -> [next: bb{}, unwind: {:?}]",
                place_text(dest),
                handler.0,
                next.0,
                unwind.map(|b| b.0)
            ),
            other => format!("{other:?}"),
        };
        let _ = writeln!(out, "    {t}");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::{verify, verify_program, Broken};

    #[test]
    fn the_example_verifies() {
        let broken = verify_program(&m3_program());
        assert!(broken.is_empty(), "{broken:?}");
    }

    #[test]
    fn a_missing_dead_is_found() {
        let mut b = handled_body();
        // Remove `Dead(_5)` from the normal path: the cell of the tail temporary
        // leaks at the `Return`.
        b.blocks[3].stmts.remove(1);
        let broken = verify(&b);
        assert!(broken.contains(&Broken::LeakedCell(BlockId(3), LocalId(5))), "{broken:?}");
    }

    #[test]
    fn a_parameter_that_does_not_end_is_found() {
        // V6: by-value parameters end before `Return` too (W0204 of a returned
        // reference into a parameter needs their end).
        let mut b = clause_body();
        b.blocks[0].stmts.pop();
        let broken = verify(&b);
        assert!(broken.contains(&Broken::LeakedCell(BlockId(0), LocalId(1))), "{broken:?}");
    }

    #[test]
    fn a_normal_edge_into_cleanup_is_found() {
        let mut b = main_body();
        b.blocks[1].term.kind = TermKind::Goto(BlockId(2));
        let broken = verify(&b);
        assert!(broken.contains(&Broken::CleanupEdge(BlockId(1), BlockId(2))), "{broken:?}");
    }

    #[test]
    fn the_continuation_goes_first_in_a_clause_chain() {
        let mut p = m3_program();
        // make the clause abort: an `assert` with the cleanup chain of bb1
        let clause = &mut p.bodies[2];
        clause.blocks[0].term.kind = TermKind::Assert {
            cond: Operand::Const(Const::Bool(true)),
            next: BlockId(3),
            unwind: Some(BlockId(1)),
        };
        // the frame end moves after the `assert`
        clause.blocks[0].stmts.truncate(5);
        clause.blocks.push(blk(vec![StmtKind::Dead(LocalId(2)), StmtKind::Dead(LocalId(1))], TermKind::Return, false));
        assert!(verify_program(&p).is_empty(), "{:?}", verify_program(&p));
        // a chain that does not start with `UnwindKont` breaks V16
        p.bodies[2].blocks[1].stmts.swap(0, 1);
        let broken = verify_program(&p);
        assert!(broken.iter().any(|b| matches!(b, Broken::KontNotFirst(..))), "{broken:?}");
    }

    #[test]
    fn a_row_capability_of_a_bound_effect_is_found() {
        let mut p = m3_program();
        if let TermKind::Perform { cap, .. } = &mut p.bodies[1].blocks[2].term.kind {
            *cap = CapOperand::Row(EffectId(0));
        }
        let broken = verify_program(&p);
        assert!(broken.iter().any(|b| matches!(b, Broken::BadCap(..))), "{broken:?}");
    }

    #[test]
    fn the_environment_of_a_closure_does_not_end_in_the_closure() {
        let mut p = j5d_program(false);
        p.bodies[1].blocks[1].stmts.push(s(StmtKind::Dead(LocalId(1))));
        let broken = verify_program(&p);
        assert!(broken.iter().any(|b| matches!(b, Broken::BadUpvar(..))), "{broken:?}");
    }

    #[test]
    fn rule_capture_rejects_a_borrowed_kept_cell() {
        assert!(verify_program(&j5d_program(false)).is_empty(), "{:?}", verify_program(&j5d_program(false)));
        let broken = verify_program(&j5d_program(true));
        assert!(broken.iter().any(|b| matches!(b, Broken::KeptBorrowed(..))), "{broken:?}");
    }

    #[test]
    fn print_example() {
        println!("{}", print("main", &main_body()));
        println!("{}", print("handled", &handled_body()));
        println!("{}", print("clause", &clause_body()));
    }
}
