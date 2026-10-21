//! Tests of the verifier (`docs/ir.md` 4). Each test of a rule changes a valid
//! program so that it breaks only that rule, and checks that the verifier gives
//! exactly one `Broken` value for it.

mod example;

use example::{
    blk, by_move_program, deref, j5d_program, j5d_tys, m3_program, m3_tys, opt_program, pl, s, Tys,
};
use weft_ir::verify::{verify_program, Broken, Rule};
use weft_ir::*;

/// Returns a broken-rule value.
fn br(rule: Rule, body: u32, block: Option<u32>, local: Option<u32>) -> Broken {
    Broken {
        rule,
        body: BodyId(body),
        block: block.map(BlockId),
        local: local.map(LocalId),
    }
}

/// Checks that the verifier gives exactly `want` for program `p`.
fn only(p: &Program, tys: &TyTable, want: Broken) {
    let got = verify_program(p, tys);
    assert_eq!(got, vec![want], "{got:#?}");
}

/// Returns the M3 program and its types.
fn m3() -> (Program, Tys) {
    let t = m3_tys();
    (m3_program(&t), t)
}

/// Returns the statement kinds of block `b` of body `body`.
fn stmts(p: &mut Program, body: usize, b: usize) -> &mut Vec<Stmt> {
    &mut p.bodies[body].blocks[b].stmts
}

#[test]
fn the_m3_program_verifies() {
    let (p, t) = m3();
    let broken = verify_program(&p, &t.table);
    assert!(broken.is_empty(), "{broken:#?}");
}

#[test]
fn the_j5d_program_with_by_ref_verifies() {
    let t = j5d_tys(true);
    let broken = verify_program(&j5d_program(&t, false), &t.table);
    assert!(broken.is_empty(), "{broken:#?}");
}

#[test]
fn the_by_move_program_of_a_once_closure_verifies() {
    let t = j5d_tys(false);
    let broken = verify_program(&by_move_program(&t, true), &t.table);
    assert!(broken.is_empty(), "{broken:#?}");
}

#[test]
fn a_variant_after_its_test_verifies() {
    let (p, t) = opt_program(1);
    let broken = verify_program(&p, &t);
    assert!(broken.is_empty(), "{broken:#?}");
}

#[test]
fn each_broken_value_names_its_rule() {
    let rules = [
        (Rule::NoBlock(BlockId(0)), 1),
        (Rule::CleanupEdge(BlockId(0)), 2),
        (Rule::CleanupTerm, 3),
        (Rule::NotLive, 4),
        (Rule::LiveTwice, 5),
        (Rule::LeakedCell, 6),
        (Rule::UnwindExit, 7),
        (Rule::BadProj(0), 8),
        (Rule::VariantUntested, 8),
        (Rule::CopyNotCopy, 9),
        (Rule::MoveOfCopy, 9),
        (Rule::MoveThroughRef, 9),
        (Rule::NoUnwind, 10),
        (Rule::BadCap, 11),
        (Rule::BadKont, 11),
        (Rule::TempLive, 12),
        (Rule::FrameEndOrder, 12),
        (Rule::KeptBorrowed, 13),
        (
            Rule::CaptureMode {
                stated: CaptureMode::Kept,
                rule: CaptureMode::ByRef,
            },
            13,
        ),
        (Rule::BadUpvar, 14),
        (Rule::EnvMove, 14),
        (Rule::NotOnceRun, 15),
        (Rule::BadKind, 15),
        (Rule::KontNotFirst, 16),
        (Rule::UnwindOrder, 16),
        (Rule::BadDrop, 17),
        (Rule::ReturnOrigin, 18),
    ];
    for (r, n) in rules {
        assert_eq!(r.number(), n, "{r:?}");
    }
    let b = br(Rule::LeakedCell, 1, Some(3), Some(5));
    assert_eq!(
        b.to_string(),
        "V6: body b1, bb3, _5: a local still has a cell at the end of the frame"
    );
}

// ---------------------------------------------------------------------------
// One test for each rule
// ---------------------------------------------------------------------------

#[test]
fn v1_a_successor_that_is_not_a_block() {
    let (mut p, t) = m3();
    p.bodies[0].blocks[1].term.kind = TermKind::Goto(BlockId(9));
    only(
        &p,
        &t.table,
        br(Rule::NoBlock(BlockId(9)), 0, Some(1), None),
    );
}

#[test]
fn v2_an_unwind_edge_into_a_normal_block() {
    let (mut p, t) = m3();
    if let TermKind::Handle { unwind, .. } = &mut p.bodies[0].blocks[0].term.kind {
        *unwind = Some(BlockId(1));
    }
    only(
        &p,
        &t.table,
        br(Rule::CleanupEdge(BlockId(1)), 0, Some(0), None),
    );
}

#[test]
fn v3_a_return_on_a_cleanup_path() {
    let (mut p, t) = m3();
    p.bodies[0].blocks[2].term.kind = TermKind::Return;
    only(&p, &t.table, br(Rule::CleanupTerm, 0, Some(2), None));
}

#[test]
fn v4_a_use_with_no_cell() {
    let (mut p, t) = m3();
    // `_3 = const 0usize` before `Live(_3)`
    stmts(&mut p, 2, 0).swap(0, 1);
    only(&p, &t.table, br(Rule::NotLive, 2, Some(0), Some(3)));
}

#[test]
fn v5_a_second_live() {
    let (mut p, t) = m3();
    stmts(&mut p, 1, 2).push(s(StmtKind::Live(LocalId(2))));
    only(&p, &t.table, br(Rule::LiveTwice, 1, Some(2), Some(2)));
}

#[test]
fn v6_a_missing_dead_of_a_temporary() {
    let (mut p, t) = m3();
    // Remove `Dead(_5)` from the normal path: the cell of the tail temporary
    // leaks at the `Return`.
    stmts(&mut p, 1, 3).remove(1);
    only(&p, &t.table, br(Rule::LeakedCell, 1, Some(3), Some(5)));
}

#[test]
fn v6_a_parameter_that_does_not_end() {
    // By-value parameters end before `Return` too (W0204 of a returned reference
    // into a parameter needs their end).
    let (mut p, t) = m3();
    stmts(&mut p, 2, 0).pop();
    only(&p, &t.table, br(Rule::LeakedCell, 2, Some(0), Some(1)));
}

#[test]
fn v7_unwind_exit_outside_the_unwind_exit_block() {
    let (mut p, t) = m3();
    let b = &mut p.bodies[1];
    b.blocks.push(blk(vec![], TermKind::UnwindExit, true));
    b.unwind_exit = BlockId(6);
    only(&p, &t.table, br(Rule::UnwindExit, 1, Some(5), None));
}

#[test]
fn v8_an_index_with_a_local_that_is_not_usize() {
    let (mut p, t) = m3();
    p.bodies[2].locals[3].ty = t.u64;
    only(&p, &t.table, br(Rule::BadProj(1), 2, Some(0), Some(1)));
}

#[test]
fn v8_a_field_of_a_type_with_no_fields() {
    let (mut p, t) = m3();
    stmts(&mut p, 2, 0)[2].kind = StmtKind::Bounds(
        deref(1, vec![Proj::Field(FieldIdx(0))]),
        Operand::Copy(pl(3)),
    );
    only(&p, &t.table, br(Rule::BadProj(1), 2, Some(0), Some(1)));
}

#[test]
fn v8_a_deref_of_a_value_that_is_not_a_pointer() {
    let (mut p, t) = m3();
    stmts(&mut p, 1, 2)[3].kind = StmtKind::Assign(pl(5), Rvalue::Ref(deref(2, vec![])));
    only(&p, &t.table, br(Rule::BadProj(0), 1, Some(2), Some(2)));
}

#[test]
fn v8_a_variant_with_no_test() {
    let (p, t) = opt_program(2);
    only(&p, &t, br(Rule::VariantUntested, 0, Some(2), Some(1)));
}

#[test]
fn v8_an_uninit_below_a_variant_needs_no_test() {
    // The place field path of a value built in place names a payload that no
    // test chose: `Uninit` reads nothing.
    let (mut p, t) = opt_program(1);
    let payload = Place {
        local: LocalId(1),
        proj: vec![Proj::Variant(VariantIdx(1)), Proj::Field(FieldIdx(0))],
    };
    p.bodies[0].blocks[2]
        .stmts
        .push(s(StmtKind::Uninit(payload.clone())));
    let broken = verify_program(&p, &t);
    assert!(broken.is_empty(), "{broken:#?}");
    // A `Mention` of the same place in the same block reads it.
    p.bodies[0].blocks[2]
        .stmts
        .push(s(StmtKind::Mention(payload)));
    only(&p, &t, br(Rule::VariantUntested, 0, Some(2), Some(1)));
}

#[test]
fn v9_a_copy_of_a_value_that_is_not_plain_data() {
    let (mut p, t) = m3();
    p.bodies[0].locals[1].props.copy = false;
    only(&p, &t.table, br(Rule::CopyNotCopy, 0, Some(1), Some(1)));
}

#[test]
fn v9_a_move_of_plain_data() {
    let (mut p, t) = m3();
    stmts(&mut p, 0, 1)[0].kind = StmtKind::Print(vec![Operand::Move(pl(1))]);
    only(&p, &t.table, br(Rule::MoveOfCopy, 0, Some(1), Some(1)));
}

#[test]
fn v9_a_move_through_a_reference() {
    let (mut p, t) = m3();
    stmts(&mut p, 2, 0).insert(0, s(StmtKind::Print(vec![Operand::Move(deref(1, vec![]))])));
    only(&p, &t.table, br(Rule::MoveThroughRef, 2, Some(0), Some(1)));
}

#[test]
fn v10_a_perform_with_no_unwind_block() {
    let (mut p, t) = m3();
    if let TermKind::Perform { unwind, .. } = &mut p.bodies[1].blocks[2].term.kind {
        *unwind = None;
    }
    only(&p, &t.table, br(Rule::NoUnwind, 1, Some(2), None));
}

#[test]
fn v10_a_call_of_a_function_with_a_body_needs_an_unwind_block() {
    let (mut p, t) = m3();
    p.fns[1].body = Some(BodyId(0));
    only(&p, &t.table, br(Rule::NoUnwind, 1, Some(0), None));
}

#[test]
fn v11_a_row_capability_of_a_bound_effect() {
    let (mut p, t) = m3();
    if let TermKind::Perform { cap, .. } = &mut p.bodies[1].blocks[2].term.kind {
        *cap = CapOperand::Row(t.pick);
    }
    only(&p, &t.table, br(Rule::BadCap, 1, Some(2), None));
}

#[test]
fn v11_a_capability_local_that_is_not_a_capability() {
    let (mut p, t) = m3();
    if let TermKind::Perform { cap, .. } = &mut p.bodies[1].blocks[2].term.kind {
        *cap = CapOperand::Local(pl(2));
    }
    only(&p, &t.table, br(Rule::BadCap, 1, Some(2), Some(2)));
}

#[test]
fn v11_a_resume_of_a_local_that_is_not_a_continuation() {
    let (mut p, t) = m3();
    let clause = &mut p.bodies[2];
    // `_0 = resume _1(copy _0)`: `_1` is the parameter, not the continuation.
    clause.blocks[0].stmts.truncate(5);
    clause.blocks[0].term.kind = TermKind::Resume {
        kont: pl(1),
        arg: Operand::Copy(pl(0)),
        dest: pl(0),
        next: BlockId(3),
        unwind: Some(BlockId(1)),
    };
    clause.blocks.push(blk(
        vec![StmtKind::Dead(LocalId(2)), StmtKind::Dead(LocalId(1))],
        TermKind::Return,
        false,
    ));
    only(&p, &t.table, br(Rule::BadKont, 2, Some(0), Some(1)));
}

#[test]
fn v12_a_temporary_with_two_lives() {
    let (mut p, t) = m3();
    let b = stmts(&mut p, 1, 2);
    b.insert(1, s(StmtKind::Live(LocalId(4))));
    b.insert(2, s(StmtKind::Dead(LocalId(4))));
    only(&p, &t.table, br(Rule::TempLive, 1, Some(2), Some(4)));
}

#[test]
fn v12_a_parameter_that_ends_before_a_temporary() {
    let (mut p, t) = m3();
    // the frame end: `Dead(_2); Dead(_1); Dead(_5)`: the capability ends before
    // the tail temporary
    stmts(&mut p, 1, 3).swap(1, 2);
    only(&p, &t.table, br(Rule::FrameEndOrder, 1, Some(3), Some(5)));
}

#[test]
fn v13_rule_capture_rejects_a_borrowed_kept_cell() {
    let t = j5d_tys(true);
    let broken = verify_program(&j5d_program(&t, true), &t.table);
    assert!(!broken.is_empty());
    assert!(broken.iter().all(|b| b.rule.number() == 13), "{broken:#?}");
    assert!(
        broken.contains(&br(Rule::KeptBorrowed, 1, Some(0), Some(1))),
        "{broken:#?}"
    );
    assert!(
        broken.contains(&br(
            Rule::CaptureMode {
                stated: CaptureMode::Kept,
                rule: CaptureMode::ByRef,
            },
            0,
            Some(0),
            Some(2)
        )),
        "{broken:#?}"
    );
}

#[test]
fn v13_a_by_ref_capture_that_rule_capture_keeps() {
    // The closure body only reads `p` (`copy (*env.0).0`): rule CAPTURE gives
    // `Kept`, not `ByRef`.
    let t = j5d_tys(true);
    let mut p = j5d_program(&t, false);
    let read = Place {
        local: LocalId(1),
        proj: vec![
            Proj::Field(FieldIdx(0)),
            Proj::Deref(DerefKind::Ref),
            Proj::Field(FieldIdx(0)),
        ],
    };
    let clo = &mut p.bodies[1];
    clo.locals[2].ty = t.u64;
    clo.blocks[0].stmts[1].kind = StmtKind::Assign(pl(2), Rvalue::Use(Operand::Copy(read)));
    clo.blocks[0].term.kind = TermKind::Goto(BlockId(1));
    clo.blocks[0].stmts.push(s(StmtKind::Assign(
        pl(3),
        Rvalue::Use(Operand::Copy(pl(2))),
    )));
    only(
        &p,
        &t.table,
        br(
            Rule::CaptureMode {
                stated: CaptureMode::ByRef,
                rule: CaptureMode::Kept,
            },
            0,
            Some(0),
            Some(2),
        ),
    );
}

#[test]
fn v14_the_environment_of_a_closure_does_not_end_in_the_closure() {
    let t = j5d_tys(true);
    let mut p = j5d_program(&t, false);
    stmts(&mut p, 1, 1).push(s(StmtKind::Dead(LocalId(1))));
    only(&p, &t.table, br(Rule::BadUpvar, 1, Some(1), Some(1)));
}

#[test]
fn v14_an_upvar_local_in_a_function_body() {
    let (mut p, t) = m3();
    let mut d = p.bodies[0].locals[1].clone();
    d.kind = LocalKind::Upvar(LocalId(0));
    p.bodies[0].locals.push(d);
    only(&p, &t.table, br(Rule::BadUpvar, 0, None, Some(2)));
}

#[test]
fn v14_a_move_below_the_environment_of_a_closure_that_is_not_once() {
    let t = j5d_tys(false);
    let p = by_move_program(&t, false);
    only(&p, &t.table, br(Rule::EnvMove, 1, Some(0), Some(1)));
}

#[test]
fn v15_a_clause_that_no_handler_names() {
    let (mut p, t) = m3();
    p.handlers[0].clauses.clear();
    only(&p, &t.table, br(Rule::NotOnceRun, 2, None, None));
}

#[test]
fn v15_a_handled_body_that_two_terminators_name() {
    let (mut p, t) = m3();
    // a second `handle h0` in `main`, on a path that never runs
    p.bodies[0].blocks.push(blk(
        vec![],
        TermKind::Handle {
            handler: HandlerId(0),
            dest: pl(1),
            next: BlockId(1),
            unwind: Some(BlockId(2)),
        },
        false,
    ));
    only(&p, &t.table, br(Rule::NotOnceRun, 1, None, None));
}

#[test]
fn v15_a_body_kind_that_its_declaration_does_not_name() {
    let (mut p, t) = m3();
    p.bodies[1].kind = BodyKind::Handled(HandlerId(0));
    p.bodies[2].kind = BodyKind::Clause(HandlerId(0), OpIdx(1));
    only(&p, &t.table, br(Rule::BadKind, 2, None, None));
}

/// The clause of M3 with an `assert` that can abort into the cleanup chain bb1.
fn clause_with_assert(p: &mut Program) {
    let clause = &mut p.bodies[2];
    clause.blocks[0].term.kind = TermKind::Assert {
        cond: Operand::Const(Const::Bool(true)),
        next: BlockId(3),
        unwind: Some(BlockId(1)),
    };
    // the frame end moves after the `assert`
    clause.blocks[0].stmts.truncate(5);
    clause.blocks.push(blk(
        vec![StmtKind::Dead(LocalId(2)), StmtKind::Dead(LocalId(1))],
        TermKind::Return,
        false,
    ));
}

#[test]
fn v16_the_continuation_goes_first_in_a_clause_chain() {
    let (mut p, t) = m3();
    clause_with_assert(&mut p);
    let broken = verify_program(&p, &t.table);
    assert!(broken.is_empty(), "{broken:#?}");
    // a chain that does not start with `UnwindKont` breaks V16
    let chain = stmts(&mut p, 2, 1);
    let dead_0 = chain.remove(2);
    chain.insert(0, dead_0);
    only(&p, &t.table, br(Rule::KontNotFirst, 2, Some(1), Some(2)));
}

#[test]
fn v16_a_temporary_after_a_local_in_a_cleanup_chain() {
    let (mut p, t) = m3();
    // `UnwindValue(_2); Dead(_2); Dead(_5); ..`: the temporary must go first
    let chain = stmts(&mut p, 1, 4);
    let dead_5 = chain.remove(0);
    chain.insert(2, dead_5);
    only(&p, &t.table, br(Rule::UnwindOrder, 1, Some(4), Some(5)));
}

#[test]
fn v16_a_return_slot_with_a_value_goes_first() {
    let (mut p, t) = m3();
    clause_with_assert(&mut p);
    // `_0` has its value at the `assert`, so `Dead(_0)` must come before the other
    // values; here it is last
    let chain = stmts(&mut p, 2, 1);
    let dead_0 = chain.remove(2);
    chain.push(dead_0);
    only(&p, &t.table, br(Rule::UnwindOrder, 2, Some(1), Some(0)));
}

#[test]
fn v17_a_drop_of_a_place_with_no_deref() {
    let (mut p, t) = m3();
    stmts(&mut p, 1, 1).insert(1, s(StmtKind::Drop(pl(3))));
    only(&p, &t.table, br(Rule::BadDrop, 1, Some(1), Some(3)));
}

#[test]
fn v18_a_return_with_the_origin_of_another_expression() {
    let (mut p, t) = m3();
    let at = |lo, hi| Origin {
        span: Span { unit: 0, lo, hi },
        expr: None,
    };
    let b = &mut p.bodies[0].blocks[1];
    b.stmts[1].origin = at(30, 35);
    b.term.origin = at(10, 20);
    only(&p, &t.table, br(Rule::ReturnOrigin, 0, Some(1), Some(0)));
    // the origin of the returned expression holds the write of `_0`
    p.bodies[0].blocks[1].term.origin = at(25, 40);
    let broken = verify_program(&p, &t.table);
    assert!(broken.is_empty(), "{broken:#?}");
}
