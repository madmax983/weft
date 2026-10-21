//! The order of the blocks (`weft_ir::order`, `docs/ir.md` 5.1.9): the builder
//! numbers the blocks of each body in reverse post-order before it prints or
//! verifies the body.

mod example;

use example::*;
use weft_ir::order::{renumber, reverse_post_order};
use weft_ir::*;

/// Returns `bb<i>`.
const fn b(i: u32) -> BlockId {
    BlockId(i)
}

/// A body with these blocks: entry `bb0`, unwind exit `exit`.
fn body(blocks: Vec<Block>, exit: u32) -> Body {
    let t = m3_tys();
    Body {
        kind: BodyKind::Fn(FnId(0)),
        parent: None,
        locals: vec![local(LocalKind::Return, None, t.unit, true)],
        ret: LocalId(0),
        params: vec![],
        caps: vec![],
        kont: None,
        blocks,
        entry: b(0),
        unwind_exit: b(exit),
        cap_env: CapEnvId(0),
        origin: origin(),
    }
}

/// A call of `f0` with a next block and an unwind block.
const fn call(next: u32, unwind: u32) -> TermKind {
    TermKind::Call {
        callee: Callee::Fn(FnId(0), vec![]),
        args: vec![],
        dest: pl(0),
        caps: CapArgs::Root,
        next: Some(b(next)),
        unwind: Some(b(unwind)),
    }
}

/// A switch on a constant: `1` goes to `then`, the other values to `other`.
fn switch(then: u32, other: u32) -> TermKind {
    TermKind::Switch {
        on: Operand::Const(Const::Bool(true)),
        arms: vec![(1, b(then))],
        otherwise: b(other),
    }
}

/// A marker statement: `Live(_l)` names block `l` of the old order.
fn mark(l: u32) -> Vec<StmtKind> {
    vec![StmtKind::Live(LocalId(l))]
}

/// Returns the old number of each block, in the new order (the marker).
fn marks(body: &Body) -> Vec<u32> {
    body.blocks
        .iter()
        .map(|blk| match blk.stmts.first().map(|s| &s.kind) {
            Some(StmtKind::Live(l)) => l.0,
            _ => u32::MAX,
        })
        .collect()
}

/// The blocks of an `if` with a call in the condition, as the builder makes them:
/// the join block and the cleanup blocks get low numbers.
fn if_body() -> Body {
    body(
        vec![
            // bb0: the condition calls f; next bb4, unwind bb2
            blk(mark(0), call(4, 2), false),
            // bb1: the join
            blk(mark(1), TermKind::Return, false),
            // bb2: the cleanup of the call
            blk(mark(2), TermKind::Goto(b(3)), true),
            // bb3: the unwind exit
            blk(mark(3), TermKind::UnwindExit, true),
            // bb4: the switch
            blk(mark(4), switch(5, 6), false),
            // bb5: then
            blk(mark(5), TermKind::Goto(b(1)), false),
            // bb6: else
            blk(mark(6), TermKind::Goto(b(1)), false),
            // bb7: dead code, no edge in
            blk(mark(7), TermKind::Goto(b(1)), false),
        ],
        3,
    )
}

#[test]
fn the_order_is_reverse_post_order_with_the_first_successor_first() {
    let order: Vec<u32> = reverse_post_order(&if_body()).iter().map(|x| x.0).collect();
    // The entry, the next block of the call, then the arms of the switch in
    // their order, the join, the cleanup blocks, and last the block that the
    // entry does not reach.
    assert_eq!(order, vec![0, 4, 5, 6, 1, 2, 3, 7]);
}

#[test]
fn renumber_moves_the_blocks_and_their_edges() {
    let mut body = if_body();
    renumber(&mut body);
    assert_eq!(marks(&body), vec![0, 4, 5, 6, 1, 2, 3, 7]);
    assert_eq!(body.entry, b(0));
    assert_eq!(body.unwind_exit, b(6));
    let terms: Vec<TermKind> = body.blocks.iter().map(|x| x.term.kind.clone()).collect();
    assert_eq!(
        terms,
        vec![
            call(1, 5),
            switch(2, 3),
            TermKind::Goto(b(4)),
            TermKind::Goto(b(4)),
            TermKind::Return,
            TermKind::Goto(b(6)),
            TermKind::UnwindExit,
            TermKind::Goto(b(4)),
        ]
    );
    let cleanup: Vec<bool> = body.blocks.iter().map(|x| x.cleanup).collect();
    assert_eq!(
        cleanup,
        vec![false, false, false, false, false, true, true, false]
    );
}

#[test]
fn a_loop_keeps_its_body_after_its_head_and_its_exit_after_the_body() {
    // bb0 -> bb3 (head); head: IterNext -> [next bb1, done bb2]; bb1 -> head;
    // bb2: Return; bb4: unwind exit.
    let iter = TermKind::IterNext {
        iter: pl(0),
        dest: pl(0),
        next: b(1),
        done: b(2),
    };
    let mut body = body(
        vec![
            blk(mark(0), TermKind::Goto(b(3)), false),
            blk(mark(1), TermKind::Goto(b(3)), false),
            blk(mark(2), TermKind::Return, false),
            blk(mark(3), iter, false),
            blk(mark(4), TermKind::UnwindExit, true),
        ],
        4,
    );
    renumber(&mut body);
    assert_eq!(marks(&body), vec![0, 3, 1, 2, 4]);
    assert_eq!(body.unwind_exit, b(4));
}

#[test]
fn renumber_keeps_a_valid_body_valid() {
    let tys = m3_tys();
    let mut p = m3_program(&tys);
    assert!(verify::verify_program(&p, &tys.table).is_empty());
    for body in &mut p.bodies {
        renumber(body);
    }
    let broken = verify::verify_program(&p, &tys.table);
    assert!(broken.is_empty(), "{broken:?}");
}

#[test]
fn renumber_twice_changes_nothing() {
    let mut once = if_body();
    renumber(&mut once);
    let mut twice = once.clone();
    renumber(&mut twice);
    assert_eq!(marks(&once), marks(&twice));
    let a: Vec<TermKind> = once.blocks.iter().map(|x| x.term.kind.clone()).collect();
    let c: Vec<TermKind> = twice.blocks.iter().map(|x| x.term.kind.clone()).collect();
    assert_eq!(a, c);
}
