//! The cost of the verifier on large bodies (`docs/ir.md` 5.1.9): each pass is
//! close to linear in the blocks, so a large body does not take minutes or
//! gigabytes. Each test builds one large valid body, verifies it, and checks the
//! time against a large bound: a quadratic pass takes far more time, also in a
//! release build.

mod example;

use std::time::{Duration, Instant};

use example::{blk, local, m3_tys, origin, pl};
use weft_ir::verify::verify_program;
use weft_ir::*;

/// The time bound of each test. The tests take well under one second in a
/// debug build; a quadratic pass takes minutes.
const BOUND: Duration = Duration::from_secs(20);

/// A program with one body and one extern function `g() -> u64` that can abort.
fn program(locals: Vec<LocalDecl>, blocks: Vec<Block>, unwind_exit: usize) -> Program {
    let t = m3_tys();
    let body = Body {
        kind: BodyKind::Fn(FnId(0)),
        parent: None,
        locals,
        ret: LocalId(0),
        params: vec![],
        caps: vec![],
        kont: None,
        blocks,
        entry: BlockId(0),
        unwind_exit: BlockId(id(unwind_exit)),
        cap_env: CapEnvId(0),
        origin: origin(),
    };
    Program {
        bodies: vec![body],
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
                name: "g".to_string(),
                body: None,
                params: vec![],
                ret: t.u64,
                generics: 0,
                stated_row: None,
                intrinsic: None,
            },
        ],
        cap_envs: vec![CapEnv {
            parent: None,
            adds: vec![],
        }],
        ..Program::default()
    }
}

/// Returns `i` as an id.
fn id(i: usize) -> u32 {
    u32::try_from(i).unwrap_or(u32::MAX)
}

/// Verifies `p`, checks that it is valid, and returns the time.
fn verify_time(p: &Program) -> Duration {
    let t = m3_tys();
    let start = Instant::now();
    let broken = verify_program(p, &t.table);
    let time = start.elapsed();
    assert!(broken.is_empty(), "{:?}", &broken[..broken.len().min(5)]);
    time
}

/// A wide `match`: `n` tests in a line, and each failed test goes to the same
/// block. That block has `n` edges in, and each one comes from a deeper block of
/// the dominator tree.
#[test]
fn a_block_with_many_edges_in_verifies_in_time() {
    let n = 40_000;
    let t = m3_tys();
    let join = n;
    let mut blocks = Vec::with_capacity(n + 2);
    for i in 0..n {
        let next = if i + 1 < n { i + 1 } else { join };
        blocks.push(blk(
            vec![],
            TermKind::Switch {
                on: Operand::Const(Const::Bool(true)),
                arms: vec![(1, BlockId(id(next)))],
                otherwise: BlockId(id(join)),
            },
            false,
        ));
    }
    blocks.push(blk(vec![], TermKind::Return, false));
    blocks.push(blk(vec![], TermKind::UnwindExit, true));
    let p = program(
        vec![local(LocalKind::Return, None, t.unit, true)],
        blocks,
        n + 1,
    );
    let time = verify_time(&p);
    assert!(time < BOUND, "{n} edges into one block: {time:?}");
}

/// `n` locals that each get a value from a call that can abort. The cleanup
/// chain of each call ends the locals that have a cell, so the chains share
/// their suffixes. Each block has a cell for each local that the
/// verifier tracks.
#[test]
fn many_locals_over_many_blocks_verify_in_time() {
    let n = 20_000;
    let t = m3_tys();
    let mut locals = vec![local(LocalKind::Return, None, t.unit, true)];
    for i in 1..=n {
        locals.push(local(LocalKind::User, Some(&format!("x{i}")), t.u64, true));
    }
    // bb0..bb{n-1}: the calls; bb{n}: the end; bb{n+1}: `Dead(_0)`;
    // bb{n+1+i}: the cleanup node of `_i`; the last block: the unwind exit.
    let end = n;
    let ret_node = n + 1;
    let node = |i: usize| n + 1 + i;
    let exit = n + 2 + n;
    let mut blocks = Vec::with_capacity(exit + 1);
    for i in 1..=n {
        let next = if i < n { i } else { end };
        blocks.push(blk(
            vec![StmtKind::Live(LocalId(id(i)))],
            TermKind::Call {
                callee: Callee::Fn(FnId(1), vec![]),
                args: vec![],
                dest: pl(id(i)),
                caps: CapArgs::Lexical(CapEnvId(0)),
                next: Some(BlockId(id(next))),
                unwind: Some(BlockId(id(node(i)))),
            },
            false,
        ));
    }
    let mut stmts = vec![StmtKind::Assign(
        pl(0),
        Rvalue::Use(Operand::Const(Const::Unit)),
    )];
    stmts.extend((1..=n).rev().map(|i| StmtKind::Dead(LocalId(id(i)))));
    blocks.push(blk(stmts, TermKind::Return, false));
    blocks.push(blk(
        vec![StmtKind::Dead(LocalId(0))],
        TermKind::Goto(BlockId(id(exit))),
        true,
    ));
    for i in 1..=n {
        let down = if i > 1 { node(i - 1) } else { ret_node };
        blocks.push(blk(
            vec![StmtKind::Dead(LocalId(id(i)))],
            TermKind::Goto(BlockId(id(down))),
            true,
        ));
    }
    blocks.push(blk(vec![], TermKind::UnwindExit, true));
    let p = program(locals, blocks, exit);
    let time = verify_time(&p);
    assert!(time < BOUND, "{n} locals: {time:?}");
}
