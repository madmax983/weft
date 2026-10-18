//! # Vacuity guards
//!
//! * An accepted program and a full execution of it. The execution meets
//!   every hypothesis of the theorems, so the hypotheses are satisfiable.
//! * For each rule, a rejected program and a concrete execution that reaches
//!   the error the rule prevents. So each rule is necessary.
//! * A lexical example: a perform through the outer capability runs the
//!   outer clause, although an inner handler of the same effect is closer.

#![allow(non_snake_case)]

use vstd::prelude::*;
use crate::model::*;
use crate::checker::*;
use crate::scope::*;
use crate::lexical::*;
use crate::safety::*;

verus! {

// ---------------------------------------------------------------------------
// Program builder: main, one body, one clause, one effect with one operation
// ---------------------------------------------------------------------------

/// The effect `E`.
pub open spec fn E() -> EffId {
    0
}

/// The main block.
pub open spec fn MAIN() -> BlockId {
    0
}

/// The body block.
pub open spec fn BODY() -> BlockId {
    1
}

/// The clause block.
pub open spec fn CLAUSE() -> BlockId {
    2
}

/// `handle E { op => CLAUSE } in BODY`
pub open spec fn handle_E() -> Instr {
    Instr::Handle { eff: E(), clauses: seq![CLAUSE()], body: BODY() }
}

/// A program with one effect `E` (one operation of mode `m`), a main block,
/// a body block with capability `E` that returns `rets`, and a clause block.
pub open spec fn prog_of(
    m: Mode,
    main_code: Seq<Instr>,
    rets: Seq<nat>,
    body_code: Seq<Instr>,
    clause_code: Seq<Instr>,
) -> Prog {
    Prog {
        effs: map![E() => seq![m]],
        blocks: map![
            MAIN() => Block { sig: Sig { caps: seq![], rets: seq![], kmode: None }, code: main_code },
            BODY() => Block { sig: Sig { caps: seq![E()], rets, kmode: None }, code: body_code },
            CLAUSE() => Block { sig: Sig { caps: seq![], rets: seq![], kmode: Some(m) }, code: clause_code },
        ],
        main: MAIN(),
    }
}

// ---------------------------------------------------------------------------
// 1. The accepted program
// ---------------------------------------------------------------------------
//
//   main:   handle E { op => clause } in body ; return
//   body:   acquire x (on abort) ; perform E.op ; consume x ; return
//   clause: resume ; return

/// `handle E { op => clause } in body ; return`
pub open spec fn main_ok() -> Seq<Instr> {
    seq![handle_E(), Instr::Return]
}

/// `acquire x (on abort) ; perform E.op ; consume x ; return`
pub open spec fn body_ok() -> Seq<Instr> {
    seq![
        Instr::Acquire { slot: 0, on_abort: true },
        Instr::Perform { cap: 0, op: 0 },
        Instr::Consume { slot: 0 },
        Instr::Return,
    ]
}

/// `resume ; return`
pub open spec fn clause_ok_code() -> Seq<Instr> {
    seq![Instr::Resume, Instr::Return]
}

/// The accepted program.
pub open spec fn p_ok() -> Prog {
    prog_of(Mode::Once, main_ok(), seq![], body_ok(), clause_ok_code())
}

/// The checker accepts the program.
pub proof fn example_ok_checks()
    ensures
        check(p_ok()),
{
    let prog = p_ok();
    assert(prog.blocks.dom() =~= set![MAIN(), BODY(), CLAUSE()]);
    // main
    let ss_m0 = ss_at(prog, MAIN(), 0);
    let ss_m1 = ss_at(prog, MAIN(), 1);
    assert(ss_m0 == SS { env: seq![], lin: Map::empty(), k: false });
    assert(ss_m1 == post(prog, prog.blocks[MAIN()].sig, ss_m0, handle_E()));
    assert(handle_ret_effs(prog, seq![], E(), BODY()) =~= Seq::<EffId>::empty());
    assert(ss_m1.env =~= Seq::<EffId>::empty());
    assert(clause_sig_ok(prog, ss_m0.env, E(), seq![CLAUSE()]));
    assert(!any_mode(prog, ss_m0.env, Mode::Once));
    assert(!any_mode(prog, ss_m0.env, Mode::Multi));
    assert(instr_ok(prog, prog.blocks[MAIN()].sig, ss_m0, handle_E()));
    assert(block_ok(prog, MAIN()));
    // body
    let bsig = prog.blocks[BODY()].sig;
    let b0 = ss_at(prog, BODY(), 0);
    let b1 = ss_at(prog, BODY(), 1);
    let b2 = ss_at(prog, BODY(), 2);
    let b3 = ss_at(prog, BODY(), 3);
    assert(b0 == SS { env: seq![E()], lin: Map::empty(), k: false });
    assert(b1 == SS { env: seq![E()], lin: Map::<Slot, bool>::empty().insert(0, true), k: false });
    assert(b2 == b1);
    assert(b3.lin =~= Map::<Slot, bool>::empty());
    assert(instr_ok(prog, bsig, b1, Instr::Perform { cap: 0, op: 0 }));
    assert forall|pc: nat| pc < prog.blocks[BODY()].code.len() implies #[trigger] instr_ok(
        prog,
        bsig,
        ss_at(prog, BODY(), pc),
        prog.blocks[BODY()].code[pc as int],
    ) by {
        if pc == 0 {
        } else if pc == 1 {
        } else if pc == 2 {
        } else {
            assert(pc == 3);
        }
    }
    assert(block_ok(prog, BODY()));
    // clause
    let csig = prog.blocks[CLAUSE()].sig;
    let c0 = ss_at(prog, CLAUSE(), 0);
    let c1 = ss_at(prog, CLAUSE(), 1);
    assert(c0 == SS { env: seq![], lin: Map::empty(), k: true });
    assert(c1 == SS { env: seq![], lin: Map::empty(), k: false });
    assert(!any_mode(prog, c0.env, Mode::Once));
    assert(!any_mode(prog, c0.env, Mode::Multi));
    assert(instr_ok(prog, csig, c0, Instr::Resume));
    assert(block_ok(prog, CLAUSE()));
}

// ---------------------------------------------------------------------------
// 2. An execution of the accepted program
// ---------------------------------------------------------------------------

/// A code frame.
pub open spec fn cf(block: BlockId, pc: nat, env: Seq<HId>, slots: Map<Slot, ResId>, k: Option<KId>) -> Frame {
    Frame::Code(CFrame { block, pc, env, slots, k })
}

/// No linear values.
pub open spec fn no_slots() -> Map<Slot, ResId> {
    Map::empty()
}

/// Slot 0 holds resource 0.
pub open spec fn x_slots() -> Map<Slot, ResId> {
    Map::empty().insert(0, 0)
}

/// The handler instance that `handle_E` records in `main`.
pub open spec fn hi0() -> HInfo {
    HInfo { eff: E(), clauses: seq![CLAUSE()], env: seq![] }
}

/// The continuation that the perform in `body` captures.
pub open spec fn kont0(multi: bool, used: bool) -> Kont {
    Kont { frames: seq![Frame::Handler(0), cf(BODY(), 2, seq![0], x_slots(), None)], multi, used }
}

/// The initial state.
pub open spec fn s0() -> State {
    State {
        stack: seq![cf(MAIN(), 0, seq![], no_slots(), None)],
        pending: seq![],
        res: Map::empty(),
        konts: Map::empty(),
        hinfo: Map::empty(),
        next_res: 0,
        next_k: 0,
        next_h: 0,
    }
}

/// After `handle`.
pub open spec fn s1() -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![], no_slots(), None), Frame::Handler(0), cf(BODY(), 0, seq![0], no_slots(), None)],
        hinfo: Map::empty().insert(0, hi0()),
        next_h: 1,
        ..s0()
    }
}

/// After `acquire x` (with `on abort` flag `oa`).
pub open spec fn s2(oa: bool) -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![], no_slots(), None), Frame::Handler(0), cf(BODY(), 1, seq![0], x_slots(), None)],
        res: Map::empty().insert(0, Res { st: RState::Live, on_abort: oa }),
        next_res: 1,
        ..s1()
    }
}

/// After `perform`: the clause runs, the continuation is captured.
pub open spec fn s3(oa: bool, multi: bool) -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![], no_slots(), None), cf(CLAUSE(), 0, seq![], no_slots(), Some(0))],
        konts: Map::empty().insert(0, kont0(multi, false)),
        next_k: 1,
        ..s2(oa)
    }
}

/// After `resume` (once: the continuation is used).
pub open spec fn s4() -> State {
    State {
        stack: seq![
            cf(MAIN(), 1, seq![], no_slots(), None),
            cf(CLAUSE(), 1, seq![], no_slots(), Some(0)),
            Frame::Handler(0),
            cf(BODY(), 2, seq![0], x_slots(), None),
        ],
        konts: Map::empty().insert(0, kont0(false, true)),
        ..s3(true, false)
    }
}

/// After `consume x`.
pub open spec fn s5() -> State {
    State {
        stack: seq![
            cf(MAIN(), 1, seq![], no_slots(), None),
            cf(CLAUSE(), 1, seq![], no_slots(), Some(0)),
            Frame::Handler(0),
            cf(BODY(), 3, seq![0], no_slots(), None),
        ],
        res: Map::empty().insert(0, Res { st: RState::Consumed, on_abort: true }),
        ..s4()
    }
}

/// After the body returns.
pub open spec fn s6() -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![], no_slots(), None), cf(CLAUSE(), 1, seq![], no_slots(), Some(0)), Frame::Handler(0)],
        ..s5()
    }
}

/// After the handler frame is removed.
pub open spec fn s7() -> State {
    State { stack: seq![cf(MAIN(), 1, seq![], no_slots(), None), cf(CLAUSE(), 1, seq![], no_slots(), Some(0))], ..s6() }
}

/// After the clause returns.
pub open spec fn s8() -> State {
    State { stack: seq![cf(MAIN(), 1, seq![], no_slots(), None)], ..s7() }
}

/// After main returns: the program is done.
pub open spec fn s9() -> State {
    State { stack: seq![], ..s8() }
}

/// Steps 0 to 3 for any program of this shape whose body starts with
/// `acquire x; perform`.
pub proof fn lemma_steps_0_3(prog: Prog, m: Mode, main_code: Seq<Instr>, rets: Seq<nat>, body_code: Seq<Instr>, clause_code: Seq<Instr>, oa: bool)
    requires
        prog == prog_of(m, main_code, rets, body_code, clause_code),
        main_code.len() >= 2,
        main_code[0] == handle_E(),
        rets == Seq::<nat>::empty(),
        body_code.len() >= 3,
        body_code[0] == (Instr::Acquire { slot: 0, on_abort: oa }),
        body_code[1] == (Instr::Perform { cap: 0, op: 0 }),
        clause_code.len() >= 1,
    ensures
        init(prog) == s0(),
        step(prog, s0(), s1()),
        step(prog, s1(), s2(oa)),
        step(prog, s2(oa), s3(oa, m == Mode::Multi)),
{
    assert(init(prog) == s0());
    // handle
    let d1 = do_handle(prog, s0(), E(), seq![CLAUSE()], BODY());
    assert(handle_rets(prog, seq![0], BODY()) =~= Seq::<HId>::empty());
    assert(d1.stack =~= s1().stack);
    assert(d1.hinfo =~= s1().hinfo);
    assert(step_handle(prog, s0(), s1()));
    // acquire
    let d2 = do_acquire(s1(), 0, oa);
    assert(d2.stack =~= s2(oa).stack);
    assert(d2.res =~= s2(oa).res);
    assert(step_acquire(prog, s1(), s2(oa)));
    // perform
    let s = s2(oa);
    assert(is_handler(s.stack[1], 0));
    assert(on_stack(s.stack, 0));
    assert(topmost(s.stack, 0, 1));
    assert(perform_ok_dyn(prog, s, 0, 0, 1));
    let d3 = do_perform(prog, s, 0, 0, 1);
    assert(captured(s, 1) =~= kont0(m == Mode::Multi, false).frames);
    assert(clause_frame(s, 0, 0, 0) == CFrame { block: CLAUSE(), pc: 0, env: seq![], slots: no_slots(), k: Some(0) });
    assert(d3.stack =~= s3(oa, m == Mode::Multi).stack);
    assert(d3.konts =~= s3(oa, m == Mode::Multi).konts);
    assert(d3 == s3(oa, m == Mode::Multi));
    assert(tf(s).env[0] == 0);
    assert(instr_at(prog, tf(s)) == Instr::Perform { cap: 0, op: 0 });
    assert(at_instr(prog, s));
    assert(perform_ok_dyn(prog, s, 0, 0, 1) && s3(oa, m == Mode::Multi) == do_perform(prog, s, tf(s).env[0], 0, 1));
    let i = instr_at(prog, tf(s));
    assert(i->Perform_cap == 0 && i->Perform_op == 0);
    assert(exists|j: int| #[trigger] perform_ok_dyn(prog, s, i->Perform_cap, i->Perform_op, j) && s3(oa, m == Mode::Multi) == do_perform(prog, s, tf(s).env[i->Perform_cap as int], i->Perform_op, j));
    assert(step_perform(prog, s, s3(oa, m == Mode::Multi)));
}

/// Steps 3 to 7 when the clause starts with `resume` and the body continues
/// with `consume x; return`.
pub proof fn lemma_steps_3_7(prog: Prog, main_code: Seq<Instr>, clause_code: Seq<Instr>)
    requires
        prog == prog_of(Mode::Once, main_code, seq![], body_ok(), clause_code),
        clause_code.len() >= 2,
        clause_code[0] == Instr::Resume,
    ensures
        step(prog, s3(true, false), s4()),
        step(prog, s4(), s5()),
        step(prog, s5(), s6()),
        step(prog, s6(), s7()),
{
    let d4 = do_resume(s3(true, false));
    assert(d4.stack =~= s4().stack);
    assert(d4.konts =~= s4().konts);
    assert(step_resume(prog, s3(true, false), s4()));
    let d5 = do_consume(s4(), 0);
    assert(x_slots().remove(0) =~= no_slots());
    assert(d5.stack =~= s5().stack);
    assert(d5.res =~= s5().res);
    assert(step_consume(prog, s4(), s5()));
    assert(!nonempty(no_slots()));
    assert(s5().stack.drop_last() =~= s6().stack);
    assert(step_return(prog, s5(), s6()));
    assert(s6().stack.drop_last() =~= s7().stack);
    assert(step_pop(s6(), s7()));
}

/// The full execution of the accepted program.
pub open spec fn tr_ok() -> Seq<State> {
    seq![s0(), s1(), s2(true), s3(true, false), s4(), s5(), s6(), s7(), s8(), s9()]
}

/// The execution steps from the initial state to the end.
pub proof fn example_ok_trace()
    ensures
        is_trace(p_ok(), tr_ok()),
        tr_ok()[0] == init(p_ok()),
        final_state(tr_ok()[9]),
{
    let prog = p_ok();
    lemma_steps_0_3(prog, Mode::Once, main_ok(), seq![], body_ok(), clause_ok_code(), true);
    lemma_steps_3_7(prog, main_ok(), clause_ok_code());
    assert(!holds_fresh(s7(), tf(s7())));
    assert(s7().stack.drop_last() =~= s8().stack);
    assert(step_return(prog, s7(), s8()));
    assert(s8().stack.drop_last() =~= s9().stack);
    assert(step_return(prog, s8(), s9()));
    let tr = tr_ok();
    assert forall|i: int| 0 <= i < tr.len() - 1 implies step(prog, #[trigger] tr[i], tr[i + 1]) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {}
        else if i == 5 {} else if i == 6 {} else if i == 7 {} else {}
    }
}

/// **The hypotheses are satisfiable.** The accepted program and its
/// execution meet every hypothesis of E1-E5. The theorems then certify the
/// execution: it reaches the end, and the resource ends consumed.
pub proof fn example_hypotheses_satisfiable()
    ensures
        check(p_ok()),
        is_trace(p_ok(), tr_ok()),
        tr_ok()[0] == init(p_ok()),
        forall|i: int| 0 <= i < tr_ok().len() ==> !#[trigger] error(p_ok(), tr_ok()[i]),
        tr_ok()[9].res[0].st == RState::Consumed,
{
    example_ok_checks();
    example_ok_trace();
    soundness(p_ok(), tr_ok());
    e1_effect_safety(p_ok(), tr_ok());
    e2_one_shot_safety(p_ok(), tr_ok());
    e3_abort_safety(p_ok(), tr_ok());
    e4_lexical_resolution(p_ok(), tr_ok());
    e5_multi_shot_restriction(p_ok(), tr_ok());
    assert(tr_ok()[9].res.contains_key(0));
}

// ---------------------------------------------------------------------------
// 3. Rule (a) is necessary: a perform with no handler
// ---------------------------------------------------------------------------
//
//   main: perform E.op ; return        (no handle, no capability)

/// A program that performs with no handler.
pub open spec fn p_unhandled() -> Prog {
    prog_of(Mode::Once, seq![Instr::Perform { cap: 0, op: 0 }, Instr::Return], seq![], body_ok(), clause_ok_code())
}

/// The checker rejects it (rule a).
pub proof fn example_unhandled_rejected()
    ensures
        !check(p_unhandled()),
{
    let prog = p_unhandled();
    let ss = ss_at(prog, MAIN(), 0);
    assert(ss.env.len() == 0);
    assert(!instr_ok(prog, prog.blocks[MAIN()].sig, ss, prog.blocks[MAIN()].code[0]));
    assert(!block_ok(prog, MAIN()));
}

/// Without rule (a), the very first state is an unhandled perform.
pub proof fn example_unhandled_is_error()
    ensures
        is_trace(p_unhandled(), seq![init(p_unhandled())]),
        err_unhandled(p_unhandled(), init(p_unhandled())),
{
}

// ---------------------------------------------------------------------------
// 4. Rule (b) is necessary: a clause that resumes twice
// ---------------------------------------------------------------------------
//
//   clause: resume ; resume ; return

/// `resume ; resume ; return`
pub open spec fn clause_twice() -> Seq<Instr> {
    seq![Instr::Resume, Instr::Resume, Instr::Return]
}

/// A program whose clause resumes twice.
pub open spec fn p_twice() -> Prog {
    prog_of(Mode::Once, main_ok(), seq![], body_ok(), clause_twice())
}

/// The checker rejects it (rule b: `resume` consumes `k`).
pub proof fn example_twice_rejected()
    ensures
        !check(p_twice()),
{
    let prog = p_twice();
    let c1 = ss_at(prog, CLAUSE(), 1);
    assert(ss_at(prog, CLAUSE(), 0).k);
    assert(!c1.k);
    assert(!instr_ok(prog, prog.blocks[CLAUSE()].sig, c1, prog.blocks[CLAUSE()].code[1]));
    assert(!block_ok(prog, CLAUSE()));
}

/// Without rule (b), the second `resume` hits a used `once` continuation.
pub proof fn example_twice_is_error()
    ensures
        is_trace(p_twice(), seq![s0(), s1(), s2(true), s3(true, false), s4(), s5(), s6(), s7()]),
        init(p_twice()) == s0(),
        err_resume_used(p_twice(), s7()),
{
    let prog = p_twice();
    lemma_steps_0_3(prog, Mode::Once, main_ok(), seq![], body_ok(), clause_twice(), true);
    lemma_steps_3_7(prog, main_ok(), clause_twice());
    let tr = seq![s0(), s1(), s2(true), s3(true, false), s4(), s5(), s6(), s7()];
    assert forall|i: int| 0 <= i < tr.len() - 1 implies step(prog, #[trigger] tr[i], tr[i + 1]) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {}
        else if i == 5 {} else {}
    }
}

// ---------------------------------------------------------------------------
// 5. Rule (c) is necessary: a linear value without `on abort` live across a
//    perform whose clause drops the continuation
// ---------------------------------------------------------------------------
//
//   body:   acquire x (no on abort) ; perform E.op ; consume x ; return
//   clause: return                      (does not resume: abort)

/// `acquire x (no on abort) ; perform E.op ; consume x ; return`
pub open spec fn body_no_abort() -> Seq<Instr> {
    seq![
        Instr::Acquire { slot: 0, on_abort: false },
        Instr::Perform { cap: 0, op: 0 },
        Instr::Consume { slot: 0 },
        Instr::Return,
    ]
}

/// `return` (the clause does not resume).
pub open spec fn clause_drop() -> Seq<Instr> {
    seq![Instr::Return]
}

/// A program that aborts a value without `on abort`.
pub open spec fn p_no_abort() -> Prog {
    prog_of(Mode::Once, main_ok(), seq![], body_no_abort(), clause_drop())
}

/// The checker rejects it (rule c: the abort rule at the perform).
pub proof fn example_no_abort_rejected()
    ensures
        !check(p_no_abort()),
{
    let prog = p_no_abort();
    let b1 = ss_at(prog, BODY(), 1);
    assert(b1.lin.contains_key(0) && !b1.lin[0]);
    assert(!instr_ok(prog, prog.blocks[BODY()].sig, b1, prog.blocks[BODY()].code[1]));
    assert(!block_ok(prog, BODY()));
}

/// After the clause drops the continuation: the unwinder has the frames.
pub open spec fn s4_drop() -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![], no_slots(), None)],
        pending: kont0(false, false).frames,
        konts: Map::empty().insert(0, kont0(false, true)),
        ..s3(false, false)
    }
}

/// Without the abort rule, the unwinder must abort `x`, whose type has no `on abort`.
pub proof fn example_no_abort_is_error()
    ensures
        is_trace(p_no_abort(), seq![s0(), s1(), s2(false), s3(false, false), s4_drop()]),
        init(p_no_abort()) == s0(),
        err_no_on_abort(s4_drop()),
{
    let prog = p_no_abort();
    lemma_steps_0_3(prog, Mode::Once, main_ok(), seq![], body_no_abort(), clause_drop(), false);
    let s = s3(false, false);
    assert(holds_fresh(s, tf(s)));
    let d = do_return(s);
    assert(d.stack =~= s4_drop().stack);
    assert(d.pending =~= s4_drop().pending);
    assert(d.konts =~= s4_drop().konts);
    assert(!nonempty(no_slots()));
    assert(step_return(prog, s, s4_drop()));
    let tr = seq![s0(), s1(), s2(false), s3(false, false), s4_drop()];
    assert forall|i: int| 0 <= i < tr.len() - 1 implies step(prog, #[trigger] tr[i], tr[i + 1]) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else {}
    }
    let u = s4_drop();
    assert(max_slot(pf(u).slots, 0));
}

//   main: acquire x ; return           (x is never consumed)

/// A program that does not consume a linear value.
pub open spec fn p_leak() -> Prog {
    prog_of(Mode::Once, seq![Instr::Acquire { slot: 0, on_abort: true }, Instr::Return], seq![], body_ok(), clause_ok_code())
}

/// After `acquire x` in `main`.
pub open spec fn s_leak() -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![], x_slots(), None)],
        res: Map::empty().insert(0, Res { st: RState::Live, on_abort: true }),
        next_res: 1,
        ..s0()
    }
}

/// The checker rejects it (rule c: consume on every normal path).
pub proof fn example_leak_rejected()
    ensures
        !check(p_leak()),
{
    let prog = p_leak();
    let m1 = ss_at(prog, MAIN(), 1);
    assert(m1.lin.contains_key(0));
    assert(!instr_ok(prog, prog.blocks[MAIN()].sig, m1, prog.blocks[MAIN()].code[1]));
    assert(!block_ok(prog, MAIN()));
}

/// Without that rule, `main` returns with `x` live: a leak.
pub proof fn example_leak_is_error()
    ensures
        is_trace(p_leak(), seq![s0(), s_leak()]),
        init(p_leak()) == s0(),
        err_leak(p_leak(), s_leak()),
{
    let prog = p_leak();
    let d = do_acquire(s0(), 0, true);
    assert(d.stack =~= s_leak().stack);
    assert(d.res =~= s_leak().res);
    assert(step_acquire(prog, s0(), s_leak()));
    let tr = seq![s0(), s_leak()];
    assert forall|i: int| 0 <= i < tr.len() - 1 implies step(prog, #[trigger] tr[i], tr[i + 1]) by {}
    assert(x_slots().contains_key(0));
    assert(nonempty(x_slots()));
}

// ---------------------------------------------------------------------------
// 6. Rule (d) is necessary: a capability escapes its handle
// ---------------------------------------------------------------------------
//
//   main: handle E { op => clause } in body ; perform E.op ; return
//   body: return                        (returns a closure over its own capability)

/// `handle E { op => clause } in body ; perform E.op ; return`
pub open spec fn main_escape() -> Seq<Instr> {
    seq![handle_E(), Instr::Perform { cap: 0, op: 0 }, Instr::Return]
}

/// A program whose body returns its own capability.
pub open spec fn p_escape() -> Prog {
    prog_of(Mode::Once, main_escape(), seq![0], seq![Instr::Return], clause_ok_code())
}

/// The checker rejects it (rule d). Note that the perform in `main` itself
/// passes the checker: the escaped capability looks like a valid capability.
pub proof fn example_escape_rejected()
    ensures
        !check(p_escape()),
{
    let prog = p_escape();
    let m0 = ss_at(prog, MAIN(), 0);
    assert(m0.env.len() == 0);
    assert(prog.blocks[BODY()].sig.rets[0] == 0);
    assert(!instr_ok(prog, prog.blocks[MAIN()].sig, m0, prog.blocks[MAIN()].code[0]));
    assert(!block_ok(prog, MAIN()));
}

/// After `handle`: `main` already holds the escaped capability.
pub open spec fn t1() -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![0], no_slots(), None), Frame::Handler(0), cf(BODY(), 0, seq![0], no_slots(), None)],
        hinfo: Map::empty().insert(0, hi0()),
        next_h: 1,
        ..s0()
    }
}

/// After the body returns.
pub open spec fn t2() -> State {
    State { stack: seq![cf(MAIN(), 1, seq![0], no_slots(), None), Frame::Handler(0)], ..t1() }
}

/// After the handler frame is removed.
pub open spec fn t3() -> State {
    State { stack: seq![cf(MAIN(), 1, seq![0], no_slots(), None)], ..t2() }
}

/// Without rule (d), `main` performs through a capability whose handler is gone.
pub proof fn example_escape_is_error()
    ensures
        is_trace(p_escape(), seq![s0(), t1(), t2(), t3()]),
        init(p_escape()) == s0(),
        err_dead_cap(p_escape(), t3()),
        err_unhandled(p_escape(), t3()),
{
    let prog = p_escape();
    let d1 = do_handle(prog, s0(), E(), seq![CLAUSE()], BODY());
    assert(handle_rets(prog, seq![0], BODY()) =~= seq![0nat]);
    assert(d1.stack =~= t1().stack);
    assert(d1.hinfo =~= t1().hinfo);
    assert(step_handle(prog, s0(), t1()));
    assert(!nonempty(no_slots()));
    assert(t1().stack.drop_last() =~= t2().stack);
    assert(step_return(prog, t1(), t2()));
    assert(t2().stack.drop_last() =~= t3().stack);
    assert(step_pop(t2(), t3()));
    let tr = seq![s0(), t1(), t2(), t3()];
    assert forall|i: int| 0 <= i < tr.len() - 1 implies step(prog, #[trigger] tr[i], tr[i + 1]) by {
        if i == 0 {} else if i == 1 {} else {}
    }
    assert(!on_stack(t3().stack, 0));
}

// ---------------------------------------------------------------------------
// 7. The multi rule is necessary: a linear value live across a `multi` perform
// ---------------------------------------------------------------------------
//
//   E.op is multi.
//   body:   acquire x (on abort) ; perform E.op ; consume x ; return
//   clause: resume ; resume ; return

/// A program with a linear value live across a `multi` perform.
pub open spec fn p_multi_bad() -> Prog {
    prog_of(Mode::Multi, main_ok(), seq![], body_ok(), clause_twice())
}

/// The checker rejects it (multi rule at the perform). The clause itself is
/// fine: a `multi` continuation may resume twice.
pub proof fn example_multi_rejected()
    ensures
        !check(p_multi_bad()),
{
    let prog = p_multi_bad();
    let b1 = ss_at(prog, BODY(), 1);
    assert(b1.lin.contains_key(0));
    assert(!instr_ok(prog, prog.blocks[BODY()].sig, b1, prog.blocks[BODY()].code[1]));
    assert(!block_ok(prog, BODY()));
}

/// The stack while the clause (at `pc`) waits for a copy of the body (at `bpc`, with `slots`).
pub open spec fn u_stack(pc: nat, bpc: nat, slots: Map<Slot, ResId>) -> Seq<Frame> {
    seq![
        cf(MAIN(), 1, seq![], no_slots(), None),
        cf(CLAUSE(), pc, seq![], no_slots(), Some(0)),
        Frame::Handler(0),
        cf(BODY(), bpc, seq![0], slots, None),
    ]
}

/// After the first resume.
pub open spec fn u4() -> State {
    State { stack: u_stack(1, 2, x_slots()), ..s3(true, true) }
}

/// After the first copy of the body consumes `x`.
pub open spec fn u5() -> State {
    State {
        stack: u_stack(1, 3, no_slots()),
        res: Map::empty().insert(0, Res { st: RState::Consumed, on_abort: true }),
        ..u4()
    }
}

/// After the first copy of the body returns.
pub open spec fn u6() -> State {
    State { stack: u_stack(1, 3, no_slots()).drop_last(), ..u5() }
}

/// After the handler frame is removed.
pub open spec fn u7() -> State {
    State { stack: u_stack(1, 3, no_slots()).drop_last().drop_last(), ..u6() }
}

/// The second resume copies the body frame again, with `x` in its slot.
pub open spec fn u8() -> State {
    State { stack: u_stack(2, 2, x_slots()), ..u7() }
}

/// Without the multi rule, `x` is duplicated at the first resume (the stack
/// copy and the continuation both hold it), and the second copy of the body
/// consumes `x` again.
pub proof fn example_multi_is_error()
    ensures
        is_trace(p_multi_bad(), seq![s0(), s1(), s2(true), s3(true, true), u4(), u5(), u6(), u7(), u8()]),
        init(p_multi_bad()) == s0(),
        err_dup(u4()),
        err_consumed_twice(p_multi_bad(), u8()),
{
    let prog = p_multi_bad();
    lemma_steps_0_3(prog, Mode::Multi, main_ok(), seq![], body_ok(), clause_twice(), true);
    let d4 = do_resume(s3(true, true));
    assert(d4.stack =~= u4().stack);
    assert(step_resume(prog, s3(true, true), u4()));
    let d5 = do_consume(u4(), 0);
    assert(x_slots().remove(0) =~= no_slots());
    assert(d5.stack =~= u5().stack);
    assert(d5.res =~= u5().res);
    assert(step_consume(prog, u4(), u5()));
    assert(!nonempty(no_slots()));
    assert(step_return(prog, u5(), u6()));
    assert(step_pop(u6(), u7()));
    let d8 = do_resume(u7());
    assert(d8.stack =~= u8().stack);
    assert(step_resume(prog, u7(), u8()));
    let tr = seq![s0(), s1(), s2(true), s3(true, true), u4(), u5(), u6(), u7(), u8()];
    assert forall|i: int| 0 <= i < tr.len() - 1 implies step(prog, #[trigger] tr[i], tr[i + 1]) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {}
        else if i == 5 {} else if i == 6 {} else {}
    }
    assert(x_slots().contains_key(0));
    // after the first resume, the stack copy and the continuation both hold `x`
    assert(slot_at(u4(), Pos::Stk(3), 0, 0));
    assert(slot_at(u4(), Pos::Knt(0, 1), 0, 0));
}

// ---------------------------------------------------------------------------
// 8. Lexical resolution: two handlers of the same effect
// ---------------------------------------------------------------------------
//
//   main:  handle E { op => ca } in ba ; return
//   ba:    handle E { op => cb } in bb ; return       (ba has the outer capability)
//   bb:    perform outer.op ; return                  (bb has outer and inner)
//   ca:    return                                     (the outer clause aborts)
//   cb:    resume ; return
//
// The inner handler frame is closer on the stack, but the perform goes
// through the outer capability, so the outer clause `ca` runs.

/// The outer body.
pub open spec fn LBA() -> BlockId {
    1
}

/// The inner body.
pub open spec fn LBB() -> BlockId {
    2
}

/// The outer clause.
pub open spec fn LCA() -> BlockId {
    3
}

/// The inner clause.
pub open spec fn LCB() -> BlockId {
    4
}

/// The program with two handlers of the same effect.
pub open spec fn p_lex() -> Prog {
    Prog {
        effs: map![E() => seq![Mode::Once]],
        blocks: map![
            MAIN() => Block {
                sig: Sig { caps: seq![], rets: seq![], kmode: None },
                code: seq![Instr::Handle { eff: E(), clauses: seq![LCA()], body: LBA() }, Instr::Return],
            },
            LBA() => Block {
                sig: Sig { caps: seq![E()], rets: seq![], kmode: None },
                code: seq![Instr::Handle { eff: E(), clauses: seq![LCB()], body: LBB() }, Instr::Return],
            },
            LBB() => Block {
                sig: Sig { caps: seq![E(), E()], rets: seq![], kmode: None },
                code: seq![Instr::Perform { cap: 0, op: 0 }, Instr::Return],
            },
            LCA() => Block { sig: Sig { caps: seq![], rets: seq![], kmode: Some(Mode::Once) }, code: seq![Instr::Return] },
            LCB() => Block {
                sig: Sig { caps: seq![E()], rets: seq![], kmode: Some(Mode::Once) },
                code: seq![Instr::Resume, Instr::Return],
            },
        ],
        main: MAIN(),
    }
}

/// The checker accepts the program.
pub proof fn example_lex_checks()
    ensures
        check(p_lex()),
{
    let prog = p_lex();
    assert(prog.blocks.dom() =~= set![MAIN(), LBA(), LBB(), LCA(), LCB()]);
    assert(prog.effs[E()][0] == Mode::Once);
    assert(has_mode(prog, E(), Mode::Once));
    assert(!has_mode(prog, E(), Mode::Multi));
    // main
    let m0 = ss_at(prog, MAIN(), 0);
    assert(m0 == SS { env: seq![], lin: Map::empty(), k: false });
    assert(handle_ret_effs(prog, seq![], E(), LBA()) =~= Seq::<EffId>::empty());
    assert(ss_at(prog, MAIN(), 1).env =~= Seq::<EffId>::empty());
    assert(clause_sig_ok(prog, m0.env, E(), seq![LCA()]));
    assert(!any_mode(prog, m0.env, Mode::Once));
    assert(!any_mode(prog, m0.env, Mode::Multi));
    assert(instr_ok(prog, prog.blocks[MAIN()].sig, m0, prog.blocks[MAIN()].code[0]));
    assert(block_ok(prog, MAIN()));
    // ba
    let a0 = ss_at(prog, LBA(), 0);
    assert(a0 == SS { env: seq![E()], lin: Map::empty(), k: false });
    assert(handle_ret_effs(prog, seq![E()], E(), LBB()) =~= Seq::<EffId>::empty());
    assert(ss_at(prog, LBA(), 1).env =~= seq![E()]);
    assert(clause_sig_ok(prog, a0.env, E(), seq![LCB()]));
    assert(!any_mode(prog, a0.env, Mode::Multi));
    assert(post(prog, prog.blocks[LBA()].sig, a0, prog.blocks[LBA()].code[0]).lin == a0.lin);
    assert(all_abortable(post(prog, prog.blocks[LBA()].sig, a0, prog.blocks[LBA()].code[0])));
    assert(a0.env.push(E()) =~= seq![E(), E()]);
    assert(instr_ok(prog, prog.blocks[LBA()].sig, a0, prog.blocks[LBA()].code[0]));
    assert(block_ok(prog, LBA()));
    // bb
    let b0 = ss_at(prog, LBB(), 0);
    assert(b0 == SS { env: seq![E(), E()], lin: Map::empty(), k: false });
    assert(instr_ok(prog, prog.blocks[LBB()].sig, b0, prog.blocks[LBB()].code[0]));
    assert(block_ok(prog, LBB()));
    // ca
    assert(ss_at(prog, LCA(), 0).lin == Map::<Slot, bool>::empty());
    assert(block_ok(prog, LCA()));
    // cb
    let c0 = ss_at(prog, LCB(), 0);
    assert(c0 == SS { env: seq![E()], lin: Map::empty(), k: true });
    assert(!any_mode(prog, c0.env, Mode::Multi));
    assert(instr_ok(prog, prog.blocks[LCB()].sig, c0, Instr::Resume));
    assert(block_ok(prog, LCB()));
}

/// The outer handler instance.
pub open spec fn hi_outer() -> HInfo {
    HInfo { eff: E(), clauses: seq![LCA()], env: seq![] }
}

/// The inner handler instance.
pub open spec fn hi_inner() -> HInfo {
    HInfo { eff: E(), clauses: seq![LCB()], env: seq![0] }
}

/// The frames that the perform captures: up to the outer handler frame.
pub open spec fn lex_kont_frames() -> Seq<Frame> {
    seq![Frame::Handler(0), cf(LBA(), 1, seq![0], no_slots(), None), Frame::Handler(1), cf(LBB(), 1, seq![0, 1], no_slots(), None)]
}

/// The initial state.
pub open spec fn l0() -> State {
    s0()
}

/// After the outer `handle`.
pub open spec fn l1() -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![], no_slots(), None), Frame::Handler(0), cf(LBA(), 0, seq![0], no_slots(), None)],
        hinfo: Map::empty().insert(0, hi_outer()),
        next_h: 1,
        ..l0()
    }
}

/// After the inner `handle`.
pub open spec fn l2() -> State {
    State {
        stack: seq![
            cf(MAIN(), 1, seq![], no_slots(), None),
            Frame::Handler(0),
            cf(LBA(), 1, seq![0], no_slots(), None),
            Frame::Handler(1),
            cf(LBB(), 0, seq![0, 1], no_slots(), None),
        ],
        hinfo: Map::empty().insert(0, hi_outer()).insert(1, hi_inner()),
        next_h: 2,
        ..l1()
    }
}

/// After the perform through the outer capability.
pub open spec fn l3() -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![], no_slots(), None), cf(LCA(), 0, seq![], no_slots(), Some(0))],
        konts: Map::empty().insert(0, Kont { frames: lex_kont_frames(), multi: false, used: false }),
        next_k: 1,
        ..l2()
    }
}

/// The outer clause returns: it drops the continuation (abort).
pub open spec fn l4() -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![], no_slots(), None)],
        pending: lex_kont_frames(),
        konts: Map::empty().insert(0, Kont { frames: lex_kont_frames(), multi: false, used: true }),
        ..l3()
    }
}

/// The unwinder removes the pending frames one by one.
pub open spec fn l_unwind(n: nat) -> State {
    State { pending: lex_kont_frames().subrange(0, n as int), ..l4() }
}

/// The execution of the lexical example.
pub open spec fn tr_lex() -> Seq<State> {
    seq![l0(), l1(), l2(), l3(), l4(), l_unwind(3), l_unwind(2), l_unwind(1), l_unwind(0), State { stack: seq![], ..l_unwind(0) }]
}

/// **Lexical, not dynamic.** In this execution the inner handler frame (id 1)
/// is the closest handler frame when `bb` performs. The perform goes through
/// the outer capability (id 0), so the outer clause `ca` runs, with the
/// environment of the outer handle site. E4 certifies that this clause is
/// the one that the handle at step 0 bound. The program then aborts the
/// captured frames and ends.
pub proof fn example_lexical()
    ensures
        check(p_lex()),
        is_trace(p_lex(), tr_lex()),
        tr_lex()[0] == init(p_lex()),
        tr_lex()[2].stack[3] == Frame::Handler(1),
        topmost(tr_lex()[2].stack, 0, 1),
        tr_lex()[3].stack.last() == cf(LCA(), 0, seq![], no_slots(), Some(0)),
        resolves_to(p_lex(), tr_lex(), 2, 0),
        final_state(tr_lex()[9]),
{
    let prog = p_lex();
    example_lex_checks();
    assert(init(prog) == l0());
    // handle (outer)
    let d1 = do_handle(prog, l0(), E(), seq![LCA()], LBA());
    assert(handle_rets(prog, seq![0], LBA()) =~= Seq::<HId>::empty());
    assert(d1.stack =~= l1().stack);
    assert(d1.hinfo =~= l1().hinfo);
    assert(step_handle(prog, l0(), l1()));
    // handle (inner)
    let d2 = do_handle(prog, l1(), E(), seq![LCB()], LBB());
    assert(handle_rets(prog, seq![0, 1], LBB()) =~= Seq::<HId>::empty());
    assert(seq![0nat].push(1) =~= seq![0nat, 1]);
    assert(d2.stack =~= l2().stack);
    assert(d2.hinfo =~= l2().hinfo);
    assert(step_handle(prog, l1(), l2()));
    // perform through the outer capability
    let s = l2();
    assert(is_handler(s.stack[1], 0));
    assert(!is_handler(s.stack[3], 0));
    assert(on_stack(s.stack, 0));
    assert(topmost(s.stack, 0, 1));
    assert(perform_ok_dyn(prog, s, 0, 0, 1));
    let d3 = do_perform(prog, s, 0, 0, 1);
    assert(captured(s, 1) =~= lex_kont_frames());
    assert(d3.stack =~= l3().stack);
    assert(d3.konts =~= l3().konts);
    assert(d3 == l3());
    let i = instr_at(prog, tf(s));
    assert(i->Perform_cap == 0 && i->Perform_op == 0);
    assert(exists|j: int| #[trigger] perform_ok_dyn(prog, s, i->Perform_cap, i->Perform_op, j) && l3() == do_perform(prog, s, tf(s).env[i->Perform_cap as int], i->Perform_op, j));
    assert(step_perform(prog, l2(), l3()));
    // the outer clause returns: abort
    assert(holds_fresh(l3(), tf(l3())));
    let d4 = do_return(l3());
    assert(d4.stack =~= l4().stack);
    assert(d4.pending =~= l4().pending);
    assert(d4.konts =~= l4().konts);
    assert(!nonempty(no_slots()));
    assert(step_return(prog, l3(), l4()));
    // the unwinder
    assert(l4() == l_unwind(4)) by {
        assert(lex_kont_frames().subrange(0, 4) =~= lex_kont_frames());
    }
    assert forall|n: nat| 1 <= n <= 4 implies step(prog, #[trigger] l_unwind(n), l_unwind((n - 1) as nat)) by {
        let u = l_unwind(n);
        assert(u.pending.drop_last() =~= l_unwind((n - 1) as nat).pending);
        assert(u.pending.last() == lex_kont_frames()[n - 1]);
        if u.pending.last() is Code {
            assert(pf(u).k is None);
            assert(!nonempty(pf(u).slots));
        }
        assert(step_unwind_pop(u, l_unwind((n - 1) as nat)));
    }
    let l9 = State { stack: seq![], ..l_unwind(0) };
    assert(l_unwind(0).pending =~= Seq::<Frame>::empty());
    assert(l_unwind(0).stack.drop_last() =~= l9.stack);
    assert(!holds_fresh(l_unwind(0), tf(l_unwind(0))));
    assert(step_return(prog, l_unwind(0), l9));
    let tr = tr_lex();
    assert forall|k: int| 0 <= k < tr.len() - 1 implies step(prog, #[trigger] tr[k], tr[k + 1]) by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {
            assert(step(prog, l_unwind(4), l_unwind(3)));
        } else if k == 4 {
            assert(step(prog, l_unwind(3), l_unwind(2)));
        } else if k == 5 {
            assert(step(prog, l_unwind(2), l_unwind(1)));
        } else if k == 6 {
            assert(step(prog, l_unwind(1), l_unwind(0)));
        } else if k == 7 {
            assert(step(prog, l_unwind(1), l_unwind(0)));
        } else {}
    }
    assert(is_trace(prog, tr));
    // E4 on this execution
    e4_lexical_resolution(prog, tr);
    assert(step_perform(prog, tr[2], tr[3]));
    let m = choose|m: int| resolves_to(prog, tr, 2, m) && forall|m2: int|
        #[trigger] minted_at(prog, tr, m2, tf(tr[2]).env[instr_at(prog, tf(tr[2]))->Perform_cap as int]) ==> m2 == m;
    assert(minted_at(prog, tr, 0, 0)) by {
        assert(step_handle(prog, tr[0], tr[1]));
    }
    assert(m == 0);
}

// ---------------------------------------------------------------------------
// 9. An accepted `multi` program that resumes twice
// ---------------------------------------------------------------------------
//
//   E.op is multi.
//   body:   perform E.op ; return     (nothing linear is live across it)
//   clause: resume ; resume ; return

/// `perform E.op ; return`
pub open spec fn body_m() -> Seq<Instr> {
    seq![Instr::Perform { cap: 0, op: 0 }, Instr::Return]
}

/// The accepted `multi` program.
pub open spec fn p_multi_ok() -> Prog {
    prog_of(Mode::Multi, main_ok(), seq![], body_m(), clause_twice())
}

/// The checker accepts the program.
pub proof fn example_multi_ok_checks()
    ensures
        check(p_multi_ok()),
{
    let prog = p_multi_ok();
    assert(prog.blocks.dom() =~= set![MAIN(), BODY(), CLAUSE()]);
    let ss_m0 = ss_at(prog, MAIN(), 0);
    assert(ss_m0 == SS { env: seq![], lin: Map::empty(), k: false });
    assert(handle_ret_effs(prog, seq![], E(), BODY()) =~= Seq::<EffId>::empty());
    assert(ss_at(prog, MAIN(), 1).env =~= Seq::<EffId>::empty());
    assert(clause_sig_ok(prog, ss_m0.env, E(), seq![CLAUSE()]));
    assert(!any_mode(prog, ss_m0.env, Mode::Once));
    assert(!any_mode(prog, ss_m0.env, Mode::Multi));
    assert(instr_ok(prog, prog.blocks[MAIN()].sig, ss_m0, handle_E()));
    assert(block_ok(prog, MAIN()));
    let b0 = ss_at(prog, BODY(), 0);
    assert(b0 == SS { env: seq![E()], lin: Map::empty(), k: false });
    assert(instr_ok(prog, prog.blocks[BODY()].sig, b0, body_m()[0]));
    assert(block_ok(prog, BODY()));
    let csig = prog.blocks[CLAUSE()].sig;
    let c0 = ss_at(prog, CLAUSE(), 0);
    assert(c0 == SS { env: seq![], lin: Map::empty(), k: true });
    assert(ss_at(prog, CLAUSE(), 1) == c0);
    assert(ss_at(prog, CLAUSE(), 2) == c0);
    assert(!any_mode(prog, c0.env, Mode::Once));
    assert(!any_mode(prog, c0.env, Mode::Multi));
    assert(instr_ok(prog, csig, c0, Instr::Resume));
    assert(block_ok(prog, CLAUSE()));
}

/// The frames that the `multi` perform captures.
pub open spec fn mk_frames() -> Seq<Frame> {
    seq![Frame::Handler(0), cf(BODY(), 1, seq![0], no_slots(), None)]
}

/// The clause at `pc` with `n` more frames of the body copy on top
/// (`n` = 2: the handler frame and the body frame; 1: the handler frame; 0: none).
pub open spec fn v(pc: nat, n: nat) -> State {
    State {
        stack: seq![cf(MAIN(), 1, seq![], no_slots(), None), cf(CLAUSE(), pc, seq![], no_slots(), Some(0))] + mk_frames().subrange(
            0,
            n as int,
        ),
        konts: Map::empty().insert(0, Kont { frames: mk_frames(), multi: true, used: false }),
        next_k: 1,
        ..s1()
    }
}

/// The execution of the `multi` example.
pub open spec fn tr_multi() -> Seq<State> {
    seq![
        s0(), s1(), v(0, 0), v(1, 2), v(1, 1), v(1, 0), v(2, 2), v(2, 1), v(2, 0),
        State { stack: seq![cf(MAIN(), 1, seq![], no_slots(), None)], ..v(2, 0) },
        State { stack: seq![], ..v(2, 0) },
    ]
}

/// **E5 is not vacuous.** An accepted program resumes a `multi`
/// continuation twice. E5 certifies that each resume pushes frames that hold
/// nothing linear and no fresh `once` continuation.
pub proof fn example_multi_ok()
    ensures
        check(p_multi_ok()),
        is_trace(p_multi_ok(), tr_multi()),
        tr_multi()[0] == init(p_multi_ok()),
        step_resume(p_multi_ok(), tr_multi()[2], tr_multi()[3]),
        step_resume(p_multi_ok(), tr_multi()[5], tr_multi()[6]),
        tr_multi()[2].konts[0].multi,
        final_state(tr_multi()[10]),
{
    let prog = p_multi_ok();
    example_multi_ok_checks();
    assert(init(prog) == s0());
    let d1 = do_handle(prog, s0(), E(), seq![CLAUSE()], BODY());
    assert(handle_rets(prog, seq![0], BODY()) =~= Seq::<HId>::empty());
    assert(d1.stack =~= s1().stack);
    assert(d1.hinfo =~= s1().hinfo);
    assert(step_handle(prog, s0(), s1()));
    // perform
    let s = s1();
    assert(is_handler(s.stack[1], 0));
    assert(on_stack(s.stack, 0));
    assert(topmost(s.stack, 0, 1));
    assert(perform_ok_dyn(prog, s, 0, 0, 1));
    let d2 = do_perform(prog, s, 0, 0, 1);
    assert(captured(s, 1) =~= mk_frames());
    assert(d2.stack =~= v(0, 0).stack);
    assert(d2.konts =~= v(0, 0).konts);
    assert(d2 == v(0, 0));
    let i = instr_at(prog, tf(s));
    assert(i->Perform_cap == 0 && i->Perform_op == 0);
    assert(exists|j: int| #[trigger] perform_ok_dyn(prog, s, i->Perform_cap, i->Perform_op, j) && v(0, 0) == do_perform(prog, s, tf(s).env[i->Perform_cap as int], i->Perform_op, j));
    assert(step_perform(prog, s1(), v(0, 0)));
    // the two rounds: resume, body returns, handler frame removed
    assert(!nonempty(no_slots()));
    assert forall|pc: nat| pc == 0 || pc == 1 implies step(prog, #[trigger] v(pc, 0), v(pc + 1, 2)) && step(prog, v(pc + 1, 2), v(pc + 1, 1))
        && step(prog, v(pc + 1, 1), v(pc + 1, 0)) by {
        let d = do_resume(v(pc, 0));
        assert(d.stack =~= v(pc + 1, 2).stack);
        assert(d == v(pc + 1, 2));
        assert(step_resume(prog, v(pc, 0), v(pc + 1, 2)));
        assert(v(pc + 1, 2).stack.drop_last() =~= v(pc + 1, 1).stack);
        assert(step_return(prog, v(pc + 1, 2), v(pc + 1, 1)));
        assert(v(pc + 1, 1).stack.drop_last() =~= v(pc + 1, 0).stack);
        assert(step_pop(v(pc + 1, 1), v(pc + 1, 0)));
    }
    let w9 = State { stack: seq![cf(MAIN(), 1, seq![], no_slots(), None)], ..v(2, 0) };
    let w10 = State { stack: seq![], ..v(2, 0) };
    assert(v(2, 0).stack.drop_last() =~= w9.stack);
    assert(!holds_fresh(v(2, 0), tf(v(2, 0))));
    assert(step_return(prog, v(2, 0), w9));
    assert(w9.stack.drop_last() =~= w10.stack);
    assert(step_return(prog, w9, w10));
    let tr = tr_multi();
    assert forall|k: int| 0 <= k < tr.len() - 1 implies step(prog, #[trigger] tr[k], tr[k + 1]) by {
        if k == 0 {} else if k == 1 {} else if k == 2 {
            assert(step(prog, v(0, 0), v(1, 2)));
        } else if k == 3 {
            assert(step(prog, v(0, 0), v(1, 2)));
        } else if k == 4 {
            assert(step(prog, v(0, 0), v(1, 2)));
        } else if k == 5 {
            assert(step(prog, v(1, 0), v(2, 2)));
        } else if k == 6 {
            assert(step(prog, v(1, 0), v(2, 2)));
        } else if k == 7 {
            assert(step(prog, v(1, 0), v(2, 2)));
        } else {}
    }
    let d = do_resume(v(1, 0));
    assert(d.stack =~= v(2, 2).stack);
    assert(step_resume(prog, v(1, 0), v(2, 2)));
    let d0 = do_resume(v(0, 0));
    assert(d0.stack =~= v(1, 2).stack);
    assert(step_resume(prog, v(0, 0), v(1, 2)));
}

} // verus!
