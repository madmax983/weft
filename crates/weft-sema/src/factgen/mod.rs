//! The fact generator of the `ir` pipeline (`docs/ir.md` section 6).
//!
//! The fact generator reads the IR of a program and writes one [`FnFacts`]
//! for each function and each test, with the schema of `weft-facts`. During
//! the migration it runs next to the old lowering (plan §2.6, stage F1):
//!
//! - `run` builds the IR of the analysis, finds the construct groups of each
//!   body (`crate::irbuild::scope`) and decides the scope of the program. A
//!   program is in scope when each group that it uses is on
//!   ([`crate::Options::ir_groups`]) and the fact generator supports each one.
//!   Else the old pipeline checks the whole program, and [`Scope::fallback`]
//!   says why.
//! - For a program in scope, [`emit`] writes the facts. It starts from the
//!   facts of the declarations of each body (the name, the effect names, the
//!   flags of the driver). The `ir` pipeline then fills the exports of the
//!   interpreter from the IR (module `exports`), and keeps the diagnostics of
//!   `typeck` (`docs/ir.md` 2.4) and of the builder.
//!
//! Stage F4: [`emit`] writes the facts of the bodies with no call, no
//! `perform` and no `resume` (group A with no calls): the analysis
//! (`crate::analysis`) gives the states, and the templates ([`templates`])
//! write the facts of each node. Stage F5 adds the calls of the functions
//! whose summary comes from a signature ([`summaries`]), and the W0204 store
//! check ([`Input::diags`]). Stage F6 adds the summaries of the bodies: the
//! fixpoint of the call graph (`crate::analysis::callgraph`) runs the fact
//! generator on each function body, callees first, and [`emit`] keeps the
//! facts of its last round. It also adds a `perform` through the capability
//! of a caller (`crate::analysis::unknown`), and W0701 and W0706 from the
//! inferred signatures. Stage F7 adds the abort destinations of each node
//! ([`frames`]: no abort edge for a call that cannot abort, `assert` in the
//! summaries), the `on abort` function at an `UnwindValue`, and W0118 as a
//! query over the summaries ([`checks`]). A program with another construct gets
//! [`Unsupported`]: the old pipeline checks it. A test can give another emit
//! ([`crate::analyze_with_emit`]), and [`preview`] gives the facts of one
//! body.

pub mod alpha;
pub mod checks;
pub mod decls;
mod exports;
pub mod frames;
pub mod holders;
pub mod kernel;
pub mod nodes;
pub mod rels;
pub mod templates;
pub mod vars;

use std::fmt;

use weft_facts::{FnFacts, PlaceId};
use weft_syntax::diag::Diagnostic;

use crate::irbuild::scope::{self, Group, Groups};
use crate::irbuild::{self, Built, Outcome};
use crate::{Analysis, BodyFacts};

/// The fact generator does not support a group that the program uses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unsupported {
    /// The group.
    pub group: Group,
    /// Why, for the note of the fallback.
    pub reason: String,
}

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "the fact generator does not support group {}: {}",
            self.group, self.reason
        )
    }
}

/// What [`emit`] reads.
#[derive(Clone, Copy, Debug)]
pub struct Input<'a> {
    /// The analysis of the old lowering: the program, the signatures and
    /// the THIR tables.
    pub analysis: &'a Analysis,
    /// The IR.
    pub built: &'a Built,
    /// The scope of the program.
    pub scope: &'a Scope,
    /// The diagnostics of the fact generator: the W0204 store check
    /// (`docs/ir.md` 6.9), W0701 and W0706 of the effect inference
    /// (`docs/ir.md` 6.8).
    pub diags: &'a std::cell::RefCell<Vec<Diagnostic>>,
    /// The `EffectSig` of each function whose summary comes from its body
    /// (`crate::analysis::sig::to_effect_sig`).
    pub effects: &'a std::cell::RefCell<Vec<(crate::FnId, crate::program::EffectSig)>>,
    /// No root handler serves an effect (W0118).
    pub no_runtime: bool,
    /// W0118 from the summaries of the `on abort` functions
    /// ([`checks::on_abort_rows`]). An emit that leaves it `None` keeps the
    /// W0118 of the old inference.
    pub on_abort: &'a std::cell::RefCell<Option<Vec<Diagnostic>>>,
}

/// W0118 of the old inference, for an emit that does not give its own, and
/// the option that the check needs.
#[derive(Clone, Debug, Default)]
pub struct OnAbortRows {
    /// The diagnostics of the old inference.
    pub old: Vec<Diagnostic>,
    /// No root handler serves an effect.
    pub no_runtime: bool,
}

/// A fact generator.
///
/// It writes the facts of each body of the analysis into `facts`, one
/// [`FnFacts`] for each body, in the order of [`Analysis::bodies`]. Each one
/// has the facts of the declarations already.
pub type Emit = fn(&Input<'_>, &mut [FnFacts]) -> Result<(), Unsupported>;

/// The fact generator of the `ir` pipeline.
///
/// It writes the facts of each body with IR into the entry of the body in
/// `facts` ([`emit_body`]). A body with no IR keeps the facts of its
/// declarations.
///
/// # Errors
///
/// Returns [`Unsupported`] for the first body with a construct that the
/// fact generator does not support yet.
pub fn emit(input: &Input<'_>, facts: &mut [FnFacts]) -> Result<(), Unsupported> {
    let mut inf = crate::analysis::callgraph::infer(input.analysis, input.built, None);
    for (i, e) in input.built.entries.iter().enumerate() {
        let Outcome::Built(entry) = e.outcome else {
            continue;
        };
        let Some(f) = facts.get_mut(i) else {
            continue;
        };
        let ds = match inf.facts.remove(&i) {
            Some(Ok((done, ds))) => {
                *f = done;
                ds
            }
            Some(Err(u)) => return Err(u),
            None => emit_body(input.analysis, input.built, &inf.sums, i, entry, f)?,
        };
        input.diags.borrow_mut().extend(ds);
    }
    *input.on_abort.borrow_mut() = Some(checks::on_abort_rows(
        input.analysis,
        input.built,
        &inf.sums,
        input.no_runtime,
    ));
    let mut diags = input.diags.borrow_mut();
    diags.extend(inf.diags);
    for (f, e) in &inf.effects {
        diags.extend(w0701(input.analysis, *f, e));
    }
    input.effects.borrow_mut().extend(inf.effects);
    Ok(())
}

/// W0701 (`docs/ir.md` 6.8): a public function with no stated row whose
/// inferred row `e` changes a place or performs an effect. The effects of a
/// function parameter pass through with no syntax, so a row with only
/// pass-through parameters has nothing to state. The text is the text of
/// the old inference (`Lower::effect_text`).
fn w0701(a: &Analysis, f: crate::FnId, e: &crate::program::EffectSig) -> Option<Diagnostic> {
    use crate::effects;
    use weft_syntax::diag::Code;
    let prog = &a.program;
    let def = prog.fns.get(f.index())?;
    let declared = a.sigs.get(f.index()).is_some_and(|s| s.declared);
    let to_state = !e.muts.is_empty() || !e.named.is_empty();
    if !def.is_pub || declared || !to_state || def.decl.is_extern {
        return None;
    }
    let mut parts: Vec<String> = Vec::new();
    if !e.muts.is_empty() {
        let ps: Vec<&str> = e.muts.iter().map(|m| m.text.as_str()).collect();
        parts.push(format!("mut({})", ps.join(", ")));
    }
    parts.extend(
        e.named
            .iter()
            .map(|n| effects::written(prog, def.module, n).unwrap_or_else(|| n.clone())),
    );
    let mut d = Diagnostic::error(
        Code::W0701,
        format!(
            "public function `{}` must state its effects: `/ {}`",
            def.name,
            parts.join(", ")
        ),
        def.decl.name.span,
    );
    // An effect that this module cannot name shows its identity. The note
    // tells why.
    for n in &e.named {
        if !effects::is_std(n) && effects::written(prog, def.module, n).is_none() {
            let hidden = effects::seen(prog, def.module, n);
            d = d.note(effects::unnamed_note(n, hidden));
        }
    }
    d.unit = prog.mods.get(def.module.index()).map_or(0, |m| m.unit);
    Some(d)
}

/// The summary of each function of the IR that a call can run (`docs/ir.md`
/// 6.7): the fixpoint of `crate::analysis::callgraph`.
///
/// A function with a stated signature (also an extern function) gets the
/// summary of its signature (`crate::analysis::sig`), with the parts that
/// its body gives. A function with no stated signature gets the summary of
/// its body.
pub fn summaries(a: &Analysis, built: &Built) -> crate::analysis::Summaries {
    crate::analysis::callgraph::infer(a, built, None).sums
}

/// The facts of body `index` of the analysis from the `ir` pipeline: the
/// facts of its declarations and of its IR. A preview for a body of a
/// program that is not in scope (plan stage F4).
///
/// # Errors
///
/// Returns [`Unsupported`] if the body has no IR or a construct that the
/// fact generator does not support yet.
pub fn preview(a: &Analysis, built: &Built, index: usize) -> Result<FnFacts, Unsupported> {
    let unsupported = |reason: &str| Unsupported {
        group: Group::A,
        reason: reason.to_string(),
    };
    let entry = match built.entries.get(index).map(|e| &e.outcome) {
        Some(Outcome::Built(b)) => *b,
        _ => return Err(unsupported("the body has no IR")),
    };
    let old = a
        .bodies
        .get(index)
        .ok_or_else(|| unsupported("no such body"))?;
    let mut facts = seed(&old.facts);
    let sums = summaries(a, built);
    emit_body(a, built, &sums, index, entry, &mut facts)?;
    Ok(facts)
}

/// The group of a construct that the fact generator of stage F4 does not
/// support, from the text of the reason.
fn later_group(why: &str) -> Group {
    let has = |w: &str| why.contains(w);
    if has("loop") || has("iterator") {
        Group::B
    } else if has("closure") || has("function value") || has("environment") {
        Group::C
    } else if has("handler") || has("capabilit") || has("continuation") {
        Group::D
    } else if has("task") || has("scope") {
        Group::E
    } else if has("type parameter") {
        Group::F
    } else {
        Group::A
    }
}

/// The error of α as an [`Unsupported`] of the fact generator.
fn unsupported(e: &alpha::AlphaError) -> Unsupported {
    let reason = match e {
        alpha::AlphaError::Later(why) => (*why).to_string(),
        alpha::AlphaError::NeedsValue { local } => {
            format!("a dereference of `_{}` with no value", local.0)
        }
        alpha::AlphaError::BadPlace(why) => format!("a place that does not fit its type: {why}"),
    };
    Unsupported {
        group: later_group(&reason),
        reason,
    }
}

/// Checks that the fact generator supports each construct of the component
/// `comp`: function and test bodies, the statements, the terminators that
/// run no other body (stage F4), and the calls of the functions that have a
/// summary in `sums` (stage F5).
fn check_supported(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    sums: &crate::analysis::Summaries,
    comp: &[weft_ir::BodyId],
) -> Result<(), Unsupported> {
    use weft_ir::{BodyKind, Rvalue, StmtKind, TermKind};
    let no = |group: Group, reason: &str| {
        Err(Unsupported {
            group,
            reason: reason.to_string(),
        })
    };
    for &bid in comp {
        let Some(b) = p.bodies.get(bid.index()) else {
            continue;
        };
        match b.kind {
            BodyKind::Fn(_) | BodyKind::Test(_) => {}
            BodyKind::Closure(_) => return no(Group::C, "a closure (stage F11)"),
            BodyKind::Clause(..) | BodyKind::Handled(_) => {
                return no(Group::D, "a handler (stage F14)");
            }
            BodyKind::Scope(_) => return no(Group::E, "a task scope (stage F18)"),
        }
        if b.locals.iter().any(|d| tys.mentions_param(d.ty)) {
            return no(Group::F, "a type parameter (stage F20)");
        }
        // A back edge: an edge to a block that does not come later in
        // reverse post-order.
        let order = weft_ir::order::reverse_post_order(b);
        let mut rank = vec![usize::MAX; b.blocks.len()];
        for (i, x) in order.iter().enumerate() {
            if let Some(r) = rank.get_mut(x.index()) {
                *r = i;
            }
        }
        for (i, blk) in b.blocks.iter().enumerate() {
            let me = rank.get(i).copied().unwrap_or(usize::MAX);
            let back = blk
                .term
                .kind
                .successors()
                .iter()
                .any(|s| rank.get(s.index()).is_some_and(|&r| r <= me));
            if back {
                return no(Group::B, "a loop (widening, stage F10)");
            }
        }
        for blk in &b.blocks {
            for s in &blk.stmts {
                match &s.kind {
                    StmtKind::Assign(_, Rvalue::Aggregate(weft_ir::AggKind::Closure(_), _)) => {
                        return no(Group::C, "a closure (stage F11)");
                    }
                    StmtKind::Assign(_, Rvalue::Iter(_)) => {
                        return no(Group::B, "an iterator (stage F10)");
                    }
                    // The unwinder runs the `on abort` function: its summary
                    // applies at the node (stage F7).
                    StmtKind::UnwindValue(_, weft_ir::UnwindAction::OnAbort(f)) => {
                        if let Err(why) = sums.get(*f) {
                            return no(later_group(why), why);
                        }
                    }
                    StmtKind::UnwindKont(_) => return no(Group::D, "a continuation (stage F16)"),
                    _ => {}
                }
            }
            match &blk.term.kind {
                TermKind::Goto(_)
                | TermKind::Switch { .. }
                | TermKind::Return
                | TermKind::UnwindExit
                | TermKind::Unreachable
                | TermKind::Assert { .. }
                | TermKind::Perform {
                    cap: weft_ir::CapOperand::Row(_),
                    ..
                } => {}
                TermKind::Call {
                    callee: weft_ir::Callee::Fn(f, _),
                    ..
                } => {
                    if let Err(why) = sums.get(*f) {
                        return no(later_group(why), why);
                    }
                }
                TermKind::Call { .. } => {
                    return no(Group::C, "a call of a function value (stage F12)");
                }
                TermKind::Perform { .. } => {
                    return no(
                        Group::D,
                        "a perform through a capability of a handler (stage F14)",
                    );
                }
                TermKind::Resume { .. } => return no(Group::D, "a continuation (stage F16)"),
                TermKind::IterNext { .. } => return no(Group::B, "an iterator (stage F10)"),
                TermKind::Handle { .. } => return no(Group::D, "a handler (stage F14)"),
                _ => return no(Group::E, "a task (stage F18)"),
            }
        }
    }
    Ok(())
}

/// Writes the facts of the component of the function or test body `entry`
/// (body `index` of the analysis) into `facts`, which hold the facts of its
/// declarations (`docs/ir.md` 6.1 to 6.4).
///
/// The steps: the variables of the component; the nodes and their edges
/// (the abort destinations of `frames`); the entry node, where the
/// parameters bind; the relations of the declarations; the analysis of the
/// body; then for each block that the entry reaches, the template of each
/// statement and of the terminator with the state before it; the owners of
/// the roots of the locals and the `@ uniq` flags.
///
/// # Errors
///
/// Returns [`Unsupported`] for a construct that the fact generator does not
/// support yet: a call of a function with no summary, a `perform`, a
/// `resume`, a loop, and the constructs of the groups B to F. The result is
/// the diagnostics of the W0204 store check.
pub fn emit_body(
    a: &Analysis,
    built: &Built,
    sums: &crate::analysis::Summaries,
    index: usize,
    entry: weft_ir::BodyId,
    facts: &mut FnFacts,
) -> Result<Vec<Diagnostic>, Unsupported> {
    emit_component(a, built, sums, index, entry, facts).map(|(d, _)| d)
}

/// [`emit_body`], that also gives the roots of the component: the summary
/// of the body maps its fact places back to its interface
/// (`crate::analysis::summarize`).
///
/// # Errors
///
/// The errors of [`emit_body`].
pub fn emit_component(
    a: &Analysis,
    built: &Built,
    sums: &crate::analysis::Summaries,
    index: usize,
    entry: weft_ir::BodyId,
    facts: &mut FnFacts,
) -> Result<(Vec<Diagnostic>, alpha::Roots), Unsupported> {
    use std::collections::BTreeMap;
    let p = &built.program;
    let comp = component(built, entry);
    let mut tys = built.tys.clone();
    check_supported(p, &tys, sums, &comp)?;
    let body = p
        .bodies
        .get(entry.index())
        .ok_or_else(|| unsupported(&alpha::AlphaError::BadPlace("no body".to_string())))?;
    let vars = vars::Vars::build(p, &mut tys, facts, &comp);
    let mut roots = alpha::Roots::default();
    roots.set_field_places(&a.program);
    // The abort destinations of each node (`docs/ir.md` 6.5).
    let frames = frames::Frames::of_body(p, &tys, sums, entry);
    let mut table = nodes::NodeTable::default();
    table.add_body(p, entry, facts, &frames);
    // The entry node: the parameters bind there.
    let sp = weft_facts::Span {
        lo: body.origin.span.lo,
        hi: body.origin.span.hi,
    };
    let entry_node = facts.add_node(sp, "entry", String::new());
    if let Some(first) = table.first(entry, body.entry, nodes::NORMAL) {
        facts.cfg_edge.push((entry_node, first));
    }
    let sig = a
        .bodies
        .get(index)
        .and_then(|b| b.func)
        .and_then(|f| a.sigs.get(f.index()));
    let (params, ret_places) = match sig {
        Some(sig) => {
            let ps = decls::params(p, &mut tys, facts, &mut roots, entry, sig)
                .map_err(|e| unsupported(&e))?;
            decls::signature(p, &tys, facts, &mut roots, sig, &ps.bases);
            let rp = decls::ret_places(p, &tys, facts, &mut roots, entry, sig, &ps.bases);
            (ps.entry, rp)
        }
        None => (Vec::new(), None),
    };
    decls::tasks(p, &comp, facts);
    let init = decls::entry_state(p, entry, &params).map_err(|e| unsupported(&e))?;
    let states = {
        let mut cx = crate::analysis::Cx {
            p,
            tys: &mut tys,
            facts,
            roots: &mut roots,
            sums,
        };
        crate::analysis::run(&mut cx, entry, init).map_err(|e| unsupported(&e))?
    };
    let mut uniq: BTreeMap<weft_facts::VarId, bool> = BTreeMap::new();
    let mut holders = holders::Holders::new(vars.holder_parts());
    let stored = {
        let mut em = templates::Em {
            p,
            sema: &a.program,
            tys: &mut tys,
            facts,
            roots: &mut roots,
            vars: &vars,
            holders: &mut holders,
            body: entry,
            cleanup: false,
            ret_places: ret_places.as_deref(),
            uniq: &mut uniq,
            skip_s: None,
            sums,
            stored: Vec::new(),
            at: (weft_ir::BlockId(0), 0),
        };
        templates::entry(&mut em, entry_node, &params).map_err(|e| unsupported(&e))?;
        emit_blocks(&mut em, &table, &frames, &states, body).map_err(|e| unsupported(&e))?;
        em.stored
    };
    holders.finish(facts);
    let diags = stored_behind(p, &tys, facts, &roots, body, &stored);
    // Each local with a root owns it.
    let owners: Vec<(PlaceId, weft_facts::VarId)> = roots
        .local_roots()
        .filter_map(|(k, r)| vars.get(&vars::VarKey::S(k.0, k.1)).map(|v| (r, v)))
        .collect();
    facts.owner.extend(owners);
    for (i, v) in facts.vars.iter_mut().enumerate() {
        let id = weft_facts::VarId(u32::try_from(i).unwrap_or(u32::MAX));
        v.uniq = uniq.get(&id).copied().unwrap_or(false);
    }
    decls::std_effects(facts);
    facts.normalize();
    Ok((diags, roots))
}

/// The W0204 store check (`docs/ir.md` 6.9): a reference into a local, a
/// temporary or a by-value parameter that the body puts behind a reference
/// parameter or into an `rc` object. The local ends at the return, and the
/// caller keeps the reference. One diagnostic for each place that gets the
/// reference and each local, at the span of the node, as the old lowering
/// (`check_stored_behind`).
fn stored_behind(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    facts: &FnFacts,
    roots: &alpha::Roots,
    body: &weft_ir::Body,
    stored: &[templates::Stored],
) -> Vec<Diagnostic> {
    use weft_syntax::diag::Code;
    let mut out = Vec::new();
    let mut seen: Vec<(String, weft_facts::RootId)> = Vec::new();
    for st in stored {
        let Some(into_root) = facts.places.get(st.into.index()).map(|i| i.root) else {
            continue;
        };
        let into = match roots.role(into_root) {
            Some(alpha::Role::Param(b, i) | alpha::Role::Held(b, i)) => format!(
                "behind the parameter `{}`",
                crate::analysis::transfer::param_name(p, b, i)
            ),
            Some(alpha::Role::Group) => {
                let name = facts
                    .roots
                    .get(into_root.index())
                    .map_or_else(String::new, |r| r.name.clone());
                format!("into an `rc` object of type `{name}`")
            }
            _ => continue,
        };
        for &r in &st.refs {
            let Some(root) = facts.places.get(r.index()).map(|i| i.root) else {
                continue;
            };
            let Some(alpha::Role::Local(key)) = roots.role(root) else {
                continue;
            };
            if seen.contains(&(into.clone(), root)) {
                continue;
            }
            seen.push((into.clone(), root));
            let d = p
                .bodies
                .get(key.0.index())
                .and_then(|b| b.locals.get(key.1.index()));
            let name = d.map_or_else(String::new, |d| alpha::local_text(tys, d));
            let what = match d.map(|d| d.kind) {
                Some(weft_ir::LocalKind::Temp(_)) => "a temporary value".to_string(),
                Some(weft_ir::LocalKind::Param(_)) => {
                    format!("the by-value parameter `{name}`")
                }
                _ => format!("the local `{name}`"),
            };
            let shown = facts.place(r).display.clone();
            let msg = format!(
                "`{}` puts a reference into `{shown}` {into}: {what} goes out of scope at the return",
                facts.name
            );
            let span = weft_syntax::ast::Span {
                lo: st.span.lo,
                hi: st.span.hi,
            };
            let mut diag = Diagnostic::error(Code::W0204, msg, span);
            diag.unit = body.origin.span.unit as usize;
            out.push(diag);
        }
    }
    out
}

/// The templates of each block of `body` that the entry reaches, with the
/// states of the analysis: each statement, then the terminator. A cleanup
/// block has one copy for each abort destination that reaches it
/// (`frames`, `docs/ir.md` 6.5).
fn emit_blocks(
    em: &mut templates::Em<'_>,
    table: &nodes::NodeTable,
    frames: &frames::Frames,
    states: &crate::analysis::States,
    body: &weft_ir::Body,
) -> Result<(), alpha::AlphaError> {
    use nodes::NORMAL;
    let bid = em.body;
    for (bi, blk) in body.blocks.iter().enumerate() {
        let block = weft_ir::BlockId(u32::try_from(bi).unwrap_or(u32::MAX));
        let Some(start) = states.at(block) else {
            continue;
        };
        // A cleanup block: each copy that the node table made.
        let copies = if blk.cleanup {
            table.copies(bid, block)
        } else {
            vec![NORMAL]
        };
        for dest in copies {
            emit_block(em, table, frames, start, body, block, dest)?;
        }
    }
    em.cleanup = false;
    em.skip_s = None;
    Ok(())
}

/// The templates of copy `dest` of block `block` of `body`, from the state
/// `start` of the analysis at its entry.
fn emit_block(
    em: &mut templates::Em<'_>,
    table: &nodes::NodeTable,
    frames: &frames::Frames,
    start: &crate::analysis::State,
    body: &weft_ir::Body,
    block: weft_ir::BlockId,
    dest: u32,
) -> Result<(), alpha::AlphaError> {
    use crate::analysis::transfer;
    use nodes::{NodeKey, Phase, NORMAL, TERM};
    let bid = em.body;
    let Some(blk) = body.blocks.get(block.index()) else {
        return Ok(());
    };
    em.cleanup = blk.cleanup;
    let mut st = start.clone();
    // The parts that the binds of the current pattern moved, by local.
    let mut run: Vec<(crate::analysis::Key, Vec<crate::analysis::PathStep>)> = Vec::new();
    for (si, s) in blk.stmts.iter().enumerate() {
        em.skip_s = None;
        match pattern_bind(em.p, bid, body, s)? {
            Bind::Part(k, path, moves) => {
                if run.iter().any(|(rk, _)| *rk == k) {
                    em.skip_s = Some(k);
                }
                if moves {
                    run.push((k, path));
                }
            }
            Bind::Keep => {}
            Bind::Other => run.clear(),
        }
        let at = u32::try_from(si).unwrap_or(u32::MAX);
        let key = NodeKey {
            body: bid,
            block,
            at,
            phase: Phase::Main,
            dest,
        };
        let pair = match &s.kind {
            weft_ir::StmtKind::Drop(_) => em.vars.get(&vars::VarKey::D(bid, block, at)),
            weft_ir::StmtKind::Assign(..) if si > 0 => {
                let prev = at - 1;
                match blk.stmts.get(si - 1).map(|x| &x.kind) {
                    Some(weft_ir::StmtKind::Drop(_)) => {
                        em.vars.get(&vars::VarKey::D(bid, block, prev))
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(n) = table.get(key) {
            em.at = (block, at);
            em.holders.before(n, &st);
            templates::stmt(em, n, &st, &s.kind, pair)?;
        }
        let mut cx = em_cx(em);
        transfer::stmt(&mut cx, bid, &mut st, &s.kind)?;
    }
    // The binds of a pattern end at the terminator.
    em.skip_s = None;
    let at = |phase, dest| NodeKey {
        body: bid,
        block,
        at: TERM,
        phase,
        dest,
    };
    let Some(n) = table.get(at(Phase::Main, dest)) else {
        return Ok(());
    };
    // The abort destinations of the terminator, and their `FrameEnd`
    // nodes (`docs/ir.md` 6.5).
    let dests = frames.dests(bid, block);
    let aborts: Vec<weft_facts::NodeId> = dests
        .iter()
        .filter_map(|d| table.get(at(Phase::FrameEnd, d.id())))
        .collect();
    // Each node of the terminator sees the state before it.
    let phases = [Phase::Main, Phase::Ret, Phase::FrameEnd];
    for m in phases
        .iter()
        .filter_map(|&ph| table.get(at(ph, dest)))
        .chain(aborts.iter().copied())
    {
        em.holders.before(m, &st);
    }
    match &blk.term.kind {
        weft_ir::TermKind::Call { .. } => {
            let nodes = templates::CallNodes {
                main: n,
                ret: table.get(at(Phase::Ret, NORMAL)),
                frame_end: table.get(at(Phase::FrameEnd, NORMAL)),
                aborts,
                may_abort: !dests.is_empty(),
            };
            templates::call(em, &nodes, &st, block, &blk.term.kind, blk.term.origin.span)
        }
        weft_ir::TermKind::Perform { .. } => {
            let nodes = templates::CallNodes {
                main: n,
                ret: table.get(at(Phase::Ret, NORMAL)),
                frame_end: None,
                aborts: Vec::new(),
                may_abort: !dests.is_empty(),
            };
            templates::perform(em, &nodes, &st, &blk.term.kind)
        }
        _ => templates::term(em, n, &st, &blk.term.kind, blk.term.origin.span),
    }
}

/// What a statement is for the binds of a pattern.
enum Bind {
    /// A bind of a pattern that reads the part `path` of a local: a move if
    /// the bool is true.
    Part(crate::analysis::Key, Vec<crate::analysis::PathStep>, bool),
    /// A statement that the binds of a pattern can have between them
    /// (`Live`, `Dead`, `Consume`).
    Keep,
    /// Another statement: the binds of the pattern end.
    Other,
}

/// What statement `s` of body `body` is for the binds of a pattern. A bind
/// of a pattern (`docs/ir.md` 5.13) gives a whole local the value of a part
/// (a move, a copy or a borrow) with the origin of the local itself: the
/// span of the name in the pattern.
fn pattern_bind(
    p: &weft_ir::Program,
    bid: weft_ir::BodyId,
    body: &weft_ir::Body,
    s: &weft_ir::Stmt,
) -> Result<Bind, alpha::AlphaError> {
    use weft_ir::{Operand, Rvalue, StmtKind};
    let (dest, q, moves) = match &s.kind {
        StmtKind::Live(_) | StmtKind::Dead(_) | StmtKind::Consume(_) => return Ok(Bind::Keep),
        StmtKind::Assign(dest, Rvalue::Use(Operand::Move(q))) => (dest, q, true),
        StmtKind::Assign(dest, Rvalue::Use(Operand::Copy(q)) | Rvalue::Ref(q)) => (dest, q, false),
        _ => return Ok(Bind::Other),
    };
    let named = body
        .locals
        .get(dest.local.index())
        .is_some_and(|d| d.origin.span == s.origin.span);
    if !dest.proj.is_empty() || q.proj.is_empty() || !named {
        return Ok(Bind::Other);
    }
    match crate::analysis::transfer::move_path(p, bid, q)? {
        Some((k, path)) => Ok(Bind::Part(k, path, moves)),
        None => Ok(Bind::Other),
    }
}

/// The context of the transfer functions for the emitter `em`.
const fn em_cx<'b>(em: &'b mut templates::Em<'_>) -> crate::analysis::Cx<'b> {
    crate::analysis::Cx {
        p: em.p,
        tys: em.tys,
        facts: em.facts,
        roots: em.roots,
        sums: em.sums,
    }
}

/// The scope of a program (plan §2.6).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Scope {
    /// The groups of each body, in the order of [`Analysis::bodies`]. A body
    /// with no IR uses no group.
    pub bodies: Vec<Groups>,
    /// The groups that the program uses: the union of [`Scope::bodies`].
    pub used: Groups,
    /// Why the old pipeline checks the program, or `None` if the program is
    /// in scope.
    pub fallback: Option<String>,
}

impl Scope {
    /// True if the `ir` pipeline checks the program.
    pub const fn in_scope(&self) -> bool {
        self.fallback.is_none()
    }
}

/// The result of the `ir` pipeline for a program in scope.
#[derive(Clone, Debug)]
pub struct IrFacts {
    /// The facts of each body, in the order of [`Analysis::bodies`].
    pub bodies: Vec<BodyFacts>,
    /// The diagnostics: those of `typeck` and of the item checks, those of
    /// the builder (W0315), and those of the fact generator and of its
    /// effect inference (W0204 stores, W0701, W0706).
    pub diags: Vec<Diagnostic>,
    /// The signatures, by [`crate::FnId`]: a function whose summary comes
    /// from its body has the `EffectSig` of its summary
    /// (`crate::analysis::sig::to_effect_sig`, `docs/ir.md` 6.8); the other
    /// functions keep the signature of the old inference.
    pub sigs: Vec<crate::FnSig>,
}

/// The text of a list of groups that are off: `group A`, or
/// `group A, group C and group D`.
fn off_text(off: Groups) -> String {
    let names: Vec<String> = off.iter().map(|g| format!("group {g}")).collect();
    match names.as_slice() {
        [] => String::new(),
        [one] => format!("the program uses {one}, which is off"),
        [rest @ .., last] => format!(
            "the program uses {} and {last}, which are off",
            rest.join(", ")
        ),
    }
}

/// Runs the `ir` pipeline on the analysis `a` of the old lowering, with the
/// groups `on` and the fact generator `emit`. `kept` holds the diagnostics of
/// the analysis that the `ir` pipeline keeps (`docs/ir.md` 2.4), and `rows`
/// the W0118 of the old inference: `emit` can replace them with its own
/// ([`Input::on_abort`]).
///
/// Returns the scope of the program and, if it is in scope, its facts and
/// diagnostics.
pub(crate) fn run(
    a: &Analysis,
    on: Groups,
    emit: Emit,
    kept: Vec<Diagnostic>,
    rows: OnAbortRows,
) -> (Scope, Option<IrFacts>) {
    let built = irbuild::build(a);
    let bodies = scope::groups(&built);
    let used = bodies.iter().fold(Groups::NONE, |g, b| g.union(*b));
    let mut s = Scope {
        bodies,
        used,
        fallback: None,
    };
    if let Some(e) = built.entries.iter().find_map(|e| match &e.outcome {
        Outcome::Unsupported(u) => Some((e, *u)),
        _ => None,
    }) {
        s.fallback = Some(format!(
            "the builder does not lower `{}`: {}",
            e.0.name,
            e.1.construct.name()
        ));
        return (s, None);
    }
    let off = used.minus(on);
    if !off.is_empty() {
        s.fallback = Some(off_text(off));
        return (s, None);
    }
    // With no group on (the default before stage F8), no program is in
    // scope: also a program whose bodies have no IR and use no group.
    if on.is_empty() {
        s.fallback = Some("no construct group is on".to_string());
        return (s, None);
    }
    let mut facts: Vec<FnFacts> = a.bodies.iter().map(|b| seed(&b.facts)).collect();
    let emitted = std::cell::RefCell::new(Vec::new());
    let effects = std::cell::RefCell::new(Vec::new());
    let on_abort = std::cell::RefCell::new(None);
    let input = Input {
        analysis: a,
        built: &built,
        scope: &s,
        diags: &emitted,
        effects: &effects,
        no_runtime: rows.no_runtime,
        on_abort: &on_abort,
    };
    if let Err(u) = emit(&input, &mut facts) {
        s.fallback = Some(u.to_string());
        return (s, None);
    }
    exports::fill(a, &built, &mut facts);
    let mut sigs = a.sigs.clone();
    for (f, e) in effects.into_inner() {
        if let Some(sig) = sigs.get_mut(f.index()) {
            sig.effects = e;
        }
    }
    let bodies = a
        .bodies
        .iter()
        .zip(facts)
        .map(|(b, facts)| BodyFacts {
            func: b.func,
            unit: b.unit,
            facts,
            effects: b
                .func
                .and_then(|f| sigs.get(f.index()))
                .map_or_else(|| b.effects.clone(), |s| s.effects.clone()),
        })
        .collect();
    let mut diags = kept;
    diags.extend(on_abort.into_inner().unwrap_or(rows.old));
    diags.extend(built.diags.iter().cloned());
    diags.extend(emitted.into_inner());
    (
        s,
        Some(IrFacts {
            bodies,
            diags,
            sigs,
        }),
    )
}

/// The bodies of the component of the function or test body `entry`.
///
/// They are in the order of their ids (`docs/ir.md` 6.1): the body and each
/// body inside it (closures, clauses, handled bodies, scope bodies). They share
/// the tables of one `FnFacts`.
pub fn component(built: &Built, entry: weft_ir::BodyId) -> Vec<weft_ir::BodyId> {
    let Some(e) = built
        .entries
        .iter()
        .position(|x| x.outcome == Outcome::Built(entry))
    else {
        return Vec::new();
    };
    scope::body_entries(built)
        .into_iter()
        .enumerate()
        .filter(|(_, x)| *x == Some(e))
        .map(|(i, _)| weft_ir::BodyId(u32::try_from(i).unwrap_or(u32::MAX)))
        .collect()
}

/// The facts of the declarations of a body, from the facts of the old
/// lowering: the name, the names of the effects, and the flags of the driver
/// (`library()`, `started()`, `no_runtime()`). They do not depend on the code
/// of the body.
pub(crate) fn seed(old: &FnFacts) -> FnFacts {
    FnFacts {
        name: old.name.clone(),
        effect_names: old.effect_names.clone(),
        hidden_effects: old.hidden_effects.clone(),
        library: old.library,
        started: old.started,
        no_runtime: old.no_runtime,
        ..FnFacts::default()
    }
}
