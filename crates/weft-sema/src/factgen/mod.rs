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
//! query over the summaries ([`checks`]). Stage F11 adds the closures: each
//! closure body is a component of the facts of its function, with a summary
//! in the terms of its interface for the calls of the closure and facts that
//! are instantiated with the places of the maker (`docs/ir.md` 6.5, 6.7). A
//! program with another construct gets
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
    // A function with no row of the IR yet (stage F12): the row of the old
    // inference, which adds the effects of the closures that it makes.
    for &f in &inf.old_rows {
        if let Some(sig) = input.analysis.sigs.get(f.index()) {
            diags.extend(w0701(input.analysis, f, &sig.effects));
        }
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
    use weft_ir::{BodyKind, StmtKind, TermKind};
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
            // A closure body is a component of its own in the facts of its
            // function (stage F11).
            BodyKind::Fn(_) | BodyKind::Test(_) | BodyKind::Closure(_) => {}
            BodyKind::Clause(..) | BodyKind::Handled(_) => {
                return no(Group::D, "a handler (stage F14)");
            }
            BodyKind::Scope(_) => return no(Group::E, "a task scope (stage F18)"),
        }
        if b.locals.iter().any(|d| tys.mentions_param(d.ty)) {
            return no(Group::F, "a type parameter (stage F20)");
        }
        for blk in &b.blocks {
            for s in &blk.stmts {
                match &s.kind {
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
                | TermKind::IterNext { .. }
                // A call of a function value: the analysis finds the values
                // that it can be (stage F11), or the program is out of scope.
                | TermKind::Call {
                    callee: weft_ir::Callee::Value(_),
                    ..
                }
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
                TermKind::Perform { .. } => {
                    return no(
                        Group::D,
                        "a perform through a capability of a handler (stage F14)",
                    );
                }
                TermKind::Resume { .. } => return no(Group::D, "a continuation (stage F16)"),
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
    emit_parts(a, built, sums, index, entry, facts).map(|e| (e.diags, e.roots))
}

/// What [`emit_parts`] makes next to the facts of a component: the tables
/// that map the IR to the facts. The fact oracle of the interpreter
/// (`docs/ir.md` 8.5) reads them.
#[derive(Clone, Debug)]
pub struct Emitted {
    /// The diagnostics of the W0204 store check.
    pub diags: Vec<Diagnostic>,
    /// The roots of the component.
    pub roots: alpha::Roots,
    /// The node of each IR location.
    pub table: nodes::NodeTable,
    /// The variables of the component.
    pub vars: vars::Vars,
    /// The versions of each part with a variable of its own.
    pub parts: Vec<holders::PartVersions>,
    /// The versions of each heap slot.
    pub slots: Vec<holders::SlotVersions>,
    /// The entry node: the parameters bind there.
    pub entry_node: weft_facts::NodeId,
    /// The type table, with the types that the fact generator interned.
    pub tys: weft_ir::TyTable,
    /// The number of nodes of the component of the entry body: the nodes of
    /// the closure bodies come after them.
    pub entry_nodes: usize,
    /// The entry node of each closure body of the component.
    pub closure_entries: Vec<(weft_ir::BodyId, weft_facts::NodeId)>,
    /// The aborts (a failure, an `assert`) of the summaries that the entry
    /// body applies at its calls of function values.
    pub aborts: std::collections::BTreeSet<crate::analysis::summary::Abort>,
    /// The runs of the function values of the interface at the run nodes of
    /// the entry body, each with `many` (stage F12).
    pub runs: Vec<(crate::analysis::transfer::RunOf, bool)>,
    /// The state at each `Return` of the entry body.
    pub returns: Vec<crate::analysis::State>,
    /// A run node of the entry body runs code of a caller that can resume
    /// more than once.
    pub code_multi: bool,
    /// The `lends_mut` of the summaries that the entry body applies and that
    /// a caller does not apply again (`templates::Em::own_lends`).
    pub own_lends: Vec<(weft_facts::NodeId, PlaceId)>,
    /// The join of the states of the entry body before each terminator and
    /// each closure literal (with closures in the component).
    pub made: Option<crate::analysis::State>,
    /// The summary of each closure of the component: a caller of the
    /// function applies it to a closure that the function gives back.
    pub closures: Vec<(weft_ir::ClosureId, crate::analysis::Summary)>,
}

/// [`emit_component`], that gives all the tables of [`Emitted`].
///
/// # Errors
///
/// The errors of [`emit_body`].
pub fn emit_parts(
    a: &Analysis,
    built: &Built,
    sums: &crate::analysis::Summaries,
    index: usize,
    entry: weft_ir::BodyId,
    facts: &mut FnFacts,
) -> Result<Emitted, Unsupported> {
    use std::collections::BTreeMap;
    let p = &built.program;
    let comp = component(built, entry);
    let mut tys = built.tys.clone();
    check_supported(p, &tys, sums, &comp)?;
    let body = p
        .bodies
        .get(entry.index())
        .ok_or_else(|| unsupported(&alpha::AlphaError::BadPlace("no body".to_string())))?;
    // The summary of each closure of the component, in the terms of its
    // interface (`docs/ir.md` 6.7): an inner closure first, as a maker has a
    // lower id than its closures.
    let closures: Vec<weft_ir::BodyId> = comp
        .iter()
        .copied()
        .filter(|&b| p.closure_of(b).is_some())
        .collect();
    let with_closures;
    let sums: &crate::analysis::Summaries = if closures.is_empty() {
        sums
    } else {
        let mut all = sums.clone();
        for &cb in closures.iter().rev() {
            let s = closure_summary(a, built, &all, cb)?;
            if let Some((c, _)) = p.closure_of(cb) {
                all.insert_closure(c, s);
            }
        }
        with_closures = all;
        &with_closures
    };
    let vars = vars::Vars::build(p, &mut tys, facts, &comp);
    let mut roots = alpha::Roots::default();
    roots.set_field_places(&a.program);
    // The abort destinations of each node (`docs/ir.md` 6.5).
    let frames = frames::Frames::of_body(p, &tys, sums, entry);
    // The entry node: the parameters bind there. It is node `n0`, as in the
    // old lowering: the hypothesis `bound_before_use` of the proof link
    // starts at `n0` (`proofs/link/lints/unbound_use.dl`).
    let sp = weft_facts::Span {
        lo: body.origin.span.lo,
        hi: body.origin.span.hi,
    };
    let entry_node = facts.add_ir_node(sp, "entry", "entry", "");
    let mut table = nodes::NodeTable::default();
    table.add_body(p, &tys, entry, facts, &frames);
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
    let cycles = crate::analysis::widen::Cycles::of(p, &comp);
    let states = {
        let mut cx = crate::analysis::Cx {
            p,
            tys: &mut tys,
            facts,
            roots: &mut roots,
            sums,
            cycles: &cycles,
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
            cycles: &cycles,
            stored: Vec::new(),
            at: (weft_ir::BlockId(0), 0),
            returns: Vec::new(),
            runs: Vec::new(),
            code_multi: false,
            run_nodes: Vec::new(),
            own_lends: Vec::new(),
            last: (!closures.is_empty()).then(crate::analysis::State::new),
            aborts: std::collections::BTreeSet::new(),
            union: (!closures.is_empty()).then(crate::analysis::State::new),
        };
        templates::entry(&mut em, entry_node, &params).map_err(|e| unsupported(&e))?;
        emit_blocks(&mut em, &table, &frames, &states, body).map_err(|e| unsupported(&e))?;
        (
            em.stored,
            em.aborts,
            em.union,
            em.runs,
            em.returns,
            em.last,
            (em.code_multi, em.own_lends),
        )
    };
    let (mut stored, aborts, union, runs, returns, last, (code_multi, own_lends)) = stored;
    let closure_sums: Vec<(weft_ir::ClosureId, crate::analysis::Summary)> = closures
        .iter()
        .filter_map(|&cb| p.closure_of(cb).map(|(c, _)| c))
        .filter_map(|c| sums.closure(c).ok().map(|s| (c, s.clone())))
        .collect();
    // The facts of each closure body, instantiated (`docs/ir.md` 6.5): a
    // `Kept` capture is the place of the variable of the maker, and the body
    // starts with the values that the maker has where the closure can run.
    let entry_nodes = facts.nodes.len();
    let mut unions: std::collections::HashMap<weft_ir::BodyId, crate::analysis::State> =
        std::collections::HashMap::new();
    if let Some(u) = union {
        unions.insert(entry, u);
    }
    let mut closure_entries = Vec::new();
    for &cb in &closures {
        let (n, st) = emit_closure(
            &ClosureCx {
                a,
                p,
                sums,
                cycles: &cycles,
                seed: p
                    .closure_of(cb)
                    .and_then(|(_, d)| unions.get(&d.maker))
                    .cloned()
                    .unwrap_or_default(),
            },
            &mut ClosureOut {
                tys: &mut tys,
                facts,
                roots: &mut roots,
                vars: &vars,
                holders: &mut holders,
                uniq: &mut uniq,
                table: &mut table,
                stored: &mut stored,
            },
            cb,
        )
        .map_err(|e| unsupported(&e))?;
        closure_entries.push((cb, n));
        unions.insert(cb, st);
    }
    let (parts, slots) = holders.finish(facts);
    let mut diags = stored_behind(p, &tys, facts, &roots, body, &stored)?;
    diags.extend(kept_escapes(p, &tys, facts, &roots, entry, &returns));
    // Each local with a root owns it, and the cell of a local that a closure
    // captures `ByRef` is owned by `C` of the local.
    let owners: Vec<(PlaceId, weft_facts::VarId)> = roots
        .local_roots()
        .filter_map(|(k, r)| vars.get(&vars::VarKey::S(k.0, k.1)).map(|v| (r, v)))
        .chain(
            roots
                .cell_roots()
                .filter_map(|(k, r)| vars.get(&vars::VarKey::C(k.0, k.1)).map(|v| (r, v))),
        )
        .collect();
    facts.owner.extend(owners);
    // A `@ uniq` value is not `many` (`once_var`, as in the old lowering):
    // a `multi` resume would copy it (W0503).
    for (i, v) in facts.vars.iter_mut().enumerate() {
        let id = weft_facts::VarId(u32::try_from(i).unwrap_or(u32::MAX));
        v.uniq = uniq.get(&id).copied().unwrap_or(false);
        v.once |= v.uniq;
    }
    decls::std_effects(facts);
    facts.normalize();
    Ok(Emitted {
        diags,
        roots,
        table,
        vars,
        parts,
        slots,
        entry_node,
        tys,
        entry_nodes,
        closure_entries,
        aborts,
        runs,
        returns,
        code_multi,
        own_lends,
        made: unions.remove(&entry).map(|mut u| {
            if let Some(l) = &last {
                u.join(l);
            }
            u
        }),
        closures: closure_sums,
    })
}

/// What the facts of a closure body read ([`emit_closure`]).
struct ClosureCx<'a> {
    /// The analysis.
    a: &'a Analysis,
    /// The program.
    p: &'a weft_ir::Program,
    /// The summaries, with those of the closures of the component.
    sums: &'a crate::analysis::Summaries,
    /// The blocks of the component that are in a cycle of the CFG.
    cycles: &'a crate::analysis::widen::Cycles,
    /// The values of the maker where the closure can run: the join of its
    /// states before each terminator and before each closure literal.
    seed: crate::analysis::State,
}

/// What the facts of a closure body write into ([`emit_closure`]): the
/// tables of the component.
struct ClosureOut<'a, 'b> {
    /// The types.
    tys: &'b mut weft_ir::TyTable,
    /// The facts of the component.
    facts: &'b mut FnFacts,
    /// The roots of the component.
    roots: &'b mut alpha::Roots,
    /// The variables of the component.
    vars: &'a vars::Vars,
    /// The versions of the parts.
    holders: &'b mut holders::Holders,
    /// The `@ uniq` mode of each variable.
    uniq: &'b mut std::collections::BTreeMap<weft_facts::VarId, bool>,
    /// The nodes of the component.
    table: &'b mut nodes::NodeTable,
    /// The references that the bodies put behind a reference parameter.
    stored: &'b mut Vec<templates::Stored>,
}

/// The value of the environment local of closure body `cb` at its entry
/// (`docs/ir.md` 6.5).
///
/// With no `seed` (the summary of the closure, in the terms of its
/// interface): a `ByRef` capture points into its `Capture` root, and a
/// `ByMove` capture holds what its `CaptureHeld` root stands for. With the
/// state `seed` of the maker (the instantiated facts): a `ByRef` capture
/// points into the places of its source in the maker, and a `ByMove`
/// capture holds the value of its source.
///
/// # Errors
///
/// The errors of α.
fn env_value(
    cx: &mut crate::analysis::Cx<'_>,
    cb: weft_ir::BodyId,
    seed: Option<&crate::analysis::State>,
) -> Result<crate::analysis::Tree, alpha::AlphaError> {
    use crate::analysis::{AbsVal, PathStep, Tree};
    use weft_ir::CaptureMode;
    let p = cx.p;
    let Some((c, decl)) = p.closure_of(cb) else {
        return Ok(Tree::none());
    };
    let mut t = Tree::leaf(AbsVal::plain());
    for (k, cap) in decl.captures.iter().enumerate() {
        let k32 = u32::try_from(k).unwrap_or(u32::MAX);
        let v = match (cap.mode, seed) {
            (CaptureMode::ByRef, None) => {
                let name = alpha::capture_name(p, c, k32);
                Tree::leaf(AbsVal::refs([cx.roots.capture(cx.facts, cb, k32, &name)]))
            }
            (CaptureMode::ByRef, Some(st)) => {
                let a = crate::analysis::transfer::alpha(cx, decl.maker, st, &cap.source)?;
                Tree::leaf(AbsVal::refs(a.places))
            }
            (CaptureMode::ByMove, None) => {
                let props = alpha::capture_ty(p, cx.tys, c, k32)
                    .map(|t| crate::props::ir_props(cx.tys, t))
                    .unwrap_or_default();
                let mut v = AbsVal::of_type(props.linear);
                if props.holds_refs {
                    v.refs
                        .insert(cx.roots.capture_held_of(p, cx.facts, cb, k32));
                }
                Tree::leaf(v)
            }
            (CaptureMode::ByMove, Some(st)) => {
                crate::analysis::transfer::place_value(cx, decl.maker, st, &cap.source)?
            }
            // A `Kept` reference points into the `CaptureHeld` root, as a
            // reference through the capture does (stage F12).
            (CaptureMode::Kept, None) => {
                let holds = alpha::capture_ty(p, cx.tys, c, k32)
                    .is_some_and(|t| crate::props::ir_props(cx.tys, t).holds_refs);
                let mut v = AbsVal::plain();
                if holds {
                    v.refs
                        .insert(cx.roots.capture_held_of(p, cx.facts, cb, k32));
                }
                Tree::leaf(v)
            }
            _ => continue,
        };
        let mut v = v;
        // In the terms of the interface, a function value of a capture is
        // the value that the run node gives (stage F12, part `runs`).
        let fns = alpha::capture_ty(p, cx.tys, c, k32)
            .is_some_and(|t| crate::props::ir_has_fns(cx.tys, t));
        if seed.is_none() && fns && cap.mode != CaptureMode::ByRef {
            v.top.fns.insert(crate::analysis::FnVal::Capture(k32));
        }
        t.kids.insert(PathStep::Field(k32), v);
    }
    Ok(t)
}

/// The summary of closure body `cb` in the terms of its interface
/// (`docs/ir.md` 6.7): the facts of the body alone, with `Arg` roots for its
/// captures and parameters, projected onto the interface
/// (`crate::analysis::summarize::closure`).
///
/// # Errors
///
/// Returns [`Unsupported`] for a construct that the fact generator does not
/// support yet in the body.
fn closure_summary(
    a: &Analysis,
    built: &Built,
    sums: &crate::analysis::Summaries,
    cb: weft_ir::BodyId,
) -> Result<crate::analysis::Summary, Unsupported> {
    let p = &built.program;
    let mut tys = built.tys.clone();
    let mut facts = FnFacts::default();
    let comp = [cb];
    let vars = vars::Vars::build(p, &mut tys, &mut facts, &comp);
    let mut roots = alpha::Roots::default();
    roots.set_field_places(&a.program);
    let frames = frames::Frames::of_body(p, &tys, sums, cb);
    let body = p
        .bodies
        .get(cb.index())
        .ok_or_else(|| unsupported(&alpha::AlphaError::BadPlace("no body".to_string())))?;
    let sp = weft_facts::Span {
        lo: body.origin.span.lo,
        hi: body.origin.span.hi,
    };
    let en = facts.add_ir_node(sp, "closure entry", "closure entry", "");
    let mut table = nodes::NodeTable::default();
    table.add_body(p, &tys, cb, &mut facts, &frames);
    if let Some(first) = table.first(cb, body.entry, nodes::NORMAL) {
        facts.cfg_edge.push((en, first));
    }
    let params = decls::closure_params(p, &mut tys, &mut facts, &mut roots, cb)
        .map_err(|e| unsupported(&e))?;
    let cycles = crate::analysis::widen::Cycles::of(p, &comp);
    let (env, states) = {
        let mut cx = crate::analysis::Cx {
            p,
            tys: &mut tys,
            facts: &mut facts,
            roots: &mut roots,
            sums,
            cycles: &cycles,
        };
        let env = env_value(&mut cx, cb, None).map_err(|e| unsupported(&e))?;
        let mut init = decls::entry_state(p, cb, &params.entry).map_err(|e| unsupported(&e))?;
        if let Some(&e) = body.params.first() {
            init.write((cb, e), &[], env.clone());
        }
        let states = crate::analysis::run(&mut cx, cb, init).map_err(|e| unsupported(&e))?;
        (env, states)
    };
    let mut uniq = std::collections::BTreeMap::new();
    let mut holders = holders::Holders::new(vars.holder_parts());
    let (returns, aborts, runs, made, (run_nodes, own_lends)) = {
        let mut em = templates::Em {
            p,
            sema: &a.program,
            tys: &mut tys,
            facts: &mut facts,
            roots: &mut roots,
            vars: &vars,
            holders: &mut holders,
            body: cb,
            cleanup: false,
            ret_places: None,
            uniq: &mut uniq,
            skip_s: None,
            sums,
            cycles: &cycles,
            stored: Vec::new(),
            at: (weft_ir::BlockId(0), 0),
            returns: Vec::new(),
            runs: Vec::new(),
            code_multi: false,
            run_nodes: Vec::new(),
            own_lends: Vec::new(),
            last: Some(crate::analysis::State::new()),
            aborts: std::collections::BTreeSet::new(),
            union: Some(crate::analysis::State::new()),
        };
        templates::closure_entry(&mut em, en, &params.entry, &env).map_err(|e| unsupported(&e))?;
        emit_blocks(&mut em, &table, &frames, &states, body).map_err(|e| unsupported(&e))?;
        (
            std::mem::take(&mut em.returns),
            std::mem::take(&mut em.aborts),
            std::mem::take(&mut em.runs),
            em.union.take().map(|mut u| {
                if let Some(l) = &em.last {
                    u.join(l);
                }
                u
            }),
            (
                std::mem::take(&mut em.run_nodes),
                std::mem::take(&mut em.own_lends),
            ),
        )
    };
    let rebind_nodes = rebind_nodes(p, &table, cb);
    let ret_linear = crate::analysis::summarize::ret_linear(p, &tys, &returns, cb);
    let mut sum = crate::analysis::summarize::closure(
        p,
        sums,
        &facts,
        &roots,
        cb,
        &aborts,
        &crate::analysis::summarize::FnParts {
            runs: &runs,
            returns: &returns,
            code_multi: false,
            run_nodes: &run_nodes,
            lends: &own_lends,
            made: made.as_ref(),
            rebind_nodes: &rebind_nodes,
        },
    );
    sum.ret.linear = ret_linear;
    Ok(sum)
}

/// The nodes of closure body `cb` where it gives a capture a whole new value
/// (`summarize::whole_capture`), with the index of the capture: the node of
/// an assignment, and the `Ret` node of a call that gives its result to the
/// capture.
fn rebind_nodes(
    p: &weft_ir::Program,
    table: &nodes::NodeTable,
    cb: weft_ir::BodyId,
) -> Vec<(u32, weft_facts::NodeId)> {
    let mut out = Vec::new();
    let (Some((_, decl)), Some(b)) = (p.closure_of(cb), p.body(cb)) else {
        return out;
    };
    let key = |block, at, phase| nodes::NodeKey {
        body: cb,
        block,
        at,
        phase,
        dest: nodes::NORMAL,
    };
    for (i, blk) in b.blocks.iter().enumerate() {
        let block = weft_ir::BlockId(u32::try_from(i).unwrap_or(u32::MAX));
        for (j, s) in blk.stmts.iter().enumerate() {
            if let weft_ir::StmtKind::Assign(q, _) = &s.kind {
                let k = crate::analysis::summarize::whole_capture(b, decl, q);
                let n = table.get(key(
                    block,
                    u32::try_from(j).unwrap_or(u32::MAX),
                    nodes::Phase::Main,
                ));
                if let (Some(k), Some(n)) = (k, n) {
                    out.push((k, n));
                }
            }
        }
        if let weft_ir::TermKind::Call { dest, .. } = &blk.term.kind {
            let k = crate::analysis::summarize::whole_capture(b, decl, dest);
            let n = table.get(key(block, nodes::TERM, nodes::Phase::Ret));
            if let (Some(k), Some(n)) = (k, n) {
                out.push((k, n));
            }
        }
    }
    out
}

/// The facts of closure body `cb`, instantiated (`docs/ir.md` 6.5): its
/// nodes, from a node `closure entry` where its parameters and its captures
/// bind, in the tables of the component. Its `Kept` captures are the places
/// of the variables of the maker (`alpha::Roots::instantiate`), and the
/// analysis starts from the state `seed` of the maker, so the facts see the
/// aliases between the captures. Returns the entry node and the join of the
/// states that a closure of the body can see.
///
/// # Errors
///
/// The errors of α and of the analysis.
fn emit_closure(
    cx: &ClosureCx<'_>,
    out: &mut ClosureOut<'_, '_>,
    cb: weft_ir::BodyId,
) -> Result<(weft_facts::NodeId, crate::analysis::State), alpha::AlphaError> {
    let p = cx.p;
    out.roots.instantiate(cb);
    let body = p
        .bodies
        .get(cb.index())
        .ok_or_else(|| alpha::AlphaError::BadPlace("no body".to_string()))?;
    let frames = frames::Frames::of_body(p, out.tys, cx.sums, cb);
    let sp = weft_facts::Span {
        lo: body.origin.span.lo,
        hi: body.origin.span.hi,
    };
    let en = out
        .facts
        .add_ir_node(sp, "closure entry", "closure entry", "");
    out.table.add_body(p, out.tys, cb, out.facts, &frames);
    if let Some(first) = out.table.first(cb, body.entry, nodes::NORMAL) {
        out.facts.cfg_edge.push((en, first));
    }
    let params = decls::closure_params(p, out.tys, out.facts, out.roots, cb)?;
    let (env, states) = {
        let mut acx = crate::analysis::Cx {
            p,
            tys: out.tys,
            facts: out.facts,
            roots: out.roots,
            sums: cx.sums,
            cycles: cx.cycles,
        };
        let env = env_value(&mut acx, cb, Some(&cx.seed))?;
        let mut init = cx.seed.clone();
        for (l, v) in &params.entry {
            init.write(crate::analysis::transfer::key(p, cb, *l)?, &[], v.clone());
        }
        if let Some(&e) = body.params.first() {
            init.write((cb, e), &[], env.clone());
        }
        let states = crate::analysis::run(&mut acx, cb, init)?;
        (env, states)
    };
    let mut em = templates::Em {
        p,
        sema: &cx.a.program,
        tys: out.tys,
        facts: out.facts,
        roots: out.roots,
        vars: out.vars,
        holders: out.holders,
        body: cb,
        cleanup: false,
        ret_places: None,
        uniq: out.uniq,
        skip_s: None,
        sums: cx.sums,
        cycles: cx.cycles,
        stored: Vec::new(),
        at: (weft_ir::BlockId(0), 0),
        returns: Vec::new(),
        runs: Vec::new(),
        code_multi: false,
        run_nodes: Vec::new(),
        own_lends: Vec::new(),
        last: None,
        aborts: std::collections::BTreeSet::new(),
        union: Some(crate::analysis::State::new()),
    };
    templates::closure_entry(&mut em, en, &params.entry, &env)?;
    emit_blocks(&mut em, out.table, &frames, &states, body)?;
    out.stored.append(&mut em.stored);
    let union = em.union.take().unwrap_or_default();
    Ok((en, union))
}

/// The facts of one component and the tables that map its IR to them
/// ([`components`]).
#[derive(Clone, Debug)]
pub struct Component {
    /// The index of the entry body in [`Analysis::bodies`].
    pub index: usize,
    /// The entry body of the component.
    pub entry: weft_ir::BodyId,
    /// The facts, as the checker gets them in the `ir` pipeline.
    pub facts: FnFacts,
    /// The tables.
    pub emitted: Emitted,
}

/// The facts of each component of a program in scope, with the tables that
/// map its IR to them: the input of the fact oracle of the interpreter
/// (`docs/ir.md` 8.5).
///
/// The summaries are the fixpoint of the call graph, as in [`emit`]. Each
/// component is made again with them, so the node ids are the ids of the
/// facts that the checker reads. A body with no IR has no component.
///
/// # Errors
///
/// Returns [`Unsupported`] for the first body that the fact generator does
/// not support (the program is not in scope).
pub fn components(a: &Analysis, built: &Built) -> Result<Vec<Component>, Unsupported> {
    let inf = crate::analysis::callgraph::infer(a, built, None);
    let mut facts: Vec<FnFacts> = a.bodies.iter().map(|b| seed(&b.facts)).collect();
    let mut tables = Vec::new();
    for (i, e) in built.entries.iter().enumerate() {
        let Outcome::Built(entry) = e.outcome else {
            continue;
        };
        if let Some(Err(u)) = inf.facts.get(&i) {
            return Err(u.clone());
        }
        let Some(f) = facts.get_mut(i) else {
            continue;
        };
        let emitted = emit_parts(a, built, &inf.sums, i, entry, f)?;
        tables.push((i, entry, emitted));
    }
    exports::fill(a, built, &mut facts);
    Ok(tables
        .into_iter()
        .filter_map(|(index, entry, emitted)| {
            let facts = facts.get(index)?.clone();
            Some(Component {
                index,
                entry,
                facts,
                emitted,
            })
        })
        .collect())
}

/// The W0204 store check (`docs/ir.md` 6.9): a reference into a local, a
/// temporary or a by-value parameter that the body puts behind a reference
/// parameter or into an `rc` object. The local ends at the return, and the
/// caller keeps the reference. One diagnostic for each place that gets the
/// reference and each local, at the span of the node, as the old lowering
/// (`check_stored_behind`).
///
/// # Errors
///
/// Returns [`Unsupported`] for a reference through a whole local handle that
/// can be a copy of a handle of the object that gets it
/// (`templates::Stored::maybe_same`).
fn stored_behind(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    facts: &FnFacts,
    roots: &alpha::Roots,
    body: &weft_ir::Body,
    stored: &[templates::Stored],
) -> Result<Vec<Diagnostic>, Unsupported> {
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
            // A whole local handle of the object that gets the store: the
            // reference goes away with the object (`templates::rc_handles`).
            if st.same.contains(&r) {
                continue;
            }
            // A whole local handle that can be a copy of a handle of the
            // object: the facts cannot tell if the object is the same.
            if st.maybe_same.contains(&r) {
                return Err(Unsupported {
                    group: Group::A,
                    reason: "a reference through a copy of an `rc` handle goes into an `rc` object of the same type".to_string(),
                });
            }
            // A reference into a local, or into the cell of a local that a
            // closure captures `ByRef` (a closure that captures the local,
            // stage F13).
            let (key, cell) = match roots.role(root) {
                Some(alpha::Role::Local(key)) => (key, false),
                Some(alpha::Role::Cell(key)) => (key, true),
                _ => continue,
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
            let msg = if cell {
                format!(
                    "`{}` puts a closure that captures `{name}` {into}: {what} goes out of scope at the return",
                    facts.name
                )
            } else {
                format!(
                    "`{}` puts a reference into `{shown}` {into}: {what} goes out of scope at the return",
                    facts.name
                )
            };
            let span = weft_syntax::ast::Span {
                lo: st.span.lo,
                hi: st.span.hi,
            };
            let mut diag = Diagnostic::error(Code::W0204, msg, span);
            diag.unit = body.origin.span.unit as usize;
            out.push(diag);
        }
    }
    Ok(out)
}

/// The W0204 check of the `Kept` captures of a closure that leaves the
/// body (stage F13, the `late_stores` of the old lowering): a closure that
/// the function gives back, or puts into a heap slot of an interface place,
/// shares the cell of each variable that it keeps, so it sees the value of
/// the variable at the return. A reference there into a local of the
/// component goes out of scope at the return. The value of the closure
/// holds the references of the variable where the closure is made only
/// (the analysis does not change them when the variable gets a new value):
/// this check gives the references of the later values. A reference that
/// the value holds is the spec error of `_0`, or the store check.
fn kept_escapes(
    p: &weft_ir::Program,
    tys: &weft_ir::TyTable,
    facts: &FnFacts,
    roots: &alpha::Roots,
    entry: weft_ir::BodyId,
    returns: &[crate::analysis::State],
) -> Vec<Diagnostic> {
    use crate::analysis::FnVal;
    use weft_syntax::diag::Code;
    let mut out = Vec::new();
    let Some(body) = p.body(entry) else {
        return out;
    };
    let ret_span = body
        .blocks
        .iter()
        .find(|b| !b.cleanup && matches!(b.term.kind, weft_ir::TermKind::Return))
        .map_or(body.origin.span, |b| b.term.origin.span);
    let mut seen: Vec<(bool, weft_facts::RootId)> = Vec::new();
    let interface = |q: PlaceId| {
        facts.places.get(q.index()).is_some_and(|i| {
            matches!(
                roots.role(i.root),
                Some(
                    alpha::Role::Param(..)
                        | alpha::Role::Held(..)
                        | alpha::Role::Group
                        | alpha::Role::Caller
                )
            )
        })
    };
    for st in returns {
        // The closures that leave: the result, and the heap slots of the
        // places of the callers, each with the references that it holds.
        let mut leaving: Vec<(Option<PlaceId>, crate::analysis::AbsVal)> = Vec::new();
        leaving.push((None, st.value((entry, body.ret), &[]).flat()));
        for (q, fns) in st.behind_fns() {
            if interface(*q) {
                let mut v = crate::analysis::AbsVal::none();
                v.fns.clone_from(fns);
                v.refs = st.behind().get(q).cloned().unwrap_or_default();
                leaving.push((Some(*q), v));
            }
        }
        for (into, v) in leaving {
            // The roots that the value holds already: the spec (or the store
            // check) reports them.
            let held: std::collections::BTreeSet<weft_facts::RootId> = v
                .refs
                .iter()
                .filter_map(|r| facts.places.get(r.index()).map(|i| i.root))
                .collect();
            let mut work: Vec<FnVal> = v.fns.iter().cloned().collect();
            let mut done = std::collections::BTreeSet::new();
            while let Some(f) = work.pop() {
                if !done.insert(f.clone()) {
                    continue;
                }
                // A closure of the component, or a closure that a closure of
                // the component made (class K3-Made of the review of stage
                // F13: `let m = || || print(r.hp); let g = m()`).
                let (FnVal::Closure(c) | FnVal::Made(c)) = f else {
                    continue;
                };
                let Some(decl) = p.closures.get(c.index()) else {
                    continue;
                };
                for (j, cap) in decl.captures.iter().enumerate() {
                    if cap.mode != weft_ir::CaptureMode::Kept {
                        continue;
                    }
                    // The variable of the entry body that the capture shares,
                    // through the `Kept` and `ByRef` captures of the makers (a
                    // capture of a capture, `env.j`, has a projection).
                    let Some(src) = crate::analysis::apply::made_capture_source(p, c, j, entry)
                    else {
                        continue;
                    };
                    let Ok(k) = alpha::owner_local(p, entry, src.local) else {
                        continue;
                    };
                    let path: Vec<crate::analysis::PathStep> = src
                        .proj
                        .iter()
                        .map_while(|pr| match pr {
                            weft_ir::Proj::Field(f) => Some(crate::analysis::PathStep::Field(f.0)),
                            weft_ir::Proj::Variant(v) => {
                                Some(crate::analysis::PathStep::Variant(v.0))
                            }
                            _ => None,
                        })
                        .collect();
                    let src = st.value(k, &path).flat();
                    work.extend(src.fns.iter().cloned());
                    for &r in &src.refs {
                        let Some(root) = facts.places.get(r.index()).map(|i| i.root) else {
                            continue;
                        };
                        if held.contains(&root) {
                            continue;
                        }
                        let Some(alpha::Role::Local(key)) = roots.role(root) else {
                            continue;
                        };
                        if seen.contains(&(into.is_some(), root)) {
                            continue;
                        }
                        seen.push((into.is_some(), root));
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
                        let (msg, sp) = match into {
                            None => (
                                format!(
                                    "the returned closure captures `{shown}`: {what} of `{}` goes out of scope at the return",
                                    facts.name
                                ),
                                ret_span,
                            ),
                            Some(q) => {
                                let place = match facts
                                    .places
                                    .get(q.index())
                                    .and_then(|i| roots.role(i.root))
                                {
                                    Some(alpha::Role::Param(b, i) | alpha::Role::Held(b, i)) => {
                                        format!(
                                            "behind the parameter `{}`",
                                            crate::analysis::transfer::param_name(p, b, i)
                                        )
                                    }
                                    _ => "into a place of a caller".to_string(),
                                };
                                let lit = p.body(decl.body).map_or(ret_span, |b| b.origin.span);
                                (
                                    format!(
                                        "`{}` puts a closure that captures `{shown}` {place}: {what} goes out of scope at the return",
                                        facts.name
                                    ),
                                    lit,
                                )
                            }
                        };
                        let span = weft_syntax::ast::Span {
                            lo: sp.lo,
                            hi: sp.hi,
                        };
                        let mut diag = Diagnostic::error(Code::W0204, msg, span);
                        diag.unit = body.origin.span.unit as usize;
                        out.push(diag);
                    }
                }
            }
        }
    }
    out
}

/// The templates of each block of `body` that the entry reaches, with the
/// states of the analysis: each statement, then the terminator. A cleanup
/// block has one copy for each abort destination that reaches it
/// (`frames`, `docs/ir.md` 6.5).
///
/// The blocks go in reverse post-order. The analysis keeps the state of
/// each join block only (`crate::analysis::States`): the state at the
/// entry of another block is the state on the edge from its one
/// predecessor, which this function computes and keeps until it uses it.
fn emit_blocks(
    em: &mut templates::Em<'_>,
    table: &nodes::NodeTable,
    frames: &frames::Frames,
    states: &crate::analysis::States,
    body: &weft_ir::Body,
) -> Result<(), alpha::AlphaError> {
    use nodes::NORMAL;
    let bid = em.body;
    let mut pending: std::collections::HashMap<weft_ir::BlockId, crate::analysis::State> =
        std::collections::HashMap::new();
    for block in weft_ir::order::reverse_post_order(body) {
        let Some(blk) = body.blocks.get(block.index()) else {
            continue;
        };
        let start = match states.at(block) {
            Some(s) => s.clone(),
            None => match pending.remove(&block) {
                Some(s) => s,
                None => continue,
            },
        };
        // A cleanup block: each copy that the node table made.
        let copies = if blk.cleanup {
            table.copies(bid, block)
        } else {
            vec![NORMAL]
        };
        let mut after = None;
        for dest in copies {
            let st = emit_block(em, table, frames, &start, body, block, dest)?;
            after.get_or_insert(st);
        }
        // The states on the edges to the blocks that are not join blocks.
        let after = match after {
            Some(st) => st,
            None => after_stmts(em, &start, blk)?,
        };
        let needs = blk
            .term
            .kind
            .unwind()
            .into_iter()
            .chain(blk.term.kind.normal_successors())
            .any(|to| !states.is_join(to));
        if needs {
            let mut cx = em_cx(em);
            for (to, st) in crate::analysis::edges(&mut cx, bid, block, &blk.term.kind, after)? {
                if !states.is_join(to) {
                    pending.insert(to, st);
                }
            }
        }
    }
    em.cleanup = false;
    em.skip_s = None;
    Ok(())
}

/// The state after the statements of block `blk`, from the state `start`
/// at its entry, with no templates.
fn after_stmts(
    em: &mut templates::Em<'_>,
    start: &crate::analysis::State,
    blk: &weft_ir::Block,
) -> Result<crate::analysis::State, alpha::AlphaError> {
    let bid = em.body;
    let mut st = start.clone();
    let mut cx = em_cx(em);
    for s in &blk.stmts {
        crate::analysis::transfer::stmt(&mut cx, bid, &mut st, &s.kind)?;
    }
    Ok(st)
}

/// The templates of copy `dest` of block `block` of `body`, from the state
/// `start` of the analysis at its entry. Returns the state after the
/// statements of the block (before its terminator).
fn emit_block(
    em: &mut templates::Em<'_>,
    table: &nodes::NodeTable,
    frames: &frames::Frames,
    start: &crate::analysis::State,
    body: &weft_ir::Body,
    block: weft_ir::BlockId,
    dest: u32,
) -> Result<crate::analysis::State, alpha::AlphaError> {
    use crate::analysis::transfer;
    use nodes::{NodeKey, Phase, NORMAL, TERM};
    let bid = em.body;
    let Some(blk) = body.blocks.get(block.index()) else {
        return Ok(start.clone());
    };
    em.cleanup = blk.cleanup;
    let mut st = start.clone();
    // The parts that the binds of the current pattern moved, by local.
    let mut run: Vec<(crate::analysis::Key, Vec<crate::analysis::PathStep>)> = Vec::new();
    for (si, s) in blk.stmts.iter().enumerate() {
        em.skip_s = None;
        match pattern_bind(em.p, bid, body, s)? {
            Bind::Part(k, path, moves) => {
                // A copy of a part that can be a `once` closure moves it
                // (stage F12, `docs/ir.md` 5.22).
                let moves = moves || copy_once(em, &st, s)?;
                // A later bind of another part of the same local is one move
                // with the earlier binds. A bind of a part that overlaps a
                // moved part reads a moved value: it keeps its use of `S(l)`
                // (W0302; review of stage F8, `consume_r(s.items, &s.items)`).
                let overlaps =
                    |p: &[crate::analysis::PathStep]| p.starts_with(&path) || path.starts_with(p);
                if run.iter().any(|(rk, _)| *rk == k)
                    && !run.iter().any(|(rk, rp)| *rk == k && overlaps(rp))
                {
                    em.skip_s = Some(k);
                }
                if moves {
                    run.push((k, path));
                }
            }
            Bind::Consumed(k, path) => run.push((k, path)),
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
        // A closure sees the values of the body when it runs: the state
        // before its literal (`docs/ir.md` 6.5).
        if let (
            Some(u),
            weft_ir::StmtKind::Assign(
                _,
                weft_ir::Rvalue::Aggregate(weft_ir::AggKind::Closure(_), _),
            ),
        ) = (em.union.as_mut(), &s.kind)
        {
            u.join(&st);
        }
        if let (Some(u), weft_ir::StmtKind::Dead(_)) = (em.last.as_mut(), &s.kind) {
            u.join(&st);
        }
        if let Some(n) = table.get(key) {
            em.at = (block, at);
            em.holders.before(n, &st, em.facts);
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
    if let Some(u) = em.union.as_mut() {
        u.join(&st);
    }
    let Some(n) = table.get(at(Phase::Main, dest)) else {
        return Ok(st);
    };
    if matches!(blk.term.kind, weft_ir::TermKind::Return) && dest == NORMAL {
        em.returns.push(st.clone());
    }
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
        em.holders.before(m, &st, em.facts);
    }
    em.at = (block, TERM);
    match &blk.term.kind {
        weft_ir::TermKind::Call { .. } => {
            let nodes = templates::CallNodes {
                main: n,
                ret: table.get(at(Phase::Ret, NORMAL)),
                frame_end: table.get(at(Phase::FrameEnd, NORMAL)),
                aborts,
                may_abort: !dests.is_empty(),
            };
            templates::call(em, &nodes, &st, block, &blk.term.kind, blk.term.origin.span)?;
        }
        weft_ir::TermKind::Perform { .. } => {
            let nodes = templates::CallNodes {
                main: n,
                ret: table.get(at(Phase::Ret, NORMAL)),
                frame_end: None,
                aborts: Vec::new(),
                may_abort: !dests.is_empty(),
            };
            templates::perform(em, &nodes, &st, &blk.term.kind)?;
        }
        _ => templates::term(em, n, &st, &blk.term.kind, blk.term.origin.span)?,
    }
    Ok(st)
}

/// What a statement is for the binds of a pattern.
enum Bind {
    /// A bind of a pattern that reads the part `path` of a local: a move if
    /// the bool is true.
    Part(crate::analysis::Key, Vec<crate::analysis::PathStep>, bool),
    /// A `Consume` of a part: a part of the pattern that ends with no
    /// bind (a variant with no payload). It is a moved part of the run.
    Consumed(crate::analysis::Key, Vec<crate::analysis::PathStep>),
    /// A statement that the binds of a pattern can have between them
    /// (`Live`, `Dead`, the `Consume` of a whole local).
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
        StmtKind::Consume(q) if !q.proj.is_empty() => {
            return Ok(match crate::analysis::transfer::move_path(p, bid, q)? {
                Some((k, path)) => Bind::Consumed(k, path),
                None => Bind::Keep,
            });
        }
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

/// True if statement `s` copies a part that can be a `once` closure in
/// state `st`: the copy moves the part ([`templates::once_read`]).
///
/// # Errors
///
/// The errors of α.
fn copy_once(
    em: &mut templates::Em<'_>,
    st: &crate::analysis::State,
    s: &weft_ir::Stmt,
) -> Result<bool, alpha::AlphaError> {
    use weft_ir::{Operand, Rvalue, StmtKind};
    match &s.kind {
        StmtKind::Assign(_, Rvalue::Use(Operand::Copy(q))) => templates::once_read(em, st, q),
        _ => Ok(false),
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
        cycles: em.cycles,
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
    // With no group on (`--groups` with no letter), no program is in
    // scope: also a program whose bodies have no IR and use no group.
    if on.is_empty() {
        s.fallback = Some("no construct group is on".to_string());
        return (s, None);
    }
    // A body with no IR has no facts. The program stays in scope only if it
    // reports an error for the reason (`irbuild::Entry::reported`): else no
    // pipeline checks the body (stage F10-fix, hole H-B).
    if let Some(e) = built
        .entries
        .iter()
        .find(|e| matches!(e.outcome, Outcome::NoIr(_)) && !e.reported)
    {
        let why = match e.outcome {
            Outcome::NoIr(n) => n.reason(),
            _ => "",
        };
        s.fallback = Some(format!(
            "`{}` has no IR ({why}), and the program reports no error for it",
            e.name
        ));
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
