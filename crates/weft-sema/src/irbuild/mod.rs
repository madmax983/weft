//! The builder of the IR: the typed tree (THIR) to IR bodies (`docs/ir.md`
//! section 5).
//!
//! [`build`] lowers each function and each test of an [`Analysis`] to one
//! [`Body`] of a [`Program`]. It reads only the syntax tree and the THIR tables
//! of the analysis ([`Analysis::thir`], [`Analysis::thir_tys`]). It never infers
//! a type.
//!
//! The builder decides the order of evaluation, the temporaries, the ends of
//! the locals and the cleanup (`docs/ir.md` 1.5, principle 8). It keeps a stack
//! of scopes (`docs/ir.md` 5.1.2). It has three entry points for an
//! expression (`docs/ir.md` 5.1.1): `into` writes the value into a place,
//! `operand` gives an operand, and `place` gives a place.
//!
//! The builder grew one construct group at a time (plan stages B3 to B12),
//! and it lowers each construct of the language now. A THIR that does not fit
//! the syntax tree gives [`Outcome::Unsupported`] (a bug), never a panic. A
//! body with a `typeck` error, or with a move through a reference (W0303),
//! gets no IR ([`Outcome::NoIr`], `docs/ir.md` 5.36).
//!
//! The builder runs the verifier ([`weft_ir::verify::verify_program`]) on the
//! program that it makes, and keeps each broken rule in [`Built::broken`]. A
//! broken rule is a bug of the builder.

mod aggregate;
mod branch;
mod call;
mod caps;
mod cleanup;
mod closure;
mod expr;
mod frame;
mod handle;
mod looping;
mod pattern;
mod place;
pub mod scope;
mod stmt;
mod task;
mod unset;
mod upvar;

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;

use weft_ir::verify::{verify_program, Broken};
use weft_ir::{
    Block, BlockId, Body, BodyId, BodyKind, CapEnv, CapEnvId, EffectId, ExprId, FnDecl, Intrinsic,
    LocalDecl, LocalId, LocalKind, Origin, Place, Program, Props, Rvalue, Stmt, StmtKind, TempKind,
    Term, TermKind, TestDecl, TestId, TyId, TyTable,
};
use weft_syntax::ast::{self, Span};
use weft_syntax::diag::Diagnostic;

pub(crate) use closure::walk_block;
pub(crate) use unset::subst;

use crate::thir::{BindingId, Tables};
use crate::Analysis;

/// A construct that the builder does not lower.
///
/// Since plan stage B12 the builder lowers each construct of the language,
/// so the only one left is a THIR that does not fit the syntax tree: a bug of
/// `typeck` or of the builder, never a property of the program. Each one
/// names the plan stage that owns it ([`Construct::stage`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Construct {
    /// The THIR has no type or no binding for a part of the body, or the
    /// entry does not fit the syntax tree.
    NoThir,
}

impl Construct {
    /// Returns the name of the construct.
    pub const fn name(self) -> &'static str {
        match self {
            Self::NoThir => "no THIR entry",
        }
    }

    /// Returns the plan stage that owns the construct.
    pub const fn stage(self) -> &'static str {
        match self {
            Self::NoThir => "T3",
        }
    }
}

/// A body that the builder does not lower: the first construct that it
/// cannot lower.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unsupported {
    /// The construct.
    pub construct: Construct,
    /// Its location in the unit of the body.
    pub span: Span,
}

/// Why a body gets no IR (`docs/ir.md` 5, 5.36).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NoIr {
    /// The body has a `typeck` error: a W01xx diagnostic, or the error type.
    TypeError,
    /// The declarations of the program have no final types.
    DeclTypes,
    /// The THIR tables of the body have a conflict.
    Conflict,
    /// The body moves a value that is not plain data through a reference:
    /// W0303 of the old lowering (`docs/ir.md` 5.36).
    MoveThroughRef,
    /// The body names the payload of a variant with no field or with more
    /// than one field as a place: `o.A` (`docs/ir.md` 5.8, 5.36).
    VariantPayload,
}

impl NoIr {
    /// Returns why the body gets no IR, as text.
    pub const fn reason(self) -> &'static str {
        match self {
            Self::TypeError => "a type error",
            Self::DeclTypes => "the declarations have no final types",
            Self::Conflict => "a conflict in the THIR tables",
            Self::MoveThroughRef => "W0303, a move through a reference",
            Self::VariantPayload => "a variant payload of no field or of more than one field",
        }
    }
}

/// What the builder made of one body of the analysis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// The body of the program.
    Built(BodyId),
    /// The body has a construct of a later stage.
    Unsupported(Unsupported),
    /// The body gets no IR.
    NoIr(NoIr),
}

/// One body of the analysis and what the builder made of it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    /// The name of the body (`FnFacts::name`: the path of a function, or
    /// `test "name"`).
    pub name: String,
    /// The unit of the body.
    pub unit: usize,
    /// What the builder made of it.
    pub outcome: Outcome,
}

/// The result of [`build`].
#[derive(Clone, Debug)]
pub struct Built {
    /// The program: the bodies that the builder made, and their declarations.
    pub program: Program,
    /// The final types: the types of the THIR, and the types that the builder
    /// adds (the type of a borrow temporary).
    pub tys: TyTable,
    /// One entry for each body of [`Analysis::bodies`], in the same order.
    pub entries: Vec<Entry>,
    /// The function of the program for each function of the analysis that has
    /// one.
    pub fns: BTreeMap<crate::FnId, weft_ir::FnId>,
    /// The rules that the program breaks (`weft_ir::verify`). Each one is a bug
    /// of the builder.
    pub broken: Vec<Broken>,
    /// The diagnostics of the builder (`docs/ir.md` 5.36): W0315 for a jump
    /// out of a fence. Only the built bodies give diagnostics.
    pub diags: Vec<Diagnostic>,
}

impl Built {
    /// Returns the count of built bodies, the count of bodies with no IR, and the
    /// count of unsupported bodies for each construct.
    pub fn counts(&self) -> (usize, usize, BTreeMap<Construct, usize>) {
        let (mut built, mut none) = (0, 0);
        let mut unsupported = BTreeMap::new();
        for e in &self.entries {
            match &e.outcome {
                Outcome::Built(_) => built += 1,
                Outcome::NoIr(_) => none += 1,
                Outcome::Unsupported(u) => *unsupported.entry(u.construct).or_insert(0) += 1,
            }
        }
        (built, none, unsupported)
    }

    /// Returns the count of bodies with no IR for each reason.
    pub fn no_ir_counts(&self) -> BTreeMap<NoIr, usize> {
        let mut out = BTreeMap::new();
        for e in &self.entries {
            if let Outcome::NoIr(n) = e.outcome {
                *out.entry(n).or_insert(0) += 1;
            }
        }
        out
    }
}

/// Returns the text of the IR of `b`.
///
/// The text is the program as [`weft_ir::print`] prints it, then one comment
/// line for each body that has no IR. `at` gives the text of a location in a
/// unit (for example `line:column`). Each diagnostic of the builder is a
/// comment line too.
pub fn text(b: &Built, at: &dyn Fn(usize, Span) -> String) -> String {
    let mut s = weft_ir::print::print_program(&b.program, &b.tys);
    for d in &b.diags {
        let _ = writeln!(
            s,
            "// {} at {}: {}",
            d.code.as_str(),
            at(d.unit, d.span),
            d.message
        );
    }
    for e in &b.entries {
        match &e.outcome {
            Outcome::Built(_) => {}
            Outcome::Unsupported(u) => {
                let _ = writeln!(
                    s,
                    "// {}: unsupported: {} at {} (stage {})",
                    e.name,
                    u.construct.name(),
                    at(e.unit, u.span),
                    u.construct.stage()
                );
            }
            Outcome::NoIr(n) => {
                let _ = writeln!(s, "// {}: no IR: {}", e.name, n.reason());
            }
        }
    }
    s
}

/// Builds the IR of each function and each test of `a`, on a large stack
/// ([`crate::on_large_stack`]).
pub fn build(a: &Analysis) -> Built {
    crate::on_large_stack(|| build_all(a))
}

/// The id of item `i` of a table of the IR.
fn id_of(i: usize) -> u32 {
    u32::try_from(i).unwrap_or(u32::MAX)
}

/// Builds the IR of each body of `a` on the current stack.
fn build_all(a: &Analysis) -> Built {
    let mut out = Built {
        program: Program::default(),
        tys: a.thir_tys.clone(),
        entries: Vec::new(),
        fns: BTreeMap::new(),
        broken: Vec::new(),
        diags: Vec::new(),
    };
    let mut fields = unset::PlaceFields::new(&out.tys);
    // One capability environment: the entry of each function and each test
    // binds no effect.
    out.program.cap_envs.push(CapEnv {
        parent: None,
        adds: Vec::new(),
    });
    let mut decl_ok = Vec::new();
    for b in &a.bodies {
        if let Some(f) = b.func {
            let (decl, ok) = fn_decl(a, &mut out.tys, f);
            out.fns
                .insert(f, weft_ir::FnId(id_of(out.program.fns.len())));
            out.program.fns.push(decl);
            decl_ok.push(ok);
        }
    }
    let funcs = a.bodies.iter().filter(|b| b.func.is_some()).count();
    let mut fn_index = 0;
    for (i, (b, t)) in a.bodies.iter().zip(&a.thir).enumerate() {
        let name = b.facts.name.clone();
        // The bodies of the tests come after the bodies of the functions.
        let test = i.checked_sub(funcs).and_then(|j| a.program.tests.get(j));
        let src = if let Some(f) = b.func {
            let k = fn_index;
            fn_index += 1;
            let def = a.program.fns.get(f.index());
            let sig = a.sigs.get(f.index());
            match (def, sig, out.fns.get(&f)) {
                (Some(def), Some(sig), Some(&id)) => def.decl.body.as_ref().map(|block| Src {
                    kind: BodyKind::Fn(id),
                    block,
                    span: def.span,
                    params: sig.params.iter().map(|p| p.uniq).collect(),
                    decl_ok: decl_ok.get(k).copied().unwrap_or(false),
                    ret: out.program.fns.get(id.index()).map(|d| d.ret),
                }),
                _ => None,
            }
        } else {
            test.map(|test| Src {
                kind: BodyKind::Test(TestId(id_of(out.program.tests.len()))),
                block: &test.body,
                span: test.span,
                params: Vec::new(),
                decl_ok: true,
                ret: Some(out.tys.unit()),
            })
        };
        let outcome = match src {
            None => Outcome::NoIr(NoIr::TypeError),
            Some(src) => {
                let outcome = body_outcome(a, b.unit, t, &src, &mut out, &mut fields);
                if let (Outcome::Built(id), BodyKind::Test(_)) = (&outcome, src.kind) {
                    out.program.tests.push(TestDecl {
                        name: test.map_or_else(String::new, |t| t.name.clone()),
                        body: *id,
                    });
                }
                outcome
            }
        };
        out.entries.push(Entry {
            name,
            unit: b.unit,
            outcome,
        });
    }
    // The blocks in reverse post-order (`docs/ir.md` 5.1.9): the text reads
    // from top to bottom, and each later pass sees a block after the blocks
    // that go to it.
    for body in &mut out.program.bodies {
        weft_ir::order::renumber(body);
    }
    out.broken = verify_program(&out.program, &out.tys);
    out
}

/// The source of one body.
struct Src<'a> {
    /// The kind of the body.
    kind: BodyKind,
    /// The block of the body.
    block: &'a ast::Block,
    /// The location of the item.
    span: Span,
    /// The `@ uniq` mode of each parameter.
    params: Vec<bool>,
    /// The declaration of the function has final types.
    decl_ok: bool,
    /// The result type.
    ret: Option<TyId>,
}

/// Returns true if a `typeck` diagnostic is inside the body at `span` with
/// block `block` of unit `unit` (the rule of test D0). W0118 does not count:
/// it is a check of the effects of an `on abort` function, and the `ir`
/// pipeline asks the summary of the body of the function for it
/// (`crate::factgen::checks`, `docs/ir.md` 6.9).
fn typeck_error(a: &Analysis, unit: usize, span: Span, block: &ast::Block) -> bool {
    a.diags.iter().any(|d| {
        d.unit == unit
            && d.code.as_str().starts_with("W01")
            && d.code != weft_syntax::diag::Code::W0118
            && d.span.lo >= span.lo
            && d.span.hi <= span.hi.max(block.span.hi)
    })
}

/// Builds one body, or tells why it has none.
fn body_outcome(
    a: &Analysis,
    unit: usize,
    t: &Tables,
    src: &Src<'_>,
    out: &mut Built,
    fields: &mut unset::PlaceFields,
) -> Outcome {
    if a.thir_decl_error.is_some() {
        return Outcome::NoIr(NoIr::DeclTypes);
    }
    if t.error || !src.decl_ok || typeck_error(a, unit, src.span, src.block) {
        return Outcome::NoIr(NoIr::TypeError);
    }
    if !t.conflicts.is_empty() {
        return Outcome::NoIr(NoIr::Conflict);
    }
    let Some(ret) = src.ret else {
        return Outcome::NoIr(NoIr::TypeError);
    };
    let unit_id = id_of(unit);
    // A body that the builder does not finish declares no function.
    let fns_before = out.program.fns.len();
    let envs_before = out.program.cap_envs.len();
    let id = BodyId(id_of(out.program.bodies.len()));
    let mut pending = closure::Pending::new(id.0, &out.program);
    let d = Decls {
        a,
        fns: &mut out.fns,
        items: &mut out.program.fns,
        cap_envs: &mut out.program.cap_envs,
        pending: &mut pending,
    };
    let mut b = Builder::new(t, &mut out.tys, fields, d, unit_id, ret, src.span);
    b.body_id = id;
    let result = b.body(src).map(|()| {
        let diags: Vec<Diagnostic> = b.diags.drain(..).collect();
        (b.finish(src.kind, src.span), diags)
    });
    let done = result.and_then(|(body, diags)| match closure::take_pending(pending) {
        Some(made) => Ok((body, diags, made)),
        None => unsupported(Construct::NoThir, src.span),
    });
    match done {
        Ok((body, diags, made)) => {
            out.diags.extend(diags.into_iter().map(|mut d| {
                d.unit = unit;
                d
            }));
            out.program.bodies.push(body);
            out.program.bodies.extend(made.bodies);
            out.program.closures.extend(made.closures);
            out.program.handlers.extend(made.handlers);
            out.program.scopes.extend(made.scopes);
            out.program.spawns.extend(made.spawns);
            if let BodyKind::Fn(f) = src.kind {
                if let Some(d) = out.program.fns.get_mut(f.index()) {
                    d.body = Some(id);
                }
            }
            Outcome::Built(id)
        }
        Err(stop) => {
            out.program.cap_envs.truncate(envs_before);
            if out.program.fns.len() > fns_before {
                out.program.fns.truncate(fns_before);
                out.fns.retain(|_, v| v.index() < fns_before);
            }
            match stop {
                Stop::Unsupported(u) => Outcome::Unsupported(u),
                Stop::NoIr(n) => Outcome::NoIr(n),
            }
        }
    }
}

/// Returns the declaration of function `f`, and false if a type of its
/// signature has no final type (the declaration then has `()` there).
///
/// The stated row of an extern function is its full row: it has no body to
/// infer more. An extern function that the runtime can make fail (`raises`)
/// with an empty row gets no stated row, so its calls get an `unwind` block
/// (V10).
fn fn_decl(a: &Analysis, tys: &mut TyTable, f: crate::FnId) -> (FnDecl, bool) {
    let mut ok = true;
    let (Some(def), Some(sig)) = (a.program.fns.get(f.index()), a.sigs.get(f.index())) else {
        return (
            FnDecl {
                name: String::new(),
                body: None,
                params: Vec::new(),
                ret: tys.unit(),
                generics: 0,
                stated_row: None,
                intrinsic: None,
            },
            false,
        );
    };
    let mut ty = |t: &crate::types::Ty| {
        crate::types::final_ty(&a.program, tys, t).unwrap_or_else(|_| {
            ok = false;
            tys.unit()
        })
    };
    let params = sig.params.iter().map(|p| ty(&p.ty)).collect();
    let ret = ty(&sig.ret);
    let stated_row = sig.declared.then(|| stated_effects(a, sig));
    let raises = def.decl.body.is_none() && sig.effects.raises;
    let stated_row = stated_row.filter(|r| !(raises && r.is_empty()));
    let intrinsic = intrinsic(a, def);
    (
        FnDecl {
            name: def.path.clone(),
            body: None,
            params,
            ret,
            generics: id_of(sig.generics.len()),
            stated_row,
            intrinsic,
        },
        ok,
    )
}

/// Returns the effects that signature `sig` states.
fn stated_effects(a: &Analysis, sig: &crate::program::FnSig) -> Vec<EffectId> {
    sig.effects
        .named
        .iter()
        .filter_map(|n| crate::effects::by_identity(&a.program, n))
        .map(|e| EffectId(id_of(e.index())))
        .collect()
}

/// Returns the run-time meaning of function `def`, if it has one.
fn intrinsic(a: &Analysis, def: &crate::program::FnDef) -> Option<Intrinsic> {
    match (def.is_std, def.decl.body.is_none(), def.path.as_str()) {
        (true, true, "with_timeout") => Some(Intrinsic::WithTimeout),
        // The path of `sim.run` is `run` in the module `sim`.
        (true, true, "run") if is_sim(a, def.module) => Some(Intrinsic::SimRun),
        _ => None,
    }
}

/// Returns the declarations of `d` for a builder of a nested body.
const fn reborrow<'b>(d: &'b mut Decls<'_>) -> Decls<'b> {
    Decls {
        a: d.a,
        fns: &mut *d.fns,
        items: &mut *d.items,
        cap_envs: &mut *d.cap_envs,
        pending: &mut *d.pending,
    }
}

/// Returns true if module `m` is the standard module `sim`.
fn is_sim(a: &Analysis, m: crate::ids::ModId) -> bool {
    a.program
        .mods
        .get(m.index())
        .is_some_and(|d| d.is_std && d.name == "sim")
}

/// The return slot `_0`.
const RET: LocalId = LocalId(0);

/// Why the builder stops on a body: a construct that it does not lower, or
/// a reason for no IR (`docs/ir.md` 5.36).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Stop {
    /// A construct that the builder does not lower.
    Unsupported(Unsupported),
    /// The body gets no IR.
    NoIr(NoIr),
}

/// A result of the builder: a value, or why the builder stops on the body.
type R<T> = Result<T, Stop>;

/// Returns the result for construct `c` at `span`.
const fn unsupported<T>(c: Construct, span: Span) -> R<T> {
    Err(Stop::Unsupported(Unsupported { construct: c, span }))
}

/// Returns the result for a body with no IR for reason `n`.
const fn no_ir<T>(n: NoIr) -> R<T> {
    Err(Stop::NoIr(n))
}

/// What a scope is (`docs/ir.md` 5.1.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ScopeKind {
    /// The body: the parameters and the temporaries of the tail.
    Frame,
    /// A block `{ }`: its `let` locals.
    Block,
    /// A statement: its temporaries.
    Stmt,
    /// A loop: the iterator of a `for`, and the targets of `break` and
    /// `continue`.
    Loop(Targets),
    /// A handled body, a clause or a scope body: no jump can cross it
    /// (W0315).
    Fence(Fence),
}

/// The targets of the jumps of a loop: block indexes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Targets {
    /// The block after the loop: the target of `break`.
    exit: usize,
    /// The loop head: the target of `continue` and of the back edge.
    head: usize,
}

/// A body that a jump cannot leave (`docs/ir.md` 5.1.5). A handled body and
/// a clause open one (`handle.rs`), and so does a scope body (`task.rs`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Fence {
    /// The handled body of a `handle`.
    Handled,
    /// A handler clause.
    Clause,
    /// The body of a `scope`.
    ScopeBody,
}

impl Fence {
    /// Returns the name of the body in a diagnostic.
    const fn name(self) -> &'static str {
        match self {
            Self::Handled => "handled body",
            Self::Clause => "handler clause",
            Self::ScopeBody => "scope body",
        }
    }
}

/// One scope of the stack.
#[derive(Clone, Debug)]
struct Scope {
    /// What the scope is.
    kind: ScopeKind,
    /// The locals that get a cell in the scope, in order.
    locals: Vec<LocalId>,
    /// The location of the end of the scope: the `Dead` statements get it.
    end: Span,
    /// The part of the cleanup chain that the locals of the scope add, for
    /// the locals that are not temporaries and for the temporaries
    /// (`cleanup.rs`).
    chain: [ChainPart; 2],
}

/// The part of a cleanup chain that the locals of one class of one scope
/// add (`cleanup.rs`). The locals of a scope only grow, so the next chain
/// from the same block below adds only the new locals.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ChainPart {
    /// The count of locals of the scope that the part has seen.
    seen: usize,
    /// The locals of the class, in order.
    members: Vec<LocalId>,
    /// The block of the chain below the part, and the count of members
    /// in the part; `None` before the first chain.
    built: Option<(usize, usize)>,
    /// The first block of the part.
    head: usize,
}

/// A block that the builder fills.
#[derive(Clone, Debug)]
struct Draft {
    /// The statements.
    stmts: Vec<Stmt>,
    /// The terminator, when the block is complete. A cleanup block with no
    /// terminator goes to the unwind exit.
    term: Option<Term>,
    /// An edge from a point that can run enters the block.
    live: bool,
    /// The block is on a cleanup path.
    cleanup: bool,
}

/// The declarations that the bodies share (`docs/ir.md` 3.2): the functions
/// and the capability environments of the program.
struct Decls<'a> {
    /// The analysis.
    a: &'a Analysis,
    /// The function of the program for each function of the analysis that
    /// has one.
    fns: &'a mut BTreeMap<crate::FnId, weft_ir::FnId>,
    /// The functions of the program.
    items: &'a mut Vec<FnDecl>,
    /// The capability environments of the program. A handled body and a
    /// closure with capability fields add one.
    cap_envs: &'a mut Vec<CapEnv>,
    /// The bodies, the closures and the handlers that the function makes
    /// (`closure.rs`, `handle.rs`).
    pending: &'a mut closure::Pending,
}

/// The builder of one body. The state is here, not in the frames of the
/// recursive functions, so that the recursion uses little stack.
struct Builder<'a> {
    /// The THIR tables of the body.
    t: &'a Tables,
    /// The final types.
    tys: &'a mut TyTable,
    /// The place fields of the full types.
    fields: &'a mut unset::PlaceFields,
    /// The unit of the body.
    unit: u32,
    /// The locals. `_0` is first.
    locals: Vec<LocalDecl>,
    /// The parameters.
    params: Vec<LocalId>,
    /// The blocks.
    blocks: Vec<Draft>,
    /// The block that gets the next statement. `None` after a terminator: the
    /// next statement starts a block that no edge enters.
    cur: Option<usize>,
    /// The current point can run: an edge from the entry reaches it.
    live: bool,
    /// The scopes, the innermost last.
    scopes: Vec<Scope>,
    /// The local of each binding.
    vars: BTreeMap<BindingId, LocalId>,
    /// The diagnostics of the builder (W0315).
    diags: Vec<Diagnostic>,
    /// The declarations that the bodies share.
    d: Decls<'a>,
    /// The capability environment of the current point.
    cap_env: CapEnvId,
    /// The cleanup blocks: the block that finishes a local and then goes to
    /// a block, by the local and that block (`cleanup.rs`).
    chains: HashMap<(LocalId, usize), usize>,
    /// The last block of each cleanup chain: the parameters, after
    /// `Dead(_0)` (index 0) or with no `Dead(_0)` (index 1: `_0` has a
    /// value and is first in the chain).
    chain_base: [Option<usize>; 2],
    /// `_0` has its value at the current point: the frame end and a
    /// `return` write it last (`docs/ir.md` 5.1.4, 5.1.6). Then `_0` is
    /// first in a cleanup chain.
    ret_value: bool,
    /// The continuation of a clause body: first in each cleanup chain
    /// (`docs/ir.md` 5.1.6).
    kont: Option<LocalId>,
    /// The continuation is `multi`.
    kont_multi: bool,
    /// The capability parameters: the capability local of a handled body.
    cap_params: Vec<(EffectId, LocalId)>,
    /// The capabilities that this body binds, with their places here: the
    /// capability local of a handled body, the capability fields of a
    /// closure environment, and the upvar locals of the capabilities of the
    /// site that the body uses (`caps.rs`).
    caps: Vec<(EffectId, Place)>,
    /// The locals and the capabilities of the site that a clause or a
    /// handled body can name (`upvar.rs`); `None` for another body.
    site: Option<Box<upvar::Site>>,
    /// The lexical parent: the body that makes this body.
    parent: Option<BodyId>,
    /// The unwind actions of the types of the body (`cleanup.rs`).
    unwinds: cleanup::UnwindTable,
    /// The id of this body in the program.
    body_id: BodyId,
    /// The captures of a closure body (`closure.rs`); `None` for another body.
    closure: Option<Box<closure::Captures>>,
    /// The views of the environment of a closure around this body: each
    /// upvar local of an environment, with the fields of the environment
    /// (`upvar.rs`, `docs/ir.md` 5.1.7).
    views: HashMap<LocalId, upvar::EnvFields>,
}

impl<'a> Builder<'a> {
    /// Makes a builder with `_0` of type `ret`.
    fn new(
        t: &'a Tables,
        tys: &'a mut TyTable,
        fields: &'a mut unset::PlaceFields,
        d: Decls<'a>,
        unit: u32,
        ret: TyId,
        span: Span,
    ) -> Self {
        let mut b = Self {
            t,
            tys,
            fields,
            unit,
            locals: Vec::new(),
            params: Vec::new(),
            blocks: vec![Draft {
                stmts: Vec::new(),
                term: None,
                live: true,
                cleanup: false,
            }],
            cur: Some(0),
            live: true,
            scopes: Vec::new(),
            vars: BTreeMap::new(),
            diags: Vec::new(),
            d,
            cap_env: CapEnvId(0),
            chains: HashMap::new(),
            chain_base: [None; 2],
            ret_value: false,
            kont: None,
            kont_multi: false,
            cap_params: Vec::new(),
            caps: Vec::new(),
            site: None,
            parent: None,
            unwinds: HashMap::new(),
            body_id: BodyId(0),
            closure: None,
            views: HashMap::new(),
        };
        let props = b.props(ret);
        b.locals.push(LocalDecl {
            ty: ret,
            kind: LocalKind::Return,
            name: None,
            props,
            in_place: false,
            origin: b.origin(span, None),
        });
        b
    }

    /// Returns the origin of `span` and expression `expr`.
    const fn origin(&self, span: Span, expr: Option<ExprId>) -> Origin {
        Origin {
            span: weft_ir::Span {
                unit: self.unit,
                lo: span.lo,
                hi: span.hi,
            },
            expr,
        }
    }

    /// Returns the properties of type `t`.
    fn props(&self, t: TyId) -> Props {
        crate::props::ir_props(self.tys, t)
    }

    /// Returns the properties of the local of binding `b` of type `t`: the
    /// properties of the type, and for a type with a function part also the
    /// modes that the analysis infers for the values of the binding
    /// (`docs/ir.md` 2.3, 5.22). A function type does not show that a value
    /// is a linear, nonportable or `once` closure: `let g = f`, a parameter or
    /// a pattern binding can hold one.
    ///
    /// `copy` does not change: it says how a read of the local runs (a copy
    /// or a move), and so the mode of a capture of it. The analysis joins the
    /// values of a variable over the whole body, also values that come later:
    /// a closure that captures `c` before `c = || eat(b)` shares the cell of
    /// `c` and calls the new value (late capture), so the read must stay a
    /// copy. A local that holds a `once` value can so have `copy` and `once`:
    /// the facts take a call of it as a move from `once`, not from `copy`.
    fn binding_props_of(&self, b: BindingId, t: TyId) -> Props {
        let mut p = self.props(t);
        if !self.tys.mentions_fn(t) {
            return p;
        }
        let Some(v) = self.t.binding_of(b).map(|x| x.value) else {
            return p;
        };
        p.linear |= v.linear;
        p.on_abort &= !v.no_on_abort;
        p.nonportable |= v.nonportable;
        p.once |= v.once;
        p
    }

    /// Returns the type of local `l`.
    fn local_ty(&self, l: LocalId) -> TyId {
        self.locals
            .get(l.index())
            .map_or_else(|| self.tys.unit(), |d| d.ty)
    }

    /// Adds a local and returns its id.
    fn add_local(&mut self, d: LocalDecl) -> LocalId {
        let id = LocalId(id_of(self.locals.len()));
        self.locals.push(d);
        id
    }

    /// Returns the index of the block that gets the next statement. After a
    /// terminator it starts a new block that no edge enters.
    fn block_index(&mut self) -> usize {
        if let Some(c) = self.cur {
            return c;
        }
        let c = self.new_block();
        self.cur = Some(c);
        c
    }

    /// Adds an empty block and returns its index. No edge enters it yet.
    fn new_block(&mut self) -> usize {
        let c = self.blocks.len();
        self.blocks.push(Draft {
            stmts: Vec::new(),
            term: None,
            live: false,
            cleanup: false,
        });
        c
    }

    /// Makes block `b` the block that gets the next statement. The point can
    /// run if an edge from a point that can run enters the block. Each edge
    /// into `b` is in the blocks before this call, but for the back edges of
    /// a loop head (`looping.rs`). A back edge comes from a point that the
    /// head reaches, so it cannot make the head live.
    fn enter(&mut self, b: usize) {
        self.cur = Some(b);
        self.live = self.blocks.get(b).is_some_and(|d| d.live);
    }

    /// Ends the current block with `Goto(b)` if the point can run. Else a
    /// block that no edge enters ends with `Unreachable`.
    fn goto(&mut self, b: usize, origin: Origin) {
        if self.live {
            self.terminate(TermKind::Goto(BlockId(id_of(b))), origin);
        } else if self.cur.is_some() {
            self.terminate(TermKind::Unreachable, origin);
        }
    }

    /// Adds statement `kind` with `origin` at the current point.
    fn push(&mut self, kind: StmtKind, origin: Origin) {
        let c = self.block_index();
        if let Some(b) = self.blocks.get_mut(c) {
            b.stmts.push(Stmt { kind, origin });
        }
    }

    /// Adds `place = rv` with `origin`.
    fn assign(&mut self, place: Place, rv: Rvalue, origin: Origin) {
        self.push(StmtKind::Assign(place, rv), origin);
    }

    /// Ends the current block with terminator `kind`. The point after it is
    /// not live: no edge comes to it.
    fn terminate(&mut self, kind: TermKind, origin: Origin) {
        let c = self.block_index();
        if self.live {
            for s in kind.successors() {
                if let Some(d) = self.blocks.get_mut(s.index()) {
                    d.live = true;
                }
            }
        }
        if let Some(b) = self.blocks.get_mut(c) {
            b.term = Some(Term { kind, origin });
        }
        self.cur = None;
        self.live = false;
    }

    /// Opens a scope of kind `kind` that ends at `end`.
    fn open(&mut self, kind: ScopeKind, end: Span) {
        self.scopes.push(Scope {
            kind,
            locals: Vec::new(),
            end,
            chain: [ChainPart::default(), ChainPart::default()],
        });
    }

    /// Adds a temporary of type `ty` with `Live` at the current point. It goes
    /// into the innermost statement scope or frame scope: a block tail is not
    /// a statement, so its temporaries belong to the scope around the block
    /// (`docs/ir.md` 5.1.2).
    fn temp(&mut self, ty: TyId, kind: TempKind, origin: Origin) -> LocalId {
        let l = self.loose_temp(ty, kind, origin);
        if let Some(s) = self
            .scopes
            .iter_mut()
            .rev()
            .find(|s| matches!(s.kind, ScopeKind::Stmt | ScopeKind::Frame))
        {
            s.locals.push(l);
        }
        l
    }

    /// Adds a promoted temporary of type `ty` (`docs/ir.md` 5.10) with
    /// `Live` at the current point. It goes into the frame scope: its `Dead`
    /// is at each exit of the frame, and no cleanup chain lists it.
    fn promoted_temp(&mut self, ty: TyId, origin: Origin) -> LocalId {
        let l = self.loose_temp(ty, TempKind::Promoted, origin);
        if let Some(s) = self
            .scopes
            .iter_mut()
            .rev()
            .find(|s| matches!(s.kind, ScopeKind::Frame))
        {
            s.locals.push(l);
        }
        l
    }

    /// Adds a temporary of type `ty` with `Live` at the current point, in no
    /// scope: the caller writes its `Dead` on each path (the tests of a
    /// `match`).
    fn loose_temp(&mut self, ty: TyId, kind: TempKind, origin: Origin) -> LocalId {
        let props = self.props(ty);
        let l = self.add_local(LocalDecl {
            ty,
            kind: LocalKind::Temp(kind),
            name: None,
            props,
            in_place: false,
            origin,
        });
        self.push(StmtKind::Live(l), origin);
        l
    }

    /// Adds the local of binding `b` with `Live` at the current point. It goes
    /// into the innermost block scope.
    fn user_local(&mut self, b: BindingId, span: Span) -> R<LocalId> {
        let Some(binding) = self.t.binding_of(b) else {
            return unsupported(Construct::NoThir, span);
        };
        let (ty, name) = (binding.ty, binding.name.clone());
        let origin = self.origin(span, None);
        let props = self.binding_props_of(b, ty);
        let l = self.add_local(LocalDecl {
            ty,
            kind: LocalKind::User,
            name: Some(name),
            props,
            in_place: false,
            origin,
        });
        self.vars.insert(b, l);
        self.push(StmtKind::Live(l), origin);
        if let Some(s) = self
            .scopes
            .iter_mut()
            .rev()
            .find(|s| matches!(s.kind, ScopeKind::Block | ScopeKind::Frame))
        {
            s.locals.push(l);
        }
        Ok(l)
    }

    /// Makes the body of kind `kind` from the blocks.
    fn finish(self, kind: BodyKind, span: Span) -> Body {
        let origin = self.origin(span, None);
        let unwind_exit = BlockId(id_of(self.blocks.len()));
        let mut blocks: Vec<Block> = self
            .blocks
            .into_iter()
            .map(|d| Block {
                stmts: d.stmts,
                // Each normal block gets its terminator before the end; a
                // block with none would be a bug, and `Unreachable` keeps the
                // IR valid. The last block of a cleanup chain goes to the
                // unwind exit.
                term: d.term.unwrap_or(Term {
                    kind: if d.cleanup {
                        TermKind::Goto(unwind_exit)
                    } else {
                        TermKind::Unreachable
                    },
                    origin,
                }),
                cleanup: d.cleanup,
            })
            .collect();
        blocks.push(Block {
            stmts: Vec::new(),
            term: Term {
                kind: TermKind::UnwindExit,
                origin,
            },
            cleanup: true,
        });
        Body {
            kind,
            parent: self.parent,
            locals: self.locals,
            ret: RET,
            params: self.params,
            caps: self.cap_params,
            kont: self.kont.map(|k| (k, self.kont_multi)),
            blocks,
            entry: BlockId(0),
            unwind_exit,
            cap_env: self.cap_env,
            origin,
        }
    }
}
