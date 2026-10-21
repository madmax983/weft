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
//! The builder grows one construct group at a time (plan stages B3 to B11). A
//! construct that a later stage lowers gives [`Outcome::Unsupported`] with the
//! construct, never a panic. A body with a `typeck` error gets no IR
//! ([`Outcome::NoIr`]).
//!
//! The builder runs the verifier ([`weft_ir::verify::verify_program`]) on the
//! program that it makes, and keeps each broken rule in [`Built::broken`]. A
//! broken rule is a bug of the builder.

mod expr;
mod frame;
mod place;
mod stmt;

use std::collections::BTreeMap;
use std::fmt::Write as _;

use weft_ir::verify::{verify_program, Broken};
use weft_ir::{
    Block, BlockId, Body, BodyId, BodyKind, CapEnv, CapEnvId, ExprId, FnDecl, Intrinsic, LocalDecl,
    LocalId, LocalKind, Origin, Place, Program, Props, Rvalue, Stmt, StmtKind, TempKind, Term,
    TermKind, TestDecl, TestId, TyId, TyTable,
};
use weft_syntax::ast::{self, Span};

use crate::thir::{BindingId, Tables};
use crate::Analysis;

/// A construct that the builder does not lower yet. Each one names the plan
/// stage that lowers it ([`Construct::stage`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Construct {
    /// An assignment whose target is not a place.
    AssignPlace,
    /// A move of a value that is not plain data through a reference: W0303
    /// (`docs/ir.md` 5.36). The verifier rejects the `Move` (V9) and the
    /// `Copy` that 5.36 names.
    MoveThroughRef,
    /// The payload of a variant as a place: `o.Some` (a test of the variant
    /// comes first).
    VariantField,
    /// `if`.
    If,
    /// `&&` or `||`.
    AndOr,
    /// `match`.
    Match,
    /// A `let` with a pattern that is not a name or `_`.
    LetPattern,
    /// A `let` with no value: `let x: T`.
    LetUninit,
    /// `while`.
    While,
    /// `for`.
    For,
    /// `loop`.
    Loop,
    /// `break`.
    Break,
    /// `continue`.
    Continue,
    /// A range `a..b`.
    Range,
    /// A call.
    Call,
    /// A method call.
    MethodCall,
    /// A tuple.
    Tuple,
    /// An array or a `Vec` literal.
    Array,
    /// A struct literal.
    StructLit,
    /// `assert`.
    Assert,
    /// A name that is not a local: a function item, a variant, a path.
    ItemName,
    /// A closure.
    Closure,
    /// `handle`.
    Handle,
    /// `scope`.
    Scope,
    /// The THIR has no type or no binding for a part of the body.
    NoThir,
}

impl Construct {
    /// Returns the name of the construct.
    pub const fn name(self) -> &'static str {
        match self {
            Self::AssignPlace => "assignment to a value",
            Self::MoveThroughRef => "move through a reference",
            Self::VariantField => "variant field",
            Self::If => "if",
            Self::AndOr => "&& or ||",
            Self::Match => "match",
            Self::LetPattern => "let pattern",
            Self::LetUninit => "let with no value",
            Self::While => "while",
            Self::For => "for",
            Self::Loop => "loop",
            Self::Break => "break",
            Self::Continue => "continue",
            Self::Range => "range",
            Self::Call => "call",
            Self::MethodCall => "method call",
            Self::Tuple => "tuple",
            Self::Array => "array",
            Self::StructLit => "struct literal",
            Self::Assert => "assert",
            Self::ItemName => "item name",
            Self::Closure => "closure",
            Self::Handle => "handle",
            Self::Scope => "scope",
            Self::NoThir => "no THIR entry",
        }
    }

    /// Returns the plan stage that lowers the construct.
    pub const fn stage(self) -> &'static str {
        match self {
            Self::AssignPlace | Self::MoveThroughRef => "B12",
            Self::If
            | Self::AndOr
            | Self::Match
            | Self::LetPattern
            | Self::LetUninit
            | Self::VariantField => "B5",
            Self::While | Self::For | Self::Loop | Self::Break | Self::Continue | Self::Range => {
                "B6"
            }
            Self::Call
            | Self::MethodCall
            | Self::Tuple
            | Self::Array
            | Self::StructLit
            | Self::Assert
            | Self::ItemName => "B7",
            Self::Closure => "B9",
            Self::Handle => "B10",
            Self::Scope => "B11",
            Self::NoThir => "T3",
        }
    }
}

/// A body that the builder does not lower yet: the first construct of a later
/// stage that it finds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unsupported {
    /// The construct.
    pub construct: Construct,
    /// Its location in the unit of the body.
    pub span: Span,
}

/// Why a body gets no IR (`docs/ir.md` 5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NoIr {
    /// The body has a `typeck` error: a W01xx diagnostic, or the error type.
    TypeError,
    /// The declarations of the program have no final types.
    DeclTypes,
    /// The THIR tables of the body have a conflict.
    Conflict,
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
}

/// Returns the text of the IR of `b`.
///
/// The text is the program as [`weft_ir::print`] prints it, then one comment
/// line for each body that has no IR. `at` gives the text of a location in a
/// unit (for example `line:column`).
pub fn text(b: &Built, at: &dyn Fn(usize, Span) -> String) -> String {
    let mut s = weft_ir::print::print_program(&b.program, &b.tys);
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
                let why = match n {
                    NoIr::TypeError => "a type error",
                    NoIr::DeclTypes => "the declarations have no final types",
                    NoIr::Conflict => "a conflict in the THIR tables",
                };
                let _ = writeln!(s, "// {}: no IR: {why}", e.name);
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
    };
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
                let outcome = body_outcome(a, b.unit, t, &src, &mut out);
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
/// block `block` of unit `unit` (the rule of test D0).
fn typeck_error(a: &Analysis, unit: usize, span: Span, block: &ast::Block) -> bool {
    a.diags.iter().any(|d| {
        d.unit == unit
            && d.code.as_str().starts_with("W01")
            && d.span.lo >= span.lo
            && d.span.hi <= span.hi.max(block.span.hi)
    })
}

/// Builds one body, or tells why it has none.
fn body_outcome(a: &Analysis, unit: usize, t: &Tables, src: &Src<'_>, out: &mut Built) -> Outcome {
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
    let mut b = Builder::new(t, &mut out.tys, unit_id, ret, src.span);
    match b.body(src) {
        Ok(()) => {
            let id = BodyId(id_of(out.program.bodies.len()));
            let body = b.finish(src.kind, src.span);
            out.program.bodies.push(body);
            if let BodyKind::Fn(f) = src.kind {
                if let Some(d) = out.program.fns.get_mut(f.index()) {
                    d.body = Some(id);
                }
            }
            Outcome::Built(id)
        }
        Err(u) => Outcome::Unsupported(u),
    }
}

/// Returns the declaration of function `f`, and false if a type of its
/// signature has no final type (the declaration then has `()` there).
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
    let stated_row = sig.declared.then(|| {
        sig.effects
            .named
            .iter()
            .filter_map(|n| crate::effects::by_identity(&a.program, n))
            .map(|e| weft_ir::EffectId(id_of(e.index())))
            .collect()
    });
    let intrinsic = match (def.is_std, def.decl.body.is_none(), def.path.as_str()) {
        (true, true, "with_timeout") => Some(Intrinsic::WithTimeout),
        (true, true, "sim.run") => Some(Intrinsic::SimRun),
        _ => None,
    };
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

/// The return slot `_0`.
const RET: LocalId = LocalId(0);

/// A result of the builder: a value, or the construct that the builder does
/// not lower yet.
type R<T> = Result<T, Unsupported>;

/// Returns the result for construct `c` at `span`.
const fn unsupported<T>(c: Construct, span: Span) -> R<T> {
    Err(Unsupported { construct: c, span })
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
}

/// A block that the builder fills.
#[derive(Clone, Debug)]
struct Draft {
    /// The statements.
    stmts: Vec<Stmt>,
    /// The terminator, when the block is complete.
    term: Option<Term>,
}

/// The builder of one body. The state is here, not in the frames of the
/// recursive functions, so that the recursion uses little stack.
struct Builder<'a> {
    /// The THIR tables of the body.
    t: &'a Tables,
    /// The final types.
    tys: &'a mut TyTable,
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
}

impl<'a> Builder<'a> {
    /// Makes a builder with `_0` of type `ret`.
    fn new(t: &'a Tables, tys: &'a mut TyTable, unit: u32, ret: TyId, span: Span) -> Self {
        let mut b = Self {
            t,
            tys,
            unit,
            locals: Vec::new(),
            params: Vec::new(),
            blocks: vec![Draft {
                stmts: Vec::new(),
                term: None,
            }],
            cur: Some(0),
            live: true,
            scopes: Vec::new(),
            vars: BTreeMap::new(),
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
        let c = self.blocks.len();
        self.blocks.push(Draft {
            stmts: Vec::new(),
            term: None,
        });
        self.cur = Some(c);
        c
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
        });
    }

    /// Adds a temporary of type `ty` with `Live` at the current point. It goes
    /// into the innermost scope that is not a block: a block tail is not a
    /// statement, so its temporaries belong to the scope around the block
    /// (`docs/ir.md` 5.1.2).
    fn temp(&mut self, ty: TyId, kind: TempKind, origin: Origin) -> LocalId {
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
        if let Some(s) = self
            .scopes
            .iter_mut()
            .rev()
            .find(|s| s.kind != ScopeKind::Block)
        {
            s.locals.push(l);
        }
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
        let props = self.props(ty);
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
        let mut blocks: Vec<Block> = self
            .blocks
            .into_iter()
            .map(|d| Block {
                stmts: d.stmts,
                // Each block gets its terminator before the end; a block with
                // none would be a bug, and `Unreachable` keeps the IR valid.
                term: d.term.unwrap_or(Term {
                    kind: TermKind::Unreachable,
                    origin,
                }),
                cleanup: false,
            })
            .collect();
        let unwind_exit = BlockId(id_of(blocks.len()));
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
            parent: None,
            locals: self.locals,
            ret: RET,
            params: self.params,
            caps: Vec::new(),
            kont: None,
            blocks,
            entry: BlockId(0),
            unwind_exit,
            cap_env: CapEnvId(0),
            origin,
        }
    }
}
