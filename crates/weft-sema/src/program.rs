//! Item collection, name resolution and signatures.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;
use std::sync::atomic::{AtomicUsize, Ordering};

use weft_syntax::ast::{
    self, EffectItem, ExternTypeDecl, File, FnDecl, Item, ItemKind, Mode, PlaceExpr, PlaceStep,
    Span, TypeExpr, TypeExprKind,
};
use weft_syntax::diag::{Diagnostic, ROOT_UNIT};

use crate::effects;
use crate::types::{AdtId, FnTy, IntTy, Ty};

/// An index into [`Program::fns`].
pub type FnId = usize;
/// An index into [`Program::mods`].
pub type ModId = usize;
/// An index into [`Program::effects`].
pub type EffectId = usize;

/// How a pointer type dereferences.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Deref {
    /// The target never moves: references through it survive mutation.
    Stable,
    /// A mutation can replace the target, as for a reassignable `Box`.
    Unstable,
    /// The target is in the `rc` group of its type.
    Group,
}

/// A struct field.
#[derive(Clone, Debug)]
pub struct FieldDef {
    /// The field name.
    pub name: String,
    /// The field type, with type parameters.
    pub ty: Ty,
    /// For a reference field of a `!Move` struct: the place in terms of `self`.
    pub place: Option<SigPlace>,
    /// The declaration.
    pub span: Span,
}

/// An enum variant.
#[derive(Clone, Debug)]
pub struct VariantDef {
    /// The variant name.
    pub name: String,
    /// The payload types, with type parameters.
    pub fields: Vec<Ty>,
}

/// The shape of a type definition.
#[derive(Clone, Debug)]
pub enum AdtKind {
    /// A struct.
    Struct(Vec<FieldDef>),
    /// An enum.
    Enum(Vec<VariantDef>),
    /// An extern type.
    Extern {
        /// The stability of `x[]`, if the type has elements.
        elem_unstable: Option<bool>,
        /// How `*x` works, if the type is a pointer.
        deref: Option<Deref>,
    },
}

/// A struct, enum or extern type.
#[derive(Clone, Debug)]
pub struct AdtDef {
    /// The name.
    pub name: String,
    /// Type parameter names.
    pub generics: Vec<String>,
    /// The shape.
    pub kind: AdtKind,
    /// The type is `linear`.
    pub linear: bool,
    /// The `on abort` function name.
    pub on_abort: Option<String>,
    /// The type has `on abort` (for extern types: the runtime provides it).
    pub has_on_abort: bool,
    /// The type is `!Move`.
    pub immovable: bool,
    /// The type is declared `copy` (extern types only).
    pub copy: bool,
    /// The type is declared `nonportable`.
    pub nonportable: bool,
    /// The module that declares it.
    pub module: ModId,
    /// The declaration.
    pub span: Span,
}

/// An effect operation.
#[derive(Clone, Debug)]
pub struct OpDef {
    /// The name.
    pub name: String,
    /// The parameter types.
    pub params: Vec<Ty>,
    /// The parameter names.
    pub param_names: Vec<String>,
    /// The return type.
    pub ret: Ty,
    /// The operation is `multi`.
    pub multi: bool,
    /// The location of the operation.
    pub span: Span,
}

/// An effect.
#[derive(Clone, Debug)]
pub struct EffectDef {
    /// The name as the source writes it. `effects::identity` is the name in the facts.
    pub name: String,
    /// The module of the definition.
    pub module: ModId,
    /// The operations.
    pub ops: Vec<OpDef>,
    /// The effect is a standard effect.
    pub is_std: bool,
    /// The effect is `pub`: another unit can name it.
    pub is_pub: bool,
}

impl EffectDef {
    /// Returns true if some operation is `multi`.
    pub fn has_multi(&self) -> bool {
        self.ops.iter().any(|o| o.multi)
    }
}

/// The root of a place in a signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SigRoot {
    /// A parameter, by index.
    Param(usize),
    /// The `rc` group of a type.
    Group(AdtId),
}

/// One step of a place in a signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SigStep {
    /// A fixed step.
    Step(weft_facts::Step, String),
    /// The wildcard step `..`: any place at or below.
    Wild,
    /// The places that the references at or below the place point into. It
    /// comes first, after a reference parameter. A caller puts in the places that
    /// the references in its argument point into (ADR 0003).
    Held,
    /// A split side at the parameter with this index.
    Seg {
        /// The parameter that names the split point.
        label: usize,
        /// True for `[k..]`.
        hi: bool,
        /// The stability of the element step.
        unstable: bool,
    },
}

/// A place written in a signature, resolved against the parameter types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SigPlace {
    /// The root.
    pub root: SigRoot,
    /// The steps.
    pub steps: Vec<SigStep>,
    /// The text, for diagnostics.
    pub text: String,
}

/// A parameter of a signature.
#[derive(Clone, Debug)]
pub struct ParamSig {
    /// The name.
    pub name: String,
    /// The type, with type parameters.
    pub ty: Ty,
    /// The place of a reference parameter with `in`.
    pub place: Option<SigPlace>,
    /// The parameter is `@ shared`.
    pub shared: bool,
    /// The parameter is `@ uniq`.
    pub uniq: bool,
    /// The location.
    pub span: Span,
}

/// The place of a reference in the return value.
#[derive(Clone, Debug)]
pub struct RetPlace {
    /// Tuple indices from the return value to the reference.
    pub path: Vec<usize>,
    /// The place.
    pub place: SigPlace,
    /// The reference is `@ uniq`.
    pub uniq: bool,
}

/// How a body runs one of its function parameters as a task or a fork branch
/// (`EffectSig::task_runs`). A caller checks the function value that it gives
/// there as a task at the call (ADR 0006).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TaskRun {
    /// The body can run it on another thread: in a fork branch, or in foreign
    /// code. Then it must be portable (W0401, W0403).
    pub thread: bool,
    /// The body can run it two times at one time: in two tasks, in a task that
    /// starts again while it runs, or in a task and at a node while it runs.
    pub twice: bool,
    /// The other function parameters that the body can run while it runs.
    pub with: BTreeSet<usize>,
    /// The places of the parameters that the body, or another task of it, can
    /// write while it runs.
    pub writes: Vec<SigPlace>,
    /// The places of the parameters that the body, or another task of it, can
    /// read while it runs.
    pub reads: Vec<SigPlace>,
}

/// A place that a function gives to one of its function parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LentPlace {
    /// The function parameter.
    pub param: usize,
    /// The argument position in the call of the parameter, or `None` for any position.
    pub arg: Option<usize>,
    /// The place, or `None` for a place that the caller cannot name: then it can be
    /// any place that the reference arguments reach.
    pub place: Option<SigPlace>,
}

/// A place that the body gives to a function value that it does not know.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GivenPlace {
    /// The argument position in the call of the value, or `None` for any position.
    pub arg: Option<usize>,
    /// The place, or `None` for a place that the caller cannot name: then it can be
    /// any place that the reference arguments reach.
    pub place: Option<SigPlace>,
}

/// What a call of a function value in the result does, in the places of the parameters.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RetFn {
    /// Places that the call mutates.
    pub muts: Vec<SigPlace>,
    /// Places that the call reads.
    pub reads: Vec<SigPlace>,
    /// Places that the call mutates through the parameters of the value.
    /// `SigRoot::Param(i)` is parameter `i` of the value, not of the function.
    pub arg_muts: Vec<SigPlace>,
    /// Places that the call gives to code that can mutate through them: a function
    /// parameter of the function, or a value that the function does not know.
    pub lends: Vec<SigPlace>,
    /// The same, through the parameters of the value, as in `arg_muts`.
    pub arg_lends: Vec<SigPlace>,
    /// Named effects. The call site of the function resolves them.
    pub named: BTreeSet<String>,
    /// Function parameters of the function that the call can call.
    pub passthrough: BTreeSet<usize>,
    /// Function items that the call can call.
    pub items: BTreeSet<FnId>,
    /// The call can abort.
    pub abort: bool,
    /// The call can resume a `multi` continuation more than once.
    pub multi: bool,
    /// The call can call a function value that the function does not know.
    pub unknown: bool,
    /// Parameters of the value that the call gives to an operation of a handler
    /// at the call site of the function, with the effect.
    pub op_fns: BTreeSet<(usize, String)>,
    /// Parameters of the value that a task of the call can call.
    pub tasks: BTreeSet<usize>,
    /// Function parameters of the function that the call can call more than
    /// once. A caller runs the value two times in a row where it calls it.
    pub repeats: BTreeSet<usize>,
}

/// The effect part of a signature.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EffectSig {
    /// `mut(...)` places.
    pub muts: Vec<SigPlace>,
    /// Named effects, canonical and expanded (for example `io` becomes its members).
    pub named: BTreeSet<String>,
    /// Function parameters whose effects pass through to the caller.
    pub passthrough: BTreeSet<usize>,
    /// The places that the body gives to its function parameters. A closure
    /// argument can mutate through them. The body always infers this part.
    pub lent: Vec<LentPlace>,
    /// What a call of a returned function value does. The body always infers this part.
    pub ret: Option<Box<RetFn>>,
    /// Function parameters that the body stores, for example in a struct field. A
    /// later call can run them. The body always infers this part.
    pub stores: BTreeSet<usize>,
    /// The body can run a function value that the caller stores: it calls a function
    /// value that it does not know, or a function that can. The body always infers this part.
    pub reaches: bool,
    /// The places that the body gives to such a function value. The body always
    /// infers this part.
    pub reach_given: Vec<GivenPlace>,
    /// The body can run such a function value more than once: at two nodes, in a
    /// loop or in a closure. The body always infers this part.
    pub reach_repeats: bool,
    /// The body calls a function value that it does not know, and that call can
    /// resume a `multi` continuation more than once. The body always infers this part.
    pub multi: bool,
    /// Function parameters that a task or a fork branch of the body can call. The
    /// body always infers this part.
    pub tasks: BTreeSet<usize>,
    /// The function parameters that the body runs as a task or a fork branch,
    /// and how. The body always infers this part.
    pub task_runs: BTreeMap<usize, TaskRun>,
    /// The body can start a pinned task for a reason that a caller does not
    /// see: the task captures a nonportable value, writes through a shared
    /// reference, runs a function value that the body does not follow, or
    /// starts such a task. A task that calls the function is pinned too. The
    /// body always infers this part.
    pub pins: bool,
    /// Function parameters that the body gives to an operation of a handler of a
    /// caller, with the effect. The clause can call or keep them. The body always
    /// infers this part.
    pub op_fns: BTreeSet<(usize, String)>,
    /// The function values that the body gives to an operation of a handler of a
    /// caller can perform effects through a handler of a caller. Each pair has the
    /// effect of the operation and the performed effect. A clause can run such a
    /// value as a task (W0314). The body always infers this part.
    pub op_effects: BTreeSet<(String, String)>,
    /// Effects that a task or a fork branch of the body performs through a handler
    /// of a caller. The body always infers this part.
    pub task_effects: BTreeSet<String>,
    /// Function parameters that the body can call more than once. The body always
    /// infers this part.
    pub repeats: BTreeSet<usize>,
    /// Reference parameters whose pointee can get a function value from the body,
    /// for example a copy out of another argument. The body always infers this part.
    pub fn_stores: BTreeSet<usize>,
    /// The places that the function values in the result point into, in the
    /// places of the parameters: what a returned closure captures. `None` for a
    /// result that holds no function value, and for a function with no body:
    /// a caller takes a place anywhere inside each reference argument. The body
    /// always infers this part.
    pub ret_refs: Option<Vec<SigPlace>>,
    /// The parameters whose references the body can put into an `rc` object,
    /// each with the `rc` type: the parameter and the type definition. The
    /// object stays after the return, so a caller must not give a reference into
    /// its own local there (W0204). The body always infers this part.
    pub group_stores: BTreeSet<(usize, usize)>,
    /// The places that the closures that the body puts behind a reference
    /// parameter point into, in the places of the parameters. Each has the
    /// parameter and the place. A caller's argument there points into them too,
    /// as for a reference that the body puts there. The body always infers this
    /// part.
    pub fn_store_refs: Vec<(usize, SigPlace)>,
    /// Type parameters, by index in `FnSig::generics`, of the values that the
    /// body can drop. On some path, a value of such a type goes out of scope or
    /// gets a new value. A caller that gives a linear type there loses a value
    /// (W0601). The body always infers this part.
    pub drops: BTreeSet<usize>,
    /// Type parameters, by index in `FnSig::generics`, of the values that the
    /// body holds at a node that can abort or resume more than once. A caller
    /// that gives a linear type there holds a linear value across the call (W0602,
    /// W0503). The body always infers this part.
    pub holds: BTreeSet<usize>,
    /// The body can raise a failure that the runtime makes, with no `fail` in
    /// the row: a `join` of a failed task, a scope or a `fork` with a failed
    /// child, or a read of a file. A closure that the body makes and a callee
    /// count too. An `on abort` function cannot raise one (W0118). The body
    /// always infers this part.
    pub raises: bool,
}

impl EffectSig {
    /// Returns true if the row has no effect.
    pub fn is_empty(&self) -> bool {
        self.muts.is_empty() && self.named.is_empty() && self.passthrough.is_empty()
    }
}

/// A resolved function signature.
#[derive(Clone, Debug)]
pub struct FnSig {
    /// Type parameter names: the impl parameters first, then the function parameters.
    pub generics: Vec<String>,
    /// The parameters.
    pub params: Vec<ParamSig>,
    /// The return type.
    pub ret: Ty,
    /// The places of references in the return value.
    pub ret_places: Vec<RetPlace>,
    /// The effects.
    pub effects: EffectSig,
    /// True if the source states the effects.
    pub declared: bool,
}

/// A function or method.
#[derive(Clone, Debug)]
pub struct FnDef {
    /// The name.
    pub name: String,
    /// The qualified name, for diagnostics.
    pub path: String,
    /// The type that owns the method.
    pub owner: Option<AdtId>,
    /// The declaration.
    pub decl: FnDecl,
    /// The signature.
    pub sig: FnSig,
    /// The function is `pub`.
    pub is_pub: bool,
    /// The function is in the prelude or a standard module.
    pub is_std: bool,
    /// The module.
    pub module: ModId,
    /// The declaration span.
    pub span: Span,
}

/// A test block.
#[derive(Clone, Debug)]
pub struct TestDef {
    /// The name.
    pub name: String,
    /// The body.
    pub body: ast::Block,
    /// The module.
    pub module: ModId,
    /// The location.
    pub span: Span,
}

/// What a name refers to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemRef {
    /// A function.
    Fn(FnId),
    /// A type.
    Adt(AdtId),
    /// An effect.
    Effect(EffectId),
    /// A module.
    Mod(ModId),
}

/// A module: a namespace.
#[derive(Clone, Debug, Default)]
pub struct ModDef {
    /// The name.
    pub name: String,
    /// The parent module.
    pub parent: Option<ModId>,
    /// The items by name.
    pub items: HashMap<String, ItemRef>,
    /// The module is a standard module.
    pub is_std: bool,
    /// The source unit: [`PRELUDE_UNIT`](weft_syntax::diag::PRELUDE_UNIT),
    /// [`ROOT_UNIT`], or a dependency after them.
    pub unit: usize,
}

/// The whole program after item collection.
#[derive(Clone, Debug, Default)]
pub struct Program {
    /// Type definitions.
    pub adts: Vec<AdtDef>,
    /// Effects.
    pub effects: Vec<EffectDef>,
    /// Functions and methods.
    pub fns: Vec<FnDef>,
    /// Modules. Module 0 is the prelude.
    pub mods: Vec<ModDef>,
    /// Tests.
    pub tests: Vec<TestDef>,
    /// Methods by owner and name.
    pub methods: HashMap<(AdtId, String), FnId>,
    /// Enum variants by name, for unqualified constructors.
    pub variants: HashMap<String, Vec<(AdtId, usize)>>,
    /// The user root module.
    pub root: ModId,
    /// The definition behind raw pointer types `*T`. No module names it.
    pub ptr: Option<AdtId>,
    /// The type properties of the definitions (`Program::props`).
    pub props: std::sync::OnceLock<crate::props::TypeProps>,
    /// Each effect by its identity (`effects::by_identity`). Item collection
    /// sets it at its end, when the effects and the names of the modules are
    /// final.
    pub(crate) effect_index: Option<HashMap<String, EffectId>>,
    /// The steps of the item checks: the work list of the size check, the walks
    /// of the `in` places and the modes of the mode checks ([`Program::item_steps`]).
    steps: StepCount,
}

/// A count of steps that a shared reference can add to. It is atomic, so that
/// a [`Program`] can go to another thread.
#[derive(Debug, Default)]
struct StepCount(AtomicUsize);

impl Clone for StepCount {
    fn clone(&self) -> Self {
        Self(AtomicUsize::new(self.0.load(Ordering::Relaxed)))
    }
}

/// The prelude module.
pub const PRELUDE: ModId = 0;

/// The name of the definition behind `*T`. It is not an identifier, so no
/// program can name it.
pub const PTR_NAME: &str = "*";

/// Returns the span of the first raw pointer type in `t`.
fn ptr_span(t: &TypeExpr) -> Option<Span> {
    match &t.kind {
        TypeExprKind::Ptr(_) => Some(t.span),
        TypeExprKind::Ref { inner, .. }
        | TypeExprKind::Array { elem: inner, .. }
        | TypeExprKind::Slice(inner) => ptr_span(inner),
        TypeExprKind::Path { args: ts, .. } | TypeExprKind::Tuple(ts) => {
            ts.iter().find_map(ptr_span)
        }
        TypeExprKind::Fn { params, ret, .. } => {
            params.iter().chain(ret.as_deref()).find_map(ptr_span)
        }
        TypeExprKind::SelfType => None,
    }
}

/// Names of built-in type definitions that sema refers to.
#[derive(Clone, Debug, Default)]
pub struct Builtins {
    /// `Vec`.
    pub vec: Option<AdtId>,
    /// `Option`.
    pub option: Option<AdtId>,
    /// `String`.
    pub string: Option<AdtId>,
    /// `Duration`.
    pub duration: Option<AdtId>,
    /// `Task`.
    pub task: Option<AdtId>,
    /// `Rc`.
    pub rc: Option<AdtId>,
    /// `Box`.
    pub boxed: Option<AdtId>,
}

impl Program {
    /// The steps of the item checks so far. A test can put a limit on them.
    pub fn item_steps(&self) -> usize {
        self.steps.0.load(Ordering::Relaxed)
    }

    /// Adds `n` steps of an item check.
    pub(crate) fn add_steps(&self, n: usize) {
        let old = self.steps.0.load(Ordering::Relaxed);
        self.steps.0.store(old.saturating_add(n), Ordering::Relaxed);
    }

    /// Looks up a name from a module outward, then in the prelude.
    pub fn lookup(&self, module: ModId, name: &str) -> Option<ItemRef> {
        let mut m = Some(module);
        while let Some(id) = m {
            if let Some(r) = self.mods[id].items.get(name) {
                return Some(*r);
            }
            m = self.mods[id].parent;
        }
        self.mods[PRELUDE].items.get(name).copied()
    }

    /// Looks up a name inside one module only.
    pub fn lookup_in(&self, module: ModId, name: &str) -> Option<ItemRef> {
        self.mods[module].items.get(name).copied()
    }

    /// Finds the built-in definitions.
    pub fn builtins(&self) -> Builtins {
        let find = |n: &str| match self.mods[PRELUDE].items.get(n) {
            Some(ItemRef::Adt(a)) => Some(*a),
            _ => None,
        };
        Builtins {
            vec: find("Vec"),
            option: find("Option"),
            string: find("String"),
            duration: find("Duration"),
            task: find("Task"),
            rc: find("Rc"),
            boxed: find("Box"),
        }
    }

    /// Finds the effect operation that a bare call `name(...)` in module `m`
    /// performs. The search goes from `m` outward, as a name lookup does: the
    /// first module with a user effect that has the operation wins, and in one
    /// module the first such effect. Then come the effects of the prelude. Only
    /// the effects that `m` sees by name count. Sema and the interpreter both
    /// use it.
    pub fn find_op(&self, m: ModId, name: &str) -> Option<(EffectId, usize)> {
        self.ops_named(m, name).first().copied()
    }

    /// Returns each operation `name` of the first module, from `m` outward,
    /// that has one (see [`Program::find_op`]). More than one makes a bare call
    /// `name(...)` ambiguous (W0107).
    pub fn ops_named(&self, m: ModId, name: &str) -> Vec<(EffectId, usize)> {
        let op_in = |ei: EffectId| -> Option<(EffectId, usize)> {
            let e = &self.effects[ei];
            let oi = e.ops.iter().position(|o| o.name == name)?;
            (self.effect_named(m, &e.name) == Some(ei)).then_some((ei, oi))
        };
        let mut at = Some(m);
        while let Some(id) = at {
            let found: Vec<(EffectId, usize)> = (0..self.effects.len())
                .filter(|&ei| self.effects[ei].module == id && !self.effects[ei].is_std)
                .filter_map(op_in)
                .collect();
            if !found.is_empty() {
                return found;
            }
            at = self.mods[id].parent;
        }
        (0..self.effects.len())
            .filter(|&ei| self.effects[ei].is_std)
            .find_map(op_in)
            .into_iter()
            .collect()
    }

    /// Finds an effect by canonical name, from a module outward.
    pub fn effect_named(&self, module: ModId, name: &str) -> Option<EffectId> {
        match self.lookup(module, name) {
            Some(ItemRef::Effect(e)) => Some(e),
            _ => effects::by_identity(self, name),
        }
    }
}

/// One source unit for analysis.
#[derive(Clone, Debug)]
pub struct Unit {
    /// The module name. Empty for the root.
    pub name: String,
    /// The parsed file.
    pub file: File,
    /// The unit is standard code (the prelude).
    pub is_std: bool,
}

/// Collects the items of all units.
pub struct Collector {
    /// The program being built.
    pub prog: Program,
    /// Diagnostics.
    pub diags: Vec<Diagnostic>,
    pending_fns: Vec<(FnId, Option<AdtId>, Vec<String>)>,
    marked: usize,
    /// Each struct with `on abort`, and the written function name.
    on_aborts: Vec<(AdtId, ast::Ident)>,
}

impl Collector {
    /// Collects the prelude first, then the other units.
    pub fn collect(units: &[Unit]) -> (Program, Vec<Diagnostic>) {
        let mut c = Self {
            prog: Program::default(),
            diags: Vec::new(),
            pending_fns: Vec::new(),
            marked: 0,
            on_aborts: Vec::new(),
        };
        // Pass 1: names.
        let mut unit_mods = Vec::new();
        for (i, u) in units.iter().enumerate() {
            // A dependency sees its own items and the prelude, not the root.
            let m = c.new_mod(&u.name, None, u.is_std, i);
            if i == ROOT_UNIT {
                c.prog.root = m;
            }
            if i > ROOT_UNIT {
                c.name_dependency(&u.name, m, i);
            }
            unit_mods.push(m);
            let before = c.diags.len();
            c.declare_items(&u.file.items, m, u.is_std);
            for d in &mut c.diags[before..] {
                d.unit = i;
            }
        }
        c.declare_ptr();
        // Pass 2: bodies of type definitions and signatures. The diagnostics
        // of pass 1 have their units already.
        let mut seen = c.diags.len();
        c.marked = seen;
        for (i, (u, &m)) in units.iter().zip(&unit_mods).enumerate() {
            c.define_items(&u.file.items, m);
            c.declare_unit_mark(&mut seen, i);
        }
        c.check_sizes();
        c.resolve_signatures();
        c.check_on_aborts();
        c.check_op_names();
        // A duplicate definition (W0107) keeps the first effect, as the search does.
        let mut index = HashMap::new();
        for e in 0..c.prog.effects.len() {
            index.entry(effects::identity(&c.prog, e)).or_insert(e);
        }
        c.prog.effect_index = Some(index);
        (c.prog, c.diags)
    }

    /// W0107: an operation that no bare call `name(...)` can reach, in any
    /// module (RR15). A bare call finds `print` and `fork`, then an item (the
    /// prelude last), then a variant, and only then an operation
    /// (`Program::find_op`). The statement `assert(...)` is an assertion. So the
    /// operation is hidden everywhere if `print`, `fork`, `assert`, a function or
    /// a type of the prelude, or a variant of a prelude type has its name. The
    /// user does not write these names, so the hiding is silent.
    ///
    /// A name that the program declares hides an operation only by the scope
    /// rule: an item of a module hides an operation of an outer module in that
    /// module. That is not an error: the effect path reaches the operation. Two
    /// operations of one module with the same name make a bare call ambiguous:
    /// that is W0107 at the call (`Lower::call`).
    fn check_op_names(&mut self) {
        let mut found = Vec::new();
        for e in &self.prog.effects {
            if e.is_std {
                continue;
            }
            for o in &e.ops {
                let n = o.name.as_str();
                let hider = if matches!(n, "print" | "fork") {
                    Some(format!("the built-in function `{n}`"))
                } else if n == "assert" {
                    Some("the `assert` statement".to_string())
                } else {
                    match self.prog.mods[PRELUDE].items.get(n) {
                        Some(ItemRef::Fn(_)) => Some(format!("the prelude function `{n}`")),
                        Some(ItemRef::Adt(_)) => Some(format!("the prelude type `{n}`")),
                        _ => self
                            .prog
                            .variants
                            .get(n)
                            .into_iter()
                            .flatten()
                            .any(|&(a, _)| {
                                let m = self.prog.adts[a].module;
                                self.prog.mods[m].unit == weft_syntax::diag::PRELUDE_UNIT
                            })
                            .then(|| format!("the prelude variant `{n}`")),
                    }
                };
                if let Some(h) = hider {
                    found.push((e.module, e.name.clone(), o.name.clone(), o.span, h));
                }
            }
        }
        for (m, effect, name, span, hider) in found {
            let d = Diagnostic::error(
                "W0107",
                format!(
                    "operation `{name}` of `{effect}` has the name of {hider}, so no call `{name}(...)` reaches it"
                ),
                span,
            )
            .note(format!(
                "rename the operation: a bare call `{name}(...)` always finds {hider}"
            ));
            self.push_in(m, d);
        }
    }

    /// Adds a diagnostic in the unit of module `m`.
    fn push_in(&mut self, m: ModId, mut d: Diagnostic) {
        d.unit = self.prog.mods[m].unit;
        self.diags.push(d);
    }

    /// W0117: a struct that holds itself with no indirection has no finite
    /// size.
    fn check_sizes(&mut self) {
        let (bad, steps) = size_check(&self.prog);
        self.prog.add_steps(steps);
        for a in bad {
            let def = &self.prog.adts[a];
            let d = Diagnostic::error(
                "W0117",
                format!(
                    "struct `{}` holds itself with no indirection, so it has no finite size",
                    def.name
                ),
                def.span,
            )
            .note("put the field behind an indirection: an enum, `Box` or `Vec`");
            self.push_in(def.module, d);
        }
    }

    /// W0101 and W0118: the function after `on abort` must exist and take
    /// one value of the type.
    fn check_on_aborts(&mut self) {
        for (a, name) in std::mem::take(&mut self.on_aborts) {
            let (module, ty) = (self.prog.adts[a].module, self.prog.adts[a].name.clone());
            let d = match self.prog.lookup(module, &name.name) {
                Some(ItemRef::Fn(f)) => {
                    let params = &self.prog.fns[f].sig.params;
                    if matches!(params.as_slice(), [p] if matches!(p.ty, Ty::Adt(b, _) if b == a)) {
                        continue;
                    }
                    Diagnostic::error(
                        "W0118",
                        format!(
                            "`on abort = {}` needs a function that takes one `{ty}` value",
                            name.name
                        ),
                        name.span,
                    )
                    .note(format!("declare it as `fn {}(x: {ty})`", name.name))
                }
                _ => Diagnostic::error(
                    "W0101",
                    format!("unknown function `{}` after `on abort`", name.name),
                    name.span,
                ),
            };
            self.push_in(module, d);
        }
    }

    /// Gives the root the name of dependency module `m` of unit `unit`. The
    /// prelude declares nested modules first, so the root is not module 1.
    ///
    /// W0107: the name must not hide a name that the root sees already: an item
    /// of the root, a prelude item or a standard effect alias such as `log`. It
    /// must not be `main` either: the effect identities of the root start with
    /// `main` (`main.Note`), so the effects of a dependency `main` would get the
    /// identities of the root (`effects::identity`).
    fn name_dependency(&mut self, name: &str, m: ModId, unit: usize) {
        let root = self.prog.root;
        let message = if name == effects::ROOT_PREFIX {
            format!("a dependency cannot have the name `{name}`: the effects of the root have `{name}` in their identity")
        } else if self.prog.lookup(root, name).is_none()
            && effects::canonical(&self.prog, root, name).is_none()
        {
            self.prog.mods[root]
                .items
                .insert(name.to_string(), ItemRef::Mod(m));
            return;
        } else {
            format!("dependency `{name}` has the name of an item that the root sees already")
        };
        let mut d = Diagnostic::error("W0107", message, Span::default())
            .note("give the dependency another name in weft.toml");
        d.unit = unit;
        self.diags.push(d);
    }

    /// Declares the definition of `*T` after all named types, so that the
    /// indices of named types do not change. A raw pointer is an opaque copy
    /// value: no fields, no elements, no deref. It is nonportable, because the
    /// checker cannot know if the foreign object allows other threads.
    fn declare_ptr(&mut self) {
        self.prog.adts.push(AdtDef {
            name: PTR_NAME.into(),
            generics: vec!["T".into()],
            kind: AdtKind::Extern {
                elem_unstable: None,
                deref: None,
            },
            linear: false,
            on_abort: None,
            has_on_abort: false,
            immovable: false,
            copy: true,
            nonportable: true,
            module: PRELUDE,
            span: Span::default(),
        });
        self.prog.ptr = Some(self.prog.adts.len() - 1);
    }

    /// W0116: a raw pointer type outside an `extern fn` signature or a local.
    fn no_ptr(&mut self, t: &TypeExpr) {
        if let Some(span) = ptr_span(t) {
            self.diags.push(Diagnostic::error(
                "W0116",
                "a raw pointer type is valid only in an `extern fn` signature or a local",
                span,
            ));
        }
    }

    /// Gives the unit index to diagnostics made since the last mark.
    fn declare_unit_mark(&mut self, seen: &mut usize, unit: usize) {
        let start = (*seen).max(self.marked);
        for d in &mut self.diags[start..] {
            d.unit = unit;
        }
        *seen = self.diags.len();
        self.marked = self.diags.len();
    }

    fn new_mod(&mut self, name: &str, parent: Option<ModId>, is_std: bool, unit: usize) -> ModId {
        self.prog.mods.push(ModDef {
            name: name.into(),
            parent,
            items: HashMap::new(),
            is_std,
            unit,
        });
        self.prog.mods.len() - 1
    }

    fn adt_at(&self, m: ModId, span: Span) -> Option<AdtId> {
        self.prog
            .adts
            .iter()
            .position(|a| a.module == m && a.span == span)
    }

    fn insert(&mut self, m: ModId, name: &ast::Ident, r: ItemRef) {
        if self.prog.mods[m].items.contains_key(&name.name) {
            self.diags.push(Diagnostic::error(
                "W0107",
                format!("`{}` is defined twice", name.name),
                name.span,
            ));
            return;
        }
        self.prog.mods[m].items.insert(name.name.clone(), r);
    }

    fn declare_items(&mut self, items: &[Item], m: ModId, is_std: bool) {
        for it in items {
            match &it.kind {
                ItemKind::Struct(s) => {
                    let id = self.new_adt(&s.name.name, &s.generics, m, it.span);
                    self.prog.adts[id].linear = s.is_linear;
                    self.prog.adts[id].immovable = s.is_immovable;
                    self.prog.adts[id].on_abort = s.on_abort.as_ref().map(|i| i.name.clone());
                    self.prog.adts[id].has_on_abort = s.on_abort.is_some();
                    if let Some(f) = &s.on_abort {
                        self.on_aborts.push((id, f.clone()));
                    }
                    self.insert(m, &s.name, ItemRef::Adt(id));
                }
                ItemKind::Enum(e) => {
                    let id = self.new_adt(&e.name.name, &e.generics, m, it.span);
                    self.insert(m, &e.name, ItemRef::Adt(id));
                }
                ItemKind::ExternType(x) => {
                    let id = self.new_adt(&x.name.name, &x.generics, m, it.span);
                    self.apply_props(id, x);
                    self.insert(m, &x.name, ItemRef::Adt(id));
                }
                ItemKind::Effect(e) => {
                    self.prog.effects.push(EffectDef {
                        name: e.name.name.clone(),
                        module: m,
                        ops: Vec::new(),
                        is_std,
                        is_pub: it.is_pub,
                    });
                    let id = self.prog.effects.len() - 1;
                    self.insert(m, &e.name, ItemRef::Effect(id));
                }
                ItemKind::Mod(md) => {
                    let unit = self.prog.mods[m].unit;
                    let sub = self.new_mod(&md.name.name, Some(m), is_std, unit);
                    self.insert(m, &md.name, ItemRef::Mod(sub));
                    self.declare_items(&md.items, sub, is_std);
                }
                ItemKind::Fn(_) | ItemKind::Impl(_) | ItemKind::Test(_) => {}
            }
        }
    }

    fn new_adt(&mut self, name: &str, generics: &[ast::Ident], m: ModId, span: Span) -> AdtId {
        report_duplicates(&mut self.diags, "type parameter", generics);
        self.prog.adts.push(AdtDef {
            name: name.into(),
            generics: generics.iter().map(|g| g.name.clone()).collect(),
            kind: AdtKind::Struct(Vec::new()),
            linear: false,
            on_abort: None,
            has_on_abort: false,
            immovable: false,
            copy: false,
            nonportable: false,
            module: m,
            span,
        });
        self.prog.adts.len() - 1
    }

    fn apply_props(&mut self, id: AdtId, x: &ExternTypeDecl) {
        let mut elem = None;
        let mut deref = None;
        for p in &x.props {
            let v = p.value.as_ref().map(|v| v.name.as_str());
            match (p.key.name.as_str(), v) {
                ("elem", Some("unstable")) => elem = Some(true),
                ("elem", Some("stable")) => elem = Some(false),
                ("deref", Some("unstable")) => deref = Some(Deref::Unstable),
                ("deref", Some("stable")) => deref = Some(Deref::Stable),
                ("deref", Some("group")) => deref = Some(Deref::Group),
                ("nonportable", None) => self.prog.adts[id].nonportable = true,
                ("linear", None) => self.prog.adts[id].linear = true,
                ("on_abort", None) => self.prog.adts[id].has_on_abort = true,
                ("copy", None) => self.prog.adts[id].copy = true,
                _ => self.diags.push(Diagnostic::error(
                    "W0108",
                    format!("unknown extern type property `{}`", p.key.name),
                    p.key.span,
                )),
            }
        }
        self.prog.adts[id].kind = AdtKind::Extern {
            elem_unstable: elem,
            deref,
        };
    }

    fn define_items(&mut self, items: &[Item], m: ModId) {
        for it in items {
            match &it.kind {
                ItemKind::Struct(s) => {
                    // Find the definition by its span: a duplicate name keeps its own record.
                    let Some(id) = self.adt_at(m, it.span) else {
                        continue;
                    };
                    let gens: Vec<String> = s.generics.iter().map(|g| g.name.clone()).collect();
                    let self_ty = Ty::Adt(
                        id,
                        (0..gens.len())
                            .map(|i| Ty::Param(u32::try_from(i).unwrap_or(0)))
                            .collect(),
                    );
                    let mut fields = Vec::new();
                    report_duplicates(&mut self.diags, "field", s.fields.iter().map(|f| &f.name));
                    for f in &s.fields {
                        self.no_ptr(&f.ty);
                        let ty = self.resolve_ty(&f.ty, m, &gens, Some(&self_ty));
                        fields.push(FieldDef {
                            name: f.name.name.clone(),
                            ty,
                            place: None,
                            span: f.span,
                        });
                    }
                    self.prog.adts[id].kind = AdtKind::Struct(fields.clone());
                    // Reference fields: only `!Move` structs may point into `self`.
                    for (i, f) in s.fields.iter().enumerate() {
                        if let TypeExprKind::Ref { place, .. } = &f.ty.kind {
                            let ok_place = place.as_ref().filter(|p| p.root.name == "self");
                            match ok_place {
                                Some(p) if s.is_immovable => {
                                    let params = vec![ParamSig {
                                        name: "self".into(),
                                        ty: Ty::Ref(Box::new(self_ty.clone())),
                                        place: None,
                                        shared: false,
                                        uniq: false,
                                        span: f.span,
                                    }];
                                    let sp = self.resolve_sig_place(p, &params, &BTreeMap::new(), m);
                                    fields[i].place = sp;
                                }
                                _ => self.diags.push(Diagnostic::error(
                                    "W0605",
                                    format!(
                                        "field `{}` holds a reference; only a `!Move` struct can hold a reference, and only into `self`",
                                        f.name.name
                                    ),
                                    f.span,
                                )),
                            }
                        }
                    }
                    self.prog.adts[id].kind = AdtKind::Struct(fields);
                }
                ItemKind::Enum(e) => {
                    let Some(id) = self.adt_at(m, it.span) else {
                        continue;
                    };
                    let gens: Vec<String> = e.generics.iter().map(|g| g.name.clone()).collect();
                    let mut vs = Vec::new();
                    report_duplicates(
                        &mut self.diags,
                        "variant",
                        e.variants.iter().map(|v| &v.name),
                    );
                    for (vi, v) in e.variants.iter().enumerate() {
                        for t in &v.fields {
                            self.no_ptr(t);
                        }
                        let fields = v
                            .fields
                            .iter()
                            .map(|t| self.resolve_ty(t, m, &gens, None))
                            .collect();
                        vs.push(VariantDef {
                            name: v.name.name.clone(),
                            fields,
                        });
                        self.prog
                            .variants
                            .entry(v.name.name.clone())
                            .or_default()
                            .push((id, vi));
                    }
                    self.prog.adts[id].kind = AdtKind::Enum(vs);
                }
                ItemKind::Effect(e) => {
                    let Some(ItemRef::Effect(id)) = self.prog.lookup_in(m, &e.name.name) else {
                        continue;
                    };
                    let mut ops = Vec::new();
                    for o in &e.ops {
                        report_duplicates(
                            &mut self.diags,
                            "parameter",
                            o.params.iter().map(|p| &p.name),
                        );
                        for t in o.params.iter().filter_map(|p| p.ty.as_ref()).chain(&o.ret) {
                            self.no_ptr(t);
                        }
                        let params = o
                            .params
                            .iter()
                            .map(|p| {
                                p.ty.as_ref()
                                    .map_or(Ty::Error, |t| self.resolve_ty(t, m, &[], None))
                            })
                            .collect();
                        let ret = o
                            .ret
                            .as_ref()
                            .map_or(Ty::Unit, |t| self.resolve_ty(t, m, &[], None));
                        ops.push(OpDef {
                            name: o.name.name.clone(),
                            params,
                            param_names: o.params.iter().map(|p| p.name.name.clone()).collect(),
                            ret,
                            multi: o.is_multi,
                            span: o.name.span,
                        });
                    }
                    self.prog.effects[id].ops = ops;
                }
                ItemKind::Fn(f) => {
                    let id = self.new_fn(f, it, m, None);
                    let name = f.name.clone();
                    self.insert(m, &name, ItemRef::Fn(id));
                    self.pending_fns.push((id, None, Vec::new()));
                }
                ItemKind::Impl(imp) => {
                    let gens: Vec<String> = imp.generics.iter().map(|g| g.name.clone()).collect();
                    report_duplicates(&mut self.diags, "type parameter", &imp.generics);
                    self.no_ptr(&imp.self_ty);
                    let self_ty = self.resolve_ty(&imp.self_ty, m, &gens, None);
                    let Ty::Adt(owner, _) = self_ty else {
                        self.diags.push(Diagnostic::error(
                            "W0109",
                            "`impl` needs a named type",
                            imp.self_ty.span,
                        ));
                        continue;
                    };
                    for mi in &imp.items {
                        if let ItemKind::Fn(f) = &mi.kind {
                            let id = self.new_fn(f, mi, m, Some(owner));
                            if self
                                .prog
                                .methods
                                .insert((owner, f.name.name.clone()), id)
                                .is_some()
                            {
                                self.diags.push(Diagnostic::error(
                                    "W0107",
                                    format!("method `{}` is defined twice", f.name.name),
                                    f.name.span,
                                ));
                            }
                            self.pending_fns.push((id, Some(owner), gens.clone()));
                        }
                    }
                }
                ItemKind::Test(t) => self.prog.tests.push(TestDef {
                    name: t.name.clone(),
                    body: t.body.clone(),
                    module: m,
                    span: it.span,
                }),
                ItemKind::Mod(md) => {
                    let Some(ItemRef::Mod(sub)) = self.prog.lookup_in(m, &md.name.name) else {
                        continue;
                    };
                    self.define_items(&md.items, sub);
                }
                ItemKind::ExternType(_) => {}
            }
        }
    }

    fn new_fn(&mut self, f: &FnDecl, it: &Item, m: ModId, owner: Option<AdtId>) -> FnId {
        let path = match owner {
            Some(o) => format!("{}.{}", self.prog.adts[o].name, f.name.name),
            None => f.name.name.clone(),
        };
        self.prog.fns.push(FnDef {
            name: f.name.name.clone(),
            path,
            owner,
            decl: f.clone(),
            sig: FnSig {
                generics: Vec::new(),
                params: Vec::new(),
                ret: Ty::Unit,
                ret_places: Vec::new(),
                effects: EffectSig::default(),
                declared: f.effects.is_some(),
            },
            is_pub: it.is_pub,
            is_std: self.prog.mods[m].is_std,
            module: m,
            span: it.span,
        });
        self.prog.fns.len() - 1
    }

    fn resolve_signatures(&mut self) {
        let pending = std::mem::take(&mut self.pending_fns);
        for (id, owner, impl_gens) in pending {
            let before = self.diags.len();
            self.resolve_one(id, owner, &impl_gens);
            let unit = self.prog.mods[self.prog.fns[id].module].unit;
            for d in &mut self.diags[before..] {
                d.unit = unit;
            }
        }
        self.marked = self.diags.len();
    }

    fn resolve_one(&mut self, id: FnId, owner: Option<AdtId>, impl_gens: &[String]) {
        {
            let f = self.prog.fns[id].decl.clone();
            let m = self.prog.fns[id].module;
            let mut gens = impl_gens.to_vec();
            gens.extend(f.generics.iter().map(|g| g.name.clone()));
            report_duplicates(&mut self.diags, "type parameter", &f.generics);
            let outer: BTreeSet<&str> = impl_gens.iter().map(String::as_str).collect();
            for g in f
                .generics
                .iter()
                .filter(|g| outer.contains(g.name.as_str()))
            {
                self.diags.push(Diagnostic::error(
                    "W0107",
                    format!("type parameter `{}` is defined twice", g.name),
                    g.span,
                ));
            }
            report_duplicates(
                &mut self.diags,
                "parameter",
                f.params.iter().map(|p| &p.name),
            );
            let self_ty = owner.map(|o| {
                Ty::Adt(
                    o,
                    (0..impl_gens.len())
                        .map(|i| Ty::Param(u32::try_from(i).unwrap_or(0)))
                        .collect(),
                )
            });
            if !f.is_extern {
                for t in f.params.iter().filter_map(|p| p.ty.as_ref()).chain(&f.ret) {
                    self.no_ptr(t);
                }
            }
            let mut params = Vec::new();
            for p in &f.params {
                let (ty, modes) = match (&p.ty, &self_ty) {
                    (None, Some(st)) if p.name.name == "self" => {
                        (Ty::Ref(Box::new(st.clone())), Vec::new())
                    }
                    (None, _) => {
                        self.diags.push(Diagnostic::error(
                            "W0110",
                            format!("parameter `{}` needs a type", p.name.name),
                            p.span,
                        ));
                        (Ty::Error, Vec::new())
                    }
                    (Some(t), st) => (self.resolve_ty(t, m, &gens, st.as_ref()), t.modes.clone()),
                };
                params.push(ParamSig {
                    name: p.name.name.clone(),
                    ty,
                    place: None,
                    shared: modes.contains(&Mode::Shared),
                    uniq: modes.contains(&Mode::Uniq),
                    span: p.span,
                });
            }
            let fn_params: BTreeMap<String, usize> = params
                .iter()
                .enumerate()
                .map(|(i, p)| (p.name.clone(), i))
                .collect();
            // `in` places of reference parameters.
            for (i, p) in f.params.iter().enumerate() {
                if let Some(TypeExpr {
                    kind:
                        TypeExprKind::Ref {
                            place: Some(pl), ..
                        },
                    ..
                }) = &p.ty
                {
                    params[i].place = self.resolve_sig_place(pl, &params, &fn_params, m);
                }
            }
            self.check_in_cycles(&params);
            let ret = f
                .ret
                .as_ref()
                .map_or(Ty::Unit, |t| self.resolve_ty(t, m, &gens, self_ty.as_ref()));
            let mut ret_places = Vec::new();
            if let Some(t) = &f.ret {
                self.collect_ret_places(
                    t,
                    &params,
                    &fn_params,
                    m,
                    &mut Vec::new(),
                    &mut ret_places,
                );
            }
            let mut effects = EffectSig::default();
            if let Some(row) = &f.effects {
                for item in &row.items {
                    match item {
                        EffectItem::Mut(ps) => {
                            for pl in ps {
                                if let Some(mut sp) =
                                    self.resolve_sig_place(pl, &params, &fn_params, m)
                                {
                                    // `mut(p..)` is equal to `mut(p)`. It also
                                    // covers what the references in `p` point into.
                                    if sp.steps.last() == Some(&SigStep::Wild) {
                                        sp.steps.pop();
                                        if let Some(held) = held_place(&self.prog, &sp, &params) {
                                            effects.muts.push(held);
                                        }
                                    }
                                    effects.muts.push(sp);
                                }
                            }
                        }
                        EffectItem::Named(n) => match effects::resolve(&self.prog, m, n) {
                            Ok(names) => effects.named.extend(names),
                            Err(d) => self.diags.push(d),
                        },
                    }
                }
            } else if f.is_extern && !self.prog.mods[m].is_std {
                // A foreign call can block unless it says otherwise.
                effects.named.insert("Blocking".into());
            }
            // A foreign generic function can drop a value of each type parameter,
            // and it can hold one while it can abort (ADR 0007).
            if f.is_extern && !self.prog.mods[m].is_std && !gens.is_empty() {
                let all: BTreeSet<usize> = (0..gens.len()).collect();
                if !effects.named.is_empty() {
                    effects.holds.clone_from(&all);
                }
                effects.drops = all;
            }
            // A prelude function can drop values of a type parameter too.
            if self.prog.mods[m].is_std {
                let owner_name = owner.map(|o| self.prog.adts[o].name.as_str());
                effects.drops.extend(std_drops(owner_name, &f.name.name));
                effects.raises = std_raises(owner_name, &f.name.name);
            } else if f.is_extern {
                // Foreign code can fail where the runtime runs it.
                effects.raises = true;
            }
            let declared = f.effects.is_some() || f.is_extern;
            self.prog.fns[id].sig = FnSig {
                generics: gens,
                params,
                ret,
                ret_places,
                effects,
                declared,
            };
        }
    }

    /// W0201: the `in` place of a parameter cannot start at the parameter
    /// itself, and the `in` places cannot form a cycle.
    fn check_in_cycles(&mut self, params: &[ParamSig]) {
        let (_, cycles, steps) = in_place_order(params);
        self.prog.add_steps(steps);
        for mut cycle in cycles {
            // Report the cycle at its first parameter.
            if let Some(first) = (0..cycle.len()).min_by_key(|&i| cycle[i]) {
                cycle.rotate_left(first);
            }
            let names: Vec<&str> = cycle.iter().map(|&j| params[j].name.as_str()).collect();
            let message = if let [one] = names.as_slice() {
                format!("the place of `{one}` starts at `{one}` itself")
            } else {
                format!("the places of `{}` form a cycle", names.join("`, `"))
            };
            self.diags.push(
                Diagnostic::error("W0201", message, params[cycle[0]].span)
                    .note("an `in` place must start at another parameter, `self` or an `rc` type"),
            );
        }
    }

    fn collect_ret_places(
        &mut self,
        t: &TypeExpr,
        params: &[ParamSig],
        names: &BTreeMap<String, usize>,
        m: ModId,
        path: &mut Vec<usize>,
        out: &mut Vec<RetPlace>,
    ) {
        match &t.kind {
            TypeExprKind::Ref { place, .. } => match place {
                Some(pl) => {
                    if let Some(sp) = self.resolve_sig_place(pl, params, names, m) {
                        if let SigRoot::Param(i) = sp.root {
                            if !params[i].ty.is_ref() {
                                self.diags.push(Diagnostic::error(
                                    "W0204",
                                    format!(
                                        "a returned reference cannot point into the by-value parameter `{}`: it goes out of scope at the return",
                                        params[i].name
                                    ),
                                    pl.span,
                                ));
                            }
                        }
                        // `p..` also covers what the references in `p` point into.
                        if sp.steps.last() == Some(&SigStep::Wild) {
                            if let Some(held) = held_place(&self.prog, &sp, params) {
                                out.push(RetPlace {
                                    path: path.clone(),
                                    place: held,
                                    uniq: t.modes.contains(&Mode::Uniq),
                                });
                            }
                        }
                        out.push(RetPlace {
                            path: path.clone(),
                            place: sp,
                            uniq: t.modes.contains(&Mode::Uniq),
                        });
                    }
                }
                None => self.diags.push(Diagnostic::error(
                    "W0204",
                    "a returned reference must state its place: `&T in param...`",
                    t.span,
                )),
            },
            TypeExprKind::Tuple(ts) => {
                for (i, t) in ts.iter().enumerate() {
                    path.push(i);
                    self.collect_ret_places(t, params, names, m, path, out);
                    path.pop();
                }
            }
            // A reference inside another type, such as `Option<&T in p>`, can
            // state its place. With no place, the caller takes the places of the
            // arguments.
            TypeExprKind::Path { args, .. } => {
                for t in args {
                    self.collect_nested_places(t, params, names, m, path, out);
                }
            }
            TypeExprKind::Array { elem, .. } => {
                self.collect_nested_places(elem, params, names, m, path, out);
            }
            _ => {}
        }
    }

    /// Collects the stated places of the references inside a type argument of a
    /// returned type. A reference with no place is not an error here.
    fn collect_nested_places(
        &mut self,
        t: &TypeExpr,
        params: &[ParamSig],
        names: &BTreeMap<String, usize>,
        m: ModId,
        path: &mut Vec<usize>,
        out: &mut Vec<RetPlace>,
    ) {
        match &t.kind {
            TypeExprKind::Ref { place: None, inner } => {
                self.collect_nested_places(inner, params, names, m, path, out);
            }
            TypeExprKind::Ref { .. } => self.collect_ret_places(t, params, names, m, path, out),
            TypeExprKind::Tuple(ts) | TypeExprKind::Path { args: ts, .. } => {
                for x in ts {
                    self.collect_nested_places(x, params, names, m, path, out);
                }
            }
            TypeExprKind::Array { elem, .. } | TypeExprKind::Slice(elem) => {
                self.collect_nested_places(elem, params, names, m, path, out);
            }
            _ => {}
        }
    }

    /// Resolves a type expression. `gens` names the type parameters in scope.
    pub fn resolve_ty(
        &mut self,
        t: &TypeExpr,
        m: ModId,
        gens: &[String],
        self_ty: Option<&Ty>,
    ) -> Ty {
        TyResolver {
            prog: &self.prog,
            diags: &mut self.diags,
        }
        .resolve(t, m, gens, self_ty)
    }

    /// Resolves a written place against parameter types. An `rc` type root is
    /// looked up from module `m`, the module of the signature.
    pub fn resolve_sig_place(
        &mut self,
        pl: &PlaceExpr,
        params: &[ParamSig],
        names: &BTreeMap<String, usize>,
        m: ModId,
    ) -> Option<SigPlace> {
        let rootname = pl.root.name.as_str();
        let (root, mut ty) = if let Some(&i) = names.get(rootname) {
            let t = match &params[i].ty {
                Ty::Ref(inner) => (**inner).clone(),
                t => t.clone(),
            };
            (SigRoot::Param(i), t)
        } else if rootname == "self" && !params.is_empty() && params[0].name == "self" {
            let t = match &params[0].ty {
                Ty::Ref(inner) => (**inner).clone(),
                t => t.clone(),
            };
            (SigRoot::Param(0), t)
        } else if let Some(ItemRef::Adt(a)) = self.prog.lookup(m, rootname) {
            let n = self.prog.adts[a].generics.len();
            (SigRoot::Group(a), Ty::Adt(a, vec![Ty::Error; n]))
        } else {
            self.diags.push(Diagnostic::error(
                "W0201",
                format!("place root `{rootname}` is not a parameter, `self` or an `rc` type"),
                pl.root.span,
            ));
            return None;
        };
        let mut steps = Vec::new();
        let mut text = rootname.to_string();
        for st in &pl.steps {
            match st {
                PlaceStep::Wildcard => {
                    text.push_str("..");
                    steps.push(SigStep::Wild);
                }
                PlaceStep::Field(id) => {
                    let Some((step, next, t)) = field_step(&self.prog, &ty, &id.name) else {
                        self.diags.push(Diagnostic::error(
                            "W0104",
                            format!("no field or variant `{}` in this place", id.name),
                            id.span,
                        ));
                        return None;
                    };
                    for s in step {
                        steps.push(SigStep::Step(s.0, s.1));
                    }
                    text.push_str(&t);
                    ty = next;
                }
                PlaceStep::Elem => {
                    if let Some((step, next)) = elem_step(&self.prog, &ty) {
                        if let Some(s) = step {
                            steps.push(SigStep::Step(s, "[]".into()));
                        }
                        text.push_str("[]");
                        ty = next;
                    } else {
                        self.diags.push(Diagnostic::error(
                            "W0104",
                            "this place has no elements",
                            pl.span,
                        ));
                        return None;
                    }
                }
                PlaceStep::SegLo(k) | PlaceStep::SegHi(k) => {
                    let hi = matches!(st, PlaceStep::SegHi(_));
                    let Some(&label) = names.get(&k.name) else {
                        self.diags.push(Diagnostic::error(
                            "W0201",
                            format!("split point `{}` is not a parameter", k.name),
                            k.span,
                        ));
                        return None;
                    };
                    let Some((step, next)) = elem_step(&self.prog, &ty) else {
                        self.diags.push(Diagnostic::error(
                            "W0104",
                            "this place has no elements",
                            pl.span,
                        ));
                        return None;
                    };
                    let unstable = step.is_some_and(|s| s.unstable);
                    steps.push(SigStep::Seg {
                        label,
                        hi,
                        unstable,
                    });
                    if hi {
                        let _ = write!(text, "[{}..]", k.name);
                    } else {
                        let _ = write!(text, "[..{}]", k.name);
                    }
                    ty = Ty::Slice(Box::new(next));
                }
            }
        }
        Some(SigPlace { root, steps, text })
    }
}

/// W0107: reports each name that repeats an earlier name of the list.
/// `what` names the kind of name, for example `field`.
fn report_duplicates<'a>(
    diags: &mut Vec<Diagnostic>,
    what: &str,
    names: impl IntoIterator<Item = &'a ast::Ident>,
) {
    let mut seen = BTreeSet::new();
    for n in names {
        if !seen.insert(n.name.as_str()) {
            diags.push(Diagnostic::error(
                "W0107",
                format!("{what} `{}` is defined twice", n.name),
                n.span,
            ));
        }
    }
}

/// Returns why two modes of a list contradict, or `None`.
///
/// Two values of one axis contradict, for example `once` and `many`. Also
/// `uniq` and `shared` contradict: other threads can read a `shared` value,
/// so other references to it exist.
fn mode_conflict(modes: &[Mode], steps: &mut usize) -> Option<String> {
    let axis = |m: Mode| match m {
        Mode::Uniq | Mode::Aliased => 0,
        Mode::Portable | Mode::Nonportable => 1,
        Mode::Uncontended | Mode::Shared => 2,
        Mode::Once | Mode::Many => 3,
    };
    // The first mode on each axis.
    let mut seen: [Option<Mode>; 4] = [None; 4];
    for &b in modes {
        *steps += 1;
        match seen[axis(b)] {
            Some(a) if a != b => {
                return Some(format!(
                    "modes `{}` and `{}` contradict: a type has one mode on each axis",
                    a.name(),
                    b.name()
                ));
            }
            Some(_) => {}
            None => seen[axis(b)] = Some(b),
        }
        let other = match b {
            Mode::Uniq => Mode::Shared,
            Mode::Shared => Mode::Uniq,
            _ => continue,
        };
        if seen[axis(other)] == Some(other) {
            return Some(format!(
                "modes `{}` and `{}` contradict: other threads can read a `shared` value, so it is not `uniq`",
                other.name(),
                b.name()
            ));
        }
    }
    None
}

/// Returns the structs that hold themselves with no indirection.
///
/// A struct holds its fields inline, also through tuples and arrays with at
/// least one element. An enum value is a cell of its own, and an extern type
/// is opaque, so each is an indirection. A generic struct holds the
/// arguments of the parameters that it holds inline.
///
/// The work has two steps, so the time is about linear in the size of the
/// definitions. First, a worklist finds the parameters that each struct
/// holds inline. Each set has at most one entry for each parameter. Then a
/// graph gets an edge from `a` to `b` when `a` holds `b` directly. A struct
/// holds itself when it is on a cycle of this graph.
pub fn infinite_structs(prog: &Program) -> Vec<AdtId> {
    size_check(prog).0
}

/// Returns [`infinite_structs`], and the number of steps: the structs that the
/// work list took, and one for each struct in the graph of direct holds.
fn size_check(prog: &Program) -> (Vec<AdtId>, usize) {
    /// What a value holds inline: a struct or a type parameter.
    enum Held {
        Adt(AdtId),
        Param(u32),
    }
    /// Calls `on` for each struct and parameter that a value of type `t`
    /// holds directly. `params[b]` holds the parameters that struct `b`
    /// holds inline.
    fn walk(t: &Ty, prog: &Program, params: &[BTreeSet<u32>], on: &mut dyn FnMut(Held)) {
        match t {
            Ty::Param(i) => on(Held::Param(*i)),
            Ty::Tuple(ts) => {
                for t in ts {
                    walk(t, prog, params, on);
                }
            }
            Ty::Array(t, n) if *n > 0 => walk(t, prog, params, on),
            Ty::Adt(b, args) if matches!(prog.adts[*b].kind, AdtKind::Struct(_)) => {
                on(Held::Adt(*b));
                for &j in &params[*b] {
                    if let Some(arg) = args.get(j as usize) {
                        walk(arg, prog, params, on);
                    }
                }
            }
            _ => {}
        }
    }
    /// Adds to `out` each struct that a value of type `t` can hold inline,
    /// for any parameter sets.
    fn mentions(t: &Ty, prog: &Program, out: &mut Vec<AdtId>) {
        match t {
            Ty::Tuple(ts) => {
                for t in ts {
                    mentions(t, prog, out);
                }
            }
            Ty::Array(t, n) if *n > 0 => mentions(t, prog, out),
            Ty::Adt(b, args) if matches!(prog.adts[*b].kind, AdtKind::Struct(_)) => {
                out.push(*b);
                for t in args {
                    mentions(t, prog, out);
                }
            }
            _ => {}
        }
    }
    let fields = |a: AdtId| match &prog.adts[a].kind {
        AdtKind::Struct(fields) => fields.as_slice(),
        _ => &[],
    };
    let n = prog.adts.len();
    // Step 1: the parameters. When the set of `b` grows, each struct that
    // mentions `b` goes back on the worklist.
    let mut users: Vec<Vec<AdtId>> = vec![Vec::new(); n];
    for a in 0..n {
        let mut out = Vec::new();
        for f in fields(a) {
            mentions(&f.ty, prog, &mut out);
        }
        out.sort_unstable();
        out.dedup();
        for b in out {
            users[b].push(a);
        }
    }
    let mut params: Vec<BTreeSet<u32>> = vec![BTreeSet::new(); n];
    let mut queued = vec![true; n];
    let mut work: Vec<AdtId> = (0..n).rev().collect();
    let mut steps = n;
    while let Some(a) = work.pop() {
        steps += 1;
        queued[a] = false;
        let mut found = BTreeSet::new();
        for f in fields(a) {
            walk(&f.ty, prog, &params, &mut |h| {
                if let Held::Param(i) = h {
                    found.insert(i);
                }
            });
        }
        if found.len() > params[a].len() {
            params[a] = found;
            for &u in &users[a] {
                if !queued[u] {
                    queued[u] = true;
                    work.push(u);
                }
            }
        }
    }
    // Step 2: the graph of direct holds, and its cycles.
    let edges: Vec<Vec<AdtId>> = (0..n)
        .map(|a| {
            let mut out = Vec::new();
            for f in fields(a) {
                walk(&f.ty, prog, &params, &mut |h| {
                    if let Held::Adt(b) = h {
                        out.push(b);
                    }
                });
            }
            out
        })
        .collect();
    let cyclic = on_cycles(&edges);
    ((0..n).filter(|&a| cyclic[a]).collect(), steps)
}

/// Returns, for each node of a graph, whether a cycle goes through it. The
/// function uses Tarjan's algorithm for strongly connected components. It
/// keeps its own stack, so a long chain cannot overflow the thread stack.
fn on_cycles(edges: &[Vec<usize>]) -> Vec<bool> {
    const NEW: usize = usize::MAX;
    let n = edges.len();
    let (mut index, mut low) = (vec![NEW; n], vec![0; n]);
    let mut on_stack = vec![false; n];
    let mut cyclic = vec![false; n];
    let (mut stack, mut calls) = (Vec::new(), Vec::new());
    let mut next = 0;
    for root in 0..n {
        if index[root] != NEW {
            continue;
        }
        calls.push((root, 0));
        while let Some(&(v, i)) = calls.last() {
            if i == 0 {
                index[v] = next;
                low[v] = next;
                next += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if let Some(&w) = edges[v].get(i) {
                if let Some(top) = calls.last_mut() {
                    top.1 += 1;
                }
                if index[w] == NEW {
                    calls.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            calls.pop();
            if let Some(&(u, _)) = calls.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                let mut members = Vec::new();
                while let Some(w) = stack.pop() {
                    on_stack[w] = false;
                    members.push(w);
                    if w == v {
                        break;
                    }
                }
                let cycle = members.len() > 1 || edges[v].contains(&v);
                for w in members {
                    cyclic[w] = cycle;
                }
            }
        }
    }
    cyclic
}

/// Resolves type expressions against a finished program. It borrows the
/// program and writes its diagnostics to `diags`.
pub struct TyResolver<'a> {
    /// The program.
    pub prog: &'a Program,
    /// Where the diagnostics go.
    pub diags: &'a mut Vec<Diagnostic>,
}

impl TyResolver<'_> {
    /// Resolves a type expression. `gens` names the type parameters in scope.
    pub fn resolve(&mut self, t: &TypeExpr, m: ModId, gens: &[String], self_ty: Option<&Ty>) -> Ty {
        let mut steps = 0;
        let conflict = mode_conflict(&t.modes, &mut steps);
        self.prog.add_steps(steps);
        if let Some(message) = conflict {
            self.diags.push(Diagnostic::error("W0119", message, t.span));
        }
        match &t.kind {
            TypeExprKind::SelfType => self_ty.cloned().unwrap_or_else(|| {
                self.diags
                    .push(Diagnostic::error("W0101", "`Self` is not in scope", t.span));
                Ty::Error
            }),
            TypeExprKind::Ref { inner, .. } => {
                Ty::Ref(Box::new(self.resolve(inner, m, gens, self_ty)))
            }
            TypeExprKind::Ptr(inner) => {
                let inner = self.resolve(inner, m, gens, self_ty);
                self.prog.ptr.map_or(Ty::Error, |p| Ty::Adt(p, vec![inner]))
            }
            TypeExprKind::Tuple(ts) if ts.is_empty() => Ty::Unit,
            TypeExprKind::Tuple(ts) => Ty::Tuple(
                ts.iter()
                    .map(|t| self.resolve(t, m, gens, self_ty))
                    .collect(),
            ),
            TypeExprKind::Array { elem, len } => {
                Ty::Array(Box::new(self.resolve(elem, m, gens, self_ty)), *len)
            }
            TypeExprKind::Slice(e) => Ty::Slice(Box::new(self.resolve(e, m, gens, self_ty))),
            TypeExprKind::Fn {
                params,
                ret,
                effects,
            } => {
                let params = params
                    .iter()
                    .map(|t| self.resolve(t, m, gens, self_ty))
                    .collect();
                let ret = ret
                    .as_ref()
                    .map_or(Ty::Unit, |t| self.resolve(t, m, gens, self_ty));
                let effects = effects.as_ref().map(|row| {
                    let mut names = BTreeSet::new();
                    for item in &row.items {
                        if let EffectItem::Named(n) = item {
                            match effects::resolve(self.prog, m, n) {
                                Ok(ns) => names.extend(ns),
                                Err(d) => self.diags.push(d),
                            }
                        }
                    }
                    names.into_iter().collect()
                });
                Ty::Fn(std::sync::Arc::new(FnTy {
                    params,
                    ret,
                    effects,
                    summary: None,
                    item: None,
                }))
            }
            TypeExprKind::Path { segments, args } => {
                let args: Vec<Ty> = args
                    .iter()
                    .map(|t| self.resolve(t, m, gens, self_ty))
                    .collect();
                if segments.len() == 1 {
                    let n = segments[0].name.as_str();
                    if let Some(i) = gens.iter().position(|g| g == n) {
                        return Ty::Param(u32::try_from(i).unwrap_or(0));
                    }
                    if let Some(it) = IntTy::from_name(n) {
                        return Ty::Int(it);
                    }
                    if n == "bool" {
                        return Ty::Bool;
                    }
                }
                let mut module = m;
                for (i, seg) in segments.iter().enumerate() {
                    let found = if i == 0 {
                        self.prog.lookup(module, &seg.name)
                    } else {
                        self.prog.lookup_in(module, &seg.name)
                    };
                    match found {
                        Some(ItemRef::Mod(sub)) if i + 1 < segments.len() => module = sub,
                        Some(ItemRef::Adt(a)) if i + 1 == segments.len() => {
                            let want = self.prog.adts[a].generics.len();
                            if want != args.len() && !args.is_empty() {
                                self.diags.push(Diagnostic::error(
                                    "W0103",
                                    format!("`{}` takes {want} type arguments", seg.name),
                                    t.span,
                                ));
                                return Ty::Error;
                            }
                            let args = if args.is_empty() {
                                vec![Ty::Error; want]
                            } else {
                                args
                            };
                            return Ty::Adt(a, args);
                        }
                        _ => break,
                    }
                }
                let text: Vec<&str> = segments.iter().map(|s| s.name.as_str()).collect();
                self.diags.push(Diagnostic::error(
                    "W0101",
                    format!("unknown type `{}`", text.join(".")),
                    t.span,
                ));
                Ty::Error
            }
        }
    }
}

/// The steps of `.name` (each with its text), the field type, and the text.
pub type FieldStep = (Vec<(weft_facts::Step, String)>, Ty, String);

/// Returns the steps for `.name` on a value of type `ty`, the next type, and the text.
///
/// Struct fields and tuple indices are stable. Variants are unstable. A `Box` adds a
/// deref step first.
pub fn field_step(prog: &Program, ty: &Ty, name: &str) -> Option<FieldStep> {
    use weft_facts::{Step, StepKind};
    match ty {
        Ty::Tuple(ts) => {
            let i: usize = name.parse().ok()?;
            let t = ts.get(i)?.clone();
            let s = Step {
                kind: StepKind::Field {
                    id: u32::try_from(i).ok()?,
                },
                unstable: false,
            };
            Some((vec![(s, format!(".{i}"))], t, format!(".{i}")))
        }
        Ty::Adt(a, args) => match &prog.adts[*a].kind {
            AdtKind::Struct(fields) => {
                let i = fields.iter().position(|f| f.name == name)?;
                let t = crate::types::subst(&fields[i].ty, args);
                let s = Step {
                    kind: StepKind::Field {
                        id: u32::try_from(i).ok()?,
                    },
                    unstable: false,
                };
                Some((vec![(s, format!(".{name}"))], t, format!(".{name}")))
            }
            AdtKind::Enum(vs) => {
                let i = vs.iter().position(|v| v.name == name)?;
                let fields: Vec<Ty> = vs[i]
                    .fields
                    .iter()
                    .map(|t| crate::types::subst(t, args))
                    .collect();
                let t = match fields.len() {
                    0 => Ty::Unit,
                    1 => fields[0].clone(),
                    _ => Ty::Tuple(fields),
                };
                let s = Step {
                    kind: StepKind::Variant {
                        id: u32::try_from(i).ok()?,
                    },
                    unstable: true,
                };
                Some((vec![(s, format!(".{name}"))], t, format!(".{name}")))
            }
            AdtKind::Extern { deref: Some(d), .. } if *d != Deref::Group => {
                let inner = args.first()?.clone();
                let (mut rest, t, text) = field_step(prog, &inner, name)?;
                let s = Step {
                    kind: StepKind::Deref,
                    unstable: *d == Deref::Unstable,
                };
                rest.insert(0, (s, "*".into()));
                Some((rest, t, text))
            }
            AdtKind::Extern { .. } => None,
        },
        _ => None,
    }
}

/// Returns the step for `x[]` on a value of type `ty` and the element type.
///
/// A slice place already names its elements, so `x[]` on a slice adds no step.
pub fn elem_step(prog: &Program, ty: &Ty) -> Option<(Option<weft_facts::Step>, Ty)> {
    use weft_facts::{Step, StepKind};
    match ty {
        Ty::Array(t, _) => Some((
            Some(Step {
                kind: StepKind::Elem,
                unstable: false,
            }),
            (**t).clone(),
        )),
        Ty::Slice(t) => Some((None, (**t).clone())),
        Ty::Adt(a, args) => match &prog.adts[*a].kind {
            AdtKind::Extern {
                elem_unstable: Some(u),
                ..
            } => {
                let t = args.first().cloned().unwrap_or(Ty::Int(IntTy::U8));
                Some((
                    Some(Step {
                        kind: StepKind::Elem,
                        unstable: *u,
                    }),
                    t,
                ))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Returns the place of what the references in a written place `sp` point into:
/// the step `Held`. Its root must be a reference parameter to a value that can
/// hold references. In the body it is any place inside what they point into.
fn held_place(prog: &Program, sp: &SigPlace, params: &[ParamSig]) -> Option<SigPlace> {
    let SigRoot::Param(i) = sp.root else {
        return None;
    };
    let Some(Ty::Ref(inner)) = params.get(i).map(|p| &p.ty) else {
        return None;
    };
    // The pointee of a slice reference is its elements.
    let pointee = match &**inner {
        Ty::Slice(x) => &**x,
        t => t,
    };
    if !prog.ty_holds_refs(pointee) {
        return None;
    }
    Some(SigPlace {
        root: sp.root.clone(),
        steps: vec![SigStep::Held],
        text: sp.text.clone(),
    })
}

/// Returns the parameters in the order of their `in` places, and the cycles.
///
/// The root parameter of each `in` place comes before the parameter, so that
/// its places are known when the lowering substitutes the place. The second
/// part has the cycles of `in` places (W0201), and the third the number of
/// steps of the walks.
///
/// Each parameter has at most one `in` place, so a walk from a parameter has
/// one way. A walk stops at a parameter that an earlier walk saw, so the time
/// is linear.
pub fn in_place_order(params: &[ParamSig]) -> (Vec<usize>, Vec<Vec<usize>>, usize) {
    let root_of = |i: usize| match params.get(i).and_then(|p| p.place.as_ref()) {
        Some(SigPlace {
            root: SigRoot::Param(j),
            ..
        }) => Some(*j),
        _ => None,
    };
    // The states: 0 is new, 1 is on this walk, 2 is done.
    let mut state = vec![0_u8; params.len()];
    let mut order = Vec::with_capacity(params.len());
    let mut cycles = Vec::new();
    let mut steps = 0;
    for start in 0..params.len() {
        let mut path = Vec::new();
        let mut at = Some(start);
        while let Some(j) = at {
            steps += 1;
            if state.get(j) != Some(&0) {
                break;
            }
            state[j] = 1;
            path.push(j);
            at = root_of(j);
        }
        // A walk that meets itself closes a cycle.
        if let Some(j) = at.filter(|&j| state.get(j) == Some(&1)) {
            if let Some(p) = path.iter().position(|&k| k == j) {
                cycles.push(path[p..].to_vec());
            }
        }
        // The end of the walk is nearest to the root: it comes first.
        for &k in path.iter().rev() {
            state[k] = 2;
            order.push(k);
        }
    }
    (order, cycles, steps)
}

/// W0118: the effects of each `on abort` function, from its final signature.
///
/// The unwinder runs the function with the root handlers only (ADR 0007). So its
/// row can name only the standard effects that the root handlers serve: not
/// `fail`, and with no runtime none at all. It can change only the places of
/// the value that it gets: not an `rc` group, and not a place that a reference in
/// the value points to. The effects proof models `on abort` as atomic
/// (`proofs/effects`), and this check mirrors that assumption.
pub fn check_on_abort_rows(prog: &Program, sigs: &[FnSig], no_runtime: bool) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    for def in &prog.adts {
        let Some(name) = &def.on_abort else {
            continue;
        };
        let Some(ItemRef::Fn(f)) = prog.lookup(def.module, name) else {
            continue;
        };
        let (Some(sig), Some(fd)) = (sigs.get(f), prog.fns.get(f)) else {
            continue;
        };
        if !seen.insert(f) || fd.is_std {
            continue;
        }
        let unit = prog.mods[fd.module].unit;
        let span = fd.decl.name.span;
        let e = &sig.effects;
        // A failure that the runtime raises in the function (a `join`, a scope,
        // a `fork`, a read) goes where a `fail` goes.
        let fails = e.named.contains("Fail") || e.raises;
        let bad: Vec<String> = e
            .named
            .iter()
            .chain(&e.task_effects)
            .filter(|n| n.as_str() != "Fail" && (no_runtime || !effects::is_std(n)))
            .map(|n| {
                let w = effects::written(prog, fd.module, n).unwrap_or_else(|| n.clone());
                format!("`{w}`")
            })
            .collect::<BTreeSet<String>>()
            .into_iter()
            .collect();
        if fails {
            let mut d = Diagnostic::error(
                "W0118",
                format!(
                    "`on abort` function `{}` can fail, and a failure there does not reach the handlers of the code that aborts",
                    fd.name
                ),
                span,
            )
            .note("handle the failure inside the function, or do the work after a normal path");
            if !e.named.contains("Fail") {
                d = d.note("a `join`, a scope, a `fork` and a read of a file can fail at run time");
            }
            d.unit = unit;
            out.push(d);
        }
        if !bad.is_empty() {
            let note = if no_runtime {
                "with no runtime, no root handler serves an effect where the unwinder runs it"
            } else {
                "an `on abort` function can perform only the standard effects other than `fail`"
            };
            let mut d = Diagnostic::error(
                "W0118",
                format!(
                    "`on abort` function `{}` performs {}, but the unwinder runs it with the root handlers only",
                    fd.name,
                    bad.join(", ")
                ),
                span,
            )
            .note(note);
            d.unit = unit;
            out.push(d);
        }
        // A function value that the function does not know, for example from a
        // field of its value, can do what its maker can: perform through a
        // handler of the code that aborts, fail, or change a place outside.
        if e.reaches {
            let mut d = Diagnostic::error(
                "W0118",
                format!(
                    "`on abort` function `{}` calls a function value that it does not know, but the unwinder runs it with the root handlers only",
                    fd.name
                ),
                span,
            )
            .note("the value can perform through a handler of the code that aborts, fail, or change a place outside the value; call only known functions there");
            d.unit = unit;
            out.push(d);
        }
        let outside: Vec<String> = e
            .muts
            .iter()
            .filter(|m| m.root != SigRoot::Param(0) || m.steps.contains(&SigStep::Held))
            .map(|m| format!("`{}`", m.text))
            .collect();
        if !outside.is_empty() {
            let mut d = Diagnostic::error(
                "W0118",
                format!(
                    "`on abort` function `{}` changes {}, a place outside the value that it gets",
                    fd.name,
                    outside.join(", ")
                ),
                span,
            )
            .note(
                "the unwinder runs it where a node aborts, and that node does not state the change",
            );
            d.unit = unit;
            out.push(d);
        }
    }
    out
}

/// Returns true if a prelude function can raise a failure that the runtime
/// makes (ADR 0007): `FsCap.read` when it cannot read the file, `Task.join` of
/// a failed task, and `with_timeout` at its deadline. Sema lowers `join`
/// itself, so its entry is for the signature only.
fn std_raises(owner: Option<&str>, name: &str) -> bool {
    matches!(
        (owner, name),
        (Some("FsCap"), "read") | (Some("Task"), "join") | (None, "with_timeout")
    )
}

/// Returns the type parameters, by index in the signature, of the values that a
/// prelude function drops (ADR 0007). `Vec.clear` drops each element,
/// `Task.detach` the result of the task, and `Response.json` its argument. Sema
/// lowers `detach` itself, so its entry is for the signature only.
fn std_drops(owner: Option<&str>, name: &str) -> Vec<usize> {
    match (owner, name) {
        (Some("Vec"), "clear") | (Some("Task"), "detach") | (Some("Response"), "json") => {
            vec![0]
        }
        _ => Vec::new(),
    }
}
