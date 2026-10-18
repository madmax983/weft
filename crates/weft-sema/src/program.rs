//! Item collection, name resolution and signatures.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;

use weft_syntax::ast::{
    self, EffectItem, ExternTypeDecl, File, FnDecl, Item, ItemKind, Mode, PlaceExpr, PlaceStep,
    Span, TypeExpr, TypeExprKind,
};
use weft_syntax::diag::Diagnostic;

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
}

/// An effect.
#[derive(Clone, Debug)]
pub struct EffectDef {
    /// The canonical name.
    pub name: String,
    /// The operations.
    pub ops: Vec<OpDef>,
    /// The effect is a standard effect.
    pub is_std: bool,
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
    pub items: BTreeSet<usize>,
    /// The call can abort.
    pub abort: bool,
    /// The call can resume a `multi` continuation more than once.
    pub multi: bool,
    /// The call can call a function value that the function does not know.
    pub unknown: bool,
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
    /// The source unit: 0 is the prelude, 1 is the root, higher are dependencies.
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
}

/// The prelude module.
pub const PRELUDE: ModId = 0;

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
    /// Returns the names of all type definitions, for type display.
    pub fn adt_names(&self) -> Vec<String> {
        self.adts.iter().map(|a| a.name.clone()).collect()
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

    /// Finds an effect by canonical name, from a module outward.
    pub fn effect_named(&self, module: ModId, name: &str) -> Option<EffectId> {
        match self.lookup(module, name) {
            Some(ItemRef::Effect(e)) => Some(e),
            _ => None,
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
}

impl Collector {
    /// Collects the prelude first, then the other units.
    pub fn collect(units: &[Unit]) -> (Program, Vec<Diagnostic>) {
        let mut c = Self {
            prog: Program::default(),
            diags: Vec::new(),
            pending_fns: Vec::new(),
            marked: 0,
        };
        // Pass 1: names.
        let mut unit_mods = Vec::new();
        for (i, u) in units.iter().enumerate() {
            let parent = (i > 1).then_some(1);
            let m = c.new_mod(&u.name, parent, u.is_std, i);
            if i == 1 {
                c.prog.root = m;
            }
            if i > 1 {
                c.prog.mods[1].items.insert(u.name.clone(), ItemRef::Mod(m));
            }
            unit_mods.push(m);
            let before = c.diags.len();
            c.declare_items(&u.file.items, m, u.is_std);
            for d in &mut c.diags[before..] {
                d.unit = i;
            }
        }
        // Pass 2: bodies of type definitions and signatures.
        let mut seen = 0;
        for (i, u) in units.iter().enumerate() {
            c.declare_unit_mark(&mut seen, i);
            let _ = u;
        }
        for (i, (u, &m)) in units.iter().zip(&unit_mods).enumerate() {
            c.define_items(&u.file.items, m);
            c.declare_unit_mark(&mut seen, i);
        }
        c.resolve_signatures();
        (c.prog, c.diags)
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
                        ops: Vec::new(),
                        is_std,
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
                    for f in &s.fields {
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
                                    let sp = self.resolve_sig_place(p, &params, &BTreeMap::new());
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
                    for (vi, v) in e.variants.iter().enumerate() {
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
            let self_ty = owner.map(|o| {
                Ty::Adt(
                    o,
                    (0..impl_gens.len())
                        .map(|i| Ty::Param(u32::try_from(i).unwrap_or(0)))
                        .collect(),
                )
            });
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
                    params[i].place = self.resolve_sig_place(pl, &params, &fn_params);
                }
            }
            let ret = f
                .ret
                .as_ref()
                .map_or(Ty::Unit, |t| self.resolve_ty(t, m, &gens, self_ty.as_ref()));
            let mut ret_places = Vec::new();
            if let Some(t) = &f.ret {
                self.collect_ret_places(t, &params, &fn_params, &mut Vec::new(), &mut ret_places);
            }
            let mut effects = EffectSig::default();
            if let Some(row) = &f.effects {
                for item in &row.items {
                    match item {
                        EffectItem::Mut(ps) => {
                            for pl in ps {
                                if let Some(mut sp) =
                                    self.resolve_sig_place(pl, &params, &fn_params)
                                {
                                    // `mut(p..)` is equal to `mut(p)`.
                                    if sp.steps.last() == Some(&SigStep::Wild) {
                                        sp.steps.pop();
                                    }
                                    effects.muts.push(sp);
                                }
                            }
                        }
                        EffectItem::Named(n) => match effects::canonical(&self.prog, m, &n.name) {
                            Some(names) => effects.named.extend(names),
                            None => self.diags.push(Diagnostic::error(
                                "W0101",
                                format!("unknown effect `{}`", n.name),
                                n.span,
                            )),
                        },
                    }
                }
            } else if f.is_extern && !self.prog.mods[m].is_std {
                // A foreign call can block unless it says otherwise.
                effects.named.insert("Blocking".into());
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

    fn collect_ret_places(
        &mut self,
        t: &TypeExpr,
        params: &[ParamSig],
        names: &BTreeMap<String, usize>,
        path: &mut Vec<usize>,
        out: &mut Vec<RetPlace>,
    ) {
        match &t.kind {
            TypeExprKind::Ref { place, .. } => match place {
                Some(pl) => {
                    if let Some(sp) = self.resolve_sig_place(pl, params, names) {
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
                    self.collect_ret_places(t, params, names, path, out);
                    path.pop();
                }
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

    /// Resolves a written place against parameter types.
    pub fn resolve_sig_place(
        &mut self,
        pl: &PlaceExpr,
        params: &[ParamSig],
        names: &BTreeMap<String, usize>,
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
        } else if let Some(ItemRef::Adt(a)) = self.prog.lookup(self.prog.root, rootname) {
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

/// Resolves type expressions against a finished program. It does not copy the program.
pub struct TyResolver<'a> {
    /// The program.
    pub prog: &'a Program,
    /// Where the diagnostics go.
    pub diags: &'a mut Vec<Diagnostic>,
}

impl TyResolver<'_> {
    /// Resolves a type expression. `gens` names the type parameters in scope.
    pub fn resolve(&mut self, t: &TypeExpr, m: ModId, gens: &[String], self_ty: Option<&Ty>) -> Ty {
        match &t.kind {
            TypeExprKind::SelfType => self_ty.cloned().unwrap_or_else(|| {
                self.diags
                    .push(Diagnostic::error("W0101", "`Self` is not in scope", t.span));
                Ty::Error
            }),
            TypeExprKind::Ref { inner, .. } => {
                Ty::Ref(Box::new(self.resolve(inner, m, gens, self_ty)))
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
                            match effects::canonical(self.prog, m, &n.name) {
                                Some(ns) => names.extend(ns),
                                None => self.diags.push(Diagnostic::error(
                                    "W0101",
                                    format!("unknown effect `{}`", n.name),
                                    n.span,
                                )),
                            }
                        }
                    }
                    names.into_iter().collect()
                });
                Ty::Fn(std::rc::Rc::new(FnTy {
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
