//! Roots and α: from an IR place to fact places (`docs/ir.md` 6.3).
//!
//! [`Roots`] gives each local of a component its root: the value of a local
//! (also a temporary and a by-value parameter) is a `Local` root, and an upvar
//! local has the root of its site local. The `rc` group of a type is a `Group`
//! root.
//!
//! [`alpha`] walks the projections of a place:
//!
//! | Projection | Fact step |
//! | --- | --- |
//! | `Field(f)` | a field step (stable) |
//! | `Variant(v)` | a variant step (unstable); the payload of a variant with one field is the variant step itself |
//! | `Index(_)`, `Elems` | the element step, with the stability of the type (`Vec`: unstable, array: stable); a slice names its elements, so it adds no step |
//! | `Split(s, side)` | the split step of split `s`, with the stability of the element step before it |
//! | `Deref(Box)` | the deref step, with the stability of the type |
//! | `Deref(Rc)` | the group root of the inner type; the handle place `h.*` joins |
//!
//! Each `Deref` adds the place before it to the pointer places
//! ([`Alpha::ptrs`]): an access reads them. `Deref(Ref)` needs the abstract
//! value of the reference: [`alpha_with`] asks a function for the places that
//! the reference at a fact place points into (the analysis reads its state,
//! `crate::analysis`), and [`alpha`] with no state returns
//! [`AlphaError::NeedsValue`]. An environment field of a closure component
//! comes with stage F11 ([`AlphaError::Later`]).
//!
//! The roots of the interface of a function body are `Param` roots: the
//! pointee of a reference parameter, or the pointees of the references in a
//! by-value parameter ([`Roots::param`]), and the pointees of the references
//! behind a parameter ([`Roots::held`], `*p`). [`Roots::role`] gives back
//! what a root is, so a fact place maps back to a move path
//! ([`Roots::path_of`]).

use std::collections::{HashMap, HashSet};

use weft_facts::{FnFacts, PlaceId, RootId, RootKind, Step, StepKind};
use weft_ir::ty::{AdtKind, ExternDeref, Lang};
use weft_ir::{
    AdtId, BodyId, DerefKind, LocalDecl, LocalId, LocalKind, Place, Program, Proj, Side, TempKind,
    Ty, TyId, TyTable,
};

use crate::analysis::domain::{Key, PathStep};
use crate::irbuild::subst;

/// The key of a group root: the definition of an `rc` type, or another type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum GroupKey {
    /// A definition.
    Adt(AdtId),
    /// Another type.
    Ty(TyId),
}

/// What a root of a component is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Role {
    /// The value of a local (its key).
    Local(Key),
    /// The pointee of parameter `i` of a body: what a reference parameter
    /// points into, or what the references in a by-value parameter point
    /// into.
    Param(BodyId, u32),
    /// What the references behind parameter `i` of a body point into (`*p`).
    Held(BodyId, u32),
    /// The `rc` group of a type.
    Group,
    /// The callee frame of the run node with this id: the locals of the
    /// callee that its result points into.
    Frame(u32),
}

/// The roots of one component, made when α first needs them.
#[derive(Clone, Debug, Default)]
pub struct Roots {
    /// The root place of the value of each local, by the body and the local
    /// that owns it (not an upvar local).
    locals: HashMap<(BodyId, LocalId), PlaceId>,
    /// The group root of each `rc` type.
    groups: HashMap<GroupKey, PlaceId>,
    /// The `Param` roots of the parameters of a body.
    params: HashMap<(BodyId, u32), PlaceId>,
    /// The `Held` roots of the parameters of a body.
    helds: HashMap<(BodyId, u32), PlaceId>,
    /// What each root is.
    roles: HashMap<RootId, Role>,
    /// The handle places `h.*` that α made.
    handles: HashSet<PlaceId>,
    /// The callee frame root of each run node.
    frames: HashMap<u32, PlaceId>,
    /// The stated place of each place field of a struct (`cur: &u8 in
    /// self.buf[]`), in terms of the struct (`self`).
    fields: HashMap<(AdtId, u32), crate::program::SigPlace>,
}

/// The fact places of an IR place.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Alpha {
    /// The places that the IR place can be.
    pub places: Vec<PlaceId>,
    /// The pointer places on the path: for each `Deref`, the place before it.
    /// An access of the place reads them.
    pub ptrs: Vec<PlaceId>,
    /// The handle places `h.*` of each `Rc` handle on the path: a reference
    /// made through the handle depends on it (ADR 0003).
    pub handles: Vec<PlaceId>,
}

/// Why α has no result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlphaError {
    /// A dereference of a reference: the places come from the abstract value
    /// of the reference (stage F3).
    NeedsValue {
        /// The local whose place has the reference.
        local: LocalId,
    },
    /// A place that a later stage handles.
    Later(&'static str),
    /// The place does not fit its type, or names no local: a bug of the
    /// builder.
    BadPlace(String),
}

/// The local that owns the value of local `l` of body `body`: the site local
/// of an upvar local, through each upvar local on the way.
///
/// # Errors
///
/// Returns [`AlphaError::BadPlace`] if a local or a parent does not exist.
pub fn owner_local(p: &Program, body: BodyId, l: LocalId) -> Result<(BodyId, LocalId), AlphaError> {
    let (mut body, mut l) = (body, l);
    // A parent has a lower id, so the walk ends.
    for _ in 0..=p.bodies.len() {
        let b = p
            .bodies
            .get(body.index())
            .ok_or_else(|| AlphaError::BadPlace(format!("no body b{}", body.0)))?;
        let d = b
            .locals
            .get(l.index())
            .ok_or_else(|| AlphaError::BadPlace(format!("no local _{} in b{}", l.0, body.0)))?;
        match d.kind {
            LocalKind::Upvar(site) => {
                body = b.parent.ok_or_else(|| {
                    AlphaError::BadPlace(format!("an upvar local of b{} with no parent", body.0))
                })?;
                l = site;
            }
            _ => return Ok((body, l)),
        }
    }
    Err(AlphaError::BadPlace(
        "an upvar chain with a cycle".to_string(),
    ))
}

/// The text of a local in the facts: its name, or what it is.
pub fn local_text(tys: &TyTable, d: &LocalDecl) -> String {
    if let Some(n) = &d.name {
        return n.clone();
    }
    match d.kind {
        LocalKind::Return => "the result".to_string(),
        LocalKind::Param(i) => format!("parameter {i}"),
        LocalKind::Env => "env".to_string(),
        LocalKind::User => "a local".to_string(),
        LocalKind::Temp(k) => format!("{} temporary", temp_text(k)),
        LocalKind::Iterator => "the iterator".to_string(),
        LocalKind::Cap(e) => {
            let name = tys
                .effects()
                .get(e.index())
                .map_or_else(String::new, |d| d.name.clone());
            format!("capability of handle {name}")
        }
        LocalKind::Kont(_) => "resume".to_string(),
        LocalKind::ScopeCap => "the scope capability".to_string(),
        LocalKind::TaskResult(_) => "a task result".to_string(),
        LocalKind::Upvar(_) => "an upvar".to_string(),
    }
}

/// The text of the kind of a temporary.
const fn temp_text(k: TempKind) -> &'static str {
    match k {
        TempKind::Operand => "operand",
        TempKind::Callee => "callee",
        TempKind::Receiver => "receiver",
        TempKind::Scrutinee => "scrutinee",
        TempKind::Borrowed => "borrowed",
        TempKind::Promoted => "promoted",
        TempKind::Discarded => "discarded",
        TempKind::Value => "value",
    }
}

impl Roots {
    /// The root place of the value of local `l` of body `body`. An upvar local
    /// has the root of its site local.
    ///
    /// # Errors
    ///
    /// Returns [`AlphaError::Later`] for the environment of a closure body,
    /// and [`AlphaError::BadPlace`] if the local does not exist.
    pub fn local(
        &mut self,
        p: &Program,
        tys: &TyTable,
        facts: &mut FnFacts,
        body: BodyId,
        l: LocalId,
    ) -> Result<PlaceId, AlphaError> {
        let key = owner_local(p, body, l)?;
        if let Some(&r) = self.locals.get(&key) {
            return Ok(r);
        }
        let d = p
            .bodies
            .get(key.0.index())
            .and_then(|b| b.locals.get(key.1.index()))
            .ok_or_else(|| AlphaError::BadPlace("no local".to_string()))?;
        if d.kind == LocalKind::Env {
            return Err(AlphaError::Later(
                "the environment of a closure (stage F11)",
            ));
        }
        let r = facts.add_root(local_text(tys, d), RootKind::Local);
        self.locals.insert(key, r);
        self.roles.insert(facts.place(r).root, Role::Local(key));
        Ok(r)
    }

    /// The `Param` root of parameter `i` of body `body`, with the text
    /// `name`: the pointee of a reference parameter, or the pointees of the
    /// references in a by-value parameter.
    pub fn param(&mut self, facts: &mut FnFacts, body: BodyId, i: u32, name: &str) -> PlaceId {
        if let Some(&r) = self.params.get(&(body, i)) {
            return r;
        }
        let r = facts.add_root(name, RootKind::Param);
        self.params.insert((body, i), r);
        self.roles.insert(facts.place(r).root, Role::Param(body, i));
        r
    }

    /// The `Held` root of parameter `i` of body `body` (the text `*name`):
    /// what the references behind the parameter point into. A caller puts
    /// in the places that the references in its argument point into.
    pub fn held(&mut self, facts: &mut FnFacts, body: BodyId, i: u32, name: &str) -> PlaceId {
        if let Some(&r) = self.helds.get(&(body, i)) {
            return r;
        }
        let r = facts.add_root(format!("*{name}"), RootKind::Param);
        self.helds.insert((body, i), r);
        self.roles.insert(facts.place(r).root, Role::Held(body, i));
        r
    }

    /// Gives the table the stated place of each place field of the structs
    /// of the program `prog` of the analysis.
    pub fn set_field_places(&mut self, prog: &crate::Program) {
        for (i, d) in prog.adts.iter().enumerate() {
            let crate::program::AdtKind::Struct(fs) = &d.kind else {
                continue;
            };
            let a = AdtId(u32::try_from(i).unwrap_or(u32::MAX));
            for (j, f) in fs.iter().enumerate() {
                if let Some(sp) = &f.place {
                    self.fields
                        .insert((a, u32::try_from(j).unwrap_or(u32::MAX)), sp.clone());
                }
            }
        }
    }

    /// The stated place of field `f` of struct `a`, if it is a place field.
    pub fn field_place(&self, a: AdtId, f: u32) -> Option<&crate::program::SigPlace> {
        self.fields.get(&(a, f))
    }

    /// What root `r` is, if this table made it.
    pub fn role(&self, r: RootId) -> Option<Role> {
        self.roles.get(&r).copied()
    }

    /// The roots of the values of the locals, with their keys.
    pub fn local_roots(&self) -> impl Iterator<Item = (Key, PlaceId)> + '_ {
        self.locals.iter().map(|(k, p)| (*k, *p))
    }

    /// True if `p` is a handle place `h.*` that α made.
    pub fn is_handle(&self, p: PlaceId) -> bool {
        self.handles.contains(&p)
    }

    /// The move path of fact place `p`, if its root is the value of a local:
    /// the local and the longest prefix of field and variant steps. A step
    /// of another kind (an element, a dereference, a wildcard) ends the
    /// path, so the path names the place or a place above it.
    pub fn path_of(&self, facts: &FnFacts, p: PlaceId) -> Option<(Key, Vec<PathStep>)> {
        let info = facts.places.get(p.index())?;
        let Some(Role::Local(key)) = self.role(info.root) else {
            return None;
        };
        let mut path = Vec::new();
        for s in &info.steps {
            match s.kind {
                StepKind::Field { id } if !weft_facts::is_wild_step(s) => {
                    path.push(PathStep::Field(id));
                }
                StepKind::Variant { id } => path.push(PathStep::Variant(id)),
                _ => break,
            }
        }
        Some((key, path))
    }

    /// The callee frame root of the run node `inst` (`docs/ir.md` 6.3): a
    /// local of the callee `callee` that the result points into.
    pub fn frame(&mut self, facts: &mut FnFacts, inst: u32, callee: &str) -> PlaceId {
        if let Some(&r) = self.frames.get(&inst) {
            return r;
        }
        let r = facts.add_root(format!("a local of {callee}"), RootKind::Local);
        self.frames.insert(inst, r);
        self.roles.insert(facts.place(r).root, Role::Frame(inst));
        r
    }

    /// The group root of the `rc` objects of definition `a` (a signature
    /// place `Group`).
    pub fn group_of_adt(&mut self, tys: &TyTable, facts: &mut FnFacts, a: AdtId) -> PlaceId {
        let key = GroupKey::Adt(a);
        if let Some(&r) = self.groups.get(&key) {
            return r;
        }
        let name = tys
            .adts()
            .get(a.index())
            .map_or_else(|| format!("group {}", a.0), |d| d.name.clone());
        let r = facts.add_root(name, RootKind::Group);
        self.groups.insert(key, r);
        self.roles.insert(facts.place(r).root, Role::Group);
        r
    }

    /// The group root of the `rc` type `inner` (the target of an `Rc`).
    pub fn group(&mut self, tys: &TyTable, facts: &mut FnFacts, inner: TyId) -> PlaceId {
        let key = match tys.try_get(inner) {
            Some(Ty::Adt(a, _)) => GroupKey::Adt(*a),
            _ => GroupKey::Ty(inner),
        };
        if let Some(&r) = self.groups.get(&key) {
            return r;
        }
        let name = match key {
            GroupKey::Adt(a) => tys
                .adts()
                .get(a.index())
                .map_or_else(|| tys.show(inner), |d| d.name.clone()),
            GroupKey::Ty(_) => tys.show(inner),
        };
        let r = facts.add_root(name, RootKind::Group);
        self.groups.insert(key, r);
        self.roles.insert(facts.place(r).root, Role::Group);
        r
    }
}

/// The type of a place on the way of α: a type, or the payload of a variant.
#[derive(Clone, Copy, Debug)]
enum At {
    /// A value of this type.
    Ty(TyId),
    /// The payload of variant `v` of the enum type `t`.
    Variant(TyId, u32),
}

/// The step and the text of one projection, and the type after it.
enum Next {
    /// A new step.
    Step(Step, String, At),
    /// No step: the place stays, the type changes.
    Same(At),
}

/// The type of a local of body `body`.
fn local_ty(p: &Program, body: BodyId, l: LocalId) -> Result<TyId, AlphaError> {
    p.bodies
        .get(body.index())
        .and_then(|b| b.locals.get(l.index()))
        .map(|d| d.ty)
        .ok_or_else(|| AlphaError::BadPlace(format!("no local _{} in b{}", l.0, body.0)))
}

/// The element step of a buffer type `t`, and the element type: `None` for a
/// slice (it names its elements), and an error for a type with no elements.
fn elem(tys: &TyTable, t: TyId) -> Result<(Option<bool>, TyId), AlphaError> {
    let bad = || AlphaError::BadPlace(format!("`{}` has no elements", tys.show(t)));
    match tys.try_get(t).ok_or_else(bad)? {
        Ty::Array(x, _) => Ok((Some(false), *x)),
        Ty::Slice(x) => Ok((None, *x)),
        Ty::Adt(a, args) => match tys.adts().get(a.index()).map(|d| &d.kind) {
            Some(AdtKind::Extern {
                elem_unstable: Some(u),
                ..
            }) => Ok((Some(*u), args.first().copied().ok_or_else(bad)?)),
            _ => Err(bad()),
        },
        _ => Err(bad()),
    }
}

/// The step of projection `pr` on a place of type `at`.
fn next(tys: &mut TyTable, at: At, pr: &Proj, last: Option<Step>) -> Result<Next, AlphaError> {
    let bad = |what: &str| AlphaError::BadPlace(format!("{what} does not fit the type"));
    let field = |id: u32| Step {
        kind: StepKind::Field { id },
        unstable: false,
    };
    match (at, pr) {
        (At::Variant(t, v), Proj::Field(f)) => {
            let (args, fields) = match tys.try_get(t) {
                Some(Ty::Adt(a, args)) => match tys.adts().get(a.index()).map(|d| &d.kind) {
                    Some(AdtKind::Enum(vs)) => (
                        args.clone(),
                        vs.get(v as usize)
                            .map(|x| x.fields.clone())
                            .unwrap_or_default(),
                    ),
                    _ => return Err(bad("a payload field")),
                },
                _ => return Err(bad("a payload field")),
            };
            let fty = *fields
                .get(f.index())
                .ok_or_else(|| bad("a payload field"))?;
            let fty = subst(tys, fty, &args);
            // The variant step names the payload of a variant with one field.
            if fields.len() == 1 {
                Ok(Next::Same(At::Ty(fty)))
            } else {
                Ok(Next::Step(field(f.0), format!(".{}", f.0), At::Ty(fty)))
            }
        }
        (At::Variant(..), _) => Err(bad("a projection of a payload")),
        (At::Ty(t), Proj::Field(f)) => match tys.try_get(t).cloned() {
            Some(Ty::Tuple(ts)) => {
                let x = *ts.get(f.index()).ok_or_else(|| bad("a tuple part"))?;
                Ok(Next::Step(field(f.0), format!(".{}", f.0), At::Ty(x)))
            }
            Some(Ty::Adt(a, args)) => {
                let fd = match tys.adts().get(a.index()).map(|d| &d.kind) {
                    Some(AdtKind::Struct(fs)) => fs.get(f.index()).cloned(),
                    _ => None,
                };
                let fd = fd.ok_or_else(|| bad("a field"))?;
                let x = subst(tys, fd.ty, &args);
                Ok(Next::Step(field(f.0), format!(".{}", fd.name), At::Ty(x)))
            }
            _ => Err(bad("a field")),
        },
        (At::Ty(t), Proj::Variant(v)) => {
            let name = match tys.try_get(t) {
                Some(Ty::Adt(a, _)) => match tys.adts().get(a.index()).map(|d| &d.kind) {
                    Some(AdtKind::Enum(vs)) => vs.get(v.index()).map(|x| x.name.clone()),
                    _ => None,
                },
                _ => None,
            };
            let name = name.ok_or_else(|| bad("a variant"))?;
            let step = Step {
                kind: StepKind::Variant { id: v.0 },
                unstable: true,
            };
            Ok(Next::Step(step, format!(".{name}"), At::Variant(t, v.0)))
        }
        (At::Ty(t), Proj::Index(_)) => {
            let (unstable, x) = elem(tys, t)?;
            Ok(match unstable {
                Some(u) => Next::Step(
                    Step {
                        kind: StepKind::Elem,
                        unstable: u,
                    },
                    "[]".to_string(),
                    At::Ty(x),
                ),
                None => Next::Same(At::Ty(x)),
            })
        }
        (At::Ty(t), Proj::Elems) => {
            let (unstable, x) = elem(tys, t)?;
            let slice = tys.intern(Ty::Slice(x));
            Ok(match unstable {
                Some(u) => Next::Step(
                    Step {
                        kind: StepKind::Elem,
                        unstable: u,
                    },
                    "[]".to_string(),
                    At::Ty(slice),
                ),
                None => Next::Same(At::Ty(slice)),
            })
        }
        (At::Ty(t), Proj::Split(s, side)) => {
            if !matches!(tys.try_get(t), Some(Ty::Slice(_))) {
                return Err(bad("a split"));
            }
            let hi = *side == Side::Right;
            // A side of a split moves with the elements that it names.
            let unstable = last.is_some_and(|l| l.kind == StepKind::Elem && l.unstable);
            let step = Step {
                kind: StepKind::Seg { split: s.0, hi },
                unstable,
            };
            let text = if hi { "[k..]" } else { "[..k]" };
            Ok(Next::Step(step, text.to_string(), At::Ty(t)))
        }
        (At::Ty(t), Proj::Deref(DerefKind::Box)) => {
            let (lang, deref, inner) = match tys.try_get(t) {
                Some(Ty::Adt(a, args)) => {
                    let d = tys.adts().get(a.index());
                    let deref = match d.map(|d| &d.kind) {
                        Some(AdtKind::Extern { deref, .. }) => *deref,
                        _ => None,
                    };
                    (d.and_then(|d| d.lang), deref, args.first().copied())
                }
                _ => (None, None, None),
            };
            let inner = inner.ok_or_else(|| bad("a dereference"))?;
            let unstable = match (lang, deref) {
                (_, Some(ExternDeref::Stable)) => false,
                (Some(Lang::Box), _) | (_, Some(ExternDeref::Unstable)) => true,
                _ => return Err(bad("a dereference")),
            };
            let step = Step {
                kind: StepKind::Deref,
                unstable,
            };
            Ok(Next::Step(step, String::new(), At::Ty(inner)))
        }
        (At::Ty(_), Proj::Deref(DerefKind::Rc | DerefKind::Ref)) => {
            Err(AlphaError::BadPlace("a dereference outside α".to_string()))
        }
    }
}

/// α of `place` of body `body` (`docs/ir.md` 6.3), with no state.
///
/// The result is the fact places that the place can be, with its pointer
/// places and its handle places. The roots go to `roots` and the places to
/// `facts`. `tys` gets the instances of generic
/// field types and the slice types of `Elems`.
///
/// # Errors
///
/// Returns [`AlphaError::NeedsValue`] for a `Deref(Ref)` (the analysis gives
/// the value, [`alpha_with`]), [`AlphaError::Later`] for an environment field
/// (stage F11), and [`AlphaError::BadPlace`] for a place that does not fit
/// its type.
pub fn alpha(
    p: &Program,
    tys: &mut TyTable,
    facts: &mut FnFacts,
    roots: &mut Roots,
    body: BodyId,
    place: &Place,
) -> Result<Alpha, AlphaError> {
    let local = place.local;
    alpha_with(p, tys, facts, roots, body, place, &mut |_, _, _, _| {
        Err(AlphaError::NeedsValue { local })
    })
}

/// The function that gives the places that the reference at a fact place
/// points into ([`alpha_with`]).
///
/// The last argument is the struct and the field that the place names, if
/// its last step is a field of a struct.
pub type Pointees<'a> = dyn FnMut(
        &mut FnFacts,
        &mut Roots,
        PlaceId,
        Option<(AdtId, u32)>,
    ) -> Result<Vec<PlaceId>, AlphaError>
    + 'a;

/// α of `place` of body `body`, with `pointees` for each `Deref(Ref)`: it
/// gives the places that the reference at a fact place points into.
///
/// # Errors
///
/// The errors of `pointees`, [`AlphaError::Later`] for an environment field
/// (stage F11), and [`AlphaError::BadPlace`] for a place that does not fit
/// its type.
pub fn alpha_with(
    p: &Program,
    tys: &mut TyTable,
    facts: &mut FnFacts,
    roots: &mut Roots,
    body: BodyId,
    place: &Place,
    pointees: &mut Pointees<'_>,
) -> Result<Alpha, AlphaError> {
    let root = roots.local(p, tys, facts, body, place.local)?;
    let mut at = At::Ty(local_ty(p, body, place.local)?);
    let mut out = Alpha {
        places: vec![root],
        ..Alpha::default()
    };
    let mut last: Option<Step> = None;
    // The struct and the field of the last projection, if it is a field of
    // a struct.
    let mut field: Option<(AdtId, u32)> = None;
    for pr in &place.proj {
        let named = match (at, pr) {
            (At::Ty(t), Proj::Field(f)) => match tys.try_get(t) {
                Some(Ty::Adt(a, _)) => Some((*a, f.0)),
                _ => None,
            },
            _ => None,
        };
        match pr {
            Proj::Deref(DerefKind::Ref) => {
                let At::Ty(t) = at else {
                    return Err(AlphaError::BadPlace(
                        "a dereference of a payload".to_string(),
                    ));
                };
                let inner = match tys.try_get(t) {
                    Some(Ty::Ref(x)) => *x,
                    _ => {
                        return Err(AlphaError::BadPlace(format!(
                            "`{}` is not a reference",
                            tys.show(t)
                        )))
                    }
                };
                let mut to = Vec::new();
                for &r in &out.places {
                    out.ptrs.push(r);
                    to.extend(pointees(facts, roots, r, field)?);
                }
                to.sort();
                to.dedup();
                out.places = to;
                at = At::Ty(inner);
                last = None;
            }
            Proj::Deref(DerefKind::Rc) => {
                let At::Ty(t) = at else {
                    return Err(AlphaError::BadPlace(
                        "a dereference of a payload".to_string(),
                    ));
                };
                let inner = match tys.try_get(t) {
                    Some(Ty::Adt(_, args)) => args.first().copied(),
                    _ => None,
                };
                let inner = inner.ok_or_else(|| {
                    AlphaError::BadPlace(format!("`{}` is not an `Rc`", tys.show(t)))
                })?;
                let handle = Step {
                    kind: StepKind::Deref,
                    unstable: true,
                };
                for &h in &out.places {
                    out.ptrs.push(h);
                    let hp = facts.child(h, handle, ".*");
                    roots.handles.insert(hp);
                    out.handles.push(hp);
                }
                out.places = vec![roots.group(tys, facts, inner)];
                at = At::Ty(inner);
                last = None;
            }
            _ => {
                if matches!(pr, Proj::Deref(_)) {
                    out.ptrs.extend(out.places.iter().copied());
                }
                match next(tys, at, pr, last)? {
                    Next::Step(step, text, after) => {
                        out.places = out
                            .places
                            .iter()
                            .map(|&q| facts.child(q, step, &text))
                            .collect();
                        last = Some(step);
                        at = after;
                    }
                    Next::Same(after) => at = after,
                }
            }
        }
        field = named;
    }
    out.places.sort();
    out.places.dedup();
    out.ptrs.sort();
    out.ptrs.dedup();
    out.handles.sort();
    out.handles.dedup();
    Ok(out)
}

/// The text of a move path `place` of body `body`: the text of the fact place
/// that α gives, with no place made. A step that α cannot give ends the text.
pub fn path_text(p: &Program, tys: &mut TyTable, body: BodyId, place: &Place) -> String {
    let base = owner_local(p, body, place.local)
        .ok()
        .and_then(|(b, l)| {
            p.bodies
                .get(b.index())
                .and_then(|x| x.locals.get(l.index()))
        })
        .map_or_else(|| format!("_{}", place.local.0), |d| local_text(tys, d));
    let Ok(t) = local_ty(p, body, place.local) else {
        return base;
    };
    let mut text = base;
    let mut at = At::Ty(t);
    let mut last = None;
    for pr in &place.proj {
        match next(tys, at, pr, last) {
            Ok(Next::Step(step, s, after)) => {
                text.push_str(&s);
                last = Some(step);
                at = after;
            }
            Ok(Next::Same(after)) => at = after,
            Err(_) => break,
        }
    }
    text
}

/// The type of a move path `place` of body `body` (a place with no
/// `Deref`), or `None` if it does not fit its type.
pub fn path_ty(p: &Program, tys: &mut TyTable, body: BodyId, place: &Place) -> Option<TyId> {
    let mut at = At::Ty(local_ty(p, body, place.local).ok()?);
    let mut last = None;
    for pr in &place.proj {
        match next(tys, at, pr, last).ok()? {
            Next::Step(step, _, after) => {
                last = Some(step);
                at = after;
            }
            Next::Same(after) => at = after,
        }
    }
    match at {
        At::Ty(t) => Some(t),
        At::Variant(..) => None,
    }
}

/// The type of `place` of body `body`: a place with any projection, also
/// through a reference, a `Box` or an `Rc`. `None` if it does not fit its
/// type, or if it names a payload with no type of its own.
pub fn place_ty(p: &Program, tys: &mut TyTable, body: BodyId, place: &Place) -> Option<TyId> {
    let mut at = At::Ty(local_ty(p, body, place.local).ok()?);
    let mut last = None;
    for pr in &place.proj {
        match (at, pr) {
            (At::Ty(t), Proj::Deref(DerefKind::Ref)) => match tys.try_get(t)? {
                Ty::Ref(x) => {
                    at = At::Ty(*x);
                    last = None;
                }
                _ => return None,
            },
            (At::Ty(t), Proj::Deref(DerefKind::Rc)) => match tys.try_get(t)? {
                Ty::Adt(_, args) => {
                    at = At::Ty(*args.first()?);
                    last = None;
                }
                _ => return None,
            },
            _ => match next(tys, at, pr, last).ok()? {
                Next::Step(step, _, after) => {
                    last = Some(step);
                    at = after;
                }
                Next::Same(after) => at = after,
            },
        }
    }
    match at {
        At::Ty(t) => Some(t),
        At::Variant(..) => None,
    }
}
