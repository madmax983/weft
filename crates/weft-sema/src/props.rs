//! Type properties of the definitions: linear, nonportable, `!Move`, and others.
//!
//! A property such as `linear` holds for a type if a part of the type has it. A
//! struct field, a tuple part, an array element, an enum payload and an
//! argument of an extern type such as `Vec<T>` are parts.
//!
//! For each definition, [`TypeProps`] keeps two things: whether the property
//! holds for every instance, and the type parameters that pass the property on.
//! `Option<T>` passes `linear` on from `T`, so `Option<Tx>` is linear and
//! `Option<u64>` is not. One least fixpoint over all definitions computes the
//! table, with a worklist. A definition changes at most once for each of its
//! type parameters and once more, so the fixpoint stops. A recursive type costs
//! no more than another type, and the depth of nesting has no limit. An instance
//! is then one walk over its type term (`Lower::ty_has`).

use crate::program::{AdtKind, Program, PRELUDE};
use crate::types::{AdtId, Ty};
use weft_ir::ty::{Lang, Props, Ty as IrTy, TyId, TyProp, TyTable};

/// A property of a type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Prop {
    /// A part is a linear value.
    Linear,
    /// A part cannot cross threads.
    Nonportable,
    /// A part keeps its address (`!Move`). A pointer such as `Box<T>` does not
    /// pass it on: its target does not move with it.
    Immovable,
    /// A part is a reference or a slice.
    Refs,
    /// A part is a function value.
    Fns,
    /// A part is not plain data: the value moves, it is not copied.
    NotCopy,
    /// A linear part has no `on abort`, and no type around it on the way has
    /// one. A type with `on abort` finishes its parts itself.
    NoOnAbort,
    /// A part is a resource that a `multi` resume cannot copy: a task handle, a
    /// scope, or a value of an extern type that is not plain data, not a buffer
    /// (`Vec`, `Box`) and not an `rc` handle. A resume copies a buffer, and the
    /// copies share an `rc` object, so `Rc` and `Weak` do not pass it on.
    Resource,
}

/// The properties, in table order.
pub const PROPS: [Prop; 8] = [
    Prop::Linear,
    Prop::Nonportable,
    Prop::Immovable,
    Prop::Refs,
    Prop::Fns,
    Prop::NotCopy,
    Prop::NoOnAbort,
    Prop::Resource,
];

impl Prop {
    const fn index(self) -> usize {
        match self {
            Self::Linear => 0,
            Self::Nonportable => 1,
            Self::Immovable => 2,
            Self::Refs => 3,
            Self::Fns => 4,
            Self::NotCopy => 5,
            Self::NoOnAbort => 6,
            Self::Resource => 7,
        }
    }
}

/// When a property holds for the instances of a definition.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Holds {
    /// The property holds for every instance.
    pub always: bool,
    /// The type parameters that pass the property on, in order: the property
    /// holds for an instance if it holds for one of these arguments.
    pub params: Vec<usize>,
}

impl Holds {
    fn join(&mut self, o: &Self) {
        self.always |= o.always;
        for &p in &o.params {
            if !self.params.contains(&p) {
                self.params.push(p);
            }
        }
        self.params.sort_unstable();
    }
}

/// The properties of each definition, by `AdtId`.
#[derive(Clone, Debug, Default)]
pub struct TypeProps {
    table: Vec<[Holds; 8]>,
    /// For each definition: a value of an instance can hold a place field.
    /// The type arguments do not count: a type term names them itself.
    places: Vec<bool>,
    /// For each definition on a cycle of the graph of inline parts: the
    /// number of its cycle (its strongly connected component).
    cycles: Vec<Option<u32>>,
}

impl TypeProps {
    /// Computes the table for every definition of `prog`.
    pub fn new(prog: &Program) -> Self {
        let cycles = adt_cycles(prog);
        Self {
            table: fixpoint(prog, &cycles).0,
            places: place_holders(prog),
            cycles,
        }
    }

    /// Returns when property `p` holds for the instances of definition `a`.
    pub fn get(&self, a: AdtId, p: Prop) -> Option<&Holds> {
        self.table.get(a.index()).map(|h| &h[p.index()])
    }

    /// Returns the number of the cycle of definition `a`, if a value of `a`
    /// can hold a value of a definition on the same cycle (`a` itself too).
    pub fn cycle(&self, a: AdtId) -> Option<u32> {
        self.cycles.get(a.index()).copied().flatten()
    }

    /// Returns true if a value of type `t` can hold a place field: in the
    /// value, in its parts, or behind a `Box`. The answer can be true for a
    /// type that holds none, but it is never false for a type that holds one.
    pub fn may_hold_place_field(&self, t: &Ty) -> bool {
        let mut found = false;
        each_inline_adt(t, &mut |a| {
            found |= self.places.get(a).copied().unwrap_or(false);
        });
        found
    }
}

/// Computes the table for every definition of `prog`, and the number of
/// evaluations of a definition that the worklist made (the work).
fn fixpoint(prog: &Program, cycles: &[Option<u32>]) -> (Vec<[Holds; 8]>, usize) {
    let n = prog.adts.len();
    let mut table: Vec<[Holds; 8]> = vec![Default::default(); n];
    // The definitions that name each definition in their parts.
    let mut users: Vec<Vec<usize>> = vec![Vec::new(); n];
    for a in 0..n {
        for t in parts(prog, a) {
            each_adt(&t, &mut |b| {
                if b < n && !users[b].contains(&a) {
                    users[b].push(a);
                }
            });
        }
    }
    // A type that holds itself has its parts in heap cells, as an enum
    // payload does: it is not plain data.
    let recursive: Vec<bool> = cycles.iter().map(Option::is_some).collect();
    for (a, &r) in recursive.iter().enumerate() {
        table[a][Prop::NotCopy.index()].always = r;
    }
    let mut work: Vec<usize> = (0..n).rev().collect();
    let mut queued = vec![true; n];
    let mut evals = 0;
    while let Some(a) = work.pop() {
        queued[a] = false;
        evals += 1;
        let mut new = eval_adt(prog, a, &table);
        new[Prop::NotCopy.index()].always |= recursive[a];
        if new != table[a] {
            table[a] = new;
            for &u in &users[a] {
                if !queued[u] {
                    queued[u] = true;
                    work.push(u);
                }
            }
        }
    }
    (table, evals)
}

impl Program {
    /// Returns the type properties of the definitions. The first call computes them.
    pub fn props(&self) -> &TypeProps {
        self.props.get_or_init(|| TypeProps::new(self))
    }

    /// Returns true if a value of the resolved type `t` can hold a reference. A
    /// type parameter does not count: the body cannot read a reference out of it.
    pub fn ty_holds_refs(&self, t: &Ty) -> bool {
        match t {
            Ty::Ref(_) | Ty::Slice(_) => true,
            Ty::Adt(a, args) => self.props().get(*a, Prop::Refs).is_some_and(|h| {
                h.always
                    || h.params
                        .iter()
                        .any(|&j| args.get(j).is_some_and(|x| self.ty_holds_refs(x)))
            }),
            Ty::Tuple(ts) => ts.iter().any(|x| self.ty_holds_refs(x)),
            Ty::Array(x, _) => self.ty_holds_refs(x),
            _ => false,
        }
    }

    /// Returns true if a value of the resolved type `t` can hold a linear
    /// value. A type parameter counts: a caller can give it a linear type. A
    /// function value counts too: a closure that moves a linear value is
    /// linear (ADR 0007).
    pub fn ty_may_hold_linear(&self, t: &Ty) -> bool {
        match t {
            Ty::Param(_) | Ty::Fn(_) => true,
            Ty::Adt(a, args) => self.props().get(*a, Prop::Linear).is_some_and(|h| {
                h.always
                    || h.params
                        .iter()
                        .any(|&j| args.get(j).is_some_and(|x| self.ty_may_hold_linear(x)))
            }),
            Ty::Tuple(ts) => ts.iter().any(|x| self.ty_may_hold_linear(x)),
            Ty::Array(x, _) => self.ty_may_hold_linear(x),
            _ => false,
        }
    }
}

/// Returns the part types of definition `a`, with its type parameters as
/// `Ty::Param`. An extern type has its type arguments as parts.
fn parts(prog: &Program, a: usize) -> Vec<Ty> {
    let def = &prog.adts[a];
    match &def.kind {
        AdtKind::Struct(fs) => fs.iter().map(|f| f.ty.clone()).collect(),
        AdtKind::Enum(vs) => vs.iter().flat_map(|v| v.fields.iter().cloned()).collect(),
        AdtKind::Extern { .. } => (0..def.generics.len())
            .map(|i| Ty::Param(u32::try_from(i).unwrap_or(u32::MAX)))
            .collect(),
    }
}

/// Calls `f` for each definition that type `t` names.
fn each_adt(t: &Ty, f: &mut dyn FnMut(usize)) {
    match t {
        Ty::Adt(a, args) => {
            f(a.index());
            for x in args {
                each_adt(x, f);
            }
        }
        Ty::Tuple(ts) => ts.iter().for_each(|x| each_adt(x, f)),
        Ty::Ref(x) | Ty::Slice(x) | Ty::Array(x, _) => each_adt(x, f),
        Ty::Cont(x, y) => {
            each_adt(x, f);
            each_adt(y, f);
        }
        Ty::Fn(ft) => {
            ft.params.iter().for_each(|x| each_adt(x, f));
            each_adt(&ft.ret, f);
        }
        _ => {}
    }
}

/// Calls `f` for each definition that a value of type `t` holds inline: not
/// behind a reference or in a function value.
fn each_inline_adt(t: &Ty, f: &mut dyn FnMut(usize)) {
    match t {
        Ty::Adt(a, args) => {
            f(a.index());
            for x in args {
                each_inline_adt(x, f);
            }
        }
        Ty::Tuple(ts) => ts.iter().for_each(|x| each_inline_adt(x, f)),
        Ty::Array(x, _) => each_inline_adt(x, f),
        _ => {}
    }
}

/// Returns, for each definition, the number of its cycle if a value of it can
/// hold a value of the same definition. The definition is then on a cycle of
/// the graph of inline parts, and each definition on the same cycle (the same
/// strongly connected component) gets the same number. The search is Tarjan's
/// algorithm, with an explicit stack.
fn adt_cycles(prog: &Program) -> Vec<Option<u32>> {
    let n = prog.adts.len();
    let edges = inline_edges(prog);
    let mut cycles: Vec<Option<u32>> = vec![None; n];
    let mut count: u32 = 0;
    let mut self_loop = vec![false; n];
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next = 0;
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        // Each frame is a definition and the position of its next edge.
        let mut frames: Vec<(usize, usize)> = vec![(root, 0)];
        index[root] = next;
        low[root] = next;
        next += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&mut (a, ref mut e)) = frames.last_mut() {
            if let Some(&b) = edges[a].get(*e) {
                *e += 1;
                if b == a {
                    self_loop[a] = true;
                }
                if index[b] == usize::MAX {
                    index[b] = next;
                    low[b] = next;
                    next += 1;
                    stack.push(b);
                    on_stack[b] = true;
                    frames.push((b, 0));
                } else if on_stack[b] {
                    low[a] = low[a].min(index[b]);
                }
                continue;
            }
            frames.pop();
            if let Some(&(parent, _)) = frames.last() {
                low[parent] = low[parent].min(low[a]);
            }
            if low[a] == index[a] {
                let mut members = Vec::new();
                while let Some(b) = stack.pop() {
                    on_stack[b] = false;
                    members.push(b);
                    if b == a {
                        break;
                    }
                }
                if members.len() > 1 || self_loop[a] {
                    for b in members {
                        cycles[b] = Some(count);
                    }
                    count += 1;
                }
            }
        }
    }
    cycles
}

/// Returns, for each definition, the definitions that its parts hold inline.
fn inline_edges(prog: &Program) -> Vec<Vec<usize>> {
    let n = prog.adts.len();
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (a, out) in edges.iter_mut().enumerate() {
        for t in parts(prog, a) {
            each_inline_adt(&t, &mut |b| {
                if b < n && !out.contains(&b) {
                    out.push(b);
                }
            });
        }
    }
    edges
}

/// Returns, for each definition, true if a value of it can hold a place field:
/// the definition has one, or one of its parts holds a definition that can
/// hold one. The search goes back from the definitions with a place field.
fn place_holders(prog: &Program) -> Vec<bool> {
    let n = prog.adts.len();
    let mut users: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (a, out) in inline_edges(prog).into_iter().enumerate() {
        for b in out {
            users[b].push(a);
        }
    }
    let mut holds: Vec<bool> = prog
        .adts
        .iter()
        .map(|d| matches!(&d.kind, AdtKind::Struct(fs) if fs.iter().any(|f| f.place.is_some())))
        .collect();
    let mut work: Vec<usize> = (0..n).filter(|&a| holds[a]).collect();
    while let Some(b) = work.pop() {
        for &a in &users[b] {
            if !holds[a] {
                holds[a] = true;
                work.push(a);
            }
        }
    }
    holds
}

/// Returns true if the extern or capability type `a` is plain data: values of it are copied.
fn extern_copy(prog: &Program, a: usize) -> bool {
    let def = &prog.adts[a];
    let capability_like = def.module == PRELUDE
        || matches!(
            def.kind,
            AdtKind::Extern {
                elem_unstable: None,
                deref: None
            }
        );
    def.copy
        || (def.generics.is_empty()
            && !def.nonportable
            && !def.linear
            && def.name != "String"
            && capability_like)
}

/// Computes the row of definition `a` from the rows of the definitions in `table`.
fn eval_adt(prog: &Program, a: usize, table: &[[Holds; 8]]) -> [Holds; 8] {
    let def = &prog.adts[a];
    let parts = parts(prog, a);
    let ext = match &def.kind {
        AdtKind::Extern {
            elem_unstable,
            deref,
        } => Some((*elem_unstable, *deref)),
        _ => None,
    };
    let mut out: [Holds; 8] = Default::default();
    for p in PROPS {
        let h = &mut out[p.index()];
        let passes = match (p, ext) {
            // A pointer does not move its target, and plain data has no `!Move` part.
            // A prelude type with no elements, such as `Weak<T>`, is a pointer or a
            // handle. A user type can hold its arguments inline.
            (Prop::Immovable, Some((elem, deref))) => {
                deref.is_none()
                    && (elem.is_some() || (def.module != PRELUDE && !extern_copy(prog, a)))
            }
            // An extern type is plain data or not, whatever its arguments are.
            (Prop::NotCopy, Some(_)) => false,
            // The copies of a resume share an `rc` object and what it holds.
            (Prop::Resource, Some(_)) => !is_rc_handle(prog, AdtId(a)),
            _ => true,
        };
        h.always = match p {
            Prop::Linear => def.linear,
            Prop::Nonportable => def.nonportable,
            Prop::Immovable => def.immovable,
            Prop::NotCopy => {
                def.linear || def.immovable || (ext.is_some() && !extern_copy(prog, a))
            }
            Prop::NoOnAbort => def.linear && !def.has_on_abort,
            // A `!Move` value keeps its address, so a copy cannot stand for it,
            // also inside a buffer.
            Prop::Resource => {
                let buffer = def.module == PRELUDE && matches!(def.name.as_str(), "Vec" | "Box");
                def.immovable
                    || (ext.is_some()
                        && !extern_copy(prog, a)
                        && !is_rc_handle(prog, AdtId(a))
                        && !buffer)
            }
            Prop::Refs | Prop::Fns => false,
        };
        // A type with `on abort` finishes its linear parts. The `on abort` of a
        // task handle only cancels the task, and a cancel does not finish the
        // result of a task that is done. So `Task<T>` passes it on from `T`
        // (review round 3, F3-6).
        if !passes || (p == Prop::NoOnAbort && def.has_on_abort && !is_task_handle(prog, AdtId(a)))
        {
            continue;
        }
        for t in &parts {
            h.join(&eval(prog, t, p, table));
        }
    }
    out
}

/// Returns when property `p` holds for type term `t` of a definition of
/// `prog`, from the rows in `table`.
fn eval(prog: &Program, t: &Ty, p: Prop, table: &[[Holds; 8]]) -> Holds {
    let always = |b: bool| Holds {
        always: b,
        params: Vec::new(),
    };
    match t {
        Ty::Param(i) => Holds {
            always: false,
            params: vec![*i as usize],
        },
        // The copies of a resume share an `rc` object. A function value or a
        // reference in it still points into the locals of the first run, so a
        // handle to such an object is not `many`. If that depends on a type
        // parameter, the property holds for every instance.
        Ty::Adt(b, args) if p == Prop::Resource && is_rc_handle(prog, *b) => {
            let Some(x) = args.first() else {
                return Holds::default();
            };
            let mut h = eval(prog, x, Prop::Fns, table);
            h.join(&eval(prog, x, Prop::Refs, table));
            always(h.always || !h.params.is_empty())
        }
        Ty::Adt(b, args) => {
            let Some(row) = table.get(b.index()) else {
                return Holds::default();
            };
            let h = &row[p.index()];
            let mut out = always(h.always);
            for &j in &h.params {
                if let Some(x) = args.get(j) {
                    out.join(&eval(prog, x, p, table));
                }
            }
            out
        }
        Ty::Tuple(ts) => {
            let mut out = Holds::default();
            for x in ts {
                out.join(&eval(prog, x, p, table));
            }
            out
        }
        Ty::Array(..) if p == Prop::NotCopy => always(true),
        Ty::Array(x, _) => eval(prog, x, p, table),
        Ty::Ref(x) => match p {
            Prop::Refs => always(true),
            Prop::Fns => eval(prog, x, p, table),
            _ => Holds::default(),
        },
        Ty::Slice(x) => match p {
            Prop::Refs | Prop::NotCopy => always(true),
            Prop::Fns => eval(prog, x, p, table),
            _ => Holds::default(),
        },
        Ty::Fn(_) => always(p == Prop::Fns),
        Ty::Cont(..) => always(p == Prop::NotCopy),
        Ty::Scope => always(matches!(p, Prop::Nonportable | Prop::Resource)),
        _ => Holds::default(),
    }
}

/// Returns true if definition `a` is the prelude `Rc` or `Weak`: a handle to a
/// shared `rc` object.
pub(crate) fn is_rc_handle(prog: &Program, a: AdtId) -> bool {
    let def = &prog.adts[a];
    def.module == PRELUDE && matches!(def.name.as_str(), "Rc" | "Weak")
}

/// Returns true if definition `a` is the prelude type `Task<T>`.
fn is_task_handle(prog: &Program, a: AdtId) -> bool {
    let def = &prog.adts[a];
    def.module == PRELUDE && def.name == "Task"
}

// ---------------------------------------------------------------------------
// Properties of the final types of the IR
// ---------------------------------------------------------------------------

/// Returns the property of the IR for property `p`.
pub const fn ir_prop(p: Prop) -> TyProp {
    match p {
        Prop::Linear => TyProp::Linear,
        Prop::Nonportable => TyProp::Nonportable,
        Prop::Immovable => TyProp::Immovable,
        Prop::Refs => TyProp::Refs,
        Prop::Fns => TyProp::Fns,
        Prop::NotCopy => TyProp::NotCopy,
        Prop::NoOnAbort => TyProp::NoOnAbort,
        Prop::Resource => TyProp::Resource,
    }
}

/// Returns the properties of the final type `t` (`docs/ir.md` 2.3, 3.2).
///
/// They are the flags that the old lowering gives a variable of type `t`
/// (`Lower::var_info`, `Lower::is_copy`, `Lower::holds_refs`), with two
/// differences. A function type has no closure summary, so a function value
/// gets only `callable`: the analysis adds the properties of the closures that
/// it can be. And `uniq` is false: the mode `@ uniq` is in the declaration, not
/// in the type. A type parameter is not linear here; `generic` tells that a
/// caller can give it a linear type.
pub fn ir_props(table: &TyTable, t: TyId) -> Props {
    let has = |p| ir_has(table, t, p);
    let top = table.try_get(t);
    let linear = has(TyProp::Linear);
    Props {
        // One source of the copy property: the verifier of the IR uses it too.
        copy: !table.not_copy(t),
        linear,
        on_abort: !has(TyProp::NoOnAbort),
        // A value that a `multi` resume cannot copy is not `many` either.
        once: linear || has(TyProp::Resource) || matches!(top, Some(IrTy::Cont(..))),
        immovable: has(TyProp::Immovable),
        nonportable: has(TyProp::Nonportable),
        uniq: false,
        callable: matches!(top, Some(IrTy::Fn(_))),
        generic: table.mentions_param(t),
        holds_refs: has(TyProp::Refs),
    }
}

/// Returns true if a borrow of a value of the final type `t` puts the value
/// into a promoted temporary (`docs/ir.md` 5.10).
///
/// The value is plain data, and no part is a function value or a resource.
/// This is the temporary of a borrow that the old lowering gives no variable
/// (`Lower::temp_root`): a temporary that is plain data never goes out of
/// scope there.
pub fn ir_promotes(table: &TyTable, t: TyId) -> bool {
    !table.not_copy(t) && !ir_has(table, t, TyProp::Fns) && !ir_has(table, t, TyProp::Resource)
}

/// Returns true if a value of the final type `t` can be linear.
///
/// A part of it is linear, or a part of it is a type parameter. This is
/// `linear` in a generic body of the old lowering (`Lower::generic`). The
/// builder of the IR uses it for the `Drop` before a store behind a pointer
/// (`docs/ir.md` 5.1.3, rule V17).
pub fn ir_maybe_linear(table: &TyTable, t: TyId) -> bool {
    ir_has_in(table, t, TyProp::Linear, true)
}

/// Returns true if property `p` holds for a value of the final type `t`: a
/// part of it has the property. The rows of the definitions come from the
/// table. The cases are the cases of `Lower::ty_has_in` for a type with no
/// inference variable and no closure summary, and with a type parameter that
/// is not linear.
fn ir_has(table: &TyTable, t: TyId, p: TyProp) -> bool {
    ir_has_in(table, t, p, false)
}

/// [`ir_has`]; with `params`, a type parameter is linear.
fn ir_has_in(table: &TyTable, t: TyId, p: TyProp, params: bool) -> bool {
    let Some(ty) = table.try_get(t) else {
        return false;
    };
    let h = |x: TyId| ir_has_in(table, x, p, params);
    let lang = |a: weft_ir::AdtId| table.adts().get(a.index()).and_then(|d| d.lang);
    match ty {
        // The copies of a `multi` resume share an `rc` object: a function
        // value or a reference in it points into the locals of one run.
        IrTy::Adt(a, args)
            if p == TyProp::Resource && matches!(lang(*a), Some(Lang::Rc | Lang::Weak)) =>
        {
            args.first()
                .is_some_and(|&x| ir_has(table, x, TyProp::Fns) || ir_has(table, x, TyProp::Refs))
        }
        IrTy::Adt(a, args) => table.adts().get(a.index()).is_some_and(|d| {
            let row = d.row(p);
            row.always
                || row
                    .params
                    .iter()
                    .any(|&j| args.get(j as usize).is_some_and(|&x| h(x)))
        }),
        IrTy::Tuple(ts) => ts.iter().any(|&x| h(x)),
        IrTy::Array(x, _) => p == TyProp::NotCopy || h(*x),
        // A reference to a nonportable value is nonportable: another thread
        // could use the value through it.
        IrTy::Ref(x) => match p {
            TyProp::Refs => true,
            TyProp::Fns | TyProp::Nonportable => h(*x),
            _ => false,
        },
        // An iterator of a `for` loop can point into its collection, as a slice does.
        IrTy::Slice(x) | IrTy::Iter(x) => match p {
            TyProp::Refs | TyProp::NotCopy => true,
            TyProp::Fns | TyProp::Nonportable => h(*x),
            _ => false,
        },
        IrTy::Fn(_) => p == TyProp::Fns,
        IrTy::Param(_) => p == TyProp::NotCopy || (p == TyProp::Linear && params),
        IrTy::Cont(..) => p == TyProp::NotCopy,
        IrTy::Scope => matches!(p, TyProp::Nonportable | TyProp::Resource),
        // A capability value is plain data: a copy names the same handler.
        IrTy::Cap(_) | IrTy::Unit | IrTy::Bool | IrTy::Never | IrTy::Int(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{analyze_source, Options};

    fn adt(prog: &Program, name: &str) -> AdtId {
        AdtId(
            prog.adts
                .iter()
                .position(|a| a.name == name)
                .unwrap_or(usize::MAX),
        )
    }

    #[test]
    fn properties_pass_through_parts_and_parameters() {
        let src = "linear struct Tok { id: u64 }\n\
                   struct W0 { t: Tok }\n\
                   struct W1 { w: W0 }\n\
                   struct Wrap<T> { x: T }\n\
                   struct Frame: !Move { buf: [u8; 4] }\n\
                   struct Outer { f: Frame }\n\
                   struct Boxed { f: Box<Frame> }\n\
                   struct Loop { next: Option<Box<Loop>>, t: Tok }\n\
                   struct Hook { f: fn() }\n\
                   struct Hooks { h: Rc<Hook> }\n\
                   struct Nums { n: Rc<u64> }\n\
                   struct Gen<T> { r: Rc<T> }\n";
        let Ok(a) = analyze_source(src, Options::default()) else {
            unreachable!("the source parses")
        };
        let p = a.program.props();
        let get = |n: &str, k: Prop| p.get(adt(&a.program, n), k).cloned().unwrap_or_default();
        assert!(get("W1", Prop::Linear).always);
        assert!(!get("Wrap", Prop::Linear).always);
        assert_eq!(get("Wrap", Prop::Linear).params, vec![0]);
        assert_eq!(get("Option", Prop::Linear).params, vec![0]);
        assert!(get("Outer", Prop::Immovable).always);
        assert!(!get("Boxed", Prop::Immovable).always);
        assert!(get("Loop", Prop::Linear).always);
        assert!(get("Loop", Prop::NoOnAbort).always);
        assert!(get("Task", Prop::Linear).always);
        assert!(!get("Task", Prop::NoOnAbort).always);
        assert_eq!(get("Task", Prop::NoOnAbort).params, vec![0]);
        assert!(get("Vec", Prop::NotCopy).always);
        assert_eq!(get("Vec", Prop::Immovable).params, vec![0]);
        assert!(get("Box", Prop::Immovable).params.is_empty());
        assert!(get("Weak", Prop::Immovable).params.is_empty());
        // A resume copies a buffer and shares an `rc` object. It cannot copy a
        // task or a scope.
        assert!(get("Task", Prop::Resource).always);
        assert!(get("Scope", Prop::Resource).always);
        assert!(!get("Vec", Prop::Resource).always);
        assert_eq!(get("Vec", Prop::Resource).params, vec![0]);
        assert!(get("Rc", Prop::Resource).params.is_empty());
        assert!(!get("Rc", Prop::Resource).always);
        assert!(!get("String", Prop::Resource).always);
        // A `!Move` value keeps its address, also in a buffer.
        assert!(get("Frame", Prop::Resource).always);
        assert!(get("Boxed", Prop::Resource).always);
        // The copies share an `rc` object, and a function value in it.
        assert!(get("Hooks", Prop::Resource).always);
        assert!(!get("Nums", Prop::Resource).always);
        assert!(get("Gen", Prop::Resource).always);
    }

    #[test]
    fn a_type_that_holds_itself_is_not_plain_data() {
        let src = "enum List { Cons(u64, List), Nil }\n\
                   enum A { X(B), Y }\n\
                   enum B { Z(A) }\n\
                   struct P { a: u64, b: (u64, bool) }\n\
                   struct R: !Move { me: &R in self }\n";
        let Ok(a) = analyze_source(src, Options::default()) else {
            unreachable!("the source parses")
        };
        let p = a.program.props();
        let not_copy = |n: &str| {
            p.get(adt(&a.program, n), Prop::NotCopy)
                .is_some_and(|h| h.always)
        };
        assert!(not_copy("List"));
        assert!(not_copy("A") && not_copy("B"));
        assert!(!not_copy("P"));
        assert!(not_copy("R"));
    }

    #[test]
    fn place_fields_and_cycles_of_the_definitions() {
        let src = "struct Frame: !Move { buf: [u8; 4], cur: &u8 in self.buf[] }\n\
                   struct Wrap<T> { x: T }\n\
                   struct Node: !Move { f: Frame, next: Option<Box<Node>> }\n\
                   struct A { b: Option<Box<B>> }\n\
                   struct B { a: Option<Box<A>> }\n\
                   struct ByRef { f: &Frame }\n";
        let Ok(a) = analyze_source(src, Options::default()) else {
            unreachable!("the source parses")
        };
        let p = a.program.props();
        let ty = |n: &str, args: Vec<Ty>| Ty::Adt(adt(&a.program, n), args);
        let frame = ty("Frame", Vec::new());
        assert!(p.may_hold_place_field(&frame));
        assert!(p.may_hold_place_field(&ty("Node", Vec::new())));
        assert!(p.may_hold_place_field(&ty("Wrap", vec![frame.clone()])));
        assert!(p.may_hold_place_field(&ty("Box", vec![frame])));
        assert!(!p.may_hold_place_field(&ty("Wrap", vec![Ty::Bool])));
        assert!(!p.may_hold_place_field(&ty("A", Vec::new())));
        assert!(!p.may_hold_place_field(&ty("ByRef", Vec::new())));
        let cycle = |n: &str| p.cycle(adt(&a.program, n));
        assert!(cycle("Node").is_some());
        assert!(cycle("A").is_some() && cycle("A") == cycle("B"));
        assert_ne!(cycle("A"), cycle("Node"));
        assert!(cycle("Wrap").is_none() && cycle("Option").is_none());
    }

    #[test]
    fn a_wide_recursive_type_is_fast() {
        // The work of the fixpoint does not grow with the number of fields
        // of a recursive type: each definition is evaluated again only when a
        // definition that it names changes.
        let evals = |width: usize| {
            let fields: Vec<String> = (0..width).map(|i| format!("f{i}: A")).collect();
            let src = format!(
                "linear struct Tok {{ id: u64 }}\nstruct A {{ {}, t: Tok }}\nfn f(x: A) {{ let y = x }}\n",
                fields.join(", ")
            );
            let Ok(a) = analyze_source(&src, Options::default()) else {
                unreachable!("the source parses")
            };
            let p = a.program.props();
            assert!(p
                .get(adt(&a.program, "A"), Prop::Linear)
                .is_some_and(|h| h.always));
            let n = a.program.adts.len();
            let (_, evals) = fixpoint(&a.program, &adt_cycles(&a.program));
            assert!(evals <= 3 * n, "{evals} evaluations for {n} definitions");
            evals
        };
        assert_eq!(evals(64), evals(2));
    }
}
