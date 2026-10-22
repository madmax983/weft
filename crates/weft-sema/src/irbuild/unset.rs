//! The place fields of a full type (`docs/ir.md` 5.2, 5.17; ADR 0007).
//!
//! A place field is a reference field of a `!Move` struct with an `in` place.
//! A value that no place held before is built in place: a literal, a call
//! result and a by-value parameter. Its place fields have no value. The
//! builder writes `Uninit` for the path of each one, so the facts see that
//! the field has no value (W0304).
//!
//! The walk follows each part of a full type (a definition with its type
//! arguments): the fields of a struct, the parts of a tuple, the payloads of
//! the variants of an enum, and the target of an extern pointer that is not
//! an `Rc` (`Deref(Box)`). It does not follow a reference, an array or the
//! elements of a buffer.
//!
//! A recursive type holds a place field at each depth, so the paths have no
//! end. The walk stops at a struct or an enum whose cycle of definitions is
//! already on the way, and gives a path that stands for each place field at
//! or below it ([`FieldPath::below`]). Each infinite walk meets such a type,
//! so the walk ends, also for a type that grows at each depth
//! (`Nest<T> { next: Option<Box<Nest<Box<T>>>> }`). A generic type that does
//! not hold itself does not stop the walk: `Wrap<Wrap<Frame>>` gives both
//! levels.
//!
//! The result depends only on the full type and the cycles on the way, so a
//! table keeps it: the key is the full type with the set of the cycles that
//! the walk visited. A type that cannot hold a place field is not walked.

use std::collections::HashMap;
use std::rc::Rc;

use weft_ir::ty::{AdtKind, ExternDeref, FnTy};
use weft_ir::{AdtId, DerefKind, FieldIdx, Proj, Ty, TyId, TyTable, VariantIdx};

/// The number of paths above which a type gets one path for each part that
/// holds place fields.
const LIMIT: usize = 64;

/// The path of a place field below a value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldPath {
    /// The projections from the value to the field.
    pub proj: Vec<Proj>,
    /// The path stops above the place fields: it stands for each place field
    /// at or below it (a recursive type, or a type with very many paths).
    pub below: bool,
}

/// When the instances of a definition can hold a place field.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Hold {
    /// Each instance can.
    always: bool,
    /// An instance can if one of these type arguments can.
    params: Vec<u32>,
}

/// The place fields of the full types of one program.
#[derive(Debug, Default)]
pub struct PlaceFields {
    /// A definition has a place field.
    any: bool,
    /// The cycle of each definition (`None`: the definition is not in a
    /// cycle), by [`AdtId`].
    cycle: Vec<Option<u32>>,
    /// When each definition can hold a place field, by [`AdtId`].
    hold: Vec<Hold>,
    /// The paths of each full type, for each set of cycles on the way.
    paths: HashMap<(TyId, Vec<u32>), Rc<[FieldPath]>>,
    /// The types that can hold a place field.
    may: HashMap<TyId, bool>,
}

/// Returns `t` with the type parameters replaced by `args`.
pub fn subst(tys: &mut TyTable, t: TyId, args: &[TyId]) -> TyId {
    if args.is_empty() || !tys.mentions_param(t) {
        return t;
    }
    let Some(ty) = tys.try_get(t).cloned() else {
        return t;
    };
    let list = |tys: &mut TyTable, xs: &[TyId]| -> Vec<TyId> {
        xs.iter().map(|&x| subst(tys, x, args)).collect()
    };
    let new = match ty {
        Ty::Param(i) => return args.get(i as usize).copied().unwrap_or(t),
        Ty::Tuple(ts) => Ty::Tuple(list(tys, &ts)),
        Ty::Array(x, n) => Ty::Array(subst(tys, x, args), n),
        Ty::Slice(x) => Ty::Slice(subst(tys, x, args)),
        Ty::Ref(x) => Ty::Ref(subst(tys, x, args)),
        Ty::Iter(x) => Ty::Iter(subst(tys, x, args)),
        Ty::Adt(a, xs) => Ty::Adt(a, list(tys, &xs)),
        Ty::Cont(a, b) => Ty::Cont(subst(tys, a, args), subst(tys, b, args)),
        Ty::Fn(f) => Ty::Fn(FnTy {
            params: list(tys, &f.params),
            ret: subst(tys, f.ret, args),
            row: f.row,
        }),
        Ty::Unit | Ty::Bool | Ty::Never | Ty::Int(_) | Ty::Scope | Ty::Cap(_) => return t,
    };
    tys.intern(new)
}

/// A part of a definition that the walk follows.
#[derive(Clone, Copy, Debug)]
enum Part {
    /// A place field: a path of its own.
    Place,
    /// A part of this declared type.
    Ty(TyId),
    /// The target of a pointer: the first type argument.
    Target,
}

/// Returns the parts that the walk follows in definition `a`, with the step
/// to each one.
fn parts(tys: &TyTable, a: AdtId) -> Vec<(Vec<Proj>, Part)> {
    let Some(d) = tys.adts().get(a.index()) else {
        return Vec::new();
    };
    match &d.kind {
        AdtKind::Struct(fs) => fs
            .iter()
            .enumerate()
            .map(|(i, f)| {
                let step = vec![Proj::Field(FieldIdx(super::id_of(i)))];
                (step, if f.place { Part::Place } else { Part::Ty(f.ty) })
            })
            .collect(),
        AdtKind::Enum(vs) => vs
            .iter()
            .enumerate()
            .flat_map(|(v, vd)| {
                vd.fields.iter().enumerate().map(move |(k, &t)| {
                    let step = vec![
                        Proj::Variant(VariantIdx(super::id_of(v))),
                        Proj::Field(FieldIdx(super::id_of(k))),
                    ];
                    (step, Part::Ty(t))
                })
            })
            .collect(),
        AdtKind::Extern {
            deref: Some(ExternDeref::Stable | ExternDeref::Unstable),
            ..
        } if d.generics > 0 => vec![(vec![Proj::Deref(DerefKind::Box)], Part::Target)],
        AdtKind::Extern { .. } => Vec::new(),
    }
}

/// Adds each definition that type `t` names (not through a reference or a
/// function type) to `out`.
fn named(tys: &TyTable, t: TyId, out: &mut Vec<AdtId>) {
    let Some(ty) = tys.try_get(t) else { return };
    match ty {
        Ty::Adt(a, args) => {
            out.push(*a);
            for &x in args {
                named(tys, x, out);
            }
        }
        Ty::Tuple(ts) => {
            for &x in ts {
                named(tys, x, out);
            }
        }
        Ty::Array(x, _) | Ty::Slice(x) | Ty::Iter(x) => named(tys, *x, out),
        _ => {}
    }
}

impl PlaceFields {
    /// Prepares the walk over the definitions of `tys`: the cycles of the
    /// definitions and when each one can hold a place field.
    pub fn new(tys: &TyTable) -> Self {
        let n = tys.adts().len();
        let any = tys
            .adts()
            .iter()
            .any(|d| matches!(&d.kind, AdtKind::Struct(fs) if fs.iter().any(|f| f.place)));
        let mut me = Self {
            any,
            cycle: vec![None; n],
            hold: vec![Hold::default(); n],
            paths: HashMap::new(),
            may: HashMap::new(),
        };
        if !any {
            return me;
        }
        // The edges of the graph of the definitions: each definition that a
        // part of a definition names.
        let edges: Vec<Vec<usize>> = (0..n)
            .map(|a| {
                let mut out = Vec::new();
                for (_, part) in parts(tys, AdtId(super::id_of(a))) {
                    if let Part::Ty(t) = part {
                        named(tys, t, &mut out);
                    }
                }
                let mut v: Vec<usize> = out.iter().map(|x| x.index()).collect();
                v.sort_unstable();
                v.dedup();
                v
            })
            .collect();
        me.cycle = cycles(&edges);
        me.hold = holds(tys, n);
        me
    }

    /// Returns true if a value of type `t` can hold a place field.
    fn may_hold(&mut self, tys: &TyTable, t: TyId) -> bool {
        if !self.any {
            return false;
        }
        if let Some(&m) = self.may.get(&t) {
            return m;
        }
        let m = match tys.try_get(t) {
            Some(Ty::Tuple(ts)) => {
                let ts = ts.clone();
                ts.iter().any(|&x| self.may_hold(tys, x))
            }
            Some(Ty::Adt(a, args)) => {
                let args = args.clone();
                let h = self.hold.get(a.index()).cloned().unwrap_or_default();
                h.always
                    || h.params
                        .iter()
                        .any(|&j| args.get(j as usize).is_some_and(|&x| self.may_hold(tys, x)))
            }
            _ => false,
        };
        self.may.insert(t, m);
        m
    }

    /// Returns the paths of the place fields that a value of the full type `t`
    /// holds.
    pub fn of(&mut self, tys: &mut TyTable, t: TyId) -> Rc<[FieldPath]> {
        self.walk(tys, t, &[])
    }

    /// Returns the paths of the place fields of type `t`. `cycles` are the
    /// cycles of the definitions on the way to `t`, in order.
    fn walk(&mut self, tys: &mut TyTable, t: TyId, cycles: &[u32]) -> Rc<[FieldPath]> {
        if !self.may_hold(tys, t) {
            return Rc::from([]);
        }
        let key = (t, cycles.to_vec());
        if let Some(ps) = self.paths.get(&key) {
            return Rc::clone(ps);
        }
        let mut out: Vec<FieldPath> = Vec::new();
        let mut steps: Vec<(Vec<Proj>, TyId)> = Vec::new();
        let mut inner = cycles.to_vec();
        match tys.try_get(t).cloned() {
            Some(Ty::Tuple(ts)) => {
                for (i, x) in ts.into_iter().enumerate() {
                    steps.push((vec![Proj::Field(FieldIdx(super::id_of(i)))], x));
                }
            }
            Some(Ty::Adt(a, args)) => {
                for (step, part) in parts(tys, a) {
                    match part {
                        Part::Place => out.push(FieldPath {
                            proj: step,
                            below: false,
                        }),
                        Part::Ty(p) => steps.push((step, subst(tys, p, &args))),
                        Part::Target => steps.extend(args.first().map(|&x| (step, x))),
                    }
                }
                if let Some(c) = self.cycle.get(a.index()).copied().flatten() {
                    if let Err(i) = inner.binary_search(&c) {
                        inner.insert(i, c);
                    }
                }
            }
            _ => {}
        }
        let mut found: Vec<(Vec<Proj>, Rc<[FieldPath]>)> = Vec::new();
        for (step, x) in steps {
            // A struct or an enum of a cycle on the way: each place field
            // below it is a place field with no value.
            let again = match tys.try_get(x) {
                Some(Ty::Adt(b, _)) => {
                    let ext = matches!(
                        tys.adts().get(b.index()).map(|d| &d.kind),
                        Some(AdtKind::Extern { .. })
                    );
                    !ext && self
                        .cycle
                        .get(b.index())
                        .copied()
                        .flatten()
                        .is_some_and(|c| inner.binary_search(&c).is_ok())
                }
                _ => false,
            };
            if again {
                if self.may_hold(tys, x) {
                    found.push((
                        step,
                        Rc::from([FieldPath {
                            proj: Vec::new(),
                            below: true,
                        }]),
                    ));
                }
                continue;
            }
            let ps = self.walk(tys, x, &inner);
            if !ps.is_empty() {
                found.push((step, ps));
            }
        }
        let many = out.len() + found.iter().map(|(_, ps)| ps.len()).sum::<usize>() > LIMIT;
        for (step, ps) in found {
            if many {
                out.push(FieldPath {
                    proj: step,
                    below: true,
                });
                continue;
            }
            for p in ps.iter() {
                let mut proj = step.clone();
                proj.extend(p.proj.iter().cloned());
                out.push(FieldPath {
                    proj,
                    below: p.below,
                });
            }
        }
        let ps: Rc<[FieldPath]> = out.into();
        self.paths.insert(key, Rc::clone(&ps));
        ps
    }
}

/// Returns the cycle of each node of the graph `edges`: the index of its
/// strongly connected component if the component has a cycle (more than one
/// node, or an edge to itself), else `None`.
fn cycles(edges: &[Vec<usize>]) -> Vec<Option<u32>> {
    // Tarjan's algorithm with an explicit stack: the graph can be deep.
    let n = edges.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0; n];
    let mut on = vec![false; n];
    let mut stack = Vec::new();
    let mut comp = vec![usize::MAX; n];
    let mut ncomp = 0;
    let mut next = 0;
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        index[root] = next;
        low[root] = next;
        next += 1;
        stack.push(root);
        on[root] = true;
        while let Some(&mut (v, ref mut k)) = work.last_mut() {
            if let Some(&w) = edges[v].get(*k) {
                *k += 1;
                if w >= n {
                    continue;
                }
                if index[w] == usize::MAX {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    stack.push(w);
                    on[w] = true;
                    work.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            work.pop();
            if let Some(&(u, _)) = work.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                while let Some(w) = stack.pop() {
                    on[w] = false;
                    comp[w] = ncomp;
                    if w == v {
                        break;
                    }
                }
                ncomp += 1;
            }
        }
    }
    let mut size = vec![0usize; ncomp];
    for &c in &comp {
        if let Some(s) = size.get_mut(c) {
            *s += 1;
        }
    }
    (0..n)
        .map(|v| {
            let c = comp[v];
            let cyclic = size.get(c).copied().unwrap_or(0) > 1 || edges[v].contains(&v);
            cyclic.then(|| super::id_of(c))
        })
        .collect()
}

/// Returns when each of the `n` definitions of `tys` can hold a place field:
/// the least fixpoint over the definitions.
fn holds(tys: &TyTable, n: usize) -> Vec<Hold> {
    let mut rows = vec![Hold::default(); n];
    let parts: Vec<Vec<(Vec<Proj>, Part)>> =
        (0..n).map(|a| parts(tys, AdtId(super::id_of(a)))).collect();
    let mut changed = true;
    while changed {
        changed = false;
        for a in 0..n {
            let mut h = Hold::default();
            for (_, part) in &parts[a] {
                match part {
                    Part::Place => h.always = true,
                    Part::Ty(t) => decl_hold(tys, &rows, *t, &mut h),
                    Part::Target => h.params.push(0),
                }
            }
            h.params.sort_unstable();
            h.params.dedup();
            if h != rows[a] {
                rows[a] = h;
                changed = true;
            }
        }
    }
    rows
}

/// Adds to `h` when the declared type `t` can hold a place field, with the
/// rows `rows` of the definitions.
fn decl_hold(tys: &TyTable, rows: &[Hold], t: TyId, h: &mut Hold) {
    match tys.try_get(t) {
        Some(Ty::Param(j)) => h.params.push(*j),
        Some(Ty::Tuple(ts)) => {
            for &x in ts {
                decl_hold(tys, rows, x, h);
            }
        }
        Some(Ty::Adt(b, args)) => {
            let Some(r) = rows.get(b.index()) else { return };
            h.always |= r.always;
            for &j in &r.params {
                if let Some(&x) = args.get(j as usize) {
                    decl_hold(tys, rows, x, h);
                }
            }
        }
        _ => {}
    }
}
