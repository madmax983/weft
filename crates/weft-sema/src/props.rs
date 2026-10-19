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
use crate::types::Ty;

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
}

/// The properties, in table order.
pub const PROPS: [Prop; 7] = [
    Prop::Linear,
    Prop::Nonportable,
    Prop::Immovable,
    Prop::Refs,
    Prop::Fns,
    Prop::NotCopy,
    Prop::NoOnAbort,
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
    table: Vec<[Holds; 7]>,
}

impl TypeProps {
    /// Computes the table for every definition of `prog`.
    pub fn new(prog: &Program) -> Self {
        let n = prog.adts.len();
        let mut table: Vec<[Holds; 7]> = vec![Default::default(); n];
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
        let recursive = recursive_adts(prog);
        for (a, &r) in recursive.iter().enumerate() {
            table[a][Prop::NotCopy.index()].always = r;
        }
        let mut work: Vec<usize> = (0..n).rev().collect();
        let mut queued = vec![true; n];
        while let Some(a) = work.pop() {
            queued[a] = false;
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
        Self { table }
    }

    /// Returns when property `p` holds for the instances of definition `a`.
    pub fn get(&self, a: usize, p: Prop) -> Option<&Holds> {
        self.table.get(a).map(|h| &h[p.index()])
    }
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
            f(*a);
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
            f(*a);
            for x in args {
                each_inline_adt(x, f);
            }
        }
        Ty::Tuple(ts) => ts.iter().for_each(|x| each_inline_adt(x, f)),
        Ty::Array(x, _) => each_inline_adt(x, f),
        _ => {}
    }
}

/// Returns, for each definition, true if a value of it can hold a value of the
/// same definition. The definition is then on a cycle of the graph of inline parts.
/// The search is Tarjan's algorithm, with an explicit stack.
fn recursive_adts(prog: &Program) -> Vec<bool> {
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
    let mut recursive = vec![false; n];
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
                    recursive[a] = true;
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
                if members.len() > 1 {
                    for b in members {
                        recursive[b] = true;
                    }
                }
            }
        }
    }
    recursive
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
fn eval_adt(prog: &Program, a: usize, table: &[[Holds; 7]]) -> [Holds; 7] {
    let def = &prog.adts[a];
    let parts = parts(prog, a);
    let ext = match &def.kind {
        AdtKind::Extern {
            elem_unstable,
            deref,
        } => Some((*elem_unstable, *deref)),
        _ => None,
    };
    let mut out: [Holds; 7] = Default::default();
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
            Prop::Refs | Prop::Fns => false,
        };
        // A type with `on abort` finishes its linear parts.
        if !passes || (p == Prop::NoOnAbort && def.has_on_abort) {
            continue;
        }
        for t in &parts {
            h.join(&eval(t, p, table));
        }
    }
    out
}

/// Returns when property `p` holds for type term `t` of a definition, from the rows in `table`.
fn eval(t: &Ty, p: Prop, table: &[[Holds; 7]]) -> Holds {
    let always = |b: bool| Holds {
        always: b,
        params: Vec::new(),
    };
    match t {
        Ty::Param(i) => Holds {
            always: false,
            params: vec![*i as usize],
        },
        Ty::Adt(b, args) => {
            let Some(row) = table.get(*b) else {
                return Holds::default();
            };
            let h = &row[p.index()];
            let mut out = always(h.always);
            for &j in &h.params {
                if let Some(x) = args.get(j) {
                    out.join(&eval(x, p, table));
                }
            }
            out
        }
        Ty::Tuple(ts) => {
            let mut out = Holds::default();
            for x in ts {
                out.join(&eval(x, p, table));
            }
            out
        }
        Ty::Array(..) if p == Prop::NotCopy => always(true),
        Ty::Array(x, _) => eval(x, p, table),
        Ty::Ref(x) => match p {
            Prop::Refs => always(true),
            Prop::Fns => eval(x, p, table),
            _ => Holds::default(),
        },
        Ty::Slice(x) => match p {
            Prop::Refs | Prop::NotCopy => always(true),
            Prop::Fns => eval(x, p, table),
            _ => Holds::default(),
        },
        Ty::Fn(_) => always(p == Prop::Fns),
        Ty::Cont(..) => always(p == Prop::NotCopy),
        Ty::Scope => always(p == Prop::Nonportable),
        _ => Holds::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{analyze_source, Options};

    fn adt(prog: &Program, name: &str) -> usize {
        prog.adts
            .iter()
            .position(|a| a.name == name)
            .unwrap_or(usize::MAX)
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
                   struct Loop { next: Option<Box<Loop>>, t: Tok }\n";
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
        assert!(get("Vec", Prop::NotCopy).always);
        assert_eq!(get("Vec", Prop::Immovable).params, vec![0]);
        assert!(get("Box", Prop::Immovable).params.is_empty());
        assert!(get("Weak", Prop::Immovable).params.is_empty());
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
    fn a_wide_recursive_type_is_fast() {
        let fields: Vec<String> = (0..64).map(|i| format!("f{i}: A")).collect();
        let src = format!(
            "linear struct Tok {{ id: u64 }}\nstruct A {{ {}, t: Tok }}\nfn f(x: A) {{ let y = x }}\n",
            fields.join(", ")
        );
        let start = std::time::Instant::now();
        let Ok(a) = analyze_source(&src, Options::default()) else {
            unreachable!("the source parses")
        };
        let p = a.program.props();
        assert!(p
            .get(adt(&a.program, "A"), Prop::Linear)
            .is_some_and(|h| h.always));
        assert!(start.elapsed().as_secs() < 10);
    }
}
