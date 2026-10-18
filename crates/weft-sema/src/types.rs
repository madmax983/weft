//! Types and unification.

use std::fmt;
use std::rc::Rc;

/// An integer type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IntTy {
    /// `i8`
    I8,
    /// `i16`
    I16,
    /// `i32`
    I32,
    /// `i64`
    I64,
    /// `u8`
    U8,
    /// `u16`
    U16,
    /// `u32`
    U32,
    /// `u64`
    U64,
    /// `usize`
    Usize,
}

impl IntTy {
    /// Parses an integer type name.
    pub fn from_name(s: &str) -> Option<Self> {
        Some(match s {
            "i8" => Self::I8,
            "i16" => Self::I16,
            "i32" => Self::I32,
            "i64" => Self::I64,
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "usize" => Self::Usize,
            _ => return None,
        })
    }

    /// Returns the type name.
    pub const fn name(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::Usize => "usize",
        }
    }
}

/// An index into the program's type definitions.
pub type AdtId = usize;

/// A function type: the type of a closure, a function item or a function parameter.
#[derive(Clone, Debug, PartialEq)]
pub struct FnTy {
    /// Parameter types.
    pub params: Vec<Ty>,
    /// The return type.
    pub ret: Ty,
    /// A declared effect row (canonical names). `None` passes the caller's effects through.
    pub effects: Option<Vec<String>>,
    /// The closure summary, for closures made in the current function.
    pub summary: Option<usize>,
    /// The function item, for a named function used as a value.
    pub item: Option<usize>,
}

/// A type.
#[derive(Clone, Debug, PartialEq, Default)]
pub enum Ty {
    /// An integer.
    Int(IntTy),
    /// `bool`.
    Bool,
    /// `()`.
    #[default]
    Unit,
    /// The type of an expression that does not return.
    Never,
    /// A tuple.
    Tuple(Vec<Self>),
    /// A struct, enum or extern type with type arguments.
    Adt(AdtId, Vec<Self>),
    /// A reference. The place is tracked by the facts, not by the type.
    Ref(Box<Self>),
    /// A slice `[T]`, only behind a reference.
    Slice(Box<Self>),
    /// A fixed array.
    Array(Box<Self>, u64),
    /// A function value.
    Fn(Rc<FnTy>),
    /// An inference variable.
    Var(u32),
    /// An inference variable that must become an integer.
    IntVar(u32),
    /// A type parameter of the current signature.
    Param(u32),
    /// The capability of a `scope`.
    Scope,
    /// A continuation: `resume` takes the first type and returns the second.
    Cont(Box<Self>, Box<Self>),
    /// The type after an error. It unifies with everything.
    Error,
}

impl Ty {
    /// Returns true for a reference type.
    pub const fn is_ref(&self) -> bool {
        matches!(self, Self::Ref(_))
    }
}

/// The inference table.
#[derive(Clone, Debug, Default)]
pub struct Infer {
    vars: Vec<Option<Ty>>,
}

impl Infer {
    /// Makes a new type variable.
    pub fn fresh(&mut self) -> Ty {
        self.vars.push(None);
        Ty::Var(u32::try_from(self.vars.len() - 1).unwrap_or(u32::MAX))
    }

    /// Makes a new integer variable.
    pub fn fresh_int(&mut self) -> Ty {
        self.vars.push(None);
        Ty::IntVar(u32::try_from(self.vars.len() - 1).unwrap_or(u32::MAX))
    }

    /// Replaces bound variables, one level deep.
    pub fn shallow(&self, t: &Ty) -> Ty {
        let mut t = t.clone();
        loop {
            match t {
                Ty::Var(v) | Ty::IntVar(v) => match &self.vars[v as usize] {
                    Some(b) => t = b.clone(),
                    None => return t,
                },
                _ => return t,
            }
        }
    }

    /// Replaces all bound variables. Unbound integer variables become `i64`.
    pub fn resolve(&self, t: &Ty) -> Ty {
        match self.shallow(t) {
            Ty::IntVar(_) => Ty::Int(IntTy::I64),
            Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| self.resolve(t)).collect()),
            Ty::Adt(id, ts) => Ty::Adt(id, ts.iter().map(|t| self.resolve(t)).collect()),
            Ty::Ref(t) => Ty::Ref(Box::new(self.resolve(&t))),
            Ty::Slice(t) => Ty::Slice(Box::new(self.resolve(&t))),
            Ty::Array(t, n) => Ty::Array(Box::new(self.resolve(&t)), n),
            Ty::Cont(a, b) => Ty::Cont(Box::new(self.resolve(&a)), Box::new(self.resolve(&b))),
            Ty::Fn(f) => Ty::Fn(Rc::new(FnTy {
                params: f.params.iter().map(|t| self.resolve(t)).collect(),
                ret: self.resolve(&f.ret),
                effects: f.effects.clone(),
                summary: f.summary,
                item: f.item,
            })),
            t => t,
        }
    }

    fn occurs(&self, v: u32, t: &Ty) -> bool {
        match self.shallow(t) {
            Ty::Var(w) | Ty::IntVar(w) => v == w,
            Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().any(|t| self.occurs(v, t)),
            Ty::Ref(t) | Ty::Slice(t) | Ty::Array(t, _) => self.occurs(v, &t),
            Ty::Cont(a, b) => self.occurs(v, &a) || self.occurs(v, &b),
            Ty::Fn(f) => f.params.iter().any(|t| self.occurs(v, t)) || self.occurs(v, &f.ret),
            _ => false,
        }
    }

    /// Makes two types equal. Returns false if they cannot be equal.
    pub fn unify(&mut self, a: &Ty, b: &Ty) -> bool {
        let a = self.shallow(a);
        let b = self.shallow(b);
        if let (Ty::Var(x), Ty::Var(y)) | (Ty::IntVar(x), Ty::IntVar(y)) = (&a, &b) {
            if x == y {
                return true;
            }
        }
        match (&a, &b) {
            (Ty::Error | Ty::Never, _)
            | (_, Ty::Error | Ty::Never)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Unit, Ty::Unit)
            | (Ty::Scope, Ty::Scope) => true,
            (Ty::Var(x), _) | (Ty::IntVar(x), Ty::Int(_) | Ty::IntVar(_)) => self.bind(*x, &b),
            (_, Ty::Var(y)) | (Ty::Int(_), Ty::IntVar(y)) => self.bind(*y, &a),
            (Ty::Int(x), Ty::Int(y)) => x == y,
            (Ty::Tuple(xs), Ty::Tuple(ys)) if xs.len() == ys.len() => {
                xs.iter().zip(ys).all(|(x, y)| self.unify(x, y))
            }
            (Ty::Adt(i, xs), Ty::Adt(j, ys)) if i == j && xs.len() == ys.len() => {
                xs.iter().zip(ys).all(|(x, y)| self.unify(x, y))
            }
            (Ty::Ref(x), Ty::Ref(y)) | (Ty::Slice(x), Ty::Slice(y)) => self.unify(x, y),
            (Ty::Array(x, n), Ty::Array(y, m)) => n == m && self.unify(x, y),
            (Ty::Cont(a1, b1), Ty::Cont(a2, b2)) => self.unify(a1, a2) && self.unify(b1, b2),
            (Ty::Fn(f), Ty::Fn(g)) if f.params.len() == g.params.len() => {
                f.params
                    .iter()
                    .zip(&g.params)
                    .all(|(x, y)| self.unify(x, y))
                    && self.unify(&f.ret, &g.ret)
            }
            (Ty::Param(x), Ty::Param(y)) => x == y,
            _ => false,
        }
    }

    fn bind(&mut self, v: u32, t: &Ty) -> bool {
        if self.occurs(v, t) {
            return false;
        }
        self.vars[v as usize] = Some(t.clone());
        true
    }
}

/// Replaces type parameters with the given types.
pub fn subst(t: &Ty, args: &[Ty]) -> Ty {
    match t {
        Ty::Param(i) => args.get(*i as usize).cloned().unwrap_or(Ty::Error),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| subst(t, args)).collect()),
        Ty::Adt(id, ts) => Ty::Adt(*id, ts.iter().map(|t| subst(t, args)).collect()),
        Ty::Ref(t) => Ty::Ref(Box::new(subst(t, args))),
        Ty::Slice(t) => Ty::Slice(Box::new(subst(t, args))),
        Ty::Array(t, n) => Ty::Array(Box::new(subst(t, args)), *n),
        Ty::Cont(a, b) => Ty::Cont(Box::new(subst(a, args)), Box::new(subst(b, args))),
        Ty::Fn(f) => Ty::Fn(Rc::new(FnTy {
            params: f.params.iter().map(|t| subst(t, args)).collect(),
            ret: subst(&f.ret, args),
            effects: f.effects.clone(),
            summary: f.summary,
            item: f.item,
        })),
        t => t.clone(),
    }
}

/// Shows a type with the names of its definitions.
pub struct Display<'a> {
    /// The type.
    pub ty: &'a Ty,
    /// The definition names, by index.
    pub names: &'a [String],
}

impl fmt::Display for Display<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names = self.names;
        let d = |t: &'_ Ty| -> String { Display { ty: t, names }.to_string() };
        match self.ty {
            Ty::Int(i) => f.write_str(i.name()),
            Ty::Bool => f.write_str("bool"),
            Ty::Unit => f.write_str("()"),
            Ty::Never => f.write_str("!"),
            Ty::Tuple(ts) => {
                f.write_str("(")?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", d(t))?;
                }
                f.write_str(")")
            }
            Ty::Adt(id, ts) => {
                f.write_str(self.names.get(*id).map_or("?", String::as_str))?;
                if !ts.is_empty() {
                    f.write_str("<")?;
                    for (i, t) in ts.iter().enumerate() {
                        if i > 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{}", d(t))?;
                    }
                    f.write_str(">")?;
                }
                Ok(())
            }
            Ty::Ref(t) => write!(f, "&{}", d(t)),
            Ty::Slice(t) => write!(f, "[{}]", d(t)),
            Ty::Array(t, n) => write!(f, "[{}; {n}]", d(t)),
            Ty::Fn(func) => {
                f.write_str("fn(")?;
                for (i, t) in func.params.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", d(t))?;
                }
                write!(f, ") -> {}", d(&func.ret))
            }
            Ty::Var(_) => f.write_str("_"),
            Ty::IntVar(_) => f.write_str("{integer}"),
            Ty::Param(i) => write!(f, "T{i}"),
            Ty::Scope => f.write_str("Scope"),
            Ty::Cont(a, b) => write!(f, "resume({}) -> {}", d(a), d(b)),
            Ty::Error => f.write_str("{error}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unify_binds_and_resolves() {
        let mut inf = Infer::default();
        let a = inf.fresh();
        let i = inf.fresh_int();
        assert!(inf.unify(&a, &Ty::Adt(0, vec![i.clone()])));
        assert!(inf.unify(&i, &Ty::Int(IntTy::U32)));
        assert_eq!(inf.resolve(&a), Ty::Adt(0, vec![Ty::Int(IntTy::U32)]));
        assert!(!inf.unify(&Ty::Bool, &Ty::Unit));
        let b = inf.fresh();
        assert!(!inf.unify(&b, &Ty::Ref(Box::new(b.clone()))));
        let j = inf.fresh_int();
        assert!(!inf.unify(&j, &Ty::Bool));
        assert_eq!(inf.resolve(&j), Ty::Int(IntTy::I64));
    }

    #[test]
    fn subst_and_display() {
        let names = vec!["Vec".to_string()];
        let t = subst(&Ty::Adt(0, vec![Ty::Param(0)]), &[Ty::Int(IntTy::U8)]);
        assert_eq!(
            Display {
                ty: &Ty::Ref(Box::new(t)),
                names: &names
            }
            .to_string(),
            "&Vec<u8>"
        );
        let tup = Ty::Tuple(vec![Ty::Bool, Ty::Unit]);
        assert_eq!(
            Display {
                ty: &tup,
                names: &names
            }
            .to_string(),
            "(bool, ())"
        );
        assert_eq!(IntTy::from_name("usize"), Some(IntTy::Usize));
        assert_eq!(IntTy::from_name("x"), None);
    }
}
