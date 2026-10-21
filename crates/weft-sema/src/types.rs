//! Types and unification.

use std::cell::{Cell, RefCell};
use std::fmt;
use std::sync::Arc;

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

    /// Returns the smallest and the largest value of the type.
    pub const fn range(self) -> (i128, i128) {
        match self {
            Self::I8 => (i8::MIN as i128, i8::MAX as i128),
            Self::I16 => (i16::MIN as i128, i16::MAX as i128),
            Self::I32 => (i32::MIN as i128, i32::MAX as i128),
            Self::I64 => (i64::MIN as i128, i64::MAX as i128),
            Self::U8 => (0, u8::MAX as i128),
            Self::U16 => (0, u16::MAX as i128),
            Self::U32 => (0, u32::MAX as i128),
            Self::U64 | Self::Usize => (0, u64::MAX as i128),
        }
    }
}

pub use crate::ids::AdtId;

/// A function type: the type of a closure, a function item or a function parameter.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    pub item: Option<crate::ids::FnId>,
}

/// A type.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
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
    Fn(Arc<FnTy>),
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
///
/// The variables form a union-find structure. A variable that is bound to
/// another variable is a link. A lookup follows the links to the last
/// variable, and then points each variable on the way to it (path
/// compression). A union of two unbound variables of the same kind binds the
/// one of lower rank, or the newer one, to the other (union by rank). So the
/// links stay short, also when each `s += 1` makes a new integer variable.
#[derive(Clone, Debug, Default)]
pub struct Infer {
    /// The binding of each variable. A lookup can shorten the links, so this
    /// is a `RefCell`: the meaning of the table does not change.
    vars: RefCell<Vec<Option<Ty>>>,
    /// The rank of each variable: a bound on the length of the links to it.
    rank: Vec<u32>,
    /// The links that the lookups followed, for a test of the work.
    steps: Cell<usize>,
}

impl Infer {
    /// Makes a new type variable.
    pub fn fresh(&mut self) -> Ty {
        Ty::Var(self.push())
    }

    /// Makes a new integer variable.
    pub fn fresh_int(&mut self) -> Ty {
        Ty::IntVar(self.push())
    }

    fn push(&mut self) -> u32 {
        let vars = self.vars.get_mut();
        vars.push(None);
        self.rank.push(0);
        u32::try_from(vars.len() - 1).unwrap_or(u32::MAX)
    }

    /// The links between variables that the lookups followed so far.
    pub fn steps(&self) -> usize {
        self.steps.get()
    }

    /// Follows the links from the variable `t` to the last variable, and
    /// returns that variable as a type (`Ty::Var` or `Ty::IntVar`). Each
    /// variable on the way then links to it directly.
    fn find(&self, t: &Ty) -> Ty {
        let mut vars = self.vars.borrow_mut();
        let mut last = t.clone();
        while let Ty::Var(v) | Ty::IntVar(v) = last {
            match &vars[v as usize] {
                Some(b @ (Ty::Var(_) | Ty::IntVar(_))) => {
                    self.steps.set(self.steps.get() + 1);
                    last = b.clone();
                }
                _ => break,
            }
        }
        let mut at = t.clone();
        while let Ty::Var(v) | Ty::IntVar(v) = at {
            if at == last {
                break;
            }
            let next = vars[v as usize].replace(last.clone());
            match next {
                Some(n) => at = n,
                None => break,
            }
        }
        last
    }

    /// Replaces bound variables, one level deep.
    pub fn shallow(&self, t: &Ty) -> Ty {
        match t {
            Ty::Var(_) | Ty::IntVar(_) => {
                let last = self.find(t);
                let (Ty::Var(v) | Ty::IntVar(v)) = last else {
                    return last;
                };
                self.vars.borrow()[v as usize].clone().unwrap_or(last)
            }
            _ => t.clone(),
        }
    }

    /// Replaces all bound variables. Unbound integer variables become `i64`.
    pub fn resolve(&self, t: &Ty) -> Ty {
        self.expand(t, true)
    }

    /// Replaces all bound variables. Unbound variables stay, so that a later
    /// unification can still give an integer literal its type.
    pub fn deep(&self, t: &Ty) -> Ty {
        self.expand(t, false)
    }

    fn expand(&self, t: &Ty, default_int: bool) -> Ty {
        let e = |t: &Ty| self.expand(t, default_int);
        match self.shallow(t) {
            Ty::IntVar(_) if default_int => Ty::Int(IntTy::I64),
            Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(e).collect()),
            Ty::Adt(id, ts) => Ty::Adt(id, ts.iter().map(e).collect()),
            Ty::Ref(t) => Ty::Ref(Box::new(e(&t))),
            Ty::Slice(t) => Ty::Slice(Box::new(e(&t))),
            Ty::Array(t, n) => Ty::Array(Box::new(e(&t)), n),
            Ty::Cont(a, b) => Ty::Cont(Box::new(e(&a)), Box::new(e(&b))),
            Ty::Fn(f) => Ty::Fn(Arc::new(FnTy {
                params: f.params.iter().map(e).collect(),
                ret: e(&f.ret),
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
        // An unbound variable links to a bound variable on the other side, not to
        // a copy of its type: a later change of that type reaches it too
        // (`rebind_fn`).
        let (ra, rb) = (self.bound_var(a), self.bound_var(b));
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
            // Two unbound variables of one kind: no cycle can form.
            (Ty::Var(x), Ty::Var(y)) | (Ty::IntVar(x), Ty::IntVar(y)) => {
                self.union(*x, &a, *y, &b);
                true
            }
            (Ty::Var(x), _) => self.bind_to(*x, &b, rb),
            (_, Ty::Var(y)) => self.bind_to(*y, &a, ra),
            (Ty::IntVar(x), Ty::Int(_)) => self.bind(*x, &b),
            (Ty::Int(_), Ty::IntVar(y)) => self.bind(*y, &a),
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

    /// Returns the variable that type variable `t` links to last, if it is bound
    /// to a function type, with that type.
    pub fn bound_fn(&self, t: &Ty) -> Option<(u32, Arc<FnTy>)> {
        let Ty::Var(_) = t else {
            return None;
        };
        let Ty::Var(v) = self.find(t) else {
            return None;
        };
        match self.vars.borrow()[v as usize].clone() {
            Some(Ty::Fn(f)) => Some((v, f)),
            _ => None,
        }
    }

    /// Gives variable `v`, which is bound to a function type, another function
    /// type of the same shape: one that can be more function values.
    pub fn rebind_fn(&mut self, v: u32, f: Arc<FnTy>) {
        if let Some(slot) = self.vars.get_mut().get_mut(v as usize) {
            if matches!(slot, Some(Ty::Fn(_))) {
                *slot = Some(Ty::Fn(f));
            }
        }
    }

    /// Returns the last variable of type variable `t` if it is bound to a type.
    fn bound_var(&self, t: &Ty) -> Option<u32> {
        let Ty::Var(_) = t else {
            return None;
        };
        let Ty::Var(v) = self.find(t) else {
            return None;
        };
        self.vars.borrow()[v as usize].is_some().then_some(v)
    }

    /// Binds variable `v` to type `t`. If `t` is the type of the bound variable
    /// `root`, `v` links to `root`.
    fn bind_to(&mut self, v: u32, t: &Ty, root: Option<u32>) -> bool {
        match root {
            Some(r) if r != v => {
                if self.occurs(v, t) {
                    return false;
                }
                self.vars.get_mut()[v as usize] = Some(Ty::Var(r));
                true
            }
            _ => self.bind(v, t),
        }
    }

    fn bind(&mut self, v: u32, t: &Ty) -> bool {
        // A variable to a variable makes no cycle: `unify` gives two
        // different unbound variables.
        if !matches!(t, Ty::Var(_) | Ty::IntVar(_)) && self.occurs(v, t) {
            return false;
        }
        self.vars.get_mut()[v as usize] = Some(t.clone());
        true
    }

    /// Joins the unbound variables `x` (the type `a`) and `y` (the type `b`)
    /// of one kind. The variable of lower rank links to the other. With equal
    /// ranks, the newer variable links to the older one, and the older one
    /// gets a higher rank.
    fn union(&mut self, x: u32, a: &Ty, y: u32, b: &Ty) {
        let (rx, ry) = (self.rank[x as usize], self.rank[y as usize]);
        // `x` links to `y` if its rank is lower, or if the ranks are equal and
        // `x` is newer.
        let (from, to, root) = if (rx, y) < (ry, x) {
            (x, b, y)
        } else {
            (y, a, x)
        };
        if rx == ry {
            self.rank[root as usize] += 1;
        }
        self.vars.get_mut()[from as usize] = Some(to.clone());
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
        Ty::Fn(f) => Ty::Fn(Arc::new(FnTy {
            params: f.params.iter().map(|t| subst(t, args)).collect(),
            ret: subst(&f.ret, args),
            effects: f.effects.clone(),
            summary: f.summary,
            item: f.item,
        })),
        t => t.clone(),
    }
}

/// The names of the type definitions, by [`AdtId`], for [`Display`].
pub trait AdtNames {
    /// Returns the name of definition `id`, if it has one.
    fn adt_name(&self, id: AdtId) -> Option<&str>;
}

impl AdtNames for [String] {
    fn adt_name(&self, id: AdtId) -> Option<&str> {
        self.get(id.index()).map(String::as_str)
    }
}

impl AdtNames for [crate::program::AdtDef] {
    fn adt_name(&self, id: AdtId) -> Option<&str> {
        self.get(id.index()).map(|a| a.name.as_str())
    }
}

/// Shows a type with the names of its definitions. The names come from a
/// table, such as the definitions of the program, with no copy.
pub struct Display<'a, N: AdtNames + ?Sized> {
    /// The type.
    pub ty: &'a Ty,
    /// The definition names, by index.
    pub names: &'a N,
}

impl<N: AdtNames + ?Sized> fmt::Display for Display<'_, N> {
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
                let name = self.names.adt_name(*id).unwrap_or("?");
                if let ([t], crate::program::PTR_NAME) = (ts.as_slice(), name) {
                    return write!(f, "*{}", d(t));
                }
                f.write_str(name)?;
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

// ---------------------------------------------------------------------------
// Final types of the IR
// ---------------------------------------------------------------------------

/// Why a type has no final type of the IR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrTyError {
    /// The type holds `Ty::Error`. A body with such a type gets no IR.
    ErrorType,
    /// The stated row of a function type names an effect that the program
    /// does not have.
    UnknownEffect(String),
}

/// Returns the final type of the IR for the settled type `t` (`docs/ir.md`
/// 2.3), interned in `table`.
///
/// The function zonks `t` with `inf`: a bound variable gets its type, a free
/// integer variable gets `i64`, and a free type variable gets `()`. No value of
/// a free type variable can exist at run time, so `()` is sound. A function type
/// loses its closure summary and its function item: the analysis finds the
/// function values.
///
/// # Errors
///
/// [`IrTyError::ErrorType`] if `t` holds `Ty::Error`, and
/// [`IrTyError::UnknownEffect`] if a stated row names an unknown effect.
pub fn to_ir_ty(
    prog: &crate::Program,
    inf: &Infer,
    table: &mut weft_ir::TyTable,
    t: &Ty,
) -> Result<weft_ir::TyId, IrTyError> {
    final_ty(prog, table, &inf.resolve(t))
}

/// Returns the IR integer type of `i`.
pub const fn to_ir_int(i: IntTy) -> weft_ir::IntTy {
    use weft_ir::IntTy as I;
    match i {
        IntTy::I8 => I::I8,
        IntTy::I16 => I::I16,
        IntTy::I32 => I::I32,
        IntTy::I64 => I::I64,
        IntTy::U8 => I::U8,
        IntTy::U16 => I::U16,
        IntTy::U32 => I::U32,
        IntTy::U64 => I::U64,
        IntTy::Usize => I::Usize,
    }
}

/// Converts an index of a table of the program to a `u32` id of the IR.
fn ir_index(i: usize) -> u32 {
    u32::try_from(i).unwrap_or(u32::MAX)
}

/// Returns the final type of the resolved type `t`.
fn final_ty(
    prog: &crate::Program,
    table: &mut weft_ir::TyTable,
    t: &Ty,
) -> Result<weft_ir::TyId, IrTyError> {
    use weft_ir::ty::{FnTy as IrFn, Ty as T};
    let list = |table: &mut weft_ir::TyTable, ts: &[Ty]| -> Result<Vec<_>, IrTyError> {
        ts.iter().map(|x| final_ty(prog, table, x)).collect()
    };
    let ir = match t {
        Ty::Int(i) => T::Int(to_ir_int(*i)),
        // `Infer::resolve` gives `i64` to a free integer variable.
        Ty::IntVar(_) => T::Int(weft_ir::IntTy::I64),
        Ty::Bool => T::Bool,
        Ty::Unit | Ty::Var(_) => T::Unit,
        Ty::Never => T::Never,
        Ty::Tuple(ts) => T::Tuple(list(table, ts)?),
        Ty::Adt(a, args) => T::Adt(weft_ir::AdtId(ir_index(a.index())), list(table, args)?),
        Ty::Ref(x) => T::Ref(final_ty(prog, table, x)?),
        Ty::Slice(x) => T::Slice(final_ty(prog, table, x)?),
        Ty::Array(x, n) => T::Array(final_ty(prog, table, x)?, *n),
        Ty::Fn(f) => {
            let params = list(table, &f.params)?;
            let ret = final_ty(prog, table, &f.ret)?;
            let row = match &f.effects {
                None => None,
                Some(names) => {
                    let mut row = Vec::with_capacity(names.len());
                    for n in names {
                        let e = crate::effects::by_identity(prog, n)
                            .ok_or_else(|| IrTyError::UnknownEffect(n.clone()))?;
                        row.push(weft_ir::EffectId(ir_index(e.index())));
                    }
                    row.sort_unstable();
                    row.dedup();
                    Some(row)
                }
            };
            T::Fn(IrFn { params, ret, row })
        }
        Ty::Param(i) => T::Param(*i),
        Ty::Scope => T::Scope,
        Ty::Cont(a, b) => {
            let a = final_ty(prog, table, a)?;
            T::Cont(a, final_ty(prog, table, b)?)
        }
        Ty::Error => return Err(IrTyError::ErrorType),
    };
    Ok(table.intern(ir))
}

/// Returns the prelude definition of the IR that definition `a` is, if any.
fn ir_lang(prog: &crate::Program, a: AdtId) -> Option<weft_ir::ty::Lang> {
    use weft_ir::ty::Lang;
    if prog.ptr == Some(a) {
        return Some(Lang::Ptr);
    }
    let def = &prog.adts[a];
    if def.module != crate::program::PRELUDE {
        return None;
    }
    Some(match def.name.as_str() {
        "Vec" => Lang::Vec,
        "Box" => Lang::Box,
        "Rc" => Lang::Rc,
        "Weak" => Lang::Weak,
        "String" => Lang::String,
        "Duration" => Lang::Duration,
        "Task" => Lang::Task,
        "Scope" => Lang::Scope,
        _ => return None,
    })
}

/// Returns the type table of the IR for `prog`: the declarations of its type
/// definitions and effects, with the same indexes, and their types.
///
/// The property rows of each definition are the rows of `Program::props`.
///
/// # Errors
///
/// [`IrTyError`] if a field, a variant or an operation has no final type.
pub fn ir_ty_table(prog: &crate::Program) -> Result<weft_ir::TyTable, IrTyError> {
    use crate::program::{AdtKind, Deref};
    use weft_ir::ty::{
        AdtDecl, AdtKind as K, EffectDecl, ExternDeref, FieldDecl, OpDecl, PropRow, VariantDecl,
    };
    let mut table = weft_ir::TyTable::new();
    let props = prog.props();
    for (i, def) in prog.adts.iter().enumerate() {
        let a = AdtId(i);
        let kind = match &def.kind {
            AdtKind::Struct(fs) => K::Struct(
                fs.iter()
                    .map(|f| {
                        Ok(FieldDecl {
                            name: f.name.clone(),
                            ty: final_ty(prog, &mut table, &f.ty)?,
                            place: f.place.is_some(),
                        })
                    })
                    .collect::<Result<_, IrTyError>>()?,
            ),
            AdtKind::Enum(vs) => K::Enum(
                vs.iter()
                    .map(|v| {
                        Ok(VariantDecl {
                            name: v.name.clone(),
                            fields: v
                                .fields
                                .iter()
                                .map(|x| final_ty(prog, &mut table, x))
                                .collect::<Result<_, _>>()?,
                        })
                    })
                    .collect::<Result<_, IrTyError>>()?,
            ),
            AdtKind::Extern {
                elem_unstable,
                deref,
            } => K::Extern {
                elem_unstable: *elem_unstable,
                deref: deref.map(|d| match d {
                    Deref::Stable => ExternDeref::Stable,
                    Deref::Unstable => ExternDeref::Unstable,
                    Deref::Group => ExternDeref::Group,
                }),
            },
        };
        let mut rows: [PropRow; 8] = Default::default();
        for p in crate::props::PROPS {
            if let Some(h) = props.get(a, p) {
                rows[crate::props::ir_prop(p).index()] = PropRow {
                    always: h.always,
                    params: h.params.iter().map(|&j| ir_index(j)).collect(),
                };
            }
        }
        table.push_adt(AdtDecl {
            name: def.name.clone(),
            generics: ir_index(def.generics.len()),
            kind,
            lang: ir_lang(prog, a),
            linear: def.linear,
            on_abort: def.on_abort.clone(),
            has_on_abort: def.has_on_abort,
            immovable: def.immovable,
            copy: def.copy,
            nonportable: def.nonportable,
            props: rows,
        });
    }
    for (i, def) in prog.effects.iter().enumerate() {
        let ops = def
            .ops
            .iter()
            .map(|o| {
                Ok(OpDecl {
                    name: o.name.clone(),
                    params: o
                        .params
                        .iter()
                        .map(|x| final_ty(prog, &mut table, x))
                        .collect::<Result<_, _>>()?,
                    ret: final_ty(prog, &mut table, &o.ret)?,
                    multi: o.multi,
                })
            })
            .collect::<Result<_, IrTyError>>()?;
        table.push_effect(EffectDecl {
            name: def.name.clone(),
            identity: crate::effects::identity(prog, crate::EffectId(i)),
            ops,
        });
    }
    Ok(table)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unify_binds_and_resolves() {
        let mut inf = Infer::default();
        let a = inf.fresh();
        let i = inf.fresh_int();
        assert!(inf.unify(&a, &Ty::Adt(AdtId(0), vec![i.clone()])));
        assert!(inf.unify(&i, &Ty::Int(IntTy::U32)));
        assert_eq!(
            inf.resolve(&a),
            Ty::Adt(AdtId(0), vec![Ty::Int(IntTy::U32)])
        );
        assert!(!inf.unify(&Ty::Bool, &Ty::Unit));
        let b = inf.fresh();
        assert!(!inf.unify(&b, &Ty::Ref(Box::new(b.clone()))));
        let j = inf.fresh_int();
        assert!(!inf.unify(&j, &Ty::Bool));
        assert_eq!(inf.resolve(&j), Ty::Int(IntTy::I64));
    }

    #[test]
    fn a_union_of_variables_keeps_the_links_short() {
        let mut inf = Infer::default();
        // Each update unifies the type of `s` with a new integer variable.
        let s = inf.fresh_int();
        for _ in 0..1000 {
            let lit = inf.fresh_int();
            assert!(inf.unify(&s, &lit));
            assert_eq!(inf.shallow(&lit), inf.shallow(&s));
        }
        assert!(inf.steps() < 4000, "{}", inf.steps());
        // A plain variable links to an integer variable, not the reverse.
        let v = inf.fresh();
        assert!(inf.unify(&s, &v));
        assert!(matches!(inf.shallow(&v), Ty::IntVar(_)));
        assert!(!inf.unify(&v, &Ty::Bool));
        assert!(inf.unify(&v, &Ty::Int(IntTy::U8)));
        assert_eq!(inf.resolve(&s), Ty::Int(IntTy::U8));
        // Two plain variables, and a cycle through a type.
        let (a, b) = (inf.fresh(), inf.fresh());
        assert!(inf.unify(&a, &b));
        assert!(!inf.unify(&a, &Ty::Ref(Box::new(b.clone()))));
        assert!(inf.unify(&b, &Ty::Bool));
        assert_eq!(inf.resolve(&a), Ty::Bool);
    }

    #[test]
    fn a_variable_links_to_a_bound_function_type() {
        let mut inf = Infer::default();
        let fn_ty = |summary| {
            Ty::Fn(Arc::new(FnTy {
                params: Vec::new(),
                ret: Ty::Unit,
                effects: None,
                summary,
                item: None,
            }))
        };
        // The element of a `Vec` gets a closure, and a second use of the type
        // links to the element variable, not to a copy of its type.
        let elem = inf.fresh();
        assert!(inf.unify(&elem, &fn_ty(Some(1))));
        let other = inf.fresh();
        assert!(inf.unify(&other, &elem));
        let Some((v, f)) = inf.bound_fn(&other) else {
            panic!("the variable is bound to a function type");
        };
        assert_eq!(f.summary, Some(1));
        // A new function value for the type reaches both variables.
        inf.rebind_fn(
            v,
            Arc::new(FnTy {
                summary: Some(2),
                ..(*f).clone()
            }),
        );
        assert_eq!(inf.resolve(&elem), fn_ty(Some(2)));
        assert_eq!(inf.resolve(&other), fn_ty(Some(2)));
        // A cycle through a bound variable is still an error.
        let w = inf.fresh();
        let list = inf.fresh();
        assert!(inf.unify(&list, &Ty::Adt(AdtId(0), vec![w.clone()])));
        assert!(!inf.unify(&w, &list));
    }

    #[test]
    fn subst_and_display() {
        let names = vec!["Vec".to_string()];
        let t = subst(
            &Ty::Adt(AdtId(0), vec![Ty::Param(0)]),
            &[Ty::Int(IntTy::U8)],
        );
        assert_eq!(
            Display {
                ty: &Ty::Ref(Box::new(t)),
                names: names.as_slice()
            }
            .to_string(),
            "&Vec<u8>"
        );
        let tup = Ty::Tuple(vec![Ty::Bool, Ty::Unit]);
        assert_eq!(
            Display {
                ty: &tup,
                names: names.as_slice()
            }
            .to_string(),
            "(bool, ())"
        );
        assert_eq!(IntTy::from_name("usize"), Some(IntTy::Usize));
        assert_eq!(IntTy::from_name("x"), None);
    }
}
