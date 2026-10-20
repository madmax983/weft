//! Tables that every run of one program shares: compiled code, built-in types,
//! native functions and the `stealable` relation from the checker.

use std::collections::BTreeSet;
use std::rc::Rc;

use weft_sema::program::{AdtKind, EffectId, FnId, ItemRef, Program, PRELUDE};
use weft_sema::types::{AdtId, IntTy, Ty};
use weft_sema::FnSig;
use weft_syntax::ast::Span;

use crate::compile::{Compiled, Compiler, Exports};

/// A function that the interpreter implements.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Native {
    /// `Vec.new()`.
    VecNew,
    /// `v.push(x)`.
    VecPush,
    /// `v.pop()`.
    VecPop,
    /// `v.clear()`.
    VecClear,
    /// `v.len()`.
    VecLen,
    /// `v.get(i)`.
    VecGet,
    /// `v.split_at(mid)`.
    VecSplitAt,
    /// `v.split_mut(mid)`.
    VecSplitMut,
    /// `Box.new(x)`.
    BoxNew,
    /// `Rc.new(x)`.
    RcNew,
    /// `r.clone()`.
    RcClone,
    /// `r.downgrade()`.
    RcDowngrade,
    /// `w.upgrade()`.
    WeakUpgrade,
    /// `s.len()`.
    StrLen,
    /// `t.join()`.
    TaskJoin,
    /// `t.detach()`.
    TaskDetach,
    /// `fs.read(path)`.
    FsRead,
    /// `net.listen(addr)`.
    NetListen,
    /// `stdout.write(s)`.
    StdoutWrite,
    /// `stdout.write_all(lines)`.
    StdoutWriteAll,
    /// `req.param(key)`.
    ReqParam,
    /// `Response.json(x)`.
    RespJson,
    /// `Response.text(s)`.
    RespText,
    /// `http.serve(listener, handler)`.
    HttpServe,
    /// `with_timeout(d) { block }`.
    WithTimeout,
    /// `sleep(d)`.
    Sleep,
    /// `sim.run(seed: n) { body }`.
    SimRun,
    /// `sim.net.partition(a, b)`.
    SimPartition,
    /// `sim.net.heal()`.
    SimHeal,
    /// `sim.clock.advance(d)`.
    SimAdvance,
    /// A foreign function of the user program. It runs on the blocking pool.
    UserExtern {
        /// The function declares `blocking`.
        blocking: bool,
    },
    /// A prelude function that the interpreter does not know.
    Unknown,
}

/// What the interpreter needs to know about one type definition.
#[derive(Clone, Debug)]
pub struct AdtInfo {
    /// The name.
    pub name: Rc<str>,
    /// Struct field names.
    pub fields: Vec<Rc<str>>,
    /// Enum variant names and payload sizes.
    pub variants: Vec<(Rc<str>, usize)>,
    /// The type is a struct.
    pub is_struct: bool,
    /// The type is linear.
    pub linear: bool,
    /// The `on abort` function.
    pub on_abort: Option<FnId>,
    /// For each struct field: the field has an unsigned integer type.
    pub unsigned: Vec<bool>,
}

/// Returns true for an unsigned integer type.
pub const fn is_unsigned(t: &Ty) -> bool {
    matches!(
        t,
        Ty::Int(IntTy::U8 | IntTy::U16 | IntTy::U32 | IntTy::U64 | IntTy::Usize)
    )
}

/// Built-in types and effects.
#[derive(Clone, Debug, Default)]
pub struct Builtins {
    /// `Vec`.
    pub vec: Option<AdtId>,
    /// `String`.
    pub string: Option<AdtId>,
    /// `Rc`.
    pub rc: Option<AdtId>,
    /// `Weak`.
    pub weak: Option<AdtId>,
    /// `Box`.
    pub boxed: Option<AdtId>,
    /// `Task`.
    pub task: Option<AdtId>,
    /// `Duration`.
    pub duration: Option<AdtId>,
    /// `Option`.
    pub option: Option<AdtId>,
    /// `Env`.
    pub env: Option<AdtId>,
    /// `FsCap`.
    pub fscap: Option<AdtId>,
    /// `NetCap`.
    pub netcap: Option<AdtId>,
    /// `Stdout`.
    pub stdout: Option<AdtId>,
    /// `Listener`.
    pub listener: Option<AdtId>,
    /// `Request`.
    pub request: Option<AdtId>,
    /// `Response`.
    pub response: Option<AdtId>,
    /// The `Fail` effect.
    pub fail: Option<EffectId>,
    /// The `Clock` effect.
    pub clock: Option<EffectId>,
}

/// The shared tables of one program.
#[derive(Debug)]
pub struct Runtime<'a> {
    /// The program.
    pub prog: &'a Program,
    /// The final signatures.
    pub sigs: &'a [FnSig],
    /// The compiled code.
    pub compiled: Compiled,
    /// The native implementation of each function, if any.
    pub natives: Vec<Option<Native>>,
    /// Type information.
    pub adts: Vec<AdtInfo>,
    /// For each type: values never copy.
    pub move_only: Rc<[bool]>,
    /// Built-in definitions.
    pub b: Builtins,
    /// The tasks that the checker marked stealable: the source unit and the
    /// span of the function value that each one runs.
    pub stealable: BTreeSet<(usize, u32, u32)>,
}

/// Returns the qualified name of a function: `Vec.push`, `sim.net.partition`.
pub fn qualified_name(prog: &Program, f: FnId) -> String {
    let def = &prog.fns[f];
    if let Some(o) = def.owner {
        return format!("{}.{}", prog.adts[o].name, def.name);
    }
    let mut names = vec![def.name.clone()];
    let mut m = def.module;
    while let Some(parent) = prog.mods[m].parent {
        if prog.mods[m].name.is_empty() {
            break;
        }
        names.push(prog.mods[m].name.clone());
        m = parent;
    }
    names.reverse();
    names.join(".")
}

fn native_of(prog: &Program, sigs: &[FnSig], f: FnId) -> Option<Native> {
    let def = &prog.fns[f];
    if !def.decl.is_extern {
        return None;
    }
    if !def.is_std {
        let blocking = sigs
            .get(f)
            .is_some_and(|s| s.effects.named.contains("Blocking"));
        return Some(Native::UserExtern { blocking });
    }
    Some(match qualified_name(prog, f).as_str() {
        "Vec.new" => Native::VecNew,
        "Vec.push" => Native::VecPush,
        "Vec.pop" => Native::VecPop,
        "Vec.clear" => Native::VecClear,
        "Vec.len" => Native::VecLen,
        "Vec.get" => Native::VecGet,
        "Vec.split_at" => Native::VecSplitAt,
        "Vec.split_mut" => Native::VecSplitMut,
        "Box.new" => Native::BoxNew,
        "Rc.new" => Native::RcNew,
        "Rc.clone" => Native::RcClone,
        "Rc.downgrade" => Native::RcDowngrade,
        "Weak.upgrade" => Native::WeakUpgrade,
        "String.len" => Native::StrLen,
        "Task.join" => Native::TaskJoin,
        "Task.detach" => Native::TaskDetach,
        "FsCap.read" => Native::FsRead,
        "NetCap.listen" => Native::NetListen,
        "Stdout.write" => Native::StdoutWrite,
        "Stdout.write_all" => Native::StdoutWriteAll,
        "Request.param" => Native::ReqParam,
        "Response.json" => Native::RespJson,
        "Response.text" => Native::RespText,
        "http.serve" => Native::HttpServe,
        "with_timeout" => Native::WithTimeout,
        "sleep" => Native::Sleep,
        "sim.run" => Native::SimRun,
        "sim.net.partition" => Native::SimPartition,
        "sim.net.heal" => Native::SimHeal,
        "sim.clock.advance" => Native::SimAdvance,
        _ => Native::Unknown,
    })
}

impl<'a> Runtime<'a> {
    /// Compiles a program and builds its tables. `exports` names the captures
    /// that each closure takes by value and the order of the arguments of some
    /// calls (see [`Exports`]).
    pub fn new(
        prog: &'a Program,
        sigs: &'a [FnSig],
        stealable: BTreeSet<(usize, u32, u32)>,
        exports: &Exports,
    ) -> Self {
        let compiled = Compiler::compile(prog, sigs, exports);
        let natives = (0..prog.fns.len())
            .map(|f| native_of(prog, sigs, f))
            .collect();
        let adts: Vec<AdtInfo> = prog
            .adts
            .iter()
            .map(|a| {
                let unsigned = match &a.kind {
                    AdtKind::Struct(fs) => fs.iter().map(|f| is_unsigned(&f.ty)).collect(),
                    _ => Vec::new(),
                };
                let (fields, variants, is_struct) = match &a.kind {
                    AdtKind::Struct(fs) => (
                        fs.iter().map(|f| Rc::from(f.name.as_str())).collect(),
                        Vec::new(),
                        true,
                    ),
                    AdtKind::Enum(vs) => (
                        Vec::new(),
                        vs.iter()
                            .map(|v| (Rc::from(v.name.as_str()), v.fields.len()))
                            .collect(),
                        false,
                    ),
                    AdtKind::Extern { .. } => (Vec::new(), Vec::new(), false),
                };
                let on_abort = a
                    .on_abort
                    .as_ref()
                    .and_then(|n| match prog.lookup(a.module, n) {
                        Some(ItemRef::Fn(f)) => Some(f),
                        _ => None,
                    });
                AdtInfo {
                    name: Rc::from(a.name.as_str()),
                    fields,
                    variants,
                    is_struct,
                    linear: a.linear,
                    on_abort,
                    unsigned,
                }
            })
            .collect();
        let move_only: Rc<[bool]> = prog.adts.iter().map(|a| a.linear || a.immovable).collect();
        let find = |n: &str| match prog.mods.get(PRELUDE).and_then(|m| m.items.get(n)) {
            Some(ItemRef::Adt(a)) => Some(*a),
            _ => None,
        };
        let eff = |n: &str| match prog.mods.get(PRELUDE).and_then(|m| m.items.get(n)) {
            Some(ItemRef::Effect(e)) => Some(*e),
            _ => None,
        };
        let b = Builtins {
            vec: find("Vec"),
            string: find("String"),
            rc: find("Rc"),
            weak: find("Weak"),
            boxed: find("Box"),
            task: find("Task"),
            duration: find("Duration"),
            option: find("Option"),
            env: find("Env"),
            fscap: find("FsCap").or_else(|| find("Fs")),
            netcap: find("NetCap"),
            stdout: find("Stdout"),
            listener: find("Listener"),
            request: find("Request"),
            response: find("Response"),
            fail: eff("Fail"),
            clock: eff("Clock"),
        };
        Self {
            prog,
            sigs,
            compiled,
            natives,
            adts,
            move_only,
            b,
            stealable,
        }
    }

    /// Returns true if the checker marked the task at this span of source
    /// unit `unit` stealable.
    pub fn is_stealable(&self, unit: usize, span: Span) -> bool {
        self.stealable.contains(&(unit, span.lo, span.hi))
    }

    /// Returns the variant index of a variant name in an enum.
    pub fn variant_index(&self, adt: AdtId, name: &str) -> Option<usize> {
        self.adts
            .get(adt)?
            .variants
            .iter()
            .position(|(n, _)| &**n == name)
    }

    /// Finds the `main` function of the root module.
    pub fn main_fn(&self) -> Option<FnId> {
        match self.prog.mods.get(self.prog.root)?.items.get("main") {
            Some(ItemRef::Fn(f)) => Some(*f),
            _ => None,
        }
    }
}
