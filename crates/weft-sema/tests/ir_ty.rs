//! Tests of the final types of the IR: `types::to_ir_ty`, `types::ir_ty_table`
//! and `props::ir_props` (plan stage T2).

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::sync::Arc;

use weft_facts::VarKind;
use weft_ir::ty::{IntTy as IrInt, Lang, Props, Ty as IrTy, TyTable};
use weft_sema::props::{ir_prop, ir_props, PROPS};
use weft_sema::types::{ir_ty_table, to_ir_ty, FnTy, Infer, IntTy, IrTyError, Ty};
use weft_sema::{analyze_source, AdtId, Program};

/// Returns the program of `src`, with the prelude.
fn program(src: &str) -> weft_sema::Analysis {
    match analyze_source(src, weft_sema::Options::default()) {
        Ok(a) => a,
        Err(d) => panic!("the source does not parse: {}", d.message),
    }
}

/// Returns the type table of `prog`.
fn table(prog: &Program) -> TyTable {
    match ir_ty_table(prog) {
        Ok(t) => t,
        Err(e) => panic!("no type table: {e:?}"),
    }
}

fn adt(prog: &Program, name: &str) -> AdtId {
    AdtId(
        prog.adts
            .iter()
            .position(|a| a.name == name)
            .unwrap_or(usize::MAX),
    )
}

fn fn_ty(params: Vec<Ty>, ret: Ty, effects: Option<Vec<String>>, summary: Option<usize>) -> Ty {
    Ty::Fn(Arc::new(FnTy {
        params,
        ret,
        effects,
        summary,
        item: None,
    }))
}

#[test]
fn free_variables_get_unit_and_i64() {
    let a = program("");
    let prog = &a.program;
    let mut t = table(prog);
    let mut inf = Infer::default();
    let v = inf.fresh();
    let i = inf.fresh_int();
    assert_eq!(to_ir_ty(prog, &inf, &mut t, &v), Ok(t.unit()));
    let i64_t = t.intern(IrTy::Int(IrInt::I64));
    assert_eq!(to_ir_ty(prog, &inf, &mut t, &i), Ok(i64_t));
    // A free variable inside a type gets unit too.
    let vec = Ty::Adt(adt(prog, "Vec"), vec![inf.fresh()]);
    let Ok(id) = to_ir_ty(prog, &inf, &mut t, &vec) else {
        panic!("Vec<_> has a final type");
    };
    assert_eq!(t.show(id), "Vec<()>");
    // A bound variable gets its type.
    let w = inf.fresh();
    assert!(inf.unify(&w, &Ty::Int(IntTy::U8)));
    let u8_t = t.intern(IrTy::Int(IrInt::U8));
    assert_eq!(to_ir_ty(prog, &inf, &mut t, &w), Ok(u8_t));
}

#[test]
fn the_error_type_has_no_final_type() {
    let a = program("");
    let prog = &a.program;
    let mut t = table(prog);
    let inf = Infer::default();
    assert_eq!(
        to_ir_ty(prog, &inf, &mut t, &Ty::Error),
        Err(IrTyError::ErrorType)
    );
    let nested = Ty::Tuple(vec![Ty::Bool, Ty::Ref(Box::new(Ty::Error))]);
    assert_eq!(
        to_ir_ty(prog, &inf, &mut t, &nested),
        Err(IrTyError::ErrorType)
    );
    let row = fn_ty(Vec::new(), Ty::Unit, Some(vec!["NoSuch".into()]), None);
    assert_eq!(
        to_ir_ty(prog, &inf, &mut t, &row),
        Err(IrTyError::UnknownEffect("NoSuch".into()))
    );
}

#[test]
fn a_function_type_drops_its_closure_summary() {
    let a = program("");
    let prog = &a.program;
    let mut t = table(prog);
    let inf = Infer::default();
    let plain = fn_ty(vec![Ty::Bool], Ty::Unit, None, None);
    let closure = fn_ty(vec![Ty::Bool], Ty::Unit, None, Some(3));
    let item = Ty::Fn(Arc::new(FnTy {
        params: vec![Ty::Bool],
        ret: Ty::Unit,
        effects: None,
        summary: None,
        item: Some(weft_sema::FnId(0)),
    }));
    let ids: Vec<_> = [plain, closure, item]
        .iter()
        .map(|x| to_ir_ty(prog, &inf, &mut t, x))
        .collect();
    assert!(ids[0].is_ok());
    assert!(ids.iter().all(|x| *x == ids[0]), "{ids:?}");
    let row = fn_ty(
        Vec::new(),
        Ty::Unit,
        Some(vec!["Async".into(), "Fail".into()]),
        None,
    );
    let Ok(id) = to_ir_ty(prog, &inf, &mut t, &row) else {
        panic!("the row names standard effects");
    };
    assert_eq!(t.show(id), "fn() -> () / Async, Fail");
}

#[test]
fn the_declarations_copy_the_program() {
    let a = program(
        "linear struct Tok { id: u64 }\n\
         enum Opt2<T> { Yes(T), No }\n\
         effect Note { fn note(n: u64) -> bool }\n",
    );
    let prog = &a.program;
    let t = table(prog);
    assert_eq!(t.adts().len(), prog.adts.len());
    assert_eq!(t.effects().len(), prog.effects.len());
    for (i, d) in prog.adts.iter().enumerate() {
        let ir = &t.adts()[i];
        assert_eq!(ir.name, d.name);
        assert_eq!(ir.linear, d.linear);
        assert_eq!(ir.immovable, d.immovable);
        assert_eq!(ir.has_on_abort, d.has_on_abort);
        // The rows are the rows of the old table.
        for p in PROPS {
            let old = prog.props().get(AdtId(i), p).cloned().unwrap_or_default();
            let new = ir.row(ir_prop(p));
            assert_eq!(old.always, new.always, "{} {p:?}", d.name);
            let params: Vec<usize> = new.params.iter().map(|&j| j as usize).collect();
            assert_eq!(old.params, params, "{} {p:?}", d.name);
        }
    }
    for (name, lang) in [
        ("Vec", Lang::Vec),
        ("Box", Lang::Box),
        ("Rc", Lang::Rc),
        ("Weak", Lang::Weak),
        ("String", Lang::String),
        ("Duration", Lang::Duration),
        ("Task", Lang::Task),
        ("Scope", Lang::Scope),
    ] {
        assert_eq!(t.adts()[adt(prog, name).index()].lang, Some(lang), "{name}");
    }
    assert_eq!(t.adts()[adt(prog, "Tok").index()].lang, None);
    let Some(e) = prog.effects.iter().position(|e| e.name == "Note") else {
        panic!("the effect exists");
    };
    let note = &t.effects()[e];
    assert_eq!(note.identity, "main.Note");
    assert_eq!(note.ops.len(), 1);
    assert_eq!(t.show(note.ops[0].ret), "bool");
}

/// The corpus programs of the table test.
const CORPUS: [&str; 3] = [
    "35_wild_places.wf",
    "83_kept_values.wf",
    "153_partial_linear.wf",
];

/// Types of the prelude that each program can name.
const PRELUDE_TYPES: [&str; 16] = [
    "u8",
    "bool",
    "()",
    "String",
    "Duration",
    "Box<u64>",
    "Rc<Vec<u64>>",
    "Rc<fn(u64) -> u64>",
    "Weak<u64>",
    "Task<u64>",
    "Option<Task<u64>>",
    "&[u64]",
    "[u64; 3]",
    "*u64",
    "fn(u64) -> u64",
    "(u64, Box<u64>, &String)",
];

/// Returns true if a type text of the old facts can be the type of a
/// parameter: it names no inference variable, no type parameter, no error, no
/// continuation and no `!`.
fn writable(ty: &str) -> bool {
    let words = ty.split(|c: char| !(c.is_alphanumeric() || c == '_'));
    let param =
        |w: &str| w.len() > 1 && w.starts_with('T') && w[1..].bytes().all(|b| b.is_ascii_digit());
    !ty.contains(['{', '!'])
        && !ty.contains("resume(")
        && !words.clone().any(|w| w == "_" || param(w))
}

/// The flags of the old pipeline for a parameter, and the flags of `ir_props`
/// for its type, in one record.
#[derive(Debug, PartialEq, Eq)]
struct Flags {
    copy: bool,
    linear: bool,
    on_abort: bool,
    once: bool,
    immovable: bool,
    nonportable: bool,
    uniq: bool,
    callable: bool,
    generic: bool,
    holds_refs: bool,
}

impl From<Props> for Flags {
    fn from(p: Props) -> Self {
        Self {
            copy: p.copy,
            linear: p.linear,
            on_abort: p.on_abort,
            once: p.once,
            immovable: p.immovable,
            nonportable: p.nonportable,
            uniq: p.uniq,
            callable: p.callable,
            generic: p.generic,
            holds_refs: p.holds_refs,
        }
    }
}

#[test]
fn ir_props_of_the_corpus_types_equal_the_old_flags() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/programs/");
    let mut checked = 0;
    for name in CORPUS {
        let src = match std::fs::read_to_string(format!("{dir}{name}")) {
            Ok(s) => s,
            Err(e) => panic!("{name}: {e}"),
        };
        // The types of the variables of the old facts.
        let a = program(&src);
        let mut tys: BTreeSet<String> = PRELUDE_TYPES.iter().map(|s| (*s).to_string()).collect();
        for b in &a.bodies {
            for v in &b.facts.vars {
                if writable(&v.ty) {
                    tys.insert(v.ty.clone());
                }
            }
        }
        let tys: Vec<String> = tys.into_iter().collect();
        // One probe function for each type. The old pipeline gives its
        // parameter the flags of the type; a move of the parameter is a
        // `moved_at` fact only if the type is not plain data.
        let mut probe = src.clone();
        for (k, ty) in tys.iter().enumerate() {
            let _ = write!(probe, "\nfn ir_probe_{k}(x: {ty}) {{\n    let y = x\n}}\n");
        }
        let a = program(&probe);
        let prog = &a.program;
        let mut table = table(prog);
        let inf = Infer::default();
        for (k, ty) in tys.iter().enumerate() {
            let fname = format!("ir_probe_{k}");
            let Some(f) = prog.fns.iter().position(|f| f.name == fname) else {
                panic!("{name}: no function {fname}");
            };
            let Some(body) = a
                .bodies
                .iter()
                .find(|b| b.func.map(weft_sema::FnId::index) == Some(f))
            else {
                panic!("{name}: no facts for {fname} ({ty})");
            };
            let facts = &body.facts;
            let Some(x) = facts
                .vars
                .iter()
                .position(|v| v.name == "x" && v.kind == VarKind::Param)
            else {
                panic!("{name}: no parameter in {fname} ({ty})");
            };
            let info = &facts.vars[x];
            let sema_ty = &prog.fns[f].sig.params[0].ty;
            let old = Flags {
                copy: !facts.moved_at.iter().any(|(v, _)| v.index() == x),
                linear: info.linear,
                on_abort: info.has_on_abort,
                once: info.once,
                immovable: info.immovable,
                nonportable: info.nonportable,
                uniq: info.uniq,
                callable: info.callable,
                generic: false,
                holds_refs: prog.ty_holds_refs(sema_ty),
            };
            let Ok(id) = to_ir_ty(prog, &inf, &mut table, sema_ty) else {
                panic!("{name}: {ty} has no final type");
            };
            let new = Flags::from(ir_props(&table, id));
            assert_eq!(old, new, "{name}: {ty} ({})", table.show(id));
            checked += 1;
        }
    }
    assert!(checked > 40, "only {checked} types");
}

#[test]
fn ir_props_of_other_types() {
    let a = program(
        "linear struct Tok { id: u64 }\n\
         struct Frame: !Move { buf: [u8; 4] }\n\
         struct Gen<T> { x: T }\n\
         effect Note { fn note(n: u64) -> bool }\n",
    );
    let prog = &a.program;
    let mut t = table(prog);
    let inf = Infer::default();
    let mut props = |ty: &Ty| match to_ir_ty(prog, &inf, &mut t, ty) {
        Ok(id) => (ir_props(&t, id), t.show(id)),
        Err(e) => panic!("{e:?}"),
    };
    let tok = Ty::Adt(adt(prog, "Tok"), Vec::new());
    // A type parameter is not plain data and is not linear in a variable.
    let (p, s) = props(&Ty::Adt(adt(prog, "Gen"), vec![Ty::Param(0)]));
    assert!(p.generic && !p.copy && !p.linear, "{s}");
    let (p, s) = props(&Ty::Adt(adt(prog, "Gen"), vec![tok.clone()]));
    assert!(!p.generic && p.linear && !p.on_abort && p.once, "{s}");
    // A continuation is not `many`; the scope capability cannot cross threads.
    let (p, s) = props(&Ty::Cont(Box::new(Ty::Unit), Box::new(Ty::Bool)));
    assert!(p.once && !p.copy, "{s}");
    let (p, s) = props(&Ty::Scope);
    assert!(p.nonportable && p.once && p.copy, "{s}");
    let (p, s) = props(&Ty::Array(Box::new(tok), 2));
    assert!(p.linear && !p.copy, "{s}");
    let (p, s) = props(&Ty::Adt(adt(prog, "Frame"), Vec::new()));
    assert!(p.immovable && !p.copy && p.once, "{s}");
}
