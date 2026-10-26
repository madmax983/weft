//! Tests of the final type table: interning, the declarations and the text form.

use weft_ir::ty::{
    AdtDecl, AdtId, AdtKind, EffectDecl, EffectId, FieldDecl, FnTy, IntTy, Lang, OpDecl, PropRow,
    Ty, TyId, TyProp, TyTable, VariantDecl,
};

/// Returns a declaration with no flags and empty property rows.
fn decl(name: &str, generics: u32, kind: AdtKind, lang: Option<Lang>) -> AdtDecl {
    AdtDecl {
        name: name.to_string(),
        generics,
        kind,
        lang,
        linear: false,
        on_abort: None,
        has_on_abort: false,
        immovable: false,
        copy: false,
        nonportable: false,
        props: Default::default(),
    }
}

#[test]
fn equal_types_get_equal_ids() {
    let mut t = TyTable::new();
    let u8_a = t.intern(Ty::Int(IntTy::U8));
    let u8_b = t.intern(Ty::Int(IntTy::U8));
    assert_eq!(u8_a, u8_b);
    let i64_t = t.intern(Ty::Int(IntTy::I64));
    assert_ne!(u8_a, i64_t);
    let r1 = t.intern(Ty::Ref(u8_a));
    let r2 = t.intern(Ty::Ref(u8_b));
    assert_eq!(r1, r2);
    let tup1 = t.intern(Ty::Tuple(vec![r1, i64_t]));
    let tup2 = t.intern(Ty::Tuple(vec![r2, i64_t]));
    let tup3 = t.intern(Ty::Tuple(vec![i64_t, r2]));
    assert_eq!(tup1, tup2);
    assert_ne!(tup1, tup3);
    let f1 = t.intern(Ty::Fn(FnTy {
        params: vec![r1],
        ret: tup1,
        row: Some(vec![EffectId(0)]),
    }));
    let f2 = t.intern(Ty::Fn(FnTy {
        params: vec![r2],
        ret: tup2,
        row: Some(vec![EffectId(0)]),
    }));
    let f3 = t.intern(Ty::Fn(FnTy {
        params: vec![r2],
        ret: tup2,
        row: None,
    }));
    assert_eq!(f1, f2);
    assert_ne!(f1, f3);
    assert_eq!(t.get(tup1), &Ty::Tuple(vec![r1, i64_t]));
    assert_eq!(t.unit(), t.intern(Ty::Unit));
    // The ids are dense: one for each different type.
    assert_eq!(t.len(), 8);
    assert!(t.ids().all(|id| id.index() < t.len()));
}

#[test]
fn an_id_from_another_table_is_not_a_type() {
    let t = TyTable::new();
    assert!(t.try_get(TyId(5)).is_none());
}

#[test]
fn declarations_and_text() {
    let mut t = TyTable::new();
    let u64_t = t.intern(Ty::Int(IntTy::U64));
    let p0 = t.intern(Ty::Param(0));
    let vec = t.push_adt(decl(
        "Vec",
        1,
        AdtKind::Extern {
            elem_unstable: Some(true),
            deref: None,
        },
        Some(Lang::Vec),
    ));
    let mut tok = decl(
        "Tok",
        0,
        AdtKind::Struct(vec![FieldDecl {
            name: "id".to_string(),
            ty: u64_t,
            place: false,
        }]),
        None,
    );
    tok.linear = true;
    tok.props[TyProp::Linear.index()] = PropRow {
        always: true,
        params: Vec::new(),
    };
    let tok = t.push_adt(tok);
    let opt = t.push_adt(decl(
        "Option",
        1,
        AdtKind::Enum(vec![
            VariantDecl {
                name: "Some".to_string(),
                fields: vec![p0],
            },
            VariantDecl {
                name: "None".to_string(),
                fields: Vec::new(),
            },
        ]),
        None,
    ));
    assert_eq!((vec, tok, opt), (AdtId(0), AdtId(1), AdtId(2)));
    assert_eq!(t.adt(vec).lang, Some(Lang::Vec));
    assert!(t.adt(tok).row(TyProp::Linear).always);
    let log = t.push_effect(EffectDecl {
        name: "Log".to_string(),
        identity: "main.Log".to_string(),
        ops: vec![OpDecl {
            name: "log".to_string(),
            params: vec![u64_t],
            ret: t.unit(),
            multi: false,
        }],
    });
    assert_eq!(log, EffectId(0));
    assert_eq!(t.effect(log).ops.len(), 1);

    let tok_t = t.intern(Ty::Adt(tok, Vec::new()));
    let vec_tok = t.intern(Ty::Adt(vec, vec![tok_t]));
    let r = t.intern(Ty::Ref(vec_tok));
    let s = t.intern(Ty::Slice(u64_t));
    let rs = t.intern(Ty::Ref(s));
    let arr = t.intern(Ty::Array(u64_t, 4));
    let unit = t.unit();
    let f = t.intern(Ty::Fn(FnTy {
        params: vec![r, rs],
        ret: arr,
        row: Some(vec![log]),
    }));
    let cont = t.intern(Ty::Cont(u64_t, unit));
    let cap = t.intern(Ty::Cap(log));
    let it = t.intern(Ty::Iter(u64_t));
    let opt_p = t.intern(Ty::Adt(opt, vec![p0]));
    assert_eq!(t.lang(vec_tok), Some((Lang::Vec, &[tok_t][..])));
    assert_eq!(t.lang(tok_t), None);
    assert_eq!(t.show(r), "&Vec<Tok>");
    assert_eq!(t.show(f), "fn(&Vec<Tok>, &[u64]) -> [u64; 4] / main.Log");
    assert_eq!(t.show(cont), "resume(u64) -> ()");
    assert_eq!(t.show(cap), "Cap<main.Log>");
    assert_eq!(t.show(it), "Iter<u64>");
    assert_eq!(t.show(opt_p), "Option<T0>");
    let never = t.intern(Ty::Never);
    let scope = t.intern(Ty::Scope);
    let b = t.intern(Ty::Bool);
    let tup = t.intern(Ty::Tuple(vec![b, never, scope]));
    assert_eq!(t.show(tup), "(bool, !, Scope)");
    assert!(t.mentions_param(opt_p));
    assert!(!t.mentions_param(f));
}

#[test]
fn integer_types() {
    for i in IntTy::ALL {
        assert_eq!(IntTy::from_name(i.name()), Some(i));
    }
    assert_eq!(IntTy::from_name("u128"), None);
    assert_eq!(IntTy::U8.range(), (0, 255));
    assert_eq!(IntTy::I8.range(), (-128, 127));
}
