//! The recorder: the old lowering writes its decisions here (`docs/ir.md` 2.2).
//!
//! The recorder only adds. It does not change what the lowering does. It
//! keeps the types as the lowering has them, with their inference variables.
//! At the end of the body [`Recorder::settle`] resolves them with the final
//! inference table, and [`build`] makes the [`Tables`] with final types.
//!
//! The lowering recurses deeply, so its state is here, in the lowering state,
//! and not in locals of its recursive functions.

use std::collections::{BTreeMap, HashMap};
use std::hash::Hash;

use weft_facts::VarId;

use super::{
    Binder, Binding, BindingId, Builtin, CallInfo, Callee, ClosureInfo, Conflict, DerefKind,
    ExprId, FieldIdx, HandleInfo, Key, PatId, Recv, Res, Tables, ValueProps,
};
use crate::ids::{FnId, ModId};
use crate::types::{Infer, IrTyError, Ty};

/// A name as the lowering resolves it, before the bindings get their ids.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawRes {
    /// The local with this variable.
    Local(VarId),
    /// A function item with its type arguments.
    Fn(FnId, Vec<Ty>),
    /// A variant.
    Variant(crate::ids::AdtId, usize),
    /// A struct constructor.
    Struct(crate::ids::AdtId),
    /// An operation.
    Op(crate::ids::EffectId, usize),
    /// A built-in.
    Builtin(Builtin),
    /// A module.
    Mod(ModId),
    /// A type definition.
    Adt(crate::ids::AdtId),
    /// An effect.
    Effect(crate::ids::EffectId),
}

/// A callee as the lowering resolves it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawCallee {
    /// A function item with its type arguments.
    Item(FnId, Vec<Ty>),
    /// The function value in the local with this variable.
    Value(VarId),
    /// The continuation in the local with this variable.
    Resume(VarId),
    /// An operation.
    Op(crate::ids::EffectId, usize),
    /// A struct constructor with its type arguments.
    Struct(crate::ids::AdtId, Vec<Ty>),
    /// A variant constructor with its type arguments.
    Variant(crate::ids::AdtId, usize, Vec<Ty>),
    /// A built-in.
    Builtin(Builtin),
}

/// A call as the lowering records it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCall {
    callee: RawCallee,
    recv: Option<Recv>,
    args: Vec<Option<u32>>,
}

/// A closure literal as the lowering records it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawClosure {
    params: Vec<Binder>,
    ret: Ty,
    row: Option<Vec<String>>,
}

/// Adds `v` to the values of `k` if it is new.
fn add<K: Eq + Hash, V: PartialEq>(m: &mut HashMap<K, Vec<V>>, k: K, v: V) {
    let vs = m.entry(k).or_default();
    if !vs.contains(&v) {
        vs.push(v);
    }
}

/// The decisions of one lowering of a body.
#[derive(Clone, Debug, Default)]
pub struct Recorder {
    /// The expressions that the lowering is in, the innermost last
    /// ([`crate::body`] pushes each expression that `expr` lowers, and each
    /// closure literal).
    pub open: Vec<ExprId>,
    /// The expression whose place the lowering found through a reference: a
    /// local of a reference type, or a temporary reference. The place of its
    /// parent takes it.
    pub base_deref: Option<ExprId>,
    /// The index of the clause whose parameters the lowering binds.
    pub clause: u32,
    /// The callee name of a call whose function item the lowering looks up.
    pub callee_name: Option<ExprId>,
    /// The receiver of the method call whose receiver mode the lowering
    /// decides next.
    pub recv_expr: Option<ExprId>,
    /// The calls whose parts the lowering records now.
    pending: HashMap<ExprId, RawCall>,
    expr_ty: HashMap<ExprId, Vec<Ty>>,
    pat_ty: HashMap<PatId, Vec<Ty>>,
    binders: HashMap<Binder, (String, Vec<Ty>)>,
    var_binder: HashMap<VarId, Binder>,
    res: HashMap<ExprId, Vec<RawRes>>,
    call: HashMap<ExprId, Vec<RawCall>>,
    adjust: HashMap<ExprId, Vec<Vec<DerefKind>>>,
    pat_adjust: HashMap<PatId, Vec<Vec<DerefKind>>>,
    field: HashMap<ExprId, Vec<FieldIdx>>,
    int_op: HashMap<ExprId, Vec<Ty>>,
    closure: HashMap<ExprId, Vec<RawClosure>>,
    handle: HashMap<ExprId, Vec<HandleInfo>>,
    effect: HashMap<ExprId, Vec<crate::ids::EffectId>>,
}

impl Recorder {
    /// The innermost open expression.
    pub fn top(&self) -> Option<ExprId> {
        self.open.last().copied()
    }

    /// Records the type of a visit of expression `e`.
    pub fn expr_ty(&mut self, e: ExprId, t: &Ty) {
        let vs = self.expr_ty.entry(e).or_default();
        if !vs.contains(t) {
            vs.push(t.clone());
        }
    }

    /// Records the type of the value at pattern `p`.
    pub fn pat_ty(&mut self, p: PatId, t: &Ty) {
        let vs = self.pat_ty.entry(p).or_default();
        if !vs.contains(t) {
            vs.push(t.clone());
        }
    }

    /// Records a binding with variable `var`, name `name` and type `t`.
    pub fn bind(&mut self, b: Binder, var: VarId, name: &str, t: &Ty) {
        self.var_binder.insert(var, b);
        let e = self
            .binders
            .entry(b)
            .or_insert_with(|| (name.to_string(), Vec::new()));
        if !e.1.contains(t) {
            e.1.push(t.clone());
        }
    }

    /// Records what name `e` means.
    pub fn res(&mut self, e: ExprId, r: RawRes) {
        add(&mut self.res, e, r);
    }

    /// Records the effect of an operation name, an effect path or a `handle`.
    pub fn effect(&mut self, e: ExprId, x: crate::ids::EffectId) {
        add(&mut self.effect, e, x);
    }

    /// Records the callee of the innermost open call, with `n` explicit
    /// arguments and a trailing block if `trailing`. The arguments bind by
    /// position until [`Recorder::args`] gives their order.
    pub fn callee(&mut self, c: RawCallee, n: usize, trailing: bool) {
        let Some(e) = self.top() else {
            return;
        };
        let count = n + usize::from(trailing);
        let args = (0..count).map(|k| u32::try_from(k).ok()).collect();
        self.pending.insert(
            e,
            RawCall {
                callee: c,
                recv: None,
                args,
            },
        );
    }

    /// Records the argument of each parameter of the innermost open call.
    pub fn args(&mut self, slots: &[Option<usize>]) {
        let Some(e) = self.top() else {
            return;
        };
        if let Some(c) = self.pending.get_mut(&e) {
            c.args = slots
                .iter()
                .map(|s| s.and_then(|k| u32::try_from(k).ok()))
                .collect();
        }
    }

    /// Records the receiver of the innermost open method call.
    pub fn recv(&mut self, r: Recv) {
        let Some(e) = self.top() else {
            return;
        };
        if let Some(c) = self.pending.get_mut(&e) {
            c.recv = Some(r);
        }
    }

    /// Ends a visit of call `e`: its record goes to the table.
    pub fn end_call(&mut self, e: ExprId) {
        if let Some(c) = self.pending.remove(&e) {
            add(&mut self.call, e, c);
        }
    }

    /// Records the dereferences of the value of expression `e`.
    pub fn adjust(&mut self, e: ExprId, steps: Vec<DerefKind>) {
        add(&mut self.adjust, e, steps);
    }

    /// Takes the dereference of the place of expression `e` that the lowering
    /// found ([`Recorder::base_deref`]).
    pub fn take_base(&mut self, e: ExprId) -> Option<DerefKind> {
        (self.base_deref == Some(e)).then(|| {
            self.base_deref = None;
            DerefKind::Ref
        })
    }

    /// Records the dereferences of the value at pattern `p`.
    pub fn pat_adjust(&mut self, p: PatId, steps: Vec<DerefKind>) {
        add(&mut self.pat_adjust, p, steps);
    }

    /// Records the part that field expression `e` names.
    pub fn field(&mut self, e: ExprId, f: FieldIdx) {
        add(&mut self.field, e, f);
    }

    /// Records the type of the arithmetic at expression `e`.
    pub fn int_op(&mut self, e: ExprId, t: &Ty) {
        let vs = self.int_op.entry(e).or_default();
        if !vs.contains(t) {
            vs.push(t.clone());
        }
    }

    /// Records closure literal `e`.
    pub fn closure(&mut self, e: ExprId, params: Vec<Binder>, ret: &Ty, row: Option<Vec<String>>) {
        add(
            &mut self.closure,
            e,
            RawClosure {
                params,
                ret: ret.clone(),
                row,
            },
        );
    }

    /// Records `handle` expression `e`.
    pub fn handle(&mut self, e: ExprId, h: HandleInfo) {
        add(&mut self.handle, e, h);
    }

    /// Replaces each type with its resolved type: the inference of the body
    /// has ended.
    pub fn settle(&mut self, inf: &Infer) {
        let fix = |ts: &mut Vec<Ty>| {
            let mut out: Vec<Ty> = Vec::with_capacity(ts.len());
            for t in ts.drain(..) {
                let r = inf.resolve(&t);
                if !out.contains(&r) {
                    out.push(r);
                }
            }
            *ts = out;
        };
        self.expr_ty.values_mut().for_each(fix);
        self.pat_ty.values_mut().for_each(fix);
        self.int_op.values_mut().for_each(fix);
        for (_, ts) in self.binders.values_mut() {
            fix(ts);
        }
        let targs = |ts: &mut Vec<Ty>| {
            for t in ts.iter_mut() {
                *t = inf.resolve(t);
            }
        };
        for rs in self.res.values_mut() {
            for r in rs.iter_mut() {
                if let RawRes::Fn(_, ts) = r {
                    targs(ts);
                }
            }
        }
        for cs in self.call.values_mut() {
            for c in cs.iter_mut() {
                match &mut c.callee {
                    RawCallee::Item(_, ts)
                    | RawCallee::Struct(_, ts)
                    | RawCallee::Variant(_, _, ts) => targs(ts),
                    _ => {}
                }
            }
        }
        for cs in self.closure.values_mut() {
            for c in cs.iter_mut() {
                c.ret = inf.resolve(&c.ret);
            }
        }
        self.open.clear();
        self.pending.clear();
    }
}

/// Returns true if `t` has an inference variable.
fn has_var(t: &Ty) -> bool {
    match t {
        Ty::Var(_) | Ty::IntVar(_) => true,
        Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().any(has_var),
        Ty::Ref(x) | Ty::Slice(x) | Ty::Array(x, _) => has_var(x),
        Ty::Cont(a, b) => has_var(a) || has_var(b),
        Ty::Fn(f) => f.params.iter().any(has_var) || has_var(&f.ret),
        Ty::Int(_) | Ty::Bool | Ty::Unit | Ty::Never | Ty::Param(_) | Ty::Scope | Ty::Error => {
            false
        }
    }
}

/// The conversion of the records of one body to [`Tables`].
struct Build<'a> {
    prog: &'a crate::Program,
    table: &'a mut weft_ir::TyTable,
    out: Tables,
}

impl Build<'_> {
    /// The final type of the settled type `t`, or `None` after an error.
    fn ty(&mut self, t: &Ty) -> Option<weft_ir::TyId> {
        match crate::types::final_ty(self.prog, self.table, t) {
            Ok(id) => Some(id),
            Err(IrTyError::ErrorType | IrTyError::UnknownEffect(_)) => {
                self.out.error = true;
                None
            }
        }
    }

    /// The final types of `ts`, or `None` after an error.
    fn tys(&mut self, ts: &[Ty]) -> Option<Vec<weft_ir::TyId>> {
        ts.iter().map(|t| self.ty(t)).collect()
    }

    /// The one value of `vs`. Two different values are a conflict.
    fn one<T: Clone + PartialEq + std::fmt::Debug>(
        &mut self,
        table: &'static str,
        key: Key,
        vs: Vec<T>,
    ) -> Option<T> {
        let mut distinct: Vec<T> = Vec::new();
        for v in vs {
            if !distinct.contains(&v) {
                distinct.push(v);
            }
        }
        if distinct.len() > 1 {
            self.out.conflicts.push(Conflict {
                table,
                key,
                values: distinct.iter().map(|v| format!("{v:?}")).collect(),
            });
        }
        distinct.into_iter().next()
    }

    /// The one final type of the visits `ts`.
    fn one_ty(&mut self, table: &'static str, key: Key, ts: &[Ty]) -> Option<weft_ir::TyId> {
        let ids: Vec<weft_ir::TyId> = ts.iter().filter_map(|t| self.ty(t)).collect();
        if ids.len() < ts.len() {
            return None;
        }
        let mut distinct: Vec<weft_ir::TyId> = Vec::new();
        for id in ids {
            if !distinct.contains(&id) {
                distinct.push(id);
            }
        }
        if distinct.len() > 1 {
            let values = distinct.iter().map(|&id| self.table.show(id)).collect();
            self.out.conflicts.push(Conflict { table, key, values });
        }
        distinct.first().copied()
    }
}

/// The id of a definition of the program in the IR.
fn adt(a: crate::ids::AdtId) -> weft_ir::AdtId {
    weft_ir::AdtId(idx(a.index()))
}

/// The id of an effect of the program in the IR.
fn eff(e: crate::ids::EffectId) -> weft_ir::EffectId {
    weft_ir::EffectId(idx(e.index()))
}

/// A `u32` index.
fn idx(i: usize) -> u32 {
    u32::try_from(i).unwrap_or(u32::MAX)
}

/// Makes the tables of a body from its settled records ([`Recorder::settle`]).
/// The final types go into `table`. `vars` are the variables of the facts of
/// the body: each binding gets the properties of its variables
/// ([`Binding::value`]).
pub fn build(
    prog: &crate::Program,
    table: &mut weft_ir::TyTable,
    rec: Recorder,
    vars: &[weft_facts::VarInfo],
) -> Tables {
    let mut b = Build {
        prog,
        table,
        out: Tables::default(),
    };
    // The bindings, in the order of their binders.
    let binders: BTreeMap<Binder, (String, Vec<Ty>)> = rec.binders.into_iter().collect();
    let mut ids: BTreeMap<Binder, BindingId> = BTreeMap::new();
    // The properties of the variables of each binder, as the analysis ends.
    let mut values: HashMap<Binder, ValueProps> = HashMap::new();
    for (v, binder) in &rec.var_binder {
        let Some(info) = vars.get(v.index()) else {
            continue;
        };
        let x = values.entry(*binder).or_default();
        x.linear |= info.linear;
        x.no_on_abort |= info.linear && !info.has_on_abort;
        x.once |= info.once;
        x.nonportable |= info.nonportable;
    }
    for (binder, (name, ts)) in binders {
        let key = match binder {
            Binder::Pat(p) => Key::Pat(p),
            Binder::ClosureParam(e, _)
            | Binder::ClauseParam(e, _, _)
            | Binder::Resume(e, _)
            | Binder::Scope(e) => Key::Expr(e),
            Binder::Param(i) => Key::Param(i),
        };
        let ty = b
            .one_ty("binding", key, &ts)
            .unwrap_or_else(|| b.table.unit());
        let id = BindingId(idx(b.out.bindings.len()));
        let value = values.get(&binder).copied().unwrap_or_default();
        b.out.bindings.push(Binding {
            binder,
            name,
            ty,
            value,
        });
        ids.insert(binder, id);
        if let Binder::Pat(p) = binder {
            b.out.binding.insert(p, id);
        }
    }
    let var_binding = |v: &VarId| rec.var_binder.get(v).and_then(|x| ids.get(x)).copied();
    let sorted =
        |m: HashMap<ExprId, Vec<Ty>>| -> BTreeMap<ExprId, Vec<Ty>> { m.into_iter().collect() };
    for (e, ts) in sorted(rec.expr_ty) {
        if ts.iter().any(has_var) {
            b.out.free.push(e);
        }
        if let Some(id) = b.one_ty("expr_ty", Key::Expr(e), &ts) {
            b.out.expr_ty.insert(e, id);
        }
    }
    let pats: BTreeMap<PatId, Vec<Ty>> = rec.pat_ty.into_iter().collect();
    for (p, ts) in pats {
        if let Some(id) = b.one_ty("pat_ty", Key::Pat(p), &ts) {
            b.out.pat_ty.insert(p, id);
        }
    }
    let res: BTreeMap<ExprId, Vec<RawRes>> = rec.res.into_iter().collect();
    for (e, rs) in res {
        let mut done = Vec::new();
        for r in rs {
            let x = match r {
                RawRes::Local(v) => var_binding(&v).map(Res::Local),
                RawRes::Fn(f, ts) => b.tys(&ts).map(|targs| Res::Fn { item: f, targs }),
                RawRes::Variant(a, v) => Some(Res::Variant {
                    adt: adt(a),
                    variant: idx(v),
                }),
                RawRes::Struct(a) => Some(Res::Struct(adt(a))),
                RawRes::Op(x, o) => Some(Res::Op {
                    effect: eff(x),
                    op: idx(o),
                }),
                RawRes::Builtin(x) => Some(Res::Builtin(x)),
                RawRes::Mod(m) => Some(Res::Mod(m)),
                RawRes::Adt(a) => Some(Res::Adt(adt(a))),
                RawRes::Effect(x) => Some(Res::Effect(eff(x))),
            };
            done.extend(x);
        }
        if let Some(r) = b.one("res", Key::Expr(e), done) {
            b.out.res.insert(e, r);
        }
    }
    let calls: BTreeMap<ExprId, Vec<RawCall>> = rec.call.into_iter().collect();
    for (e, cs) in calls {
        let mut done = Vec::new();
        for c in cs {
            let callee = match c.callee {
                RawCallee::Item(f, ts) => b.tys(&ts).map(|targs| Callee::Item { item: f, targs }),
                RawCallee::Value(v) => var_binding(&v).map(Callee::Value),
                RawCallee::Resume(v) => var_binding(&v).map(Callee::Resume),
                RawCallee::Op(x, o) => Some(Callee::Op {
                    effect: eff(x),
                    op: idx(o),
                }),
                RawCallee::Struct(a, ts) => b
                    .tys(&ts)
                    .map(|targs| Callee::Struct { adt: adt(a), targs }),
                RawCallee::Variant(a, v, ts) => b.tys(&ts).map(|targs| Callee::Variant {
                    adt: adt(a),
                    variant: idx(v),
                    targs,
                }),
                RawCallee::Builtin(x) => Some(Callee::Builtin(x)),
            };
            if let Some(callee) = callee {
                done.push(CallInfo {
                    callee,
                    recv: c.recv,
                    args: c.args,
                });
            }
        }
        if let Some(c) = b.one("call", Key::Expr(e), done) {
            b.out.call.insert(e, c);
        }
    }
    let adjusts: BTreeMap<ExprId, Vec<Vec<DerefKind>>> = rec.adjust.into_iter().collect();
    for (e, vs) in adjusts {
        if let Some(steps) = b.one("adjust", Key::Expr(e), vs) {
            if !steps.is_empty() {
                b.out.adjust.insert(e, steps);
            }
        }
    }
    let adjusts: BTreeMap<PatId, Vec<Vec<DerefKind>>> = rec.pat_adjust.into_iter().collect();
    for (p, vs) in adjusts {
        if let Some(steps) = b.one("pat_adjust", Key::Pat(p), vs) {
            if !steps.is_empty() {
                b.out.pat_adjust.insert(p, steps);
            }
        }
    }
    let fields: BTreeMap<ExprId, Vec<FieldIdx>> = rec.field.into_iter().collect();
    for (e, vs) in fields {
        if let Some(f) = b.one("field", Key::Expr(e), vs) {
            b.out.field.insert(e, f);
        }
    }
    let ops: BTreeMap<ExprId, Vec<Ty>> = rec.int_op.into_iter().collect();
    for (e, ts) in ops {
        // Arithmetic on a `String` or a `Duration` has no integer type.
        let ints: Vec<crate::types::IntTy> = ts
            .iter()
            .filter_map(|t| match t {
                Ty::Int(i) => Some(*i),
                _ => None,
            })
            .collect();
        if let Some(i) = b.one("int_ty", Key::Expr(e), ints) {
            b.out.int_ty.insert(e, crate::types::to_ir_int(i));
        }
    }
    let closures: BTreeMap<ExprId, Vec<RawClosure>> = rec.closure.into_iter().collect();
    for (e, cs) in closures {
        let mut done = Vec::new();
        for c in cs {
            let params: Option<Vec<BindingId>> =
                c.params.iter().map(|p| ids.get(p).copied()).collect();
            let Some(params) = params else {
                continue;
            };
            let Some(ret) = b.ty(&c.ret) else {
                continue;
            };
            let row = match &c.row {
                None => None,
                Some(names) => {
                    let ids: Option<Vec<weft_ir::EffectId>> = names
                        .iter()
                        .map(|n| crate::effects::by_identity(prog, n).map(eff))
                        .collect();
                    let Some(mut ids) = ids else {
                        b.out.error = true;
                        continue;
                    };
                    ids.sort_unstable();
                    ids.dedup();
                    Some(ids)
                }
            };
            done.push(ClosureInfo { params, ret, row });
        }
        if let Some(c) = b.one("closure", Key::Expr(e), done) {
            b.out.closure.insert(e, c);
        }
    }
    let handles: BTreeMap<ExprId, Vec<HandleInfo>> = rec.handle.into_iter().collect();
    for (e, hs) in handles {
        if let Some(h) = b.one("handle", Key::Expr(e), hs) {
            b.out.handle.insert(e, h);
        }
    }
    let effects: BTreeMap<ExprId, Vec<crate::ids::EffectId>> = rec.effect.into_iter().collect();
    for (e, xs) in effects {
        let xs: Vec<weft_ir::EffectId> = xs.into_iter().map(eff).collect();
        if let Some(x) = b.one("effect", Key::Expr(e), xs) {
            b.out.effect.insert(e, x);
        }
    }
    b.out
}
