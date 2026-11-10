//! The properties of the values of the bindings, from the IR (plan stage
//! R0i-b, `docs/ir.md` 2.3, 5.22).
//!
//! A function type does not show that a value is a linear, a nonportable or
//! a `once` closure: `let g = f`, a pattern binding and a parameter of a
//! clause can hold one. The builder puts these properties into the
//! `LocalDecl::props` of the local of a binding (`Builder::binding_props_of`).
//! Before stage R0i-b they came from the value flow of the old lowering
//! (`thir::Binding::value`). Now `infer` gives them from the IR:
//!
//! - each local starts with the properties of its type;
//! - a closure has the properties of its captures (a linear capture makes a
//!   linear closure, a nonportable capture a nonportable one, a moved capture
//!   that is not plain data or a `once` value a `once` one) and of its
//!   declaration (`ClosureDecl::once`);
//! - an assignment gives the properties of its right side to the local of
//!   its place: a copy or a move of a place, a reference, an aggregate (the
//!   join of its operands), a closure;
//! - a call gives the properties of `_0` of each body that it can run: the
//!   function of a `Call`, and each closure and function item that the value
//!   of a call of a function value can be;
//! - a perform gives each argument to the parameter of each clause of its
//!   operation, and its result gets the argument of each `resume` there;
//! - a `handle` and a `scope` get `_0` of their bodies; an upvar local and
//!   its local in the parent share their properties; the environment of a
//!   closure body gets the captures of each closure value of the body.
//!
//! The analysis joins the properties over the whole body, also values that
//! come later (a closure that is assigned after a read of the local). A
//! parameter of a function and of a closure gets no properties from its
//! callers, as in the old value flow: the caller cannot give a `once` or a
//! linear value there (W0502, W0601 at the call).
//!
//! The builder reads the properties while it builds (the cleanup gives a
//! local that can hold a linear closure an `UnwindValue`). So `build` runs
//! the builder again with the properties of the last round until they do not
//! change ([`super::build`]). The properties only grow, and each local has
//! four of them, so the rounds end.

use std::collections::{BTreeSet, HashMap};

use weft_ir::{
    AggKind, BodyId, Callee, CaptureMode, ClosureId, Const, FnId, IterSource, LocalId, LocalKind,
    Operand, Place, Program, Rvalue, StmtKind, TermKind, Ty, TyTable,
};

use crate::thir::{BindingId, ValueProps};

/// The properties of the values of the bindings of one entry body.
pub type BindingValues = HashMap<BindingId, ValueProps>;

/// What the analysis knows about the values of one local.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Val {
    /// The properties.
    props: ValueProps,
    /// The closures that the value can be.
    closures: BTreeSet<ClosureId>,
    /// The function items that the value can be.
    items: BTreeSet<FnId>,
    /// The parameters of a body whose value the value can be, by the body
    /// and the index: a call substitutes the arguments for them.
    params: BTreeSet<(BodyId, usize)>,
    /// The locals that a reference of the value can point to.
    refs: BTreeSet<(BodyId, LocalId)>,
}

impl Val {
    /// Joins `o` into `self`. Returns true if `self` grows.
    fn join(&mut self, o: &Self) -> bool {
        let before = (
            self.props,
            self.closures.len(),
            self.items.len(),
            self.params.len(),
            self.refs.len(),
        );
        self.props.linear |= o.props.linear;
        self.props.no_on_abort |= o.props.no_on_abort;
        self.props.once |= o.props.once;
        self.props.nonportable |= o.props.nonportable;
        self.closures.extend(o.closures.iter().copied());
        self.items.extend(o.items.iter().copied());
        self.params.extend(o.params.iter().copied());
        self.refs.extend(o.refs.iter().copied());
        before
            != (
                self.props,
                self.closures.len(),
                self.items.len(),
                self.params.len(),
                self.refs.len(),
            )
    }
}

/// The state of the analysis: the value of each local of each body.
struct Flow<'a> {
    /// The program.
    p: &'a Program,
    /// The types.
    tys: &'a TyTable,
    /// The value of each local.
    vals: HashMap<(BodyId, LocalId), Val>,
    /// What a body writes through a reference of parameter `i`: a call
    /// writes it, with the arguments for the parameters, into the locals
    /// that the argument points to.
    writes: HashMap<(BodyId, usize), Val>,
    /// The values grew in this pass.
    grew: bool,
}

impl Flow<'_> {
    /// The value of local `l` of body `b`.
    fn get(&self, b: BodyId, l: LocalId) -> Val {
        self.vals.get(&(b, l)).cloned().unwrap_or_default()
    }

    /// Joins `v` into the value of local `l` of body `b`.
    fn put(&mut self, b: BodyId, l: LocalId, v: &Val) {
        let grew = self.vals.entry((b, l)).or_default().join(v);
        self.grew |= grew;
    }

    /// Writes `v` through the references of `r` (a write through a
    /// reference, a callee that keeps an argument behind a reference).
    fn write_through(&mut self, r: &Val, v: &Val) {
        for &(rb, rl) in &r.refs {
            self.put(rb, rl, v);
        }
        for &k in &r.params {
            let grew = self.writes.entry(k).or_default().join(v);
            self.grew |= grew;
        }
    }

    /// `v` with the arguments `args` of body `b` for the parameters of body
    /// `callee`.
    fn subst(&self, b: BodyId, callee: BodyId, v: &Val, args: &[Operand]) -> Val {
        let mut out = v.clone();
        let given: Vec<usize> = out
            .params
            .iter()
            .filter(|(pb, _)| *pb == callee)
            .map(|&(_, j)| j)
            .collect();
        out.params.retain(|(pb, _)| *pb != callee);
        for j in given {
            if let Some(a) = args.get(j) {
                out.join(&self.operand(b, a));
            }
        }
        out
    }

    /// The writes of a call of body `callee` with the arguments `args` of
    /// body `b` (`writes`), or, for a callee with no body, of each argument
    /// into each argument whose type is a reference to a type with a
    /// function part (`Vec.push`).
    fn call_writes(&mut self, b: BodyId, callee: Option<BodyId>, args: &[Operand]) {
        for (i, a) in args.iter().enumerate() {
            let r = self.operand(b, a);
            if r.refs.is_empty() && r.params.is_empty() {
                continue;
            }
            let v = if let Some(cb) = callee {
                let Some(w) = self.writes.get(&(cb, i)).cloned() else {
                    continue;
                };
                self.subst(b, cb, &w, args)
            } else {
                {
                    let ty = a
                        .place()
                        .and_then(|q| self.p.body(b)?.locals.get(q.local.index()))
                        .filter(|_| a.place().is_some_and(|q| q.proj.is_empty()))
                        .map(|d| d.ty);
                    let fns = ty.is_some_and(|t| match self.tys.try_get(t) {
                        Some(Ty::Ref(x)) => crate::props::ir_has_fns(self.tys, *x),
                        _ => false,
                    });
                    if !fns {
                        continue;
                    }
                    let mut v = Val::default();
                    for (j, o) in args.iter().enumerate() {
                        if j != i {
                            v.join(&self.operand(b, o));
                        }
                    }
                    v.refs.clear();
                    v
                }
            };
            self.write_through(&r, &v);
        }
    }

    /// The value that operand `op` of body `b` reads.
    fn operand(&self, b: BodyId, op: &Operand) -> Val {
        match op {
            Operand::Copy(p) | Operand::Move(p) => self.get(b, p.local),
            Operand::Const(Const::Fn(g, _)) => Val {
                items: BTreeSet::from([*g]),
                ..Val::default()
            },
            Operand::Const(_) => Val::default(),
        }
    }

    /// The value of a new closure `c` (`Builder::closure_props`): its
    /// captures and its declaration give its properties.
    fn closure(&self, c: ClosureId) -> Val {
        let mut v = Val {
            closures: BTreeSet::from([c]),
            ..Val::default()
        };
        let Some(d) = self.p.closures.get(c.index()) else {
            return v;
        };
        v.props.once |= d.once || self.calls_once(d.body);
        for cap in &d.captures {
            let mut src = self.get(d.maker, cap.source.local);
            // A capture of a type with no function part has the props of
            // its declaration (`Builder::closure_props`): a part of a
            // linear struct is not linear by itself (`let G(x) = g` with
            // `x: T` in a generic body).
            if let Some(sd) = self
                .p
                .body(d.maker)
                .and_then(|x| x.locals.get(cap.source.local.index()))
            {
                if !self.tys.mentions_fn(sd.ty) {
                    src.props = decl_props(sd);
                }
            }
            v.params.extend(src.params.iter().copied());
            match cap.mode {
                CaptureMode::ByMove | CaptureMode::Kont => {
                    // A `@ uniq` capture makes a `once` closure, as
                    // `Builder::closure_props` says.
                    v.props.once |= self.uniq(d.maker, cap.source.local, false);
                    v.props.linear |= src.props.linear;
                    v.props.no_on_abort |= src.props.no_on_abort;
                    v.props.once |= src.props.once;
                    v.props.nonportable |= src.props.nonportable;
                }
                CaptureMode::ByRef | CaptureMode::Kept | CaptureMode::Cap => {
                    // A capture of a value that is not `many` (a scope
                    // capability, a `once` closure) makes a closure that is
                    // not `many` (`Lower::closure_not_many`).
                    v.props.once |= src.props.once
                        || self.uniq(d.maker, cap.source.local, cap.mode == CaptureMode::ByRef);
                    v.props.nonportable |= src.props.nonportable;
                }
            }
        }
        v
    }

    /// True if local `l` of body `b` is `@ uniq` (with `by_ref`, a reference
    /// to it is), as `Builder::closure_props` reads it.
    fn uniq(&self, b: BodyId, l: LocalId, by_ref: bool) -> bool {
        let Some(d) = self.p.body(b).and_then(|x| x.locals.get(l.index())) else {
            return false;
        };
        if by_ref {
            self.tys
                .find(&Ty::Ref(d.ty))
                .map_or(d.props.uniq, |r| crate::props::ir_props(self.tys, r).uniq)
        } else {
            d.props.uniq
        }
    }

    /// True if body `b` calls a `once` value: a closure that calls such a
    /// value is `once` too (W0502).
    fn calls_once(&self, b: BodyId) -> bool {
        self.p.body(b).is_some_and(|body| {
            body.blocks.iter().any(|blk| match &blk.term.kind {
                TermKind::Call {
                    callee: Callee::Value(op),
                    ..
                } => self.operand(b, op).props.once,
                _ => false,
            })
        })
    }

    /// The result of a call of body `callee` with the arguments `args` of
    /// body `b`: `_0` of the callee, and the argument for each parameter of
    /// the callee whose value `_0` can be.
    fn call_result(&self, b: BodyId, callee: BodyId, args: &[Operand]) -> Val {
        let r = self.ret_of(callee);
        let mut out = self.subst(b, callee, &r, args);
        out.refs.clear();
        out
    }

    /// The value of `_0` of body `b`.
    fn ret_of(&self, b: BodyId) -> Val {
        self.p
            .body(b)
            .map_or_else(Val::default, |x| self.get(b, x.ret))
    }

    /// The value that a call of a function value with value `callee` and
    /// the arguments `args` of body `b` gives: the result of each closure
    /// body and function body that it can run (`LocalKind::Param(j)` of a
    /// closure body gets argument `j`; the environment is no parameter).
    fn run_result(&self, b: BodyId, callee: &Val, args: &[Operand]) -> Val {
        let mut out = Val::default();
        for c in &callee.closures {
            if let Some(d) = self.p.closures.get(c.index()) {
                out.join(&self.call_result(b, d.body, args));
            }
        }
        for g in &callee.items {
            if let Some(gb) = self.p.fns.get(g.index()).and_then(|d| d.body) {
                out.join(&self.call_result(b, gb, args));
            }
        }
        out
    }
}

/// The properties of the values of a local with declaration `d`: those of
/// its type and those that the builder knows (a closure that it makes, a
/// `multi` continuation, the last round).
const fn decl_props(d: &weft_ir::LocalDecl) -> ValueProps {
    let p = d.props;
    ValueProps {
        linear: p.linear,
        no_on_abort: p.linear && !p.on_abort,
        once: p.once,
        nonportable: p.nonportable,
    }
}

/// The effect of the capability of a perform in body `b`, if the analysis
/// knows it.
fn perform_effect(
    p: &Program,
    tys: &TyTable,
    b: BodyId,
    cap: &weft_ir::CapOperand,
) -> Option<weft_ir::EffectId> {
    match cap {
        weft_ir::CapOperand::Row(e) => Some(*e),
        weft_ir::CapOperand::Local(place) => {
            let body = p.body(b)?;
            let d = body.locals.get(place.local.index())?;
            match tys.try_get(d.ty)? {
                Ty::Cap(e) => Some(*e),
                _ => None,
            }
        }
    }
}

/// The base local of place `p`.
const fn base(p: &Place) -> LocalId {
    p.local
}

/// Runs the analysis on the program `p` with the types `tys` and gives the
/// properties of the bindings of each entry. `bound` holds the local of each
/// binding of each body of each entry.
pub(super) fn infer(
    p: &Program,
    tys: &TyTable,
    bound: &[Vec<(BodyId, BindingId, LocalId)>],
) -> Vec<BindingValues> {
    let f = run(p, tys);
    bound
        .iter()
        .map(|entry| {
            let mut out = BindingValues::new();
            for &(b, binding, l) in entry {
                let v = f.get(b, l).props;
                let x = out.entry(binding).or_default();
                x.linear |= v.linear;
                x.no_on_abort |= v.no_on_abort;
                x.once |= v.once;
                x.nonportable |= v.nonportable;
            }
            out
        })
        .collect()
}

/// Runs the analysis on the program `p` with the types `tys` to its
/// fixpoint.
fn run<'a>(p: &'a Program, tys: &'a TyTable) -> Flow<'a> {
    let mut f = Flow {
        p,
        tys,
        vals: HashMap::new(),
        writes: HashMap::new(),
        grew: true,
    };
    for (i, body) in p.bodies.iter().enumerate() {
        let b = BodyId(super::id_of(i));
        for (j, d) in body.locals.iter().enumerate() {
            let mut v = Val {
                props: decl_props(d),
                ..Val::default()
            };
            if let LocalKind::Param(k) = d.kind {
                v.params.insert((b, k as usize));
            }
            f.put(b, LocalId(super::id_of(j)), &v);
        }
    }
    // The clauses of each effect and operation.
    let mut clauses: HashMap<(weft_ir::EffectId, u32), Vec<BodyId>> = HashMap::new();
    for h in &p.handlers {
        for &(op, cb) in &h.clauses {
            clauses.entry((h.effect, op.0)).or_default().push(cb);
        }
    }
    // Each pass looks at each statement and each terminator; the values
    // only grow, and each one is finite.
    let mut passes = 0usize;
    while f.grew && passes <= p.bodies.len().saturating_mul(8).saturating_add(64) {
        f.grew = false;
        passes += 1;
        for i in 0..p.bodies.len() {
            let b = BodyId(super::id_of(i));
            pass_body(&mut f, b, &clauses);
        }
    }
    f
}

/// True if the declared type of field `k` of the struct or of variant `v`
/// of the enum of type `t` is a function type.
fn declared_fn_field(tys: &TyTable, t: weft_ir::TyId, v: Option<usize>, k: usize) -> bool {
    let Some(Ty::Adt(a, _)) = tys.try_get(t) else {
        return false;
    };
    let Some(d) = tys.adts().get(a.index()) else {
        return false;
    };
    let ft = match (&d.kind, v) {
        (weft_ir::ty::AdtKind::Struct(fs), None) => fs.get(k).map(|f| f.ty),
        (weft_ir::ty::AdtKind::Enum(vs), Some(v)) => {
            vs.get(v).and_then(|x| x.fields.get(k)).copied()
        }
        _ => None,
    };
    ft.is_some_and(|ft| matches!(tys.try_get(ft), Some(Ty::Fn(_))))
}

/// The type of place `q` of a local of type `t`, and true if its last
/// projection is a field whose declared type is a function type (a place of
/// plain data that does not show a closure).
fn declared_fn_place(tys: &TyTable, t: weft_ir::TyId, q: &Place) -> bool {
    let mut t = t;
    let mut variant: Option<usize> = None;
    let mut last = false;
    for pr in &q.proj {
        last = false;
        let Some(ty) = tys.try_get(t) else {
            return false;
        };
        match (pr, ty) {
            (weft_ir::Proj::Deref(_), Ty::Ref(x)) => t = *x,
            (weft_ir::Proj::Deref(_), Ty::Adt(_, args)) if args.len() == 1 => {
                t = args[0];
            }
            (weft_ir::Proj::Variant(v), Ty::Adt(..)) => variant = Some(v.index()),
            (weft_ir::Proj::Field(k), Ty::Adt(a, args)) => {
                last = declared_fn_field(tys, t, variant, k.index());
                let Some(d) = tys.adts().get(a.index()) else {
                    return false;
                };
                let ft = match (&d.kind, variant) {
                    (weft_ir::ty::AdtKind::Struct(fs), None) => fs.get(k.index()).map(|f| f.ty),
                    (weft_ir::ty::AdtKind::Enum(vs), Some(v)) => {
                        vs.get(v).and_then(|x| x.fields.get(k.index())).copied()
                    }
                    _ => None,
                };
                let Some(ft) = ft else {
                    return false;
                };
                // A field of a type parameter: the type of the place is
                // the type argument.
                t = match tys.try_get(ft) {
                    Some(Ty::Param(j)) => match args.get(*j as usize) {
                        Some(&x) => x,
                        None => return false,
                    },
                    _ if args.is_empty() => ft,
                    _ => return last,
                };
                variant = None;
            }
            (weft_ir::Proj::Field(k), Ty::Tuple(ts)) => match ts.get(k.index()) {
                Some(&x) => t = x,
                None => return false,
            },
            _ => return false,
        }
    }
    last
}

/// W0502 of a `once` closure that goes into a place of plain data (as
/// `Lower::keep_modes` of the old lowering, plan stage R0i-b): a closure
/// that moves a capture that is not plain data (`ClosureDecl::once`) runs
/// only once, and a copy of a place of a stated function type could call it
/// again. A type that the analysis infers from the closure shows the
/// closure (the old lowering keeps its summary in the type), so only these
/// places count:
///
/// - a field of a struct or of a variant literal whose declared type is a
///   function type;
/// - the place of an assignment whose last projection is such a field;
/// - an argument of a function item whose parameter type is not a function
///   type (the callee can keep it: `v.push(..)`), if another argument is a
///   place of a stated type that has a function part: a parameter, a `let`
///   binding with a stated type (`stated`), a field.
///
/// Each one gives the location of the operand (the expression of its
/// temporary, else of the statement) and the type of the value.
pub(super) fn once_into_plain(
    p: &Program,
    tys: &TyTable,
    stated: &[(BodyId, LocalId)],
) -> Vec<(weft_ir::Span, weft_ir::TyId)> {
    let f = run(p, tys);
    let stated: BTreeSet<(BodyId, LocalId)> = stated.iter().copied().collect();
    // A linear closure goes there with no W0502: the facts give W0601 if
    // it can go away there (`Lower::keep_modes`).
    let moving = |b: BodyId, op: &Operand| {
        f.operand(b, op).closures.iter().any(|&c| {
            p.closures.get(c.index()).is_some_and(|d| d.once) && !f.closure(c).props.linear
        })
    };
    let mut out = Vec::new();
    for (i, body) in p.bodies.iter().enumerate() {
        let b = BodyId(super::id_of(i));
        let local = |l: LocalId| body.locals.get(l.index());
        // The location and the type of operand `op` at origin `at`: the
        // origin of its temporary, else `at`. Only a value of a function
        // type is a closure here.
        let place_of = |op: &Operand, at: weft_ir::Span| {
            op.place()
                .and_then(|q| local(q.local))
                .filter(|d| matches!(tys.try_get(d.ty), Some(Ty::Fn(_))))
                .map(|d| {
                    let span = if matches!(d.kind, LocalKind::Temp(_)) {
                        d.origin.span
                    } else {
                        at
                    };
                    (span, d.ty)
                })
        };
        // The places that a reference temporary points to.
        let mut ref_of: HashMap<LocalId, Place> = HashMap::new();
        for blk in &body.blocks {
            for st in &blk.stmts {
                if let StmtKind::Assign(dst, Rvalue::Ref(q)) = &st.kind {
                    if dst.proj.is_empty() {
                        ref_of.insert(dst.local, q.clone());
                    }
                }
            }
        }
        // True if operand `op` is (a reference to) a place of a stated type
        // with a function part.
        let stated_place = |op: &Operand| {
            let Some(q) = op.place() else {
                return false;
            };
            let q = match local(q.local).map(|d| d.kind) {
                Some(LocalKind::Temp(_)) if q.proj.is_empty() => match ref_of.get(&q.local) {
                    Some(r) => r,
                    None => return false,
                },
                _ => q,
            };
            let Some(d) = local(q.local) else {
                return false;
            };
            if !crate::props::ir_has_fns(tys, d.ty) {
                return false;
            }
            // An upvar local is the local of its parent body.
            let (mut ob, mut ol, mut kind) = (b, q.local, d.kind);
            for _ in 0..p.bodies.len() {
                let LocalKind::Upvar(pl) = kind else {
                    break;
                };
                let Some(parent) = p.body(ob).and_then(|x| x.parent) else {
                    break;
                };
                let Some(pd) = p.body(parent).and_then(|x| x.locals.get(pl.index())) else {
                    break;
                };
                (ob, ol, kind) = (parent, pl, pd.kind);
            }
            match kind {
                // A capture of a closure: its type is the type of the
                // variable of the maker.
                LocalKind::Env => false,
                LocalKind::Param(_) => true,
                _ => !q.proj.is_empty() || stated.contains(&(ob, ol)),
            }
        };
        for blk in &body.blocks {
            for st in &blk.stmts {
                let StmtKind::Assign(dst, rv) = &st.kind else {
                    continue;
                };
                match rv {
                    Rvalue::Aggregate(AggKind::Struct(t), ops) => {
                        for (k, op) in ops.iter().enumerate() {
                            if declared_fn_field(tys, *t, None, k) && moving(b, op) {
                                out.extend(place_of(op, st.origin.span));
                            }
                        }
                    }
                    Rvalue::Aggregate(AggKind::Variant(t, v), ops) => {
                        for (k, op) in ops.iter().enumerate() {
                            if declared_fn_field(tys, *t, Some(v.index()), k) && moving(b, op) {
                                out.extend(place_of(op, st.origin.span));
                            }
                        }
                    }
                    Rvalue::Use(op) if !dst.proj.is_empty() => {
                        let fits =
                            local(dst.local).is_some_and(|d| declared_fn_place(tys, d.ty, dst));
                        if fits && moving(b, op) {
                            out.extend(place_of(op, st.origin.span));
                        }
                    }
                    _ => {}
                }
            }
            if let TermKind::Call {
                callee: Callee::Fn(g, _),
                args,
                ..
            } = &blk.term.kind
            {
                let Some(decl) = p.fns.get(g.index()) else {
                    continue;
                };
                for (j, a) in args.iter().enumerate() {
                    let callback = decl
                        .params
                        .get(j)
                        .is_some_and(|&t| matches!(tys.try_get(t), Some(Ty::Fn(_))));
                    let into = args
                        .iter()
                        .enumerate()
                        .any(|(k, x)| k != j && stated_place(x));
                    if !callback && into && moving(b, a) {
                        out.extend(place_of(a, blk.term.origin.span));
                    }
                }
            }
        }
    }
    out.sort_by_key(|(s, _)| (s.unit, s.lo, s.hi));
    out.dedup_by_key(|(s, _)| (s.unit, s.lo, s.hi));
    out
}

/// One pass of the analysis over body `b`.
fn pass_body(
    f: &mut Flow<'_>,
    b: BodyId,
    clauses: &HashMap<(weft_ir::EffectId, u32), Vec<BodyId>>,
) {
    let p = f.p;
    let Some(body) = p.body(b) else {
        return;
    };
    // An upvar local and its local in the parent share their values.
    if let Some(parent) = body.parent {
        for (j, d) in body.locals.iter().enumerate() {
            if let LocalKind::Upvar(pl) = d.kind {
                let l = LocalId(super::id_of(j));
                let here = f.get(b, l);
                let there = f.get(parent, pl);
                f.put(b, l, &there);
                f.put(parent, pl, &here);
            }
        }
    }
    // The environment of a closure body holds the captures of each closure
    // value of the body.
    if let (Some((_, d)), Some(&env)) = (p.closure_of(b), body.params.first()) {
        let mut v = Val::default();
        for cap in &d.captures {
            v.join(&f.get(d.maker, cap.source.local));
        }
        f.put(b, env, &v);
    }
    for blk in &body.blocks {
        for s in &blk.stmts {
            if let StmtKind::Assign(dst, rv) = &s.kind {
                let v = match rv {
                    Rvalue::Use(op) => f.operand(b, op),
                    Rvalue::Ref(q) => {
                        let mut v = f.get(b, base(q));
                        // A reference to a place behind a reference points
                        // where that reference points (`&(*ks)`): its value
                        // keeps those referents. Else it points to the local.
                        let through = q.proj.iter().any(|x| matches!(x, weft_ir::Proj::Deref(_)));
                        if !through {
                            v.refs.insert((b, base(q)));
                        }
                        v
                    }
                    Rvalue::Aggregate(AggKind::Closure(c), _) => f.closure(*c),
                    Rvalue::Aggregate(_, ops) => {
                        let mut v = Val::default();
                        for op in ops {
                            v.join(&f.operand(b, op));
                        }
                        v
                    }
                    Rvalue::Iter(IterSource::Elems(q)) => f.get(b, base(q)),
                    _ => continue,
                };
                let behind = dst.proj.iter().any(|x| {
                    matches!(
                        x,
                        weft_ir::Proj::Deref(weft_ir::DerefKind::Ref | weft_ir::DerefKind::Rc)
                    )
                });
                if behind {
                    // A write behind a reference or into an `rc` object
                    // reaches each local that points to the object.
                    let r = f.get(b, base(dst));
                    f.write_through(&r, &v);
                }
                f.put(b, base(dst), &v);
            }
        }
        match &blk.term.kind {
            TermKind::Call {
                callee, args, dest, ..
            } => {
                if let Callee::Fn(g, _) = callee {
                    if let Some(d) = p.fns.get(g.index()) {
                        f.call_writes(b, d.body, args);
                    }
                }
                let v = match callee {
                    Callee::Fn(g, _) => {
                        if let Some(gb) = p.fns.get(g.index()).and_then(|d| d.body) {
                            f.call_result(b, gb, args)
                        } else {
                            // A function with no body (`Rc.clone`, `v.get`):
                            // its result can be a part of an argument, also
                            // an `rc` handle of the same object.
                            let fns = body
                                .locals
                                .get(dest.local.index())
                                .is_some_and(|d| crate::props::ir_has_fns(f.tys, d.ty));
                            let mut v = Val::default();
                            if fns && dest.proj.is_empty() {
                                for a in args {
                                    v.join(&f.operand(b, a));
                                }
                                v.params.clear();
                            }
                            v
                        }
                    }
                    Callee::Value(op) => {
                        let c = f.operand(b, op);
                        f.run_result(b, &c, args)
                    }
                };
                f.put(b, base(dest), &v);
            }
            TermKind::Perform {
                cap,
                op,
                args,
                dest,
                ..
            } => {
                let Some(e) = perform_effect(p, f.tys, b, cap) else {
                    continue;
                };
                for &cb in clauses.get(&(e, op.0)).into_iter().flatten() {
                    let Some(cbody) = p.body(cb) else {
                        continue;
                    };
                    for (k, a) in args.iter().enumerate() {
                        if let Some(&pl) = cbody.params.get(k) {
                            let v = f.operand(b, a);
                            f.put(cb, pl, &v);
                        }
                    }
                    let given = resumed(f, cb);
                    f.put(b, base(dest), &given);
                }
            }
            TermKind::Handle { handler, dest, .. } => {
                if let Some(h) = p.handlers.get(handler.index()) {
                    let mut v = f.ret_of(h.handled);
                    for &(_, cb) in &h.clauses {
                        v.join(&f.ret_of(cb));
                    }
                    f.put(b, base(dest), &v);
                }
            }
            TermKind::Scope { scope, dest, .. } => {
                if let Some(s) = p.scopes.get(scope.index()) {
                    let v = f.ret_of(s.body);
                    f.put(b, base(dest), &v);
                }
            }
            TermKind::IterNext { iter, dest, .. } => {
                let v = f.get(b, base(iter));
                f.put(b, base(dest), &v);
            }
            _ => {}
        }
    }
}

/// The values that clause body `cb` gives to `resume`.
fn resumed(f: &Flow<'_>, cb: BodyId) -> Val {
    let mut out = Val::default();
    let Some(body) = f.p.body(cb) else {
        return out;
    };
    for blk in &body.blocks {
        if let TermKind::Resume { arg, .. } = &blk.term.kind {
            out.join(&f.operand(cb, arg));
        }
    }
    out
}

/// W0303 of a copy of a function value out of a place behind a reference or
/// an `rc` object (`reads`, `Decls::fn_reads`) whose value can be a closure
/// that moves a capture (`ClosureDecl::once`), and whose type does not come
/// from a declared function type: such a closure is no plain data, so the
/// read moves it out of the borrowed place, as the old lowering says (plan
/// stage R0i-b). Each one gives the location, its unit and the
/// type.
pub(super) fn once_reads(
    p: &Program,
    tys: &TyTable,
    reads: &[super::FnRead],
) -> Vec<(weft_syntax::ast::Span, u32, weft_ir::TyId)> {
    if reads.is_empty() {
        return Vec::new();
    }
    let f = run(p, tys);
    let mut out: Vec<(weft_syntax::ast::Span, u32, weft_ir::TyId)> = reads
        .iter()
        .filter(|(b, q, ..)| {
            // A field of a declared function type is plain data: the type
            // does not show the closure (`h.f` of `struct Hook { f: fn() }`).
            let declared = p
                .body(*b)
                .and_then(|x| x.locals.get(q.local.index()))
                .is_some_and(|d| declared_fn_place(tys, d.ty, q));
            !declared
                && f.get(*b, q.local)
                    .closures
                    .iter()
                    .any(|c| p.closures.get(c.index()).is_some_and(|d| d.once))
        })
        .map(|&(_, _, span, unit, ty)| (span, unit, ty))
        .collect();
    out.sort_by_key(|(s, u, _)| (*u, s.lo, s.hi));
    out.dedup_by_key(|(s, u, _)| (*u, s.lo, s.hi));
    out
}
