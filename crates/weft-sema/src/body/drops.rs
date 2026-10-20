//! Linear values that go away: a pattern `_`, a value that nothing keeps, and a
//! place whose type does not keep the value linear.
//!
//! A dropped linear value gets a hidden variable that goes out of scope where
//! the value goes away. The rule `unconsumed(V, P)` then reports it (W0601).

use std::collections::{BTreeMap, BTreeSet};
use weft_syntax::diag::Code;

use weft_facts::{Step, StepKind};

use super::{ast, subst, AdtKind, FnId, Lower, Pattern, Span, Ty, Val, VarId, VarKind};

impl Lower<'_> {
    /// A linear value of type `ty` goes away at `span`. `name` names it in the
    /// diagnostic.
    pub(super) fn drop_linear(&mut self, name: &str, ty: &Ty, span: Span) {
        self.drop_linear_as(name, VarKind::Temp, ty, span);
    }

    /// A linear value of type `ty` goes away at `span`, in a hidden variable of
    /// kind `kind`.
    pub(super) fn drop_linear_as(&mut self, name: &str, kind: VarKind, ty: &Ty, span: Span) {
        if self.cur.is_none() {
            return;
        }
        let info = self.var_info(name, kind, span, ty, false);
        let var = self.new_var(info, ty);
        let n = self.emit(span, "drop", String::new());
        self.bind(var, n);
        let d = self.emit(span, "drop", String::new());
        self.facts.scope_end.push((var, d));
    }

    /// Generic function item `f` is a value here, with the type arguments `targs`.
    /// Code that the body does not follow can call it, so the checks of a call of
    /// `f` apply here (`hold_generic`, `callee_drops`). A type argument in `holds`
    /// gets a hidden variable across a node of its own. That node can abort or
    /// resume more than once, as `f` can (W0602, W0503). A type argument in
    /// `drops` gets a value that goes away (W0601). `finish` decides from the
    /// inferred types. The node is in a part of the graph of its own: no other
    /// value is live there.
    pub(super) fn check_item_value(&mut self, f: FnId, targs: &[Ty], span: Span) {
        let sigs = self.sigs;
        let sig = &sigs[f];
        if self.cur.is_none() || (sig.effects.holds.is_empty() && sig.effects.drops.is_empty()) {
            return;
        }
        let name = self.prog.fns[f].name.clone();
        let abort = !sig.effects.named.is_empty() || !sig.effects.passthrough.is_empty();
        let multi = sig.effects.multi || sig.effects.named.iter().any(|e| self.effect_has_multi(e));
        let saved = self.cur;
        let pending = self.take_pending();
        for &j in &sig.effects.holds {
            let Some(t) = targs.get(j).cloned() else {
                continue;
            };
            if !self.may_be_linear(&t) || !(abort || multi) {
                continue;
            }
            let shown = sig.generics.get(j).cloned().unwrap_or_default();
            let info = self.var_info(&shown, VarKind::Temp, span, &t, false);
            let var = self.new_var(info, &t);
            let b = self.start(span, "held by the callee");
            self.bind(var, b);
            let a = self.emit(span, &name, "a generic function used as a value".into());
            if abort {
                self.facts.may_abort.push(a);
            }
            if multi {
                self.facts.multi_at.push(a);
            }
            let r = self.emit(span, "given back by the callee", String::new());
            self.facts.uses.push((var, r));
            self.facts.moved_at.push((var, r));
        }
        for &j in &sig.effects.drops {
            let Some(t) = targs.get(j).cloned() else {
                continue;
            };
            if !self.may_be_linear(&t) {
                continue;
            }
            // The diagnostic names the item and the type argument.
            let _ = self.start(span, &name);
            self.drop_linear_as(&name, VarKind::Dropped, &t, span);
        }
        self.cur = saved;
        self.restore_pending(pending);
    }

    /// Returns the type parameters of the values that a generic body can drop.
    /// Each variable of `vars` is linear only because a type parameter can be.
    /// The rules of W0601 find a drop: the value is live where its variable goes
    /// out of scope, or where it gets a new value. The type parameters of its
    /// type are then in `drops`. The callers check them (`call_fn_as`).
    pub(super) fn dropped_params(&self, vars: &[(VarId, Ty)]) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        if vars.is_empty() {
            return out;
        }
        let n = self.facts.nodes.len();
        let mut succ = vec![Vec::new(); n];
        for &(a, b) in &self.facts.cfg_edge {
            succ[a.index()].push(b.index());
        }
        let wanted: BTreeSet<VarId> = vars.iter().map(|(v, _)| *v).collect();
        // The nodes of each variable: where it gets a value, where it moves,
        // and where its value can go away.
        let mut binds: BTreeMap<VarId, Vec<usize>> = BTreeMap::new();
        let mut moves: BTreeMap<VarId, BTreeSet<usize>> = BTreeMap::new();
        let mut ends: BTreeMap<VarId, BTreeSet<usize>> = BTreeMap::new();
        let empty: BTreeSet<(VarId, super::NodeId)> = self.facts.empty_at.iter().copied().collect();
        for &(v, p) in &self.facts.rebound_at {
            if wanted.contains(&v) {
                // A new value with no linear part has nothing to drop.
                if !empty.contains(&(v, p)) {
                    binds.entry(v).or_default().push(p.index());
                }
                ends.entry(v).or_default().insert(p.index());
            }
        }
        for &(v, p) in &self.facts.overwrites {
            if wanted.contains(&v) {
                binds.entry(v).or_default().push(p.index());
            }
        }
        // A move of a part that leaves a linear part does not end the value
        // (`ends_linear`).
        let rest: BTreeSet<(VarId, super::NodeId)> =
            self.facts.rest_linear.iter().copied().collect();
        for &(v, p) in &self.facts.moved_at {
            if wanted.contains(&v) && !rest.contains(&(v, p)) {
                moves.entry(v).or_default().insert(p.index());
            }
        }
        for &(v, p) in self.facts.scope_end.iter().chain(&self.facts.overwrites) {
            if wanted.contains(&v) {
                ends.entry(v).or_default().insert(p.index());
            }
        }
        let empty = BTreeSet::new();
        for (v, ty) in vars {
            let (mv, end) = (
                moves.get(v).unwrap_or(&empty),
                ends.get(v).unwrap_or(&empty),
            );
            // `live` holds the nodes where the value is live on entry.
            let mut live = vec![false; n];
            let mut work: Vec<usize> = Vec::new();
            for &b in binds.get(v).into_iter().flatten() {
                work.extend(succ[b].iter().copied());
            }
            let mut dropped = false;
            while let Some(a) = work.pop() {
                if std::mem::replace(&mut live[a], true) {
                    continue;
                }
                if end.contains(&a) {
                    dropped = true;
                    break;
                }
                if !mv.contains(&a) {
                    work.extend(succ[a].iter().copied());
                }
            }
            if dropped {
                let mut ps = BTreeSet::new();
                self.ty_params(ty, &mut ps, &mut Vec::new());
                if ps.is_empty() {
                    let all = self.self_fn.map_or(0, |f| self.sigs[f].generics.len());
                    ps.extend(0..all);
                }
                out.extend(ps);
            }
        }
        out
    }

    /// Returns the type parameters of the values that a generic body holds at a
    /// node that can abort or resume more than once. Each variable of `vars` is
    /// linear only because a type parameter can be. Such a value is live from a
    /// new value to a move, as in the rules of W0602 and W0503. A caller that
    /// gives a linear type to one of these type parameters checks the call
    /// (`hold_generic`).
    pub(super) fn held_params(&self, vars: &[(VarId, Ty)]) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        if vars.is_empty() {
            return out;
        }
        let n = self.facts.nodes.len();
        let mut succ = vec![Vec::new(); n];
        for &(a, b) in &self.facts.cfg_edge {
            succ[a.index()].push(b.index());
        }
        let mut risky = vec![false; n];
        for p in self.facts.may_abort.iter().chain(&self.facts.multi_at) {
            risky[p.index()] = true;
        }
        let wanted: BTreeSet<VarId> = vars.iter().map(|(v, _)| *v).collect();
        let mut binds: BTreeMap<VarId, Vec<usize>> = BTreeMap::new();
        let mut moves: BTreeMap<VarId, BTreeSet<usize>> = BTreeMap::new();
        let empty_at: BTreeSet<(VarId, super::NodeId)> =
            self.facts.empty_at.iter().copied().collect();
        for &(v, p) in self.facts.rebound_at.iter().chain(&self.facts.overwrites) {
            if wanted.contains(&v) && !empty_at.contains(&(v, p)) {
                binds.entry(v).or_default().push(p.index());
            }
        }
        let rest: BTreeSet<(VarId, super::NodeId)> =
            self.facts.rest_linear.iter().copied().collect();
        for &(v, p) in &self.facts.moved_at {
            if wanted.contains(&v) && !rest.contains(&(v, p)) {
                moves.entry(v).or_default().insert(p.index());
            }
        }
        let empty = BTreeSet::new();
        for (v, ty) in vars {
            let mv = moves.get(v).unwrap_or(&empty);
            let mut live = vec![false; n];
            let mut work: Vec<usize> = Vec::new();
            for &b in binds.get(v).into_iter().flatten() {
                work.extend(succ[b].iter().copied());
            }
            let mut held = false;
            while let Some(a) = work.pop() {
                if std::mem::replace(&mut live[a], true) {
                    continue;
                }
                if mv.contains(&a) {
                    continue;
                }
                if risky[a] {
                    held = true;
                    break;
                }
                work.extend(succ[a].iter().copied());
            }
            if held {
                let mut ps = BTreeSet::new();
                self.ty_params(ty, &mut ps, &mut Vec::new());
                if ps.is_empty() {
                    let all = self.self_fn.map_or(0, |f| self.sigs[f].generics.len());
                    ps.extend(0..all);
                }
                out.extend(ps);
            }
        }
        out
    }

    /// Adds the type parameters that a value of type `t` can hold. A closure
    /// holds the values that it moves.
    fn ty_params(&self, t: &Ty, out: &mut BTreeSet<usize>, seen: &mut Vec<usize>) {
        match self.inf.shallow(t) {
            Ty::Param(j) => {
                out.insert(j as usize);
            }
            Ty::Adt(_, ts) | Ty::Tuple(ts) => {
                for x in &ts {
                    self.ty_params(x, out, seen);
                }
            }
            Ty::Array(x, _) => self.ty_params(&x, out, seen),
            Ty::Fn(f) => {
                if let Some(s) = f.summary {
                    self.closure_params(s, out, seen);
                }
            }
            _ => {}
        }
    }

    /// Adds the type parameters of the values that closure `s` moves.
    fn closure_params(&self, s: usize, out: &mut BTreeSet<usize>, seen: &mut Vec<usize>) {
        if seen.contains(&s) {
            return;
        }
        seen.push(s);
        for &v in &self.closures[s].moved_captures {
            if let Some(l) = self.local_of(v) {
                self.ty_params(&self.locals[l].ty, out, seen);
                if let Some(ls) = self.locals[l].summary {
                    self.closure_params(ls, out, seen);
                }
            }
        }
    }

    /// A temporary value of type `ty` moves at `span`. A `!Move` value cannot (W0604).
    pub(super) fn move_temp(&mut self, ty: &Ty, span: Span) {
        if self.cur.is_none() {
            return;
        }
        let info = self.var_info("temporary", VarKind::Temp, span, ty, false);
        let var = self.facts.add_var(info);
        let n = self.emit(span, "move", String::new());
        self.facts.moved_at.push((var, n));
    }

    /// Value `v` goes into a place of type `into`. If the value is linear and the
    /// type is not, the value can go away there unseen (W0601). An example is a
    /// closure that moves a linear value, in a field of type `fn()`. A closure that
    /// runs only once cannot go into a place of plain data (W0502). A copy of the
    /// place could call it again.
    pub(super) fn keep_modes(&mut self, v: &Val, into: &Ty, span: Span) {
        if self.is_linear(&v.ty) && !self.is_linear(into) {
            let name = self.val_name(v);
            self.drop_linear(&name, &v.ty, span);
        } else if let Some(s) = self.fn_info(v).summary {
            if self.closure_is_once(s) && self.is_copy(into) {
                let shown = self.show(into);
                self.err(
                    Code::W0502,
                    format!("a `once` closure cannot go into a place of type `{shown}`: a copy of the place could call it again"),
                    span,
                );
            }
        }
    }

    /// Returns true if a value of type `ty` keeps a part that can be linear
    /// after a move of its part at `steps` (review round 3, R3RT1): a part on
    /// another branch of the type, another element of an array or a buffer, a
    /// part of a step that the walk does not know, or the value itself if its
    /// struct or enum is `linear`: the shell stays.
    pub(super) fn rest_linear(&self, ty: &Ty, steps: &[Step]) -> bool {
        let Some((step, rest)) = steps.split_first() else {
            return false;
        };
        let ty = self.inf.shallow(ty);
        let others = |ts: &[Ty], i: usize| {
            ts.iter()
                .enumerate()
                .any(|(j, t)| j != i && self.may_be_linear(t))
        };
        match (&step.kind, &ty) {
            (StepKind::Field { id }, Ty::Tuple(ts)) => {
                let i = *id as usize;
                others(ts, i) || ts.get(i).is_some_and(|t| self.rest_linear(t, rest))
            }
            (StepKind::Field { id }, Ty::Adt(a, args)) => match &self.prog.adts[*a].kind {
                AdtKind::Struct(fields) => {
                    let ts: Vec<Ty> = fields.iter().map(|f| subst(&f.ty, args)).collect();
                    let i = *id as usize;
                    self.prog.adts[*a].linear
                        || others(&ts, i)
                        || ts.get(i).is_some_and(|t| self.rest_linear(t, rest))
                }
                _ => self.may_be_linear(&ty),
            },
            // A value of an enum is one variant: its payload is the rest.
            (StepKind::Variant { id }, Ty::Adt(a, args)) => match &self.prog.adts[*a].kind {
                AdtKind::Enum(vs) => {
                    self.prog.adts[*a].linear
                        || vs.get(*id as usize).is_some_and(|v| {
                            let ts: Vec<Ty> = v.fields.iter().map(|t| subst(t, args)).collect();
                            match ts.as_slice() {
                                [t] => self.rest_linear(t, rest),
                                _ => self.rest_linear(&Ty::Tuple(ts), rest),
                            }
                        })
                }
                _ => self.may_be_linear(&ty),
            },
            // The other elements stay: an array of one element has none.
            (StepKind::Elem, Ty::Array(t, n)) => {
                (*n != 1 && self.may_be_linear(t)) || self.rest_linear(t, rest)
            }
            (StepKind::Elem | StepKind::Deref, Ty::Adt(_, args)) => {
                let inner = args.first().cloned().unwrap_or(Ty::Error);
                let more = matches!(step.kind, StepKind::Elem) && self.may_be_linear(&inner);
                more || self.rest_linear(&inner, rest)
            }
            _ => self.may_be_linear(&ty),
        }
    }

    /// The name of a value in a diagnostic: its local, or `temporary`.
    pub(super) fn val_name(&self, v: &Val) -> String {
        v.local
            .map_or_else(|| "temporary".to_string(), |l| self.locals[l].name.clone())
    }

    /// The linear parts that a `match` arm with pattern `pat` drops, for a
    /// scrutinee `sval` of type `ty`. `moves` is true if the arm takes the value: a
    /// temporary, or a by-value binding. Then each `_` over a linear part drops it.
    /// An arm that takes nothing can match a value with no linear part, such as
    /// `None`. It consumes a local scrutinee: nothing linear is left in it.
    pub(super) fn match_drops(&mut self, pat: &Pattern, ty: &Ty, sval: &Val, moves: bool) {
        if matches!(self.inf.shallow(ty), Ty::Ref(_))
            || sval.place.as_ref().is_some_and(|p| p.through_ref)
        {
            return;
        }
        if moves {
            for (span, t) in self.wild_drops(pat, ty) {
                self.drop_linear("temporary", &t, span);
            }
        } else if sval.var.is_some() && self.is_linear(ty) && !self.pattern_holds_linear(pat, ty) {
            self.consume(sval, pat.span());
        }
    }

    /// Returns the parts that pattern `pat` drops from a value of type `ty`, with
    /// their types: each `_` over a linear part. A variant pattern looks at its
    /// own payload only.
    pub(super) fn wild_drops(&self, pat: &Pattern, ty: &Ty) -> Vec<(Span, Ty)> {
        let mut out = Vec::new();
        self.wild_drops_into(pat, ty, &mut out);
        out
    }

    fn wild_drops_into(&self, pat: &Pattern, ty: &Ty, out: &mut Vec<(Span, Ty)>) {
        match pat {
            Pattern::Wild(span) => {
                if self.may_be_linear(ty) {
                    out.push((*span, ty.clone()));
                }
            }
            Pattern::Bind(_) | Pattern::Lit(..) => {}
            Pattern::Tuple(ps, _) => {
                if let Ty::Tuple(ts) = self.inf.deep(ty) {
                    for (p, t) in ps.iter().zip(&ts) {
                        self.wild_drops_into(p, t, out);
                    }
                }
            }
            Pattern::Variant { path, fields, .. } => {
                for (p, t) in fields.iter().zip(self.payload_tys(path, ty)) {
                    self.wild_drops_into(p, &t, out);
                }
            }
        }
    }

    /// Returns true if a value that pattern `pat` matches, of type `ty`, can hold a
    /// linear part. `None` in place of `Some(t)` holds nothing.
    pub(super) fn pattern_holds_linear(&self, pat: &Pattern, ty: &Ty) -> bool {
        match pat {
            Pattern::Wild(_) | Pattern::Bind(_) => self.is_linear(ty),
            Pattern::Lit(..) => false,
            Pattern::Tuple(ps, _) => match self.inf.deep(ty) {
                Ty::Tuple(ts) => ps
                    .iter()
                    .zip(&ts)
                    .any(|(p, t)| self.pattern_holds_linear(p, t)),
                _ => self.is_linear(ty),
            },
            Pattern::Variant { path, fields, .. } => {
                let tys = self.payload_tys(path, ty);
                if tys.len() != fields.len() {
                    return self.is_linear(ty);
                }
                fields
                    .iter()
                    .zip(&tys)
                    .any(|(p, t)| self.pattern_holds_linear(p, t))
            }
        }
    }

    /// The payload types of the variant or the struct that `path` names, in a
    /// value of type `ty`.
    fn payload_tys(&self, path: &[ast::Ident], ty: &Ty) -> Vec<Ty> {
        let Ty::Adt(a, args) = self.inf.deep(&self.deref_ty(ty)) else {
            return Vec::new();
        };
        let Some(name) = path.last() else {
            return Vec::new();
        };
        match &self.prog.adts[a].kind {
            AdtKind::Enum(vs) => self
                .prog
                .variant_index(a, &name.name)
                .map(|i| {
                    vs[i]
                        .fields
                        .iter()
                        .map(|t| super::subst(t, &args))
                        .collect()
                })
                .unwrap_or_default(),
            AdtKind::Struct(fs) => fs.iter().map(|f| super::subst(&f.ty, &args)).collect(),
            AdtKind::Extern { .. } => Vec::new(),
        }
    }
}
