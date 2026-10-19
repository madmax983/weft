//! Linear values that go away: a pattern `_`, a value that nothing keeps, and a
//! place whose type does not keep the value linear.
//!
//! A dropped linear value gets a hidden variable that goes out of scope where
//! the value goes away. The rule `unconsumed(V, P)` then reports it (W0601).

use super::{ast, AdtKind, Lower, Pattern, Span, Ty, Val, VarKind};

impl Lower<'_> {
    /// A linear value of type `ty` goes away at `span`. `name` names it in the
    /// diagnostic.
    pub(super) fn drop_linear(&mut self, name: &str, ty: &Ty, span: Span) {
        if self.cur.is_none() {
            return;
        }
        let info = self.var_info(name, VarKind::Temp, span, ty, false);
        let var = self.facts.add_var(info);
        let n = self.emit(span, "drop", String::new());
        self.bind(var, n);
        let d = self.emit(span, "drop", String::new());
        self.facts.scope_end.push((var, d));
    }

    /// Returns the by-value parameters of a type parameter that the body can drop:
    /// a path from `entry` to `exit` does not move them. The body does not know
    /// that a caller can give a linear value there, so the caller checks it.
    pub(super) fn param_drops(
        &self,
        sig: &crate::program::FnSig,
        params: &[usize],
        entry: super::NodeId,
        exit: super::NodeId,
    ) -> std::collections::BTreeSet<usize> {
        let mut out = std::collections::BTreeSet::new();
        let n = self.facts.nodes.len();
        let mut succ = vec![Vec::new(); n];
        for &(a, b) in &self.facts.cfg_edge {
            succ[a.index()].push(b.index());
        }
        for (i, p) in sig.params.iter().enumerate() {
            if !super::flow::mentions_param(&p.ty) || p.ty.is_ref() {
                continue;
            }
            let Some(&l) = params.get(i) else { continue };
            let var = self.locals[l].var;
            // A callee that can drop the value drops it here.
            if self.generic_drops.contains(&var) {
                out.insert(i);
                continue;
            }
            let mut moved = vec![false; n];
            for &(v, at) in &self.facts.moved_at {
                if v == var {
                    moved[at.index()] = true;
                }
            }
            let mut seen = vec![false; n];
            let mut work = vec![entry.index()];
            while let Some(a) = work.pop() {
                if std::mem::replace(&mut seen[a], true) || moved[a] {
                    continue;
                }
                work.extend(succ[a].iter().copied());
            }
            if seen[exit.index()] {
                out.insert(i);
            }
        }
        out
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
    /// type is not, the value can go away there unseen: for example a closure that
    /// moves a linear value, in a field of type `fn()` (W0601). A closure that runs
    /// only once cannot go into a place of plain data: a copy of the place could
    /// call it again (W0502).
    pub(super) fn keep_modes(&mut self, v: &Val, into: &Ty, span: Span) {
        if self.is_linear(&v.ty) && !self.is_linear(into) {
            let name = self.val_name(v);
            self.drop_linear(&name, &v.ty, span);
        } else if let Some(s) = self.fn_info(v).summary {
            if self.closure_is_once(s) && self.is_copy(into) {
                let shown = self.show(into);
                self.err(
                    "W0502",
                    format!("a `once` closure cannot go into a place of type `{shown}`: a copy of the place could call it again"),
                    span,
                );
            }
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
    /// An arm that takes nothing and matches a value with no linear part, such
    /// as `None`, consumes a local scrutinee: nothing linear is left in it.
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
                if self.is_linear(ty) {
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
            AdtKind::Enum(vs) => vs
                .iter()
                .find(|v| v.name == name.name)
                .map(|v| v.fields.iter().map(|t| super::subst(t, &args)).collect())
                .unwrap_or_default(),
            AdtKind::Struct(fs) => fs.iter().map(|f| super::subst(&f.ty, &args)).collect(),
            AdtKind::Extern { .. } => Vec::new(),
        }
    }
}
