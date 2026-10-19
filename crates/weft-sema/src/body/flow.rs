//! References inside values: where a reference goes when it is inside a value
//! of another type, such as `Option<&T>`, `Vec<&T>` or a generic struct.
//!
//! A value points where its parts point. A local that holds such a value points
//! into the places of its references (`points_into`), so a mutation of these
//! places invalidates the local. A reference that comes out of the value again,
//! through a pattern, an element or a call, points into the same places.

use super::{Lower, PlaceId, Ty};

impl Lower<'_> {
    /// Returns a new instance of one-place wildcard places for the result of a
    /// call, if the result is one reference: a `&T` or an `Option<&T>` where `T`
    /// holds no reference. The call must be in the body of the function, not in
    /// a closure or a clause, which can run more than once with one lowering. A
    /// loop lowers its body again, with new instances, so a result of an
    /// iteration before has another instance (`stmt::lower_loop`).
    pub(super) fn one_result(&mut self, ret: &Ty) -> Option<u32> {
        let one = |me: &Self, t: &Ty| match me.inf.shallow(t) {
            Ty::Ref(inner) => !me.holds_refs(&inner),
            _ => false,
        };
        let single = match self.inf.shallow(ret) {
            Ty::Adt(a, args) if Some(a) == self.b.option => {
                args.first().is_some_and(|t| one(self, t))
            }
            t => one(self, &t),
        };
        (single && self.scope_now() == super::fnval::Scope::Function).then(|| self.fresh_split())
    }

    /// Returns the places that the values at places `ps` point into: the
    /// references that the locals and the temporaries at these places hold. The
    /// read uses these locals, so a reference in them that is not valid is an
    /// error. A place behind a reference parameter of the function holds
    /// references that the caller gives. They point anywhere into the root of
    /// what they point into (`held_root`, ADR 0003).
    pub(super) fn held_refs(&mut self, ps: &[PlaceId]) -> Vec<PlaceId> {
        let mut out = Vec::new();
        for &p in ps {
            let root = self.facts.place(p).root;
            match self.root_owner(root) {
                // Reading the references uses the local that holds them.
                Some(l) => {
                    out.extend(self.locals[l].refs.iter().copied());
                    for h in self.part_holders.iter().filter(|h| h.local == l) {
                        out.extend(h.refs.iter().copied());
                    }
                    self.use_local(l);
                }
                None => {
                    if let Some(rs) = self.temp_refs.get(&root) {
                        out.extend(rs.iter().copied());
                    } else if let Some(&(0, i)) = self.param_of_root.get(&root) {
                        // Only a pointee that can hold references has a root for them.
                        if self.param_points_to_refs(i) {
                            let h = self.held_root(i);
                            out.push(self.facts.wildcard(h));
                        }
                    } else if let Some(&i) = self.held_of.get(&root) {
                        // A reference behind a stored reference: also the caller's.
                        let h = self.held_root(i);
                        out.push(self.facts.wildcard(h));
                    }
                }
            }
        }
        out.sort();
        out.dedup();
        out
    }

    /// Returns true if the value behind a reference, of type `t`, can hold a
    /// reference. The value behind a slice reference is its elements.
    pub(super) fn pointee_refs(&self, t: &Ty) -> bool {
        match self.inf.shallow(t) {
            Ty::Slice(x) => self.holds_refs(&x),
            t => self.holds_refs(&t),
        }
    }

    /// Returns true if reference parameter `i` of the function points to a value
    /// that can hold a reference.
    pub(super) fn param_points_to_refs(&self, i: usize) -> bool {
        let Some(p) = self.self_fn.and_then(|f| self.sigs[f].params.get(i)) else {
            return false;
        };
        match &p.ty {
            Ty::Ref(inner) => self.pointee_refs(inner),
            _ => false,
        }
    }

    /// Returns the root place of what the references behind reference parameter
    /// `i` of the function point into. A caller puts in the places that the
    /// references in its argument point into (`SigStep::Held`).
    pub(super) fn held_root(&mut self, i: usize) -> PlaceId {
        if let Some(&r) = self.held_roots.get(&i) {
            return r;
        }
        let name = self
            .self_fn
            .and_then(|f| self.sigs[f].params.get(i))
            .map_or_else(|| "parameter".to_string(), |p| format!("*{}", p.name));
        let r = self.facts.add_root(name, super::RootKind::Param);
        self.held_roots.insert(i, r);
        let id = self.facts.place(r).root;
        self.held_of.insert(id, i);
        r
    }

    /// Returns the places that an argument with places `refs` can give to the
    /// result of a call or to another argument. `declared` is the type of the
    /// parameter in the signature. With `reach`, a parameter with a reference
    /// type lets the callee make a reference to any place inside the argument.
    /// A by-value parameter of a type parameter passes the value on as it is. `pointee`
    /// is the type behind a reference argument: if it holds references, the
    /// callee can read them too. With `one`, the place inside the argument is
    /// the one-place wildcard place of that instance (`Lower::one_result`).
    pub(super) fn flow_refs(
        &mut self,
        declared: &Ty,
        refs: &[PlaceId],
        pointee: Option<&Ty>,
        reach: bool,
        one: Option<u32>,
    ) -> Vec<PlaceId> {
        let (named, deps) = self.split_deps(refs);
        let mut out = Vec::new();
        if reach && self.holds_refs(declared) {
            for &p in &named {
                out.push(match one {
                    Some(k) => self.facts.wildcard_one(p, k),
                    None => self.facts.wildcard(p),
                });
            }
            out.extend(deps);
        } else if !declared.is_ref() && mentions_param(declared) {
            out.extend(refs.iter().copied());
        }
        if pointee.is_some_and(|t| self.pointee_refs(t)) {
            out.extend(self.held_refs(&named));
        }
        out.sort();
        out.dedup();
        out
    }
}

impl Lower<'_> {
    /// Returns true if a by-value parameter of type `t` holds references that
    /// point into places of the caller, such as an `Option<&T>`. A function
    /// value has its own places, and a type parameter hides what it holds.
    pub(super) fn byval_refs(&self, t: &Ty) -> bool {
        !t.is_ref() && !matches!(t, Ty::Fn(_)) && self.holds_refs(t)
    }
}

/// Returns true if type `t` names a type parameter.
pub(super) fn mentions_param(t: &Ty) -> bool {
    match t {
        Ty::Param(_) => true,
        Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().any(mentions_param),
        Ty::Ref(x) | Ty::Slice(x) | Ty::Array(x, _) => mentions_param(x),
        Ty::Cont(a, b) => mentions_param(a) || mentions_param(b),
        Ty::Fn(f) => f.params.iter().any(mentions_param) || mentions_param(&f.ret),
        _ => false,
    }
}

/// Returns true if type `t` names type parameter `j`.
pub(super) fn mentions(t: &Ty, j: u32) -> bool {
    match t {
        Ty::Param(i) => *i == j,
        Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().any(|x| mentions(x, j)),
        Ty::Ref(x) | Ty::Slice(x) | Ty::Array(x, _) => mentions(x, j),
        Ty::Cont(a, b) => mentions(a, j) || mentions(b, j),
        Ty::Fn(f) => f.params.iter().any(|x| mentions(x, j)) || mentions(&f.ret, j),
        _ => false,
    }
}

/// Returns the number of reference types in type `t`.
pub(super) fn count_refs(t: &Ty) -> usize {
    match t {
        Ty::Ref(x) => 1 + count_refs(x),
        Ty::Tuple(ts) | Ty::Adt(_, ts) => ts.iter().map(count_refs).sum(),
        Ty::Slice(x) | Ty::Array(x, _) => count_refs(x),
        _ => 0,
    }
}
