//! References inside values: where a reference goes when it is inside a value
//! of another type, such as `Option<&T>`, `Vec<&T>` or a generic struct.
//!
//! A value points where its parts point. A local that holds such a value points
//! into the places of its references (`points_into`), so a mutation of these
//! places invalidates the local. A reference that comes out of the value again,
//! through a pattern, an element or a call, points into the same places.

use super::{Lower, PlaceId, Ty};

impl Lower<'_> {
    /// Returns the places that the values at places `ps` point into: the
    /// references that the locals and the temporaries at these places hold. The
    /// read uses these locals, so a reference in them that is not valid is an
    /// error. A place behind a reference parameter holds references that this
    /// body cannot name: it adds nothing (ADR 0003).
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
                    }
                }
            }
        }
        out.sort();
        out.dedup();
        out
    }

    /// Returns the places that an argument with places `refs` can give to the
    /// result of a call or to another argument. `declared` is the type of the
    /// parameter in the signature. With `reach`, a parameter with a reference
    /// type lets the callee make a reference to any place inside the argument.
    /// A by-value parameter of a type parameter passes the value on as it is. `pointee`
    /// is the type behind a reference argument: if it holds references, the
    /// callee can read them too.
    pub(super) fn flow_refs(
        &mut self,
        declared: &Ty,
        refs: &[PlaceId],
        pointee: Option<&Ty>,
        reach: bool,
    ) -> Vec<PlaceId> {
        let (named, deps) = self.split_deps(refs);
        let mut out = Vec::new();
        if reach && self.holds_refs(declared) {
            for &p in &named {
                out.push(self.facts.wildcard(p));
            }
            out.extend(deps);
        } else if !declared.is_ref() && mentions_param(declared) {
            out.extend(refs.iter().copied());
        }
        if pointee.is_some_and(|t| self.holds_refs(t)) {
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
