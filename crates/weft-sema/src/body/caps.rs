//! Capabilities: where a function value that performs through a local handler goes.
//!
//! A handler capability lives only while its handled body runs. A function value
//! that performs through the capability must not leave that body (W0313): not as
//! the result, not through a local outside the body, and not to a place or code
//! that can keep it. A value in a local of the body goes out of scope with it.

use std::collections::BTreeSet;

use super::{CapId, FnId, FnInfo, Lower, PlaceId, RootKind, Span, Summary, Ty, Val};

/// A function value that can live after the node that gives it away.
#[derive(Clone, Debug)]
pub(super) struct Kept {
    /// The capabilities that a call of the value can perform through.
    pub caps: BTreeSet<CapId>,
    /// Where the value goes.
    pub to: KeptTo,
}

/// Where a kept function value goes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum KeptTo {
    /// A place that the body does not follow: a field, an element, a container or
    /// a callee that stores it.
    Stored,
    /// Code that the body does not know: it can keep the value.
    Given,
}

/// The state of a handled body at its start, to find what leaves it.
#[derive(Clone, Copy, Debug)]
pub(super) struct HandleStart {
    /// The number of locals: a local below it is declared outside the body.
    pub locals: usize,
    /// The number of kept values.
    pub kept: usize,
}

impl Lower<'_> {
    /// Returns the capabilities that a call of a function value in `v` can perform
    /// through: of its summary, of its parts, and of the closures in its type.
    pub(super) fn val_caps(&self, v: &Val) -> BTreeSet<CapId> {
        let mut out = v.caps.clone();
        if let Some(s) = self.fn_info(v).summary {
            out.extend(self.closures[s].performs.iter().copied());
            // A closure can call or return what it captures.
            for &c in &self.closures[s].captures {
                if let Some(l) = self.locals.iter().position(|l| l.var == c) {
                    out.extend(self.locals[l].caps.iter().copied());
                }
            }
        }
        for p in v.parts.iter().flatten() {
            out.extend(self.val_caps(p));
        }
        self.ty_caps(&v.ty, 0, &mut out);
        // A part of a local, for example a field, can hold what the local holds.
        let owner = v.local.or_else(|| v.place.as_ref().and_then(|p| p.owner));
        if let (Some(l), true) = (owner, self.has_fn(&v.ty, 0)) {
            out.extend(self.locals[l].caps.iter().copied());
        }
        out
    }

    /// Adds the capabilities of the closures in type `t`.
    fn ty_caps(&self, t: &Ty, depth: usize, out: &mut BTreeSet<CapId>) {
        if depth > 6 {
            return;
        }
        let t = self.inf.shallow(t);
        match &t {
            Ty::Fn(f) => {
                if let Some(s) = f.summary {
                    out.extend(self.closures[s].performs.iter().copied());
                }
            }
            Ty::Ref(inner) => self.ty_caps(inner, depth + 1, out),
            _ => {
                for f in self.adt_fields(&t) {
                    self.ty_caps(&f, depth + 1, out);
                }
            }
        }
    }

    /// Returns the capabilities of the function values in local `l`.
    fn local_caps(&self, l: usize) -> BTreeSet<CapId> {
        let mut out = self.locals[l].caps.clone();
        if let Some(s) = self.local_fn_info(l).summary {
            out.extend(self.closures[s].performs.iter().copied());
        }
        self.ty_caps(&self.locals[l].ty, 0, &mut out);
        out
    }

    /// Records that the function values in `v` go to `to`.
    pub(super) fn keep(&mut self, v: &Val, to: KeptTo) {
        let caps = self.val_caps(v);
        if !caps.is_empty() {
            self.kept.push(Kept { caps, to });
        }
    }

    /// Records that the function values in `v` go into the places `into`. A place
    /// that a local owns keeps them in the local; another place keeps them where
    /// the body does not follow them.
    pub(super) fn store_into(&mut self, v: &Val, into: &[PlaceId]) {
        let caps = self.val_caps(v);
        if caps.is_empty() {
            return;
        }
        let mut stored = into.is_empty();
        for &p in into {
            match self.place_local(p) {
                Some(l) => self.locals[l].caps.extend(caps.iter().copied()),
                None => stored = true,
            }
        }
        if stored {
            self.kept.push(Kept {
                caps,
                to: KeptTo::Stored,
            });
        }
    }

    /// Returns the local that owns place `p`, if `p` is not behind a reference.
    fn place_local(&self, p: PlaceId) -> Option<usize> {
        let root = self.root_place(p);
        let kind = self.facts.roots[self.facts.place(root).root.index()].kind;
        if kind != RootKind::Local {
            return None;
        }
        self.locals.iter().position(|l| l.root == Some(root))
    }

    /// Records that `v` goes to the clause of an operation. The clause can keep
    /// it, so it must not perform through a handler inside the handler of the
    /// operation: index `at` in `Lower::handlers`, or `None` for a handler of a caller.
    pub(super) fn keep_for_op(&mut self, v: &Val, at: Option<usize>) {
        let inner: BTreeSet<CapId> = self
            .handlers
            .iter()
            .skip(at.map_or(0, |i| i + 1))
            .map(|h| h.cap)
            .collect();
        let caps: BTreeSet<CapId> = self.val_caps(v).intersection(&inner).copied().collect();
        if !caps.is_empty() {
            self.kept.push(Kept {
                caps,
                to: KeptTo::Given,
            });
        }
    }

    /// Returns true if a call of function value `callee` can keep its function
    /// argument `i`: a value that the body does not know, or one that stores it.
    pub(super) fn value_keeps(&self, callee: &FnInfo, i: usize) -> bool {
        if callee.param.is_some() {
            return true;
        }
        match callee.summary {
            Some(s) => {
                let sum = &self.closures[s];
                sum.unknown
                    || !sum.params.is_empty()
                    || sum.stores.contains(&i)
                    || sum.items.iter().any(|&f| self.item_keeps(f, i))
            }
            None => callee.item.is_none_or(|f| self.item_keeps(f, i)),
        }
    }

    /// Returns true if function item `f` can keep its function argument `i`.
    fn item_keeps(&self, f: FnId, i: usize) -> bool {
        let def = &self.prog.fns[f];
        (def.decl.body.is_none() && !def.is_std) || self.sigs[f].effects.stores.contains(&i)
    }

    /// Returns the effects that clause summary `cs` performs outside its handler:
    /// the effects that escape the function, and the effects of the handlers
    /// outside the `handle` that it uses.
    pub(super) fn clause_effects(&self, cs: &Summary) -> BTreeSet<String> {
        let mut out: BTreeSet<String> = cs.escapes.iter().cloned().collect();
        for c in cs.performs.difference(&cs.own_caps) {
            if let Some(h) = self.handlers.iter().find(|h| h.cap == *c) {
                out.insert(h.effect.clone());
            }
        }
        out
    }

    /// Notes the start of the body of a handler.
    pub(super) fn handle_start(&self) -> HandleStart {
        HandleStart {
            locals: self.locals.len(),
            kept: self.kept.len(),
        }
    }

    /// Reports W0313 if a function value that performs through `cap` leaves the
    /// handled body that started at `start`: as its value `v`, through a local
    /// outside it, or to a place or code that can keep it.
    pub(super) fn check_cap_escape(
        &mut self,
        cap: CapId,
        effect: &str,
        start: HandleStart,
        v: &Val,
        span: Span,
    ) {
        let head = format!("a closure that performs `{effect}` escapes its handler");
        if self.val_caps(v).contains(&cap) {
            self.err("W0313", head, span);
            return;
        }
        let mut how = None;
        for k in &self.kept[start.kept..] {
            if !k.caps.contains(&cap) {
                continue;
            }
            how = Some(match k.to {
                KeptTo::Stored => "the body stores it".to_string(),
                KeptTo::Given => "the body gives it to code that can keep it".to_string(),
            });
            break;
        }
        if how.is_none() {
            how = (0..start.locals)
                .find(|&l| self.local_caps(l).contains(&cap))
                .map(|l| format!("the local `{}` keeps it", self.locals[l].name));
        }
        if let Some(how) = how {
            self.err("W0313", format!("{head}: {how}"), span);
        }
    }
}
