//! Capabilities (`docs/ir.md` 5.1.8).
//!
//! Handlers are lexical, so the builder knows the capability of each effect
//! at each point. A body binds the effects of its own capabilities
//! ([`Builder::caps`](super::Builder)): the capability local of a handled
//! body, and the `Cap` fields of a closure environment. A clause and a
//! handled body also see the capabilities of their site, through upvar
//! locals (`upvar.rs`). An effect that nothing binds resolves to the
//! capability of the row, `CapOperand::Row(E)`: the caller of the function
//! gives it.
//!
//! A clause runs in the capability environment of its site, without the
//! capability of its own handler (rule 6 of the effects proof). A call passes
//! the lexical environment (`CapArgs::Lexical`): the callee takes the
//! capability of each effect of its row from it.
//!
//! A closure gets a `Cap` field for each effect that its maker binds and
//! that its body can use ([`Builder::effects_used`]): an effect that the
//! body performs, an effect of the stated row of a call in the body, and
//! each effect if a call in the body has a row that the builder does not
//! know.

use std::collections::BTreeSet;

use weft_ir::{CapArgs, CapEnv, CapEnvId, CapOperand, EffectId, Place, Ty};
use weft_syntax::ast::{Expr, ExprKind};

use super::closure::walk_exprs;
use super::{id_of, Builder};
use crate::thir::{Builtin, Callee};

/// The effects that the code of an expression can use.
#[derive(Clone, Debug, Default)]
pub(super) struct Need {
    /// Each effect: a call has a row that the builder does not know.
    all: bool,
    /// The effects that the code names.
    some: BTreeSet<EffectId>,
}

impl Need {
    /// Returns true if the code can use effect `e`.
    fn has(&self, e: EffectId) -> bool {
        self.all || self.some.contains(&e)
    }
}

impl Builder<'_> {
    /// Returns the capability of effect `e` at the current point
    /// (`docs/ir.md` 5.1.8): a capability of this body, the upvar local of
    /// a capability of the site (made at the first use), or the capability
    /// of the row.
    pub(super) fn cap_of(&mut self, e: EffectId) -> CapOperand {
        if let Some((_, p)) = self.caps.iter().find(|(x, _)| *x == e) {
            return CapOperand::Local(p.clone());
        }
        let v = self.site.as_ref().and_then(|s| s.cap(e)).cloned();
        if let Some(v) = v {
            let p = self.upvar(&v);
            self.caps.push((e, p.clone()));
            return CapOperand::Local(p);
        }
        CapOperand::Row(e)
    }

    /// Returns the capabilities that a call at the current point gives to
    /// its callee: the lexical environment (`docs/ir.md` 5.1.8, 5.34).
    pub(super) const fn cap_args(&self) -> CapArgs {
        CapArgs::Lexical(self.cap_env)
    }

    /// Adds capability environment `env` and returns its id.
    pub(super) fn new_cap_env(&mut self, env: CapEnv) -> CapEnvId {
        let id = CapEnvId(id_of(self.d.cap_envs.len()));
        self.d.cap_envs.push(env);
        id
    }

    /// Returns each effect that this body binds and that the code of `e` can
    /// use, with the place of its capability in this body. The capabilities
    /// of this body come first, then those of the site. `inner`: the code
    /// of `e` is the body of a closure, so its calls count too.
    pub(super) fn caps_for(&mut self, e: &Expr, inner: bool) -> Vec<(EffectId, Place)> {
        let mut bound: Vec<EffectId> = self.caps.iter().map(|(x, _)| *x).collect();
        if let Some(s) = &self.site {
            for (x, _) in &s.caps {
                if !bound.contains(x) {
                    bound.push(*x);
                }
            }
        }
        if bound.is_empty() {
            return Vec::new();
        }
        let need = self.effects_used(e, inner);
        let mut out = Vec::new();
        for x in bound {
            if need.has(x) {
                if let CapOperand::Local(p) = self.cap_of(x) {
                    out.push((x, p));
                }
            }
        }
        out
    }

    /// Returns the effects that the code of `e` can use where it runs: each
    /// effect that it performs (also in the closures and the bodies inside
    /// it), and for each call inside a closure the effects of the row of
    /// the callee. A closure performs through the capabilities of the point
    /// where it is made, so its calls need them. A call outside a closure
    /// passes the lexical environment. `inner`: `e` is the body of a
    /// closure.
    fn effects_used(&self, e: &Expr, inner: bool) -> Need {
        let mut need = Need::default();
        walk_exprs(e, inner, &mut |x, in_closure| {
            let callee = match &x.kind {
                ExprKind::Call { callee, .. } => Some(&**callee),
                ExprKind::MethodCall { .. } => None,
                _ => return,
            };
            let Some(info) = self.t.call.get(&x.id) else {
                // A call with no call entry: its row is not known.
                need.all |= in_closure;
                return;
            };
            match &info.callee {
                Callee::Op { effect, .. } => {
                    need.some.insert(*effect);
                }
                _ if !in_closure => {}
                Callee::Item { item, .. } => match self.item_row(*item) {
                    Some(r) => need.some.extend(r),
                    None => need.all = true,
                },
                Callee::Value(_) => {
                    let row = callee
                        .and_then(|c| self.t.expr_ty.get(&c.id))
                        .and_then(|&t| match self.tys.try_get(t) {
                            Some(Ty::Fn(f)) => f.row.clone(),
                            _ => None,
                        });
                    match row {
                        Some(r) => need.some.extend(r),
                        None => need.all = true,
                    }
                }
                Callee::Resume(_)
                | Callee::Struct { .. }
                | Callee::Variant { .. }
                | Callee::Builtin(Builtin::Print) => {}
                Callee::Builtin(_) => need.all = true,
            }
        });
        need
    }

    /// Returns the stated row of function item `f`, or `None` if the
    /// signature states no row or the function has a run-time meaning
    /// (`sim.run`, `with_timeout`).
    fn item_row(&self, f: crate::FnId) -> Option<Vec<EffectId>> {
        let a = self.d.a;
        let def = a.program.fns.get(f.index())?;
        let sig = a.sigs.get(f.index())?;
        if !sig.declared || super::intrinsic(a, def).is_some() {
            return None;
        }
        Some(super::stated_effects(a, sig))
    }
}
