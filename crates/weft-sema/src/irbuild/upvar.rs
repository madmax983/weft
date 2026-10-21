//! Upvar locals (`docs/ir.md` 5.1.7, "Upvars").
//!
//! A handled body and a clause do not capture into an environment. They run
//! while the frame of their site runs, so they name each local of the site
//! that they use as an upvar local (`LocalKind::Upvar(site_local)`). An upvar
//! local has the cell of the site local: it has no `Live` and no `Dead`
//! (V14), and it is not in a cleanup chain.
//!
//! Before the builder builds a nested body, the site gives it a [`Site`]: the
//! place in the site of each binding that the nested body names, and of each
//! capability that it can use. A binding of an outer body is an upvar local
//! of the site too, so a body inside a handled body names a local of the
//! function through the chain of upvar locals. The nested body makes its
//! upvar local of a site local at the first use.
//!
//! An upvar local names a whole local of the site. A capture of a closure
//! body (`env.k`) is not a whole local: a `handle` in a closure body that
//! names a capture or a capability field of the closure is
//! [`Construct::Handle`] (plan stage B12).

use std::collections::HashMap;

use weft_ir::{EffectId, LocalDecl, LocalId, LocalKind, Origin, Place, Props, TyId};
use weft_syntax::ast::{Expr, Span};

use super::closure::free_bindings;
use super::{unsupported, Builder, Construct, R};
use crate::thir::BindingId;

/// A local of the site that a nested body can name.
#[derive(Clone, Debug)]
pub(super) struct SiteVar {
    /// The local in the site.
    local: LocalId,
    /// Its type.
    ty: TyId,
    /// Its source name.
    name: Option<String>,
    /// Its properties.
    props: Props,
    /// Where it comes from.
    origin: Origin,
}

/// The locals and the capabilities of the site that a nested body can name.
#[derive(Clone, Debug, Default)]
pub(super) struct Site {
    /// The local of the site of each binding that the body names.
    vars: HashMap<BindingId, SiteVar>,
    /// The capability local of the site of each effect that the site binds
    /// and that the body can use.
    pub(super) caps: Vec<(EffectId, SiteVar)>,
    /// The upvar local of each local of the site that the body names.
    upvars: HashMap<LocalId, LocalId>,
}

impl Site {
    /// Returns the local of the site that binds effect `e`, if one does.
    pub(super) fn cap(&self, e: EffectId) -> Option<&SiteVar> {
        self.caps.iter().find(|(x, _)| *x == e).map(|(_, v)| v)
    }
}

impl Builder<'_> {
    /// Returns the upvar local of binding `b` of the site, if the site names
    /// `b`. The builder makes it at the first use.
    pub(super) fn site_var(&mut self, b: BindingId) -> Option<LocalId> {
        let v = self.site.as_ref()?.vars.get(&b)?.clone();
        let l = self.upvar(&v);
        self.vars.insert(b, l);
        Some(l)
    }

    /// Returns the upvar local of site local `v`. The builder makes it at
    /// the first use: it has a cell at the entry, and no `Live` or `Dead`.
    pub(super) fn upvar(&mut self, v: &SiteVar) -> LocalId {
        if let Some(&l) = self.site.as_ref().and_then(|s| s.upvars.get(&v.local)) {
            return l;
        }
        let l = self.add_local(LocalDecl {
            ty: v.ty,
            kind: LocalKind::Upvar(v.local),
            name: v.name.clone(),
            props: v.props,
            in_place: false,
            origin: v.origin,
        });
        if let Some(s) = self.site.as_mut() {
            s.upvars.insert(v.local, l);
        }
        l
    }

    /// Returns the site of the bodies of `handle` expression `e`: the local
    /// of this body of each binding that the bodies name, and of each
    /// capability that they can use. A binding or a capability that comes
    /// from the site of this body gets its upvar local here now.
    pub(super) fn site_for(&mut self, e: &Expr) -> R<Site> {
        let mut site = Site::default();
        for b in free_bindings(self.t, e) {
            if let Some(p) = self.binding_place(b) {
                let v = self.site_local(&p, e.span)?;
                site.vars.insert(b, v);
            }
        }
        for (effect, p) in self.caps_for(e, false) {
            let v = self.site_local(&p, e.span)?;
            site.caps.push((effect, v));
        }
        Ok(site)
    }

    /// Returns the site local of place `p` of this body. Only a whole local
    /// can be the cell of an upvar local.
    fn site_local(&self, p: &Place, span: Span) -> R<SiteVar> {
        if !p.is_local() {
            return unsupported(Construct::Handle, span);
        }
        let Some(d) = self.locals.get(p.local.index()) else {
            return unsupported(Construct::NoThir, span);
        };
        Ok(SiteVar {
            local: p.local,
            ty: d.ty,
            name: d.name.clone(),
            props: d.props,
            origin: d.origin,
        })
    }
}
