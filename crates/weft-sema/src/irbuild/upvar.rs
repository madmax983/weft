//! Upvar locals (`docs/ir.md` 5.1.7, "Upvars").
//!
//! A handled body, a clause and a scope body do not capture into an
//! environment. They run while the frame of their site runs, so they name each local of the site
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
//! body (`env.k`) is not a whole local, so a nested body in a closure body
//! names the captures through an upvar local of the environment: an
//! *environment view* (`docs/ir.md` 5.1.7, plan stage B12). The capture is
//! `u.k` there, as it is `env.k` in the closure body. The closure reads the
//! views when it gives the capture modes (`closure.rs`).

use std::collections::HashMap;
use std::rc::Rc;

use weft_ir::{EffectId, LocalDecl, LocalId, LocalKind, Origin, Place, Proj, Props, TyId};
use weft_syntax::ast::{Expr, Span};

use super::closure::free_bindings;
use super::{unsupported, Builder, Construct, R};
use crate::thir::BindingId;

/// The type and the properties of each capture of a closure, in the order
/// of the fields of its environment.
pub(super) type EnvFields = Rc<[(TyId, Props)]>;

/// A local of the site that a nested body can name, or a field of it.
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
    /// The path from the local to the variable: empty, or the field `k` of
    /// an environment (a capture or a capability field of a closure).
    proj: Vec<Proj>,
    /// The fields of the environment if the local is an environment or a
    /// view of one.
    fields: Option<EnvFields>,
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
    /// Returns the place of binding `b` of the site, if the site names `b`:
    /// its upvar local, or the field of the view of the environment
    /// (`u.k`). The builder makes the upvar local at the first use.
    pub(super) fn site_var(&mut self, b: BindingId) -> Option<Place> {
        let v = self.site.as_ref()?.vars.get(&b)?.clone();
        let p = self.upvar(&v);
        if p.is_local() {
            self.vars.insert(b, p.local);
        }
        Some(p)
    }

    /// Returns the place of site variable `v` in this body: its upvar local,
    /// with the path of `v`. The builder makes the upvar local at the first
    /// use: it has a cell at the entry, and no `Live` or `Dead`.
    pub(super) fn upvar(&mut self, v: &SiteVar) -> Place {
        let local = self.upvar_local(v);
        Place {
            local,
            proj: v.proj.clone(),
        }
    }

    /// Returns the upvar local of the local of site variable `v`.
    fn upvar_local(&mut self, v: &SiteVar) -> LocalId {
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
        if let Some(f) = &v.fields {
            self.views.insert(l, Rc::clone(f));
        }
        l
    }

    /// Returns the fields of the environment if local `l` is the
    /// environment of this closure body or a view of an environment.
    pub(super) fn env_fields(&self, l: LocalId) -> Option<EnvFields> {
        if let Some(c) = self.closure.as_ref().filter(|c| c.env == l) {
            return Some(Rc::clone(&c.fields));
        }
        self.views.get(&l).cloned()
    }

    /// Returns the type and the properties of the capture that place `p`
    /// names, if `p` is a whole capture `env.k` or `u.k`.
    pub(super) fn capture_part(&self, p: &Place) -> Option<(TyId, Props)> {
        let [Proj::Field(k)] = p.proj.as_slice() else {
            return None;
        };
        self.env_fields(p.local)?.get(k.index()).copied()
    }

    /// Returns the site of the bodies of `handle` or `scope` expression `e`:
    /// the local of this body of each binding that the bodies name, and of
    /// each capability that they can use. A binding or a capability that comes
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

    /// Returns the site variable of place `p` of this body: a whole local,
    /// or a field `k` of the environment or of a view of it (a capture or a
    /// capability field: `env.k`, `u.k`). The cell of the upvar local is the
    /// local; the nested body names the field through it.
    fn site_local(&self, p: &Place, span: Span) -> R<SiteVar> {
        let fields = self.env_fields(p.local);
        let whole_field = matches!(p.proj.as_slice(), [Proj::Field(_)]) && fields.is_some();
        if !p.is_local() && !whole_field {
            return unsupported(Construct::NoThir, span);
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
            proj: p.proj.clone(),
            fields,
        })
    }
}
