//! The reference-fragment rules of the templates as pure functions
//! (`docs/ir.md` 6.4).
//!
//! Each function takes what a template knows about a place (an [`Access`])
//! and gives the facts of one node as a [`Frag`]. It reads no state and
//! writes no facts: the templates (`super::templates`) put the fragment into
//! the facts at the node. These rules are the kernel of the borrow model:
//!
//! - a borrow `Ref(q)` uses the variables of `q`, reads the pointers on the
//!   way, and gives the places of `q` ([`borrow`]);
//! - a copy of a reference points into the places of the value
//!   ([`copy_ref`]);
//! - a read of `q` uses the variables of `q` and reads `q` and its pointers
//!   ([`read`]); a read through a reference reads what it points into
//!   ([`read_through`]);
//! - a write through a reference changes the places of `q`, uses and reads
//!   its pointers, and gives `writes_via` when the reference holds one place
//!   at or above each change ([`write_through`]).

use weft_facts::{PlaceId, VarId};

/// What a template knows about one access of a place.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Access {
    /// The variables that the access uses: the variables of the move paths
    /// that overlap the place, of its pointer locals and of its index locals.
    pub vars: Vec<VarId>,
    /// The fact places of the place (α).
    pub places: Vec<PlaceId>,
    /// The pointer places on the way, and the roots of the index locals: an
    /// access reads them.
    pub ptrs: Vec<PlaceId>,
    /// The root of the base local, if it is a source local: a use of a
    /// variable reads it.
    pub root: Option<PlaceId>,
}

/// The facts of one node, as plain lists.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Frag {
    /// `uses(v, n)`.
    pub uses: Vec<VarId>,
    /// `reads_at(n, a)`.
    pub reads: Vec<PlaceId>,
    /// `mutates_at(n, m)`.
    pub mutates: Vec<PlaceId>,
    /// `points_into(v, a)`.
    pub points_into: Vec<(VarId, PlaceId)>,
    /// `writes_via(n, v)`.
    pub writes_via: Vec<VarId>,
}

impl Frag {
    /// Adds the facts of `o`.
    pub fn extend(&mut self, o: Self) {
        self.uses.extend(o.uses);
        self.reads.extend(o.reads);
        self.mutates.extend(o.mutates);
        self.points_into.extend(o.points_into);
        self.writes_via.extend(o.writes_via);
    }
}

/// A read of the place: it uses its variables, and reads the place, its
/// pointers and the root of its variable.
pub fn read(a: &Access) -> Frag {
    let mut reads = a.places.clone();
    reads.extend(a.ptrs.iter().copied());
    reads.extend(a.root);
    Frag {
        uses: a.vars.clone(),
        reads,
        ..Frag::default()
    }
}

/// A mention of the place (`Mention`): it uses its variables and reads its
/// pointers and index locals (the place is evaluated), but it does not read
/// the place.
pub fn mention(a: &Access) -> Frag {
    Frag {
        uses: a.vars.clone(),
        reads: a.ptrs.clone(),
        ..Frag::default()
    }
}

/// A borrow `Ref(q)`: it uses the variables of the place and reads its
/// pointers, but it does not read the place.
///
/// The value of the reference points into the places of `q` and into the
/// handle places `handles` of the `Rc` handles on the way (the second
/// result, in order).
pub fn borrow(a: &Access, handles: &[PlaceId]) -> (Frag, Vec<PlaceId>) {
    let mut refs: Vec<PlaceId> = a.places.iter().chain(handles).copied().collect();
    refs.sort();
    refs.dedup();
    (
        Frag {
            uses: a.vars.clone(),
            reads: a.ptrs.clone(),
            ..Frag::default()
        },
        refs,
    )
}

/// A copy of a reference value into the variables `dest`: each one can
/// point into each place of the value.
pub fn copy_ref(dest: &[VarId], refs: &[PlaceId]) -> Frag {
    Frag {
        points_into: dest
            .iter()
            .flat_map(|&v| refs.iter().map(move |&r| (v, r)))
            .collect(),
        ..Frag::default()
    }
}

/// A read through a reference: the node reads each place that the value
/// points into (`print` of a reference).
pub fn read_through(refs: &[PlaceId]) -> Frag {
    Frag {
        reads: refs.to_vec(),
        ..Frag::default()
    }
}

/// A write through a reference to the place: it changes the places, uses
/// the variables of the pointer, and reads the pointers.
///
/// `one` is the variable of the reference and the place that it points to,
/// if it holds one reference to one place that is not a wildcard place. Then
/// the node gets `writes_via` if each change is at or below that place
/// (`below(m, d)`: place `m` is at or below place `d`; rule 4, C6).
pub fn write_through(
    a: &Access,
    one: Option<(VarId, PlaceId)>,
    below: &dyn Fn(PlaceId, PlaceId) -> bool,
) -> Frag {
    let via = one
        .filter(|&(_, d)| !a.places.is_empty() && a.places.iter().all(|&m| below(m, d)))
        .map(|(v, _)| v);
    Frag {
        uses: a.vars.clone(),
        reads: a.ptrs.clone(),
        mutates: a.places.clone(),
        writes_via: via.into_iter().collect(),
        ..Frag::default()
    }
}
