//! The values of the parts with variables of their own (`docs/ir.md` 6.3).
//!
//! `points_into` has no node: a variable points into each place that one of
//! its values points into. So one `H` variable for each part collects the
//! places of every value that the part gets, and a reference in an old value
//! makes a later use of the part invalid (a false positive). This module
//! gives each value of a part a variable of its own, as the part holders of
//! the old lowering did:
//!
//! - A *version* of the part is a variable for the values with one set of
//!   places (the places of the new value at a write). Two writes with the
//!   same places use one version.
//! - The templates use the variable of the part (the *placeholder*, the
//!   first version) in `uses`, `rebound_at`, `scope_end` and `unwound_at`,
//!   and give the places of the values to this module (a new value, or a
//!   weak definition through a pointer).
//! - [`Holders::finish`] gives each version the places of its values, and
//!   changes the facts of the placeholder: a `uses` goes to each version
//!   that is *current* at the node, the other facts go to each version.
//! - A version is current at a node if the state of the analysis before the
//!   node lets the part hold one of the places of the version. At each node
//!   where a version is not current, it gets `rebound_at`: an old value that
//!   a branch replaced does not carry its invalid state to the join.
//!
//! A version that is current where the part holds one of its places is used
//! there, and nothing but a new value of the part (or of a part above it)
//! rebinds it while the part holds the value. So each reference that the
//! part can hold at a use is in a version that the node uses and that is
//! invalid if the reference is.
//!
//! A heap slot (`docs/ir.md` 6.6: a place that no local of the component
//! owns, behind a reference parameter or in a place of a caller, that gets
//! references) gets variables in the same way (stage F10.1, hole H-A of the
//! review of stage F10). The state of the analysis gives the places that
//! each slot can hold before each node (`State::behind`). A version of a
//! slot is a variable for the places of the slot that overlap. It is current
//! at a node where the slot can hold one of its places, and it gets
//! `rebound_at` at each other node: before the store, a change of the
//! referent does not make the version invalid. A read of a place of the slot
//! (an access through it, a copy of a reference out of it, a read through a
//! chain of references) uses the slot ([`Holders::slot_vars`]), and the use
//! goes to the current versions. So a reference that a body stores behind
//! `out`, then reads back after its referent changes, is W0301.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use weft_facts::{FnFacts, NodeId, PlaceId, VarId, VarInfo, VarKind};

use crate::analysis::{Key, PathStep, State};

/// A part with a variable of its own.
#[derive(Clone, Debug)]
struct Part {
    /// The key of the local.
    key: Key,
    /// The move path of the part.
    steps: Vec<PathStep>,
    /// The parts of the local below this part that have variables of their
    /// own, relative to this part: their places are not places of this
    /// part.
    deeper: Vec<Vec<PathStep>>,
    /// The placeholder: the variable that the templates use.
    var: VarId,
}

/// A heap slot with a variable of its own (see the module comment).
#[derive(Clone, Debug)]
struct Slot {
    /// The place of the slot: its key in `State::behind`.
    key: PlaceId,
    /// The placeholder: the variable that the templates use.
    var: VarId,
}

/// True if fact place `a` is at or below `b`.
fn at_or_below(facts: &FnFacts, a: PlaceId, b: PlaceId) -> bool {
    let mut cur = Some(a);
    while let Some(c) = cur {
        if c == b {
            return true;
        }
        cur = facts.places.get(c.index()).and_then(|i| i.parent);
    }
    false
}

/// True if fact places `a` and `b` overlap: one is at or below the other. A
/// place below a wildcard place counts as the base of the wildcard place (the
/// rule of the heap slots of the analysis, `stored_at`).
fn overlap(facts: &FnFacts, a: PlaceId, b: PlaceId) -> bool {
    let norm = |p: PlaceId| facts.wild_base(p).unwrap_or(p);
    let (a, b) = (norm(a), norm(b));
    at_or_below(facts, a, b) || at_or_below(facts, b, a)
}

/// A version of a part.
#[derive(Clone, Debug)]
struct Version {
    /// The places of the new values that use this version.
    key: BTreeSet<PlaceId>,
    /// Each place that a value of the version can point into.
    all: BTreeSet<PlaceId>,
    /// The variable.
    var: VarId,
}

/// What a template gives to a part.
#[derive(Clone, Debug)]
enum Event {
    /// A new value with the places `refs` at a node.
    Value {
        part: usize,
        refs: BTreeSet<PlaceId>,
    },
    /// A weak definition at node `n` (or at no node): the part can hold
    /// `refs` too.
    Add {
        n: Option<NodeId>,
        part: usize,
        refs: BTreeSet<PlaceId>,
    },
}

/// The versions of the parts of one component.
#[derive(Clone, Debug, Default)]
pub struct Holders {
    /// The parts.
    parts: Vec<Part>,
    /// The part of each placeholder.
    by_var: HashMap<VarId, usize>,
    /// The events, in the order of the templates.
    events: Vec<Event>,
    /// For each node: the places that each part can hold before the node,
    /// in the order of [`Holders::parts`].
    before: BTreeMap<NodeId, Vec<BTreeSet<PlaceId>>>,
    /// The heap slots, in the order that the states show them.
    slots: Vec<Slot>,
    /// The slot of each place of a slot.
    slot_of: HashMap<PlaceId, usize>,
    /// For each node: the places that each slot can hold before the node, in
    /// the order of [`Holders::slots`]. A slot after the end of the list
    /// holds nothing there.
    slot_before: BTreeMap<NodeId, Vec<BTreeSet<PlaceId>>>,
}

/// The versions of one part, as [`Holders::finish`] makes them: what the
/// fact oracle of the interpreter needs to find the value of each version
/// at run time (`docs/ir.md` 8.5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartVersions {
    /// The key of the local.
    pub key: Key,
    /// The move path of the part.
    pub steps: Vec<PathStep>,
    /// The parts below this part that have variables of their own, relative
    /// to this part.
    pub deeper: Vec<Vec<PathStep>>,
    /// The variables of the versions. A part with no version keeps its
    /// placeholder.
    pub vars: Vec<VarId>,
}

/// True if `a` is a prefix of `b` (or equal to it).
fn is_prefix(a: &[PathStep], b: &[PathStep]) -> bool {
    a.len() <= b.len() && a.iter().zip(b).all(|(x, y)| x == y)
}

impl Holders {
    /// The holders of the parts `parts`: for each part, the key of its
    /// local, its move path and its variable.
    pub fn new(parts: impl IntoIterator<Item = (Key, Vec<PathStep>, VarId)>) -> Self {
        let all: Vec<(Key, Vec<PathStep>, VarId)> = parts.into_iter().collect();
        let mut out = Self::default();
        for (key, steps, var) in &all {
            let deeper = all
                .iter()
                .filter(|(k, s, _)| k == key && s.len() > steps.len() && is_prefix(steps, s))
                .filter_map(|(_, s, _)| s.get(steps.len()..).map(<[PathStep]>::to_vec))
                .collect();
            out.by_var.insert(*var, out.parts.len());
            out.parts.push(Part {
                key: *key,
                steps: steps.clone(),
                deeper,
                var: *var,
            });
        }
        out
    }

    /// True if the component has no part with a variable of its own.
    pub fn is_empty(&self) -> bool {
        self.parts.is_empty()
    }

    /// The places that part `i` can hold in state `st`.
    fn holds(&self, i: usize, st: &State) -> BTreeSet<PlaceId> {
        self.parts.get(i).map_or_else(BTreeSet::new, |p| {
            let deeper: Vec<&[PathStep]> = p.deeper.iter().map(Vec::as_slice).collect();
            st.value(p.key, &p.steps).flat_without(&deeper).refs
        })
    }

    /// Records the state `st` before node `n`. A heap slot that `st` shows for
    /// the first time gets its placeholder variable in `facts`.
    pub fn before(&mut self, n: NodeId, st: &State, facts: &mut FnFacts) {
        self.slots_before(n, st, facts);
        if self.parts.is_empty() || self.before.contains_key(&n) {
            return;
        }
        let cur = (0..self.parts.len()).map(|i| self.holds(i, st)).collect();
        self.before.insert(n, cur);
    }

    /// Records the places of each heap slot in the state `st` before node `n`.
    fn slots_before(&mut self, n: NodeId, st: &State, facts: &mut FnFacts) {
        if self.slot_before.contains_key(&n) {
            return;
        }
        for (q, refs) in st.behind() {
            if refs.is_empty() || self.slot_of.contains_key(q) {
                continue;
            }
            let name = format!("value in `{}`", facts.place(*q).display);
            let span = facts.node(n).span;
            let var = facts.add_var(VarInfo::plain(name, VarKind::Temp, span, String::new()));
            self.slot_of.insert(*q, self.slots.len());
            self.slots.push(Slot { key: *q, var });
        }
        let cur = self
            .slots
            .iter()
            .map(|s| st.behind().get(&s.key).cloned().unwrap_or_default())
            .collect();
        self.slot_before.insert(n, cur);
    }

    /// The placeholders of the heap slots whose places overlap fact place
    /// `q`: a read of `q` reads what the slot holds.
    pub fn slot_vars(&self, facts: &FnFacts, q: PlaceId) -> Vec<VarId> {
        self.slots
            .iter()
            .filter(|s| overlap(facts, s.key, q))
            .map(|s| s.var)
            .collect()
    }

    /// The part `var` gets a new value that points into `refs`. Returns
    /// false if `var` is not the variable of a part.
    pub fn value(&mut self, var: VarId, refs: &[PlaceId]) -> bool {
        let Some(&part) = self.by_var.get(&var) else {
            return false;
        };
        if !refs.is_empty() {
            self.events.push(Event::Value {
                part,
                refs: refs.iter().copied().collect(),
            });
        }
        true
    }

    /// The part `var` can hold `refs` too after node `n` (a weak
    /// definition). Returns false if `var` is not the variable of a part.
    pub fn add(&mut self, n: NodeId, var: VarId, refs: &[PlaceId]) -> bool {
        let Some(&part) = self.by_var.get(&var) else {
            return false;
        };
        if !refs.is_empty() {
            self.events.push(Event::Add {
                n: Some(n),
                part,
                refs: refs.iter().copied().collect(),
            });
        }
        true
    }

    /// Makes the versions and writes their facts (see the module comment).
    /// Returns the versions of each part.
    pub fn finish(self, facts: &mut FnFacts) -> Vec<PartVersions> {
        self.finish_slots(facts);
        if self.parts.is_empty() {
            return Vec::new();
        }
        let mut versions: Vec<Vec<Version>> = vec![Vec::new(); self.parts.len()];
        let new_var = |facts: &mut FnFacts, part: &Part, first: bool| {
            if first {
                part.var
            } else {
                let info = facts.var(part.var).clone();
                facts.add_var(info)
            }
        };
        // A place that a template gave to a placeholder itself goes to each
        // version, as a weak definition at no node.
        let mut events = self.events.clone();
        facts
            .points_into
            .retain(|&(v, q)| match self.by_var.get(&v) {
                Some(&part) => {
                    events.push(Event::Add {
                        n: None,
                        part,
                        refs: std::iter::once(q).collect(),
                    });
                    false
                }
                None => true,
            });
        // The new values first: a weak definition adds to the versions that
        // the part can hold.
        for e in &events {
            let Event::Value { part, refs } = e else {
                continue;
            };
            let (Some(p), Some(vs)) = (self.parts.get(*part), versions.get_mut(*part)) else {
                continue;
            };
            if !vs.iter().any(|v| v.key == *refs) {
                let var = new_var(facts, p, vs.is_empty());
                vs.push(Version {
                    key: refs.clone(),
                    all: refs.clone(),
                    var,
                });
            }
        }
        for e in &events {
            let Event::Add { n, part, refs } = e else {
                continue;
            };
            let (Some(p), Some(vs)) = (self.parts.get(*part), versions.get_mut(*part)) else {
                continue;
            };
            let mut found = false;
            let cur = n.map(|n| {
                let mut c = self
                    .before
                    .get(&n)
                    .and_then(|c| c.get(*part))
                    .cloned()
                    .unwrap_or_default();
                c.extend(refs.iter().copied());
                c
            });
            // With no node, each version can hold the places.
            let holds = |v: &Version| cur.as_ref().is_none_or(|c| !v.all.is_disjoint(c));
            for v in vs.iter_mut().filter(|v| holds(v)) {
                v.all.extend(refs.iter().copied());
                found = true;
            }
            if !found {
                let var = new_var(facts, p, vs.is_empty());
                vs.push(Version {
                    key: refs.clone(),
                    all: refs.clone(),
                    var,
                });
            }
        }
        // The places of each version.
        for vs in &versions {
            for v in vs {
                facts.points_into.extend(v.all.iter().map(|&q| (v.var, q)));
            }
        }
        // The facts of each placeholder go to its versions.
        let part_of = |var: VarId| {
            self.by_var
                .get(&var)
                .copied()
                .filter(|&i| versions.get(i).is_some_and(|vs| !vs.is_empty()))
        };
        let current = |i: usize, n: NodeId| -> Vec<VarId> {
            let vs = versions.get(i).map_or(&[][..], Vec::as_slice);
            match self.before.get(&n).and_then(|c| c.get(i)) {
                Some(cur) => vs
                    .iter()
                    .filter(|v| !v.all.is_disjoint(cur))
                    .map(|v| v.var)
                    .collect(),
                None => vs.iter().map(|v| v.var).collect(),
            }
        };
        let each = |i: usize| -> Vec<VarId> {
            versions
                .get(i)
                .map(|vs| vs.iter().map(|v| v.var).collect())
                .unwrap_or_default()
        };
        let spread = |rel: &mut Vec<(VarId, NodeId)>, only_current: bool| {
            let mut out = Vec::with_capacity(rel.len());
            for &(v, n) in rel.iter() {
                match part_of(v) {
                    Some(i) if only_current => {
                        out.extend(current(i, n).into_iter().map(|w| (w, n)));
                    }
                    Some(i) => out.extend(each(i).into_iter().map(|w| (w, n))),
                    None => out.push((v, n)),
                }
            }
            *rel = out;
        };
        spread(&mut facts.uses, true);
        spread(&mut facts.rebound_at, false);
        spread(&mut facts.scope_end, false);
        spread(&mut facts.unwound_at, false);
        spread(&mut facts.spared_at, false);
        // An old value that the part no longer holds: the version binds
        // again at each node where it is not current, so its invalid state
        // stops there.
        for (n, cur) in &self.before {
            for (i, vs) in versions.iter().enumerate() {
                let Some(c) = cur.get(i) else {
                    continue;
                };
                for v in vs.iter().filter(|v| v.all.is_disjoint(c)) {
                    facts.rebound_at.push((v.var, *n));
                }
            }
        }
        self.parts
            .iter()
            .zip(&versions)
            .map(|(p, vs)| PartVersions {
                key: p.key,
                steps: p.steps.clone(),
                deeper: p.deeper.clone(),
                vars: if vs.is_empty() {
                    vec![p.var]
                } else {
                    vs.iter().map(|v| v.var).collect()
                },
            })
            .collect()
    }

    /// Makes the versions of each heap slot and writes their facts (see the
    /// module comment).
    fn finish_slots(&self, facts: &mut FnFacts) {
        for (i, slot) in self.slots.iter().enumerate() {
            // Each place that the slot can hold at some node.
            let held: BTreeSet<PlaceId> = self
                .slot_before
                .values()
                .filter_map(|c| c.get(i))
                .flatten()
                .copied()
                .collect();
            // The versions: a place goes to each version that it overlaps,
            // or makes a new one.
            let mut versions: Vec<(BTreeSet<PlaceId>, VarId)> = Vec::new();
            for r in held {
                let mut found = false;
                for (all, _) in &mut versions {
                    if all.iter().any(|&x| overlap(facts, x, r)) {
                        all.insert(r);
                        found = true;
                    }
                }
                if !found {
                    let var = if versions.is_empty() {
                        slot.var
                    } else {
                        let info = facts.var(slot.var).clone();
                        facts.add_var(info)
                    };
                    versions.push((std::iter::once(r).collect(), var));
                }
            }
            for (all, var) in &versions {
                facts.points_into.extend(all.iter().map(|&q| (*var, q)));
            }
            // A version is current at a node where the slot can hold one of
            // its places. With no record of the node, each version is.
            let current = |n: NodeId| -> Vec<VarId> {
                match self.slot_before.get(&n) {
                    Some(c) => versions
                        .iter()
                        .filter(|(all, _)| c.get(i).is_some_and(|c| !all.is_disjoint(c)))
                        .map(|(_, v)| *v)
                        .collect(),
                    None => versions.iter().map(|(_, v)| *v).collect(),
                }
            };
            let mut uses = Vec::with_capacity(facts.uses.len());
            for &(v, n) in &facts.uses {
                if v == slot.var {
                    uses.extend(current(n).into_iter().map(|w| (w, n)));
                } else {
                    uses.push((v, n));
                }
            }
            facts.uses = uses;
            for (n, c) in &self.slot_before {
                for (all, var) in &versions {
                    if c.get(i).is_none_or(|c| all.is_disjoint(c)) {
                        facts.rebound_at.push((*var, *n));
                    }
                }
            }
        }
    }
}
