//! The domain of the analysis (`docs/ir.md` 6.6): abstract values, the
//! values of move paths, the state at a point, and the joins.
//!
//! - [`AbsVal`] is the abstract value of one value: the places that it can
//!   point into, the function values that it can be, the capabilities and the
//!   tasks that it can hold, and three flags.
//! - [`Tree`] keeps the structure of the move paths of a value: a tuple of
//!   two references has one value for each part. The `top` of a node is the
//!   part of the value that no child names (a value that came in as a whole).
//! - [`State`] maps each local of a component to its tree, and holds which
//!   move paths can hold a value (may) and must hold a value (must, with
//!   the holes that a move or an `Uninit` makes below a path that must hold
//!   a value).
//!
//! A join is a union of the may parts and an intersection of the must parts.
//! A local or a path with no entry has no value: [`AbsVal::none`] is the
//! identity of the join.

use std::collections::{BTreeMap, BTreeSet};

use weft_facts::PlaceId;
use weft_ir::{BodyId, FnId, LocalId, SpawnId, TyId};

/// A function value that a value can be (stage F3 knows items only; the
/// closures and the function parameters come with stages F11 and F12).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FnVal {
    /// A function item with its type arguments.
    Item(FnId, Vec<TyId>),
    /// A value that the analysis does not know.
    Unknown,
}

/// The abstract value of one value (`docs/ir.md` 6.6).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbsVal {
    /// The places that the value can point into (may).
    pub refs: BTreeSet<PlaceId>,
    /// The function values that the value can be (may).
    pub fns: BTreeSet<FnVal>,
    /// The capability and continuation roots that the value can hold (may).
    pub caps: BTreeSet<PlaceId>,
    /// The task sites that the value can be a handle of (may).
    pub tasks: BTreeSet<SpawnId>,
    /// The value can hold a linear value (may).
    pub linear: bool,
    /// The value holds nothing linear, such as `None` (must).
    pub empty: bool,
    /// The value is `@ uniq` (must).
    pub uniq: bool,
}

impl Default for AbsVal {
    fn default() -> Self {
        Self::none()
    }
}

impl AbsVal {
    /// No value: the identity of the join. It holds nothing, so it is
    /// empty, and each of its values (none) is `@ uniq`.
    pub const fn none() -> Self {
        Self {
            refs: BTreeSet::new(),
            fns: BTreeSet::new(),
            caps: BTreeSet::new(),
            tasks: BTreeSet::new(),
            linear: false,
            empty: true,
            uniq: true,
        }
    }

    /// A plain value: no reference, nothing linear, not `@ uniq`. A
    /// constant and the result of an operator have this value.
    pub const fn plain() -> Self {
        Self {
            refs: BTreeSet::new(),
            fns: BTreeSet::new(),
            caps: BTreeSet::new(),
            tasks: BTreeSet::new(),
            linear: false,
            empty: true,
            uniq: false,
        }
    }

    /// A value that points into `refs`, and holds nothing linear.
    pub fn refs(refs: impl IntoIterator<Item = PlaceId>) -> Self {
        Self {
            refs: refs.into_iter().collect(),
            ..Self::plain()
        }
    }

    /// A value whose linear part comes from its type: `linear` is true if
    /// the type can hold a linear value.
    pub const fn of_type(linear: bool) -> Self {
        Self {
            refs: BTreeSet::new(),
            fns: BTreeSet::new(),
            caps: BTreeSet::new(),
            tasks: BTreeSet::new(),
            linear,
            empty: !linear,
            uniq: false,
        }
    }

    /// Joins `o` into `self`: a union of the may parts and an intersection
    /// of the must parts. Returns true if `self` changed.
    pub fn join(&mut self, o: &Self) -> bool {
        let before = (
            self.refs.len(),
            self.fns.len(),
            self.caps.len(),
            self.tasks.len(),
            self.linear,
            self.empty,
            self.uniq,
        );
        self.refs.extend(o.refs.iter().copied());
        self.fns.extend(o.fns.iter().cloned());
        self.caps.extend(o.caps.iter().copied());
        self.tasks.extend(o.tasks.iter().copied());
        self.linear |= o.linear;
        self.empty &= o.empty;
        self.uniq &= o.uniq;
        before
            != (
                self.refs.len(),
                self.fns.len(),
                self.caps.len(),
                self.tasks.len(),
                self.linear,
                self.empty,
                self.uniq,
            )
    }

    /// The join of `self` and `o`.
    #[must_use]
    pub fn joined(mut self, o: &Self) -> Self {
        self.join(o);
        self
    }
}

/// One step of a move path: a field (or a tuple part, or a payload field),
/// or a variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PathStep {
    /// A field, a tuple part or a field of a payload.
    Field(u32),
    /// A variant of an enum.
    Variant(u32),
}

/// The value of a move path and its parts.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Tree {
    /// The part of the value that no child names.
    pub top: AbsVal,
    /// The values of the parts.
    pub kids: BTreeMap<PathStep, Self>,
}

impl Tree {
    /// A value with no parts.
    pub const fn leaf(v: AbsVal) -> Self {
        Self {
            top: v,
            kids: BTreeMap::new(),
        }
    }

    /// No value.
    pub const fn none() -> Self {
        Self::leaf(AbsVal::none())
    }

    /// The value as one abstract value: the join of the top and of each part.
    pub fn flat(&self) -> AbsVal {
        let mut v = self.top.clone();
        for k in self.kids.values() {
            v.join(&k.flat());
        }
        v
    }

    /// The value with no part at or below each path of `skip` (paths
    /// relative to this tree): what the parts with variables of their own
    /// do not hold.
    pub fn flat_without(&self, skip: &[&[PathStep]]) -> AbsVal {
        if skip.iter().any(|s| s.is_empty()) {
            return AbsVal::none();
        }
        let mut v = self.top.clone();
        for (step, k) in &self.kids {
            let below: Vec<&[PathStep]> = skip
                .iter()
                .filter_map(|s| s.split_first().filter(|(h, _)| *h == step).map(|(_, r)| r))
                .collect();
            v.join(&k.flat_without(&below));
        }
        v
    }

    /// The value at `path`. The top of each node above the path joins into
    /// the top of the result: a value that came in as a whole holds the
    /// part too.
    #[must_use]
    pub fn get(&self, path: &[PathStep]) -> Self {
        let mut node = self;
        let mut above = AbsVal::none();
        for s in path {
            above.join(&node.top);
            match node.kids.get(s) {
                Some(k) => node = k,
                None => return Self::leaf(above),
            }
        }
        let mut out = node.clone();
        out.top.join(&above);
        out
    }

    /// Gives the part at `path` the value `v`. The parts below `path` go
    /// away. The tops above the path stay: they can hold the old value of
    /// the part.
    pub fn set(&mut self, path: &[PathStep], v: Self) {
        match path.split_first() {
            None => *self = v,
            Some((s, rest)) => self.kids.entry(*s).or_insert_with(Self::none).set(rest, v),
        }
    }

    /// Joins `v` into the part at `path` (a weak update).
    pub fn add(&mut self, path: &[PathStep], v: &Self) -> bool {
        match path.split_first() {
            None => self.join(v),
            Some((s, rest)) => self.kids.entry(*s).or_insert_with(Self::none).add(rest, v),
        }
    }

    /// Joins `o` into `self`, part by part. Returns true if `self` changed.
    pub fn join(&mut self, o: &Self) -> bool {
        let mut changed = self.top.join(&o.top);
        for (s, k) in &o.kids {
            if let Some(mine) = self.kids.get_mut(s) {
                changed |= mine.join(k);
            } else {
                self.kids.insert(*s, k.clone());
                changed = true;
            }
        }
        changed
    }
}

/// The key of a local: the body and the local that own its value. An upvar
/// local has the key of its site local.
pub type Key = (BodyId, LocalId);

/// A move path: a local and the steps below it.
pub type Path = (Key, Vec<PathStep>);

/// The state at one point of a component (`docs/ir.md` 6.6).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct State {
    /// The value of each local that can have one.
    vals: BTreeMap<Key, Tree>,
    /// The move paths that can hold a value.
    may: BTreeSet<Path>,
    /// The move paths that must hold a value, but for the holes below them.
    must: BTreeSet<Path>,
    /// The move paths that can have no value: a part that moved or that an
    /// `Uninit` left with no value (may).
    holes: BTreeSet<Path>,
}

/// True if `a` is a prefix of `b` (or equal to it).
fn is_prefix(a: &[PathStep], b: &[PathStep]) -> bool {
    a.len() <= b.len() && a.iter().zip(b).all(|(x, y)| x == y)
}

impl State {
    /// The empty state: no local has a value.
    pub fn new() -> Self {
        Self::default()
    }

    /// The value of the move path `path` of local `key`. A local with no
    /// value gives [`Tree::none`].
    pub fn value(&self, key: Key, path: &[PathStep]) -> Tree {
        self.vals.get(&key).map_or_else(Tree::none, |t| t.get(path))
    }

    /// The tree of local `key`, if it has one.
    pub fn tree(&self, key: Key) -> Option<&Tree> {
        self.vals.get(&key)
    }

    /// Gives the move path `path` of local `key` the value `v` (a strong
    /// update): it can and must hold a value now, and its parts get the
    /// parts of `v`.
    pub fn write(&mut self, key: Key, path: &[PathStep], v: Tree) {
        self.vals.entry(key).or_insert_with(Tree::none).set(path, v);
        self.may.retain(|(k, p)| *k != key || !is_prefix(path, p));
        self.must.retain(|(k, p)| *k != key || !is_prefix(path, p));
        self.holes.retain(|(k, p)| *k != key || !is_prefix(path, p));
        self.may.insert((key, path.to_vec()));
        self.must.insert((key, path.to_vec()));
    }

    /// Joins `v` into the move path `path` of local `key` (a weak update:
    /// a store through a reference or into an element). The path can hold a
    /// value now.
    pub fn add(&mut self, key: Key, path: &[PathStep], v: &Tree) {
        self.vals.entry(key).or_insert_with(Tree::none).add(path, v);
        self.may.insert((key, path.to_vec()));
    }

    /// The move path `path` of local `key` has no value now: a move, a
    /// `Consume`, an `Uninit`. With an empty path, the whole local.
    pub fn clear(&mut self, key: Key, path: &[PathStep]) {
        self.may.retain(|(k, p)| *k != key || !is_prefix(path, p));
        self.must.retain(|(k, p)| *k != key || !is_prefix(path, p));
        self.holes.retain(|(k, p)| *k != key || !is_prefix(path, p));
        if path.is_empty() {
            self.vals.remove(&key);
        } else {
            if let Some(t) = self.vals.get_mut(&key) {
                t.set(path, Tree::none());
            }
            // The paths above the cleared part keep their other parts.
            self.holes.insert((key, path.to_vec()));
        }
    }

    /// Adds a hole at the move path `path` of local `key`: the part can have
    /// no value (a part of a moved value that had no value).
    pub fn add_hole(&mut self, key: Key, path: &[PathStep]) {
        self.holes.insert((key, path.to_vec()));
    }

    /// The holes of local `key` at or below the move path `path`, relative
    /// to `path`.
    pub fn holes_below(&self, key: Key, path: &[PathStep]) -> Vec<Vec<PathStep>> {
        self.holes
            .iter()
            .filter(|(k, p)| *k == key && is_prefix(path, p))
            .filter_map(|(_, p)| p.get(path.len()..).map(<[PathStep]>::to_vec))
            .collect()
    }

    /// True if local `key` can hold a value, or a value of a part.
    pub fn may_hold(&self, key: Key) -> bool {
        self.may.iter().any(|(k, _)| *k == key)
    }

    /// True if the move path `path` of local `key` must hold a value: the
    /// path or a path above it got a value on each path to this point, and
    /// no hole overlaps the path.
    pub fn must_hold(&self, key: Key, path: &[PathStep]) -> bool {
        self.must
            .iter()
            .any(|(k, p)| *k == key && is_prefix(p, path))
            && !self
                .holes
                .iter()
                .any(|(k, p)| *k == key && (is_prefix(p, path) || is_prefix(path, p)))
    }

    /// Joins `o` into `self`: a union of the values and of the may parts,
    /// and an intersection of the must parts. Returns true if `self`
    /// changed.
    pub fn join(&mut self, o: &Self) -> bool {
        let mut changed = false;
        for (k, t) in &o.vals {
            if let Some(mine) = self.vals.get_mut(k) {
                changed |= mine.join(t);
            } else {
                self.vals.insert(*k, t.clone());
                changed = true;
            }
        }
        let may = self.may.len();
        self.may.extend(o.may.iter().cloned());
        changed |= self.may.len() != may;
        let must = self.must.len();
        self.must.retain(|p| o.must.contains(p));
        changed |= self.must.len() != must;
        let holes = self.holes.len();
        self.holes.extend(o.holes.iter().cloned());
        changed |= self.holes.len() != holes;
        changed
    }
}
