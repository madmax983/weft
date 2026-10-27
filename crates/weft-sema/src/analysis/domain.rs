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
use std::rc::Rc;

use weft_facts::PlaceId;
use weft_ir::{BodyId, ClosureId, FnId, LocalId, SpawnId, TyId};

/// A function value that a value can be (`docs/ir.md` 6.6).
///
/// Stage F3 knows items, stage F11 the closures of the component, and stage F12 the
/// function values of the interface, the closures that a callee makes and gives back, and
/// the values that the analysis does not know.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FnVal {
    /// A function item with its type arguments.
    Item(FnId, Vec<TyId>),
    /// The closure of a literal of the component. Its environment is in the
    /// value too: the cell roots of its `ByRef` captures and what its
    /// `ByMove` captures hold (`docs/ir.md` 6.6); a `Kept` capture shares
    /// the cell of the variable of the maker, so a call reads the variable.
    Closure(ClosureId),
    /// A closure that a callee made and gave back (its result, `Ret::fns`).
    /// Its maker frame is gone: the value itself holds its environment, so
    /// the references of the value are the references of the captures.
    Made(ClosureId),
    /// A function value that parameter `i` of the body holds, or that is
    /// inside the value of the parameter (a field, an element, behind a
    /// reference): a value of a caller. A call of it is code of a caller,
    /// and the summary of the body runs it (part `runs`).
    Param(u32),
    /// The result of a run of a value of parameter `i` (`let g = m()`): a
    /// value that a run of the value of the caller gives back. A run of it
    /// is a run of the result, not of the parameter, so a `once` maker that
    /// the body runs one time, and whose result it runs one time, runs
    /// once (the W0502 class of the third review of the ABC preview).
    ParamResult(u32),
    /// A function value that capture `k` of the closure body holds, in the
    /// summary of the closure (its interface): the run node of the closure
    /// runs the value of the capture (part `runs`).
    Capture(u32),
    /// A value that the analysis does not know: code of a caller.
    Unknown,
}

/// The most function values that one value keeps.
///
/// With more, the items go and [`FnVal::Unknown`] takes their place: code of a caller
/// does each change that an item can do to the places that the node gives it. The other
/// values are finite (the closures and the parameters of a component), so a join ends
/// (the widening of `docs/ir.md` 6.6).
pub const FNS_MAX: usize = 32;

/// Widens the function set `fns` (see [`FNS_MAX`]).
fn widen_fns(fns: &mut BTreeSet<FnVal>) {
    if fns.len() > FNS_MAX {
        fns.retain(|f| !matches!(f, FnVal::Item(..)));
        fns.insert(FnVal::Unknown);
    }
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
        widen_fns(&mut self.fns);
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

    /// Each place of the value: the places of the top and of each part.
    pub fn places(&self, out: &mut BTreeSet<PlaceId>) {
        out.extend(self.top.refs.iter().copied());
        for k in self.kids.values() {
            k.places(out);
        }
    }

    /// Changes the places of the top and of each part with `f`. `f` gives
    /// true if it changed a set. Returns true if a set changed.
    pub fn map_refs(&mut self, f: &mut dyn FnMut(&mut BTreeSet<PlaceId>) -> bool) -> bool {
        let mut changed = f(&mut self.top.refs);
        for k in self.kids.values_mut() {
            changed |= k.map_refs(f);
        }
        changed
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
    vals: Chunked<Rc<Tree>>,
    /// The move paths that can hold a value.
    may: PathSet,
    /// The move paths that must hold a value, but for the holes below them.
    must: PathSet,
    /// The move paths that can have no value: a part that moved or that an
    /// `Uninit` left with no value (may).
    holes: PathSet,
    /// The heap slots (`docs/ir.md` 6.6): for each fact place that is not
    /// a place of a local of the component (behind a reference parameter,
    /// in a place of a caller), the places that the references stored
    /// there can point into (may; a store there is a weak update).
    behind: Rc<BTreeMap<PlaceId, BTreeSet<PlaceId>>>,
    /// The function values of the heap slots (stage F13): for each fact
    /// place that no local of the component owns, the function values that a
    /// store put there (may; a weak update). The places that their
    /// environments point into are in `behind`.
    behind_fns: Rc<BTreeMap<PlaceId, BTreeSet<FnVal>>>,
}

/// The number of locals of one chunk of a [`Chunked`] map.
const CHUNK: u32 = 64;

/// The key of the chunk of local `k`.
const fn chunk_of(k: Key) -> (BodyId, u32) {
    (k.0, k.1 .0 / CHUNK)
}

/// A map from locals to values that the states of the blocks share: the
/// locals go in chunks of [`CHUNK`], and a clone shares each chunk. A
/// change copies the map of the chunks and the one chunk that it changes.
/// So a body with many blocks and many locals (a long chain of calls, a
/// cleanup chain) keeps one copy of each chunk that no block changes, and a
/// clone of a state costs no copy of the values.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Chunked<V: Clone> {
    /// The chunks, by body and chunk number.
    chunks: Rc<Chunks<V>>,
}

/// The chunks of a [`Chunked`] map.
type Chunks<V> = BTreeMap<(BodyId, u32), Rc<BTreeMap<Key, V>>>;

/// The paths of one local in a [`PathSet`].
type Paths = Rc<BTreeSet<Vec<PathStep>>>;

impl<V: Clone> Default for Chunked<V> {
    fn default() -> Self {
        Self {
            chunks: Rc::new(BTreeMap::new()),
        }
    }
}

impl<V: Clone> Chunked<V> {
    /// The value of local `k`.
    fn get(&self, k: Key) -> Option<&V> {
        self.chunks.get(&chunk_of(k)).and_then(|c| c.get(&k))
    }

    /// Gives local `k` the value `v`.
    fn insert(&mut self, k: Key, v: V) {
        let chunk = Rc::make_mut(&mut self.chunks)
            .entry(chunk_of(k))
            .or_default();
        Rc::make_mut(chunk).insert(k, v);
    }

    /// The value of local `k` to change, with `f` for a new value.
    fn entry(&mut self, k: Key, f: impl FnOnce() -> V) -> &mut V {
        let chunk = Rc::make_mut(&mut self.chunks)
            .entry(chunk_of(k))
            .or_default();
        Rc::make_mut(chunk).entry(k).or_insert_with(f)
    }

    /// The value of local `k` to change, if it has one.
    fn get_mut(&mut self, k: Key) -> Option<&mut V> {
        self.get(k)?;
        let chunk = Rc::make_mut(&mut self.chunks).get_mut(&chunk_of(k))?;
        Rc::make_mut(chunk).get_mut(&k)
    }

    /// Removes the value of local `k`.
    fn remove(&mut self, k: Key) {
        if self.get(k).is_none() {
            return;
        }
        let chunks = Rc::make_mut(&mut self.chunks);
        let c = chunk_of(k);
        if let Some(chunk) = chunks.get_mut(&c) {
            Rc::make_mut(chunk).remove(&k);
            if chunk.is_empty() {
                chunks.remove(&c);
            }
        }
    }

    /// The locals and their values.
    fn iter(&self) -> impl Iterator<Item = (&Key, &V)> {
        self.chunks.values().flat_map(|chunk| chunk.iter())
    }

    /// The locals and their values, by chunk: a chunk that `o` shares with
    /// `self` is left out (for the joins).
    fn not_shared<'a>(&'a self, o: &'a Self) -> impl Iterator<Item = (&'a Key, &'a V)> {
        self.chunks
            .iter()
            .filter(move |(c, chunk)| o.chunks.get(c).is_none_or(|x| !Rc::ptr_eq(x, chunk)))
            .flat_map(|(_, chunk)| chunk.iter())
    }
}

/// A set of move paths, by local. The set of each local is shared between
/// the states of the blocks, as the trees of [`State`] are: a change copies
/// the set of one local.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct PathSet(Chunked<Paths>);

impl PathSet {
    /// Adds the path `path` of local `key`.
    fn insert(&mut self, key: Key, path: &[PathStep]) {
        if self.0.get(key).is_some_and(|s| s.contains(path)) {
            return;
        }
        let set = self.0.entry(key, Rc::default);
        Rc::make_mut(set).insert(path.to_vec());
    }

    /// Removes the paths of local `key` at or below `path`.
    fn remove_below(&mut self, key: Key, path: &[PathStep]) {
        let Some(set) = self.0.get(key) else {
            return;
        };
        if !set.iter().any(|p| is_prefix(path, p)) {
            return;
        }
        let kept: BTreeSet<Vec<PathStep>> = set
            .iter()
            .filter(|p| !is_prefix(path, p))
            .cloned()
            .collect();
        if kept.is_empty() {
            self.0.remove(key);
        } else {
            self.0.insert(key, Rc::new(kept));
        }
    }

    /// The paths of local `key`.
    fn of(&self, key: Key) -> impl Iterator<Item = &Vec<PathStep>> {
        self.0.get(key).into_iter().flat_map(|s| s.iter())
    }

    /// Adds each path of `o`. Returns true if `self` changed.
    fn union(&mut self, o: &Self) -> bool {
        let mut new: Vec<(Key, Paths)> = Vec::new();
        for (k, theirs) in o.0.not_shared(&self.0) {
            match self.0.get(*k) {
                Some(mine) if Rc::ptr_eq(mine, theirs) => {}
                Some(mine) => {
                    if !theirs.iter().all(|p| mine.contains(p)) {
                        let mut all = (**mine).clone();
                        all.extend(theirs.iter().cloned());
                        new.push((*k, Rc::new(all)));
                    }
                }
                None => new.push((*k, Rc::clone(theirs))),
            }
        }
        let changed = !new.is_empty();
        for (k, v) in new {
            self.0.insert(k, v);
        }
        changed
    }

    /// Keeps only the paths that `o` has too. Returns true if `self`
    /// changed.
    fn intersect(&mut self, o: &Self) -> bool {
        let mut new: Vec<(Key, Option<Paths>)> = Vec::new();
        for (k, mine) in self.0.not_shared(&o.0) {
            match o.0.get(*k) {
                Some(theirs) if Rc::ptr_eq(mine, theirs) => {}
                Some(theirs) => {
                    if mine.iter().any(|p| !theirs.contains(p)) {
                        let kept: BTreeSet<Vec<PathStep>> = mine
                            .iter()
                            .filter(|p| theirs.contains(*p))
                            .cloned()
                            .collect();
                        new.push((*k, (!kept.is_empty()).then(|| Rc::new(kept))));
                    }
                }
                None => new.push((*k, None)),
            }
        }
        let changed = !new.is_empty();
        for (k, v) in new {
            match v {
                Some(v) => self.0.insert(k, v),
                None => self.0.remove(k),
            }
        }
        changed
    }
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
        self.vals.get(key).map_or_else(Tree::none, |t| t.get(path))
    }

    /// The tree of local `key`, if it has one.
    pub fn tree(&self, key: Key) -> Option<&Tree> {
        self.vals.get(key).map(Rc::as_ref)
    }

    /// Gives local `key` the value `v` and no may part, must part or holes:
    /// the local ended, but a closure that captured it keeps the value that
    /// it had (a `Kept` or a `ByRef` capture of a local of a handled body
    /// that runs after the `handle`, plan stage F15).
    pub fn keep_value(&mut self, key: Key, v: Tree) {
        *self.vals.entry(key, || Rc::new(Tree::none())) = Rc::new(v);
    }

    /// Gives the move path `path` of local `key` the value `v` (a strong
    /// update): it can and must hold a value now, and its parts get the
    /// parts of `v`.
    pub fn write(&mut self, key: Key, path: &[PathStep], v: Tree) {
        Rc::make_mut(self.vals.entry(key, || Rc::new(Tree::none()))).set(path, v);
        self.may.remove_below(key, path);
        self.must.remove_below(key, path);
        self.holes.remove_below(key, path);
        self.may.insert(key, path);
        self.must.insert(key, path);
    }

    /// Joins `v` into the move path `path` of local `key` (a weak update:
    /// a store through a reference or into an element). The path can hold a
    /// value now.
    pub fn add(&mut self, key: Key, path: &[PathStep], v: &Tree) {
        Rc::make_mut(self.vals.entry(key, || Rc::new(Tree::none()))).add(path, v);
        self.may.insert(key, path);
    }

    /// The move path `path` of local `key` has no value now: a move, a
    /// `Consume`, an `Uninit`. With an empty path, the whole local.
    pub fn clear(&mut self, key: Key, path: &[PathStep]) {
        self.may.remove_below(key, path);
        self.must.remove_below(key, path);
        self.holes.remove_below(key, path);
        if path.is_empty() {
            self.vals.remove(key);
        } else {
            if let Some(t) = self.vals.get_mut(key) {
                Rc::make_mut(t).set(path, Tree::none());
            }
            // The paths above the cleared part keep their other parts.
            self.holes.insert(key, path);
        }
    }

    /// Adds a hole at the move path `path` of local `key`: the part can have
    /// no value (a part of a moved value that had no value).
    pub fn add_hole(&mut self, key: Key, path: &[PathStep]) {
        self.holes.insert(key, path);
    }

    /// The holes of local `key` at or below the move path `path`, relative
    /// to `path`.
    pub fn holes_below(&self, key: Key, path: &[PathStep]) -> Vec<Vec<PathStep>> {
        self.holes
            .of(key)
            .filter(|p| is_prefix(path, p))
            .filter_map(|p| p.get(path.len()..).map(<[PathStep]>::to_vec))
            .collect()
    }

    /// True if local `key` can hold a value, or a value of a part.
    pub fn may_hold(&self, key: Key) -> bool {
        self.may.of(key).next().is_some()
    }

    /// True if the move path `path` of local `key` must hold a value: the
    /// path or a path above it got a value on each path to this point, and
    /// no hole overlaps the path.
    pub fn must_hold(&self, key: Key, path: &[PathStep]) -> bool {
        self.must.of(key).any(|p| is_prefix(p, path))
            && !self
                .holes
                .of(key)
                .any(|p| is_prefix(p, path) || is_prefix(path, p))
    }

    /// The places of the value of each local: the places of each part of
    /// its tree (for the widening at a loop head, `super::widen`).
    pub fn places(&self) -> BTreeMap<Key, BTreeSet<PlaceId>> {
        let mut out: BTreeMap<Key, BTreeSet<PlaceId>> = BTreeMap::new();
        for (k, t) in self.vals.iter() {
            let mut ps = BTreeSet::new();
            t.places(&mut ps);
            if !ps.is_empty() {
                out.insert(*k, ps);
            }
        }
        out
    }

    /// Changes the places of each part of the value of local `key` with
    /// `f` (`super::widen`). Only a tree that changes is copied.
    pub fn map_refs(&mut self, key: Key, f: &mut dyn FnMut(&mut BTreeSet<PlaceId>) -> bool) {
        let Some(t) = self.vals.get(key) else {
            return;
        };
        let mut copy = (**t).clone();
        if copy.map_refs(f) {
            self.vals.insert(key, Rc::new(copy));
        }
    }

    /// Removes the value, the may part, the must part and the holes of each
    /// local of a body for which `of` is true: the locals of a frame that
    /// ended (a handled body, a clause, plan stage F14).
    pub fn remove_bodies(&mut self, of: &dyn Fn(BodyId) -> bool) {
        let keys: BTreeSet<Key> = self
            .vals
            .iter()
            .map(|(k, _)| *k)
            .chain(self.may.0.iter().map(|(k, _)| *k))
            .chain(self.must.0.iter().map(|(k, _)| *k))
            .chain(self.holes.0.iter().map(|(k, _)| *k))
            .filter(|k| of(k.0))
            .collect();
        for k in keys {
            self.vals.remove(k);
            self.may.0.remove(k);
            self.must.0.remove(k);
            self.holes.0.remove(k);
        }
    }

    /// A copy of `self` where each local of a body for which `of` is true has
    /// its value, its may part, its must part and its holes from `o`: the
    /// locals of a clause keep their values across a `resume`, and the
    /// other locals get the values at the end of the handled body (plan
    /// stage F14).
    #[must_use]
    pub fn with_bodies_of(&self, o: &Self, of: &dyn Fn(BodyId) -> bool) -> Self {
        let mut out = self.clone();
        out.remove_bodies(of);
        for (k, t) in o.vals.iter() {
            if of(k.0) {
                out.vals.insert(*k, Rc::clone(t));
            }
        }
        for (k, ps) in o.may.0.iter() {
            if of(k.0) {
                out.may.0.insert(*k, Rc::clone(ps));
            }
        }
        for (k, ps) in o.must.0.iter() {
            if of(k.0) {
                out.must.0.insert(*k, Rc::clone(ps));
            }
        }
        for (k, ps) in o.holes.0.iter() {
            if of(k.0) {
                out.holes.0.insert(*k, Rc::clone(ps));
            }
        }
        out
    }

    /// Joins the value in `o` of each local of a body for which `of` is
    /// false into its value in `self`, if `self` has one. The may parts, the
    /// must parts and the holes stay. After a `resume`, a local of the site
    /// has its value at the end of the handled body (in the terms of the
    /// site) and its value at the resume point (in the terms of the clause:
    /// a reference that the clause put there points below a parameter of
    /// the clause, plan stage F14).
    pub fn join_values_but(&mut self, o: &Self, of: &dyn Fn(BodyId) -> bool) {
        let mut new: Vec<(Key, Rc<Tree>)> = Vec::new();
        for (k, t) in o.vals.iter() {
            if of(k.0) {
                continue;
            }
            if let Some(mine) = self.vals.get(*k) {
                if Rc::ptr_eq(mine, t) || **mine == **t {
                    continue;
                }
                let mut j = (**mine).clone();
                if j.join(t) {
                    new.push((*k, Rc::new(j)));
                }
            }
        }
        for (k, t) in new {
            self.vals.insert(k, t);
        }
    }

    /// Joins `o` into `self`: a union of the values and of the may parts,
    /// and an intersection of the must parts. Returns true if `self`
    /// changed.
    pub fn join(&mut self, o: &Self) -> bool {
        let mut new: Vec<(Key, Rc<Tree>)> = Vec::new();
        for (k, t) in o.vals.not_shared(&self.vals) {
            match self.vals.get(*k) {
                Some(mine) if Rc::ptr_eq(mine, t) || **mine == **t => {}
                Some(mine) => {
                    let mut joined = (**mine).clone();
                    if joined.join(t) {
                        new.push((*k, Rc::new(joined)));
                    }
                }
                None => new.push((*k, Rc::clone(t))),
            }
        }
        let mut changed = !new.is_empty();
        for (k, t) in new {
            self.vals.insert(k, t);
        }
        changed |= self.may.union(&o.may);
        changed |= self.must.intersect(&o.must);
        changed |= self.holes.union(&o.holes);
        if !Rc::ptr_eq(&self.behind, &o.behind) {
            for (q, refs) in o.behind.iter() {
                changed |= self.store_behind(*q, refs.iter().copied());
            }
        }
        if !Rc::ptr_eq(&self.behind_fns, &o.behind_fns) {
            for (q, fns) in o.behind_fns.iter() {
                changed |= self.store_fns_behind(*q, fns.iter().cloned());
            }
        }
        changed
    }

    /// A store of the function values `fns` at the fact place `q` that no
    /// local of the component owns (a heap slot, stage F13). Returns true if
    /// the slot changed. A slot with more than [`FNS_MAX`] values widens.
    pub fn store_fns_behind(&mut self, q: PlaceId, fns: impl IntoIterator<Item = FnVal>) -> bool {
        let new: Vec<FnVal> = fns
            .into_iter()
            .filter(|f| self.behind_fns.get(&q).is_none_or(|have| !have.contains(f)))
            .collect();
        if new.is_empty() {
            return false;
        }
        let slot = Rc::make_mut(&mut self.behind_fns).entry(q).or_default();
        let before = slot.clone();
        slot.extend(new);
        widen_fns(slot);
        *slot != before
    }

    /// The function values of the heap slots: each place that got a store of
    /// a function value, and the values (stage F13).
    pub fn behind_fns(&self) -> &BTreeMap<PlaceId, BTreeSet<FnVal>> {
        &self.behind_fns
    }

    /// A store of references that point into `refs` at the fact place `q`
    /// that no local of the component owns (a heap slot). Returns true if
    /// the slot changed.
    pub fn store_behind(&mut self, q: PlaceId, refs: impl IntoIterator<Item = PlaceId>) -> bool {
        let new: Vec<PlaceId> = refs
            .into_iter()
            .filter(|r| self.behind.get(&q).is_none_or(|have| !have.contains(r)))
            .collect();
        if new.is_empty() {
            return false;
        }
        Rc::make_mut(&mut self.behind)
            .entry(q)
            .or_default()
            .extend(new);
        true
    }

    /// The heap slots: each place that got a store, and the places that the
    /// stored references can point into.
    pub fn behind(&self) -> &BTreeMap<PlaceId, BTreeSet<PlaceId>> {
        &self.behind
    }

    /// Changes the places of each heap slot with `f` (`super::widen`). `f`
    /// gets the place of the slot and gives true if it changed the set.
    pub fn map_behind(&mut self, f: &mut dyn FnMut(PlaceId, &mut BTreeSet<PlaceId>) -> bool) {
        let mut copy = (*self.behind).clone();
        let mut changed = false;
        for (q, refs) in &mut copy {
            changed |= f(*q, refs);
        }
        if changed {
            self.behind = Rc::new(copy);
        }
    }
}
