//! Tuple storage with hash indexes.
//!
//! A relation keeps its tuples in one flat vector, row after row. Rows are
//! never removed, so a row id is stable. Each index maps the hash of some
//! key columns to the newest row with that hash. A `next` array links each
//! row to the previous row with the same hash. Index 0 covers all columns
//! and removes duplicates.

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

use crate::value::Value;

/// The end of a hash chain.
pub const NONE: u32 = u32::MAX;

/// The provenance tag of a fact from the program text.
pub const FACT: u32 = u32::MAX;

/// Converts a count to `u32`.
///
/// # Panics
///
/// Panics if `n` is `u32::MAX` or more. Relations and the interner do not
/// support so many items.
pub fn to_u32(n: usize) -> u32 {
    match u32::try_from(n) {
        Ok(v) if v != NONE => v,
        _ => panic!("weft-datalog supports fewer than {NONE} items, not {n}"),
    }
}

/// A hasher for keys that are hashes already.
#[derive(Clone, Copy, Debug, Default)]
pub struct IdHasher(u64);

impl Hasher for IdHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = self.0.rotate_left(8) ^ u64::from(b);
        }
    }

    fn write_u64(&mut self, n: u64) {
        self.0 = n;
    }
}

type IdMap = HashMap<u64, u32, BuildHasherDefault<IdHasher>>;

const SEED: u64 = 0x243f_6a88_85a3_08d3;
const MULTIPLIER: u64 = 0x517c_c1b7_2722_0a95;
const SYMBOL_SALT: u64 = 0x9e37_79b9_7f4a_7c15;

/// Hashes a sequence of values. The result is well mixed in all bits.
pub fn hash_values(values: impl IntoIterator<Item = Value>) -> u64 {
    let mut h = SEED;
    for v in values {
        let word = match v {
            Value::Int(i) => u64::from_ne_bytes(i.to_ne_bytes()),
            Value::Sym(s) => u64::from(s.index()) ^ SYMBOL_SALT,
        };
        h = (h.rotate_left(5) ^ word).wrapping_mul(MULTIPLIER);
    }
    // The finalizer of MurmurHash3.
    h ^= h >> 33;
    h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
    h ^= h >> 33;
    h = h.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    h ^ (h >> 33)
}

#[derive(Clone, Debug)]
struct Index {
    cols: Vec<usize>,
    heads: IdMap,
    next: Vec<u32>,
}

impl Index {
    fn key_hash(&self, row: &[Value]) -> u64 {
        hash_values(self.cols.iter().map(|&c| row[c]))
    }

    fn push(&mut self, hash: u64, row: u32) {
        let prev = self.heads.insert(hash, row).unwrap_or(NONE);
        self.next.push(prev);
    }
}

/// The rows of one hash chain, newest first. The rows can have different
/// keys with the same hash, so the caller must compare the key columns.
pub struct Chain<'a> {
    next: &'a [u32],
    cur: u32,
}

impl Iterator for Chain<'_> {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        if self.cur == NONE {
            return None;
        }
        let row = self.cur;
        self.cur = self.next[row as usize];
        Some(row)
    }
}

/// The first derivation of a row: a rule index (or [`FACT`]) and the start
/// of its premise rows in the premise arena.
#[derive(Clone, Copy, Debug)]
struct Prov {
    rule: u32,
    start: u32,
}

/// The tuples of one relation.
#[derive(Clone, Debug)]
pub struct Relation {
    /// The relation name.
    pub name: String,
    /// The number of columns.
    pub arity: usize,
    data: Vec<Value>,
    len: usize,
    indexes: Vec<Index>,
    /// Rows before this row are input facts. Later rows have provenance
    /// entries when provenance is on.
    pub input_rows: usize,
    prov: Vec<Prov>,
    premises: Vec<u32>,
}

impl Relation {
    /// Makes an empty relation.
    pub fn new(name: &str, arity: usize) -> Self {
        Self {
            name: name.to_string(),
            arity,
            data: Vec::new(),
            len: 0,
            indexes: vec![Index {
                cols: (0..arity).collect(),
                heads: IdMap::default(),
                next: Vec::new(),
            }],
            input_rows: 0,
            prov: Vec::new(),
            premises: Vec::new(),
        }
    }

    /// Returns the number of rows.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns the values of a row.
    pub fn row(&self, row: u32) -> &[Value] {
        let start = row as usize * self.arity;
        &self.data[start..start + self.arity]
    }

    /// Returns all rows in insertion order.
    pub fn rows(&self) -> impl Iterator<Item = &[Value]> {
        (0..to_u32(self.len)).map(|r| self.row(r))
    }

    /// Returns the rows in the chain of `hash` in index `index`.
    pub fn chain(&self, index: usize, hash: u64) -> Chain<'_> {
        let index = &self.indexes[index];
        Chain {
            next: &index.next,
            cur: index.heads.get(&hash).copied().unwrap_or(NONE),
        }
    }

    /// Returns the row of `tuple`. `hash` is `hash_values(tuple)`.
    pub fn find(&self, tuple: &[Value], hash: u64) -> Option<u32> {
        self.chain(0, hash).find(|&r| self.row(r) == tuple)
    }

    /// Returns the row of `tuple`, or `None` if the relation does not have it.
    pub fn find_tuple(&self, tuple: &[Value]) -> Option<u32> {
        if tuple.len() != self.arity {
            return None;
        }
        self.find(tuple, hash_values(tuple.iter().copied()))
    }

    /// Adds `tuple` if it is new. `hash` is `hash_values(tuple)`. Returns
    /// `true` if the tuple is new.
    pub fn insert(&mut self, tuple: &[Value], hash: u64) -> bool {
        if self.find(tuple, hash).is_some() {
            return false;
        }
        let row = to_u32(self.len);
        self.data.extend_from_slice(tuple);
        self.len += 1;
        let (all, others) = self.indexes.split_at_mut(1);
        all[0].push(hash, row);
        for index in others {
            let h = index.key_hash(tuple);
            index.push(h, row);
        }
        true
    }

    /// Returns the id of an index on `cols`. Makes the index if necessary.
    pub fn ensure_index(&mut self, cols: &[usize]) -> usize {
        if let Some(id) = self.indexes.iter().position(|i| i.cols == cols) {
            return id;
        }
        let mut index = Index {
            cols: cols.to_vec(),
            heads: IdMap::default(),
            next: Vec::with_capacity(self.len),
        };
        for r in 0..to_u32(self.len) {
            let h = index.key_hash(self.row(r));
            index.push(h, r);
        }
        self.indexes.push(index);
        self.indexes.len() - 1
    }

    /// Records the provenance of the newest row.
    pub fn push_prov(&mut self, rule: u32, premises: &[u32]) {
        self.prov.push(Prov {
            rule,
            start: to_u32(self.premises.len()),
        });
        self.premises.extend_from_slice(premises);
    }

    /// Returns the provenance of `row`: the rule (or [`FACT`]) and the
    /// premise rows. For a program fact, the only premise is the fact index.
    /// Returns `None` for an input row, or if provenance is off.
    pub fn prov(&self, row: u32) -> Option<(u32, &[u32])> {
        let i = (row as usize).checked_sub(self.input_rows)?;
        let entry = self.prov.get(i)?;
        let end = self
            .prov
            .get(i + 1)
            .map_or(self.premises.len(), |next| next.start as usize);
        Some((entry.rule, &self.premises[entry.start as usize..end]))
    }
}

#[cfg(test)]
mod tests {
    use std::hash::BuildHasher;

    use super::*;

    #[test]
    fn id_hasher_mixes_bytes() {
        let build = BuildHasherDefault::<IdHasher>::default();
        assert_eq!(build.hash_one(7_u64), 7);
        assert_ne!(build.hash_one("ab"), build.hash_one("ba"));
    }

    #[test]
    fn indexes_find_rows_by_key() {
        let mut r = Relation::new("r", 2);
        let t = |a, b| [Value::Int(a), Value::Int(b)];
        for (a, b) in [(1, 2), (1, 3), (2, 3)] {
            assert!(r.insert(&t(a, b), hash_values(t(a, b))));
        }
        assert!(!r.insert(&t(1, 2), hash_values(t(1, 2))));
        let by_first = r.ensure_index(&[0]);
        assert_eq!(r.ensure_index(&[0]), by_first);
        let rows: Vec<u32> = r.chain(by_first, hash_values([Value::Int(1)])).collect();
        assert_eq!(rows, [1, 0]);
        assert!(r.insert(&t(1, 4), hash_values(t(1, 4))));
        assert_eq!(r.chain(by_first, hash_values([Value::Int(1)])).count(), 3);
        assert_eq!(r.find_tuple(&t(2, 3)), Some(2));
        assert_eq!(r.find_tuple(&[Value::Int(2)]), None);
        assert_eq!(r.rows().count(), 4);
    }

    #[test]
    fn nullary_relations_hold_one_row() {
        let mut r = Relation::new("n", 0);
        assert!(r.insert(&[], hash_values([])));
        assert!(!r.insert(&[], hash_values([])));
        assert_eq!(r.len(), 1);
        assert_eq!(r.row(0), &[] as &[Value]);
    }

    #[test]
    fn stores_provenance_after_input_rows() {
        let mut r = Relation::new("r", 1);
        r.insert(&[Value::Int(0)], hash_values([Value::Int(0)]));
        r.input_rows = 1;
        r.insert(&[Value::Int(1)], hash_values([Value::Int(1)]));
        r.push_prov(3, &[7, 8]);
        r.insert(&[Value::Int(2)], hash_values([Value::Int(2)]));
        r.push_prov(FACT, &[0]);
        assert_eq!(r.prov(0), None);
        assert_eq!(r.prov(1), Some((3, &[7, 8][..])));
        assert_eq!(r.prov(2), Some((FACT, &[0][..])));
        assert_eq!(r.prov(3), None);
    }

    #[test]
    #[should_panic(expected = "fewer than")]
    fn rejects_huge_counts() {
        let _ = to_u32(u32::MAX as usize);
    }
}
