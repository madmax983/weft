//! The roots of the argument places of a call: the third part of
//! `call_arg(P, A, I)` and `call_mut(P, M, I)`.
//!
//! W0312 compares the places of one call that have different roots. Two places
//! with one root are parts of one argument, so they can overlap. Each kind of
//! root has a range of its own, so two kinds never share a root.

use weft_facts::CapId;

use crate::types::AdtId;

/// The size of the range of each kind. No call has as many parameters, and no
/// program has as many types or handlers: each of them takes more than a byte
/// of source. A round number keeps the roots easy to read in a derivation.
const KIND: u32 = 1_000_000;

/// The index `i` in the range of a kind.
fn index(i: usize) -> u32 {
    u32::try_from(i).map_or(KIND - 1, |i| i.min(KIND - 1))
}

/// The root of parameter `i`. A parameter whose place is in another parameter
/// has the root of that parameter (`Lower::sig_root`).
pub fn param(i: usize) -> u32 {
    index(i)
}

/// The root of what function value argument `i` reaches: the places that the
/// value gets, and the places that the argument holds.
pub fn fn_arg(i: usize) -> u32 {
    KIND + index(i)
}

/// The root of the `rc` group of type `a`.
pub fn group(a: AdtId) -> u32 {
    2 * KIND + index(a)
}

/// The root of the footprint of the clauses of the handler with capability
/// `c`, at a call that reaches the handler.
pub fn clause(c: CapId) -> u32 {
    3 * KIND + c.0.min(KIND - 1)
}

/// The root of a function value that the call runs and that is not an
/// argument: a stored value, the value that the call runs, or a value inside
/// an argument that is not a callback.
pub const STORED: u32 = 4 * KIND;

#[cfg(test)]
mod tests {
    use super::*;

    /// The kinds of roots do not overlap, also at the ends of their ranges.
    #[test]
    fn the_kinds_of_roots_are_apart() {
        for i in [0, 1, 10, 100, 800, KIND as usize, usize::MAX] {
            assert_eq!(param(i) / KIND, 0);
            assert_eq!(fn_arg(i) / KIND, 1);
            assert_eq!(group(i) / KIND, 2);
        }
        for c in [0, 1, 1000, u32::MAX] {
            assert_eq!(clause(CapId(c)) / KIND, 3);
        }
        assert_eq!(STORED / KIND, 4);
        // The first roots: the old numbers 800 + i, 810 + i, 900 + a and
        // 1000 + c could be equal for two kinds.
        assert_ne!(fn_arg(0), STORED);
        assert_ne!(param(800), fn_arg(0));
        assert_ne!(fn_arg(100), group(0));
        assert_ne!(group(100), clause(CapId(0)));
        assert_eq!((param(3), fn_arg(3)), (3, KIND + 3));
    }
}
