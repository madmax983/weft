//! The mode lattice.
//!
//! A mode has four axes. On each axis the first value is the better one. A value
//! with a better mode can be used where a worse mode is expected (submoding).
//!
//! | Axis | Better | Worse |
//! | --- | --- | --- |
//! | Uniqueness | `uniq` | `aliased` |
//! | Portability | `portable` | `nonportable` |
//! | Contention | `uncontended` | `shared` |
//! | Affinity | `many` | `once` |

use vstd::prelude::*;

verus! {

/// A mode: one value on each axis.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Modes {
    /// True for `aliased`, false for `uniq`.
    pub aliased: bool,
    /// True for `nonportable`, false for `portable`.
    pub nonportable: bool,
    /// True for `shared`, false for `uncontended`.
    pub shared: bool,
    /// True for `once`, false for `many`.
    pub once: bool,
}

/// The best mode on every axis. Plain immutable data has this mode.
pub open spec fn spec_bottom() -> Modes {
    Modes { aliased: false, nonportable: false, shared: false, once: false }
}

/// `a` can be used where `b` is expected.
pub open spec fn spec_submode(a: Modes, b: Modes) -> bool {
    (a.aliased ==> b.aliased) && (a.nonportable ==> b.nonportable) && (a.shared ==> b.shared) && (
    a.once ==> b.once)
}

/// The least mode above `a` and `b`.
pub open spec fn spec_join(a: Modes, b: Modes) -> Modes {
    Modes {
        aliased: a.aliased || b.aliased,
        nonportable: a.nonportable || b.nonportable,
        shared: a.shared || b.shared,
        once: a.once || b.once,
    }
}

/// Returns the best mode on every axis.
pub const fn bottom() -> (r: Modes)
    ensures
        r == spec_bottom(),
{
    Modes { aliased: false, nonportable: false, shared: false, once: false }
}

/// Returns true if `a` can be used where `b` is expected.
pub const fn submode(a: &Modes, b: &Modes) -> (r: bool)
    ensures
        r == spec_submode(*a, *b),
{
    (!a.aliased || b.aliased) && (!a.nonportable || b.nonportable) && (!a.shared || b.shared) && (
    !a.once || b.once)
}

/// Returns the least mode above `a` and `b`.
pub const fn join(a: &Modes, b: &Modes) -> (r: Modes)
    ensures
        r == spec_join(*a, *b),
{
    Modes {
        aliased: a.aliased || b.aliased,
        nonportable: a.nonportable || b.nonportable,
        shared: a.shared || b.shared,
        once: a.once || b.once,
    }
}

/// Submoding is reflexive.
pub proof fn lemma_submode_reflexive(a: Modes)
    ensures
        spec_submode(a, a),
{
}

/// Submoding is transitive.
pub proof fn lemma_submode_transitive(a: Modes, b: Modes, c: Modes)
    requires
        spec_submode(a, b),
        spec_submode(b, c),
    ensures
        spec_submode(a, c),
{
}

/// Submoding is antisymmetric.
pub proof fn lemma_submode_antisymmetric(a: Modes, b: Modes)
    requires
        spec_submode(a, b),
        spec_submode(b, a),
    ensures
        a == b,
{
}

/// The join is the least upper bound.
pub proof fn lemma_join_is_lub(a: Modes, b: Modes, c: Modes)
    ensures
        spec_submode(a, spec_join(a, b)),
        spec_submode(b, spec_join(a, b)),
        spec_submode(a, c) && spec_submode(b, c) ==> spec_submode(spec_join(a, b), c),
{
}

/// Mode crossing: plain immutable data can be used at every mode.
pub proof fn lemma_bottom_crosses(b: Modes)
    ensures
        spec_submode(spec_bottom(), b),
{
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    // One flag for each mode axis, in the order of the fields of `Modes`.
    #[allow(clippy::fn_params_excessive_bools)]
    const fn m(aliased: bool, nonportable: bool, shared: bool, once: bool) -> Modes {
        Modes {
            aliased,
            nonportable,
            shared,
            once,
        }
    }

    #[test]
    fn uniq_value_can_be_used_as_aliased() {
        assert!(submode(
            &m(false, false, false, false),
            &m(true, false, false, false)
        ));
        assert!(!submode(
            &m(true, false, false, false),
            &m(false, false, false, false)
        ));
    }

    #[test]
    fn join_takes_the_worse_value() {
        let j = join(&m(true, false, false, true), &m(false, true, false, false));
        assert_eq!(j, m(true, true, false, true));
        assert!(submode(&bottom(), &j));
    }
}
