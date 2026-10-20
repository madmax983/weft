//! The indexes of the tables of a [`Program`](crate::Program): functions,
//! modules, effects and type definitions.
//!
//! Each index has a type of its own, so an index of one table cannot index
//! another table. A table of a program can take its index type in `[]`:
//!
//! ```
//! fn name(p: &weft_sema::Program, f: weft_sema::FnId) -> &str {
//!     &p.fns[f].name
//! }
//! ```
//!
//! ```compile_fail
//! fn name(p: &weft_sema::Program, f: weft_sema::FnId) -> &str {
//!     &p.mods[f].name
//! }
//! ```

use crate::program::{AdtDef, EffectDef, FnDef, FnSig, ModDef};

/// Makes an index type.
macro_rules! index_type {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub usize);

        impl $name {
            /// Returns the index into the table.
            pub const fn index(self) -> usize {
                self.0
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
            }
        }
    };
}

/// Lets a table of `$elem`, a slice or a `Vec`, take `$id` in `[]`.
macro_rules! index_table {
    ($id:ty => $($elem:ty),+) => {
        $(
            impl std::ops::Index<$id> for [$elem] {
                type Output = $elem;

                fn index(&self, i: $id) -> &$elem {
                    &self[i.0]
                }
            }

            impl std::ops::IndexMut<$id> for [$elem] {
                fn index_mut(&mut self, i: $id) -> &mut $elem {
                    &mut self[i.0]
                }
            }

            impl std::ops::Index<$id> for Vec<$elem> {
                type Output = $elem;

                fn index(&self, i: $id) -> &$elem {
                    &self[i.0]
                }
            }

            impl std::ops::IndexMut<$id> for Vec<$elem> {
                fn index_mut(&mut self, i: $id) -> &mut $elem {
                    &mut self[i.0]
                }
            }
        )+
    };
}

index_type!(
    /// An index into [`Program::fns`](crate::Program::fns) and the
    /// signatures.
    FnId
);
index_type!(
    /// An index into [`Program::mods`](crate::Program::mods).
    ModId
);
index_type!(
    /// An index into [`Program::effects`](crate::Program::effects).
    EffectId
);
index_type!(
    /// An index into [`Program::adts`](crate::Program::adts): a struct, an
    /// enum or an extern type.
    AdtId
);

index_table!(FnId => FnDef, FnSig);
index_table!(ModId => ModDef);
index_table!(EffectId => EffectDef);
index_table!(AdtId => AdtDef);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Program;

    /// A table takes its own index, as a slice and as a `Vec`, to read and to
    /// write. An index shows as its number.
    #[test]
    fn a_table_takes_its_own_index() {
        let Ok(unit) = crate::prelude_unit() else {
            panic!("the prelude parses");
        };
        let a = crate::analyze(&[unit], crate::Options::default());
        let mut prog: Program = a.program;
        let f = FnId(0);
        let name = prog.fns[f].name.clone();
        prog.fns[f].name.push('x');
        assert_eq!(prog.fns.as_slice()[f].name, format!("{name}x"));
        prog.fns.as_mut_slice()[f].name.pop();
        assert_eq!(prog.fns[f].name, name);
        let mut sigs = a.sigs;
        sigs.as_mut_slice()[f].generics.push("T".into());
        assert_eq!(sigs[f].generics.last().map(String::as_str), Some("T"));
        assert_eq!(f.index(), 0);
        assert_eq!(AdtId(7).to_string(), "7");
        assert_eq!(prog.fn_ids().count(), prog.fns.len());
        assert_eq!(prog.adt_ids().count(), prog.adts.len());
        assert_eq!(prog.effect_ids().count(), prog.effects.len());
        assert!(ModId(0) < ModId(1) && EffectId::default() == EffectId(0));
    }
}
