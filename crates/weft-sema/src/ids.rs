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
