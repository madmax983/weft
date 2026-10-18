//! Soundness of Weft's algebraic effects, machine-checked in Verus.
//! See `README.md` for the model, the theorems and the limitations.

pub mod model;
pub mod checker;
pub mod scope;
pub mod scope_steps;
pub mod lexical;
pub mod own;
pub mod own_steps;
pub mod safety;
pub mod progress;
pub mod examples;
