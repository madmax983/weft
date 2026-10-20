//! The verified core of the Weft checker.
//!
//! Verus proves the code in this crate. A normal `cargo build` compiles the same
//! code: the `verus!` macro removes specs and proofs. The production checker and
//! the interpreter call these functions.
//!
//! Verify with `verus crates/weft-verified/src/lib.rs --crate-type=lib`.

pub mod dataflow;
pub mod lifecycle;
pub mod modes;
pub mod places;
