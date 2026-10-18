//! B6: proofs that link the verified exec core to the proof models.
//! See `README.md` for the theorems and the limits.
//!
//! The crate includes the source files of the three developments with
//! `#[path]`. It does not copy them. Thus each proof here is about the exact
//! code and the exact model definitions. A change to an included file can
//! break this crate. Then the link is broken, and `verify.sh` fails.
//! `check-copies.sh` checks that each included file is a module of its home
//! crate, and that this crate has no copy of an included item.

// The verified exec core: the code that the checker and the interpreter run.
// Source: crates/weft-verified/src/.
#[path = "../../../crates/weft-verified/src/places.rs"]
pub mod places;
#[path = "../../../crates/weft-verified/src/dataflow.rs"]
pub mod dataflow;
#[path = "../../../crates/weft-verified/src/lifecycle.rs"]
pub mod lifecycle;

// The group-borrowing model: the base model, its soundness, B1 (CFG) and B3
// (layout). Source: proofs/borrowing/src/. The names stay the same, because
// `cfg.rs` and `layout.rs` refer to `crate::model` and `crate::soundness`.
#[path = "../../borrowing/src/model.rs"]
pub mod model;
#[path = "../../borrowing/src/soundness.rs"]
pub mod soundness;
#[path = "../../borrowing/src/cfg.rs"]
pub mod cfg;
#[path = "../../borrowing/src/layout.rs"]
pub mod layout;

// The effects model: the abstract machine. Source: proofs/effects/src/model.rs.
#[path = "../../effects/src/model.rs"]
pub mod effects_model;

/// L1: rule 3 and the B3 kill predicate.
pub mod places_link;
/// L2: `propagate` and the B1 CFG checker.
pub mod dataflow_link;
/// L3: the lifecycle state machines and the effects machine.
pub mod lifecycle_link;
/// Vacuity guards and gap witnesses.
pub mod examples;
