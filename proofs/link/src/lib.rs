//! B6: proofs that link the verified exec core to the proof models.
//! See `README.md` for the theorems and the limits.
//!
//! The crate includes the source files of the three developments with
//! `#[path]`. It does not copy them. Thus each proof here is about the exact
//! code and the exact model definitions. A change to an included file can
//! break this crate. Then the link is broken, and `verify.sh` fails.
//! `check-copies.sh` checks that this file includes the expected files, that
//! each included file is a module of its home crate, and that this crate has
//! no copy of an included item. `verify.sh` runs it first.

// The verified exec core: the code that the checker and the interpreter run.
// Source: crates/weft-verified/src/.
#[path = "../../../crates/weft-verified/src/places.rs"]
pub mod places;
#[path = "../../../crates/weft-verified/src/dataflow.rs"]
pub mod dataflow;
#[path = "../../../crates/weft-verified/src/lifecycle.rs"]
pub mod lifecycle;

// The group-borrowing model: the base model, its soundness, B1 (CFG) and B3
// (layout, its soundness proof and its examples). Source:
// proofs/borrowing/src/. The names stay the same, because the files refer to
// `crate::model`, `crate::soundness`, `crate::layout` and
// `crate::layout_proof`.
#[path = "../../borrowing/src/model.rs"]
pub mod model;
#[path = "../../borrowing/src/soundness.rs"]
pub mod soundness;
#[path = "../../borrowing/src/cfg.rs"]
pub mod cfg;
#[path = "../../borrowing/src/layout.rs"]
pub mod layout;
#[path = "../../borrowing/src/layout_proof.rs"]
pub mod layout_proof;
#[path = "../../borrowing/src/layout_examples.rs"]
pub mod layout_examples;

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
