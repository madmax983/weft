//! The core IR of Weft (ADR 0012, `docs/ir.md`).
//!
//! The IR goes between the typed tree (THIR) and fact generation. The
//! interpreter runs it too. This crate holds the IR types, the final type
//! table ([`ty`]), the printer and the verifier. It does not depend on
//! `weft-sema`: `weft-sema` makes the IR from its typed tree.

#![forbid(unsafe_code)]

pub mod ty;

pub use ty::{AdtId, EffectId, IntTy, Props, Ty, TyId, TyTable};
pub use weft_syntax::ast::{ExprId, PatId};
