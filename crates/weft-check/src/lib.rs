//! The Weft production checker.
//!
//! [`check`] runs the specialized rules on the facts of one function.
//! [`bridge::check_spec`] runs `spec/weft.dl` on the same facts with the Datalog
//! engine. The two results must be equal: [`driver::agreement`] compares them.

pub mod bridge;
pub mod codes;
pub mod diagnose;
pub mod driver;
pub mod rules;

pub use driver::{agreement, check_analysis, check_source, Checked};
pub use rules::{check, check_counted, Cause, Conflict, Invalidation, Report, Work};

#[cfg(test)]
mod tests;
