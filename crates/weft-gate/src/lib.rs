//! The diff gate of the core IR migration (`docs/plan/core-ir.md`, section 2).
//!
//! [`manifest`] lists the programs of the gate. [`archive`] packs the tier-2 probes
//! into one reproducible file and unpacks the committed archive. [`copy`] copies the
//! hand probes into the repository. [`snapshot`] checks each program and makes
//! one record for each program and pipeline, with the fact digest of [`digest`].
//! [`oracle`] runs each program in the interpreter oracle and keeps the verdicts
//! in a cache. [`pool`] runs the work of `snapshot` and `oracle` on worker
//! threads. [`classify`] gives the class of each program from its two
//! records and its verdict. [`ledger`] reads the ledger that accepts groups of
//! programs. [`report`] runs the gate, applies the rules and writes the
//! report. [`baseline`] keeps the old records of a tier and compares a run
//! with them. [`claims`] reads the claims file and checks each claim that is on
//! with the `ir` pipeline. [`thir`] runs test D0 on the THIR tables of each
//! program. [`ir_build`] builds and verifies the IR of each program.

use std::path::PathBuf;

pub mod archive;
pub mod baseline;
pub mod claims;
pub mod classify;
pub mod copy;
pub mod digest;
pub mod ir_build;
pub mod ledger;
pub mod manifest;
pub mod oracle;
pub mod pool;
pub mod report;
pub mod snapshot;
pub mod thir;

/// An error of the gate tools.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// A file or a directory cannot be read or written.
    #[error("{path}: {source}")]
    Io {
        /// The file or the directory.
        path: PathBuf,
        /// The cause.
        source: std::io::Error,
    },
    /// A line of a manifest text is not correct.
    #[error("line {line} of the manifest: {message}")]
    Syntax {
        /// The line number, from 1.
        line: usize,
        /// What is wrong.
        message: String,
    },
    /// The SHA-256 of a file is not the committed hash.
    #[error("{path}: the SHA-256 is {found}, but the committed hash is `{expected}`")]
    Hash {
        /// The file.
        path: PathBuf,
        /// The committed hash.
        expected: String,
        /// The hash of the file.
        found: String,
    },
    /// A line of an oracle cache is not correct.
    #[error("line {line} of the oracle cache: {message}")]
    Cache {
        /// The line number, from 1.
        line: usize,
        /// What is wrong.
        message: String,
    },
    /// A line of a baseline file is not a record.
    #[error("line {line} of the baseline: {message}")]
    Baseline {
        /// The line number, from 1.
        line: usize,
        /// What is wrong.
        message: String,
    },
    /// The ledger is not correct.
    #[error("the ledger: {0}")]
    Ledger(String),
    /// The claims file is not correct.
    #[error("the claims file: {0}")]
    Claims(String),
    /// The oracle cache has no verdict for some programs: the interpreter
    /// sources or the programs changed after the last run of the oracle.
    #[error("{message}")]
    Stale {
        /// The number of programs with no verdict.
        programs: usize,
        /// What to do.
        message: String,
    },
    /// The system cannot start a worker thread.
    #[error("cannot start a worker thread: {0}")]
    Thread(std::io::Error),
}

impl Error {
    /// Makes an [`Error::Io`] for `path`.
    pub fn io(path: impl Into<PathBuf>, source: std::io::Error) -> Self {
        Self::Io {
            path: path.into(),
            source,
        }
    }
}
