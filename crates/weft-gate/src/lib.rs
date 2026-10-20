//! The diff gate of the core IR migration (`docs/plan/core-ir.md`, section 2).
//!
//! [`manifest`] lists the programs of the gate. [`archive`] packs the tier-2 probes
//! into one reproducible file and unpacks the committed archive. [`copy`] copies the
//! hand probes into the repository. [`snapshot`] checks each program and makes
//! one record for each program and pipeline, with the fact digest of [`digest`].

use std::path::PathBuf;

pub mod archive;
pub mod copy;
pub mod digest;
pub mod manifest;
pub mod snapshot;

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
