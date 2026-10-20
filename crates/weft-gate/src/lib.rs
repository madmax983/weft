//! The diff gate of the core IR migration (`docs/plan/core-ir.md`, section 2).
//!
//! [`manifest`] lists the programs of the gate. [`archive`] packs the tier-2 probes
//! into one reproducible file.

use std::path::PathBuf;

pub mod archive;
pub mod manifest;

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
