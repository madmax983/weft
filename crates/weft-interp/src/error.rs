//! Run-time errors.

use std::fmt;

use weft_syntax::ast::Span;

use crate::RunOutcome;

/// The kind of a run-time error.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ErrorKind {
    /// The program performed `fail(msg)` and no handler caught it.
    Failed,
    /// An `assert` was false.
    Assertion,
    /// The program did something that the checker should reject, or a guard failed.
    Fault,
    /// The program ran more steps than `RunOptions::max_steps` allows.
    StepLimit,
    /// Every task waits and no timer can wake one.
    Deadlock,
    /// The program has no `main` function.
    NoMain,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Failed => "failed",
            Self::Assertion => "assertion failed",
            Self::Fault => "runtime error",
            Self::StepLimit => "step limit",
            Self::Deadlock => "deadlock",
            Self::NoMain => "no main",
        };
        f.write_str(s)
    }
}

/// A run-time error. It keeps the output that the program wrote before the error.
#[derive(Debug, Clone, thiserror::Error)]
#[error("{kind}: {message}")]
pub struct RuntimeError {
    /// The kind.
    pub kind: ErrorKind,
    /// The message.
    pub message: String,
    /// The source location, if known.
    pub span: Option<Span>,
    /// The output, trace and counters up to the error.
    pub outcome: Box<RunOutcome>,
}

impl RuntimeError {
    /// Makes an error with an empty outcome.
    pub fn new(kind: ErrorKind, message: impl Into<String>, span: Option<Span>) -> Self {
        Self {
            kind,
            message: message.into(),
            span,
            outcome: Box::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_shows_kind_and_message() {
        let e = RuntimeError::new(ErrorKind::Failed, "too much", None);
        assert_eq!(e.to_string(), "failed: too much");
        for k in [
            ErrorKind::Assertion,
            ErrorKind::Fault,
            ErrorKind::StepLimit,
            ErrorKind::Deadlock,
            ErrorKind::NoMain,
        ] {
            assert!(!k.to_string().is_empty());
        }
    }
}
