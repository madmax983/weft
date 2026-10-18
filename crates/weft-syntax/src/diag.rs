//! Diagnostics shared by every compiler phase.

use std::fmt::Write as _;

use crate::ast::Span;
use crate::source::SourceFile;

/// The unit index of the standard prelude.
pub const PRELUDE_UNIT: usize = 0;

/// The unit index of the root: the file or the package that is checked.
/// Dependencies have the indices after it.
pub const ROOT_UNIT: usize = 1;

/// How serious a diagnostic is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Severity {
    /// The program is rejected.
    Error,
    /// The program is accepted, but a rule (for example a user lint) fired.
    Warning,
}

/// One line of explanation under a diagnostic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Note {
    /// The text.
    pub text: String,
    /// The location the text refers to. The renderer adds `(line N)`.
    pub span: Option<Span>,
}

/// A diagnostic: a code, a message, a location and the derivation lines.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    /// The code, for example `W0301`.
    pub code: String,
    /// The severity.
    pub severity: Severity,
    /// The main message.
    pub message: String,
    /// The main location.
    pub span: Span,
    /// The explanation, one fact per line.
    pub notes: Vec<Note>,
    /// The source unit: [`PRELUDE_UNIT`], [`ROOT_UNIT`], or a dependency.
    pub unit: usize,
}

impl Diagnostic {
    /// Makes an error.
    pub fn error(code: &str, message: impl Into<String>, span: Span) -> Self {
        Self {
            code: code.into(),
            severity: Severity::Error,
            message: message.into(),
            span,
            notes: Vec::new(),
            unit: ROOT_UNIT,
        }
    }

    /// Makes a warning.
    pub fn warning(code: &str, message: impl Into<String>, span: Span) -> Self {
        Self {
            severity: Severity::Warning,
            ..Self::error(code, message, span)
        }
    }

    /// Adds a note with a location.
    #[must_use]
    pub fn note_at(mut self, text: impl Into<String>, span: Span) -> Self {
        self.notes.push(Note {
            text: text.into(),
            span: Some(span),
        });
        self
    }

    /// Adds a note without a location.
    #[must_use]
    pub fn note(mut self, text: impl Into<String>) -> Self {
        self.notes.push(Note {
            text: text.into(),
            span: None,
        });
        self
    }

    /// Renders the diagnostic in the format of the design doc.
    ///
    /// ```text
    /// error[W0301]: `first` used after it was invalidated
    ///   first  : &Entity in world.entities[]          (line 2)
    /// ```
    pub fn render(&self, file: &SourceFile) -> String {
        let kind = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        let (line, col) = file.line_col(self.span.lo);
        let mut out = format!("{kind}[{}]: {}\n", self.code, self.message);
        let _ = writeln!(out, "  --> {}:{line}:{col}", file.name);
        let width = self
            .notes
            .iter()
            .filter(|n| n.span.is_some())
            .map(|n| n.text.chars().count())
            .max()
            .unwrap_or(0);
        for n in &self.notes {
            match n.span {
                Some(s) => {
                    let pad = width - n.text.chars().count();
                    let _ = writeln!(
                        out,
                        "  {}{}  (line {})",
                        n.text,
                        " ".repeat(pad),
                        file.line(s)
                    );
                }
                None => {
                    let _ = writeln!(out, "  {}", n.text);
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_aligns_located_notes() {
        let f = SourceFile::new("a.wf", "let x = 1\nlet y = 2\n");
        let d = Diagnostic::error(
            "W0301",
            "`x` used after it was invalidated",
            Span::new(10, 11),
        )
        .note_at("x : &u32 in a", Span::new(0, 1))
        .note_at("push : mut(a)", Span::new(10, 11))
        .note("used at line 2");
        let r = d.render(&f);
        assert!(r.starts_with("error[W0301]: `x` used after it was invalidated\n  --> a.wf:2:1\n"));
        assert!(r.contains("  x : &u32 in a  (line 1)\n"));
        assert!(r.contains("  push : mut(a)  (line 2)\n"));
        assert!(r.ends_with("  used at line 2\n"));
        let w = Diagnostic::warning("L0001", "lint", Span::new(0, 1));
        assert!(w.render(&f).starts_with("warning[L0001]"));
    }
}
