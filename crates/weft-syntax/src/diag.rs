//! Diagnostics shared by every compiler phase.

use std::fmt::Write as _;

use crate::ast::Span;
use crate::source::SourceFile;

/// The unit index of the standard prelude.
pub const PRELUDE_UNIT: usize = 0;

/// The unit index of the root: the file or the package that the command
/// checks. Dependencies have the indices after it.
pub const ROOT_UNIT: usize = 1;

/// Makes the [`Code`] enum: one variant for each code, its text and the
/// list of all codes.
macro_rules! codes {
    ($($(#[$doc:meta])* $name:ident,)*) => {
        /// A diagnostic code. Each code has a text for `weft explain`
        /// (`weft_check::codes`). A code that does not exist does not compile:
        ///
        /// ```
        /// use weft_syntax::diag::Code;
        /// assert_eq!(Code::W0301.as_str(), "W0301");
        /// assert_eq!(Code::parse("w0301"), Some(Code::W0301));
        /// ```
        ///
        /// ```compile_fail
        /// let typo = weft_syntax::diag::Code::W030;
        /// ```
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub enum Code {
            $($(#[$doc])* $name,)*
        }

        impl Code {
            /// Every code, in order.
            pub const ALL: &'static [Self] = &[$(Self::$name,)*];

            /// Returns the code as text, for example `W0301`.
            pub const fn as_str(self) -> &'static str {
                match self {
                    $(Self::$name => stringify!($name),)*
                }
            }
        }
    };
}

codes! {
    /// L0001: lint warning.
    L0001,
    /// W0001: syntax error.
    W0001,
    /// W0101: unknown name.
    W0101,
    /// W0102: type mismatch.
    W0102,
    /// W0103: wrong number of arguments or fields.
    W0103,
    /// W0104: unknown field, method or operation.
    W0104,
    /// W0105: not callable.
    W0105,
    /// W0107: duplicate definition.
    W0107,
    /// W0108: unknown extern type property.
    W0108,
    /// W0109: impl of an unnamed type.
    W0109,
    /// W0110: parameter type missing.
    W0110,
    /// W0111: break or continue outside a loop.
    W0111,
    /// W0112: assignment to a value.
    W0112,
    /// W0113: variant pattern outside match.
    W0113,
    /// W0114: range outside for.
    W0114,
    /// W0115: incomplete construct.
    W0115,
    /// W0116: raw pointer outside FFI.
    W0116,
    /// W0117: type of infinite size.
    W0117,
    /// W0118: bad `on abort` function.
    W0118,
    /// W0119: contradictory modes.
    W0119,
    /// W0120: match does not cover every value.
    W0120,
    /// W0201: bad place root.
    W0201,
    /// W0203: argument points elsewhere.
    W0203,
    /// W0204: returned reference place.
    W0204,
    /// W0301: use of an invalidated reference.
    W0301,
    /// W0302: use after move.
    W0302,
    /// W0303: move out of a borrowed place.
    W0303,
    /// W0304: use before a value.
    W0304,
    /// W0312: overlapping arguments.
    W0312,
    /// W0313: capability escapes its handler.
    W0313,
    /// W0314: task reaches a handler on another stack.
    W0314,
    /// W0315: jump out of a handled or scope body.
    W0315,
    /// W0401: nonportable capture in fork.
    W0401,
    /// W0402: mutation through @shared.
    W0402,
    /// W0403: shared-mutable reference in fork.
    W0403,
    /// W0405: task footprints overlap.
    W0405,
    /// W0406: uniq reference expected.
    W0406,
    /// W0501: once continuation resumed twice.
    W0501,
    /// W0502: once closure called twice.
    W0502,
    /// W0503: value live across multi.
    W0503,
    /// W0504: resume in a clause of fail.
    W0504,
    /// W0601: linear value not consumed.
    W0601,
    /// W0602: abort without on abort.
    W0602,
    /// W0604: move of a !Move value.
    W0604,
    /// W0605: reference field.
    W0605,
    /// W0701: public effects not stated.
    W0701,
    /// W0702: effect not in signature.
    W0702,
    /// W0703: mutation not in signature.
    W0703,
    /// W0704: effect inference does not stop.
    W0704,
    /// W0705: function argument effects.
    W0705,
    /// W0706: effect inference does not converge.
    W0706,
    /// W0707: loop analysis does not converge.
    W0707,
    /// W0801: root handler in a library.
    W0801,
    /// W0802: simulation in a library.
    W0802,
    /// W0803: no runtime.
    W0803,
    /// W0804: unknown file marker.
    W0804,
    /// W0805: effect with no handler.
    W0805,
    /// W0901: dependency authority.
    W0901,
    /// W0902: library enables the GC.
    W0902,
    /// W1001: fip allocation.
    W1001,
    /// W1002: fip linearity.
    W1002,
    /// W1003: fip call.
    W1003,
    /// W1004: fip effects.
    W1004,
}

impl Code {
    /// Finds the code with the text `text`, in upper or lower case.
    pub fn parse(text: &str) -> Option<Self> {
        Self::ALL
            .iter()
            .copied()
            .find(|c| c.as_str().eq_ignore_ascii_case(text))
    }
}

impl std::fmt::Display for Code {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl PartialEq<str> for Code {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<String> for Code {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&str> for Code {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

/// How serious a diagnostic is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Severity {
    /// The checker rejects the program.
    Error,
    /// The checker accepts the program, but a rule (for example a user lint)
    /// fired.
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
    pub code: Code,
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
    /// The facts of the specification that the diagnostic reports, each with
    /// the index of its body, for example `body 3: error(v1, n6)`. `weft
    /// check --explain` links each derivation to its diagnostic with them. A
    /// diagnostic that no rule of the specification derives has none.
    pub facts: Vec<String>,
}

impl Diagnostic {
    /// Makes an error.
    pub fn error(code: Code, message: impl Into<String>, span: Span) -> Self {
        Self {
            code,
            severity: Severity::Error,
            message: message.into(),
            span,
            notes: Vec::new(),
            unit: ROOT_UNIT,
            facts: Vec::new(),
        }
    }

    /// Makes a warning.
    pub fn warning(code: Code, message: impl Into<String>, span: Span) -> Self {
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

    /// Adds the facts of the specification that the diagnostic reports (see
    /// [`Diagnostic::facts`]).
    #[must_use]
    pub fn with_facts(mut self, facts: impl IntoIterator<Item = String>) -> Self {
        self.facts.extend(facts);
        self
    }

    /// Renders the diagnostic in the format of the design doc: the message,
    /// the location, then one line for each note. A note with a location
    /// shows its line.
    ///
    /// ```text
    /// error[W0301]: `first` used after it was invalidated
    ///   --> world.wf:9:5
    ///   first : &Entity in world.entities[]  (line 7)
    ///   push : mut(world.entities)           (line 8)
    ///   used at line 9
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
            Code::W0301,
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
        let w = Diagnostic::warning(Code::L0001, "lint", Span::new(0, 1));
        assert!(w.render(&f).starts_with("warning[L0001]"));
    }
}
