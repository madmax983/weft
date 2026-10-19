//! Source text with line lookup for diagnostics.

use crate::ast::Span;

/// A named source text with a line index.
#[derive(Clone, Debug)]
pub struct SourceFile {
    /// The file name, as shown in diagnostics.
    pub name: String,
    /// The full text.
    pub text: String,
    line_starts: Vec<u32>,
}

impl SourceFile {
    /// Makes a source file and indexes its lines.
    pub fn new(name: impl Into<String>, text: impl Into<String>) -> Self {
        let text = text.into();
        let mut line_starts = vec![0];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(u32::try_from(i + 1).unwrap_or(u32::MAX));
            }
        }
        Self {
            name: name.into(),
            text,
            line_starts,
        }
    }

    /// Returns the 1-based line and column of a byte offset.
    pub fn line_col(&self, offset: u32) -> (usize, usize) {
        let line = match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let col = offset - self.line_starts[line];
        (line + 1, col as usize + 1)
    }

    /// Returns the 1-based line of the start of a span.
    pub fn line(&self, span: Span) -> usize {
        self.line_col(span.lo).0
    }

    /// Returns the text of a 1-based line, without the line break.
    pub fn line_text(&self, line: usize) -> &str {
        let Some(&start) = self.line_starts.get(line.wrapping_sub(1)) else {
            return "";
        };
        let end = self
            .line_starts
            .get(line)
            .map_or(self.text.len(), |&e| e as usize);
        self.text[start as usize..end].trim_end_matches(['\n', '\r'])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_col_finds_lines() {
        let f = SourceFile::new("t", "ab\ncd\n");
        assert_eq!(f.line_col(0), (1, 1));
        assert_eq!(f.line_col(3), (2, 1));
        assert_eq!(f.line_col(4), (2, 2));
        assert_eq!(f.line_text(2), "cd");
        assert_eq!(f.line_text(9), "");
    }
}
