//! Values, symbols and the symbol interner.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Write as _;
use std::sync::Arc;

/// An interned string. It is a small `Copy` id into an [`Interner`].
///
/// A symbol is valid only for the interner that made it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(u32);

impl Symbol {
    /// Returns the index of the symbol in its interner.
    pub const fn index(self) -> u32 {
        self.0
    }
}

/// A value in a tuple: an integer or a symbol.
///
/// Strings and lowercase identifiers are the same symbol type: `foo` and
/// `"foo"` are equal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Value {
    /// A 64-bit signed integer.
    Int(i64),
    /// An interned symbol.
    Sym(Symbol),
}

impl Value {
    /// Returns the integer, if the value is an integer.
    pub const fn as_int(self) -> Option<i64> {
        match self {
            Self::Int(i) => Some(i),
            Self::Sym(_) => None,
        }
    }

    /// Returns the symbol, if the value is a symbol.
    pub const fn as_sym(self) -> Option<Symbol> {
        match self {
            Self::Sym(s) => Some(s),
            Self::Int(_) => None,
        }
    }
}

impl From<i64> for Value {
    fn from(i: i64) -> Self {
        Self::Int(i)
    }
}

impl From<Symbol> for Value {
    fn from(s: Symbol) -> Self {
        Self::Sym(s)
    }
}

/// A table of interned strings.
#[derive(Clone, Debug, Default)]
pub struct Interner {
    ids: HashMap<Arc<str>, Symbol>,
    names: Vec<Arc<str>>,
}

impl Interner {
    /// Makes an empty interner.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the symbol for `text`. Adds the symbol if it is new.
    ///
    /// # Panics
    ///
    /// Panics if the interner has more than `u32::MAX` symbols.
    pub fn intern(&mut self, text: &str) -> Symbol {
        if let Some(&sym) = self.ids.get(text) {
            return sym;
        }
        let sym = Symbol(crate::relation::to_u32(self.names.len()));
        let name: Arc<str> = Arc::from(text);
        self.names.push(Arc::clone(&name));
        self.ids.insert(name, sym);
        sym
    }

    /// Returns the symbol for `text`, if the interner has it.
    pub fn get(&self, text: &str) -> Option<Symbol> {
        self.ids.get(text).copied()
    }

    /// Returns the text of `sym`, if `sym` is from this interner.
    pub fn resolve(&self, sym: Symbol) -> Option<&str> {
        self.names.get(sym.0 as usize).map(|s| &**s)
    }

    /// Returns the number of symbols.
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// Returns `true` if the interner has no symbols.
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    /// Writes `v` in Datalog syntax. A symbol that is not a lowercase
    /// identifier gets double quotes.
    pub fn display(&self, v: Value) -> String {
        match v {
            Value::Int(i) => i.to_string(),
            Value::Sym(s) => self
                .resolve(s)
                .map_or_else(|| format!("<unknown symbol {}>", s.0), display_symbol),
        }
    }

    /// Compares two values. Integers come before symbols. Integers compare
    /// by number. Symbols compare by text.
    pub fn compare(&self, a: Value, b: Value) -> Ordering {
        match (a, b) {
            (Value::Int(x), Value::Int(y)) => x.cmp(&y),
            (Value::Int(_), Value::Sym(_)) => Ordering::Less,
            (Value::Sym(_), Value::Int(_)) => Ordering::Greater,
            (Value::Sym(x), Value::Sym(y)) => self.resolve(x).cmp(&self.resolve(y)),
        }
    }
}

/// Returns `true` if `text` is a lowercase identifier: it starts with an
/// ASCII lowercase letter and continues with ASCII letters, digits or `_`.
pub fn is_identifier(text: &str) -> bool {
    let mut chars = text.chars();
    chars.next().is_some_and(|c| c.is_ascii_lowercase())
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Writes a symbol in Datalog syntax.
pub fn display_symbol(text: &str) -> String {
    if is_identifier(text) {
        return text.to_string();
    }
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Writes `text` as a JSON string.
pub fn json_string(out: &mut String, text: &str) {
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if u32::from(c) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interns_each_text_once() {
        let mut i = Interner::new();
        assert!(i.is_empty());
        let a = i.intern("a");
        assert_eq!(i.intern("a"), a);
        assert_ne!(i.intern("b"), a);
        assert_eq!(i.len(), 2);
        assert_eq!(a.index(), 0);
        assert_eq!(Value::from(a), Value::Sym(a));
    }

    #[test]
    fn displays_unknown_symbols() {
        let i = Interner::new();
        assert_eq!(i.display(Value::Sym(Symbol(9))), "<unknown symbol 9>");
    }

    #[test]
    fn compares_values() {
        let mut i = Interner::new();
        let b = Value::Sym(i.intern("b"));
        let a = Value::Sym(i.intern("a"));
        assert_eq!(i.compare(a, b), Ordering::Less);
        assert_eq!(i.compare(b, Value::Int(1)), Ordering::Greater);
        assert_eq!(i.compare(Value::Int(1), a), Ordering::Less);
        assert_eq!(i.compare(Value::Int(2), Value::Int(1)), Ordering::Greater);
    }

    #[test]
    fn escapes_json_control_characters() {
        let mut out = String::new();
        json_string(&mut out, "a\u{1}\t");
        assert_eq!(out, "\"a\\u0001\\t\"");
    }
}
