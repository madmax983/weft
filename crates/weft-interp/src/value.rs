//! Run-time values, places and handler environments.

use std::collections::BTreeMap;
use std::rc::Rc;

use weft_sema::program::EffectId;
use weft_sema::types::AdtId;
use weft_syntax::ast::Span;

/// An index into the heap.
pub type CellId = usize;
/// An index into the task table.
pub type TaskId = usize;
/// An index into the continuation table.
pub type ContId = usize;
/// An index into the scope table.
pub type ScopeId = usize;
/// An index into the linear value table.
pub type LinId = usize;
/// An index into the compiled code table.
pub type CodeId = usize;

/// A location: a heap cell and a path of field or element indices inside it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Place {
    /// The cell.
    pub cell: CellId,
    /// Field, payload or element indices, from the outside in.
    pub path: Vec<u32>,
}

impl Place {
    /// Returns the place of a whole cell.
    pub const fn root(cell: CellId) -> Self {
        Self {
            cell,
            path: Vec::new(),
        }
    }

    /// Returns the place of field or element `i` of this place.
    #[must_use]
    pub fn child(&self, i: u32) -> Self {
        let mut path = self.path.clone();
        path.push(i);
        Self {
            cell: self.cell,
            path,
        }
    }
}

/// A struct value. A linear struct has a record in the linear table.
#[derive(Clone, Debug)]
pub struct Obj {
    /// The struct type.
    pub adt: AdtId,
    /// The fields, in declaration order.
    pub fields: Vec<Value>,
    /// The linear record, for a linear struct.
    pub lin: Option<LinId>,
}

/// An enum value.
#[derive(Clone, Debug)]
pub struct EnumVal {
    /// The enum type.
    pub adt: AdtId,
    /// The variant index.
    pub variant: u32,
    /// The payload.
    pub fields: Vec<Value>,
}

/// A closure: code, captured cells and the handlers where it was made.
#[derive(Clone, Debug)]
pub struct ClosureVal {
    /// The code.
    pub code: CodeId,
    /// The captured cells. A capture by reference is the cell of the variable. A
    /// capture that the closure moves is a cell of its own: the closure took the
    /// value when it was made.
    pub cells: Vec<CellId>,
    /// The cells of `cells` that the closure owns: the captures that it moved.
    /// The unwinder finishes the linear values in them (ADR 0010).
    pub owned: Vec<CellId>,
    /// The lexical handlers at the creation point.
    pub henv: HEnv,
    /// The closure expression.
    pub span: Span,
}

/// A root capability or an opaque runtime handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cap {
    /// The file system capability.
    Fs,
    /// The network capability.
    Net,
    /// The standard output capability.
    Stdout,
    /// A listener made by `NetCap.listen`.
    Listener(usize),
    /// The capability of a handler: the value of the capability local of a
    /// handled body of the IR (`docs/ir.md` 5.24).
    Handler {
        /// The handled effect.
        effect: EffectId,
        /// The handler instance.
        id: u64,
    },
}

/// An HTTP request.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HttpRequest {
    /// The method, for example `GET`.
    pub method: String,
    /// The path without the query.
    pub path: String,
    /// The query parameters.
    pub params: BTreeMap<String, String>,
}

/// An HTTP response.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HttpResponse {
    /// The status code.
    pub status: u16,
    /// The content type.
    pub content_type: String,
    /// The body.
    pub body: String,
}

/// The state of a `for` loop.
#[derive(Clone, Debug)]
pub enum IterState {
    /// `for i in a..b`.
    Range {
        /// The next value.
        next: i64,
        /// The end (excluded).
        end: i64,
    },
    /// `for e in xs[]`: references to the elements of a buffer.
    Elems {
        /// The buffer cell.
        buf: CellId,
        /// The next index.
        next: u32,
        /// The end index (excluded).
        end: u32,
    },
}

/// A run-time value.
#[derive(Clone, Debug, Default)]
pub enum Value {
    /// `()`.
    #[default]
    Unit,
    /// A boolean.
    Bool(bool),
    /// An integer.
    Int(i64),
    /// An immutable string.
    Str(Rc<str>),
    /// A duration in milliseconds.
    Dur(u64),
    /// A tuple.
    Tuple(Vec<Self>),
    /// A struct.
    Struct(Box<Obj>),
    /// An enum value.
    Enum(Box<EnumVal>),
    /// A `Vec`: a handle to a heap buffer.
    Vec(CellId),
    /// The contents of a heap buffer.
    List(Vec<Self>),
    /// A `Box`: a handle to a heap cell.
    Boxed(CellId),
    /// An `Rc`: a handle to a counted heap cell.
    Rc(CellId),
    /// A `Weak`: a weak handle to a counted heap cell.
    Weak(CellId),
    /// A reference to a place.
    Ref(Place),
    /// A reference to the elements `lo..hi` of a buffer.
    Slice {
        /// The buffer cell.
        buf: CellId,
        /// The first index.
        lo: u32,
        /// One past the last index.
        hi: u32,
    },
    /// A closure.
    Closure(Rc<ClosureVal>),
    /// A function item used as a value.
    FnItem(weft_sema::FnId),
    /// A task handle.
    Task(TaskId),
    /// A captured continuation.
    Cont(ContId),
    /// The capability of a `scope`.
    Scope(ScopeId),
    /// A capability or runtime handle.
    Cap(Cap),
    /// An HTTP request.
    Request(Rc<HttpRequest>),
    /// An HTTP response.
    Response(Rc<HttpResponse>),
    /// A loop iterator (internal).
    Iter(Box<IterState>),
    /// A place on the operand stack (internal). The flag is true if the path went
    /// through a reference.
    Loc(Place, bool),
    /// The value was moved out.
    Moved,
}

impl Value {
    /// Makes a string value.
    pub fn str(s: &str) -> Self {
        Self::Str(Rc::from(s))
    }
}

/// A persistent list of lexical handlers: effect to handler instance.
#[derive(Clone, Debug, Default)]
pub struct HEnv(Option<Rc<HNode>>);

/// One entry of a handler environment.
#[derive(Debug)]
pub struct HNode {
    /// The effect.
    pub effect: EffectId,
    /// The handler instance.
    pub handler: u64,
    /// The outer entries.
    pub next: HEnv,
}

impl HEnv {
    /// Returns a new environment where `handler` handles `effect`.
    #[must_use]
    pub fn with(&self, effect: EffectId, handler: u64) -> Self {
        Self(Some(Rc::new(HNode {
            effect,
            handler,
            next: self.clone(),
        })))
    }

    /// Returns the handler instances for `effect`, innermost first.
    pub fn handlers_for(&self, effect: EffectId) -> Vec<u64> {
        let mut out = Vec::new();
        let mut cur = self.0.as_ref();
        while let Some(n) = cur {
            if n.effect == effect {
                out.push(n.handler);
            }
            cur = n.next.0.as_ref();
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn henv_finds_innermost_first() {
        let id = weft_sema::EffectId;
        let e = HEnv::default()
            .with(id(1), 10)
            .with(id(2), 20)
            .with(id(1), 30);
        assert_eq!(e.handlers_for(id(1)), vec![30, 10]);
        assert_eq!(e.handlers_for(id(2)), vec![20]);
        assert!(e.handlers_for(id(3)).is_empty());
    }

    #[test]
    fn place_child_extends_path() {
        let p = Place::root(3).child(1).child(2);
        assert_eq!(p.cell, 3);
        assert_eq!(p.path, vec![1, 2]);
        assert!(matches!(Value::str("a"), Value::Str(_)));
    }
}
