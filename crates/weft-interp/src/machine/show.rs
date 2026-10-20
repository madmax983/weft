//! Display, equality, arithmetic and JSON for run-time values.

use std::fmt::Write as _;

use weft_syntax::ast::BinOp;

use super::R;
use crate::heap::SlotKind;
use crate::value::{Cap, Value};

const MAX_DEPTH: usize = 24;

impl super::Machine<'_, '_> {
    /// Returns the display text of a value. A string shows without quotes.
    pub(crate) fn show(&self, v: &Value) -> String {
        let mut s = String::new();
        self.show_into(v, &mut s, true, 0);
        s
    }

    fn show_list(&self, vs: &[Value], out: &mut String, depth: usize) {
        out.push('[');
        for (i, v) in vs.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            self.show_into(v, out, false, depth + 1);
        }
        out.push(']');
    }

    fn show_cell(&self, c: usize, out: &mut String, top: bool, depth: usize) {
        match self.heap.slot(c) {
            Ok(s) if s.kind != SlotKind::Free => self.show_into(&s.val, out, top, depth + 1),
            _ => self.show_fault(
                out,
                "<freed>",
                "a read of a freed cell (a dangling reference)",
            ),
        }
    }

    /// Shows the marker of a value that a read cannot get. With the oracle
    /// checks on, the read is a fault too: a display reads the value, as
    /// each other use does.
    fn show_fault(&self, out: &mut String, marker: &str, what: &str) {
        out.push_str(marker);
        if let Some(o) = self.heap.oracle() {
            o.borrow_mut().flag(format!("oracle: {what}"));
        }
    }

    #[allow(clippy::too_many_lines)]
    fn show_into(&self, v: &Value, out: &mut String, top: bool, depth: usize) {
        if depth > MAX_DEPTH {
            out.push_str("...");
            return;
        }
        match v {
            Value::Unit => out.push_str("()"),
            Value::Bool(b) => {
                let _ = write!(out, "{b}");
            }
            Value::Int(i) => {
                let _ = write!(out, "{i}");
            }
            Value::Str(s) => {
                if top {
                    out.push_str(s);
                } else {
                    let _ = write!(out, "{:?}", &**s);
                }
            }
            Value::Dur(ms) => {
                if ms % 1000 == 0 {
                    let _ = write!(out, "{}s", ms / 1000);
                } else {
                    let _ = write!(out, "{ms}ms");
                }
            }
            Value::Tuple(vs) => {
                out.push('(');
                for (i, v) in vs.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.show_into(v, out, false, depth + 1);
                }
                if vs.len() == 1 {
                    out.push(',');
                }
                out.push(')');
            }
            Value::Struct(o) => {
                let info = &self.rt.adts[o.adt.index()];
                out.push_str(&info.name);
                if o.fields.is_empty() {
                    return;
                }
                out.push_str(" { ");
                for (i, f) in o.fields.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    if let Some(n) = info.fields.get(i) {
                        out.push_str(n);
                        out.push_str(": ");
                    }
                    self.show_into(f, out, false, depth + 1);
                }
                out.push_str(" }");
            }
            Value::Enum(e) => {
                let info = &self.rt.adts[e.adt.index()];
                if let Some((n, _)) = info.variants.get(e.variant as usize) {
                    out.push_str(n);
                }
                if !e.fields.is_empty() {
                    out.push('(');
                    for (i, f) in e.fields.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        self.show_into(f, out, false, depth + 1);
                    }
                    out.push(')');
                }
            }
            Value::Vec(c) => match self.heap.list(*c) {
                Ok(vs) => self.show_list(vs, out, depth),
                Err(_) => self.show_fault(
                    out,
                    "<freed>",
                    "a read of a freed buffer (a dangling reference)",
                ),
            },
            Value::List(vs) => self.show_list(vs, out, depth),
            Value::Slice { buf, lo, hi } => match self.heap.list(*buf) {
                Ok(vs) => {
                    let lo = (*lo as usize).min(vs.len());
                    let hi = (*hi as usize).clamp(lo, vs.len());
                    self.show_list(&vs[lo..hi], out, depth);
                }
                Err(_) => self.show_fault(
                    out,
                    "<freed>",
                    "a read of a freed buffer (a dangling reference)",
                ),
            },
            Value::Boxed(c) | Value::Rc(c) => self.show_cell(*c, out, top, depth),
            Value::Weak(_) => out.push_str("Weak"),
            Value::Ref(p) | Value::Loc(p, _) => {
                if let Value::Ref(p) = v {
                    self.heap.check_ref(p);
                }
                self.heap.log_read(p);
                match self.heap.get(p) {
                    Ok(x) => self.show_into(x, out, top, depth + 1),
                    Err(_) => {
                        self.show_fault(out, "<dangling>", "a read through a dangling reference");
                    }
                }
            }
            Value::Closure(_) => out.push_str("<closure>"),
            Value::FnItem(f) => {
                let _ = write!(
                    out,
                    "<fn {}>",
                    crate::runtime::qualified_name(self.rt.prog, *f)
                );
            }
            Value::Task(t) => {
                let _ = write!(out, "<task {t}>");
            }
            Value::Cont(_) => out.push_str("<continuation>"),
            Value::Scope(_) => out.push_str("<scope>"),
            Value::Cap(c) => out.push_str(match c {
                Cap::Fs => "<FsCap>",
                Cap::Net => "<NetCap>",
                Cap::Stdout => "<Stdout>",
                Cap::Listener(_) => "<Listener>",
            }),
            Value::Request(r) => {
                let _ = write!(out, "<request {} {}>", r.method, r.path);
            }
            Value::Response(r) => out.push_str(&r.body),
            Value::Iter(_) => out.push_str("<iterator>"),
            Value::Moved => self.show_fault(out, "<moved>", "a read of a moved value"),
        }
    }

    fn deref_shallow<'v>(&'v self, v: &'v Value) -> &'v Value {
        let mut v = v;
        for _ in 0..MAX_DEPTH {
            match v {
                Value::Ref(p) | Value::Loc(p, _) => match self.heap.get(p) {
                    Ok(x) => v = x,
                    Err(_) => return v,
                },
                _ => return v,
            }
        }
        v
    }

    fn elems<'v>(&'v self, v: &'v Value) -> Option<&'v [Value]> {
        match v {
            Value::Vec(c) => self.heap.list(*c).ok().map(Vec::as_slice),
            Value::List(vs) => Some(vs),
            Value::Slice { buf, lo, hi } => {
                let vs = self.heap.list(*buf).ok()?;
                let lo = (*lo as usize).min(vs.len());
                let hi = (*hi as usize).clamp(lo, vs.len());
                Some(&vs[lo..hi])
            }
            _ => None,
        }
    }

    /// Structural equality. References compare their targets.
    pub(crate) fn equal(&self, a: &Value, b: &Value, depth: usize) -> bool {
        if depth > MAX_DEPTH {
            return false;
        }
        let (a, b) = (self.deref_shallow(a), self.deref_shallow(b));
        match (a, b) {
            (Value::Unit, Value::Unit) => true,
            (Value::Bool(x), Value::Bool(y)) => x == y,
            (Value::Int(x), Value::Int(y)) => x == y,
            (Value::Str(x), Value::Str(y)) => x == y,
            (Value::Dur(x), Value::Dur(y)) => x == y,
            (Value::Task(x), Value::Task(y)) => x == y,
            (Value::Tuple(x), Value::Tuple(y)) => self.all_equal(x, y, depth),
            (Value::Struct(x), Value::Struct(y)) => {
                x.adt == y.adt && self.all_equal(&x.fields, &y.fields, depth)
            }
            (Value::Enum(x), Value::Enum(y)) => {
                x.adt == y.adt
                    && x.variant == y.variant
                    && self.all_equal(&x.fields, &y.fields, depth)
            }
            (Value::Boxed(x), Value::Boxed(y)) | (Value::Rc(x), Value::Rc(y)) => {
                x == y
                    || match (self.heap.slot(*x), self.heap.slot(*y)) {
                        (Ok(p), Ok(q)) => self.equal(&p.val, &q.val, depth + 1),
                        _ => false,
                    }
            }
            _ => match (self.elems(a), self.elems(b)) {
                (Some(x), Some(y)) => self.all_equal(x, y, depth),
                _ => false,
            },
        }
    }

    fn all_equal(&self, x: &[Value], y: &[Value], depth: usize) -> bool {
        x.len() == y.len() && x.iter().zip(y).all(|(a, b)| self.equal(a, b, depth + 1))
    }

    /// Applies a binary operator. Operands are read through references.
    pub(crate) fn binop(&self, op: BinOp, a: Value, b: Value) -> R<Value> {
        let a = self.deref_value(a)?;
        let b = self.deref_value(b)?;
        let overflow = || self.fault("integer overflow");
        Ok(match (op, &a, &b) {
            (BinOp::Add, Value::Int(x), Value::Int(y)) => {
                Value::Int(x.checked_add(*y).ok_or_else(overflow)?)
            }
            (BinOp::Sub, Value::Int(x), Value::Int(y)) => {
                Value::Int(x.checked_sub(*y).ok_or_else(overflow)?)
            }
            (BinOp::Mul, Value::Int(x), Value::Int(y)) => {
                Value::Int(x.checked_mul(*y).ok_or_else(overflow)?)
            }
            (BinOp::Div | BinOp::Rem, Value::Int(_), Value::Int(0)) => {
                return Err(self.fault("division by zero"));
            }
            (BinOp::Div, Value::Int(x), Value::Int(y)) => {
                Value::Int(x.checked_div(*y).ok_or_else(overflow)?)
            }
            (BinOp::Rem, Value::Int(x), Value::Int(y)) => {
                Value::Int(x.checked_rem(*y).ok_or_else(overflow)?)
            }
            (BinOp::Lt, Value::Int(x), Value::Int(y)) => Value::Bool(x < y),
            (BinOp::Le, Value::Int(x), Value::Int(y)) => Value::Bool(x <= y),
            (BinOp::Gt, Value::Int(x), Value::Int(y)) => Value::Bool(x > y),
            (BinOp::Ge, Value::Int(x), Value::Int(y)) => Value::Bool(x >= y),
            (BinOp::Add, Value::Dur(x), Value::Dur(y)) => Value::Dur(x.saturating_add(*y)),
            (BinOp::Sub, Value::Dur(x), Value::Dur(y)) => Value::Dur(
                x.checked_sub(*y)
                    .ok_or_else(|| self.fault("duration underflow"))?,
            ),
            (BinOp::Mul, Value::Dur(x), Value::Int(y))
            | (BinOp::Mul, Value::Int(y), Value::Dur(x)) => {
                Value::Dur(x.saturating_mul(u64::try_from(*y).unwrap_or(0)))
            }
            (BinOp::Lt, Value::Dur(x), Value::Dur(y)) => Value::Bool(x < y),
            (BinOp::Le, Value::Dur(x), Value::Dur(y)) => Value::Bool(x <= y),
            (BinOp::Gt, Value::Dur(x), Value::Dur(y)) => Value::Bool(x > y),
            (BinOp::Ge, Value::Dur(x), Value::Dur(y)) => Value::Bool(x >= y),
            (BinOp::Add, Value::Str(x), Value::Str(y)) => {
                let mut s = x.to_string();
                s.push_str(y);
                Value::str(&s)
            }
            (BinOp::Lt, Value::Str(x), Value::Str(y)) => Value::Bool(x < y),
            (BinOp::Le, Value::Str(x), Value::Str(y)) => Value::Bool(x <= y),
            (BinOp::Gt, Value::Str(x), Value::Str(y)) => Value::Bool(x > y),
            (BinOp::Ge, Value::Str(x), Value::Str(y)) => Value::Bool(x >= y),
            (BinOp::Eq, _, _) => Value::Bool(self.equal(&a, &b, 0)),
            (BinOp::Ne, _, _) => Value::Bool(!self.equal(&a, &b, 0)),
            (BinOp::And, Value::Bool(x), Value::Bool(y)) => Value::Bool(*x && *y),
            (BinOp::Or, Value::Bool(x), Value::Bool(y)) => Value::Bool(*x || *y),
            _ => {
                return Err(self.fault(format!(
                    "`{op:?}` cannot apply to `{}` and `{}`",
                    self.show(&a),
                    self.show(&b)
                )));
            }
        })
    }

    /// Returns the JSON text of a value.
    pub(crate) fn json(&self, v: &Value) -> String {
        let mut s = String::new();
        self.json_into(v, &mut s, 0);
        s
    }

    fn json_list(&self, vs: &[Value], out: &mut String, depth: usize) {
        out.push('[');
        for (i, v) in vs.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            self.json_into(v, out, depth + 1);
        }
        out.push(']');
    }

    fn json_into(&self, v: &Value, out: &mut String, depth: usize) {
        if depth > MAX_DEPTH {
            out.push_str("null");
            return;
        }
        let v = self.deref_shallow(v);
        match v {
            Value::Bool(b) => {
                let _ = write!(out, "{b}");
            }
            Value::Int(i) => {
                let _ = write!(out, "{i}");
            }
            Value::Dur(d) => {
                let _ = write!(out, "{d}");
            }
            Value::Str(s) => json_str(s, out),
            Value::Tuple(vs) => self.json_list(vs, out, depth),
            Value::Struct(o) => {
                let info = &self.rt.adts[o.adt.index()];
                out.push('{');
                for (i, f) in o.fields.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    json_str(info.fields.get(i).map_or("", |n| n), out);
                    out.push(':');
                    self.json_into(f, out, depth + 1);
                }
                out.push('}');
            }
            Value::Enum(e) => {
                let name = self.rt.adts[e.adt.index()]
                    .variants
                    .get(e.variant as usize)
                    .map_or("", |(n, _)| &**n);
                match (name, e.fields.as_slice()) {
                    ("None", []) => out.push_str("null"),
                    ("Some", [x]) => self.json_into(x, out, depth + 1),
                    (n, []) => json_str(n, out),
                    (n, fs) => {
                        out.push('{');
                        json_str(n, out);
                        out.push(':');
                        self.json_list(fs, out, depth);
                        out.push('}');
                    }
                }
            }
            Value::Boxed(c) | Value::Rc(c) => match self.heap.slot(*c) {
                Ok(s) => self.json_into(&s.val, out, depth + 1),
                Err(_) => out.push_str("null"),
            },
            other => match self.elems(other) {
                Some(vs) => self.json_list(vs, out, depth),
                None => out.push_str("null"),
            },
        }
    }

    /// Returns the integer elements of a `Vec` value.
    pub(crate) fn int_list(&self, v: &Value) -> Vec<u64> {
        let v = self.deref_shallow(v);
        self.elems(v)
            .map(|vs| {
                vs.iter()
                    .filter_map(|x| match self.deref_shallow(x) {
                        Value::Int(i) => u64::try_from(*i).ok(),
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default()
    }
}

/// Writes a JSON string literal.
pub fn json_str(s: &str, out: &mut String) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}
