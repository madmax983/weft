//! The binding of call arguments to parameters (ADR 0009).
//!
//! A named argument binds by name where the callee has parameter names: a
//! function, a method, an operation, a function item in a local and a struct
//! constructor. The other arguments fill the free parameters in order, and a
//! trailing block goes to the last free parameter. A callee with no parameter
//! names takes no named argument. The interpreter binds the same way.

use super::{Arg, Expr, Lower, Span};
use weft_syntax::diag::Code;

/// A callee with parameter names, as the messages of W0103 and W0104 show it.
pub(super) struct ParamNames<'a> {
    /// The callee: "`f`", "operation `put`" or "`Range`".
    pub what: String,
    /// "parameter" or "field".
    pub noun: &'static str,
    /// The name of each parameter.
    pub names: Vec<&'a str>,
    /// The number of parameters that the call gives already: 1 for the
    /// receiver of a method.
    pub first: usize,
}

impl Lower<'_> {
    /// Binds the arguments of a call to the parameters of `callee`. Returns,
    /// for each parameter, the index of its argument: an index into `args`, or
    /// `args.len()` for the trailing block. Reports W0104 for an unknown name,
    /// and W0103 for a name given twice or a wrong number of arguments. An
    /// argument that binds to no parameter is still lowered.
    pub(super) fn order_args(
        &mut self,
        callee: &ParamNames<'_>,
        args: &[Arg],
        trailing: Option<&Expr>,
        span: Span,
    ) -> Vec<Option<usize>> {
        let n = callee.names.len();
        let mut slots: Vec<Option<usize>> = vec![None; n];
        let mut pos = callee.first;
        let mut extra = 0usize;
        let mut named_bad = false;
        for (k, a) in args.iter().enumerate() {
            let idx = if let Some(nm) = &a.name {
                let found = callee
                    .names
                    .iter()
                    .enumerate()
                    .skip(callee.first)
                    .find(|(_, p)| **p == nm.name)
                    .map(|(i, _)| i);
                let Some(i) = found else {
                    let msg = format!("{} has no {} named `{}`", callee.what, callee.noun, nm.name);
                    self.err(Code::W0104, msg, nm.span);
                    named_bad = true;
                    let _ = self.expr(&a.value);
                    continue;
                };
                if slots[i].is_some() {
                    let msg = format!("argument `{}` is given twice", nm.name);
                    self.err(Code::W0103, msg, nm.span);
                    named_bad = true;
                    let _ = self.expr(&a.value);
                    continue;
                }
                i
            } else {
                while pos < n && slots[pos].is_some() {
                    pos += 1;
                }
                pos
            };
            match slots.get_mut(idx) {
                Some(s) => *s = Some(k),
                None => extra += 1,
            }
        }
        if trailing.is_some() {
            match slots.iter().rposition(Option::is_none) {
                Some(i) if i >= callee.first => slots[i] = Some(args.len()),
                _ => extra += 1,
            }
        }
        let missing = slots
            .iter()
            .skip(callee.first)
            .filter(|s| s.is_none())
            .count();
        if (extra > 0 || missing > 0) && !named_bad {
            self.err(
                Code::W0103,
                format!(
                    "{} takes {} arguments, found {}",
                    callee.what,
                    n - callee.first.min(n),
                    args.len() + usize::from(trailing.is_some())
                ),
                span,
            );
        }
        slots
    }

    /// Reports W0104 for each named argument of a callee with no parameter
    /// names, such as a closure or a variant. The arguments then bind by
    /// position.
    pub(super) fn no_names(&mut self, what: &str, args: &[Arg]) {
        for a in args {
            if let Some(nm) = &a.name {
                let msg = format!(
                    "{what} has no parameter names: give the argument `{}` by position",
                    nm.name
                );
                self.err(Code::W0104, msg, nm.span);
            }
        }
    }
}

/// Returns the expression of each slot of [`Lower::order_args`].
pub(super) fn slot_exprs<'e>(
    slots: &[Option<usize>],
    args: &'e [Arg],
    trailing: Option<&'e Expr>,
) -> Vec<Option<&'e Expr>> {
    slots
        .iter()
        .map(|s| s.and_then(|k| args.get(k).map(|a| &a.value).or(trailing)))
        .collect()
}
