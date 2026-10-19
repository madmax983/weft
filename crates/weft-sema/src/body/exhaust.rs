//! Exhaustiveness: a `match` needs an arm for each value of its scrutinee (W0120).
//!
//! The check works on a matrix of patterns, one row for each arm, as in the
//! classic algorithm for pattern matching. The first column splits by the
//! constructors of its type: the variants of an enum, `true` and `false`, or
//! the parts of a tuple. A type with no finite set of constructors, such as an
//! integer, needs a row that matches anything in that column.

use std::cell::Cell;

use super::{AdtKind, Diagnostic, Lit, Lower, Pattern, Ty};

/// The most matrix steps that one `match` can take. A larger check stops and
/// reports nothing, so that a large match cannot take a long time.
const BUDGET: usize = 20_000;

/// One row of the matrix: a pattern for each column. `None` matches anything.
type Row<'a> = Vec<Option<&'a Pattern>>;

impl Lower<'_> {
    /// Reports W0120 if the arm patterns `pats` do not match each value of type `ty`.
    pub(super) fn check_exhaustive(&mut self, pats: &[&Pattern], ty: &Ty, span: super::Span) {
        let rows: Vec<Row<'_>> = pats.iter().map(|&p| vec![Some(p)]).collect();
        let budget = Cell::new(BUDGET);
        if !self.covers(&rows, std::slice::from_ref(ty), &budget) && budget.get() > 0 {
            let shown = self.show(&self.deref_ty(ty));
            self.diags.push(
                Diagnostic::error(
                    "W0120",
                    format!("this `match` does not cover every value of `{shown}`"),
                    span,
                )
                .note("add an arm for each missing value, or an arm `_ => ...`"),
            );
        }
    }

    /// Returns true if the rows match each list of values of the types `tys`.
    fn covers(&self, rows: &[Row<'_>], tys: &[Ty], budget: &Cell<usize>) -> bool {
        let left = budget.get();
        if left == 0 {
            return true;
        }
        budget.set(left - 1);
        let Some((first, rest)) = tys.split_first() else {
            return !rows.is_empty();
        };
        let t = self.inf.deep(&self.deref_ty(first));
        // Split by constructors only if a row names one: each split then uses up
        // a pattern, so the check ends also for a recursive type.
        let named = rows.iter().any(|r| {
            matches!(
                r.first(),
                Some(Some(
                    Pattern::Variant { .. } | Pattern::Tuple(..) | Pattern::Lit(..)
                ))
            )
        });
        match &t {
            _ if !named => {}
            Ty::Adt(a, args) => {
                if let AdtKind::Enum(vs) = &self.prog.adts[*a].kind {
                    return vs.iter().all(|v| {
                        let fields: Vec<Ty> =
                            v.fields.iter().map(|f| super::subst(f, args)).collect();
                        let spec = Self::specialize(rows, fields.len(), |p| match p {
                            Pattern::Variant {
                                path, fields: fs, ..
                            } => path
                                .last()
                                .filter(|n| n.name == v.name && fs.len() == fields.len())
                                .map(|_| fs.iter().map(Some).collect()),
                            _ => None,
                        });
                        let mut tys = fields;
                        tys.extend(rest.iter().cloned());
                        self.covers(&spec, &tys, budget)
                    });
                }
            }
            Ty::Bool => {
                return [true, false].iter().all(|&b| {
                    let spec = Self::specialize(rows, 0, |p| match p {
                        Pattern::Lit(Lit::Bool(x), _) if *x == b => Some(Vec::new()),
                        _ => None,
                    });
                    self.covers(&spec, rest, budget)
                });
            }
            Ty::Tuple(ts) => {
                let spec = Self::specialize(rows, ts.len(), |p| match p {
                    Pattern::Tuple(ps, _) if ps.len() == ts.len() => {
                        Some(ps.iter().map(Some).collect())
                    }
                    _ => None,
                });
                let mut tys = ts.clone();
                tys.extend(rest.iter().cloned());
                return self.covers(&spec, &tys, budget);
            }
            // A type that is not known has no error of its own here.
            Ty::Error | Ty::Var(_) | Ty::Never => return true,
            _ => {}
        }
        // Other types: only a row that matches anything covers the column. A
        // unit literal matches the only value of `()`.
        let unit = matches!(t, Ty::Unit);
        let rows: Vec<Row<'_>> = rows
            .iter()
            .filter(|r| match r.first() {
                Some(None | Some(Pattern::Wild(_) | Pattern::Bind(_))) => true,
                Some(Some(Pattern::Lit(Lit::Unit, _))) => unit,
                _ => false,
            })
            .map(|r| r[1..].to_vec())
            .collect();
        self.covers(&rows, rest, budget)
    }

    /// The rows for one constructor with `arity` parts: a row that matches anything
    /// in the first column matches anything in each part, and `parts` gives the
    /// parts of a row whose first pattern is this constructor.
    fn specialize<'a>(
        rows: &[Row<'a>],
        arity: usize,
        parts: impl Fn(&'a Pattern) -> Option<Row<'a>>,
    ) -> Vec<Row<'a>> {
        let mut out = Vec::new();
        for r in rows {
            let head = match r.first() {
                Some(None | Some(Pattern::Wild(_) | Pattern::Bind(_))) => vec![None; arity],
                Some(Some(p)) => match parts(p) {
                    Some(ps) => ps,
                    None => continue,
                },
                None => continue,
            };
            let mut row = head;
            row.extend(r[1..].iter().copied());
            out.push(row);
        }
        out
    }
}
