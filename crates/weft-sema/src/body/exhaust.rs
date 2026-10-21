//! Exhaustiveness: a `match` needs an arm for each value of its scrutinee (W0120).
//!
//! The check works on a matrix of patterns, one row for each arm, as in the
//! classic algorithm for pattern matching. The first column splits by the
//! constructors of its type: the variants of an enum, `true` and `false`, or
//! the parts of a tuple. A type with no finite set of constructors, such as an
//! integer, needs a row that matches anything in that column.

use std::cell::Cell;
use std::collections::HashMap;
use weft_syntax::diag::Code;

use super::{AdtKind, Diagnostic, Lit, Lower, Pattern, PatternKind, Ty};

/// The most matrix steps that one `match` can take. A larger check stops, so
/// that a large match cannot take a long time. It then reports W0120 too: the
/// check cannot show that the arms cover each value.
const BUDGET: usize = if cfg!(test) { 500 } else { 20_000 };

/// One row of the matrix: a pattern for each column. `None` matches anything.
type Row<'a> = Vec<Option<&'a Pattern>>;

impl Lower<'_> {
    /// Reports W0120 if the arm patterns `pats` do not match each value of type `ty`.
    pub(super) fn check_exhaustive(&mut self, pats: &[&Pattern], ty: &Ty, span: super::Span) {
        let rows: Vec<Row<'_>> = pats.iter().map(|&p| vec![Some(p)]).collect();
        let budget = Cell::new(BUDGET);
        if !self.covers(&rows, std::slice::from_ref(ty), &budget) {
            let shown = self.show(&self.deref_ty(ty));
            let msg = if budget.get() == 0 {
                format!(
                    "this `match` is too large to check that it covers every value of `{shown}`"
                )
            } else {
                format!("this `match` does not cover every value of `{shown}`")
            };
            self.diags.push(
                Diagnostic::error(Code::W0120, msg, span)
                    .note("add an arm for each missing value, or an arm `_ => ...`"),
            );
        }
    }

    /// Returns true if the rows match each list of values of the types `tys`.
    fn covers(&self, rows: &[Row<'_>], tys: &[Ty], budget: &Cell<usize>) -> bool {
        let left = budget.get();
        if left == 0 {
            return false;
        }
        budget.set(left - 1);
        // A row that matches anything in each column covers each value.
        if rows.iter().any(|r| r.iter().all(|p| is_wild(*p))) {
            return true;
        }
        let Some((first, rest)) = tys.split_first() else {
            return false;
        };
        let t = self.inf.deep(&self.deref_ty(first));
        // Split by constructors only if a row names one: each split then uses up
        // a pattern, so the check ends also for a recursive type.
        let named = rows.iter().any(|r| {
            matches!(
                r.first(),
                Some(Some(Pattern {
                    kind: PatternKind::Variant { .. }
                        | PatternKind::Tuple(..)
                        | PatternKind::Lit(..),
                    ..
                }))
            )
        });
        match &t {
            _ if !named => {}
            Ty::Adt(a, args) => {
                if let AdtKind::Enum(vs) = &self.prog.adts[*a].kind {
                    let (own, wild) = rows_by_variant(rows);
                    return vs.iter().all(|v| {
                        let fields: Vec<Ty> =
                            v.fields.iter().map(|f| super::subst(f, args)).collect();
                        // Only the rows of this variant and the rows that match
                        // anything give rows for it.
                        let mut picked: Vec<usize> = own
                            .get(v.name.as_str())
                            .map_or(&[][..], Vec::as_slice)
                            .iter()
                            .chain(&wild)
                            .copied()
                            .collect();
                        picked.sort_unstable();
                        let rows: Vec<Row<'_>> = picked.iter().map(|&i| rows[i].clone()).collect();
                        let spec = Self::specialize(&rows, fields.len(), |p| match &p.kind {
                            PatternKind::Variant {
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
                    let spec = Self::specialize(rows, 0, |p| match &p.kind {
                        PatternKind::Lit(Lit::Bool(x), _) if *x == b => Some(Vec::new()),
                        _ => None,
                    });
                    self.covers(&spec, rest, budget)
                });
            }
            Ty::Tuple(ts) => {
                let spec = Self::specialize(rows, ts.len(), |p| match &p.kind {
                    PatternKind::Tuple(ps, _) if ps.len() == ts.len() => {
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
                Some(p) if is_wild(*p) => true,
                Some(Some(Pattern {
                    kind: PatternKind::Lit(Lit::Unit, _),
                    ..
                })) => unit,
                _ => false,
            })
            .map(|r| r[1..].to_vec())
            .collect();
        self.covers(&rows, rest, budget)
    }

    /// The rows for one constructor with `arity` parts. A row that matches anything
    /// in the first column matches anything in each part. `parts` gives the parts
    /// of a row whose first pattern is this constructor.
    fn specialize<'a>(
        rows: &[Row<'a>],
        arity: usize,
        parts: impl Fn(&'a Pattern) -> Option<Row<'a>>,
    ) -> Vec<Row<'a>> {
        let mut out = Vec::new();
        for r in rows {
            let head = match r.first() {
                None => continue,
                Some(p) if is_wild(*p) => vec![None; arity],
                Some(p) => match p.and_then(&parts) {
                    Some(ps) => ps,
                    None => continue,
                },
            };
            let mut row = head;
            row.extend(r[1..].iter().copied());
            out.push(row);
        }
        out
    }
}

/// Returns the rows whose first pattern is a variant, by the name of the
/// variant, and the rows whose first cell matches anything. Each list is in
/// the order of the rows. So a `match` with an arm for each of many variants
/// costs time linear in the number of arms.
fn rows_by_variant<'a>(rows: &[Row<'a>]) -> (HashMap<&'a str, Vec<usize>>, Vec<usize>) {
    let mut own: HashMap<&'a str, Vec<usize>> = HashMap::new();
    let mut wild = Vec::new();
    for (i, r) in rows.iter().enumerate() {
        match r.first() {
            Some(p) if is_wild(*p) => wild.push(i),
            Some(Some(Pattern {
                kind: PatternKind::Variant { path, .. },
                ..
            })) => {
                if let Some(n) = path.last() {
                    own.entry(n.name.as_str()).or_default().push(i);
                }
            }
            _ => {}
        }
    }
    (own, wild)
}

/// Returns true if a cell of the matrix matches anything.
const fn is_wild(p: Option<&Pattern>) -> bool {
    matches!(
        p,
        None | Some(Pattern {
            kind: PatternKind::Wild(_) | PatternKind::Bind(_),
            ..
        })
    )
}
