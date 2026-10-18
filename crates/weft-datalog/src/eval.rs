//! The database, evaluation and the output.
//!
//! Evaluation runs one strongly connected component of the dependency graph
//! at a time, in dependency order. Inside a component it uses semi-naive
//! evaluation:
//!
//! 1. Iteration 0 applies every rule to the full relations.
//! 2. Each later iteration applies each recursive rule once for each body
//!    atom of the component. That atom reads only the delta: the rows that
//!    the previous iteration added. The other atoms read the full relations.
//! 3. Evaluation stops when an iteration adds no rows.
//!
//! The planner puts the delta atom first. Then it adds the atom with the most
//! bound columns. A lookup on bound columns uses a hash index. Negations and
//! comparisons go to the first place where all their variables are bound.

use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, HashMap};

use crate::ast::{Atom, CmpOp, Const, Literal, Program, Rule, Term};
use crate::check::analyze;
use crate::error::{Error, Location};
use crate::parser::parse_facts;
use crate::provenance::{Derivation, GroundAtom, Premise, Reason};
use crate::relation::{hash_values, to_u32, Relation, FACT};
use crate::value::{Interner, Value};

/// Options for [`evaluate`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EvalOptions {
    /// Record the first derivation of each tuple, for [`Output::explain`].
    /// This uses more memory and time. The default is `true`.
    pub provenance: bool,
}

impl Default for EvalOptions {
    fn default() -> Self {
        Self { provenance: true }
    }
}

/// Input facts and the symbol interner.
///
/// The database owns the interner. Make symbol values with
/// [`Database::sym`] before evaluation. The values stay valid in the
/// [`Output`].
#[derive(Clone, Debug, Default)]
pub struct Database {
    interner: Interner,
    relations: Vec<Relation>,
    names: HashMap<String, usize>,
    error: Option<Error>,
}

impl Database {
    /// Makes an empty database.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the symbol value for `text`. Adds the symbol if it is new.
    pub fn sym(&mut self, text: &str) -> Value {
        Value::Sym(self.interner.intern(text))
    }

    /// Adds a tuple to a relation. A duplicate tuple has no effect.
    ///
    /// All tuples of a relation must have the same number of values. If a
    /// tuple has a different number, the database records an error and
    /// [`evaluate`] returns [`Error::DatabaseArity`].
    pub fn insert(&mut self, relation: &str, tuple: impl AsRef<[Value]>) {
        let tuple = tuple.as_ref();
        let id = self.relation_id(relation, tuple.len());
        let rel = &mut self.relations[id];
        if rel.arity != tuple.len() {
            if self.error.is_none() {
                self.error = Some(Error::DatabaseArity {
                    relation: relation.to_string(),
                    expected: rel.arity,
                    found: tuple.len(),
                });
            }
            return;
        }
        rel.insert(tuple, hash_values(tuple.iter().copied()));
    }

    /// Parses facts in Datalog syntax and adds them, for example
    /// `edge(a, b). edge(b, c).` Returns the number of facts in the text.
    pub fn load_facts(&mut self, src: &str) -> Result<usize, Error> {
        let facts = parse_facts(src)?;
        for fact in &facts {
            let tuple: Vec<Value> = fact
                .values
                .iter()
                .map(|c| constant(c, &mut self.interner))
                .collect();
            self.insert(&fact.relation, tuple);
        }
        Ok(facts.len())
    }

    /// Returns the number of tuples in a relation.
    pub fn len(&self, relation: &str) -> usize {
        self.names
            .get(relation)
            .map_or(0, |&id| self.relations[id].len())
    }

    /// Writes a value in Datalog syntax.
    pub fn display(&self, v: Value) -> String {
        self.interner.display(v)
    }

    /// Returns the interner.
    pub const fn interner(&self) -> &Interner {
        &self.interner
    }

    fn relation_id(&mut self, relation: &str, arity: usize) -> usize {
        if let Some(&id) = self.names.get(relation) {
            return id;
        }
        self.relations.push(Relation::new(relation, arity));
        let id = self.relations.len() - 1;
        self.names.insert(relation.to_string(), id);
        id
    }
}

/// Converts a program constant to a value.
fn constant(c: &Const, interner: &mut Interner) -> Value {
    match c {
        Const::Int(i) => Value::Int(*i),
        Const::Sym(s) => Value::Sym(interner.intern(s)),
    }
}

/// A term of a compiled atom.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CTerm {
    Var(usize),
    Const(Value),
    Wild,
}

/// A value source: a constant or a variable slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Operand {
    Var(usize),
    Const(Value),
}

#[derive(Clone, Debug)]
struct CAtom {
    rel: usize,
    terms: Vec<CTerm>,
}

#[derive(Clone, Debug)]
enum CLit {
    Pos(CAtom),
    Neg(CAtom),
    Cmp(CmpOp, Operand, Operand),
}

/// A rule with relation ids and variable slots.
#[derive(Clone, Debug)]
struct CRule {
    head_rel: usize,
    head: Vec<Operand>,
    body: Vec<CLit>,
    nvars: usize,
    npos: usize,
    text: String,
}

struct Compiler<'a> {
    names: &'a HashMap<String, usize>,
    interner: &'a mut Interner,
    vars: HashMap<String, usize>,
    nvars: usize,
}

impl Compiler<'_> {
    fn var(&mut self, name: &str) -> usize {
        if let Some(&slot) = self.vars.get(name) {
            return slot;
        }
        let slot = self.fresh();
        self.vars.insert(name.to_string(), slot);
        slot
    }

    const fn fresh(&mut self) -> usize {
        self.nvars += 1;
        self.nvars - 1
    }

    fn term(&mut self, t: &Term) -> CTerm {
        match t {
            Term::Var(v) => CTerm::Var(self.var(v)),
            Term::Wildcard => CTerm::Wild,
            Term::Const(c) => CTerm::Const(constant(c, self.interner)),
        }
    }

    /// Compiles a term that must have a value. The checks reject a wildcard
    /// here. A wildcard gets a fresh variable, so the code does not panic.
    fn operand(&mut self, t: &Term) -> Operand {
        match t {
            Term::Var(v) => Operand::Var(self.var(v)),
            Term::Wildcard => Operand::Var(self.fresh()),
            Term::Const(c) => Operand::Const(constant(c, self.interner)),
        }
    }

    fn atom(&mut self, a: &Atom) -> CAtom {
        CAtom {
            rel: self.names[&a.relation],
            terms: a.terms.iter().map(|t| self.term(t)).collect(),
        }
    }

    fn rule(mut self, rule: &Rule) -> CRule {
        let body: Vec<CLit> = rule
            .body
            .iter()
            .map(|lit| match lit {
                Literal::Pos(a) => CLit::Pos(self.atom(a)),
                Literal::Neg(a) => CLit::Neg(self.atom(a)),
                Literal::Cmp { op, left, right } => {
                    CLit::Cmp(*op, self.operand(left), self.operand(right))
                }
            })
            .collect();
        let head = rule.head.terms.iter().map(|t| self.operand(t)).collect();
        CRule {
            head_rel: self.names[&rule.head.relation],
            head,
            npos: body.iter().filter(|l| matches!(l, CLit::Pos(_))).count(),
            body,
            nvars: self.nvars,
            text: rule.to_string(),
        }
    }
}

/// A column action for a matched row.
#[derive(Clone, Copy, Debug)]
enum Action {
    /// The column must equal the operand.
    Check(usize, Operand),
    /// The column gives the value of a variable.
    Bind(usize, usize),
}

/// One step of a join plan.
#[derive(Clone, Debug)]
enum Step {
    /// Read all rows, or the delta rows, of a relation.
    Scan {
        rel: usize,
        delta: bool,
        actions: Vec<Action>,
        slot: usize,
    },
    /// Read the rows that match a key through an index.
    Lookup {
        rel: usize,
        index: usize,
        key: Vec<Operand>,
        actions: Vec<Action>,
        slot: usize,
    },
    /// Continue only if no row matches the key.
    Absent {
        rel: usize,
        index: usize,
        cols: Vec<usize>,
        key: Vec<Operand>,
    },
    /// Continue only if the comparison holds.
    Test(CmpOp, Operand, Operand),
}

/// A join plan for one rule, with an optional delta atom.
#[derive(Debug)]
struct Plan {
    rule: u32,
    head_rel: usize,
    head: Vec<Operand>,
    steps: Vec<Step>,
    nvars: usize,
    npos: usize,
    /// The position in the component of the delta relation.
    delta_slot: usize,
}

fn vars_of(terms: &[CTerm]) -> impl Iterator<Item = usize> + '_ {
    terms.iter().filter_map(|t| match t {
        CTerm::Var(v) => Some(*v),
        _ => None,
    })
}

const fn operand_bound(op: Operand, bound: &[bool]) -> bool {
    match op {
        Operand::Var(v) => bound[v],
        Operand::Const(_) => true,
    }
}

/// Makes a join plan. `delta` is the body position of the delta atom.
fn plan(
    rule: &CRule,
    index: usize,
    delta: Option<usize>,
    delta_slot: usize,
    rels: &mut [Relation],
) -> Plan {
    // Positive atoms: (body position, premise slot).
    let mut atoms: Vec<(usize, usize)> = Vec::new();
    let mut filters: Vec<usize> = Vec::new();
    for (pos, lit) in rule.body.iter().enumerate() {
        match lit {
            CLit::Pos(_) => atoms.push((pos, atoms.len())),
            CLit::Neg(_) | CLit::Cmp(..) => filters.push(pos),
        }
    }
    let mut bound = vec![false; rule.nvars];
    let mut steps = Vec::new();
    place_filters(rule, &mut filters, &bound, &mut steps, rels);
    // The delta atom goes first, because it is usually the smallest input.
    let mut next = delta.and_then(|d| atoms.iter().position(|&(pos, _)| pos == d));
    while !atoms.is_empty() {
        let pick = next
            .take()
            .unwrap_or_else(|| best_atom(rule, &atoms, &bound, rels));
        let (pos, slot) = atoms.remove(pick);
        if let CLit::Pos(atom) = &rule.body[pos] {
            steps.push(atom_step(atom, slot, Some(pos) == delta, &mut bound, rels));
            place_filters(rule, &mut filters, &bound, &mut steps, rels);
        }
    }
    Plan {
        rule: to_u32(index),
        head_rel: rule.head_rel,
        head: rule.head.clone(),
        steps,
        nvars: rule.nvars,
        npos: rule.npos,
        delta_slot,
    }
}

/// Chooses the next atom: the most bound columns, then the smallest
/// relation, then the first in the body.
fn best_atom(rule: &CRule, atoms: &[(usize, usize)], bound: &[bool], rels: &[Relation]) -> usize {
    let key = |&(pos, _): &(usize, usize)| {
        let CLit::Pos(atom) = &rule.body[pos] else {
            return (Reverse(0), usize::MAX, pos);
        };
        let bound_cols = atom
            .terms
            .iter()
            .filter(|t| match t {
                CTerm::Var(v) => bound[*v],
                CTerm::Const(_) => true,
                CTerm::Wild => false,
            })
            .count();
        (Reverse(bound_cols), rels[atom.rel].len(), pos)
    };
    atoms
        .iter()
        .enumerate()
        .min_by_key(|(_, a)| key(a))
        .map_or(0, |(i, _)| i)
}

/// Makes the step for a positive atom and marks its variables as bound.
fn atom_step(
    atom: &CAtom,
    slot: usize,
    delta: bool,
    bound: &mut [bool],
    rels: &mut [Relation],
) -> Step {
    let before = bound.to_vec();
    let mut actions = Vec::new();
    let mut key_cols = Vec::new();
    let mut key = Vec::new();
    for (col, term) in atom.terms.iter().enumerate() {
        match *term {
            CTerm::Const(v) => {
                actions.push(Action::Check(col, Operand::Const(v)));
                key_cols.push(col);
                key.push(Operand::Const(v));
            }
            CTerm::Var(x) if before[x] => {
                actions.push(Action::Check(col, Operand::Var(x)));
                key_cols.push(col);
                key.push(Operand::Var(x));
            }
            CTerm::Var(x) if bound[x] => actions.push(Action::Check(col, Operand::Var(x))),
            CTerm::Var(x) => {
                actions.push(Action::Bind(col, x));
                bound[x] = true;
            }
            CTerm::Wild => {}
        }
    }
    if delta || key_cols.is_empty() {
        Step::Scan {
            rel: atom.rel,
            delta,
            actions,
            slot,
        }
    } else {
        Step::Lookup {
            rel: atom.rel,
            index: rels[atom.rel].ensure_index(&key_cols),
            key,
            actions,
            slot,
        }
    }
}

/// Moves each filter whose variables are all bound into the plan.
fn place_filters(
    rule: &CRule,
    filters: &mut Vec<usize>,
    bound: &[bool],
    steps: &mut Vec<Step>,
    rels: &mut [Relation],
) {
    filters.retain(|&pos| {
        let step = match &rule.body[pos] {
            CLit::Neg(atom) if vars_of(&atom.terms).all(|v| bound[v]) => {
                let mut cols = Vec::new();
                let mut key = Vec::new();
                for (col, term) in atom.terms.iter().enumerate() {
                    match *term {
                        CTerm::Var(v) => key.push(Operand::Var(v)),
                        CTerm::Const(c) => key.push(Operand::Const(c)),
                        CTerm::Wild => continue,
                    }
                    cols.push(col);
                }
                Step::Absent {
                    rel: atom.rel,
                    index: rels[atom.rel].ensure_index(&cols),
                    cols,
                    key,
                }
            }
            CLit::Cmp(op, l, r) if operand_bound(*l, bound) && operand_bound(*r, bound) => {
                Step::Test(*op, *l, *r)
            }
            _ => return true,
        };
        steps.push(step);
        false
    });
}

/// Rows that one plan derived, before insertion.
#[derive(Default)]
struct Buffer {
    values: Vec<Value>,
    hashes: Vec<u64>,
    premises: Vec<u32>,
}

/// The state of one plan execution.
struct Exec<'a> {
    rels: &'a [Relation],
    delta: (u32, u32),
    vars: Vec<Value>,
    rows: Vec<u32>,
    head: &'a [Operand],
    head_rel: &'a Relation,
    scratch: Vec<Value>,
    out: Buffer,
    provenance: bool,
}

impl Exec<'_> {
    fn value(&self, op: Operand) -> Value {
        match op {
            Operand::Const(v) => v,
            Operand::Var(x) => self.vars[x],
        }
    }

    fn bind(&mut self, row: &[Value], actions: &[Action]) -> bool {
        for action in actions {
            match *action {
                Action::Check(col, op) => {
                    if row[col] != self.value(op) {
                        return false;
                    }
                }
                Action::Bind(col, var) => self.vars[var] = row[col],
            }
        }
        true
    }

    fn key_hash(&self, key: &[Operand]) -> u64 {
        hash_values(key.iter().map(|op| self.value(*op)))
    }

    fn run(&mut self, steps: &[Step]) {
        let Some((step, rest)) = steps.split_first() else {
            self.emit();
            return;
        };
        let rels = self.rels;
        match step {
            Step::Scan {
                rel,
                delta,
                actions,
                slot,
            } => {
                let r = &rels[*rel];
                let (lo, hi) = if *delta {
                    self.delta
                } else {
                    (0, to_u32(r.len()))
                };
                for row in lo..hi {
                    if self.bind(r.row(row), actions) {
                        self.rows[*slot] = row;
                        self.run(rest);
                    }
                }
            }
            Step::Lookup {
                rel,
                index,
                key,
                actions,
                slot,
            } => {
                let r = &rels[*rel];
                for row in r.chain(*index, self.key_hash(key)) {
                    if self.bind(r.row(row), actions) {
                        self.rows[*slot] = row;
                        self.run(rest);
                    }
                }
            }
            Step::Absent {
                rel,
                index,
                cols,
                key,
            } => {
                let r = &rels[*rel];
                let found = r.chain(*index, self.key_hash(key)).any(|row| {
                    let t = r.row(row);
                    cols.iter().zip(key).all(|(&c, op)| t[c] == self.value(*op))
                });
                if !found {
                    self.run(rest);
                }
            }
            Step::Test(op, l, r) => {
                if op.holds(self.value(*l), self.value(*r)) {
                    self.run(rest);
                }
            }
        }
    }

    fn emit(&mut self) {
        let mut tuple = std::mem::take(&mut self.scratch);
        tuple.clear();
        tuple.extend(self.head.iter().map(|op| self.value(*op)));
        let hash = hash_values(tuple.iter().copied());
        if self.head_rel.find(&tuple, hash).is_none() {
            self.out.values.extend_from_slice(&tuple);
            self.out.hashes.push(hash);
            if self.provenance {
                self.out.premises.extend_from_slice(&self.rows);
            }
        }
        self.scratch = tuple;
    }
}

/// Runs one plan and inserts the new rows into the head relation. The new
/// rows go to the end of the relation, so the caller finds them by length.
/// `delta` is the row range for the delta atom.
fn run_plan(rels: &mut [Relation], plan: &Plan, delta: (u32, u32), provenance: bool) {
    let out = {
        let rels: &[Relation] = rels;
        let head_rel = &rels[plan.head_rel];
        let mut exec = Exec {
            rels,
            delta,
            vars: vec![Value::Int(0); plan.nvars],
            rows: vec![0; plan.npos],
            head: &plan.head,
            head_rel,
            scratch: Vec::with_capacity(head_rel.arity),
            out: Buffer::default(),
            provenance,
        };
        exec.run(&plan.steps);
        exec.out
    };
    let rel = &mut rels[plan.head_rel];
    let arity = rel.arity;
    for (i, &hash) in out.hashes.iter().enumerate() {
        let tuple = &out.values[i * arity..(i + 1) * arity];
        if rel.insert(tuple, hash) && provenance {
            rel.push_prov(plan.rule, &out.premises[i * plan.npos..(i + 1) * plan.npos]);
        }
    }
}

/// Evaluates the rules of one component to a fixpoint.
fn run_component(
    rels: &mut [Relation],
    rules: &[CRule],
    comp: &[usize],
    rule_ids: &[usize],
    provenance: bool,
) {
    let first: Vec<Plan> = rule_ids
        .iter()
        .map(|&r| plan(&rules[r], r, None, 0, rels))
        .collect();
    let mut recursive = Vec::new();
    for &r in rule_ids {
        for (pos, lit) in rules[r].body.iter().enumerate() {
            if let CLit::Pos(atom) = lit {
                if let Some(slot) = comp.iter().position(|&c| c == atom.rel) {
                    recursive.push(plan(&rules[r], r, Some(pos), slot, rels));
                }
            }
        }
    }
    let lens =
        |rels: &[Relation]| -> Vec<u32> { comp.iter().map(|&c| to_u32(rels[c].len())).collect() };
    let mut marks = lens(rels);
    for p in &first {
        run_plan(rels, p, (0, 0), provenance);
    }
    if recursive.is_empty() {
        return;
    }
    loop {
        let now = lens(rels);
        if now == marks {
            return;
        }
        let ranges: Vec<(u32, u32)> = marks.iter().copied().zip(now.iter().copied()).collect();
        marks = now;
        for p in &recursive {
            let range = ranges[p.delta_slot];
            if range.0 < range.1 {
                run_plan(rels, p, range, provenance);
            }
        }
    }
}

/// Evaluates `program` over the input facts in `input`.
///
/// The function checks the program first (arity, range restriction,
/// stratification), and checks that input relations have the arities that
/// the program uses.
///
/// # Examples
///
/// ```
/// use weft_datalog::{evaluate, parse_program, Database, EvalOptions, Value};
///
/// let program = parse_program("path(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).")?;
/// let mut db = Database::new();
/// let (a, b, c) = (db.sym("a"), db.sym("b"), db.sym("c"));
/// db.insert("edge", [a, b]);
/// db.insert("edge", [b, c]);
/// let out = evaluate(&program, db, EvalOptions::default())?;
/// assert!(out.contains("path", &[a, c]));
/// let proof = out.explain("path", &[a, c]).expect("derived");
/// assert!(proof.to_string().starts_with("path(a, c)  by  path(X, Z) :- "));
/// # Ok::<(), weft_datalog::Error>(())
/// ```
pub fn evaluate(program: &Program, input: Database, opts: EvalOptions) -> Result<Output, Error> {
    let Database {
        mut interner,
        mut relations,
        mut names,
        error,
    } = input;
    if let Some(e) = error {
        return Err(e);
    }
    let analysis = analyze(program)?;
    for (name, (arity, loc)) in &analysis.arities {
        if let Some(&id) = names.get(name) {
            if relations[id].arity != *arity {
                return Err(Error::InputArity {
                    loc: loc.clone(),
                    relation: name.clone(),
                    expected: relations[id].arity,
                    found: *arity,
                });
            }
        } else {
            relations.push(Relation::new(name, *arity));
            names.insert(name.clone(), relations.len() - 1);
        }
    }
    for rel in &mut relations {
        rel.input_rows = rel.len();
    }
    let rules: Vec<CRule> = program
        .rules
        .iter()
        .map(|rule| {
            Compiler {
                names: &names,
                interner: &mut interner,
                vars: HashMap::new(),
                nvars: 0,
            }
            .rule(rule)
        })
        .collect();
    for (i, fact) in program.facts.iter().enumerate() {
        let tuple: Vec<Value> = fact
            .values
            .iter()
            .map(|c| constant(c, &mut interner))
            .collect();
        let rel = &mut relations[names[&fact.relation]];
        if rel.insert(&tuple, hash_values(tuple.iter().copied())) && opts.provenance {
            rel.push_prov(FACT, &[to_u32(i)]);
        }
    }
    for comp in &analysis.components {
        let ids: Vec<usize> = comp.iter().map(|name| names[name]).collect();
        let rule_ids: Vec<usize> = (0..rules.len())
            .filter(|&r| ids.contains(&rules[r].head_rel))
            .collect();
        if !rule_ids.is_empty() {
            run_component(&mut relations, &rules, &ids, &rule_ids, opts.provenance);
        }
    }
    Ok(Output {
        interner,
        names: names.into_iter().collect(),
        relations,
        rules,
        fact_locs: program.facts.iter().map(|f| f.loc.clone()).collect(),
        provenance: opts.provenance,
    })
}

/// The result of [`evaluate`]: all relations, the interner and the
/// provenance.
#[derive(Debug)]
pub struct Output {
    interner: Interner,
    relations: Vec<Relation>,
    names: BTreeMap<String, usize>,
    rules: Vec<CRule>,
    fact_locs: Vec<Location>,
    provenance: bool,
}

/// A part of a derivation node before its children are complete.
enum Part {
    Child(usize, u32),
    Done(Premise),
}

/// A derivation node before its children are complete.
struct Node {
    fact: GroundAtom,
    kind: Kind,
    parts: Vec<Part>,
}

enum Kind {
    Input,
    Fact(Location),
    Rule(usize),
}

impl Output {
    fn relation(&self, name: &str) -> Option<&Relation> {
        self.names.get(name).map(|&id| &self.relations[id])
    }

    /// Returns the tuples of a relation, sorted. Integers come before
    /// symbols. Integers sort by number, symbols by text. An unknown relation
    /// has no tuples.
    pub fn tuples(&self, relation: &str) -> Vec<Vec<Value>> {
        let Some(rel) = self.relation(relation) else {
            return Vec::new();
        };
        let mut tuples: Vec<Vec<Value>> = rel.rows().map(<[Value]>::to_vec).collect();
        tuples.sort_by(|a, b| {
            a.iter()
                .zip(b)
                .map(|(x, y)| self.interner.compare(*x, *y))
                .find(|o| o.is_ne())
                .unwrap_or(Ordering::Equal)
        });
        tuples
    }

    /// Returns the number of tuples in a relation.
    pub fn len(&self, relation: &str) -> usize {
        self.relation(relation).map_or(0, Relation::len)
    }

    /// Returns `true` if the relation contains the tuple.
    pub fn contains(&self, relation: &str, tuple: &[Value]) -> bool {
        self.relation(relation)
            .and_then(|rel| rel.find_tuple(tuple))
            .is_some()
    }

    /// Returns the names of all relations, sorted. The list includes input
    /// relations that the program does not use.
    pub fn relations(&self) -> impl Iterator<Item = &str> {
        self.names.keys().map(String::as_str)
    }

    /// Writes a value in Datalog syntax.
    pub fn display_value(&self, v: Value) -> String {
        self.interner.display(v)
    }

    /// Writes a tuple in Datalog syntax, for example `edge(a, 1)`.
    pub fn display_tuple(&self, relation: &str, tuple: &[Value]) -> String {
        let args: Vec<String> = tuple.iter().map(|&v| self.display_value(v)).collect();
        format!("{relation}({})", args.join(", "))
    }

    /// Returns the value of an existing symbol. Returns `None` if no input
    /// fact and no program constant has this text.
    pub fn symbol(&self, text: &str) -> Option<Value> {
        self.interner.get(text).map(Value::Sym)
    }

    /// Returns the interner.
    pub const fn interner(&self) -> &Interner {
        &self.interner
    }

    /// Explains a tuple. Returns the first derivation of the tuple as a tree.
    ///
    /// Returns `None` if the relation does not contain the tuple, or if
    /// evaluation ran with provenance off.
    ///
    /// The tree is finite. A derived row records only premise rows that
    /// existed before it, so the premises of a node are always older than
    /// the node.
    pub fn explain(&self, relation: &str, tuple: &[Value]) -> Option<Derivation> {
        if !self.provenance {
            return None;
        }
        let rel = *self.names.get(relation)?;
        let row = self.relations[rel].find_tuple(tuple)?;
        self.derive(rel, row)
    }

    fn ground(&self, rel: usize, values: &[Value]) -> GroundAtom {
        let name = &self.relations[rel].name;
        GroundAtom {
            relation: name.clone(),
            values: values.to_vec(),
            text: self.display_tuple(name, values),
        }
    }

    /// Makes one node and lists its parts. Positive premises stay as
    /// references to rows.
    fn node(&self, rel: usize, row: u32) -> Node {
        let r = &self.relations[rel];
        let fact = self.ground(rel, r.row(row));
        let Some((rule, rows)) = r.prov(row) else {
            return Node {
                fact,
                kind: Kind::Input,
                parts: Vec::new(),
            };
        };
        if rule == FACT {
            let loc = rows
                .first()
                .and_then(|&i| self.fact_locs.get(i as usize))
                .cloned()
                .unwrap_or_else(|| Location {
                    origin: "".into(),
                    line: 0,
                });
            return Node {
                fact,
                kind: Kind::Fact(loc),
                parts: Vec::new(),
            };
        }
        let index = rule as usize;
        let c = &self.rules[index];
        // Bind the variables from the positive premises.
        let mut vars = vec![Value::Int(0); c.nvars];
        let mut premise_rows = rows.iter();
        let mut children = Vec::new();
        for lit in &c.body {
            if let CLit::Pos(atom) = lit {
                let child = premise_rows.next().copied().unwrap_or(0);
                let t = self.relations[atom.rel].row(child);
                for (term, v) in atom.terms.iter().zip(t) {
                    if let CTerm::Var(x) = term {
                        vars[*x] = *v;
                    }
                }
                children.push((atom.rel, child));
            }
        }
        let value = |op: Operand| match op {
            Operand::Var(x) => vars[x],
            Operand::Const(v) => v,
        };
        let mut children = children.into_iter();
        let parts = c
            .body
            .iter()
            .filter_map(|lit| match lit {
                CLit::Pos(_) => children.next().map(|(rel, row)| Part::Child(rel, row)),
                CLit::Neg(atom) => {
                    let args: Vec<Option<Value>> = atom
                        .terms
                        .iter()
                        .map(|t| match *t {
                            CTerm::Var(x) => Some(vars[x]),
                            CTerm::Const(v) => Some(v),
                            CTerm::Wild => None,
                        })
                        .collect();
                    let shown: Vec<String> = args
                        .iter()
                        .map(|a| a.map_or_else(|| "_".to_string(), |v| self.display_value(v)))
                        .collect();
                    let relation = self.relations[atom.rel].name.clone();
                    let text = format!("{relation}({})", shown.join(", "));
                    Some(Part::Done(Premise::Absent {
                        relation,
                        args,
                        text,
                    }))
                }
                CLit::Cmp(op, l, r) => {
                    let (left, right) = (value(*l), value(*r));
                    let text = format!(
                        "{} {op} {}",
                        self.display_value(left),
                        self.display_value(right)
                    );
                    Some(Part::Done(Premise::Holds {
                        op: *op,
                        left,
                        right,
                        text,
                    }))
                }
            })
            .collect();
        Node {
            fact,
            kind: Kind::Rule(index),
            parts,
        }
    }

    /// Builds the derivation tree without recursion, so that deep trees do
    /// not overflow the stack.
    fn derive(&self, rel: usize, row: u32) -> Option<Derivation> {
        // Pass 1: visit the nodes in pre-order. A child has a larger id than
        // its parent.
        let mut nodes: Vec<Node> = Vec::new();
        let mut child_ids: Vec<Vec<usize>> = Vec::new();
        let mut stack = vec![(rel, row, None::<usize>)];
        while let Some((rel, row, parent)) = stack.pop() {
            let id = nodes.len();
            if let Some(parent) = parent {
                child_ids[parent].push(id);
            }
            let node = self.node(rel, row);
            for part in node.parts.iter().rev() {
                if let Part::Child(r, w) = part {
                    stack.push((*r, *w, Some(id)));
                }
            }
            nodes.push(node);
            child_ids.push(Vec::new());
        }
        // Pass 2: build the nodes in reverse order, so each child is done
        // before its parent.
        let mut built: Vec<Option<Derivation>> = Vec::new();
        built.resize_with(nodes.len(), || None);
        while let Some(node) = nodes.pop() {
            let id = nodes.len();
            let mut kids = child_ids[id].iter();
            let reason = match node.kind {
                Kind::Input => Reason::Input,
                Kind::Fact(loc) => Reason::Fact { loc },
                Kind::Rule(index) => {
                    let mut premises = Vec::with_capacity(node.parts.len());
                    for part in node.parts {
                        premises.push(match part {
                            Part::Child(..) => Premise::Derived(built[*kids.next()?].take()?),
                            Part::Done(p) => p,
                        });
                    }
                    Reason::Rule {
                        index,
                        text: self.rules[index].text.clone(),
                        premises,
                    }
                }
            };
            built[id] = Some(Derivation {
                fact: node.fact,
                reason,
            });
        }
        built.first_mut()?.take()
    }
}
