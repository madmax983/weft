//! Property tests. The semi-naive engine must agree with a naive fixpoint
//! evaluator on random stratified programs, and transitive closure must agree
//! with breadth-first search.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use proptest::prelude::*;
use weft_datalog::{
    evaluate, parse_program, Atom, Const, Database, Derivation, EvalOptions, Literal, Output,
    Premise, Program, Reason, Rule, Term, Value,
};

type Relation = BTreeSet<Vec<Value>>;
type Facts = BTreeMap<String, Relation>;
type Env = BTreeMap<String, Value>;

// ---------------------------------------------------------------------------
// A naive evaluator. It recomputes every rule over the full relations until
// nothing changes. It supports integer constants only.
// ---------------------------------------------------------------------------

fn constant(c: &Const) -> Value {
    match c {
        Const::Int(i) => Value::Int(*i),
        Const::Sym(s) => panic!("the naive evaluator has no symbols: {s}"),
    }
}

fn term_value(term: &Term, env: &Env) -> Option<Value> {
    match term {
        Term::Var(v) => env.get(v).copied(),
        Term::Const(c) => Some(constant(c)),
        Term::Wildcard => None,
    }
}

/// Extends `env` so that `atom` matches `tuple`. Returns `None` on a conflict.
fn unify(atom: &Atom, tuple: &[Value], env: &Env) -> Option<Env> {
    let mut env = env.clone();
    for (term, value) in atom.terms.iter().zip(tuple) {
        match term {
            Term::Wildcard => {}
            Term::Const(c) => {
                if constant(c) != *value {
                    return None;
                }
            }
            Term::Var(v) => match env.get(v) {
                Some(bound) if bound != value => return None,
                Some(_) => {}
                None => {
                    env.insert(v.clone(), *value);
                }
            },
        }
    }
    Some(env)
}

fn rule_matches(rule: &Rule, db: &Facts) -> Vec<Vec<Value>> {
    let empty = Relation::new();
    let mut envs = vec![Env::new()];
    for lit in &rule.body {
        if let Literal::Pos(atom) = lit {
            let rel = db.get(&atom.relation).unwrap_or(&empty);
            envs = envs
                .iter()
                .flat_map(|env| rel.iter().filter_map(|t| unify(atom, t, env)))
                .collect();
        }
    }
    envs.retain(|env| {
        rule.body.iter().all(|lit| match lit {
            Literal::Pos(_) => true,
            Literal::Neg(atom) => {
                let rel = db.get(&atom.relation).unwrap_or(&empty);
                !rel.iter().any(|t| unify(atom, t, env).is_some())
            }
            Literal::Cmp { op, left, right } => {
                let l = term_value(left, env).expect("bound");
                let r = term_value(right, env).expect("bound");
                op.holds(l, r)
            }
        })
    });
    envs.iter()
        .map(|env| {
            rule.head
                .terms
                .iter()
                .map(|t| term_value(t, env).expect("range restricted"))
                .collect()
        })
        .collect()
}

/// Computes a stratum number for each relation by relaxation.
fn strata(program: &Program) -> BTreeMap<String, usize> {
    let mut level: BTreeMap<String, usize> = BTreeMap::new();
    loop {
        let mut changed = false;
        for rule in program.rules() {
            let mut need = 0;
            for lit in &rule.body {
                match lit {
                    Literal::Pos(a) => {
                        need = need.max(level.get(&a.relation).copied().unwrap_or(0));
                    }
                    Literal::Neg(a) => {
                        need = need.max(level.get(&a.relation).copied().unwrap_or(0) + 1);
                    }
                    Literal::Cmp { .. } => {}
                }
            }
            let entry = level.entry(rule.head.relation.clone()).or_insert(0);
            if *entry < need {
                *entry = need;
                changed = true;
            }
        }
        if !changed {
            return level;
        }
    }
}

fn naive(program: &Program, input: &Facts) -> Facts {
    let mut db = input.clone();
    for fact in program.facts() {
        let tuple = fact.values.iter().map(constant).collect();
        db.entry(fact.relation.clone()).or_default().insert(tuple);
    }
    let level = strata(program);
    let top = level.values().copied().max().unwrap_or(0);
    for current in 0..=top {
        loop {
            let mut changed = false;
            for rule in program.rules() {
                if level[&rule.head.relation] != current {
                    continue;
                }
                for tuple in rule_matches(rule, &db) {
                    changed |= db
                        .entry(rule.head.relation.clone())
                        .or_default()
                        .insert(tuple);
                }
            }
            if !changed {
                break;
            }
        }
    }
    db
}

// ---------------------------------------------------------------------------
// A generator for random stratified programs.
// ---------------------------------------------------------------------------

/// A small deterministic random number generator (`SplitMix64`).
struct Rng(u64);

impl Rng {
    const fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).expect("small");
        usize::try_from(self.next() % n).expect("small")
    }

    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }
}

/// Relations as (name, arity, stratum level). Level 0 is the input.
const RELATIONS: [(&str, usize, usize); 8] = [
    ("e", 2, 0),
    ("s", 1, 0),
    ("b", 1, 0),
    ("d1", 1, 1),
    ("d2", 2, 1),
    ("d3", 1, 2),
    ("d4", 2, 2),
    ("d5", 1, 3),
];
const VARS: [&str; 4] = ["X", "Y", "Z", "W"];

fn atom_text(rel: &str, terms: &[String]) -> String {
    format!("{rel}({})", terms.join(", "))
}

fn generate_rule(rng: &mut Rng) -> String {
    let derived: Vec<_> = RELATIONS.iter().filter(|r| r.2 > 0).collect();
    let &&(head, head_arity, level) = rng.pick(&derived);
    let positive: Vec<_> = RELATIONS.iter().filter(|r| r.2 <= level).collect();
    let negative: Vec<_> = RELATIONS.iter().filter(|r| r.2 < level).collect();
    let mut body = Vec::new();
    let mut bound: Vec<String> = Vec::new();
    for _ in 0..=rng.below(3) {
        let &&(rel, arity, _) = rng.pick(&positive);
        let terms: Vec<String> = (0..arity)
            .map(|_| match rng.below(10) {
                0 => "_".to_string(),
                1 | 2 => rng.below(4).to_string(),
                _ => (*rng.pick(&VARS)).to_string(),
            })
            .collect();
        for t in &terms {
            if t.starts_with(char::is_uppercase) && !bound.contains(t) {
                bound.push(t.clone());
            }
        }
        body.push(atom_text(rel, &terms));
    }
    let operand = |rng: &mut Rng, wildcard: bool| -> String {
        if wildcard && rng.chance(20) {
            "_".to_string()
        } else if bound.is_empty() || rng.chance(20) {
            rng.below(4).to_string()
        } else {
            rng.pick(&bound).clone()
        }
    };
    if rng.chance(50) {
        let &&(rel, arity, _) = rng.pick(&negative);
        let terms: Vec<String> = (0..arity).map(|_| operand(rng, true)).collect();
        body.push(format!("!{}", atom_text(rel, &terms)));
    }
    if rng.chance(40) {
        let op = if rng.chance(50) { "=" } else { "!=" };
        body.push(format!(
            "{} {op} {}",
            operand(rng, false),
            operand(rng, false)
        ));
    }
    let head_terms: Vec<String> = (0..head_arity).map(|_| operand(rng, false)).collect();
    // Shuffle the body so that the planner must reorder it.
    for i in (1..body.len()).rev() {
        body.swap(i, rng.below(i + 1));
    }
    format!("{} :- {}.", atom_text(head, &head_terms), body.join(", "))
}

fn generate_program(seed: u64) -> String {
    let mut rng = Rng(seed);
    let mut lines = Vec::new();
    for _ in 0..=rng.below(7) {
        lines.push(generate_rule(&mut rng));
    }
    if rng.chance(50) {
        lines.push(format!("d1({}).", rng.below(4)));
    }
    if rng.chance(30) {
        lines.push(format!("d4({}, {}).", rng.below(4), rng.below(4)));
    }
    lines.join("\n")
}

/// A random graph: node count, edges, start nodes, blocked nodes.
type Graph = (usize, Vec<(usize, usize)>, Vec<usize>, Vec<usize>);

fn graph(max_nodes: usize, max_edges: usize) -> impl Strategy<Value = Graph> {
    (2..max_nodes).prop_flat_map(move |n| {
        (
            Just(n),
            prop::collection::vec((0..n, 0..n), 0..max_edges),
            prop::collection::vec(0..n, 0..3),
            prop::collection::vec(0..n, 0..3),
        )
    })
}

fn int(n: usize) -> Value {
    Value::Int(i64::try_from(n).expect("small"))
}

fn input_facts(g: &Graph) -> Facts {
    let (_, edges, start, blocked) = g;
    let mut facts = Facts::new();
    for &(a, b) in edges {
        facts
            .entry("e".into())
            .or_default()
            .insert(vec![int(a), int(b)]);
    }
    for &a in start {
        facts.entry("s".into()).or_default().insert(vec![int(a)]);
    }
    for &a in blocked {
        facts.entry("b".into()).or_default().insert(vec![int(a)]);
    }
    // An input relation that rules also derive.
    if let Some(&(a, b)) = edges.first() {
        facts
            .entry("d2".into())
            .or_default()
            .insert(vec![int(b), int(a)]);
    }
    facts
}

fn database(facts: &Facts) -> Database {
    let mut db = Database::new();
    for (rel, tuples) in facts {
        for t in tuples {
            db.insert(rel, t);
        }
    }
    db
}

/// Checks that `d` is a valid proof in `out`.
fn valid_proof(out: &Output, d: &Derivation) -> bool {
    if !out.contains(&d.fact.relation, &d.fact.values) {
        return false;
    }
    match &d.reason {
        Reason::Input | Reason::Fact { .. } => true,
        Reason::Rule { premises, .. } => premises.iter().all(|p| match p {
            Premise::Derived(child) => valid_proof(out, child),
            Premise::Absent { relation, args, .. } => !out
                .tuples(relation)
                .iter()
                .any(|t| t.iter().zip(args).all(|(v, a)| a.is_none_or(|a| a == *v))),
            Premise::Holds {
                op, left, right, ..
            } => op.holds(*left, *right),
        }),
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    #[test]
    fn semi_naive_equals_naive(seed in any::<u64>(), g in graph(7, 14), provenance in any::<bool>()) {
        let src = generate_program(seed);
        let program = parse_program(&src).map_err(|e| TestCaseError::fail(format!("{e}\n{src}")))?;
        let input = input_facts(&g);
        let expected = naive(&program, &input);
        let out = evaluate(&program, database(&input), EvalOptions { provenance })
            .map_err(|e| TestCaseError::fail(format!("{e}\n{src}")))?;
        for (rel, _, _) in RELATIONS {
            let got: Relation = out.tuples(rel).into_iter().collect();
            let want = expected.get(rel).cloned().unwrap_or_default();
            prop_assert_eq!(got, want, "relation {} differs for program\n{}", rel, src);
        }
        if provenance {
            for (rel, _, _) in RELATIONS {
                for t in out.tuples(rel) {
                    let d = out.explain(rel, &t).expect("every tuple has a proof");
                    prop_assert!(valid_proof(&out, &d), "bad proof\n{}\nfor program\n{}", d, src);
                }
            }
        }
    }

    #[test]
    fn reachability_with_negation_equals_naive(g in graph(9, 20)) {
        let src = "\
            r(X) :- s(X), !b(X).\n\
            r(Y) :- r(X), e(X, Y), !b(Y).\n\
            n(X) :- e(X, _).\n\
            n(X) :- e(_, X).\n\
            u(X) :- n(X), !r(X).\n";
        let program = parse_program(src).expect("valid");
        let input = input_facts(&g);
        let expected = naive(&program, &input);
        let out = evaluate(&program, database(&input), EvalOptions::default()).expect("ok");
        for rel in ["r", "n", "u"] {
            let got: Relation = out.tuples(rel).into_iter().collect();
            prop_assert_eq!(got, expected.get(rel).cloned().unwrap_or_default());
        }
    }

    #[test]
    fn transitive_closure_equals_bfs(g in graph(40, 120)) {
        let (n, edges, _, _) = &g;
        let mut adjacent = vec![Vec::new(); *n];
        let mut db = Database::new();
        for &(a, b) in edges {
            adjacent[a].push(b);
            db.insert("edge", [int(a), int(b)]);
        }
        let mut expected = Relation::new();
        for from in 0..*n {
            let mut seen = vec![false; *n];
            let mut queue: VecDeque<usize> = adjacent[from].iter().copied().collect();
            while let Some(x) = queue.pop_front() {
                if !seen[x] {
                    seen[x] = true;
                    expected.insert(vec![int(from), int(x)]);
                    queue.extend(adjacent[x].iter().copied());
                }
            }
        }
        let program = parse_program("path(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).")
            .expect("valid");
        let out = evaluate(&program, db, EvalOptions { provenance: false }).expect("ok");
        let got: Relation = out.tuples("path").into_iter().collect();
        prop_assert_eq!(got, expected);
    }
}

#[test]
fn generator_makes_valid_programs() {
    for seed in 0..500 {
        let src = generate_program(seed);
        assert!(parse_program(&src).is_ok(), "{src}");
    }
}
