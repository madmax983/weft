//! Static checks: arity, range restriction and stratification.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use crate::ast::{Atom, Literal, Program, Rule, Term};
use crate::error::{Error, Location, Place};

/// The result of the checks.
#[derive(Debug)]
pub struct Analysis {
    /// The arity of each relation and the location of its first atom.
    pub arities: BTreeMap<String, (usize, Location)>,
    /// The strongly connected components of the dependency graph, in
    /// evaluation order. A component comes after the components that it
    /// depends on.
    pub components: Vec<Vec<String>>,
}

/// Checks `program` and computes its evaluation order.
pub fn analyze(program: &Program) -> Result<Analysis, Error> {
    let arities = check_arity(program)?;
    for rule in &program.rules {
        check_range(rule)?;
    }
    let components = stratify(program)?;
    Ok(Analysis {
        arities,
        components,
    })
}

/// Checks that all atoms of a relation have the same number of arguments.
fn check_arity(program: &Program) -> Result<BTreeMap<String, (usize, Location)>, Error> {
    let mut arities: BTreeMap<String, (usize, Location)> = BTreeMap::new();
    let mut note = |relation: &str, found: usize, loc: &Location| match arities.get(relation) {
        Some((expected, first)) if *expected != found => Err(Error::Arity {
            loc: loc.clone(),
            relation: relation.to_string(),
            expected: *expected,
            found,
            first: first.clone(),
        }),
        Some(_) => Ok(()),
        None => {
            arities.insert(relation.to_string(), (found, loc.clone()));
            Ok(())
        }
    };
    for fact in &program.facts {
        note(&fact.relation, fact.values.len(), &fact.loc)?;
    }
    for rule in &program.rules {
        note(&rule.head.relation, rule.head.terms.len(), &rule.loc)?;
        for lit in &rule.body {
            if let Literal::Pos(atom) | Literal::Neg(atom) = lit {
                note(&atom.relation, atom.terms.len(), &rule.loc)?;
            }
        }
    }
    Ok(arities)
}

/// Checks range restriction. Every variable in the head, in a negated atom
/// or in a comparison must occur in a positive body atom.
fn check_range(rule: &Rule) -> Result<(), Error> {
    let bound: HashSet<&str> = rule
        .body
        .iter()
        .filter_map(|lit| match lit {
            Literal::Pos(atom) => Some(atom),
            _ => None,
        })
        .flat_map(|atom| &atom.terms)
        .filter_map(|t| match t {
            Term::Var(v) => Some(v.as_str()),
            _ => None,
        })
        .collect();
    let check = |term: &Term, place: Place, wildcard_ok: bool| match term {
        Term::Var(v) if !bound.contains(v.as_str()) => Err(Error::Unbound {
            loc: rule.loc.clone(),
            variable: v.clone(),
            place,
        }),
        Term::Wildcard if !wildcard_ok => Err(Error::Wildcard {
            loc: rule.loc.clone(),
            place,
        }),
        _ => Ok(()),
    };
    for term in &rule.head.terms {
        check(term, Place::Head, false)?;
    }
    for lit in &rule.body {
        match lit {
            Literal::Pos(_) => {}
            Literal::Neg(atom) => {
                for term in &atom.terms {
                    check(term, Place::Negation, true)?;
                }
            }
            Literal::Cmp { left, right, .. } => {
                check(left, Place::Comparison, false)?;
                check(right, Place::Comparison, false)?;
            }
        }
    }
    Ok(())
}

/// The dependency graph: one node for each relation, and an edge from each
/// rule head to each relation in the rule body.
struct Graph<'a> {
    names: Vec<&'a str>,
    ids: HashMap<&'a str, usize>,
    edges: Vec<Vec<usize>>,
}

impl<'a> Graph<'a> {
    fn node(&mut self, name: &'a str) -> usize {
        if let Some(&id) = self.ids.get(name) {
            return id;
        }
        let id = self.names.len();
        self.names.push(name);
        self.ids.insert(name, id);
        self.edges.push(Vec::new());
        id
    }

    fn build(program: &'a Program) -> Self {
        let mut graph = Graph {
            names: Vec::new(),
            ids: HashMap::new(),
            edges: Vec::new(),
        };
        for fact in &program.facts {
            graph.node(&fact.relation);
        }
        for rule in &program.rules {
            let head = graph.node(&rule.head.relation);
            for atom in body_atoms(rule) {
                let dep = graph.node(&atom.relation);
                if !graph.edges[head].contains(&dep) {
                    graph.edges[head].push(dep);
                }
            }
        }
        graph
    }

    /// Returns a shortest path from `from` to `to` inside component `comp`.
    fn path(&self, from: usize, to: usize, comp: &[usize]) -> Vec<usize> {
        let mut prev: HashMap<usize, usize> = HashMap::new();
        let mut queue = VecDeque::from([from]);
        while let Some(u) = queue.pop_front() {
            if u == to {
                break;
            }
            for &v in &self.edges[u] {
                if comp[v] == comp[from] && v != from && !prev.contains_key(&v) {
                    prev.insert(v, u);
                    queue.push_back(v);
                }
            }
        }
        let mut path = vec![to];
        let mut node = to;
        while node != from {
            match prev.get(&node) {
                Some(&p) => node = p,
                None => break,
            }
            path.push(node);
        }
        path.reverse();
        path
    }
}

fn body_atoms(rule: &Rule) -> impl Iterator<Item = &Atom> {
    rule.body.iter().filter_map(|lit| match lit {
        Literal::Pos(atom) | Literal::Neg(atom) => Some(atom),
        Literal::Cmp { .. } => None,
    })
}

/// Tarjan's algorithm for strongly connected components.
struct Tarjan<'a> {
    edges: &'a [Vec<usize>],
    index: Vec<Option<usize>>,
    low: Vec<usize>,
    on_stack: Vec<bool>,
    stack: Vec<usize>,
    next: usize,
    comp: Vec<usize>,
    components: Vec<Vec<usize>>,
}

impl Tarjan<'_> {
    fn visit(&mut self, v: usize) {
        let edges = self.edges;
        self.index[v] = Some(self.next);
        self.low[v] = self.next;
        self.next += 1;
        self.stack.push(v);
        self.on_stack[v] = true;
        for &w in &edges[v] {
            match self.index[w] {
                None => {
                    self.visit(w);
                    self.low[v] = self.low[v].min(self.low[w]);
                }
                Some(iw) if self.on_stack[w] => self.low[v] = self.low[v].min(iw),
                Some(_) => {}
            }
        }
        if Some(self.low[v]) == self.index[v] {
            let id = self.components.len();
            let mut members = Vec::new();
            while let Some(w) = self.stack.pop() {
                self.on_stack[w] = false;
                self.comp[w] = id;
                members.push(w);
                if w == v {
                    break;
                }
            }
            members.reverse();
            self.components.push(members);
        }
    }
}

/// Computes the components in evaluation order. Returns an error if a rule
/// negates a relation in the component of its head.
fn stratify(program: &Program) -> Result<Vec<Vec<String>>, Error> {
    let graph = Graph::build(program);
    let n = graph.names.len();
    let mut tarjan = Tarjan {
        edges: &graph.edges,
        index: vec![None; n],
        low: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::new(),
        next: 0,
        comp: vec![0; n],
        components: Vec::new(),
    };
    for v in 0..n {
        if tarjan.index[v].is_none() {
            tarjan.visit(v);
        }
    }
    for rule in &program.rules {
        let head = graph.ids[rule.head.relation.as_str()];
        for lit in &rule.body {
            let Literal::Neg(atom) = lit else { continue };
            let neg = graph.ids[atom.relation.as_str()];
            if tarjan.comp[neg] == tarjan.comp[head] {
                let mut cycle = format!("{} -> !{}", graph.names[head], graph.names[neg]);
                for &node in graph.path(neg, head, &tarjan.comp).iter().skip(1) {
                    cycle.push_str(" -> ");
                    cycle.push_str(graph.names[node]);
                }
                return Err(Error::Stratification {
                    loc: rule.loc.clone(),
                    relation: rule.head.relation.clone(),
                    cycle,
                });
            }
        }
    }
    Ok(tarjan
        .components
        .iter()
        .map(|c| c.iter().map(|&v| graph.names[v].to_string()).collect())
        .collect())
}
