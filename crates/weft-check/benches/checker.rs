//! The production checker against the general Datalog engine on the same facts.
//!
//! The design asks for a checker that agrees with the spec and stays fast. This
//! benchmark measures both on the corpus and on one large generated function.

#![allow(clippy::significant_drop_tightening)]

use std::fmt::Write as _;

use criterion::{criterion_group, criterion_main, Criterion};
use weft_check::{bridge, check, check_source};
use weft_sema::Options;

/// A function with `n` blocks of borrow, mutation and use.
fn large_program(n: usize) -> String {
    let mut s =
        String::from("struct E { hp: u64 }\nstruct W { es: Vec<E>, log: Vec<u64>, n: u64 }\n");
    s.push_str("fn big(w: &W) / mut(w..) {\n");
    for i in 0..n {
        let _ = writeln!(s, "    let r{i} = &w.es[0]");
        let _ = writeln!(s, "    w.log.push({i})");
        let _ = writeln!(s, "    if w.n > {i} {{ w.n += 1 }}");
        let _ = writeln!(s, "    print(r{i}.hp)");
    }
    s.push_str("}\n");
    s
}

fn bench(c: &mut Criterion) {
    let src = large_program(200);
    let facts = check_source("big.wf", &src, Options::default())
        .analysis
        .bodies[0]
        .facts
        .clone();
    let mut g = c.benchmark_group("large function (200 blocks)");
    g.sample_size(10);
    g.bench_function("production checker", |b| b.iter(|| check(&facts)));
    g.bench_function("datalog spec", |b| b.iter(|| bridge::check_spec(&facts)));
    g.finish();

    let corpus = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/programs");
    let mut all = Vec::new();
    if let Ok(dir) = std::fs::read_dir(corpus) {
        for e in dir.flatten() {
            if let Ok(text) = std::fs::read_to_string(e.path()) {
                let opts = Options {
                    library: text.contains("// weft: library"),
                    no_runtime: false,
                };
                all.extend(
                    check_source("x.wf", &text, opts)
                        .analysis
                        .bodies
                        .into_iter()
                        .map(|b| b.facts),
                );
            }
        }
    }
    let mut g = c.benchmark_group("corpus");
    g.bench_function("production checker", |b| {
        b.iter(|| {
            all.iter()
                .filter(|f| check(f).violations.is_clean())
                .count()
        });
    });
    g.bench_function("datalog spec", |b| {
        b.iter(|| all.iter().filter(|f| bridge::check_spec(f).is_ok()).count());
    });
    g.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
