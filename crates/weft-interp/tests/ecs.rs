//! The typed ECS example: semantics, checker agreement, and reference boundaries.

#![allow(clippy::unwrap_used, clippy::expect_used)]

use weft_check::{agreement, check_source, Checked};
use weft_interp::{run_main, run_tests, Engine, RunOptions};
use weft_sema::Options;
use weft_syntax::diag::{Code, Severity};
use weft_syntax::SourceFile;

const ECS: &str = include_str!("../../../examples/ecs/ecs.wf");

fn checked() -> Checked {
    let c = check_source("ecs.wf", ECS, Options::default());
    let file = SourceFile::new("ecs.wf", ECS);
    let errors: String = c.diags.iter().map(|d| d.render(&file)).collect();
    assert!(c.ok(), "{errors}");
    c
}

#[test]
fn ecs_agrees_with_the_spec() {
    let c = checked();
    assert!(agreement(&c).is_ok(), "checker and spec differ");
}

#[test]
fn ecs_contracts_run_on_both_engines() {
    let c = checked();
    for engine in [Engine::Ast, Engine::Ir] {
        for (seed, workers) in [(1, 1), (42, 4)] {
            let opts = RunOptions {
                engine,
                seed,
                workers,
                oracle: true,
                max_steps: Some(5_000_000),
                ..RunOptions::default()
            };
            let results = run_tests(&c, &opts);
            assert_eq!(results.len(), 15);
            for result in results {
                assert!(
                    result.message.is_none(),
                    "{engine:?}: {}: {:?}",
                    result.name,
                    result.message
                );
                assert!(
                    result.outcome.fallback.is_none(),
                    "IR must run without fallback"
                );
            }
        }
    }
}

#[test]
fn structural_changes_reject_live_component_references() {
    for change in [
        "spawn(w, Position(0, 0), None, 1)",
        "despawn(w, Entity(0, 0))",
        "set_velocity(w, Entity(0, 0), None)",
        "let q = Vec.new(); q.push(Despawn(Entity(0, 0))); apply_commands(w, &q)",
    ] {
        let src = format!(
            "{ECS}\nfn invalid_reference(w: &World) {{\n\
             let p = &w.moving.positions[0]\n{change}\nprint(p.x)\n}}\n"
        );
        let c = check_source("ecs-negative.wf", &src, Options::default());
        let errors: Vec<_> = c
            .diags
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .collect();
        assert_eq!(errors.len(), 1, "{change}: {errors:?}");
        assert_eq!(errors[0].code, Code::W0301, "{change}");
        assert!(agreement(&c).is_ok(), "negative case disagrees: {change}");
    }
}

#[test]
fn conflicting_tasks_are_rejected() {
    let src = format!(
        "{ECS}\nfn conflicting(w: &World) {{\n\
         scope {{ s =>\n\
         s.spawn(|| integrate(w))\n\
         s.spawn(|| print(w.moving.positions[0].x))\n\
         }}\n}}\n"
    );
    let c = check_source("ecs-conflict.wf", &src, Options::default());
    assert!(c.diags.iter().any(|d| d.code == Code::W0405));
    assert!(agreement(&c).is_ok());
}

#[test]
fn ecs_demo_has_a_fixed_result() {
    let c = checked();
    let out = run_main(
        &c,
        &RunOptions {
            oracle: true,
            max_steps: Some(5_000_000),
            ..RunOptions::default()
        },
    )
    .expect("the ECS demo runs");
    assert_eq!(out.stdout, "entities=64 ticks=10 checksum=12768\n");
}
