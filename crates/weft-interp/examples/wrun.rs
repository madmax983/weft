//! Runs a Weft file: `cargo run -p weft-interp --example wrun -- FILE [SEED]`.

#![allow(clippy::unwrap_used, clippy::expect_used, missing_docs)]

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = &args[1];
    let seed = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
    let src = std::fs::read_to_string(path).unwrap();
    let checked = weft_check::check_source(path, &src, weft_sema::Options::default());
    let file = weft_syntax::SourceFile::new(path, src.as_str());
    for d in &checked.diags {
        eprint!("{}", d.render(&file));
    }
    let opts = weft_interp::RunOptions {
        seed,
        max_steps: Some(10_000_000),
        ..weft_interp::RunOptions::default()
    };
    if checked.analysis.program.tests.is_empty() {
        match weft_interp::run_main(&checked, &opts) {
            Ok(o) => {
                print!("{}", o.stdout);
                eprint!("{}", o.stderr);
                if std::env::var("TRACE").is_ok() {
                    for e in &o.trace {
                        eprintln!("  {e}");
                    }
                }
                eprintln!("leaked_rc={} blocking={}", o.leaked_rc, o.blocking_calls);
            }
            Err(e) => {
                print!("{}", e.outcome.stdout);
                eprint!("{}", e.outcome.stderr);
                if std::env::var("TRACE").is_ok() {
                    for ev in &e.outcome.trace {
                        eprintln!("  {ev}");
                    }
                }
                let line = e.span.map_or(0, |s| file.line(s));
                eprintln!("error (line {line}): {e}");
            }
        }
    } else {
        for t in weft_interp::run_tests(&checked, &opts) {
            print!("{}", t.outcome.stdout);
            println!(
                "test {}: {}",
                t.name,
                if t.passed {
                    "ok".to_string()
                } else {
                    format!("FAILED {:?}", t.message)
                }
            );
        }
    }
}
