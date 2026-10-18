//! The `weft` command.

use std::process::ExitCode;

use anyhow::{bail, Context, Result};
use weft_check::check_source;
use weft_sema::Options;
use weft_syntax::SourceFile;

fn main() -> ExitCode {
    match run(std::env::args().skip(1).collect()) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(2)
        }
    }
}

fn run(args: Vec<String>) -> Result<ExitCode> {
    let Some(cmd) = args.first() else {
        bail!("usage: weft <check|facts> FILE");
    };
    match cmd.as_str() {
        "check" => {
            let path = args.get(1).context("missing FILE")?;
            let src =
                std::fs::read_to_string(path).with_context(|| format!("cannot read {path}"))?;
            let c = check_source(path, &src, Options::default());
            let file = SourceFile::new(path, src.as_str());
            for d in &c.diags {
                print!("{}", d.render(&file));
            }
            Ok(if c.ok() {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            })
        }
        "facts" => {
            let path = args.get(1).context("missing FILE")?;
            let only = args.get(2);
            let src =
                std::fs::read_to_string(path).with_context(|| format!("cannot read {path}"))?;
            let c = check_source(path, &src, Options::default());
            for b in &c.analysis.bodies {
                if only.is_some_and(|o| *o != b.facts.name) {
                    continue;
                }
                println!("== {}\n{:#?}", b.facts.name, b.facts);
            }
            Ok(ExitCode::SUCCESS)
        }
        other => bail!("unknown command `{other}`"),
    }
}
