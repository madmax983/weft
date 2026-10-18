//! The `weft` command.

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match weft_cli::run(&args) {
        Ok(out) => {
            print!("{}", out.text);
            ExitCode::from(out.code)
        }
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(2)
        }
    }
}
