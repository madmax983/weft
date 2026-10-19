//! The `weft` command.

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // The library runs the command on a large stack (`weft_cli::STACK`).
    match weft_cli::run_live(&args) {
        Ok(out) => {
            print!("{}", out.text);
            eprint!("{}", out.stderr);
            ExitCode::from(out.code)
        }
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(2)
        }
    }
}
