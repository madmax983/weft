//! The `weft` command.

use std::process::ExitCode;

/// The stack of the thread that runs the command. The derivation printer of
/// `check --explain` recurses once for each step of a derivation, and a long
/// path of the control-flow graph gives a deep derivation. The system only
/// reserves this memory; it uses a page when the recursion gets to it.
const STACK: usize = 256 * 1024 * 1024;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let thread_args = args.clone();
    let worker = std::thread::Builder::new()
        .name("weft".into())
        .stack_size(STACK)
        .spawn(move || weft_cli::run_live(&thread_args));
    let result = match worker {
        Ok(handle) => match handle.join() {
            Ok(result) => result,
            // The panic hook has written the message.
            Err(_) => return ExitCode::from(101),
        },
        // With no memory for the large stack, the main thread runs the command.
        Err(_) => weft_cli::run_live(&args),
    };
    match result {
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
