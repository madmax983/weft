//! The `weft` command as a library, so tests can call each command.

pub mod package;

use std::fmt::Write as _;
use std::path::Path;
use weft_syntax::diag::Code;

use anyhow::{bail, Context, Result};
use weft_check::{agreement, bridge, check_analysis, codes, Checked};
use weft_datalog::{evaluate, parse_program_named, EvalOptions};
use weft_interp::{Engine, RunOptions, RuntimeError};
use weft_sema::{FactGen, Groups};
use weft_syntax::diag::{Diagnostic, Severity};

use crate::package::{load, package_diags, Package, Profile, SyntaxError};

/// The usage text.
pub const USAGE: &str = "\
usage: weft <command> [options] PATH

commands:
  check   [PROFILE] [FACTS] [--json] [--explain] PATH            check a file or a package
  run     [PROFILE] [FACTS] [RUN] PATH                           check, then run `fn main`
  test    [PROFILE] [FACTS] [RUN] PATH                           check, then run the test blocks
  facts   [PROFILE] [FACTS] PATH [FUNCTION]                      print the facts in Datalog syntax
  ir      [PROFILE] PATH [FUNCTION]                              print the core IR (docs/ir.md)
  agree   [PROFILE] [FACTS] PATH                                 compare the checker with spec/weft.dl
  lint    [PROFILE] [FACTS] --rules RULES.dl PATH                run user lint rules over the facts
  explain CODE                                                   explain a diagnostic code
  deps    PATH                                                   check dependency authority
  spec                                                           print spec/weft.dl
  help    [COMMAND]                                              print this text

PROFILE is --lib or --bin, and --no-runtime or --runtime. A single file sets
its profile with marker lines: `// weft: library` and `// weft: no-runtime`.
A package sets it in weft.toml. A flag wins over both.

FACTS is --facts=old|ir|both: the fact pipeline (docs/plan/core-ir.md 2.6).
--facts=old (the default) uses the facts of the old lowering. --facts=ir uses
the facts of the core IR for a program in scope: each construct group that
the program uses must be on. Else the old pipeline checks the program, and a
note tells why. --facts=both makes both fact sets: the output is that of the
old pipeline; `check` writes a note for each diagnostic that only one
pipeline gives, `facts` also prints the facts of the ir pipeline, and `agree`
compares both.

RUN is [--seed N] [--workers N] [--unchecked] [--oracle] [--engine=ast|ir].
`run` and `test` do not run a program that has errors, unless --unchecked is given.
--seed (default 0) and --workers (1 to 1024, default 4) set the deterministic scheduler.
--oracle turns on strict run-time checks: a dangling reference, a moved `Vec`
buffer, a linear leak, a data race and a stealable task that reaches a
nonportable value are run-time errors.
--engine=ir runs the core IR (docs/ir.md 8.1). A program with a body that has
no IR (a type error, an error in a declaration, W0303) has errors: the AST
compiler runs it, and a note tells why. --engine=ast (the default) runs the AST
compiler.

Exit codes: 0 on success; 1 when the program has errors or fails; 2 on a usage
error or a file that cannot be read. With --unchecked, the exit code of `run`
and `test` shows only the run.
";

/// The most virtual workers of `run` and `test`.
pub const MAX_WORKERS: usize = 1024;

/// The output of a command.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Output {
    /// The text for standard output.
    pub text: String,
    /// The text for standard error.
    pub stderr: String,
    /// The exit code: 0 is success, 1 means the program has errors or failed.
    pub code: u8,
}

/// Command-line flags.
#[derive(Clone, Debug, Default)]
struct Flags {
    profile: Profile,
    json: bool,
    explain: bool,
    unchecked: bool,
    oracle: bool,
    rules: Option<String>,
    seed: Option<u64>,
    workers: Option<usize>,
    engine: Engine,
    facts: FactGen,
    positional: Vec<String>,
    /// The options as given, for the check that the command takes them.
    given: Vec<String>,
}

/// The profile options.
const PROFILE: [&str; 4] = ["--lib", "--bin", "--no-runtime", "--runtime"];

/// Returns the options that a command takes, or `None` for an unknown command.
fn options_of(cmd: &str) -> Option<Vec<&'static str>> {
    let own: &[&str] = match cmd {
        "check" => &["--json", "--explain", "--facts"],
        "run" | "test" => &[
            "--seed",
            "--workers",
            "--unchecked",
            "--oracle",
            "--engine",
            "--facts",
        ],
        "lint" => &["--rules", "--facts"],
        "facts" | "agree" => &["--facts"],
        "ir" => &[],
        "explain" | "deps" | "spec" | "help" | "--help" | "-h" => return Some(Vec::new()),
        _ => return None,
    };
    Some(PROFILE.iter().chain(own).copied().collect())
}

/// Returns the positional arguments of a command: the names of the arguments
/// that it needs, then the names of the arguments that it can take.
fn positional_of(cmd: &str) -> (&'static [&'static str], &'static [&'static str]) {
    match cmd {
        "check" | "run" | "test" | "agree" | "lint" | "deps" => (&["PATH"], &[]),
        "facts" | "ir" => (&["PATH"], &["FUNCTION"]),
        "explain" => (&["CODE"], &[]),
        "help" | "--help" | "-h" => (&[], &["COMMAND"]),
        _ => (&[], &[]),
    }
}

/// Checks the number of positional arguments of a command.
fn check_positional(cmd: &str, given: &[String]) -> Result<()> {
    let (needs, can) = positional_of(cmd);
    if let Some(name) = needs.get(given.len()) {
        bail!("`{cmd}` needs a {name}; see `weft help`");
    }
    let max = needs.len() + can.len();
    if let Some(extra) = given.get(max) {
        let takes = match (max, can.is_empty()) {
            (0, _) => "takes no arguments".to_string(),
            (1, true) => "takes 1 argument".to_string(),
            (n, true) => format!("takes {n} arguments"),
            (1, false) => "takes at most 1 argument".to_string(),
            (n, false) => format!("takes at most {n} arguments"),
        };
        bail!(
            "`{cmd}` {takes}, found {}: `{extra}` is extra; see `weft help`",
            given.len()
        );
    }
    Ok(())
}

/// Reads the number after an option.
fn number<T: std::str::FromStr>(it: &mut std::slice::Iter<'_, String>, opt: &str) -> Result<T> {
    let v = it.next().with_context(|| format!("{opt} needs a number"))?;
    v.parse()
        .ok()
        .with_context(|| format!("{opt} needs a number, found `{v}`"))
}

/// Reads the value of `--engine`.
fn engine(v: Option<&str>) -> Result<Engine> {
    match v {
        Some("ast") => Ok(Engine::Ast),
        Some("ir") => Ok(Engine::Ir),
        Some(v) => bail!("--engine needs `ast` or `ir`, found `{v}`"),
        None => bail!("--engine needs `ast` or `ir`"),
    }
}

/// Reads the value of `--facts`.
fn fact_gen(v: Option<&str>) -> Result<FactGen> {
    let need = "--facts needs `old`, `ir` or `both`";
    match v {
        Some(v) => FactGen::parse(v).with_context(|| format!("{need}, found `{v}`")),
        None => bail!("{need}"),
    }
}

fn flags(args: &[String]) -> Result<Flags> {
    let mut f = Flags::default();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--lib" => f.profile.library = Some(true),
            "--bin" => f.profile.library = Some(false),
            "--no-runtime" => f.profile.no_runtime = Some(true),
            "--runtime" => f.profile.no_runtime = Some(false),
            "--json" => f.json = true,
            "--explain" => f.explain = true,
            "--unchecked" => f.unchecked = true,
            "--oracle" => f.oracle = true,
            "--rules" => f.rules = Some(it.next().context("--rules needs a file")?.clone()),
            "--seed" => f.seed = Some(number(&mut it, "--seed")?),
            "--engine" => f.engine = engine(it.next().map(String::as_str))?,
            "--facts" => f.facts = fact_gen(it.next().map(String::as_str))?,
            s if s.starts_with("--facts=") => {
                f.facts = fact_gen(s.strip_prefix("--facts="))?;
                f.given.push("--facts".into());
                continue;
            }
            s if s.starts_with("--engine=") => {
                f.engine = engine(s.strip_prefix("--engine="))?;
                f.given.push("--engine".into());
                continue;
            }
            "--workers" => {
                let v = it.next().context("--workers needs a number")?;
                match v.parse::<usize>() {
                    Ok(n) if (1..=MAX_WORKERS).contains(&n) => f.workers = Some(n),
                    _ => bail!("--workers needs a number from 1 to {MAX_WORKERS}, found `{v}`"),
                }
            }
            s if s.starts_with("--") => bail!("unknown option `{s}`"),
            s => {
                f.positional.push(s.to_string());
                continue;
            }
        }
        f.given.push(a.clone());
    }
    Ok(f)
}

/// Runs one command on a thread with a [`weft_sema::STACK`] stack. The output
/// of a Weft program stays in [`Output`].
pub fn run(args: &[String]) -> Result<Output> {
    on_large_stack(args, false)
}

/// Runs one command, and writes the output of a Weft program at once.
///
/// `weft run` and `weft test` write to the process standard output and
/// standard error while the program runs, so the log of a test comes before
/// its result line.
pub fn run_live(args: &[String]) -> Result<Output> {
    on_large_stack(args, true)
}

/// Runs one command on a thread with a [`weft_sema::STACK`] stack
/// ([`weft_sema::on_large_stack`]). Sema, the checker and the interpreter use
/// the same thread.
fn on_large_stack(args: &[String], live: bool) -> Result<Output> {
    weft_sema::on_large_stack(|| run_with(args, live))
}

fn run_with(args: &[String], live: bool) -> Result<Output> {
    let Some((cmd, rest)) = args.split_first() else {
        return Ok(Output {
            text: USAGE.into(),
            code: 2,
            ..Output::default()
        });
    };
    let cmd = cmd.as_str();
    let Some(takes) = options_of(cmd) else {
        bail!("unknown command `{cmd}`\n{USAGE}");
    };
    let f = flags(rest)?;
    if let Some(o) = f.given.iter().find(|o| !takes.contains(&o.as_str())) {
        bail!("`{cmd}` does not take {o}; see `weft help`");
    }
    check_positional(cmd, &f.positional)?;
    if let ("help" | "--help" | "-h", Some(c)) = (cmd, f.positional.first()) {
        if options_of(c).is_none() {
            bail!("unknown command `{c}`\n{USAGE}");
        }
    }
    let out = match cmd {
        "check" => check(&f),
        "run" => run_main(&f, live),
        "test" => run_tests(&f, live),
        "facts" => facts(&f),
        "ir" => ir(&f),
        "agree" => agree(&f),
        "lint" => lint(&f),
        "explain" => explain(&f),
        "deps" => deps(&f),
        "spec" => Ok(Output {
            text: bridge::SPEC_SRC.into(),
            ..Output::default()
        }),
        _ => Ok(Output {
            text: USAGE.into(),
            ..Output::default()
        }),
    };
    // A file that does not parse is an error of the program, not of the usage.
    out.or_else(|e| match e.downcast::<SyntaxError>() {
        Ok(s) => Ok(syntax_output(cmd, &f, &s)),
        Err(e) => Err(e),
    })
}

/// The output for a file that does not parse: W0001, and exit code 1.
fn syntax_output(cmd: &str, f: &Flags, s: &SyntaxError) -> Output {
    let mut out = Output {
        code: 1,
        ..Output::default()
    };
    if cmd != "check" {
        out.stderr = s.diag.render(&s.file);
    } else if f.json {
        out.text = format!("{}\n", diag_json_in(Some(&s.file), &s.diag));
    } else {
        out.text = s.diag.render(&s.file);
        let _ = writeln!(
            out.text,
            "{}: 1 error(s), 0 function(s) checked",
            f.positional.first().map_or("", String::as_str)
        );
    }
    out
}

/// Returns the first positional argument. [`check_positional`] makes sure
/// that a command that needs it has it.
fn path_arg(f: &Flags) -> Result<&str> {
    f.positional
        .first()
        .map(String::as_str)
        .context("missing PATH; see `weft help`")
}

/// Loads, analyzes and checks a file or a package. The flags win over the
/// options of the manifest or of the file markers.
pub fn check_path(path: &Path, profile: Profile) -> Result<(Package, Checked)> {
    check_path_with(path, profile, FactGen::Old, Groups::NONE)
}

/// Loads, analyzes and checks a file or a package with a fact pipeline.
///
/// `facts` is the pipeline and `groups` the construct groups of the `ir`
/// pipeline (plan §2.6). With [`FactGen::Both`], [`Checked::ir`] holds the
/// check of the `ir` pipeline for a program in scope.
pub fn check_path_with(
    path: &Path,
    profile: Profile,
    facts: FactGen,
    groups: Groups,
) -> Result<(Package, Checked)> {
    let pkg = load(path)?;
    let opts = weft_sema::Options {
        facts,
        ir_groups: groups,
        ..pkg.options(profile)
    };
    let analysis = weft_sema::analyze(&pkg.units, opts);
    let mut checked = check_analysis(analysis, &pkg.files);
    finish_diags(&pkg, &mut checked);
    if let Some(ir) = checked.ir.as_deref_mut() {
        finish_diags(&pkg, ir);
    }
    Ok((pkg, checked))
}

/// Adds the diagnostics of the package and of the file markers, and sorts.
fn finish_diags(pkg: &Package, checked: &mut Checked) {
    checked.diags.extend(package_diags(pkg, &checked.analysis));
    checked.diags.extend(pkg.marker_diags());
    checked
        .diags
        .sort_by(|a, b| (a.unit, a.span.lo, &a.code).cmp(&(b.unit, b.span.lo, &b.code)));
}

/// Checks the program of the flags with their fact pipeline. Returns the
/// package, the check, and the note of the fallback to the old pipeline, if
/// any (empty otherwise).
fn check_flags(f: &Flags) -> Result<(Package, Checked, String)> {
    let path = Path::new(path_arg(f)?);
    let (pkg, c) = check_path_with(path, f.profile, f.facts, Groups::NONE)?;
    let note = c
        .analysis
        .ir_scope
        .as_ref()
        .and_then(|s| s.fallback.as_ref())
        .map_or_else(String::new, |why| {
            format!(
                "note: --facts={}: the old pipeline checks the program: {why}\n",
                f.facts.name()
            )
        });
    Ok((pkg, c, note))
}

/// The notes of `--facts=both` for a program in scope: each diagnostic that
/// only one pipeline gives.
fn both_notes(pkg: &Package, c: &Checked) -> String {
    let Some(ir) = c.ir.as_deref() else {
        return String::new();
    };
    let key = |d: &Diagnostic| (d.unit, d.span.lo, d.code, d.severity == Severity::Error);
    let text = |d: &Diagnostic| {
        let sev = if d.severity == Severity::Error {
            "error"
        } else {
            "warning"
        };
        let at = pkg.files.get(d.unit).map_or_else(String::new, |f| {
            let (line, col) = f.line_col(d.span.lo);
            format!(" at {}:{line}:{col}", f.name)
        });
        format!("{sev}[{}]{at}", d.code)
    };
    let mut out = String::new();
    for (side, mine, other) in [("old", &c.diags, &ir.diags), ("ir", &ir.diags, &c.diags)] {
        let mut rest: Vec<_> = other.iter().map(key).collect();
        for d in mine {
            if let Some(i) = rest.iter().position(|k| *k == key(d)) {
                rest.swap_remove(i);
            } else {
                let _ = writeln!(
                    out,
                    "note: --facts=both: only the {side} pipeline gives {}",
                    text(d)
                );
            }
        }
    }
    out
}

fn render(pkg: &Package, d: &Diagnostic) -> String {
    pkg.files.get(d.unit).map_or_else(
        || format!("{}[{}]: {}\n", "error", d.code, d.message),
        |f| d.render(f),
    )
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Writes one diagnostic as a JSON object, for coding agents.
pub fn diag_json(pkg: &Package, d: &Diagnostic) -> String {
    diag_json_in(pkg.files.get(d.unit), d)
}

/// Writes one diagnostic in `file` as a JSON object.
fn diag_json_in(file: Option<&weft_syntax::SourceFile>, d: &Diagnostic) -> String {
    let (line, col) = file.map_or((0, 0), |f| f.line_col(d.span.lo));
    let name = file.map_or_else(String::new, |f| f.name.clone());
    // A note with a location keeps its line, as the text form shows it.
    let notes: Vec<String> = d
        .notes
        .iter()
        .map(|n| match (n.span, file) {
            (Some(s), Some(f)) => format!(
                "{{\"text\":{},\"line\":{}}}",
                json_escape(&n.text),
                f.line_col(s.lo).0
            ),
            _ => format!("{{\"text\":{}}}", json_escape(&n.text)),
        })
        .collect();
    let sev = if d.severity == Severity::Error {
        "error"
    } else {
        "warning"
    };
    format!(
        "{{\"code\":{},\"severity\":\"{sev}\",\"message\":{},\"file\":{},\"line\":{line},\"column\":{col},\"notes\":[{}]}}",
        json_escape(d.code.as_str()),
        json_escape(&d.message),
        json_escape(&name),
        notes.join(",")
    )
}

fn check(f: &Flags) -> Result<Output> {
    let path = Path::new(path_arg(f)?);
    let (pkg, c, note) = check_flags(f)?;
    let stderr = note + &both_notes(&pkg, &c);
    let mut text = String::new();
    for d in &c.diags {
        if f.json {
            text.push_str(&diag_json(&pkg, d));
            text.push('\n');
        } else {
            text.push_str(&render(&pkg, d));
        }
    }
    if f.explain {
        for (i, b) in c.analysis.bodies.iter().enumerate() {
            let Some(file) = pkg.files.get(b.unit) else {
                continue;
            };
            let line_of = |o: u32| file.line_col(o).0;
            let ex = bridge::explain(&b.facts, &line_of).map_err(|e| anyhow::anyhow!("{e}"))?;
            for e in ex {
                // The diagnostic that reports the fact of this body
                // (`Diagnostic::facts`).
                let key = bridge::body_key(i, &e.key);
                let diag = c
                    .diags
                    .iter()
                    .find(|d| d.unit == b.unit && d.facts.contains(&key))
                    .map(|d| (d, file.line_col(d.span.lo)));
                if f.json {
                    let link = diag.map_or_else(
                        || "null".to_string(),
                        |(d, (line, col))| {
                            format!(
                                "{{\"code\":{},\"line\":{line},\"column\":{col}}}",
                                json_escape(d.code.as_str())
                            )
                        },
                    );
                    let _ = writeln!(
                        text,
                        "{{\"derivation\":{},\"function\":{},\"diagnostic\":{link}}}",
                        e.json,
                        json_escape(&b.facts.name)
                    );
                } else {
                    let link = diag.map_or_else(String::new, |(d, (line, _))| {
                        let sev = if d.severity == Severity::Error {
                            "error"
                        } else {
                            "warning"
                        };
                        format!(", for {sev}[{}] at line {line}", d.code)
                    });
                    let _ = write!(
                        text,
                        "derivation of {} in `{}`{link}:\n{}",
                        e.fact, b.facts.name, e.tree
                    );
                }
            }
        }
    }
    if !f.json {
        let errors = c
            .diags
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .count();
        let _ = writeln!(
            text,
            "{}: {errors} error(s), {} function(s) checked",
            path.display(),
            c.analysis.bodies.len()
        );
    }
    Ok(Output {
        text,
        stderr,
        code: u8::from(!c.ok()),
    })
}

fn facts(f: &Flags) -> Result<Output> {
    let path = Path::new(path_arg(f)?);
    let only = f.positional.get(1);
    let (_, c, stderr) = check_flags(f)?;
    let mut text = String::new();
    for b in &c.analysis.bodies {
        if only.is_some_and(|o| *o != b.facts.name) {
            continue;
        }
        text.push_str(&bridge::facts_text(&b.facts));
    }
    if let Some(ir) = c.ir.as_deref() {
        for b in &ir.analysis.bodies {
            if only.is_some_and(|o| *o != b.facts.name) {
                continue;
            }
            text.push_str("// the ir pipeline\n");
            text.push_str(&bridge::facts_text(&b.facts));
        }
    }
    if let (Some(name), true) = (only, text.is_empty()) {
        let names: Vec<&str> = c
            .analysis
            .bodies
            .iter()
            .map(|b| b.facts.name.as_str())
            .collect();
        let bodies = if names.is_empty() {
            "it has no functions or tests".to_string()
        } else {
            format!("the bodies are `{}`", names.join("`, `"))
        };
        return Ok(Output {
            stderr: format!(
                "{stderr}error: no function or test `{name}` in {}; {bodies}\n",
                path.display()
            ),
            code: 1,
            ..Output::default()
        });
    }
    Ok(Output {
        text,
        stderr,
        ..Output::default()
    })
}

/// Prints the core IR of a file or a package, or of one function or test
/// (`docs/ir.md` 3.3). A body that the builder does not lower yet, or that has
/// a type error, gets a comment line. A broken rule of the verifier is a bug
/// of the builder: the command writes it to standard error and exits with 1.
/// Returns true if body `b` of `p` is body `top` or a body inside it: a
/// parent of a parent of `b` is `top`.
fn inside(p: &weft_ir::Program, b: weft_ir::BodyId, top: weft_ir::BodyId) -> bool {
    let mut cur = Some(b);
    // A parent has a lower id, so the walk ends; the bound is for a program
    // that is not well formed.
    for _ in 0..=p.bodies.len() {
        match cur {
            Some(x) if x == top => return true,
            Some(x) => cur = p.body(x).and_then(|d| d.parent),
            None => return false,
        }
    }
    false
}

fn ir(f: &Flags) -> Result<Output> {
    let path = Path::new(path_arg(f)?);
    let only = f.positional.get(1);
    let pkg = load(path)?;
    let analysis = weft_sema::analyze(&pkg.units, pkg.options(f.profile));
    let built = weft_sema::irbuild::build(&analysis);
    let at = |unit: usize, span: weft_syntax::ast::Span| {
        pkg.files.get(unit).map_or_else(
            || format!("{}..{}", span.lo, span.hi),
            |sf| {
                let (line, col) = sf.line_col(span.lo);
                format!("{}:{line}:{col}", sf.name)
            },
        )
    };
    let mut out = Output::default();
    match only {
        None => out.text = weft_sema::irbuild::text(&built, &at),
        Some(name) => {
            let Some(e) = built.entries.iter().find(|e| e.name == *name) else {
                let names: Vec<&str> = built.entries.iter().map(|e| e.name.as_str()).collect();
                let bodies = if names.is_empty() {
                    "it has no functions or tests".to_string()
                } else {
                    format!("the bodies are `{}`", names.join("`, `"))
                };
                out.stderr = format!(
                    "error: no function or test `{name}` in {}; {bodies}\n",
                    path.display()
                );
                out.code = 1;
                return Ok(out);
            };
            match &e.outcome {
                weft_sema::irbuild::Outcome::Built(id) => {
                    // The body, then the bodies inside it (its closures).
                    for b in 0..built.program.bodies.len() {
                        let b = weft_ir::BodyId(u32::try_from(b).unwrap_or(u32::MAX));
                        if inside(&built.program, b, *id) {
                            if !out.text.is_empty() {
                                out.text.push('\n');
                            }
                            out.text += &weft_ir::print::print_body(&built.program, &built.tys, b);
                        }
                    }
                }
                weft_sema::irbuild::Outcome::Unsupported(u) => {
                    out.stderr = format!(
                        "error: `{name}` has no IR: the builder does not lower {} at {} (stage {})\n",
                        u.construct.name(),
                        at(e.unit, u.span),
                        u.construct.stage()
                    );
                    out.code = 1;
                }
                weft_sema::irbuild::Outcome::NoIr(n) => {
                    out.stderr = format!("error: `{name}` has no IR: {}\n", n.reason());
                    out.code = 1;
                }
            }
        }
    }
    for b in &built.broken {
        let _ = writeln!(out.stderr, "error: a bug of the IR builder: {b}");
        out.code = 1;
    }
    Ok(out)
}

fn agree(f: &Flags) -> Result<Output> {
    let (_, c, stderr) = check_flags(f)?;
    let mut out = agree_text(&c, "");
    if let Some(ir) = c.ir.as_deref() {
        let more = agree_text(ir, " of the ir pipeline");
        out.text += &more.text;
        out.code = out.code.max(more.code);
    }
    out.stderr = stderr;
    Ok(out)
}

/// The output of `agree` for one check. `what` follows the count of bodies.
fn agree_text(c: &Checked, what: &str) -> Output {
    match agreement(c) {
        Ok(n) => Output {
            text: format!("agree: the checker and spec/weft.dl agree on {n} bodies{what}\n"),
            ..Output::default()
        },
        Err(bad) => {
            let mut text = String::new();
            for b in bad {
                let _ = match &b.spec {
                    Ok(spec) if *spec != b.checker => writeln!(
                        text,
                        "disagree in `{}`\n  checker: {:?}\n  spec:    {spec:?}",
                        b.function, b.checker
                    ),
                    Ok(_) => writeln!(text, "disagree in `{}`: the evidence", b.function),
                    Err(e) => writeln!(text, "disagree in `{}`: {e}", b.function),
                };
                for e in &b.evidence {
                    let _ = writeln!(text, "  evidence: {e}");
                }
            }
            if !what.is_empty() {
                let _ = writeln!(text, "(the bodies{what})");
            }
            Output {
                text,
                code: 1,
                ..Output::default()
            }
        }
    }
}

/// Runs user lint rules. A rule file defines `lint(Name, Node)`.
fn lint(f: &Flags) -> Result<Output> {
    let rules_path = f.rules.as_ref().context("lint needs --rules RULES.dl")?;
    let src =
        std::fs::read_to_string(rules_path).with_context(|| format!("cannot read {rules_path}"))?;
    let user = parse_program_named(rules_path, &src).map_err(|e| anyhow::anyhow!("{e}"))?;
    if !user.relations_defined().contains("lint") {
        bail!("{rules_path} must define `lint(Name, Node)`");
    }
    let heads = user
        .rules()
        .iter()
        .map(|r| (r.head.relation.as_str(), r.head.terms.len(), &r.loc));
    let facts = user
        .facts()
        .iter()
        .map(|f| (f.relation.as_str(), f.values.len(), &f.loc));
    if let Some((_, n, loc)) = heads
        .chain(facts)
        .find(|&(rel, n, _)| rel == "lint" && n != 2)
    {
        bail!("{loc}: `lint` must have 2 arguments (Name, Node), found {n}");
    }
    let mut program = bridge::spec().clone();
    program.extend(user);
    let (pkg, c, stderr) = check_flags(f)?;
    let mut text = String::new();
    let mut count = 0;
    for b in &c.analysis.bodies {
        let out = evaluate(
            &program,
            bridge::database(&b.facts),
            EvalOptions { provenance: false },
        )
        .map_err(|e| anyhow::anyhow!("{e}"))?;
        for t in out.tuples("lint") {
            let [name, node] = t.as_slice() else {
                continue;
            };
            let name = out.display_value(*name).trim_matches('"').to_string();
            let node = out.display_value(*node);
            let span = node
                .strip_prefix('n')
                .and_then(|n| n.parse::<usize>().ok())
                .and_then(|n| b.facts.nodes.get(n))
                .map(|n| n.span)
                .unwrap_or_default();
            let mut d = Diagnostic::warning(
                Code::L0001,
                format!("lint `{name}` in `{}`", b.facts.name),
                span,
            );
            d.unit = b.unit;
            text.push_str(&render(&pkg, &d));
            count += 1;
        }
    }
    let _ = writeln!(text, "{count} lint warning(s)");
    Ok(Output {
        text,
        stderr,
        ..Output::default()
    })
}

fn explain(f: &Flags) -> Result<Output> {
    let code = path_arg(f)?;
    let c = codes::lookup(code).with_context(|| format!("unknown code `{code}`"))?;
    Ok(Output {
        text: format!("{}: {}\nrule: {}\n{}\n", c.code, c.title, c.rule, c.text),
        ..Output::default()
    })
}

fn deps(f: &Flags) -> Result<Output> {
    let path = Path::new(path_arg(f)?);
    let (pkg, c) = check_path(path, Profile::default())?;
    let mut text = String::new();
    let mut bad = 0;
    for d in package_diags(&pkg, &c.analysis) {
        text.push_str(&render(&pkg, &d));
        bad += 1;
    }
    for dep in &pkg.deps {
        let _ = writeln!(
            text,
            "dependency `{}`: authority [{}]",
            dep.name,
            dep.written.join(", ")
        );
    }
    let _ = writeln!(text, "{bad} authority error(s)");
    Ok(Output {
        text,
        code: u8::from(bad > 0),
        ..Output::default()
    })
}

/// Where `run` and `test` write. A live sink writes to the process at once.
struct Sink {
    live: bool,
    out: Output,
}

impl Sink {
    fn stdout(&mut self, s: &str) {
        if self.live {
            print!("{s}");
        } else {
            self.out.text.push_str(s);
        }
    }

    fn stderr(&mut self, s: &str) {
        if self.live {
            eprint!("{s}");
        } else {
            self.out.stderr.push_str(s);
        }
    }
}

/// Checks the program for `run` and `test`. Writes the diagnostics to standard
/// error. Returns `None` if the program has errors and `--unchecked` is not given.
fn checked_program(f: &Flags, sink: &mut Sink) -> Result<Option<(Package, Checked)>> {
    let path = Path::new(path_arg(f)?);
    let (pkg, c, note) = check_flags(f)?;
    sink.stderr(&note);
    sink.stderr(&both_notes(&pkg, &c));
    for d in &c.diags {
        sink.stderr(&render(&pkg, d));
    }
    if c.ok() || f.unchecked {
        return Ok(Some((pkg, c)));
    }
    let errors = c
        .diags
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .count();
    sink.stderr(&format!(
        "error: {} has {errors} error(s); it does not run. Fix them, or give --unchecked to run it anyway\n",
        path.display()
    ));
    sink.out.code = 1;
    Ok(None)
}

fn run_options(f: &Flags, pkg: &Package, capture: bool) -> RunOptions {
    let defaults = RunOptions::default();
    RunOptions {
        seed: f.seed.unwrap_or(defaults.seed),
        workers: f.workers.unwrap_or(defaults.workers),
        capture_output: capture,
        no_runtime: pkg.options(f.profile).no_runtime,
        oracle: f.oracle,
        engine: f.engine,
        ..defaults
    }
}

/// The note of `--engine=ir` when the AST compiler runs the program.
fn fallback_note(why: &str) -> String {
    format!("note: --engine=ir: the AST compiler runs the program: {why}\n")
}

/// Shows a run-time error, with its location when the program is one file.
fn runtime_error(pkg: &Package, e: &RuntimeError) -> String {
    let mut s = format!("error: {e}\n");
    if let (Some(span), [_, file]) = (e.span, pkg.files.as_slice()) {
        let (line, col) = file.line_col(span.lo);
        let _ = writeln!(s, "  --> {}:{line}:{col}", file.name);
    }
    s
}

/// `weft run`: checks the program, then runs `fn main`.
fn run_main(f: &Flags, live: bool) -> Result<Output> {
    let mut sink = Sink {
        live,
        out: Output::default(),
    };
    let Some((pkg, c)) = checked_program(f, &mut sink)? else {
        return Ok(sink.out);
    };
    let opts = run_options(f, &pkg, !live);
    let (outcome, err) = match weft_interp::run_main(&c, &opts) {
        Ok(o) => (o, None),
        Err(e) => (*e.outcome.clone(), Some(e)),
    };
    if let Some(why) = &outcome.fallback {
        sink.stderr(&fallback_note(why));
    }
    if !live {
        sink.stdout(&outcome.stdout);
        sink.stderr(&outcome.stderr);
    }
    if let Some(e) = err {
        sink.stderr(&runtime_error(&pkg, &e));
        sink.out.code = 1;
    }
    Ok(sink.out)
}

/// `weft test`: checks the program, then runs each test block. Each test
/// writes its output, then one result line.
fn run_tests(f: &Flags, live: bool) -> Result<Output> {
    let mut sink = Sink {
        live,
        out: Output::default(),
    };
    let Some((pkg, c)) = checked_program(f, &mut sink)? else {
        return Ok(sink.out);
    };
    let opts = run_options(f, &pkg, true);
    let (mut passed, mut failed) = (0, 0);
    let path = path_arg(f)?;
    let results = weft_interp::run_tests(&c, &opts);
    if results.is_empty() {
        sink.stderr(&format!("note: {path} has no test blocks\n"));
    }
    if let Some(why) = results.first().and_then(|t| t.outcome.fallback.as_ref()) {
        sink.stderr(&fallback_note(why));
    }
    for t in results {
        sink.stdout(&t.outcome.stdout);
        sink.stderr(&t.outcome.stderr);
        match &t.message {
            None => {
                passed += 1;
                sink.stdout(&format!("test {}: ok\n", t.name));
            }
            Some(m) => {
                failed += 1;
                sink.stdout(&format!("test {}: FAILED: {m}\n", t.name));
            }
        }
    }
    sink.stdout(&format!("{path}: {passed} passed, {failed} failed\n"));
    sink.out.code = u8::from(failed > 0);
    Ok(sink.out)
}
