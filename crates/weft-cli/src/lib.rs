//! The `weft` command as a library, so tests can call each command.

pub mod package;

use std::fmt::Write as _;
use std::path::Path;

use anyhow::{bail, Context, Result};
use weft_check::{agreement, bridge, check_analysis, codes, Checked};
use weft_datalog::{evaluate, parse_program_named, EvalOptions};
use weft_interp::{RunOptions, RuntimeError};
use weft_syntax::diag::{Diagnostic, Severity};

use crate::package::{load, package_diags, Package};

/// The usage text.
pub const USAGE: &str = "\
usage: weft <command> [options] PATH

commands:
  check   [--lib] [--no-runtime] [--json] [--explain] PATH   check a file or a package
  run     [--seed N] [--workers N] [--unchecked] PATH        check, then run `fn main`
  test    [--seed N] [--workers N] [--unchecked] PATH        check, then run the test blocks
  facts   PATH [FUNCTION]                                    print the facts in Datalog syntax
  agree   PATH                                               compare the checker with spec/weft.dl
  lint    --rules RULES.dl PATH                              run user lint rules over the facts
  explain CODE                                               explain a diagnostic code
  deps    PATH                                               check dependency authority
  spec                                                       print spec/weft.dl
  help                                                       print this text

`run` and `test` do not run a program that has errors, unless --unchecked is given.
--seed (default 0) and --workers (default 4) set the deterministic scheduler.
`run` and `test` also take --lib and --no-runtime.

A single file sets its options with marker lines: `// weft: library` and
`// weft: no-runtime`. A package sets them in weft.toml. A flag adds to them.

Exit codes: 0 on success, 1 when the program has errors or fails, 2 on a usage error.
";

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
    lib: bool,
    no_runtime: bool,
    json: bool,
    explain: bool,
    unchecked: bool,
    rules: Option<String>,
    seed: Option<u64>,
    workers: Option<usize>,
    positional: Vec<String>,
}

impl Flags {
    const fn options(&self) -> weft_sema::Options {
        weft_sema::Options {
            library: self.lib,
            no_runtime: self.no_runtime,
        }
    }
}

/// Reads the number after an option.
fn number<T: std::str::FromStr>(it: &mut std::slice::Iter<'_, String>, opt: &str) -> Result<T> {
    let v = it.next().with_context(|| format!("{opt} needs a number"))?;
    v.parse()
        .ok()
        .with_context(|| format!("{opt} needs a number, found `{v}`"))
}

fn flags(args: &[String]) -> Result<Flags> {
    let mut f = Flags::default();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--lib" => f.lib = true,
            "--no-runtime" => f.no_runtime = true,
            "--json" => f.json = true,
            "--explain" => f.explain = true,
            "--unchecked" => f.unchecked = true,
            "--rules" => f.rules = Some(it.next().context("--rules needs a file")?.clone()),
            "--seed" => f.seed = Some(number(&mut it, "--seed")?),
            "--workers" => {
                let n: usize = number(&mut it, "--workers")?;
                if n == 0 {
                    bail!("--workers needs at least 1");
                }
                f.workers = Some(n);
            }
            s if s.starts_with("--") => bail!("unknown option `{s}`"),
            s => f.positional.push(s.to_string()),
        }
    }
    Ok(f)
}

/// Runs one command. The output of a Weft program stays in [`Output`].
pub fn run(args: &[String]) -> Result<Output> {
    run_with(args, false)
}

/// Runs one command. `weft run` writes the output of the Weft program to the
/// process standard output and standard error while the program runs.
pub fn run_live(args: &[String]) -> Result<Output> {
    run_with(args, true)
}

fn run_with(args: &[String], live: bool) -> Result<Output> {
    let Some((cmd, rest)) = args.split_first() else {
        return Ok(Output {
            text: USAGE.into(),
            code: 2,
            ..Output::default()
        });
    };
    let f = flags(rest)?;
    match cmd.as_str() {
        "check" => check(&f),
        "run" => run_main(&f, live),
        "test" => run_tests(&f),
        "facts" => facts(&f),
        "agree" => agree(&f),
        "lint" => lint(&f),
        "explain" => explain(&f),
        "deps" => deps(&f),
        "spec" => Ok(Output {
            text: bridge::SPEC_SRC.into(),
            ..Output::default()
        }),
        "help" | "--help" | "-h" => Ok(Output {
            text: USAGE.into(),
            ..Output::default()
        }),
        other => bail!("unknown command `{other}`\n{USAGE}"),
    }
}

fn path_arg(f: &Flags) -> Result<&str> {
    f.positional
        .first()
        .map(String::as_str)
        .context("missing PATH")
}

/// Loads, analyzes and checks a file or a package. The flags add to the
/// options of the manifest or of the file markers.
pub fn check_path(path: &Path, lib: bool, no_runtime: bool) -> Result<(Package, Checked)> {
    let pkg = load(path)?;
    let opts = pkg.options(weft_sema::Options {
        library: lib,
        no_runtime,
    });
    let analysis = weft_sema::analyze(&pkg.units, opts);
    let mut checked = check_analysis(analysis, &pkg.files, opts);
    checked.diags.extend(package_diags(&pkg, &checked.analysis));
    checked
        .diags
        .sort_by_key(|d| (d.unit, d.span.lo, d.code.clone()));
    Ok((pkg, checked))
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
    let file = pkg.files.get(d.unit);
    let (line, col) = file.map_or((0, 0), |f| f.line_col(d.span.lo));
    let name = file.map_or_else(String::new, |f| f.name.clone());
    let notes: Vec<String> = d.notes.iter().map(|n| json_escape(&n.text)).collect();
    let sev = if d.severity == Severity::Error {
        "error"
    } else {
        "warning"
    };
    format!(
        "{{\"code\":{},\"severity\":\"{sev}\",\"message\":{},\"file\":{},\"line\":{line},\"column\":{col},\"notes\":[{}]}}",
        json_escape(&d.code),
        json_escape(&d.message),
        json_escape(&name),
        notes.join(",")
    )
}

fn check(f: &Flags) -> Result<Output> {
    let path = Path::new(path_arg(f)?);
    let (pkg, c) = check_path(path, f.lib, f.no_runtime)?;
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
        for b in &c.analysis.bodies {
            let Some(file) = pkg.files.get(b.unit) else {
                continue;
            };
            let line_of = |o: u32| file.line_col(o).0;
            let ex = bridge::explain(&b.facts, &line_of).map_err(|e| anyhow::anyhow!("{e}"))?;
            for e in ex {
                if f.json {
                    let _ = writeln!(
                        text,
                        "{{\"derivation\":{},\"function\":{}}}",
                        e.json,
                        json_escape(&b.facts.name)
                    );
                } else {
                    let _ = write!(
                        text,
                        "derivation of {} in `{}`:\n{}",
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
        code: u8::from(!c.ok()),
        ..Output::default()
    })
}

fn facts(f: &Flags) -> Result<Output> {
    let path = Path::new(path_arg(f)?);
    let only = f.positional.get(1);
    let (_, c) = check_path(path, f.lib, f.no_runtime)?;
    let mut text = String::new();
    for b in &c.analysis.bodies {
        if only.is_some_and(|o| *o != b.facts.name) {
            continue;
        }
        text.push_str(&bridge::facts_text(&b.facts));
    }
    Ok(Output {
        text,
        ..Output::default()
    })
}

fn agree(f: &Flags) -> Result<Output> {
    let path = Path::new(path_arg(f)?);
    let (_, c) = check_path(path, f.lib, f.no_runtime)?;
    match agreement(&c) {
        Ok(n) => Ok(Output {
            text: format!("agree: the checker and spec/weft.dl agree on {n} bodies\n"),
            ..Output::default()
        }),
        Err(bad) => {
            let mut text = String::new();
            for b in bad {
                let _ = writeln!(
                    text,
                    "disagree in `{}`\n  checker: {:?}\n  spec:    {:?}",
                    b.function, b.checker, b.spec
                );
            }
            Ok(Output {
                text,
                code: 1,
                ..Output::default()
            })
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
    let mut program = bridge::spec().clone();
    program.extend(user);
    let path = Path::new(path_arg(f)?);
    let (pkg, c) = check_path(path, f.lib, f.no_runtime)?;
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
            let name = out.display_value(t[0]).trim_matches('"').to_string();
            let node = t.get(1).map(|v| out.display_value(*v)).unwrap_or_default();
            let span = node
                .strip_prefix('n')
                .and_then(|n| n.parse::<usize>().ok())
                .and_then(|n| b.facts.nodes.get(n))
                .map(|n| n.span)
                .unwrap_or_default();
            let mut d = Diagnostic::warning(
                "L0001",
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
    let (pkg, c) = check_path(path, false, false)?;
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
    let (pkg, c) = check_path(path, f.lib, f.no_runtime)?;
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
        no_runtime: pkg.options(f.options()).no_runtime,
        ..defaults
    }
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

/// `weft test`: checks the program, then runs each test block. Each test prints
/// its output, then one result line.
fn run_tests(f: &Flags) -> Result<Output> {
    let mut sink = Sink {
        live: false,
        out: Output::default(),
    };
    let Some((pkg, c)) = checked_program(f, &mut sink)? else {
        return Ok(sink.out);
    };
    let opts = run_options(f, &pkg, true);
    let (mut passed, mut failed) = (0, 0);
    for t in weft_interp::run_tests(&c, &opts) {
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
    sink.stdout(&format!(
        "{}: {passed} passed, {failed} failed\n",
        path_arg(f)?
    ));
    sink.out.code = u8::from(failed > 0);
    Ok(sink.out)
}
