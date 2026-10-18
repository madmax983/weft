//! The `weft` command as a library, so tests can call each command.

pub mod package;

use std::fmt::Write as _;
use std::path::Path;

use anyhow::{bail, Context, Result};
use weft_check::{agreement, bridge, check_analysis, codes, Checked};
use weft_datalog::{evaluate, parse_program_named, EvalOptions};
use weft_interp::{RunOptions, RuntimeError};
use weft_syntax::diag::{Diagnostic, Severity};

use crate::package::{load, package_diags, Package, Profile, SyntaxError};

/// The usage text.
pub const USAGE: &str = "\
usage: weft <command> [options] PATH

commands:
  check   [PROFILE] [--json] [--explain] PATH                    check a file or a package
  run     [PROFILE] [--seed N] [--workers N] [--unchecked] PATH  check, then run `fn main`
  test    [PROFILE] [--seed N] [--workers N] [--unchecked] PATH  check, then run the test blocks
  facts   [PROFILE] PATH [FUNCTION]                              print the facts in Datalog syntax
  agree   [PROFILE] PATH                                         compare the checker with spec/weft.dl
  lint    [PROFILE] --rules RULES.dl PATH                        run user lint rules over the facts
  explain CODE                                                   explain a diagnostic code
  deps    PATH                                                   check dependency authority
  spec                                                           print spec/weft.dl
  help    [COMMAND]                                              print this text

PROFILE is --lib or --bin, and --no-runtime or --runtime. A single file sets
its profile with marker lines: `// weft: library` and `// weft: no-runtime`.
A package sets it in weft.toml. A flag wins over both.

`run` and `test` do not run a program that has errors, unless --unchecked is given.
--seed (default 0) and --workers (1 to 1024, default 4) set the deterministic scheduler.

Exit codes: 0 on success; 1 when the program has errors or fails; 2 on a usage
error or a file that cannot be read. With --unchecked, the exit code of `run`
and `test` shows only the run.
";

/// The most virtual workers of `run` and `test`.
pub const MAX_WORKERS: usize = 1024;

/// The stack of the thread that runs a command.
///
/// Sema and the interpreter walk the syntax tree with recursion. The parser
/// limits the depth of the tree, and `tests/limits.rs` shows that a 2 MiB
/// stack is sufficient for the deepest tree that it accepts. The large stack
/// is a margin: each caller of [`run`] and [`run_live`] gets it, also a test
/// thread. The system only reserves this memory. It uses a page when the
/// recursion gets to it.
pub const STACK: usize = 256 * 1024 * 1024;

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
    rules: Option<String>,
    seed: Option<u64>,
    workers: Option<usize>,
    positional: Vec<String>,
    /// The options as given, for the check that the command takes them.
    given: Vec<String>,
}

/// The profile options.
const PROFILE: [&str; 4] = ["--lib", "--bin", "--no-runtime", "--runtime"];

/// Returns the options that a command takes, or `None` for an unknown command.
fn options_of(cmd: &str) -> Option<Vec<&'static str>> {
    let own: &[&str] = match cmd {
        "check" => &["--json", "--explain"],
        "run" | "test" => &["--seed", "--workers", "--unchecked"],
        "lint" => &["--rules"],
        "facts" | "agree" => &[],
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
        "facts" => (&["PATH"], &["FUNCTION"]),
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
            "--rules" => f.rules = Some(it.next().context("--rules needs a file")?.clone()),
            "--seed" => f.seed = Some(number(&mut it, "--seed")?),
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

/// Runs one command on a thread with a [`STACK`] stack. The output of a Weft
/// program stays in [`Output`].
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

/// Runs one command on a thread with a [`STACK`] stack. If the system cannot
/// give the stack, the command runs on the current thread. A panic of the
/// command continues in the caller.
fn on_large_stack(args: &[String], live: bool) -> Result<Output> {
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("weft".into())
            .stack_size(STACK)
            .spawn_scoped(scope, || run_with(args, live));
        match worker {
            Ok(handle) => handle
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic)),
            Err(_) => run_with(args, live),
        }
    })
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
    let pkg = load(path)?;
    let opts = pkg.options(profile);
    let analysis = weft_sema::analyze(&pkg.units, opts);
    let mut checked = check_analysis(analysis, &pkg.files, opts);
    checked.diags.extend(package_diags(&pkg, &checked.analysis));
    checked.diags.extend(pkg.marker_diags());
    checked
        .diags
        .sort_by(|a, b| (a.unit, a.span.lo, &a.code).cmp(&(b.unit, b.span.lo, &b.code)));
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
    diag_json_in(pkg.files.get(d.unit), d)
}

/// Writes one diagnostic in `file` as a JSON object.
fn diag_json_in(file: Option<&weft_syntax::SourceFile>, d: &Diagnostic) -> String {
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
    let (pkg, c) = check_path(path, f.profile)?;
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
    let (_, c) = check_path(path, f.profile)?;
    let mut text = String::new();
    for b in &c.analysis.bodies {
        if only.is_some_and(|o| *o != b.facts.name) {
            continue;
        }
        text.push_str(&bridge::facts_text(&b.facts));
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
                "error: no function or test `{name}` in {}; {bodies}\n",
                path.display()
            ),
            code: 1,
            ..Output::default()
        });
    }
    Ok(Output {
        text,
        ..Output::default()
    })
}

fn agree(f: &Flags) -> Result<Output> {
    let path = Path::new(path_arg(f)?);
    let (_, c) = check_path(path, f.profile)?;
    match agreement(&c) {
        Ok(n) => Ok(Output {
            text: format!("agree: the checker and spec/weft.dl agree on {n} bodies\n"),
            ..Output::default()
        }),
        Err(bad) => {
            let mut text = String::new();
            for b in bad {
                let _ = match &b.spec {
                    Ok(spec) => writeln!(
                        text,
                        "disagree in `{}`\n  checker: {:?}\n  spec:    {spec:?}",
                        b.function, b.checker
                    ),
                    Err(e) => writeln!(text, "disagree in `{}`: {e}", b.function),
                };
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
    let path = Path::new(path_arg(f)?);
    let (pkg, c) = check_path(path, f.profile)?;
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
    let (pkg, c) = check_path(path, f.profile)?;
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
