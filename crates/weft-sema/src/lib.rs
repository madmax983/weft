//! Semantic analysis for Weft: names, types, places, modes and effects.
//!
//! [`analyze`] collects items, resolves signatures, infers the effects of
//! functions that do not state them, and lowers every body to [`FnFacts`].
//! The checker in `weft-check` runs the rules on these facts.

pub mod body;
pub mod effects;
pub mod fip;
pub mod ids;
pub mod infer;
pub mod irbuild;
pub mod program;
pub mod props;
pub mod thir;
pub mod types;

use weft_facts::FnFacts;
use weft_syntax::diag::Code;
use weft_syntax::diag::Diagnostic;
use weft_syntax::{parse_file, ParseError};

pub use ids::{AdtId, EffectId, FnId, ModId};
pub use program::{FnSig, Program, TaskRun, Unit};
pub use weft_syntax::diag::{PRELUDE_UNIT, ROOT_UNIT};

/// The source of the standard prelude.
pub const PRELUDE_SRC: &str = include_str!("../../../std/prelude.wf");

/// Analysis options.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Options {
    /// The root unit is a library: it may not install root handlers.
    pub library: bool,
    /// The embedded profile: no `std.rt`, so `main` must handle every standard effect.
    pub no_runtime: bool,
}

/// The words of file markers.
pub const MARKERS: [&str; 2] = ["library", "no-runtime"];

/// Returns each word of the file markers of a source text, with its byte
/// offset. A marker is a line comment `// weft: WORD ...`. Spaces and commas
/// separate the words.
pub fn marker_words(src: &str) -> Vec<(usize, &str)> {
    let mut out = Vec::new();
    let mut start = 0;
    for line in src.split_inclusive('\n') {
        let indent = line.len() - line.trim_start().len();
        if let Some(words) = line.trim_start().strip_prefix("// weft:") {
            let mut at = start + indent + "// weft:".len();
            for w in words.split_inclusive([' ', ',', '\t', '\r', '\n']) {
                let word = w.trim_end_matches([' ', ',', '\t', '\r', '\n']);
                if !word.is_empty() {
                    out.push((at, word));
                }
                at += w.len();
            }
        }
        start += line.len();
    }
    out
}

impl Options {
    /// Reads the file markers of a source text (see [`marker_words`]). The
    /// words are [`MARKERS`]. Other words have no effect.
    pub fn from_markers(src: &str) -> Self {
        let mut o = Self::default();
        for (_, w) in marker_words(src) {
            match w {
                "library" => o.library = true,
                "no-runtime" => o.no_runtime = true,
                _ => {}
            }
        }
        o
    }
}

/// Counts of the work of an analysis. A test can put a limit on them, as a
/// clock cannot be stable on a loaded machine.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    /// The passes of the loop bodies, also of nested loops.
    pub loop_passes: usize,
    /// The values that the loop heads copied and the rewinds put back: the
    /// state at each head, and the locals that each pass changed.
    pub loop_copies: usize,
    /// The links between type variables that the type inference followed.
    pub type_steps: usize,
    /// The part holders that the lowering looked at: a use of a local and a new
    /// value of a part look at the holders.
    pub holder_steps: usize,
    /// The steps of the item checks ([`program::Program::item_steps`]).
    pub item_steps: usize,
    /// The full types whose place fields the lowering walked: each one once
    /// for a body (review round 3, Q3-4).
    pub place_types: usize,
}

impl Work {
    /// Adds the counts of `o`.
    pub const fn add(&mut self, o: Self) {
        self.loop_passes += o.loop_passes;
        self.loop_copies += o.loop_copies;
        self.type_steps += o.type_steps;
        self.holder_steps += o.holder_steps;
        self.item_steps += o.item_steps;
        self.place_types += o.place_types;
    }
}

/// The facts of one body.
#[derive(Clone, Debug)]
pub struct BodyFacts {
    /// The function, or `None` for a test.
    pub func: Option<program::FnId>,
    /// The unit index of the body.
    pub unit: usize,
    /// The facts.
    pub facts: FnFacts,
    /// The effects that the body infers, also for a function that states its
    /// effects. They include the closures that the body makes.
    pub effects: program::EffectSig,
}

/// The result of analysis.
#[derive(Clone, Debug)]
pub struct Analysis {
    /// The program.
    pub program: Program,
    /// The final signatures, with inferred effects.
    pub sigs: Vec<FnSig>,
    /// The facts of every user body.
    pub bodies: Vec<BodyFacts>,
    /// Diagnostics from analysis (not from the checker).
    pub diags: Vec<Diagnostic>,
    /// The number of body lowerings that effect inference used.
    pub lowerings: usize,
    /// The work of the last lowering of each body.
    pub work: Work,
    /// The THIR tables of each body, in the order of [`Analysis::bodies`]
    /// (`docs/ir.md` 2.1). The last lowering of each body records them.
    pub thir: Vec<thir::Tables>,
    /// The final types of the THIR tables, with the declarations of the
    /// program (`types::ir_ty_table`).
    pub thir_tys: weft_ir::TyTable,
    /// Why the declarations of the program have no final types. The type
    /// table then has no declarations.
    pub thir_decl_error: Option<types::IrTyError>,
}

/// Parses the prelude.
///
/// # Errors
///
/// Returns the parse error if `std/prelude.wf` does not parse. The tests
/// make sure that it parses.
pub fn prelude_unit() -> Result<Unit, ParseError> {
    Ok(Unit {
        name: "prelude".into(),
        file: parse_file(PRELUDE_SRC)?,
        is_std: true,
    })
}

/// Returns the unit index of a module: [`PRELUDE_UNIT`], [`ROOT_UNIT`], then
/// the dependencies.
fn unit_of(prog: &Program, m: program::ModId) -> usize {
    prog.mods[m].unit
}

/// The stack of the thread that runs analysis, the checker and the
/// interpreter ([`on_large_stack`]).
///
/// Sema, the checker and the interpreter walk the syntax tree with recursion.
/// The parser limits the depth of the tree, and `crates/weft-cli/tests/limits.rs`
/// shows that a 2 MiB stack is sufficient for the deepest tree that it accepts:
/// it runs each stage there with [`on_current_stack`]. The large stack is a
/// margin. The system only reserves this memory. It uses a page when the
/// recursion gets to it.
pub const STACK: usize = 256 * 1024 * 1024;

std::thread_local! {
    /// True on a thread that [`on_large_stack`] started.
    static LARGE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Runs `f` on a new thread with a [`STACK`] stack, and returns its result.
///
/// So a caller on a small stack can analyze, check and run the deepest
/// program that the parser accepts. On a thread that this function started,
/// `f` runs at once, with no new thread. If the system cannot start the
/// thread, `f` runs on the current thread. A panic of `f` continues in the
/// caller.
pub fn on_large_stack<T: Send>(f: impl Fn() -> T + Sync) -> T {
    if LARGE.with(std::cell::Cell::get) {
        return f();
    }
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("weft".into())
            .stack_size(STACK)
            .spawn_scoped(scope, || {
                LARGE.with(|l| l.set(true));
                f()
            });
        match worker {
            Ok(handle) => handle
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic)),
            Err(_) => f(),
        }
    })
}

/// Runs `f` and each call of [`on_large_stack`] in it on the current thread.
///
/// It is the path of [`on_large_stack`] when the system cannot start a
/// thread. A caller that has a large stack can use it, and a test uses it to
/// show that a small stack is sufficient ([`STACK`]).
pub fn on_current_stack<T>(f: impl FnOnce() -> T) -> T {
    /// Puts the mark of the thread back, also when `f` panics.
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            LARGE.with(|l| l.set(self.0));
        }
    }
    let _restore = Restore(LARGE.with(|l| l.replace(true)));
    f()
}

/// Analyzes the units. Unit [`PRELUDE_UNIT`] must be the prelude and unit
/// [`ROOT_UNIT`] the root. The analysis runs on a large stack
/// ([`on_large_stack`]).
///
/// Effect inference ([`infer`]) gives a row to each function that does not
/// state its effects. Each function, also one that states its effects, also
/// gets the parts of its signature that its body always infers
/// ([`infer::PARTS`]), for example what it lends to its function parameters
/// and what its returned function value does. If these other parts of a function still
/// change after [`infer::parts_limit`] changes, the function gets W0704. If a
/// row grows past the height of its lattice, the inference has a bug: it
/// stops, and each function whose signature can still change gets W0706.
pub fn analyze(units: &[Unit], opts: Options) -> Analysis {
    on_large_stack(|| analyze_bounded(units, opts, None, None))
}

/// Analyzes the units. The row of a function may grow at most `limit` times.
#[cfg(test)]
pub(crate) fn analyze_with_limit(units: &[Unit], opts: Options, limit: usize) -> Analysis {
    analyze_bounded(units, opts, Some(limit), None)
}

/// Analyzes the units. The lowering of a loop may take at most `passes` passes.
#[cfg(test)]
pub(crate) fn analyze_with_loop_bound(units: &[Unit], opts: Options, passes: usize) -> Analysis {
    analyze_bounded(units, opts, None, Some(passes))
}

fn analyze_bounded(
    units: &[Unit],
    opts: Options,
    limit: Option<usize>,
    loop_bound: Option<usize>,
) -> Analysis {
    let (prog, mut diags) = program::Collector::collect(units);
    let mut sigs: Vec<FnSig> = prog.fns.iter().map(|f| f.sig.clone()).collect();
    let user_fns: Vec<FnId> = prog
        .fn_ids()
        .filter(|&i| !prog.fns[i].is_std && prog.fns[i].decl.body.is_some())
        .collect();
    let library_of =
        |prog: &Program, f: FnId| opts.library || unit_of(prog, prog.fns[f].module) > ROOT_UNIT;
    let lower = |sigs: &[FnSig], f: FnId| {
        let lib = library_of(&prog, f);
        body::Lower::new(&prog, sigs, prog.fns[f].module, &prog.fns[f].path, lib)
            .with_loop_bound(loop_bound)
            .lower_fn(f)
    };
    let inferred = infer::infer(&prog, &mut sigs, &user_fns, limit, &lower);
    diags.extend(inferred.diags);
    diags.extend(program::check_on_abort_rows(&prog, &sigs, opts.no_runtime));
    let mut bodies = Vec::new();
    let mut work = Work::default();
    let (mut thir_tys, thir_decl_error) = match types::ir_ty_table(&prog) {
        Ok(t) => (t, None),
        Err(e) => (weft_ir::TyTable::new(), Some(e)),
    };
    let mut thir = Vec::new();
    // The runtime starts `main` and the tests of the root (`started()`). With
    // no runtime, `main` handles every effect itself (`no_runtime()`).
    let main = match prog.lookup(prog.root, "main") {
        Some(program::ItemRef::Fn(m)) => Some(m),
        _ => None,
    };
    for (&f, mut l) in user_fns.iter().zip(inferred.lowered) {
        diags.extend(l.diags);
        work.add(l.work);
        thir.push(thir::record::build(
            &prog,
            &mut thir_tys,
            *l.thir,
            &l.facts.vars,
        ));
        let unit = unit_of(&prog, prog.fns[f].module);
        l.facts.started = unit == ROOT_UNIT && main == Some(f);
        l.facts.no_runtime = l.facts.started && opts.no_runtime;
        bodies.push(BodyFacts {
            func: Some(f),
            unit,
            facts: l.facts,
            effects: l.effects,
        });
    }
    for t in &prog.tests {
        let name = format!("test \"{}\"", t.name);
        let lib = opts.library || unit_of(&prog, t.module) > ROOT_UNIT;
        let mut l = body::Lower::new(&prog, &sigs, t.module, &name, lib)
            .with_loop_bound(loop_bound)
            .lower_test(&t.body, t.span);
        diags.extend(l.diags);
        work.add(l.work);
        thir.push(thir::record::build(
            &prog,
            &mut thir_tys,
            *l.thir,
            &l.facts.vars,
        ));
        l.facts.started = unit_of(&prog, t.module) == ROOT_UNIT;
        bodies.push(BodyFacts {
            func: None,
            unit: unit_of(&prog, t.module),
            facts: l.facts,
            effects: l.effects,
        });
    }
    for &f in &user_fns {
        if prog.fns[f].decl.is_fip {
            let unit = unit_of(&prog, prog.fns[f].module);
            diags.extend(fip::check(&prog, &sigs, f).into_iter().map(|mut d| {
                d.unit = unit;
                d
            }));
        }
    }
    work.item_steps = prog.item_steps();
    Analysis {
        program: prog,
        sigs,
        bodies,
        diags,
        lowerings: inferred.lowerings,
        work,
        thir,
        thir_tys,
        thir_decl_error,
    }
}

/// Parses and analyzes one source text as the root unit, on a large stack
/// ([`on_large_stack`]).
///
/// # Errors
///
/// Returns W0001 if the source or the prelude does not parse.
pub fn analyze_source(src: &str, opts: Options) -> Result<Analysis, Diagnostic> {
    on_large_stack(|| parse_and_analyze(src, opts))
}

fn parse_and_analyze(src: &str, opts: Options) -> Result<Analysis, Diagnostic> {
    let prelude = prelude_unit().map_err(|e| {
        let mut d = Diagnostic::error(
            Code::W0001,
            format!("std/prelude.wf does not parse: {}", e.message),
            e.span,
        );
        d.unit = PRELUDE_UNIT;
        d
    })?;
    let file = parse_file(src).map_err(|e| {
        let mut d = Diagnostic::error(Code::W0001, e.message, e.span);
        d.unit = ROOT_UNIT;
        d
    })?;
    let units = vec![
        prelude,
        Unit {
            name: String::new(),
            file,
            is_std: false,
        },
    ];
    Ok(analyze(&units, opts))
}

#[cfg(test)]
mod tests;
