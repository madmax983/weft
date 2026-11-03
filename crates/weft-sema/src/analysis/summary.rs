//! Summaries (`docs/ir.md` 6.7): what a body does, in the terms of its
//! interface.
//!
//! A [`Summary`] has the parts of `docs/ir.md` 6.7. Each part names places of
//! the interface of the body ([`IPlace`]): the pointee of a parameter, the
//! places that the references behind a parameter point into, a capture, a
//! capability, the frame of the body, a place of a caller, the `rc` group of
//! a type. A run node maps them onto its own places with `σ`
//! (`super::apply`). The relation table `RELS` (`crate::factgen::rels`) says
//! which part carries each relation of the spec.
//!
//! A place of a summary has at most [`SIG_PLACE_STEPS`] steps. A longer place
//! is cut there, and a wildcard step after the cut stands for each place
//! below it ([`IPlace::cut`]). So the parts are finite, and a fixpoint over
//! summaries ends (`docs/ir.md` 6.6).
//!
//! Stage F5 makes summaries from signatures (`super::sig`). Stage F6 makes
//! the summary of a function with a body from its facts (`super::summarize`)
//! in the fixpoint of the call graph (`super::callgraph`). Stage F11 makes
//! the summary of a closure body (`super::summarize::closure`): its parts
//! name the captures (`Capture`, `CaptureHeld`) and the parameters of the
//! closure, and it has the parts `runs` (the captures that hold a function
//! value and that the body calls), `uses`, `moves`, `rebinds` and `puts`
//! (the values that the body stores into a capture or behind a reference).
//! The parts that only a handler or a task gives (`tasks`, `frees`) stay
//! empty; later stages fill them.

use std::collections::BTreeSet;

use weft_facts::Step;
use weft_ir::{AdtId, ClosureId, FnId, TyId};

use crate::factgen::rels::Part;

/// The most steps of a place of a summary (`docs/ir.md` 6.6).
pub const SIG_PLACE_STEPS: usize = 8;

/// The root of a place of an interface (`docs/ir.md` 6.7).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IRoot {
    /// What reference parameter `i` points into, or the places that the
    /// references in by-value parameter `i` point into.
    Param(u32),
    /// The places that the references behind parameter `i` point into.
    Held(u32),
    /// The cell of capture or upvar `k`.
    CaptureCell(u32),
    /// The value of capture or upvar `k`: what a `ByRef` capture points
    /// into, the cell of a `Kept` capture, or the value in the environment
    /// of a `ByMove` capture.
    Capture(u32),
    /// What the references in the value of capture `k` point into.
    CaptureHeld(u32),
    /// What the references behind the references of capture `k` point into.
    CaptureDeep(u32),
    /// A capability: an effect of the row, or a captured capability.
    Cap(u32),
    /// In a handled body: what a `resume` gives to operation `op`.
    OpResult(u32),
    /// In a clause: what `resume` gives back.
    ResumeResult,
    /// A local of the frame of the body that leaves it (the callee frame).
    Frame,
    /// A place of a caller.
    Caller,
    /// The `rc` group of a type definition.
    Group(AdtId),
}

/// One step of a place of an interface.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IStep {
    /// A fixed step, with its text.
    Step(Step, String),
    /// The wildcard step: each place at or below.
    Wild,
    /// A side of a split at the parameter `label`. Each run node gives the
    /// split an id of its own (QA17).
    Seg {
        /// The parameter that names the split point.
        label: u32,
        /// True for `[k..]`.
        hi: bool,
        /// The stability of the element step.
        unstable: bool,
    },
}

/// A place of an interface: a root and its steps.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IPlace {
    /// The root.
    pub root: IRoot,
    /// The steps, at most [`SIG_PLACE_STEPS`] and a wildcard.
    pub steps: Vec<IStep>,
}

impl IPlace {
    /// The place `root` with the steps `steps`, cut at
    /// [`SIG_PLACE_STEPS`] steps: a longer place keeps its first steps and
    /// gets a wildcard step.
    pub fn cut(root: IRoot, mut steps: Vec<IStep>) -> Self {
        if steps.len() > SIG_PLACE_STEPS {
            steps.truncate(SIG_PLACE_STEPS);
            steps.push(IStep::Wild);
        }
        Self { root, steps }
    }

    /// The root itself.
    pub const fn root(root: IRoot) -> Self {
        Self {
            root,
            steps: Vec::new(),
        }
    }

    /// The wildcard place of the root: each place at or below it.
    pub fn wild(root: IRoot) -> Self {
        Self {
            root,
            steps: vec![IStep::Wild],
        }
    }

    /// True if the place starts at the frame of the body.
    pub const fn in_frame(&self) -> bool {
        matches!(self.root, IRoot::Frame)
    }
}

/// The capability interface of an operation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CapIface {
    /// The capability of the effect that a caller gives (the row).
    Row,
    /// A capability of the interface: an effect of the row, or a captured
    /// capability (`IRoot::Cap`).
    Cap(u32),
}

/// An effect that the body performs, and through which capability.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Perform {
    /// The identity of the effect (`crate::effects::identity`).
    pub effect: String,
    /// The capability.
    pub cap: CapIface,
}

/// A way the body can end with an abort (`docs/ir.md` 6.5).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Abort {
    /// An operation of the effect through the capability can abort.
    Perform(Perform),
    /// A failure that the runtime makes (`raises`).
    Raises,
    /// A failed `assert`.
    Assert,
}

/// A function value of the interface that the body runs.
///
/// It is a capture of a closure (stage F11), or a value that a parameter holds (stage F12: the
/// value of the parameter, or a function value inside it or behind it).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Run {
    /// The function parameter (or capture) that the body runs.
    pub param: u32,
    /// True if `param` is a capture of the closure, not a parameter.
    pub capture: bool,
    /// True for a run of a result of a run of the parameter
    /// (`FnVal::ParamResult`): the caller applies the values that the
    /// runs of its values give back.
    pub result: bool,
    /// The body can run it more than once.
    pub many: bool,
    /// The body runs it as a task.
    pub task: bool,
    /// How the body runs it as a task (plan stage F19, OR7).
    pub how: TaskHow,
    /// The interface places that the body gives to the runs (the places of
    /// their arguments): the run node gives each parameter of the value
    /// that runs these places.
    pub args: Vec<IPlace>,
    /// Code of a caller there can resume more than once (the row of the
    /// function type of the value): a value of a caller that the run node
    /// does not know runs with it.
    pub multi: bool,
    /// The body can return with no run of it: a normal path to a `Return`
    /// passes no run node (hole H5 of the review of the ABC preview). A
    /// linear closure that goes there can go away with no run.
    pub maybe: bool,
    /// After a run of it, the body can perform an operation or abort (a
    /// node after a run node has `escapes_at` of an effect other than
    /// `Async`, `performs_at` or `may_abort`; follow-up F19.4, R2-1): a
    /// clause of a handler of a caller can run while a task that the value
    /// starts runs.
    pub then: bool,
}

/// How a body runs a function value of its interface as a task.
///
/// It is in the part `runs` (`docs/ir.md` 6.7, plan stage F19; the
/// `task_runs` part of the old inference). A run node applies the value as
/// a task with these facts (OR7, V126, V127, V132).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TaskHow {
    /// The task is a branch of a `fork`: it runs on another thread
    /// (`fork_task`: W0401, W0403).
    pub thread: bool,
    /// Two tasks of the value can run at the same time (a spawn in a loop,
    /// two spawns): each run of the task conflicts with the other one.
    pub twice: bool,
    /// The function values of the interface (by parameter, or by capture
    /// for a closure body) that the body runs while the task runs.
    pub with: BTreeSet<u32>,
    /// The interface places that the body changes while the task runs.
    pub writes: Vec<IPlace>,
    /// The interface places that the body reads while the task runs.
    pub reads: Vec<IPlace>,
    /// The body is code of a caller with no body (a foreign function): it
    /// runs the value in the worst way.
    pub foreign: bool,
}

/// The places of the tasks that can run while a body waits at an operation
/// of one effect (part `waits`, follow-up F19.5).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Wait {
    /// The interface places that the tasks change.
    pub writes: Vec<IPlace>,
    /// The interface places that the tasks read.
    pub reads: Vec<IPlace>,
}

/// A function value that the result can be (part `ret`, stage F12).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RetFn {
    /// A function item with its type arguments.
    Item(FnId, Vec<TyId>),
    /// A closure that the body (or a callee of it) made: the result holds its
    /// environment.
    Made(ClosureId),
    /// The function values of parameter `i` (a value of the caller).
    Param(u32),
    /// The function values of capture `k` of a closure.
    Capture(u32),
    /// A value that the body does not know.
    Unknown,
}

/// The abstract value of `_0` (`docs/ir.md` 6.7, part `ret`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Ret {
    /// The places that the result points into, with no part of its own.
    pub places: Vec<IPlace>,
    /// The places of a part of a tuple result: the index of the part, its
    /// places, and the `@ uniq` mode of the part.
    pub parts: Vec<(u32, Vec<IPlace>, bool)>,
    /// The result is `@ uniq`.
    pub uniq: bool,
    /// The places that flow from the arguments into a result with no stated
    /// place: a `Param(i)` root names the places that the references in
    /// argument `i` point into. They hold only if the type of the result can
    /// hold a reference. A one-place result (`&T` or `Option<&T>`) gets a
    /// one-place instance of each wildcard place (ADR 0003).
    pub flows: Vec<IPlace>,
    /// The function values that the result can be (stage F12). The places
    /// that their environments point into are in `places`.
    pub fns: Vec<RetFn>,
    /// The result can hold a linear value that its type does not show: a
    /// linear closure in a value of a type with a function part (hole H3 of
    /// the review of the ABC preview).
    pub linear: bool,
    /// The spawn sites of the part `tasks` whose handle the result holds,
    /// and no other value of the body at a `Return` (follow-up F19.3, E-3):
    /// a closure that gives back the handle of a task that it starts. A
    /// `join` of the result can end the task.
    pub tasks: Vec<u32>,
}

/// How a value of an argument flows into the pointee of a reference
/// argument that the body changes (part `stores`, R3RT6).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Flow {
    /// The references behind argument `i` (`Held(i)`, wildcard).
    Held(u32),
    /// A reference into argument `i` (`Param(i)`, wildcard). It goes in only
    /// if the type of the pointee can hold a reference to a part of the
    /// pointee of the argument.
    Into(u32),
    /// The references of the by-value argument `i` as they are. They go in
    /// only if the type of the pointee can hold a reference of their type.
    Value(u32),
}

/// A store of the body: values of other arguments that go behind
/// reference parameter `into` (part `stores`).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Store {
    /// The reference parameter whose pointee gets the values.
    pub into: u32,
    /// What goes there.
    pub flows: Vec<Flow>,
}

/// The parts of a summary (`docs/ir.md` 6.7).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// Places that the body changes, each with the callee root index of the
    /// parameter that it names (`call_mut`).
    pub muts: Vec<(IPlace, u32)>,
    /// Places that the body reads.
    pub reads: Vec<IPlace>,
    /// Places that the body frees.
    pub frees: Vec<IPlace>,
    /// Places that the body gives to code that it does not know.
    pub lends: Vec<IPlace>,
    /// The operations that the body performs.
    pub performs: BTreeSet<Perform>,
    /// The ways the body can abort.
    pub aborts: BTreeSet<Abort>,
    /// The body can resume a `multi` continuation more than once.
    pub multi: bool,
    /// The body can resume more than once with no effect of its row that
    /// says so (a call of an unknown function value): the `multi` part of
    /// the `EffectSig` of today.
    pub unknown_multi: bool,
    /// The function values of the interface that the body runs.
    pub runs: Vec<Run>,
    /// The tasks that the body starts in a scope that it does not own
    /// (stage F18 fills this part).
    pub tasks: Vec<u32>,
    /// The body can start a pinned task (a task that captures a
    /// nonportable value, writes through a reference that is not `@ uniq`,
    /// or runs code that the analysis does not follow), or it calls a
    /// function that can: a task that runs the body is pinned too (part
    /// `pins` of the signature, plan stage F18).
    pub pins: bool,
    /// The task handles of the interface (parameters of a function,
    /// captures of a closure) that the body joins on each path to its
    /// `Return` (a must part; plan stage F18, O3-9): a run node ends their
    /// tasks.
    pub joins: BTreeSet<u32>,
    /// The task handles of the interface that the body joins on each path
    /// where an abort leaves it (a must part; follow-up F19.3, E-1). A call
    /// ends the task of a handle of `joins` at its `Main` node only if the
    /// handle is here too; else at its `Ret` node, because an abort of the
    /// call can leave the task running.
    pub abort_joins: BTreeSet<u32>,
    /// The effects that a task of the body (or of a callee) performs
    /// through a handler of a caller (plan stage F19): a call where a
    /// handler of this task handles such an effect is W0314.
    pub task_effects: BTreeSet<String>,
    /// The tasks that can run while the body waits at an operation that a
    /// handler of a caller handles (follow-up F19.5, issue #50): for each
    /// effect, the interface places that such tasks change and read. The
    /// operation is a perform through the row (also a `fail` and a
    /// timeout), a call of a callee or a run of a value that waits there, or
    /// a run of a value that starts a task before such an operation of the
    /// callee. A key with no places says that a task runs there, but that
    /// it accesses no place of the interface. A call that runs a clause of a
    /// local handler of the effect gives these places to the tasks of the
    /// call that run while the clause runs
    /// (`factgen::templates::wait_tasks`).
    pub waits: std::collections::BTreeMap<String, Wait>,
    /// The value of `_0`.
    pub ret: Ret,
    /// The values that the body writes behind a reference parameter.
    pub stores: Vec<Store>,
    /// The type parameters of the values that the body drops.
    pub drops: BTreeSet<u32>,
    /// The type parameters of the values that the body holds across a node
    /// that can abort or resume more than once.
    pub holds: BTreeSet<u32>,
    /// The type parameters of the values that a `fork` branch of the body
    /// captures (plan stage F20, OL-NR-ptrfork): the branch runs on another
    /// thread, so a nonportable type argument is W0401 at a call.
    pub forks: BTreeSet<u32>,
    /// The captures and upvars that the body uses.
    pub uses: BTreeSet<u32>,
    /// The captures and upvars that the body moves.
    pub moves: BTreeSet<u32>,
    /// The captures and upvars that the body gives a whole new value on each
    /// path to its `Return` (a must part).
    pub rebinds: BTreeSet<u32>,
    /// In the summary of a closure with `rebinds`: the places that the body
    /// changes or lends after it gives a capture its new value (on some
    /// path). A call gives the new values at `Ret`, and these changes there
    /// too, so the new value of a capture sees them.
    pub late_muts: Vec<(IPlace, u32)>,
    /// The references that the body puts into an interface place: for a
    /// closure, a capture, a part of it, or a place behind a reference (the
    /// heap slots of the body at its `Return`); for a function, a place of
    /// an `rc` object, and the environments of the function values that it
    /// puts behind a reference (stage F13; the part `stores` has the other
    /// references of a function). Each entry is the place and the places
    /// that the references there can point into. A place of a local of the
    /// body of a closure is the `Frame` root.
    pub puts: Vec<(IPlace, Vec<IPlace>)>,
    /// The function values that the body puts into an interface place (a
    /// place behind a reference parameter, in an `rc` object, a capture):
    /// the function values of the heap slots of the body at its `Return`
    /// (stage F13). The places that their environments point into are in
    /// `puts`. A run node gives the place of the caller these values.
    pub put_fns: Vec<(IPlace, Vec<RetFn>)>,
    /// The reference parameters that are `@ uniq`.
    pub uniq_needs: BTreeSet<u32>,
    /// Each change of the body is below its first parameter (`writes_via`
    /// at a method call).
    pub only_self: bool,
    /// The interface of each parameter: its name, its callee root index
    /// (`call_arg`), and its stated `in` place (`param_in`).
    pub params: Vec<ParamIface>,
    /// The body can give a place of its own frame (a local of the body or
    /// of a callee) to an operation of a caller, also through a callee
    /// (plan stage F15): a local clause that a call runs can get a
    /// reference into the callee frame (`clause::given`).
    pub gives_frame: bool,
    /// The places of `lends` that code of a caller other than an operation
    /// of the row gets (the inferred part `lends`, follow-up F13.2). A call
    /// that runs a local clause for each effect of the row lends only these
    /// (plan stage F15): it runs the clauses itself.
    pub code_lends: Vec<IPlace>,
}

/// The interface of one parameter.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ParamIface {
    /// The name of the parameter.
    pub name: String,
    /// The callee root index (`crate::body::roots`): a parameter with an
    /// `in` place has the root of the parameter of its place.
    pub root: u32,
    /// The stated `in` place of a reference parameter.
    pub in_place: Option<IPlace>,
}

impl Summary {
    /// True if the result (or a function value that the body runs) can
    /// point into the frame of the body: then the frame root of a run node
    /// ends at its `FrameEnd`.
    pub fn ret_in_frame(&self) -> bool {
        self.runs
            .iter()
            .any(|r| r.args.iter().any(IPlace::in_frame))
            || self
                .puts
                .iter()
                .any(|(_, ps)| ps.iter().any(IPlace::in_frame))
            || self.ret.places.iter().any(IPlace::in_frame)
            || self.ret.flows.iter().any(IPlace::in_frame)
            || self
                .ret
                .parts
                .iter()
                .any(|(_, ps, _)| ps.iter().any(IPlace::in_frame))
    }

    /// True if the body can abort.
    pub fn can_abort(&self) -> bool {
        !self.aborts.is_empty()
    }

    /// True if the part `part` of the relation table `RELS` has content. The
    /// match is exhaustive: each part that `RELS` names has a field here.
    pub fn has(&self, part: Part) -> bool {
        match part {
            Part::Muts => !self.muts.is_empty(),
            Part::Reads => !self.reads.is_empty(),
            Part::Frees => !self.frees.is_empty(),
            Part::Lends => !self.lends.is_empty(),
            Part::Performs => !self.performs.is_empty(),
            Part::Aborts => !self.aborts.is_empty(),
            Part::Multi => self.multi,
            Part::Runs => !self.runs.is_empty(),
            Part::Tasks => !self.tasks.is_empty(),
            Part::Ret => {
                !self.ret.places.is_empty()
                    || !self.ret.parts.is_empty()
                    || !self.ret.flows.is_empty()
                    || !self.ret.fns.is_empty()
            }
            Part::Stores => {
                !self.stores.is_empty() || !self.puts.is_empty() || !self.put_fns.is_empty()
            }
            Part::Drops => !self.drops.is_empty(),
            Part::Holds => !self.holds.is_empty(),
            Part::UsesMoves => !self.uses.is_empty() || !self.moves.is_empty(),
            Part::Rebinds => !self.rebinds.is_empty(),
            Part::UniqNeeds => !self.uniq_needs.is_empty(),
            Part::OnlySelf => self.only_self,
        }
    }
}

/// The summary of each function that a call can run, and of each closure.
///
/// The functions are keyed by the function of the IR, the closures by the
/// closure of a component (`super::summarize::closure`). A function with no
/// summary has the reason (a later stage gives it).
#[derive(Clone, Debug, Default)]
pub struct Summaries {
    /// The summary of each function, or why it has none.
    by_fn: std::collections::HashMap<weft_ir::FnId, Result<Summary, &'static str>>,
    /// The summary of each closure of the component that the fact generator
    /// emits.
    by_closure: std::collections::HashMap<weft_ir::ClosureId, Summary>,
}

impl Summaries {
    /// The summary of function `f`.
    ///
    /// # Errors
    ///
    /// Returns why `f` has no summary yet.
    pub fn get(&self, f: weft_ir::FnId) -> Result<&Summary, &'static str> {
        match self.by_fn.get(&f) {
            Some(Ok(s)) => Ok(s),
            Some(Err(why)) => Err(why),
            None => Err("a call of a function with no summary"),
        }
    }

    /// Gives function `f` the summary `s`, or the reason why it has none.
    pub fn insert(&mut self, f: weft_ir::FnId, s: Result<Summary, &'static str>) {
        self.by_fn.insert(f, s);
    }

    /// The summary of closure `c`.
    ///
    /// # Errors
    ///
    /// Returns why `c` has no summary.
    pub fn closure(&self, c: weft_ir::ClosureId) -> Result<&Summary, &'static str> {
        self.by_closure
            .get(&c)
            .ok_or("a call of a closure with no summary")
    }

    /// Gives closure `c` the summary `s`.
    pub fn insert_closure(&mut self, c: weft_ir::ClosureId, s: Summary) {
        self.by_closure.insert(c, s);
    }

    /// True if a closure has a summary.
    pub fn has_closures(&self) -> bool {
        !self.by_closure.is_empty()
    }
}
