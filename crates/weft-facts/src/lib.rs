//! The fact tables that the rules query.
//!
//! Semantic analysis writes one [`FnFacts`] per function. The Datalog engine runs
//! `spec/weft.dl` over these facts. The production checker reads the same facts.
//! Both produce a [`Violations`] value, and the two values must be equal.
//!
//! A function body, each closure body and each handler clause is one connected
//! component of the control-flow graph. All components share the place and
//! variable tables.

use std::collections::{BTreeSet, HashMap};
use std::fmt;

pub use weft_syntax::ast::Span;
pub use weft_verified::places::{Step, StepKind};

macro_rules! id_type {
    ($(#[$doc:meta])* $name:ident, $prefix:literal) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);

        impl $name {
            /// Returns the index into the owning table.
            pub const fn index(self) -> usize {
                self.0 as usize
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!($prefix, "{}"), self.0)
            }
        }
    };
}

id_type!(
    /// A node of the control-flow graph.
    NodeId,
    "n"
);
id_type!(
    /// A variable: a local, a parameter, a temporary or a hidden value.
    VarId,
    "v"
);
id_type!(
    /// An interned place.
    PlaceId,
    "p"
);
id_type!(
    /// A place root.
    RootId,
    "r"
);
id_type!(
    /// A capability that a local handler creates.
    CapId,
    "c"
);
id_type!(
    /// A spawned task or a fork branch.
    TaskId,
    "t"
);
id_type!(
    /// A `handle` expression.
    HandlerId,
    "h"
);

/// What a place root is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RootKind {
    /// The referent of a reference parameter. Mutations need a declaration.
    Param,
    /// An owned local or an owned parameter. Mutations are local.
    Local,
    /// The group of an `rc` type. Mutations need a declaration.
    Group,
}

/// A place root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Root {
    /// The name, as shown in diagnostics.
    pub name: String,
    /// The kind.
    pub kind: RootKind,
}

/// An interned place: a root plus steps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlaceInfo {
    /// The root.
    pub root: RootId,
    /// The place without its last step. `None` for a root place.
    pub parent: Option<PlaceId>,
    /// All steps from the root.
    pub steps: Vec<Step>,
    /// The text form, for example `world.entities[]`.
    pub display: String,
}

/// What a variable is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VarKind {
    /// A named local.
    Local,
    /// A parameter.
    Param,
    /// A temporary value inside an expression.
    Temp,
    /// The hidden iterator of a `for` loop.
    Iterator,
    /// A closure value.
    Closure,
    /// A captured continuation (`resume`).
    Continuation,
    /// A task handle.
    Task,
}

/// A variable and its static properties.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VarInfo {
    /// The name, as shown in diagnostics.
    pub name: String,
    /// The kind.
    pub kind: VarKind,
    /// The declaration.
    pub span: Span,
    /// The type, as shown in diagnostics.
    pub ty: String,
    /// The value is linear.
    pub linear: bool,
    /// The type declares `on abort`.
    pub has_on_abort: bool,
    /// The value is not `many`.
    pub once: bool,
    /// The type is `!Move`.
    pub immovable: bool,
    /// The value is `@ uniq`.
    pub uniq: bool,
    /// The value cannot cross threads.
    pub nonportable: bool,
}

impl VarInfo {
    /// Makes a plain `many`, portable, aliased variable.
    pub fn plain(
        name: impl Into<String>,
        kind: VarKind,
        span: Span,
        ty: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            kind,
            span,
            ty: ty.into(),
            linear: false,
            has_on_abort: false,
            once: false,
            immovable: false,
            uniq: false,
            nonportable: false,
        }
    }
}

/// A node and what it does, for diagnostics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodeInfo {
    /// The source location.
    pub span: Span,
    /// A short label, such as the callee name `push`.
    pub label: String,
    /// More text, such as the effect `mut(world.entities)`.
    pub detail: String,
}

/// The kind of task.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TaskKind {
    /// A branch of `fork`: it runs on another thread.
    Fork,
    /// A task from `s.spawn`.
    Spawn,
}

/// A task and its source location.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaskInfo {
    /// The kind.
    pub kind: TaskKind,
    /// The closure that the task runs.
    pub span: Span,
}

/// A `handle` expression, for the root-handler rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandlerInfo {
    /// The handled effect.
    pub effect: String,
    /// The effect is a standard effect.
    pub is_std: bool,
    /// The enclosing function can still perform the effect, so the handler intercepts.
    pub forwards: bool,
    /// The source location.
    pub span: Span,
}

/// All facts of one function.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FnFacts {
    /// The function name.
    pub name: String,
    /// The place roots.
    pub roots: Vec<Root>,
    /// The places. A parent comes before its children.
    pub places: Vec<PlaceInfo>,
    /// The variables.
    pub vars: Vec<VarInfo>,
    /// The nodes.
    pub nodes: Vec<NodeInfo>,
    /// The tasks.
    pub tasks: Vec<TaskInfo>,
    /// The `handle` expressions.
    pub handlers: Vec<HandlerInfo>,
    /// The number of local capabilities.
    pub caps: u32,

    /// `cfg_edge(P, Q)`.
    pub cfg_edge: Vec<(NodeId, NodeId)>,
    /// `points_into(R, Path)`.
    pub points_into: Vec<(VarId, PlaceId)>,
    /// `mutates_at(P, M)`.
    pub mutates_at: Vec<(NodeId, PlaceId)>,
    /// `reads_at(P, A)`.
    pub reads_at: Vec<(NodeId, PlaceId)>,
    /// `performs_at(P, Cap)`.
    pub performs_at: Vec<(NodeId, CapId)>,
    /// `footprint(Cap, M)`.
    pub footprint: Vec<(CapId, PlaceId)>,
    /// `rebound_at(V, P)`.
    pub rebound_at: Vec<(VarId, NodeId)>,
    /// `uses(V, P)`.
    pub uses: Vec<(VarId, NodeId)>,
    /// `moved_at(V, P)`.
    pub moved_at: Vec<(VarId, NodeId)>,
    /// `scope_end(V, P)`.
    pub scope_end: Vec<(VarId, NodeId)>,
    /// `may_abort(P)`.
    pub may_abort: Vec<NodeId>,
    /// `multi_at(P)`.
    pub multi_at: Vec<NodeId>,

    /// `has_signature()`.
    pub has_signature: bool,
    /// `declared_mut(D)`.
    pub declared_mut: Vec<PlaceId>,
    /// `declared_effect(E)`, closed under implication.
    pub declared_effect: Vec<String>,
    /// `escapes_at(P, E)`.
    pub escapes_at: Vec<(NodeId, String)>,
    /// `shared_root(S)`.
    pub shared_root: Vec<PlaceId>,

    /// `spawned_at(T, P)`.
    pub spawned_at: Vec<(TaskId, NodeId)>,
    /// `joined_at(T, P)`.
    pub joined_at: Vec<(TaskId, NodeId)>,
    /// `task_reads(T, A)`.
    pub task_reads: Vec<(TaskId, PlaceId)>,
    /// `task_writes(T, M)`.
    pub task_writes: Vec<(TaskId, PlaceId)>,
    /// `captures(T, V)`.
    pub captures: Vec<(TaskId, VarId)>,
    /// `mut_through(T, V)`.
    pub mut_through: Vec<(TaskId, VarId)>,

    /// `call_mut(P, M, I)`.
    pub call_mut: Vec<(NodeId, PlaceId, u32)>,
    /// `call_arg(P, A, I)`.
    pub call_arg: Vec<(NodeId, PlaceId, u32)>,

    /// `library()`.
    pub library: bool,

    /// The interning index of places: parent and step to child. `add_root` and
    /// `child` keep it current.
    pub place_index: HashMap<(PlaceId, Step), PlaceId>,
}

impl FnFacts {
    /// Returns the place record.
    pub fn place(&self, p: PlaceId) -> &PlaceInfo {
        &self.places[p.index()]
    }

    /// Returns the variable record.
    pub fn var(&self, v: VarId) -> &VarInfo {
        &self.vars[v.index()]
    }

    /// Returns the node record.
    pub fn node(&self, n: NodeId) -> &NodeInfo {
        &self.nodes[n.index()]
    }

    /// Returns true if the root of `p` needs a declaration to mutate.
    pub fn param_rooted(&self, p: PlaceId) -> bool {
        matches!(
            self.roots[self.place(p).root.index()].kind,
            RootKind::Param | RootKind::Group
        )
    }

    /// Adds a root and its root place. Returns the root place.
    pub fn add_root(&mut self, name: impl Into<String>, kind: RootKind) -> PlaceId {
        let name = name.into();
        let root = RootId(u32::try_from(self.roots.len()).unwrap_or(u32::MAX));
        self.roots.push(Root {
            name: name.clone(),
            kind,
        });
        self.push_place(PlaceInfo {
            root,
            parent: None,
            steps: Vec::new(),
            display: name,
        })
    }

    /// Returns the child place of `parent` with one more step. Interns it.
    pub fn child(&mut self, parent: PlaceId, step: Step, text: &str) -> PlaceId {
        if let Some(&p) = self.place_index.get(&(parent, step)) {
            return p;
        }
        let base = self.place(parent);
        let mut steps = base.steps.clone();
        steps.push(step);
        let info = PlaceInfo {
            root: base.root,
            parent: Some(parent),
            steps,
            display: format!("{}{}", base.display, text),
        };
        let id = self.push_place(info);
        self.place_index.insert((parent, step), id);
        id
    }

    fn push_place(&mut self, info: PlaceInfo) -> PlaceId {
        let id = PlaceId(u32::try_from(self.places.len()).unwrap_or(u32::MAX));
        self.places.push(info);
        id
    }

    /// Adds a variable.
    pub fn add_var(&mut self, info: VarInfo) -> VarId {
        let id = VarId(u32::try_from(self.vars.len()).unwrap_or(u32::MAX));
        self.vars.push(info);
        id
    }

    /// Adds a node.
    pub fn add_node(
        &mut self,
        span: Span,
        label: impl Into<String>,
        detail: impl Into<String>,
    ) -> NodeId {
        let id = NodeId(u32::try_from(self.nodes.len()).unwrap_or(u32::MAX));
        self.nodes.push(NodeInfo {
            span,
            label: label.into(),
            detail: detail.into(),
        });
        id
    }

    /// Adds a task.
    pub fn add_task(&mut self, kind: TaskKind, span: Span) -> TaskId {
        let id = TaskId(u32::try_from(self.tasks.len()).unwrap_or(u32::MAX));
        self.tasks.push(TaskInfo { kind, span });
        id
    }

    /// Adds a capability.
    pub const fn add_cap(&mut self) -> CapId {
        let id = CapId(self.caps);
        self.caps += 1;
        id
    }

    /// Sorts and deduplicates every relation, so that equal facts compare equal.
    pub fn normalize(&mut self) {
        fn nd<T: Ord>(v: &mut Vec<T>) {
            v.sort();
            v.dedup();
        }
        nd(&mut self.cfg_edge);
        nd(&mut self.points_into);
        nd(&mut self.mutates_at);
        nd(&mut self.reads_at);
        nd(&mut self.performs_at);
        nd(&mut self.footprint);
        nd(&mut self.rebound_at);
        nd(&mut self.uses);
        nd(&mut self.moved_at);
        nd(&mut self.scope_end);
        nd(&mut self.may_abort);
        nd(&mut self.multi_at);
        nd(&mut self.declared_mut);
        nd(&mut self.declared_effect);
        nd(&mut self.escapes_at);
        nd(&mut self.shared_root);
        nd(&mut self.spawned_at);
        nd(&mut self.joined_at);
        nd(&mut self.task_reads);
        nd(&mut self.task_writes);
        nd(&mut self.captures);
        nd(&mut self.mut_through);
        nd(&mut self.call_mut);
        nd(&mut self.call_arg);
    }
}

/// The violation relations of the spec. Both checkers produce this value.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Violations {
    /// `error(R, P)`: W0301.
    pub error: BTreeSet<(VarId, NodeId)>,
    /// `use_after_move(V, P)`: W0302, W0501, W0502.
    pub use_after_move: BTreeSet<(VarId, NodeId)>,
    /// `moved_immovable(V, P)`: W0604.
    pub moved_immovable: BTreeSet<(VarId, NodeId)>,
    /// `unconsumed(V, P)`: W0601.
    pub unconsumed: BTreeSet<(VarId, NodeId)>,
    /// `overwritten(V, P)`: W0601.
    pub overwritten: BTreeSet<(VarId, NodeId)>,
    /// `abort_unhandled(V, P)`: W0602.
    pub abort_unhandled: BTreeSet<(VarId, NodeId)>,
    /// `live_across_multi(V, P)`: W0503.
    pub live_across_multi: BTreeSet<(VarId, NodeId)>,
    /// `unauthorized_mut(P, M)`: W0703.
    pub unauthorized_mut: BTreeSet<(NodeId, PlaceId)>,
    /// `unauthorized_effect(P, E)`: W0702.
    pub unauthorized_effect: BTreeSet<(NodeId, String)>,
    /// `shared_mutation(P, M)`: W0402.
    pub shared_mutation: BTreeSet<(NodeId, PlaceId)>,
    /// `alias_conflict(P, M, A)`: W0312.
    pub alias_conflict: BTreeSet<(NodeId, PlaceId, PlaceId)>,
    /// `task_conflict(T, P)`: W0405.
    pub task_conflict: BTreeSet<(TaskId, NodeId)>,
    /// `nonportable_capture(T, V)`: W0401.
    pub nonportable_capture: BTreeSet<(TaskId, VarId)>,
    /// `shared_mut_capture(T, V)`: W0403.
    pub shared_mut_capture: BTreeSet<(TaskId, VarId)>,
    /// `root_handler_in_lib(H)`: W0801.
    pub root_handler_in_lib: BTreeSet<HandlerId>,
    /// `stealable(T)`: information for the scheduler.
    pub stealable: BTreeSet<TaskId>,
}

impl Violations {
    /// Returns true if no rule fired (the `stealable` relation is not a violation).
    pub fn is_clean(&self) -> bool {
        self.error.is_empty()
            && self.use_after_move.is_empty()
            && self.moved_immovable.is_empty()
            && self.unconsumed.is_empty()
            && self.overwritten.is_empty()
            && self.abort_unhandled.is_empty()
            && self.live_across_multi.is_empty()
            && self.unauthorized_mut.is_empty()
            && self.unauthorized_effect.is_empty()
            && self.shared_mutation.is_empty()
            && self.alias_conflict.is_empty()
            && self.task_conflict.is_empty()
            && self.nonportable_capture.is_empty()
            && self.shared_mut_capture.is_empty()
            && self.root_handler_in_lib.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn child_places_are_interned() {
        let mut f = FnFacts::default();
        let w = f.add_root("world", RootKind::Param);
        let s = Step {
            kind: StepKind::Field { id: 0 },
            unstable: false,
        };
        let a = f.child(w, s, ".entities");
        let b = f.child(w, s, ".entities");
        assert_eq!(a, b);
        assert_eq!(f.place(a).display, "world.entities");
        assert_eq!(f.place(a).parent, Some(w));
        assert!(f.param_rooted(a));
        let l = f.add_root("lines", RootKind::Local);
        assert!(!f.param_rooted(l));
    }

    #[test]
    fn ids_display_with_prefix() {
        assert_eq!(NodeId(3).to_string(), "n3");
        assert_eq!(VarId(1).to_string(), "v1");
        assert_eq!(PlaceId(0).to_string(), "p0");
        assert_eq!(TaskId(2).index(), 2);
    }

    #[test]
    fn normalize_sorts_and_dedups() {
        let mut f = FnFacts {
            cfg_edge: vec![
                (NodeId(2), NodeId(3)),
                (NodeId(0), NodeId(1)),
                (NodeId(2), NodeId(3)),
            ],
            ..FnFacts::default()
        };
        f.normalize();
        assert_eq!(
            f.cfg_edge,
            vec![(NodeId(0), NodeId(1)), (NodeId(2), NodeId(3))]
        );
        assert!(Violations::default().is_clean());
    }
}
