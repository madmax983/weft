//! # Group Borrowing: a formal model
//!
//! This file defines
//!   * a *dynamic* semantics: a heap of allocations whose ownership edges form
//!     a forest rooted at local variables, plus reference variables that are
//!     raw pointers (address + allocation stamp), and
//!   * a *static* checker implementing the group-borrowing rules from
//!     Nick Smith's proposal (as written up at verdagon.dev/blog/group-borrowing):
//!       - every reference has a *group*: a local plus a path of child-group
//!         labels (`d`, `d.rings*`, `d.rings*.gems*`, ...);
//!       - any number of references, mutable or not, may alias within a group;
//!       - a possibly-mutating use of a reference in group `G` invalidates
//!         references into *strict child groups* of `G`, and nothing else.
//!
//! `soundness.rs` proves that checked programs never dereference a dangling
//! pointer.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Basic names
// ---------------------------------------------------------------------------

pub type Addr = nat;
/// A child-group label: a field holding independently destroyable contents
/// (a `Box`, a `List`'s elements, a variant payload, ...).
pub type Label = nat;
pub type Local = nat;
/// A reference variable.
pub type Var = nat;
/// Allocation identity ("provenance"). Fresh allocations get fresh stamps, so a
/// pointer whose stamp matches the object at its address points at the very
/// allocation it was created from.
pub type Stamp = nat;
pub type Ty = nat;

// ---------------------------------------------------------------------------
// Heap
// ---------------------------------------------------------------------------

/// One allocation. `data` is inline (stable) content: primitive fields, the
/// header of an inline `List`, ... Everything that can be destroyed
/// independently of this allocation is a separate allocation owned through
/// `kids`, each edge tagged with the child-group label it lives in.
pub struct Obj {
    pub stamp: Stamp,
    pub ty: Ty,
    pub data: Seq<int>,
    pub kids: Seq<(Label, Addr)>,
}

pub type Heap = Map<Addr, Obj>;

/// A raw pointer, as held by a reference variable at runtime.
pub struct Ptr {
    pub addr: Addr,
    pub stamp: Stamp,
    pub ty: Ty,
}

pub struct DState {
    pub heap: Heap,
    /// Each local owns one root allocation.
    pub locals: Map<Local, Addr>,
    pub vars: Map<Var, Ptr>,
    pub next_stamp: Stamp,
}

/// One step down the ownership tree: follow the `idx`-th kid, which must carry `label`.
pub type Step = (Label, nat);

pub type Route = Seq<Step>;

pub open spec fn kid_at(h: Heap, b: Addr, st: Step) -> Option<Addr> {
    if h.contains_key(b) && st.1 < h[b].kids.len() && h[b].kids[st.1 as int].0 == st.0 {
        Some(h[b].kids[st.1 as int].1)
    } else {
        None
    }
}

/// Follow a route from `a`.
pub open spec fn resolve(h: Heap, a: Addr, r: Route) -> Option<Addr>
    decreases r.len(),
{
    if r.len() == 0 {
        Some(a)
    } else {
        match resolve(h, a, r.drop_last()) {
            Some(b) => kid_at(h, b, r.last()),
            None => None,
        }
    }
}

pub open spec fn labels(r: Route) -> Seq<Label> {
    Seq::new(r.len(), |j: int| r[j].0)
}

/// Allocation `b` owns `c` through its `i`-th kid edge.
pub open spec fn owns(h: Heap, b: Addr, i: int, c: Addr) -> bool {
    h.contains_key(b) && 0 <= i < h[b].kids.len() && h[b].kids[i].1 == c
}

pub open spec fn unique_owners(h: Heap) -> bool {
    forall|b1: Addr, i1: int, b2: Addr, i2: int, c: Addr|
        #[trigger] owns(h, b1, i1, c) && #[trigger] owns(h, b2, i2, c) ==> b1 == b2 && i1 == i2
}

pub open spec fn unowned(h: Heap, a: Addr) -> bool {
    forall|b: Addr, i: int| !#[trigger] owns(h, b, i, a)
}

/// Heap well-formedness: ownership is a forest whose roots are exactly the
/// locals, and stamps identify allocations.
pub open spec fn wf(s: DState) -> bool {
    let h = s.heap;
    &&& forall|x: Local| #[trigger] s.locals.contains_key(x) ==> h.contains_key(s.locals[x])
    &&& forall|x: Local, y: Local|
        s.locals.contains_key(x) && s.locals.contains_key(y) && #[trigger] s.locals[x]
            == #[trigger] s.locals[y] ==> x == y
    &&& forall|x: Local| #[trigger] s.locals.contains_key(x) ==> unowned(h, s.locals[x])
    &&& forall|b: Addr, i: int|
        h.contains_key(b) && 0 <= i < h[b].kids.len() ==> h.contains_key(#[trigger] h[b].kids[i].1)
    &&& unique_owners(h)
    &&& forall|a: Addr| #[trigger] h.contains_key(a) ==> h[a].stamp < s.next_stamp
    &&& forall|a: Addr, b: Addr|
        h.contains_key(a) && h.contains_key(b) && #[trigger] h[a].stamp == #[trigger] h[b].stamp
            ==> a == b
}

// ---------------------------------------------------------------------------
// Programs
// ---------------------------------------------------------------------------

pub struct Ret {
    pub dst: Var,
    /// Index into the call's argument list.
    pub arg: nat,
    /// The returned reference lives in child group `args[arg].group ++ path`.
    pub path: Seq<Label>,
}

pub enum Instr {
    /// `dst = &x`
    Borrow { dst: Var, x: Local },
    /// `dst = &src.label[i]` for a runtime-chosen `i` (bounds failure aborts safely)
    Child { dst: Var, src: Var, label: Label },
    /// `dst = src`
    Copy { dst: Var, src: Var },
    /// read an inline field
    Read { src: Var, field: nat },
    /// write an inline (primitive) field: cannot destroy anything
    Write { src: Var, field: nat, val: int },
    /// Call an arbitrary function. `args[k] = (var, is_mut)`. Mutable arguments
    /// may share groups (mutable aliasing). The callee is any code that only
    /// touches what it can reach from its mutable arguments.
    Call { args: Seq<(Var, bool)>, ret: Option<Ret> },
}

// ---------------------------------------------------------------------------
// Dynamic semantics
// ---------------------------------------------------------------------------

pub open spec fn ptr_to(h: Heap, a: Addr) -> Ptr {
    Ptr { addr: a, stamp: h[a].stamp, ty: h[a].ty }
}

/// The pointer still designates the live allocation (and type) it was created for.
pub open spec fn live(s: DState, p: Ptr) -> bool {
    s.heap.contains_key(p.addr) && s.heap[p.addr].stamp == p.stamp && s.heap[p.addr].ty == p.ty
}

pub open spec fn dangling(s: DState, v: Var) -> bool {
    !s.vars.contains_key(v) || !live(s, s.vars[v])
}

/// Undefined behaviour: dereferencing a dangling reference.
pub open spec fn ub(s: DState, i: Instr) -> bool {
    match i {
        Instr::Borrow { .. } => false,
        Instr::Copy { .. } => false,
        Instr::Child { src, .. } => dangling(s, src),
        Instr::Read { src, .. } => dangling(s, src),
        Instr::Write { src, .. } => dangling(s, src),
        Instr::Call { args, .. } => exists|k: int| 0 <= k < args.len() && #[trigger] dangling(s, args[k].0),
    }
}

/// `a` is the target of some mutable argument.
pub open spec fn is_mut_root(s: DState, args: Seq<(Var, bool)>, a: Addr) -> bool {
    exists|k: int| 0 <= k < args.len() && args[k].1 && #[trigger] s.vars[args[k].0].addr == a
}

/// `c` is a strict descendant of `m` in the ownership tree.
pub open spec fn below(h: Heap, m: Addr, c: Addr) -> bool {
    exists|r: Route| r.len() > 0 && #[trigger] resolve(h, m, r) == Some(c)
}

pub open spec fn below_mut(s: DState, args: Seq<(Var, bool)>, c: Addr) -> bool {
    exists|m: Addr| is_mut_root(s, args, m) && #[trigger] below(s.heap, m, c)
}

/// Everything a callee could possibly modify or free.
pub open spec fn footprint(s: DState, args: Seq<(Var, bool)>, a: Addr) -> bool {
    is_mut_root(s, args, a) || below_mut(s, args, a)
}

/// What an arbitrary callee may do to the heap. It is the most general effect
/// of code that (a) only reaches memory through its mutable arguments — there
/// are no globals and references are not stored in the heap — and (b) keeps
/// the ownership discipline. Inside its footprint it may mutate, move, free
/// and allocate at will.
pub open spec fn callee_effect(s: DState, args: Seq<(Var, bool)>, h2: Heap, n2: Stamp) -> bool {
    let s2 = DState { heap: h2, locals: s.locals, vars: s.vars, next_stamp: n2 };
    &&& wf(s2)
    &&& n2 >= s.next_stamp
    // frame: outside the footprint nothing changes
    &&& forall|a: Addr|
        #[trigger] s.heap.contains_key(a) && !footprint(s, args, a) ==> h2.contains_key(a) && h2[a]
            == s.heap[a]
    // the borrowed argument objects themselves cannot be destroyed (only their contents)
    &&& forall|m: Addr|
        is_mut_root(s, args, m) && !below_mut(s, args, m) ==> #[trigger] h2.contains_key(m)
            && h2[m].stamp == s.heap[m].stamp && h2[m].ty == s.heap[m].ty
    // stamp honesty: an object is either the same allocation as before, or fresh
    &&& forall|a: Addr|
        #[trigger] h2.contains_key(a) ==> h2[a].stamp >= s.next_stamp || (s.heap.contains_key(a)
            && s.heap[a].stamp == h2[a].stamp && s.heap[a].ty == h2[a].ty)
}

pub open spec fn call_result(
    s: DState,
    args: Seq<(Var, bool)>,
    ret: Option<Ret>,
    h2: Heap,
    n2: Stamp,
    s2: DState,
) -> bool {
    match ret {
        None => s2 == DState { heap: h2, locals: s.locals, vars: s.vars, next_stamp: n2 },
        Some(r) => r.arg < args.len() && exists|route: Route|
            {
                let res = #[trigger] resolve(h2, s.vars[args[r.arg as int].0].addr, route);
                &&& labels(route) == r.path
                &&& res is Some
                &&& h2.contains_key(res->0)
                &&& s2 == DState {
                    heap: h2,
                    locals: s.locals,
                    vars: s.vars.insert(r.dst, ptr_to(h2, res->0)),
                    next_stamp: n2,
                }
            },
    }
}

/// One (non-UB) execution step. Nondeterminism models unknown indices and
/// unknown callees.
pub open spec fn step(s: DState, i: Instr, s2: DState) -> bool {
    match i {
        Instr::Borrow { dst, x } => s.locals.contains_key(x) && s2 == DState {
            vars: s.vars.insert(dst, ptr_to(s.heap, s.locals[x])),
            ..s
        },
        Instr::Child { dst, src, label } => !dangling(s, src) && exists|idx: nat|
            {
                let res = #[trigger] kid_at(s.heap, s.vars[src].addr, (label, idx));
                res is Some && s2 == DState { vars: s.vars.insert(dst, ptr_to(s.heap, res->0)), ..s }
            },
        Instr::Copy { dst, src } => s2 == DState {
            vars: if s.vars.contains_key(src) {
                s.vars.insert(dst, s.vars[src])
            } else {
                s.vars.remove(dst)
            },
            ..s
        },
        Instr::Read { src, field } => !dangling(s, src) && field < s.heap[s.vars[src].addr].data.len()
            && s2 == s,
        Instr::Write { src, field, val } => {
            let a = s.vars[src].addr;
            let o = s.heap[a];
            !dangling(s, src) && field < o.data.len() && s2 == DState {
                heap: s.heap.insert(a, Obj { data: o.data.update(field as int, val), ..o }),
                ..s
            }
        },
        Instr::Call { args, ret } => (forall|k: int|
            0 <= k < args.len() ==> !#[trigger] dangling(s, args[k].0)) && exists|h2: Heap, n2: Stamp|
            #[trigger] callee_effect(s, args, h2, n2) && call_result(s, args, ret, h2, n2, s2),
    }
}

// ---------------------------------------------------------------------------
// Static checker (group borrowing)
// ---------------------------------------------------------------------------

/// `local` followed by child-group labels, e.g. `d.rings*.gems*`.
pub struct Group {
    pub root: Local,
    pub path: Seq<Label>,
}

/// The checker's state: which locals exist, and which reference variables are
/// currently valid, with their groups.
pub struct SState {
    pub locals: Set<Local>,
    pub vars: Map<Var, Group>,
}

/// `g` is a strict child group of `p`.
pub open spec fn strict_child(g: Group, p: Group) -> bool {
    g.root == p.root && p.path.len() < g.path.len() && g.path.subrange(0, p.path.len() as int)
        == p.path
}

/// The group-borrowing invalidation rule: a reference is invalidated by a call
/// iff its group is a strict child group of some mutable argument's group.
pub open spec fn killed(ss: SState, args: Seq<(Var, bool)>, g: Group) -> bool {
    exists|k: int| 0 <= k < args.len() && args[k].1 && #[trigger] strict_child(g, ss.vars[args[k].0])
}

pub open spec fn survivors(ss: SState, args: Seq<(Var, bool)>) -> Map<Var, Group> {
    Map::new(ss.vars.dom().filter(|v: Var| !killed(ss, args, ss.vars[v])), |v: Var| ss.vars[v])
}

pub open spec fn instr_ok(ss: SState, i: Instr) -> bool {
    match i {
        Instr::Borrow { x, .. } => ss.locals.contains(x),
        Instr::Child { src, .. } => ss.vars.contains_key(src),
        Instr::Copy { .. } => true,
        Instr::Read { src, .. } => ss.vars.contains_key(src),
        Instr::Write { src, .. } => ss.vars.contains_key(src),
        Instr::Call { args, ret } => {
            &&& forall|k: int| 0 <= k < args.len() ==> ss.vars.contains_key(#[trigger] args[k].0)
            &&& match ret {
                None => true,
                Some(r) => r.arg < args.len() && !killed(ss, args, ss.vars[args[r.arg as int].0]),
            }
        },
    }
}

pub open spec fn post(ss: SState, i: Instr) -> SState {
    match i {
        Instr::Borrow { dst, x } => SState {
            vars: ss.vars.insert(dst, Group { root: x, path: Seq::empty() }),
            ..ss
        },
        Instr::Child { dst, src, label } => SState {
            vars: ss.vars.insert(
                dst,
                Group { root: ss.vars[src].root, path: ss.vars[src].path.push(label) },
            ),
            ..ss
        },
        Instr::Copy { dst, src } => SState {
            vars: if ss.vars.contains_key(src) {
                ss.vars.insert(dst, ss.vars[src])
            } else {
                ss.vars.remove(dst)
            },
            ..ss
        },
        Instr::Read { .. } => ss,
        Instr::Write { .. } => ss,
        Instr::Call { args, ret } => {
            let sv = survivors(ss, args);
            match ret {
                None => SState { vars: sv, ..ss },
                Some(r) => {
                    let g = ss.vars[args[r.arg as int].0];
                    SState { vars: sv.insert(r.dst, Group { root: g.root, path: g.path + r.path }), ..ss }
                },
            }
        },
    }
}

/// Checker state before instruction `k`.
pub open spec fn ss_at(ss0: SState, prog: Seq<Instr>, k: nat) -> SState
    decreases k,
{
    if k == 0 {
        ss0
    } else {
        post(ss_at(ss0, prog, (k - 1) as nat), prog[k - 1])
    }
}

pub open spec fn check(ss0: SState, prog: Seq<Instr>) -> bool {
    forall|k: nat| k < prog.len() ==> #[trigger] instr_ok(ss_at(ss0, prog, k), prog[k as int])
}

/// A trace of `prog` from `trace[0]` (possibly stopped early, e.g. by a safe abort).
pub open spec fn is_trace(prog: Seq<Instr>, trace: Seq<DState>) -> bool {
    &&& 1 <= trace.len() <= prog.len() + 1
    &&& forall|k: int| 0 <= k < trace.len() - 1 ==> step(#[trigger] trace[k], prog[k], trace[k + 1])
}

} // verus!
