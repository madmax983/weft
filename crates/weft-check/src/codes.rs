//! The diagnostic codes. `weft explain CODE` prints these texts.

/// One diagnostic code.
#[derive(Clone, Copy, Debug)]
pub struct Code {
    /// The code, for example `W0301`.
    pub code: &'static str,
    /// A short title.
    pub title: &'static str,
    /// The rule in the spec, or the phase that reports it.
    pub rule: &'static str,
    /// What the code means and how to fix it.
    pub text: &'static str,
}

/// All codes, in order.
pub const CODES: &[Code] = &[
    Code { code: "W0001", title: "syntax error", rule: "parser", text: "The source does not follow docs/grammar.md." },
    Code { code: "W0101", title: "unknown name", rule: "names", text: "No local, item, effect or module has this name in scope." },
    Code { code: "W0102", title: "type mismatch", rule: "types", text: "Two types must be equal and they are not." },
    Code { code: "W0103", title: "wrong number of arguments or fields", rule: "types", text: "The call or the pattern has a different number of parts than the declaration." },
    Code { code: "W0104", title: "unknown field, method or operation", rule: "types", text: "The type, module or effect has no member with this name." },
    Code { code: "W0105", title: "not callable", rule: "types", text: "Only functions, closures and constructors can be called." },
    Code { code: "W0107", title: "duplicate definition", rule: "names", text: "Two items in one module have the same name." },
    Code { code: "W0201", title: "bad place root", rule: "signatures", text: "A place in a signature must start at a parameter, `self` or an `rc` type." },
    Code { code: "W0203", title: "argument points elsewhere", rule: "signatures", text: "A reference argument must point inside the place that the parameter states with `in`." },
    Code { code: "W0204", title: "returned reference place", rule: "signatures", text: "A returned reference must state its place, and the body must return a reference inside it. A function or a closure cannot return a reference into its own locals, by-value parameters or temporaries: they go out of scope at the return." },
    Code { code: "W0301", title: "use of an invalidated reference", rule: "error(R, P)", text: "A mutation of an enclosing place, through an unstable step, invalidated the reference. Rules 3 to 5 of the design. A move or the end of the scope of the owner also invalidates every reference into the owned value, and so does a new value, a move or the end of an `Rc` handle on the way to the place." },
    Code { code: "W0302", title: "use after move", rule: "use_after_move(V, P)", text: "Values are affine: a moved value cannot be used again until it gets a new value." },
    Code { code: "W0303", title: "move out of a borrowed place", rule: "moves", text: "A value behind a reference cannot be moved. Borrow it with `&`." },
    Code { code: "W0312", title: "overlapping arguments", rule: "alias_conflict(P, M, A)", text: "The callee mutates one place while another argument (or a handler footprint) points into it. The callee sees separate places and cannot protect the references." },
    Code { code: "W0313", title: "capability escapes its handler", rule: "handlers", text: "A closure that performs through a local handler cannot leave the handled computation." },
    Code { code: "W0314", title: "task performs a user effect", rule: "tasks", text: "A handler runs on the stack of one task. A spawned task or a fork branch cannot reach it." },
    Code { code: "W0401", title: "nonportable capture in fork", rule: "nonportable_capture(T, V)", text: "A fork branch runs on another thread. It cannot capture a nonportable value, for example an `rc` value." },
    Code { code: "W0402", title: "mutation through @shared", rule: "shared_mutation(P, M)", text: "A `@ shared` reference is read-only from every thread." },
    Code { code: "W0403", title: "shared-mutable reference in fork", rule: "shared_mut_capture(T, V)", text: "A shared-mutable reference is nonportable. Split the data into `@ uniq` parts with disjoint places first." },
    Code { code: "W0405", title: "task footprints overlap", rule: "task_conflict(T, P)", text: "Tasks that can run at the same time, even on one thread, must have separate footprints." },
    Code { code: "W0406", title: "uniq reference expected", rule: "modes", text: "The parameter is `@ uniq`, but the argument can be aliased." },
    Code { code: "W0501", title: "once continuation resumed twice", rule: "use_after_move(V, P)", text: "An operation that is not `multi` resumes at most once." },
    Code { code: "W0502", title: "once closure called twice", rule: "use_after_move(V, P)", text: "The closure moves a captured value, so it can run only once." },
    Code { code: "W0503", title: "value live across multi", rule: "live_across_multi(V, P)", text: "A `multi` operation can resume more than once. Linear values, uniq references and once values cannot be live there." },
    Code { code: "W0601", title: "linear value not consumed", rule: "unconsumed(V, P)", text: "A linear value must be moved or consumed on every normal path. Task handles must be joined or detached." },
    Code { code: "W0602", title: "abort without on abort", rule: "abort_unhandled(V, P)", text: "A linear value is live across an operation that can abort, but its type declares no `on abort`." },
    Code { code: "W0604", title: "move of a !Move value", rule: "moved_immovable(V, P)", text: "A `!Move` value keeps its address for its whole life." },
    Code { code: "W0605", title: "reference field", rule: "types", text: "Only a `!Move` struct can hold a reference, and only into `self`." },
    Code { code: "W0701", title: "public effects not stated", rule: "signatures", text: "Bodies infer effects. A public signature must state them." },
    Code { code: "W0702", title: "effect not in signature", rule: "unauthorized_effect(P, E)", text: "The body performs an effect that the signature does not state and no local handler handles." },
    Code { code: "W0703", title: "mutation not in signature", rule: "unauthorized_mut(P, M)", text: "The body mutates a place reached from a parameter that no `mut(...)` in the signature covers." },
    Code { code: "W0705", title: "function argument effects", rule: "signatures", text: "A function argument performs an effect that the parameter type does not allow." },
    Code { code: "W0801", title: "root handler in a library", rule: "root_handler_in_lib(H)", text: "Only binaries and tests install root handlers for standard effects. Libraries may intercept them." },
    Code { code: "W0802", title: "simulation in a library", rule: "root handlers", text: "`sim.run` replaces every root handler. Only binaries and tests can use it." },
    Code { code: "W0803", title: "no runtime", rule: "runtime profile", text: "With `runtime = \"none\"`, `main` must handle every standard effect that it performs." },
    Code { code: "W0901", title: "dependency authority", rule: "package", text: "A dependency's public function needs an effect that the project does not grant to it." },
    Code { code: "W0902", title: "library enables the GC", rule: "package", text: "Libraries may never require the GC tier. Only a binary may switch it on." },
    Code { code: "W1001", title: "fip allocation", rule: "fip", text: "A `fip` function must reuse a freed cell of the same size for each constructor." },
    Code { code: "W1002", title: "fip linearity", rule: "fip", text: "A `fip` function must use each owned value exactly once on every path." },
    Code { code: "W1003", title: "fip call", rule: "fip", text: "A `fip` function can call only `fip` functions and constructors." },
    Code { code: "W1004", title: "fip effects", rule: "fip", text: "A `fip` function has no effects." },
];

/// Finds a code.
pub fn lookup(code: &str) -> Option<&'static Code> {
    CODES.iter().find(|c| c.code.eq_ignore_ascii_case(code))
}

#[cfg(test)]
mod tests {
    #[test]
    fn codes_are_sorted_and_unique() {
        let codes: Vec<&str> = super::CODES.iter().map(|c| c.code).collect();
        let mut sorted = codes.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(codes, sorted);
        assert!(super::lookup("w0301").is_some());
        assert!(super::lookup("X").is_none());
    }
}
