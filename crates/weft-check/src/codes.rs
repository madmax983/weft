//! The diagnostic codes. `weft explain CODE` prints these texts.

use weft_syntax::diag::Code as DiagCode;

/// One diagnostic code.
#[derive(Clone, Copy, Debug)]
pub struct Code {
    /// The code, for example `W0301`.
    pub code: DiagCode,
    /// A short title.
    pub title: &'static str,
    /// The rule in the spec, or the phase that reports it.
    pub rule: &'static str,
    /// What the code means and how to fix it.
    pub text: &'static str,
}

/// All codes, in order.
pub const CODES: &[Code] = &[
    Code { code: DiagCode::L0001, title: "lint warning", rule: "user lint rules", text: "A rule of the file that `weft lint --rules` reads derived `lint(Name, Node)` for this node." },
    Code { code: DiagCode::W0001, title: "syntax error", rule: "parser", text: "The source does not follow docs/grammar.md." },
    Code { code: DiagCode::W0101, title: "unknown name", rule: "names", text: "No local, item, effect or module has this name in scope. A function or an effect of another package is in scope only if it is `pub`. An effect of another module has a path, as a type has (`a.Note`, `util.Note`)." },
    Code { code: DiagCode::W0102, title: "type mismatch", rule: "types", text: "Two types must be equal and they are not." },
    Code { code: DiagCode::W0103, title: "wrong number of arguments or fields", rule: "types", text: "The call or the pattern has a different number of parts than the declaration, or a call gives a named argument two times." },
    Code { code: DiagCode::W0104, title: "unknown field, method or operation", rule: "types", text: "The type, module or effect has no member with this name. A named argument must name a parameter of the function, the method or the operation, or a field of the struct. A closure, a function parameter, a variant, `resume`, `print`, `fork` and `s.spawn` have no parameter names: give their arguments by position." },
    Code { code: DiagCode::W0105, title: "not callable", rule: "types", text: "Only functions, closures and constructors can be called." },
    Code { code: DiagCode::W0107, title: "duplicate definition", rule: "names", text: "A name is defined twice in one scope. A scope can be the items of a module, the fields of a struct or the variants of an enum. It can also be the parameters of a function, a closure or an operation, the type parameters of an item, the names that one pattern binds or the fields of one struct literal. The name of a dependency must not hide a name that the root sees. Such a name is an item of the root, a prelude item or a standard effect such as `log`. A dependency cannot have the name `main`: the effects of the root have `main` in their identity. An operation must not have a name that a bare call always finds first: `print`, `fork`, the `assert` statement, or a function, a type or a variant of the prelude. Rename it. A bare call that can perform the operations of two effects of one module is an error too: write the effect name (`First.go(...)`)." },
    Code { code: DiagCode::W0108, title: "unknown extern type property", rule: "items", text: "An extern type property must be `elem`, `deref`, `copy`, `linear`, `on_abort` or `nonportable`." },
    Code { code: DiagCode::W0109, title: "impl of an unnamed type", rule: "items", text: "An `impl` block needs a named struct, enum or extern type." },
    Code { code: DiagCode::W0110, title: "parameter type missing", rule: "signatures", text: "Each parameter needs a type. Only `self` in an `impl` can have no type." },
    Code { code: DiagCode::W0111, title: "break or continue outside a loop", rule: "control flow", text: "`break` and `continue` are valid only in a `while`, `for` or `loop` body. In a closure, the loop must be in the closure too." },
    Code { code: DiagCode::W0112, title: "assignment to a value", rule: "places", text: "The left side of an assignment must be a place: a local, a field, an element or a variant payload." },
    Code { code: DiagCode::W0113, title: "variant pattern outside match", rule: "patterns", text: "`let` can destructure a tuple or a struct. An enum variant needs `match`, because the value can be another variant." },
    Code { code: DiagCode::W0114, title: "range outside for", rule: "types", text: "A range `a..b` is valid only as the iterated value of a `for` loop." },
    Code { code: DiagCode::W0115, title: "incomplete construct", rule: "types", text: "A struct literal must give every field that is not a place field. `s.spawn` needs the capability `s` of an enclosing `scope`." },
    Code { code: DiagCode::W0116, title: "raw pointer outside FFI", rule: "types", text: "A written raw pointer type `*T` is valid only in an `extern fn` signature, in a local and in a closure parameter. The check looks at written types only; a type argument can hold a raw pointer. A raw pointer is an opaque copy value with no place: it has no fields and no deref." },
    Code { code: DiagCode::W0117, title: "type of infinite size", rule: "items", text: "A struct holds its fields inline, also through tuples, arrays and other structs. A struct that holds itself that way has no finite size. Put the field behind an indirection: an enum, `Box` or `Vec`." },
    Code { code: DiagCode::W0118, title: "bad `on abort` function", rule: "items", text: "The function after `on abort =` must take exactly one parameter: a value of the linear type, with the type parameters of the function in order (`fn undo<T>(g: G<T>)` for `G<T>`). The unwinder calls it with the value, with the root handlers only. So its effects, also inferred ones, can name only the standard effects other than `fail`, and with no runtime none. It cannot change a place outside the value that it gets, such as an `rc` group: the node that aborts does not state the change. It cannot raise a failure of the runtime (a `join` of a failed task, a scope or a `fork` with a failed child, a read of a file) unless a `Fail` handler of the function gets it. It cannot call a function value that it does not know, for example one from a field of its value. The unwinder gives it each instance of the type, and it drops the result. So the function cannot drop or hold a value of a type parameter, and its result cannot hold a linear value. A change through a reference that the value holds is a change outside the value: if the parameter type holds a reference, each change of the parameter counts so." },
    Code { code: DiagCode::W0119, title: "contradictory modes", rule: "modes", text: "A type has one mode on each axis, so two values of one axis contradict, for example `once` and `many`. Also `uniq` and `shared` contradict: other threads can read a `shared` value, so other references to it exist." },
    Code { code: DiagCode::W0120, title: "match does not cover every value", rule: "patterns", text: "A `match` needs an arm for each value that the scrutinee can have: each variant of an enum, `true` and `false`, and an arm that matches any other integer or string. A `_` or a name matches anything. The interpreter stops if no arm matches. A `match` that is too large to check is W0120 too." },
    Code { code: DiagCode::W0201, title: "bad place root", rule: "signatures", text: "A place in a signature must start at a parameter, `self` or an `rc` type. The `in` place of a parameter cannot start at the parameter itself, and the `in` places of the parameters cannot form a cycle." },
    Code { code: DiagCode::W0203, title: "argument points elsewhere", rule: "arg_outside(P, I, A)", text: "A reference argument must point inside the place that the parameter states with `in`. Below a plain place only stable steps can follow: `in w.a` does not take a reference into `w.a[]`, because a change of `w.a` can invalidate it. Write `in w.a[]` or `in w.a..`." },
    Code { code: DiagCode::W0204, title: "returned reference place", rule: "ref_outside(P, A), signatures", text: "A returned reference must state its place, and the body must return a reference inside it (`ref_outside`). Below a plain place only stable steps can follow, as for W0203. A function or a closure cannot return a reference into its own locals, by-value parameters or temporaries: they go out of scope at the return. A function cannot put such a reference behind a reference parameter either: the caller keeps it. It cannot put one into an `rc` object, because the object stays after the return. A reference behind a local `Rc` handle of another `rc` type counts too: the object can go away with the handle. A closure points into what it captures, also into a value that a captured variable gets later. So a function cannot return such a closure or put it there. A closure or a clause that puts its reference parameter there gets the places that each call gives. A handler of a caller can resume with a reference into a place of the caller, so a function that returns it cannot state a place for it." },
    Code { code: DiagCode::W0301, title: "use of an invalidated reference", rule: "error(R, P)", text: "A mutation of an enclosing place, through an unstable step, invalidated the reference. Rules 3 to 5 of the design. A move or the end of the scope of the owner also invalidates every reference into the owned value, and so does a new value, a move or the end of an `Rc` handle on the way to the place. A move of a part, such as `take(p.a)`, leaves no value in the part: it invalidates each reference that overlaps the part, also a reference to the whole value. A reference to another part stays valid. A call that gives a place to a function parameter, or to a function value that the body does not know, can mutate through it. A reference into a wildcard place `p..` is invalid after any change that overlaps `p`, and a change anywhere in `p..` invalidates each reference strictly inside `p`. The result of one call with no stated place is one place `(p..)`: a change through it follows rules 3 to 5 for references into the same result. A write through a reference, at its place or below it, leaves that reference valid. A clause parameter is not valid after a `resume` if the handled body changed or moved a place above what it points to, if a local of the body that it points into went out of scope, or if a callee of the body performed the operation. A call that runs a closure that resumes does the same. A closure reads its captured variables where it runs, so it gets their new values there. A callee that can call a function argument more than once, also one in a container, runs it two times in a row: a change in the first run can invalidate what the closure captures for the second run. A task can change what it writes at any time while it runs, so a reference that the parent makes while the task runs is invalid after the end of the task (a `join`, the end of a scope or a `fork`, or an abort) if the task can break it. A closure that captures the scope capability is invalid after the scope." },
    Code { code: DiagCode::W0302, title: "use after move", rule: "use_after_move(V, P)", text: "Values are affine: a moved value cannot be used again until it gets a new value." },
    Code { code: DiagCode::W0303, title: "move out of a borrowed place", rule: "moves", text: "A value behind a reference cannot be moved. Borrow it with `&`." },
    Code { code: DiagCode::W0304, title: "use before a value", rule: "use_before_set(V, P)", text: "`let x: T` with no value declares `x`. Each path to a use of `x` must give it a value first. A place field of a `!Move` struct that the struct literal does not give has no value too, also in a new value that an assignment gives. A reference to the struct, or to the field, can read it. A `let` or an assignment that moves a value needs a value in each of its place fields. A recursive type has a place field at each depth: a read or a borrow of a part that holds the recursive type uses them, until the body gives that part a new value." },
    Code { code: DiagCode::W0312, title: "overlapping arguments", rule: "alias_conflict(P, M, A)", text: "The callee mutates one place while another argument (or a handler footprint) points into it. The callee sees separate places and cannot protect the references. A closure argument points into the places that it captures, and a perform passes its reference arguments to the clause. A function value can mutate through each place that it gets." },
    Code { code: DiagCode::W0313, title: "capability escapes its handler", rule: "handlers", text: "A closure that performs through a local handler cannot leave the handled computation: not as its value (also inside a tuple, a struct or another closure), not through a local outside it, and not to a place or code that can keep it. A callee can copy it out of a reference argument, and a clause of a handler inside the computation can keep its parameter. A clause runs outside its own handler, so the closure cannot go to an operation of that handler either. A continuation is a capability of its clause in the same way: a closure that calls `resume` cannot leave the clause, and a `resume` cannot give it to the handled computation." },
    Code { code: DiagCode::W0314, title: "task reaches a handler on another stack", rule: "tasks", text: "A handler runs on the stack of one task. A spawned task or a fork branch cannot reach it: not a local handler, not the handler of a user effect, and not a local handler of a standard effect that a task of a callee performs. A task can run a function value from a field or a container: the caller checks the values in the argument. A clause can run a function argument of its operation as a task. The root handlers of `sim.run` replace the runtime for every task. A failure of a task goes to the task that joins it. A task or a fork branch cannot resume a continuation of this task either: the rest of the handled body would run on another task." },
    Code { code: DiagCode::W0315, title: "jump out of a handled or scope body", rule: "control flow", text: "A `return`, `break` or `continue` cannot leave a handled body, a handler clause or a scope body. The handler or the scope must end first. A `return` in a closure returns from the closure." },
    Code { code: DiagCode::W0401, title: "nonportable capture in fork", rule: "nonportable_capture(T, V)", text: "A fork branch runs on another thread. It cannot capture a nonportable value, for example an `rc` value. A function argument that a callee can run on another thread (in a `fork`, or in foreign code) is a fork branch at the call." },
    Code { code: DiagCode::W0402, title: "mutation through @shared", rule: "shared_mutation(P, M)", text: "A `@ shared` reference is read-only from every thread." },
    Code { code: DiagCode::W0403, title: "shared-mutable reference in fork", rule: "shared_mut_capture(T, V)", text: "A shared-mutable reference is nonportable. Split the data into `@ uniq` parts with disjoint places first. A captured variable that the branch writes counts too. A function argument that a callee can run on another thread is a fork branch at the call." },
    Code { code: DiagCode::W0405, title: "task footprints overlap", rule: "task_conflict(T, P)", text: "Tasks that can run at the same time, even on one thread, must have separate footprints. A node that runs while a task is active must not access what the task writes, must not write what the task reads, and must not free (move or end the owner of) what the task reads or writes. A node that gives a place to a function value that can mutate through it must not give what the task reads or writes. A closure that spawns can start its task more than once: a callee can call it twice, also from a field or a container. The copies conflict. A task handle can hold one of several tasks, for example after an `if` or in a loop. A `join` ends a task only if no other handle can hold it. A use of a whole local reads it and a new value writes it, also for a reference local; an index reads the length and the buffer of its place. A callee can run a function argument as a task: two times at one time, or at the same time as another argument (the `task_runs` part of its signature). The caller checks the argument as a task at the call." },
    Code { code: DiagCode::W0406, title: "uniq reference expected", rule: "not_uniq(P, I)", text: "The parameter is `@ uniq`, but the argument can be aliased: the mode of an argument must be a submode of the mode of its parameter. A closure that gives a captured local to such a parameter needs the local to be `@ uniq` where the closure runs." },
    Code { code: DiagCode::W0501, title: "once continuation resumed twice", rule: "use_after_move(V, P)", text: "An operation that is not `multi` resumes at most once." },
    Code { code: DiagCode::W0502, title: "once closure called twice", rule: "use_after_move(V, P)", text: "The closure moves a captured value that is not plain data, so it can run only once. A closure that calls such a closure, or resumes a `once` continuation, is `once` too. A callee that can call its function argument more than once, an operation of a handler and a place of plain data, such as a field of type `fn()`, cannot get a `once` closure." },
    Code { code: DiagCode::W0503, title: "value live across multi", rule: "live_across_multi(V, P)", text: "A `multi` operation can resume more than once. Linear values, uniq references and once values cannot be live there. A call of a function parameter or of an unknown function value counts as `multi` if a `multi` operation can reach it, and so does a call of a function that makes such a call. A node that runs a handler clause and a `resume` count too, if the clause or the handled computation can resume more than once. A `once` continuation is a once value, and so is a closure that holds one. A generic callee that holds a value of a type parameter across such a node holds the value that the call gives it. A resume copies the values of the handled body: a buffer gets a copy, and the copies share an `rc` object. So a `!Move` value (also in a `Box`, and through a reference into it or a reference argument), a task handle, a scope, a resource of an extern type that is not plain data, and an `Rc` to an object that can hold a function value or a reference are not `many` either. An operation of a local handler copies only the values of its handled body, if no clause of the handler performs through a handler outside it." },
    Code { code: DiagCode::W0504, title: "resume in a clause of fail", rule: "handlers", text: "A failure has no value to go on with. The runtime raises it where the code after it needs a value: at a `join` of a failed task, at the end of a scope with a failed child, at a `fork`, at a `with_timeout` deadline and at a failed read. So a clause of `Fail.fail` cannot resume, also not in a closure, and it cannot name its continuation. The clause gives the value of the `handle`. The effects proof models `fail` as an operation whose clause does not resume." },
    Code { code: DiagCode::W0601, title: "linear value not consumed", rule: "unconsumed(V, P), overwritten(V, P)", text: "A linear value must be moved or consumed on every normal path. Task handles must be joined or detached. A pattern `_`, a new value of its place and a place whose type is not linear drop a linear value. So does a temporary that only `print`, a comparison, a borrow or a method receiver reads. A closure that moves a linear value is linear: a callee that gets it can drop it. A generic function can drop a value of a type parameter. A `return`, a `break` or a `continue` in a later operand leaves a value that is on its way to a call. A new value with no linear part, such as `None`, has nothing to consume. `Vec.clear`, `Task.detach` and `Response.json` drop values of their type parameter. A move of a part of a linear value, such as `take(t.0)`, leaves the other parts in the value: it is still live. So does a move of a field of a `linear` struct, a move of a part in a handler clause, and a move of a part of a value of a type parameter. A later use of the value is a use after a move, so destructure it (`let (a, b) = t`) to consume each part." },
    Code { code: DiagCode::W0602, title: "abort without on abort", rule: "abort_unhandled(V, P)", text: "A linear value is live across an operation that can abort, but its type declares no `on abort`. A generic callee that holds a value of a type parameter while it can abort holds the linear value that the call gives it. So does a generic function used as a value. When a clause does not resume, the unwinder finishes the values of the handled body on the way to the end of the `handle`. So an operation of a local handler aborts only the values of its handled body, if no clause of the handler performs through a handler outside it. A move of a part of a linear value leaves the other parts live, also across a later abort. A scope can cancel a task, and a `fork` its branches, before the task runs: a sibling fails, or the owner times out or is cancelled. The closure then goes away with the values that it took. So a linear value that a task closure or a fork branch takes by value needs `on abort` at the spawn or the `fork`, and also where a block or a closure runs whose code starts the task with that value." },
    Code { code: DiagCode::W0604, title: "move of a !Move value", rule: "moved_immovable(V, P)", text: "A `!Move` value keeps its address for its whole life. A struct, a tuple, an enum or a `Vec` that holds one is `!Move` too; a `Box` is not. A callee with a parameter of a type parameter can move the value, as `Vec.push` does when its buffer grows." },
    Code { code: DiagCode::W0605, title: "reference field", rule: "ref_outside(P, A), types", text: "Only a `!Move` struct can hold a reference, and only into `self`. A new value of the field must point into the place that the field states, in the same struct (`ref_outside`). A struct literal cannot give the field a value: the struct has no place yet." },
    Code { code: DiagCode::W0701, title: "public effects not stated", rule: "signatures", text: "Bodies infer effects. A public signature must state them. The effects of a function parameter pass through to the caller with no syntax, so a public function that has no other effects has nothing to state." },
    Code { code: DiagCode::W0702, title: "effect not in signature", rule: "unauthorized_effect(P, E)", text: "The body performs an effect that the signature does not state and no local handler handles. The effects of each closure that the body makes count, also when nothing calls the closure." },
    Code { code: DiagCode::W0703, title: "mutation not in signature", rule: "unauthorized_mut(P, M)", text: "The body mutates a place reached from a parameter that no `mut(...)` in the signature covers." },
    Code { code: DiagCode::W0704, title: "effect inference does not stop", rule: "signatures", text: "Effect inference runs over the call graph until no signature changes. A body always infers the parts of its signature other than the row. These parts are: what it lends to its function parameters (`lent`); what its returned function value does (`ret`) and what that value captures (`ret_refs`); the function parameters that it stores (`stores`); if it can run a stored function value (`reaches`), what it gives to that value (`reach_given`) and if it can run it more than once (`reach_repeats`); if an unknown function value that it calls can resume more than once (`multi`); the function parameters that its tasks can call (`tasks`) and how it runs them as tasks (`task_runs`); if it can start a pinned task for a reason that a caller does not see (`pins`); the function parameters that it gives to an operation of a handler of a caller (`op_fns`) and the effects of these values there (`op_effects`); the effects that its tasks perform through a handler of a caller (`task_effects`); the function parameters that it can call more than once (`repeats`); the reference parameters that can get a function value (`fn_stores`); the parameters whose references it can put into an `rc` object (`group_stores`); the places of the closures that it puts behind a reference parameter (`fn_store_refs`); the type parameters of the values that it can drop (`drops`) or hold across an abort (`holds`); and if it can raise a failure of the runtime (`raises`). These parts do not only grow, so they have a bound: 32 changes, and two more for each function of the program. The parts of this function still change after the bound. The inference keeps their last value, so the inferred effects of this function and of its callers can be incomplete. Report the program." },
    Code { code: DiagCode::W0705, title: "function argument effects", rule: "arg_effect_outside(P, I, E)", text: "A function argument performs an effect that the parameter type does not allow." },
    Code { code: DiagCode::W0706, title: "effect inference does not converge", rule: "effect inference", text: "Effect inference stopped before it reached a fixpoint, so the inferred effects can be incomplete. A row only grows, and the bound is the height of its lattice, so this shows a checker bug. State the effects of the function, and report the program." },
    Code { code: DiagCode::W0707, title: "loop analysis does not converge", rule: "lowering", text: "The lowering of a loop body runs again until the values that an iteration gives to the next are stable: references, function values and task handles. A chain of locals needs one pass for each local. After 8 passes the lowering widens what still changes: a deeper place becomes a wildcard place, and a function value becomes one that the body does not know. So the values become stable. This error shows that they did not, so the facts of the loop can be incomplete. This is a checker bug. Report the program." },
    Code { code: DiagCode::W0801, title: "root handler in a library", rule: "root_handler_in_lib(H)", text: "Only binaries and tests install root handlers for standard effects. Libraries may intercept them: a clause that performs the effect again, through the handler outside, forwards it." },
    Code { code: DiagCode::W0802, title: "simulation in a library", rule: "sim_in_lib(P)", text: "`sim.run` replaces every root handler. Only binaries and tests can use it." },
    Code { code: DiagCode::W0803, title: "no runtime", rule: "embedded_effect(P, E)", text: "With `runtime = \"none\"`, `main` must handle every standard effect that it performs." },
    Code { code: DiagCode::W0804, title: "unknown file marker", rule: "file markers", text: "A `// weft:` line has a word that is not a marker, so the word has no effect. The markers are `library` and `no-runtime`." },
    Code { code: DiagCode::W0805, title: "effect with no handler", rule: "unhandled_effect(P, E)", text: "The runtime has root handlers only for the standard effects. So `main` and each test must handle every other effect that they perform. A handler clause runs outside its own handler, so a perform in a clause goes to the next handler out." },
    Code { code: DiagCode::W0901, title: "dependency authority", rule: "package", text: "A function of a dependency needs an effect that the project does not grant to it. Each function counts, also a private one, with the effects that its body infers and the closures that it makes. Only the standard effects count: the caller must handle a user effect." },
    Code { code: DiagCode::W0902, title: "library enables the GC", rule: "package", text: "Libraries may never require the GC tier. Only a binary may switch it on." },
    Code { code: DiagCode::W1001, title: "fip allocation", rule: "fip", text: "A `fip` function must reuse a freed cell of the same size for each constructor." },
    Code { code: DiagCode::W1002, title: "fip linearity", rule: "fip", text: "A `fip` function must use each owned value exactly once on every path." },
    Code { code: DiagCode::W1003, title: "fip call", rule: "fip", text: "A `fip` function can call only `fip` functions and constructors." },
    Code { code: DiagCode::W1004, title: "fip effects", rule: "fip", text: "A `fip` function has no effects." },
];

/// Finds a code, in upper or lower case.
pub fn lookup(code: &str) -> Option<&'static Code> {
    let code = DiagCode::parse(code)?;
    CODES.iter().find(|c| c.code == code)
}

#[cfg(test)]
mod tests {
    /// The text of W0704 names each part of a signature that a body always
    /// infers, so that a user knows what can still change.
    #[test]
    fn w0704_names_each_inferred_part() {
        let Some(code) = super::lookup("W0704") else {
            panic!("W0704 has no text");
        };
        let missing: Vec<&str> = weft_sema::infer::PARTS
            .iter()
            .copied()
            .filter(|p| !code.text.contains(&format!("`{p}`")))
            .collect();
        assert!(missing.is_empty(), "W0704 does not name {missing:?}");
    }

    /// A code whose rule names a relation, such as `error(R, P)`, names a
    /// violation relation of the spec. Each violation relation has a code.
    #[test]
    fn the_rules_of_the_codes_are_the_sinks_of_the_spec() {
        // Each word right before a `(` names a relation.
        let named: std::collections::BTreeSet<&str> = super::CODES
            .iter()
            .flat_map(|c| c.rule.split(')'))
            .filter_map(|part| part.split_once('('))
            .map(|(r, _)| r.trim_start_matches([',', ' ']))
            .collect();
        let sinks: std::collections::BTreeSet<&str> =
            crate::bridge::VIOLATION_RELATIONS.into_iter().collect();
        assert_eq!(named, sinks);
    }

    /// `weft explain W0901` says that only the standard effects need authority.
    #[test]
    fn w0901_says_that_only_standard_effects_need_authority() {
        let Some(code) = super::lookup("W0901") else {
            panic!("W0901 has no text");
        };
        assert!(
            code.text
                .contains("Only the standard effects count: the caller must handle a user effect."),
            "{}",
            code.text
        );
    }

    /// The table has one text for each code that a diagnostic can have, in
    /// the order of the codes. So a code with no text, or a text with no
    /// code, is a test failure, and a code that does not exist does not
    /// compile.
    #[test]
    fn each_code_has_one_text_in_order() {
        let codes: Vec<super::DiagCode> = super::CODES.iter().map(|c| c.code).collect();
        assert_eq!(codes, super::DiagCode::ALL);
        let texts: Vec<&str> = codes.iter().map(|c| c.as_str()).collect();
        let mut sorted = texts.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(texts, sorted);
        assert!(super::lookup("w0301").is_some());
        assert!(super::lookup("X").is_none());
        assert!(super::lookup(&format!("W{}", 9999)).is_none());
    }

    /// Collects the words `W` or `L` and four digits in the file `path`, or in
    /// the files under the directory `path`.
    fn scan(path: &std::path::Path, out: &mut std::collections::BTreeMap<String, String>) {
        if path.is_dir() {
            let Ok(entries) = std::fs::read_dir(path) else {
                return;
            };
            for e in entries.flatten() {
                let sub = e.path();
                // The design inputs are a record of past reviews. They can name
                // codes that do not exist, for example a test's unknown code.
                if sub
                    .file_name()
                    .is_some_and(|n| n != "target" && n != "core-ir-inputs")
                {
                    scan(&sub, out);
                }
            }
            return;
        }
        let Ok(text) = std::fs::read_to_string(path) else {
            return;
        };
        let b = text.as_bytes();
        for i in 0..b.len().saturating_sub(4) {
            let word_start = i == 0 || !b[i - 1].is_ascii_alphanumeric();
            let word_end = b.get(i + 5).is_none_or(|c| !c.is_ascii_alphanumeric());
            if word_start
                && word_end
                && matches!(b[i], b'W' | b'L')
                && b[i + 1..i + 5].iter().all(u8::is_ascii_digit)
            {
                out.entry(text[i..i + 5].to_string())
                    .or_insert_with(|| path.display().to_string());
            }
        }
    }

    /// Every code that the sources emit or the docs name has a text for
    /// `weft explain`. The tests of `crates/*/tests` may name unknown codes.
    #[test]
    fn every_code_in_the_sources_is_explained() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut found = std::collections::BTreeMap::new();
        let crates = std::fs::read_dir(root.join("crates")).into_iter().flatten();
        for c in crates.flatten() {
            scan(&c.path().join("src"), &mut found);
        }
        for dir in ["spec", "std", "docs", "tests/programs", "examples"] {
            scan(&root.join(dir), &mut found);
        }
        assert!(found.contains_key("W0301"), "the scan finds nothing");
        let missing: Vec<String> = found
            .iter()
            .filter(|(code, _)| super::lookup(code).is_none())
            .map(|(code, file)| format!("{code} (in {file})"))
            .collect();
        assert!(missing.is_empty(), "codes with no text: {missing:?}");
    }

    /// Each code of the table occurs in a test: a corpus program, a test file of
    /// a crate or a unit test module. So each code has a test that gives it.
    #[test]
    fn every_code_has_a_test() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut found = std::collections::BTreeMap::new();
        scan(&root.join("tests"), &mut found);
        let crates = std::fs::read_dir(root.join("crates")).into_iter().flatten();
        for c in crates.flatten() {
            scan(&c.path().join("tests"), &mut found);
            scan(&c.path().join("src/tests.rs"), &mut found);
            scan(&c.path().join("src/tests"), &mut found);
        }
        let missing: Vec<&str> = super::CODES
            .iter()
            .map(|c| c.code.as_str())
            .filter(|c| !found.contains_key(*c))
            .collect();
        assert!(missing.is_empty(), "codes with no test: {missing:?}");
    }
}
