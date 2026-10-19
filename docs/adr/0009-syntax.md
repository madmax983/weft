# ADR 0009: Surface syntax decisions

Status: accepted. Date: 2026-10-18.

## Decision

- No semicolons. The lexer inserts statement ends, Go style (docs/grammar.md).
- A trailing block after `)` on the same line is a closure argument:
  `with_timeout(2.s) { ... }`.
- No struct literal and no trailing block in `if`, `while`, `for` and `match` heads.
- `handle`, `scope` and the mode words are contextual keywords.
- A `return` in a closure returns from the closure. Its value has the result type of
  the closure, not of the function. `break` and `continue` in a closure go only to a
  loop of the closure (W0111). No jump (`return`, `break`, `continue`) can leave a
  handled body, a handler clause or a scope body (W0315): the interpreter runs each of
  them as separate code, and the handler or the scope must end first.
- A `loop` that no `break` leaves does not end normally. As the last statement of a
  body it has the type `!`, so `fn f(xs: T) -> T { loop { return xs } }` is correct.
- A function type with more than one effect needs parentheses: `fn() / (net, log)`.
- `*T` is a raw pointer for foreign functions. A written `*T` is valid only in an
  `extern fn` signature, in a local and in a closure parameter (W0116). The check looks
  only at written types. A type argument can still hold a raw pointer (`Option<*Stmt>`,
  or `T` of a generic function); generic instantiation is not restricted. It is an
  opaque copy value with no place: no fields, no elements and no deref. It is
  nonportable, because the checker cannot know if the foreign object allows other
  threads. A container of a raw pointer is nonportable too, so a `fork` that captures
  one gets W0401. A generic function that forks with its argument is a known gap: there
  is no mode polymorphism yet, so the same holds for `Rc`.
- Nesting deeper than 96 levels, or a chain of more than about 150 prefix operators,
  postfix steps or `else if` branches, is a parser error. The parser, the printer,
  sema, the checker, the spec and the interpreter must run on a 2 MiB thread for every
  program that parses (`crates/weft-cli/tests/limits.rs`). The derivation printer of
  `check --explain` is not covered yet: it recurses once for each derivation step.
- A chain of binary operators has no limit. The parser keeps each part of 32 operators
  in a hidden local of a block. The value, the order of evaluation and the
  short-circuit of `&&` and `||` do not change. The pretty-printer prints the chain.
