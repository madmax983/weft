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
- An argument of a call or of an effect operation can name its parameter
  (`put(b: 1, a: v)`). A named argument binds by name, the others fill the free
  parameters in order, and a trailing block goes to the last free parameter. The
  arguments run in the order of the parameters. W0103 is for a name given twice or a
  wrong count. `s.spawn` takes one closure with no parameters, and `fork` takes at
  least two (W0102, W0103).
- One rule for named arguments holds in sema and in the interpreter (review round 2,
  RR10 and RR13). A named argument binds by name where the callee has names: a
  function, a method (also of a value receiver), an operation, a function item in a
  local, and a struct constructor (`Range(hi: 10, lo: 2)` gives the field `hi`). An
  unknown name is W0104. A callee with no names takes no named argument (W0104): a
  closure, a function parameter, a join of function values, a variant, `resume`,
  `print`, `fork` and `s.spawn`. The interpreter does not know the callee of a method
  of a value or of an item in a local when it compiles the call, so sema gives it the
  order of the arguments (`FnFacts::arg_order`).
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
  program that parses (`crates/weft-cli/tests/limits.rs`).
- A chain of binary operators has no limit. The parser keeps each part of 32 operators
  in a hidden local of a block. The value, the order of evaluation and the
  short-circuit of `&&` and `||` do not change. The pretty-printer prints the chain.
