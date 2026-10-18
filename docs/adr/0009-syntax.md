# ADR 0009: Surface syntax decisions

Status: accepted. Date: 2026-10-18.

## Decision

- No semicolons. The lexer inserts statement ends, Go style (docs/grammar.md).
- A trailing block after `)` on the same line is a closure argument:
  `with_timeout(2.s) { ... }`.
- No struct literal and no trailing block in `if`, `while`, `for` and `match` heads.
- `handle`, `scope` and the mode words are contextual keywords.
- A function type with more than one effect needs parentheses: `fn() / (net, log)`.
- `*T` is a raw pointer for foreign functions. It is valid only in an `extern fn`
  signature and in a local (W0116). It is an opaque copy value with no place: no fields,
  no elements and no deref. It is nonportable, because the checker cannot know if the
  foreign object allows other threads.
- Nesting deeper than 96 levels, or a chain of more than about 150 prefix operators,
  postfix steps or `else if` branches, is a parser error. The whole pipeline must run on
  a 2 MiB thread for every program that parses (`crates/weft-cli/tests/limits.rs`).
- A chain of binary operators has no limit. The parser keeps each part of 32 operators
  in a hidden local of a block. The value, the order of evaluation and the
  short-circuit of `&&` and `||` do not change. The pretty-printer prints the chain.
