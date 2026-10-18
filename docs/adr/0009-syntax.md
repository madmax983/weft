# ADR 0009: Surface syntax decisions

Status: accepted. Date: 2026-10-18.

## Decision

- No semicolons. The lexer inserts statement ends, Go style (docs/grammar.md).
- A trailing block after `)` on the same line is a closure argument:
  `with_timeout(2.s) { ... }`.
- No struct literal and no trailing block in `if`, `while`, `for` and `match` heads.
- `handle`, `scope` and the mode words are contextual keywords.
- A function type with more than one effect needs parentheses: `fn() / (net, log)`.
