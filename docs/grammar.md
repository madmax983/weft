# Weft surface grammar (Phase 1)

This grammar defines the syntax that the parser accepts. The AST is in
`crates/weft-syntax/src/ast.rs`.

## Lexical rules

- Comments start with `//` and end at the end of the line.
- Identifiers: `[A-Za-z_][A-Za-z0-9_]*`. Integers: `[0-9][0-9_]*`.
- `2.s` is the integer `2`, a dot, and the name `s`. A float needs a digit after the dot.
  Phase 1 has no floats.
- Strings use double quotes. Escapes: `\n`, `\t`, `\\`, `\"`, `\{`, `\}`.
  `{expr}` inside a string is an interpolation.
- Reserved keywords: `fn let if else while for in loop break continue return match struct
  enum effect impl mod pub extern true false self Self`.
- Contextual keywords: `handle`, `scope`, `linear`, `fip`, `multi`, `test`, `type`, `on`,
  `abort`, `mut`, `assert`, and the mode words. They are names in other positions.
  For example, `fn handle(req: Request)` declares a function named `handle`.

### Automatic statement ends

The lexer inserts a statement end (`NL`) at a line break when all of these are true:

1. The last token on the line is a name, a literal, `)`, `]`, `}`, `return`, `break`,
   `continue`, `true`, `false`, `self` or `Self`.
2. The line break is not inside `(...)` or `[...]`.
3. The next line does not start with `.` followed by a name (a method chain).

A `;` is also a statement end. The parser skips statement ends before `else`, before the
`in` of a `handle`, and before the `on` of `on abort`.

## Items

```
file        = item* EOF
item        = "pub"? ( fn | extern_fn | extern_type | struct | enum | effect | impl | mod | test )
fn          = "fip"? "fn" NAME generics? "(" params? ")" ( "->" type )? ( "/" row )? block
extern_fn   = "extern" "fn" NAME generics? "(" params? ")" ( "->" type )? ( "/" row )?
extern_type = "extern" "type" NAME generics? ( "{" prop ( "," prop )* ","? "}" )?
prop        = NAME ( ":" NAME )?
generics    = "<" NAME ( "," NAME )* ">"
params      = param ( "," param )* ","?
param       = NAME ( ":" type )?
struct      = "linear"? "struct" NAME generics? ( ":" "!" "Move" )?
              "{" ( field sep )* "}" ( "on" "abort" "=" NAME )?
field       = NAME ":" type
enum        = "enum" NAME generics? "{" ( variant sep )* "}"
variant     = NAME ( "(" type ( "," type )* ")" )?
effect      = "effect" NAME "{" ( op sep )* "}"
op          = "multi"? "fn" NAME "(" params? ")" ( "->" type )?
impl        = "impl" generics? type "{" item* "}"
mod         = "mod" NAME "{" item* "}"
test        = "test" STRING block
sep         = "," | NL
```

## Types, places and effect rows

```
type        = type_atom ( "@" MODE+ )?
type_atom   = "&" type_atom ( "in" place )?
            | "(" ( type ( "," type )* ","? )? ")"
            | "[" type ( ";" INT )? "]"
            | "fn" "(" ( type ( "," type )* )? ")" ( "->" type )? ( "/" fn_row )?
            | "Self"
            | NAME ( "." NAME )* ( "<" type ( "," type )* ">" )?
place       = ( NAME | "self" ) step*
step        = "." ( NAME | INT ) | "[" "]" | "[" ".." NAME "]" | "[" NAME ".." "]" | ".."
row         = row_item ( "," row_item )*
fn_row      = row_item | "(" row ")"
row_item    = "mut" "(" place ( "," place )* ")" | NAME
MODE        = uniq | aliased | portable | nonportable | uncontended | shared | once | many
```

Notes:

- The wildcard step `..` must be the last step: `mut(world..)`.
- In a function type, a row with more than one item needs parentheses:
  `fn(Request) -> Response / (net, log)`.

## Statements

```
block       = "{" ( stmt? end )* stmt? "}"
end         = NL | ";"
stmt        = "let" pattern ( ":" type )? ( "=" expr )?
            | "return" expr? | "break" | "continue"
            | "while" expr_ns block
            | "for" pattern "in" expr_ns block
            | "loop" block
            | "assert" expr
            | expr ( ( "=" | "+=" | "-=" | "*=" ) expr )?
pattern     = "_" | NAME | literal
            | "(" pattern ( "," pattern )* ")"
            | UNAME ( "." UNAME )? ( "(" pattern ( "," pattern )* ")" )?
```

`UNAME` is a name that starts with an uppercase letter. A lowercase name is a binding.

## Expressions

Precedence, from low to high:

| Level | Operators | Associativity |
| --- | --- | --- |
| 1 | `..` | none |
| 2 | `\|\|` | left |
| 3 | `&&` | left |
| 4 | `==` `!=` `<` `<=` `>` `>=` | none |
| 5 | `+` `-` | left |
| 6 | `*` `/` `%` | left |
| 7 | prefix `-` `!` `&` | prefix |
| 8 | `.name`, `.method(args)`, `(args)`, `[expr]`, `[]` | postfix |

```
primary     = literal | NAME | "(" expr ")" | "(" expr "," ( expr "," ? )* ")"
            | "[" ( expr ( "," expr )* )? "]"
            | UNAME ( "." UNAME )? "{" ( NAME ":" expr sep )* "}"      // struct literal
            | "|" params? "|" expr | "||" expr                           // closure
            | block
            | "if" expr_ns block ( "else" ( block | if ) )?
            | "match" expr_ns "{" ( pattern "=>" expr sep )* "}"
            | "handle" NAME "{" ( "fn" NAME "(" params? ")" block )* "}" "in" expr
            | "scope" "{" NAME "=>" stmts "}"
args        = arg ( "," arg )* ","?
arg         = ( NAME ":" )? expr
call_suffix = "(" args? ")" trailing?
trailing    = block           // same line as ")"; becomes a closure with no parameters
```

- `expr_ns` is an expression with no struct literal and no trailing block at its top level.
  This removes the ambiguity in `if x.ready() { ... }`.
- A struct literal needs `{` followed by `NAME :` or by `}`.
- `x[]` names every element of `x`. It is valid in `for e in x[]` and after `&`.

## Further rules

These rules complete the grammar above.

1. A line break after a `>` that closes type arguments, or after a wildcard `..`, also
   ends a statement or a list item.
2. `|| x += 1` is a closure whose body is a block with one assignment.
3. `(e)`, `(p)` and `(T)` are the item itself. `(e,)` is a one-item tuple. `()` is unit.
4. Trailing commas are allowed in every comma list. In braces (struct and enum bodies,
   effect operations, struct literals, match arms) a comma or a line break separates
   items. Handler clauses and items need no separator.
5. A raw line break in a string is an error. An unknown escape is an error. An empty
   interpolation `{}` is an error. A lone `}` is text.
6. `assert` starts an assert statement only when an expression follows. `mut` in an
   effect row means `mut(...)` only when `(` follows. `self` is a parameter name.
7. The parser skips `;` and line breaks before `else`, `in` and `on`.
8. In a method chain, the name after `.` must be on the same line as the `.`.
9. Comparison chains and range chains are errors. `&&x` is `&(&x)`. `>=` after type
   arguments splits into `>` and `=`.
10. Deep nesting (about 96 levels) is an error, not a stack overflow.

The pretty-printer (`weft_syntax::pretty`) prints a file that parses back to the same
tree.
