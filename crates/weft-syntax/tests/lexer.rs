//! Lexer tests: tokens, spans, strings and automatic statement ends.

#![allow(clippy::unwrap_used)]

use weft_syntax::ast::Span;
use weft_syntax::lexer::{escape_text, lex, lex_at, StrPiece, Token, TokenKind};

fn toks(src: &str) -> Vec<Token> {
    lex(src).unwrap_or_else(|e| panic!("lex failed: {} at {:?}", e.message, e.span))
}

/// Shows the token stream as text, one word per token.
fn show(src: &str) -> String {
    toks(src)
        .iter()
        .map(|t| t.kind.to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

fn lex_err(src: &str) -> (String, Span) {
    match lex(src) {
        Ok(t) => panic!("expected a lex error for {src:?}, got {t:?}"),
        Err(e) => (e.message, e.span),
    }
}

#[test]
fn keywords_and_punctuation() {
    let kws = "fn let if else while for in loop break continue return match struct enum effect \
               impl mod pub extern true false self Self";
    assert_eq!(show(kws), format!("{kws} EOF"));
    let punct = "( ) [ ] { } , ; : . .. -> => = == != < <= > >= + - * / % ! & && | || += -= *= @";
    assert_eq!(show(punct), format!("{punct} EOF"));
    assert_eq!(show("a->b=>c"), "a -> b => c EOF");
    assert_eq!(show("x...y"), "x .. . y EOF");
}

#[test]
fn keywords_have_their_own_kinds() {
    let t = toks("fn self Self true");
    assert_eq!(t[0].kind, TokenKind::Fn);
    assert_eq!(t[1].kind, TokenKind::SelfValue);
    assert_eq!(t[2].kind, TokenKind::SelfType);
    assert_eq!(t[3].kind, TokenKind::True);
}

#[test]
fn contextual_keywords_are_names() {
    let words = [
        "handle",
        "scope",
        "linear",
        "fip",
        "multi",
        "test",
        "type",
        "on",
        "abort",
        "mut",
        "assert",
        "uniq",
        "aliased",
        "portable",
        "nonportable",
        "uncontended",
        "shared",
        "once",
        "many",
        "_",
        "_x",
        "sqlite3_step",
    ];
    for w in words {
        let t = toks(w);
        assert_eq!(t[0].kind, TokenKind::Name(w.into()), "{w}");
    }
}

#[test]
fn integers() {
    let t = toks("0 42 1_000_000 18446744073709551615");
    assert_eq!(t[0].kind, TokenKind::Int(0));
    assert_eq!(t[1].kind, TokenKind::Int(42));
    assert_eq!(t[2].kind, TokenKind::Int(1_000_000));
    assert_eq!(t[3].kind, TokenKind::Int(u64::MAX));
    let (msg, span) = lex_err("x = 18446744073709551616");
    assert!(msg.contains("too large"), "{msg}");
    assert_eq!(span, Span::new(4, 24));
}

#[test]
fn int_dot_name_is_three_tokens() {
    let t = toks("2.s");
    assert_eq!(t[0].kind, TokenKind::Int(2));
    assert_eq!(t[1].kind, TokenKind::Dot);
    assert_eq!(t[2].kind, TokenKind::Name("s".into()));
    assert_eq!(show("1..10"), "1 .. 10 EOF");
    assert_eq!(show("t.0.1"), "t . 0 . 1 EOF");
}

#[test]
fn spans_are_byte_offsets() {
    let t = toks("ab  cd\n(e)");
    assert_eq!(t[0].span, Span::new(0, 2));
    assert_eq!(t[1].span, Span::new(4, 6));
    assert_eq!(t[2].kind, TokenKind::Newline);
    assert_eq!(t[2].span, Span::new(6, 7));
    assert_eq!(t[3].span, Span::new(7, 8));
    assert_eq!(t.last().unwrap().kind, TokenKind::Eof);
    assert_eq!(t.last().unwrap().span, Span::new(10, 10));
}

#[test]
fn lex_at_adds_the_base_offset() {
    let t = lex_at("x + 1", 100).unwrap();
    assert_eq!(t[0].span, Span::new(100, 101));
    assert_eq!(t[2].span, Span::new(104, 105));
    assert_eq!(t[3].span, Span::new(105, 105));
    let e = lex_at("x", u32::MAX).unwrap_err();
    assert_eq!(e.message, "the source text is too large");
}

#[test]
fn starts_line_marks_tokens_after_a_line_break() {
    let t = toks("a b\n  c");
    assert!(!t[0].starts_line);
    assert!(!t[1].starts_line);
    assert!(t[3].starts_line, "{t:?}");
}

#[test]
fn comments_are_skipped() {
    assert_eq!(show("a // comment\nb"), "a NL b EOF");
    assert_eq!(show("// only a comment"), "EOF");
    assert_eq!(show("a / b // c / d"), "a / b EOF");
    assert_eq!(show("x // é ünïcode\ny"), "x NL y EOF");
}

#[test]
fn newline_span_is_the_line_break() {
    let t = toks("a // c\nb");
    assert_eq!(t[1].kind, TokenKind::Newline);
    assert_eq!(t[1].span, Span::new(6, 7));
}

#[test]
fn rule1_tokens_that_end_a_statement() {
    let ends = [
        "x", "42", "\"s\"", ")", "]", "}", "return", "break", "continue", "true", "false", "self",
        "Self",
    ];
    for end in ends {
        let src = format!("{end}\ny");
        let t = toks(&src);
        let nl = t.iter().any(|t| t.kind == TokenKind::Newline);
        assert!(nl, "no NL after {end:?}: {t:?}");
    }
}

#[test]
fn rule1_other_tokens_do_not_end_a_statement() {
    let others = [
        "+", "-", "*", "==", "&&", "||", ",", "=", "{", "(", "[", "->", "=>", ":", ".", "..", "<",
        ">", "@", "&", "|", "!", "fn", "let", "in", "else",
    ];
    for op in others {
        let src = format!("{op}\ny");
        let t = toks(&src);
        assert!(
            t.iter().all(|t| t.kind != TokenKind::Newline),
            "NL after {op:?}: {t:?}"
        );
    }
}

#[test]
fn rule2_no_newline_inside_parens_or_brackets() {
    assert_eq!(show("f(a,\nb\n)"), "f ( a , b ) EOF");
    assert_eq!(show("[1\n,2]\n"), "[ 1 , 2 ] NL EOF");
    assert_eq!(show("((a)\n)"), "( ( a ) ) EOF");
}

#[test]
fn rule2_braces_inside_parens_get_newlines() {
    assert_eq!(show("f(|| {\na\nb\n})"), "f ( || { a NL b NL } ) EOF");
    assert_eq!(show("{\na\n}\nb"), "{ a NL } NL b EOF");
    // After the `}` closes, the innermost bracket is `(` again.
    assert_eq!(show("f({\na\n}\n)"), "f ( { a NL } ) EOF");
}

#[test]
fn rule2_unbalanced_closers_do_not_break_the_lexer() {
    assert_eq!(show(")\na"), ") NL a EOF");
    assert_eq!(show("]]}\na"), "] ] } NL a EOF");
}

#[test]
fn rule3_method_chain_continues() {
    assert_eq!(
        show("world\n    .entities\n    .clear()"),
        "world . entities . clear ( ) EOF"
    );
    assert_eq!(show("a\n// note\n.b"), "a . b EOF");
}

#[test]
fn rule3_only_for_dot_and_name() {
    assert_eq!(show("a\n..b"), "a NL .. b EOF");
    assert_eq!(show("a\n.0"), "a NL . 0 EOF");
    assert_eq!(show("a\n.\nb"), "a NL . b EOF");
}

#[test]
fn newline_before_eof() {
    assert_eq!(show("a\n"), "a NL EOF");
    assert_eq!(show("a\n\n\n"), "a NL EOF");
    assert_eq!(show(""), "EOF");
}

#[test]
fn semicolons() {
    assert_eq!(show("a; b"), "a ; b EOF");
}

#[test]
fn plain_strings() {
    let t = toks(r#""hi there""#);
    assert_eq!(
        t[0].kind,
        TokenKind::Str(vec![StrPiece::Text("hi there".into())])
    );
    assert_eq!(t[0].span, Span::new(0, 10));
    assert_eq!(toks(r#""""#)[0].kind, TokenKind::Str(vec![]));
    assert_eq!(
        toks("\"é ü\"")[0].kind,
        TokenKind::Str(vec![StrPiece::Text("é ü".into())])
    );
}

#[test]
fn string_escapes() {
    let t = toks(r#""a\n\t\\\"\{\}b""#);
    assert_eq!(
        t[0].kind,
        TokenKind::Str(vec![StrPiece::Text("a\n\t\\\"{}b".into())])
    );
    assert_eq!(escape_text("a\n\t\\\"{}b"), r#"a\n\t\\\"\{\}b"#);
}

#[test]
fn string_lone_close_brace_is_text() {
    let t = toks(r#""a } b""#);
    assert_eq!(
        t[0].kind,
        TokenKind::Str(vec![StrPiece::Text("a } b".into())])
    );
}

#[test]
fn string_interpolation_pieces() {
    let src = r#""x {a.b} y""#;
    let t = toks(src);
    assert_eq!(
        t[0].kind,
        TokenKind::Str(vec![
            StrPiece::Text("x ".into()),
            StrPiece::Interp {
                src: "a.b".into(),
                offset: 4
            },
            StrPiece::Text(" y".into()),
        ])
    );
}

#[test]
fn string_interpolation_with_base_and_unicode() {
    let t = lex_at("\"é{x}\"", 10).unwrap();
    assert_eq!(
        t[0].kind,
        TokenKind::Str(vec![
            StrPiece::Text("é".into()),
            StrPiece::Interp {
                src: "x".into(),
                offset: 14
            },
        ])
    );
}

#[test]
fn string_interpolation_nesting() {
    let t = toks(r#""{f({a})}""#);
    assert_eq!(
        t[0].kind,
        TokenKind::Str(vec![StrPiece::Interp {
            src: "f({a})".into(),
            offset: 2
        }])
    );
    let t = toks(r#""{g("}", "{h}")} end""#);
    assert_eq!(
        t[0].kind,
        TokenKind::Str(vec![
            StrPiece::Interp {
                src: r#"g("}", "{h}")"#.into(),
                offset: 2
            },
            StrPiece::Text(" end".into()),
        ])
    );
    let t = toks(r#""{f("\"{x}")}""#);
    assert_eq!(
        t[0].kind,
        TokenKind::Str(vec![StrPiece::Interp {
            src: r#"f("\"{x}")"#.into(),
            offset: 2
        }])
    );
    assert_eq!(t.len(), 2);
}

#[test]
fn string_errors() {
    let (msg, span) = lex_err("x = \"abc");
    assert!(msg.contains("not closed"), "{msg}");
    assert_eq!(span, Span::new(4, 8));
    let (msg, _) = lex_err("\"abc\ndef\"");
    assert!(msg.contains("not closed"), "{msg}");
    let (msg, span) = lex_err(r#""a\qb""#);
    assert!(msg.contains("unknown escape `\\q`"), "{msg}");
    assert_eq!(span, Span::new(2, 4));
    let (msg, span) = lex_err("\"\\é\"");
    assert!(msg.contains("unknown escape"), "{msg}");
    assert_eq!(span, Span::new(1, 4));
    let (msg, _) = lex_err("\"abc\\");
    assert!(msg.contains("not closed"), "{msg}");
    let (msg, span) = lex_err(r#""a {b"#);
    assert!(msg.contains("interpolation"), "{msg}");
    assert_eq!(span.lo, 3);
    let (msg, _) = lex_err("\"{a\n}\"");
    assert!(msg.contains("interpolation"), "{msg}");
    let (msg, _) = lex_err(r#""{"abc}""#);
    assert!(msg.contains("interpolation"), "{msg}");
    let (msg, _) = lex_err("\"{\"a\\");
    assert!(msg.contains("interpolation"), "{msg}");
    let (msg, _) = lex_err("\"{\"a\\\n\"}\"");
    assert!(msg.contains("interpolation"), "{msg}");
}

#[test]
fn unexpected_characters() {
    let (msg, span) = lex_err("a # b");
    assert_eq!(msg, "unexpected character `#`");
    assert_eq!(span, Span::new(2, 3));
    let (msg, span) = lex_err("a é");
    assert_eq!(msg, "unexpected character `é`");
    assert_eq!(span, Span::new(2, 4));
    let (msg, _) = lex_err("a\u{0}");
    assert!(msg.starts_with("unexpected character"), "{msg}");
}

#[test]
fn token_descriptions() {
    assert_eq!(TokenKind::Name("x".into()).describe(), "`x`");
    assert_eq!(TokenKind::Int(7).describe(), "`7`");
    assert_eq!(TokenKind::Str(vec![]).describe(), "a string");
    assert_eq!(TokenKind::Newline.describe(), "end of line");
    assert_eq!(TokenKind::Eof.describe(), "end of file");
    assert_eq!(TokenKind::LBrace.describe(), "`{`");
    assert_eq!(TokenKind::Fn.describe(), "`fn`");
    assert_eq!(TokenKind::Name("x".into()).fixed_text(), None);
}

#[test]
fn string_display_shows_source_form() {
    let t = toks(r#""a\"{x}\n""#);
    assert_eq!(t[0].kind.to_string(), r#""a\"{x}\n""#);
}
