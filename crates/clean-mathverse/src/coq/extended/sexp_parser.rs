// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! S-expression parser for Coq SerAPI output.
//!
//! Parses the textual s-expression format produced by `sertop` / `sercomp`
//! into a tree of [`SexpValue`] nodes. Handles string literals with escape
//! sequences, semicolon line-comments, and arbitrarily nested parentheses.
//!
//! This parser is separate from [`crate::coq::alpha`] because the extended
//! importer operates on full SerAPI library dumps (`.sexp` files) rather than
//! individual term snippets.

use thiserror::Error;

/// A parsed s-expression value.
#[derive(Clone, Debug, PartialEq)]
pub enum SexpValue {
    /// An atomic token (identifier, number, or quoted string body).
    Atom(String),
    /// A parenthesised list of sub-expressions.
    List(Vec<SexpValue>),
}

impl SexpValue {
    /// Return the atom string, or `None` if this is a list.
    #[must_use]
    pub fn as_atom(&self) -> Option<&str> {
        match self {
            SexpValue::Atom(s) => Some(s),
            SexpValue::List(_) => None,
        }
    }

    /// Return the list children, or `None` if this is an atom.
    #[must_use]
    pub fn as_list(&self) -> Option<&[SexpValue]> {
        match self {
            SexpValue::List(v) => Some(v),
            SexpValue::Atom(_) => None,
        }
    }

    /// Return `true` if this is an atom equal to `name`.
    #[must_use]
    pub fn is_atom(&self, name: &str) -> bool {
        matches!(self, SexpValue::Atom(s) if s == name)
    }

    /// Return the first child of a list, if present.
    #[must_use]
    pub fn head(&self) -> Option<&SexpValue> {
        self.as_list().and_then(|v| v.first())
    }

    /// Return true if this is a list whose first child is `Atom(tag)`.
    #[must_use]
    pub fn is_tagged(&self, tag: &str) -> bool {
        self.head().is_some_and(|h| h.is_atom(tag))
    }
}

/// Errors from s-expression parsing.
#[derive(Debug, Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum SexpParseError {
    #[error("unexpected end of input")]
    UnexpectedEof,

    #[error("unexpected character '{ch}' at byte offset {offset}")]
    UnexpectedChar { ch: char, offset: usize },

    #[error("unmatched opening parenthesis at byte offset {offset}")]
    UnmatchedParen { offset: usize },

    #[error("unterminated string literal starting at byte offset {offset}")]
    UnterminatedString { offset: usize },
}

/// Parse a single s-expression from `input`.
///
/// Leading whitespace is skipped. Trailing content after the first complete
/// s-expression is ignored — use [`parse_sexp_stream`] to consume all
/// top-level forms.
pub fn parse_sexp(input: &str) -> Result<SexpValue, SexpParseError> {
    let tokens = tokenize(input)?;
    let mut pos = 0;
    if tokens.is_empty() {
        return Err(SexpParseError::UnexpectedEof);
    }
    parse_one(&tokens, &mut pos)
}

/// Parse zero or more top-level s-expressions from `input`.
pub fn parse_sexp_stream(input: &str) -> Result<Vec<SexpValue>, SexpParseError> {
    let tokens = tokenize(input)?;
    let mut pos = 0;
    let mut out = Vec::new();
    while pos < tokens.len() {
        out.push(parse_one(&tokens, &mut pos)?);
    }
    Ok(out)
}

// ---- Internal tokenizer ----------------------------------------------------

#[derive(Clone, Debug)]
enum Token {
    Open(usize),
    Close(usize),
    Atom(String),
}

fn tokenize(input: &str) -> Result<Vec<Token>, SexpParseError> {
    let b = input.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;

    while i < b.len() {
        match b[i] {
            b' ' | b'\t' | b'\n' | b'\r' => {
                i += 1;
            }
            b'(' => {
                tokens.push(Token::Open(i));
                i += 1;
            }
            b')' => {
                tokens.push(Token::Close(i));
                i += 1;
            }
            b'"' => {
                let start = i;
                i += 1;
                let mut s = String::new();
                while i < b.len() && b[i] != b'"' {
                    if b[i] == b'\\' && i + 1 < b.len() {
                        i += 1;
                        match b[i] {
                            b'n' => s.push('\n'),
                            b't' => s.push('\t'),
                            b'\\' => s.push('\\'),
                            b'"' => s.push('"'),
                            b'r' => s.push('\r'),
                            b'0' => s.push('\0'),
                            other => {
                                s.push('\\');
                                s.push(other as char);
                            }
                        }
                    } else {
                        s.push(b[i] as char);
                    }
                    i += 1;
                }
                if i >= b.len() {
                    return Err(SexpParseError::UnterminatedString { offset: start });
                }
                i += 1; // skip closing quote
                tokens.push(Token::Atom(s));
            }
            b';' => {
                // Line comment: skip to end of line.
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
            }
            _ => {
                let mut s = String::new();
                while i < b.len()
                    && !matches!(
                        b[i],
                        b' ' | b'\t' | b'\n' | b'\r' | b'(' | b')' | b'"' | b';'
                    )
                {
                    s.push(b[i] as char);
                    i += 1;
                }
                tokens.push(Token::Atom(s));
            }
        }
    }

    Ok(tokens)
}

fn parse_one(tokens: &[Token], pos: &mut usize) -> Result<SexpValue, SexpParseError> {
    if *pos >= tokens.len() {
        return Err(SexpParseError::UnexpectedEof);
    }

    match &tokens[*pos] {
        Token::Open(off) => {
            let open_off = *off;
            *pos += 1;
            let mut children = Vec::new();
            loop {
                if *pos >= tokens.len() {
                    return Err(SexpParseError::UnmatchedParen { offset: open_off });
                }
                if matches!(tokens[*pos], Token::Close(_)) {
                    *pos += 1;
                    return Ok(SexpValue::List(children));
                }
                children.push(parse_one(tokens, pos)?);
            }
        }
        Token::Close(off) => Err(SexpParseError::UnexpectedChar {
            ch: ')',
            offset: *off,
        }),
        Token::Atom(s) => {
            *pos += 1;
            Ok(SexpValue::Atom(s.clone()))
        }
    }
}

// ---- Tests -----------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_sexp_atom() {
        let v = parse_sexp("hello").expect("should parse atom");
        assert_eq!(v, SexpValue::Atom("hello".into()));
    }

    #[test]
    fn test_parse_sexp_empty_list() {
        let v = parse_sexp("()").expect("should parse empty list");
        assert_eq!(v, SexpValue::List(vec![]));
    }

    #[test]
    fn test_parse_sexp_nested() {
        let v = parse_sexp("(a (b c) d)").expect("should parse nested");
        let items = v.as_list().expect("root is list");
        assert_eq!(items.len(), 3);
        assert!(items[0].is_atom("a"));
        assert!(items[1].is_tagged("b"));
        assert!(items[2].is_atom("d"));
    }

    #[test]
    fn test_parse_sexp_string_literal() {
        let v = parse_sexp(r#""hello \"world\"""#).expect("should parse string");
        assert_eq!(v, SexpValue::Atom("hello \"world\"".into()));
    }

    #[test]
    fn test_parse_sexp_escape_sequences() {
        let v = parse_sexp(r#""a\nb\tc\\d""#).expect("should parse escapes");
        assert_eq!(v, SexpValue::Atom("a\nb\tc\\d".into()));
    }

    #[test]
    fn test_parse_sexp_stream_multiple() {
        let vals = parse_sexp_stream("(a b) (c d) atom").expect("should parse stream");
        assert_eq!(vals.len(), 3);
        assert!(vals[0].is_tagged("a"));
        assert!(vals[1].is_tagged("c"));
        assert!(vals[2].is_atom("atom"));
    }

    #[test]
    fn test_parse_sexp_stream_empty() {
        let vals = parse_sexp_stream("").expect("empty is ok");
        assert!(vals.is_empty());
    }

    #[test]
    fn test_parse_sexp_line_comment() {
        let v = parse_sexp("; this is a comment\n(hello)").expect("should skip comment");
        assert!(v.is_tagged("hello"));
    }

    #[test]
    fn test_parse_sexp_error_unmatched() {
        let err = parse_sexp("(a b").unwrap_err();
        assert!(matches!(err, SexpParseError::UnmatchedParen { .. }));
    }

    #[test]
    fn test_parse_sexp_error_unexpected_close() {
        let err = parse_sexp(")").unwrap_err();
        assert!(matches!(
            err,
            SexpParseError::UnexpectedChar { ch: ')', .. }
        ));
    }

    #[test]
    fn test_parse_sexp_error_eof() {
        let err = parse_sexp("   ").unwrap_err();
        assert!(matches!(err, SexpParseError::UnexpectedEof));
    }

    #[test]
    fn test_parse_sexp_error_unterminated_string() {
        let err = parse_sexp("\"hello").unwrap_err();
        assert!(matches!(err, SexpParseError::UnterminatedString { .. }));
    }

    #[test]
    fn test_sexp_value_helpers() {
        let atom = SexpValue::Atom("x".into());
        assert_eq!(atom.as_atom(), Some("x"));
        assert!(atom.as_list().is_none());

        let list = SexpValue::List(vec![
            SexpValue::Atom("tag".into()),
            SexpValue::Atom("val".into()),
        ]);
        assert!(list.as_atom().is_none());
        assert_eq!(list.as_list().map(|v| v.len()), Some(2));
        assert!(list.is_tagged("tag"));
        assert!(!list.is_tagged("other"));
    }

    #[test]
    fn test_parse_sexp_deeply_nested() {
        let v = parse_sexp("(((a)))").expect("should parse deep nesting");
        let inner = v.as_list().expect("l1")[0].as_list().expect("l2")[0]
            .as_list()
            .expect("l3");
        assert!(inner[0].is_atom("a"));
    }

    #[test]
    fn test_parse_sexp_whitespace_variants() {
        let v = parse_sexp("( a\tb\n c\r\n)").expect("should handle all whitespace");
        let items = v.as_list().expect("list");
        assert_eq!(items.len(), 3);
    }

    #[test]
    fn test_parse_sexp_serapi_style() {
        // A simplified SerAPI-style declaration output
        let input = r#"(CoqConstr (Prod "n" (Ind "Coq.Init.Datatypes.nat" 0) (App (Const "Coq.Init.Peano.eq") ((Ind "Coq.Init.Datatypes.nat" 0) (App (Const "Coq.Init.Nat.add") ((Rel 1) (Const "Coq.Init.Datatypes.O"))) (Rel 1)))))"#;
        let v = parse_sexp(input).expect("should parse serapi output");
        assert!(v.is_tagged("CoqConstr"));
    }
}
