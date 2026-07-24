// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tiny s-expression parser for the `mathverse_try` DSL.
//!
//! Grammar is the minimum viable for `Const + App` proof terms (the
//! Tier A pattern). Binders live behind the `json:` escape hatch.
//! See the crate docs at `main.rs` for the full surface.

use clean_kernel::level::Level;
use clean_kernel::{Expr, ExprKind, Name};

/// Parse the MVP DSL into an [`Expr`].
pub(super) fn parse_expr(src: &str) -> Result<Expr, String> {
    let src = src.trim();
    if let Some(rest) = src.strip_prefix("json:") {
        let kind: ExprKind =
            serde_json::from_str(rest.trim()).map_err(|e| format!("json parse failed: {e}"))?;
        return Ok(Expr::from_kind(kind));
    }
    let tokens = tokenize(src);
    let mut it = tokens.into_iter().peekable();
    let expr = parse_one(&mut it)?;
    if it.peek().is_some() {
        return Err("trailing tokens after expression".to_string());
    }
    Ok(expr)
}

#[derive(Debug, PartialEq, Eq)]
enum Tok {
    LParen,
    RParen,
    Ident(String),
}

fn tokenize(src: &str) -> Vec<Tok> {
    let mut out = Vec::new();
    let mut buf = String::new();
    for c in src.chars() {
        match c {
            '(' => {
                flush_ident(&mut buf, &mut out);
                out.push(Tok::LParen);
            }
            ')' => {
                flush_ident(&mut buf, &mut out);
                out.push(Tok::RParen);
            }
            c if c.is_whitespace() => flush_ident(&mut buf, &mut out),
            c => buf.push(c),
        }
    }
    flush_ident(&mut buf, &mut out);
    out
}

fn flush_ident(buf: &mut String, out: &mut Vec<Tok>) {
    if !buf.is_empty() {
        out.push(Tok::Ident(std::mem::take(buf)));
    }
}

fn parse_one<I: Iterator<Item = Tok>>(it: &mut std::iter::Peekable<I>) -> Result<Expr, String> {
    match it
        .next()
        .ok_or_else(|| "unexpected end of input".to_string())?
    {
        Tok::RParen => Err("unexpected ')'".to_string()),
        Tok::LParen => parse_list(it),
        Tok::Ident(s) => parse_ident(&s),
    }
}

fn parse_list<I: Iterator<Item = Tok>>(it: &mut std::iter::Peekable<I>) -> Result<Expr, String> {
    let head = parse_one(it)?;
    let mut args = Vec::new();
    loop {
        match it.peek() {
            Some(Tok::RParen) => {
                it.next();
                break;
            }
            Some(_) => args.push(parse_one(it)?),
            None => return Err("unterminated '(...)'".to_string()),
        }
    }
    if args.is_empty() {
        // `(f)` — single-element list is just the head, matching Lean 4's
        // habit of unary parens around identifiers.
        Ok(head)
    } else {
        Ok(Expr::apps(head, args))
    }
}

fn parse_ident(s: &str) -> Result<Expr, String> {
    match s {
        "Prop" => return Ok(Expr::sort(Level::zero())),
        "Type" => return Ok(Expr::sort(Level::succ(Level::zero()))),
        _ => {}
    }
    // `^N` suffix → N levels (each `Level::succ` of zero). N=0 matches
    // bare identifier. Multiple distinct levels require `json:`.
    let (name, levels) = split_universe_suffix(s)?;
    if name.is_empty() {
        return Err(format!("empty identifier in `{s}`"));
    }
    Ok(Expr::const_(Name::from_string(&name), levels))
}

fn split_universe_suffix(s: &str) -> Result<(String, Vec<Level>), String> {
    if let Some(caret_idx) = s.find('^') {
        let (name_part, count_part) = s.split_at(caret_idx);
        let count_str = &count_part[1..];
        let count: u32 = count_str
            .parse()
            .map_err(|_| format!("bad universe count in `{s}` — expected `name^N`"))?;
        let levels = (0..count).map(|_| Level::succ(Level::zero())).collect();
        Ok((name_part.to_string(), levels))
    } else {
        Ok((s.to_string(), Vec::new()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_bare_identifier_is_const() {
        let e = parse_expr("Rat.zero").expect("should parse bare ident");
        match e.kind() {
            ExprKind::Const(name, levels) => {
                assert_eq!(name.to_string(), "Rat.zero");
                assert!(levels.is_empty());
            }
            other => panic!("expected Const, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_universe_suffix_adds_one_succ() {
        let e = parse_expr("Eq^1").expect("should parse Eq^1");
        match e.kind() {
            ExprKind::Const(name, levels) => {
                assert_eq!(name.to_string(), "Eq");
                assert_eq!(levels.len(), 1);
            }
            other => panic!("expected Const with 1 level, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_application_nested_left_assoc() {
        let e = parse_expr("(f x y)").expect("should parse application");
        // (f x y) == App(App(f, x), y)
        match e.kind() {
            ExprKind::App(outer_f, y) => {
                assert!(matches!(y.kind(), ExprKind::Const(_, _)));
                match outer_f.kind() {
                    ExprKind::App(_, _) => {}
                    other => panic!("expected nested App, got {other:?}"),
                }
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_unary_parens_is_identity() {
        let a = parse_expr("Foo").unwrap();
        let b = parse_expr("(Foo)").unwrap();
        assert_eq!(a.kind(), b.kind());
    }

    #[test]
    fn test_parse_missing_rparen_errors() {
        let err = parse_expr("(f x").unwrap_err();
        assert!(err.contains("unterminated"), "got: {err}");
    }

    #[test]
    fn test_parse_sorts() {
        let prop = parse_expr("Prop").unwrap();
        assert!(matches!(prop.kind(), ExprKind::Sort(_)));
        let ty = parse_expr("Type").unwrap();
        assert!(matches!(ty.kind(), ExprKind::Sort(_)));
    }
}
