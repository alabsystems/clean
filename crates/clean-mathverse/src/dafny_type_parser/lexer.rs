// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dafny type-expression lexer — the token layer under
//! [`super::parse_dafny_type`].
//!
//! The lexer is where the parser's "refuse what we cannot model faithfully"
//! fence actually lives: only the characters that make up the modelled type
//! grammar (`(`, `)`, `<`, `>`, `,`, `->`, identifiers) produce tokens, and
//! ANY other character — a refinement bar `|`, a partial/total arrow variant
//! `-->` / `~>`, a `?`, a bit-vector width digit glued to a name — aborts the
//! whole lex with `None`, so the importer skips the declaration rather than
//! emitting a placeholder. Keeping that rejection rule in one file makes the
//! fence auditable independently of the recursive-descent parser.

/// A Dafny type-expression token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Tok {
    Ident(String),
    LParen,
    RParen,
    LAngle,
    RAngle,
    Comma,
    /// `->` total function arrow.
    Arrow,
}

/// Tokenise a Dafny type expression, or `None` if it contains any construct
/// outside the modelled grammar.
pub(super) fn lex(src: &str) -> Option<Vec<Tok>> {
    let chars: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < chars.len() {
        let ch = chars[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }
        match ch {
            '(' => {
                out.push(Tok::LParen);
                i += 1;
            }
            ')' => {
                out.push(Tok::RParen);
                i += 1;
            }
            '<' => {
                out.push(Tok::LAngle);
                i += 1;
            }
            '>' => {
                out.push(Tok::RAngle);
                i += 1;
            }
            ',' => {
                out.push(Tok::Comma);
                i += 1;
            }
            '-' if chars.get(i + 1) == Some(&'>') => {
                out.push(Tok::Arrow);
                i += 2;
            }
            _ if is_ident_start(ch) => {
                let start = i;
                i += 1;
                while i < chars.len() && is_ident_continue(chars[i]) {
                    i += 1;
                }
                out.push(Tok::Ident(chars[start..i].iter().collect()));
            }
            // Any other character (refinement `|`, partial arrows, `?`,
            // bit-vector width digits glued to a name, …) is something
            // we do not faithfully model — refuse the whole type.
            _ => return None,
        }
    }
    Some(out)
}

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '.' || ch == '\''
}
