// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 interpolated string support.

use crate::lexer::InterpolatedStringKind;
use crate::surface::{Span, SurfaceExpr, SurfaceLit};

#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum InterpolationPart {
    Literal(String),
    Expr(SurfaceExpr),
}

#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum InterpolationError {
    #[error("unclosed interpolation brace at byte offset {offset}")]
    UnclosedBrace { offset: usize },
    #[error("empty interpolation at byte offset {offset}")]
    EmptyInterpolation { offset: usize },
    #[error("invalid expression in interpolation at byte offset {offset}: {message}")]
    InvalidExpr { offset: usize, message: String },
    #[error("unexpected closing brace at byte offset {offset}")]
    UnmatchedCloseBrace { offset: usize },
}

pub fn parse_interpolation(input: &str) -> Result<Vec<InterpolationPart>, InterpolationError> {
    let mut parts = Vec::new();
    let mut literal = String::new();
    let mut chars = input.char_indices().peekable();

    while let Some(&(offset, ch)) = chars.peek() {
        match ch {
            '\\' => {
                chars.next();
                handle_escape(&mut chars, &mut literal);
            }
            '{' => {
                if !literal.is_empty() {
                    parts.push(InterpolationPart::Literal(std::mem::take(&mut literal)));
                }
                chars.next();
                parts.push(extract_interpolation_expr(input, offset, &mut chars)?);
            }
            '}' => return Err(InterpolationError::UnmatchedCloseBrace { offset }),
            _ => {
                literal.push(ch);
                chars.next();
            }
        }
    }

    if !literal.is_empty() {
        parts.push(InterpolationPart::Literal(literal));
    }

    Ok(parts)
}

fn handle_escape(chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>, literal: &mut String) {
    match chars.peek() {
        Some(&(_, '{')) => {
            literal.push('{');
            chars.next();
        }
        Some(&(_, '}')) => {
            literal.push('}');
            chars.next();
        }
        Some(&(_, '\\')) => {
            literal.push('\\');
            chars.next();
        }
        Some(&(_, 'n')) => {
            literal.push('\n');
            chars.next();
        }
        Some(&(_, 't')) => {
            literal.push('\t');
            chars.next();
        }
        Some(&(_, 'r')) => {
            literal.push('\r');
            chars.next();
        }
        Some(&(_, '"')) => {
            literal.push('"');
            chars.next();
        }
        _ => literal.push('\\'),
    }
}

fn extract_interpolation_expr(
    input: &str,
    open_offset: usize,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> Result<InterpolationPart, InterpolationError> {
    let expr_start = chars.peek().map_or(input.len(), |&(offset, _)| offset);
    let mut expr_end = expr_start;
    let mut depth = 1_u32;

    while let Some(&(offset, ch)) = chars.peek() {
        match ch {
            '"' => expr_end = consume_string_literal(chars, offset),
            '-' if next_char(chars) == Some('-') => expr_end = consume_line_comment(chars, offset),
            '/' if next_char(chars) == Some('-') => expr_end = consume_block_comment(chars, offset),
            '{' => {
                depth += 1;
                expr_end = offset + ch.len_utf8();
                chars.next();
            }
            '}' => {
                depth -= 1;
                if depth == 0 {
                    chars.next();
                    break;
                }
                expr_end = offset + ch.len_utf8();
                chars.next();
            }
            _ => {
                expr_end = offset + ch.len_utf8();
                chars.next();
            }
        }
    }

    if depth != 0 {
        return Err(InterpolationError::UnclosedBrace {
            offset: open_offset,
        });
    }

    let expr_text = input[expr_start..expr_end].trim();
    if expr_text.is_empty() {
        return Err(InterpolationError::EmptyInterpolation {
            offset: open_offset,
        });
    }

    let expr = crate::parse_expr_with_tactics_exact(expr_text, &crate::TacticPatterns::new())
        .map_err(|err| InterpolationError::InvalidExpr {
            offset: open_offset,
            message: err.to_string(),
        })?;

    Ok(InterpolationPart::Expr(expr))
}

fn next_char(chars: &std::iter::Peekable<std::str::CharIndices<'_>>) -> Option<char> {
    let mut lookahead = chars.clone();
    lookahead.next();
    lookahead.peek().map(|(_, ch)| *ch)
}

fn consume_string_literal(
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    start: usize,
) -> usize {
    chars.next();
    let mut end = start + '"'.len_utf8();
    while let Some(&(offset, ch)) = chars.peek() {
        end = offset + ch.len_utf8();
        chars.next();
        if ch == '\\' {
            if let Some(&(esc_offset, esc)) = chars.peek() {
                end = esc_offset + esc.len_utf8();
                chars.next();
            }
            continue;
        }
        if ch == '"' {
            break;
        }
    }
    end
}

fn consume_line_comment(
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    start: usize,
) -> usize {
    chars.next();
    chars.next();
    let mut end = start + 2;
    while let Some(&(offset, ch)) = chars.peek() {
        if ch == '\n' {
            break;
        }
        end = offset + ch.len_utf8();
        chars.next();
    }
    end
}

fn consume_block_comment(
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    start: usize,
) -> usize {
    chars.next();
    chars.next();
    let mut depth = 1_u32;
    let mut end = start + 2;

    while let Some(&(offset, ch)) = chars.peek() {
        match ch {
            '/' if next_char(chars) == Some('-') => {
                chars.next();
                chars.next();
                depth += 1;
                end = offset + 2;
            }
            '-' if next_char(chars) == Some('/') => {
                chars.next();
                chars.next();
                depth -= 1;
                end = offset + 2;
                if depth == 0 {
                    break;
                }
            }
            _ => {
                end = offset + ch.len_utf8();
                chars.next();
            }
        }
    }

    end
}

#[must_use]
pub fn desugar_interpolation(parts: Vec<InterpolationPart>) -> SurfaceExpr {
    desugar_parts(parts, mk_string_lit, mk_to_string, "String.append")
}

pub fn desugar_prefixed_interpolation(
    kind: InterpolatedStringKind,
    input: &str,
) -> Result<SurfaceExpr, InterpolationError> {
    let parts = parse_interpolation(input)?;
    Ok(desugar_prefixed_interpolation_parts(kind, &parts))
}

/// Desugar pre-parsed interpolation parts by kind.
///
/// This variant takes already-parsed parts (as stored in
/// `SurfaceExpr::InterpolatedStr`) and desugars them into the appropriate
/// function application chain. Used by the elaborator to desugar at
/// elaboration time rather than parse time.
#[must_use]
pub fn desugar_prefixed_interpolation_parts(
    kind: InterpolatedStringKind,
    parts: &[InterpolationPart],
) -> SurfaceExpr {
    let owned: Vec<InterpolationPart> = parts.to_vec();
    match kind {
        InterpolatedStringKind::String => desugar_interpolation(owned),
        InterpolatedStringKind::Format => {
            desugar_parts(owned, mk_format_text, mk_format_expr, "Format.append")
        }
        InterpolatedStringKind::MessageData => mk_message_data(desugar_parts(
            owned,
            mk_format_text,
            mk_format_expr,
            "Format.append",
        )),
    }
}

fn desugar_parts(
    parts: Vec<InterpolationPart>,
    mk_lit: fn(&str) -> SurfaceExpr,
    mk_expr: fn(SurfaceExpr) -> SurfaceExpr,
    append_name: &str,
) -> SurfaceExpr {
    if parts.is_empty() {
        return mk_lit("");
    }

    let mut exprs: Vec<_> = parts
        .into_iter()
        .map(|part| match part {
            InterpolationPart::Literal(text) => mk_lit(&text),
            InterpolationPart::Expr(expr) => mk_expr(expr),
        })
        .collect();

    if exprs.len() == 1 {
        return exprs.pop().expect("single interpolation segment");
    }

    let mut acc = exprs.pop().expect("non-empty interpolation");
    while let Some(expr) = exprs.pop() {
        acc = mk_binary_app(append_name, expr, acc);
    }
    acc
}

fn mk_string_lit(text: &str) -> SurfaceExpr {
    SurfaceExpr::Lit(Span::dummy(), SurfaceLit::String(text.to_owned()))
}

fn mk_to_string(expr: SurfaceExpr) -> SurfaceExpr {
    mk_unary_app("toString", expr)
}

fn mk_format_text(text: &str) -> SurfaceExpr {
    mk_unary_app("Format.text", mk_string_lit(text))
}

fn mk_format_expr(expr: SurfaceExpr) -> SurfaceExpr {
    mk_unary_app("format", expr)
}

fn mk_message_data(expr: SurfaceExpr) -> SurfaceExpr {
    mk_unary_app("MessageData.ofFormat", expr)
}

fn mk_unary_app(name: &str, arg: SurfaceExpr) -> SurfaceExpr {
    let func = SurfaceExpr::Ident(Span::dummy(), name.to_owned());
    SurfaceExpr::app(func, vec![arg])
}

fn mk_binary_app(name: &str, lhs: SurfaceExpr, rhs: SurfaceExpr) -> SurfaceExpr {
    let func = SurfaceExpr::Ident(Span::dummy(), name.to_owned());
    SurfaceExpr::app(func, vec![lhs, rhs])
}

#[cfg(test)]
#[path = "interpolation_tests.rs"]
mod tests;
