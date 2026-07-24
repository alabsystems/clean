// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended kernel-level builders for string interpolation elaboration.

use crate::error::ElabError;
use clean_kernel::name::Name;
use clean_kernel::Expr;

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum InterpKind {
    SString,
    Message,
    Format,
    Custom(Name),
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum InterpFragment {
    Literal(String),
    Expr(Expr),
    Nested(Vec<InterpFragment>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InterpConfig {
    pub(crate) max_fragments: usize,
    pub(crate) allow_nested: bool,
    pub(crate) auto_to_string: bool,
}

impl Default for InterpConfig {
    fn default() -> Self {
        Self {
            max_fragments: 100,
            allow_nested: true,
            auto_to_string: true,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct InterpResult {
    pub(crate) elaborated: Expr,
    pub(crate) fragments_count: usize,
    pub(crate) to_string_insertions: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FormatSpec {
    pub(crate) width: Option<usize>,
    pub(crate) precision: Option<usize>,
    pub(crate) fill: char,
    pub(crate) align: Align,
}

impl Default for FormatSpec {
    fn default() -> Self {
        Self {
            width: None,
            precision: None,
            fill: ' ',
            align: Align::Left,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum Align {
    Left,
    Right,
    Center,
}

pub(crate) fn elaborate_interpolation(
    kind: &InterpKind,
    fragments: &[InterpFragment],
    config: &InterpConfig,
) -> Result<InterpResult, ElabError> {
    validate_interpolation(fragments, config)?;

    let fragments_count = count_fragments(fragments);
    let expr_count = count_expr_fragments(fragments);
    let elaborated = match kind {
        InterpKind::SString => {
            let prepared = prepare_string_fragments(fragments, config.auto_to_string);
            build_string_append_chain(&prepared)
        }
        InterpKind::Message => {
            let prepared = prepare_message_fragments(fragments);
            build_message_chain(&prepared)
        }
        InterpKind::Format => {
            let prepared = prepare_format_fragments(fragments);
            build_format_append_chain(&prepared)
        }
        InterpKind::Custom(name) => {
            let prepared = prepare_string_fragments(fragments, config.auto_to_string);
            build_custom_append_chain(name, &prepared)
        }
    };

    let to_string_insertions = match kind {
        InterpKind::SString | InterpKind::Custom(_) if config.auto_to_string => expr_count,
        _ => 0,
    };

    Ok(InterpResult {
        elaborated,
        fragments_count,
        to_string_insertions,
    })
}

pub(crate) fn build_string_append_chain(fragments: &[InterpFragment]) -> Expr {
    let flattened = flatten_fragments(fragments);
    let parts = flattened
        .into_iter()
        .map(|fragment| match fragment {
            InterpFragment::Literal(text) => Expr::str_lit(text),
            InterpFragment::Expr(expr) => expr,
            InterpFragment::Nested(_) => Expr::str_lit(""),
        })
        .collect::<Vec<_>>();
    build_binary_chain(Expr::const_str("String.append"), parts, Expr::str_lit(""))
}

pub(crate) fn build_message_chain(fragments: &[InterpFragment]) -> Expr {
    let flattened = flatten_fragments(fragments);
    let parts = flattened
        .into_iter()
        .map(|fragment| match fragment {
            InterpFragment::Literal(text) => message_of_format(format_text(text)),
            InterpFragment::Expr(expr) => expr,
            InterpFragment::Nested(_) => empty_message(),
        })
        .collect::<Vec<_>>();
    build_binary_chain(
        Expr::const_str("MessageData.compose"),
        parts,
        empty_message(),
    )
}

pub(crate) fn insert_to_string(expr: &Expr, target_type: &Expr) -> Expr {
    let _ = target_type;
    Expr::app(Expr::const_str("toString"), expr.clone())
}

pub(crate) fn parse_format_spec(spec: &str) -> Result<FormatSpec, ElabError> {
    let raw = spec
        .strip_prefix("{:")
        .and_then(|rest| rest.strip_suffix('}'))
        .or_else(|| spec.strip_prefix(':'))
        .unwrap_or(spec);
    if raw.is_empty() {
        return Ok(FormatSpec::default());
    }

    let mut chars = raw.chars().collect::<Vec<_>>();
    if let Some(last) = chars.last().copied() {
        if is_format_type(last) {
            let _ = chars.pop();
        }
    }

    let mut out = FormatSpec::default();
    let mut idx = 0;

    if chars.len() >= 2 && is_align_char(chars[1]) {
        out.fill = chars[0];
        out.align = align_from_char(chars[1])?;
        idx = 2;
    } else if chars.first().is_some_and(|ch| is_align_char(*ch)) {
        out.align = align_from_char(chars[0])?;
        idx = 1;
    } else if chars.get(idx) == Some(&'0')
        && chars.get(idx + 1).is_some_and(|ch| ch.is_ascii_digit())
    {
        out.fill = '0';
        out.align = Align::Right;
        idx += 1;
    }

    let width_start = idx;
    while chars.get(idx).is_some_and(|ch| ch.is_ascii_digit()) {
        idx += 1;
    }
    if idx > width_start {
        out.width = Some(parse_usize(&chars[width_start..idx], "width")?);
    }

    if chars.get(idx) == Some(&'.') {
        idx += 1;
        let precision_start = idx;
        while chars.get(idx).is_some_and(|ch| ch.is_ascii_digit()) {
            idx += 1;
        }
        if idx == precision_start {
            return Err(ElabError::ParseError(format!(
                "invalid format spec {spec:?}: precision requires digits"
            )));
        }
        out.precision = Some(parse_usize(&chars[precision_start..idx], "precision")?);
    }

    if idx != chars.len() {
        return Err(ElabError::ParseError(format!(
            "invalid format spec {spec:?}: trailing data {:?}",
            chars[idx..].iter().collect::<String>()
        )));
    }

    Ok(out)
}

pub(crate) fn validate_interpolation(
    fragments: &[InterpFragment],
    config: &InterpConfig,
) -> Result<(), ElabError> {
    let count = count_fragments(fragments);
    if count > config.max_fragments {
        return Err(ElabError::Unsupported {
            feature: format!(
                "interpolation has {count} fragments, exceeding max_fragments {}",
                config.max_fragments
            ),
        });
    }
    if !config.allow_nested && has_nested_fragments(fragments) {
        return Err(ElabError::Unsupported {
            feature: "nested interpolation fragments are disabled".to_string(),
        });
    }
    Ok(())
}

#[must_use]
fn count_fragments(fragments: &[InterpFragment]) -> usize {
    fragments
        .iter()
        .map(|fragment| match fragment {
            InterpFragment::Literal(_) | InterpFragment::Expr(_) => 1,
            InterpFragment::Nested(inner) => 1 + count_fragments(inner),
        })
        .sum()
}

#[must_use]
fn count_expr_fragments(fragments: &[InterpFragment]) -> usize {
    fragments
        .iter()
        .map(|fragment| match fragment {
            InterpFragment::Literal(_) => 0,
            InterpFragment::Expr(_) => 1,
            InterpFragment::Nested(inner) => count_expr_fragments(inner),
        })
        .sum()
}

#[must_use]
fn has_nested_fragments(fragments: &[InterpFragment]) -> bool {
    fragments.iter().any(|fragment| match fragment {
        InterpFragment::Nested(_) => true,
        InterpFragment::Literal(_) | InterpFragment::Expr(_) => false,
    })
}

#[must_use]
fn flatten_fragments(fragments: &[InterpFragment]) -> Vec<InterpFragment> {
    let mut out = Vec::new();
    flatten_into(fragments, &mut out);
    out
}

fn flatten_into(fragments: &[InterpFragment], out: &mut Vec<InterpFragment>) {
    for fragment in fragments {
        match fragment {
            InterpFragment::Literal(text) => push_literal(out, text),
            InterpFragment::Expr(expr) => out.push(InterpFragment::Expr(expr.clone())),
            InterpFragment::Nested(inner) => flatten_into(inner, out),
        }
    }
}

fn push_literal(out: &mut Vec<InterpFragment>, text: &str) {
    if let Some(InterpFragment::Literal(existing)) = out.last_mut() {
        existing.push_str(text);
    } else {
        out.push(InterpFragment::Literal(text.to_string()));
    }
}

#[must_use]
fn prepare_string_fragments(
    fragments: &[InterpFragment],
    auto_to_string: bool,
) -> Vec<InterpFragment> {
    flatten_fragments(fragments)
        .into_iter()
        .map(|fragment| match fragment {
            InterpFragment::Literal(text) => InterpFragment::Literal(text),
            InterpFragment::Expr(expr) if auto_to_string => {
                InterpFragment::Expr(insert_to_string(&expr, &Expr::const_str("String")))
            }
            InterpFragment::Expr(expr) => InterpFragment::Expr(expr),
            InterpFragment::Nested(_) => InterpFragment::Literal(String::new()),
        })
        .collect()
}

#[must_use]
fn prepare_format_fragments(fragments: &[InterpFragment]) -> Vec<InterpFragment> {
    flatten_fragments(fragments)
        .into_iter()
        .map(|fragment| match fragment {
            InterpFragment::Literal(text) => InterpFragment::Expr(format_text(text)),
            InterpFragment::Expr(expr) => {
                InterpFragment::Expr(Expr::app(Expr::const_str("format"), expr))
            }
            InterpFragment::Nested(_) => InterpFragment::Expr(Expr::const_str("Format.nil")),
        })
        .collect()
}

#[must_use]
fn prepare_message_fragments(fragments: &[InterpFragment]) -> Vec<InterpFragment> {
    flatten_fragments(fragments)
        .into_iter()
        .map(|fragment| match fragment {
            InterpFragment::Literal(text) => InterpFragment::Literal(text),
            InterpFragment::Expr(expr) => {
                let fmt = Expr::app(Expr::const_str("format"), expr);
                InterpFragment::Expr(message_of_format(fmt))
            }
            InterpFragment::Nested(_) => InterpFragment::Expr(empty_message()),
        })
        .collect()
}

fn build_format_append_chain(fragments: &[InterpFragment]) -> Expr {
    let flattened = flatten_fragments(fragments);
    let parts = flattened
        .into_iter()
        .map(|fragment| match fragment {
            InterpFragment::Literal(text) => format_text(text),
            InterpFragment::Expr(expr) => expr,
            InterpFragment::Nested(_) => Expr::const_str("Format.nil"),
        })
        .collect::<Vec<_>>();
    build_binary_chain(
        Expr::const_str("Format.append"),
        parts,
        Expr::const_str("Format.nil"),
    )
}

fn build_custom_append_chain(name: &Name, fragments: &[InterpFragment]) -> Expr {
    let flattened = flatten_fragments(fragments);
    let parts = flattened
        .into_iter()
        .map(|fragment| match fragment {
            InterpFragment::Literal(text) => Expr::str_lit(text),
            InterpFragment::Expr(expr) => expr,
            InterpFragment::Nested(_) => Expr::str_lit(""),
        })
        .collect::<Vec<_>>();
    build_binary_chain(Expr::const_(name.clone(), vec![]), parts, Expr::str_lit(""))
}

fn build_binary_chain(op: Expr, parts: Vec<Expr>, empty: Expr) -> Expr {
    let mut iter = parts.into_iter().rev();
    let Some(mut acc) = iter.next() else {
        return empty;
    };
    for part in iter {
        acc = Expr::app(Expr::app(op.clone(), part), acc);
    }
    acc
}

fn format_text(text: String) -> Expr {
    Expr::app(Expr::const_str("Format.text"), Expr::str_lit(text))
}

fn message_of_format(expr: Expr) -> Expr {
    Expr::app(Expr::const_str("MessageData.ofFormat"), expr)
}

fn empty_message() -> Expr {
    message_of_format(Expr::const_str("Format.nil"))
}

#[must_use]
fn is_align_char(ch: char) -> bool {
    matches!(ch, '<' | '>' | '^')
}

fn align_from_char(ch: char) -> Result<Align, ElabError> {
    match ch {
        '<' => Ok(Align::Left),
        '>' => Ok(Align::Right),
        '^' => Ok(Align::Center),
        other => Err(ElabError::ParseError(format!(
            "invalid alignment character {other:?}"
        ))),
    }
}

#[must_use]
fn is_format_type(ch: char) -> bool {
    matches!(ch, 'd' | 'f' | 's' | 'x' | 'o' | 'b' | 'e')
}

fn parse_usize(chars: &[char], label: &str) -> Result<usize, ElabError> {
    chars
        .iter()
        .collect::<String>()
        .parse::<usize>()
        .map_err(|err| ElabError::ParseError(format!("invalid {label}: {err}")))
}
