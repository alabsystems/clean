// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro registration helpers — syntax/notation pattern conversion.

use clean_macro::quotation::parse_quotation;
use clean_macro::{Syntax, SyntaxKind, SyntaxQuote};
use clean_parser::{NotationItem, NotationKind, SurfaceExpr, SyntaxPatternItem};

use super::surface_to_syntax;

/// Determine the syntax category of a raw quotation body from its outer
/// delimiter: `` `(...) `` ⇒ term, `` `[...] `` ⇒ tactic, `` `{...} `` ⇒ command.
pub(super) fn quotation_category(content: &str) -> SyntaxKind {
    match content.trim().chars().next() {
        Some('[') => SyntaxKind::tactic(),
        Some('{') => SyntaxKind::command(),
        _ => SyntaxKind::term(),
    }
}

/// Lower an already-parsed quotation `body` to a [`SyntaxQuote`], taking the
/// syntax category from the original quotation `content`'s outer delimiter.
///
/// This is the same lowering [`surface_expr_to_syntax_quote`] applies on the
/// fast path (`surface_to_syntax(&body)` + delimiter-derived category); exposing
/// it lets the computed-body evaluator reuse it on a body it has already parsed
/// and resolved, so the produced `Syntax` is byte-identical to the equivalent
/// direct quotation.
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(super) fn syntax_quote_from_body(body: &SurfaceExpr, content: &str) -> SyntaxQuote {
    SyntaxQuote::new(surface_to_syntax(body), quotation_category(content))
}

/// Errors that can occur while registering macros from surface syntax
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum MacroRegistrationError {
    /// Failed to parse a syntax quotation
    #[error("failed to parse syntax quotation: {0}")]
    QuotationParse(String),
    /// A computed (`do`-block) `macro_rules` right-hand side is outside the
    /// faithfully-evaluable subset (see [`super::computed_body`]). This is an
    /// honest defer: it surfaces as a registration error rather than a silent
    /// mis-expansion.
    #[error("computed macro_rules body not supported: {0}")]
    ComputedBodyUnsupported(String),
    /// A computed `macro_rules` body unconditionally raised `throwError "msg"`
    /// (or a fully-resolved `throwError s!"…"`) at macro-expansion time. Faithful
    /// to Lean's `MacroM`, the macro cannot produce a valid expansion: this is the
    /// user's own custom error, surfaced verbatim as a real diagnostic — NOT a
    /// fabricated expansion. The `String` is the rendered message.
    #[error("{0}")]
    MacroThrowError(String),
}

/// Convert a surface expression that may contain a syntax quotation into a `SyntaxQuote`.
pub(super) fn surface_expr_to_syntax_quote(
    expr: &SurfaceExpr,
) -> Result<SyntaxQuote, MacroRegistrationError> {
    match expr {
        SurfaceExpr::SyntaxQuote(_, content) => {
            // Faithful path: parse the quotation body with the antiquotation- and
            // operator-aware quotation grammar, then lower to macro `Syntax`. This
            // correctly handles multi-token templates such as `` `($x + $x) `` that
            // the simplified string quotation parser silently truncates to `$x`.
            //
            // If the full quotation grammar cannot parse the body (e.g. a construct
            // it does not yet support), fall back to the legacy simplified parser so
            // we never regress previously-handled shapes.
            match clean_parser::parse_quotation_body(content) {
                Ok(body) => Ok(SyntaxQuote::new(
                    surface_to_syntax(&body),
                    quotation_category(content),
                )),
                Err(_) => {
                    let raw = format!("`{content}");
                    parse_quotation(&raw)
                        .map_err(|e| MacroRegistrationError::QuotationParse(e.to_string()))
                }
            }
        }
        other => Ok(SyntaxQuote::new(
            surface_to_syntax(other),
            SyntaxKind::term(),
        )),
    }
}

/// Convert a syntax pattern (from `syntax` decl) to Syntax AST.
pub(super) fn syntax_pattern_to_syntax(items: &[SyntaxPatternItem]) -> Syntax {
    if items.is_empty() {
        return Syntax::missing();
    }

    let children: Vec<Syntax> = items.iter().map(syntax_pattern_item_to_syntax).collect();

    if children.len() == 1 {
        children
            .into_iter()
            .next()
            .expect("children has exactly 1 element")
    } else {
        // Create a sequence node
        Syntax::node(SyntaxKind::app("seq"), children)
    }
}

/// Convert a single SyntaxPatternItem to Syntax.
fn syntax_pattern_item_to_syntax(item: &SyntaxPatternItem) -> Syntax {
    match item {
        SyntaxPatternItem::Literal(s) => Syntax::atom(s),
        SyntaxPatternItem::Variable { name, category } => {
            if category.is_some() {
                // Variable with category becomes an antiquotation
                Syntax::mk_antiquot(name)
            } else {
                Syntax::mk_antiquot(name)
            }
        }
        SyntaxPatternItem::CategoryRef(cat) => Syntax::mk_antiquot(cat),
        SyntaxPatternItem::Optional(inner) => {
            let inner_syn = syntax_pattern_to_syntax(inner);
            Syntax::node(SyntaxKind::app("optional"), vec![inner_syn])
        }
        SyntaxPatternItem::Repetition {
            pattern,
            separator,
            at_least_one,
        } => {
            let inner_syn = syntax_pattern_to_syntax(pattern);
            let sep_syn = separator
                .as_ref()
                .map_or_else(Syntax::missing, |s| Syntax::atom(s));
            let kind = if *at_least_one { "rep1" } else { "rep0" };
            Syntax::node(SyntaxKind::app(kind), vec![inner_syn, sep_syn])
        }
        SyntaxPatternItem::Precedence(_) => Syntax::missing(), // Precedence is metadata, not pattern
    }
}

/// Determine the target kind from pattern items.
pub(super) fn pattern_kind_from_items(items: &[SyntaxPatternItem]) -> SyntaxKind {
    // Look for the first literal or use app_kind as default
    for item in items {
        if let SyntaxPatternItem::Literal(lit) = item {
            return SyntaxKind::app(lit);
        }
    }
    SyntaxKind::app_kind()
}

/// Generate a name from pattern items.
pub(super) fn pattern_to_name(items: &[SyntaxPatternItem]) -> String {
    items
        .iter()
        .filter_map(|item| match item {
            SyntaxPatternItem::Literal(s) => Some(s.replace(' ', "_")),
            SyntaxPatternItem::Variable { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("_")
}

/// Convert notation pattern to Syntax, returning pattern, target kind, and variable names.
pub(super) fn notation_pattern_to_syntax(
    kind: NotationKind,
    items: &[NotationItem],
) -> (Syntax, SyntaxKind, Vec<String>) {
    let mut children = Vec::new();
    let mut var_names = Vec::new();

    for item in items {
        match item {
            NotationItem::Literal(s) => {
                children.push(Syntax::atom(s));
            }
            NotationItem::Variable(name) => {
                children.push(Syntax::mk_antiquot(name));
                var_names.push(name.clone());
            }
        }
    }

    let target_kind = match kind {
        NotationKind::Infixl | NotationKind::Infixr | NotationKind::Infix => {
            // Infix: look for operator literal
            items
                .iter()
                .find_map(|i| {
                    if let NotationItem::Literal(s) = i {
                        Some(SyntaxKind::app(s.trim()))
                    } else {
                        None
                    }
                })
                .unwrap_or_else(SyntaxKind::app_kind)
        }
        NotationKind::Prefix | NotationKind::Postfix => {
            // Prefix/postfix: use the literal as kind
            items
                .iter()
                .find_map(|i| {
                    if let NotationItem::Literal(s) = i {
                        Some(SyntaxKind::app(s.trim()))
                    } else {
                        None
                    }
                })
                .unwrap_or_else(SyntaxKind::app_kind)
        }
        NotationKind::Notation => {
            // General notation: use first literal or app_kind
            items
                .iter()
                .find_map(|i| {
                    if let NotationItem::Literal(s) = i {
                        Some(SyntaxKind::app(s.trim()))
                    } else {
                        None
                    }
                })
                .unwrap_or_else(SyntaxKind::app_kind)
        }
    };

    let pattern = if children.len() == 1 {
        children
            .into_iter()
            .next()
            .expect("children has exactly 1 element")
    } else {
        Syntax::node(SyntaxKind::app("notation"), children)
    };

    (pattern, target_kind, var_names)
}

/// Generate name from notation.
pub(super) fn notation_to_name(kind: NotationKind, items: &[NotationItem]) -> String {
    let prefix = match kind {
        NotationKind::Infixl => "infixl",
        NotationKind::Infixr => "infixr",
        NotationKind::Infix => "infix",
        NotationKind::Prefix => "prefix",
        NotationKind::Postfix => "postfix",
        NotationKind::Notation => "notation",
    };

    let parts: Vec<String> = items
        .iter()
        .map(|i| match i {
            NotationItem::Literal(s) => s.trim().replace(' ', "_"),
            NotationItem::Variable(v) => v.clone(),
        })
        .collect();

    format!("{}_{}", prefix, parts.join("_"))
}
