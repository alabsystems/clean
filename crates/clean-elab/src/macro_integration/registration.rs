// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro registration helpers — syntax/notation pattern conversion.

use clean_macro::quotation::parse_quotation;
use clean_macro::{Syntax, SyntaxKind, SyntaxQuote};
use clean_parser::{NotationItem, NotationKind, SurfaceExpr, SurfaceName, SyntaxPatternItem};

use super::surface_to_syntax;

/// Determine the syntax category of a raw quotation body. A `(cat| …)`
/// category head ([`quotation_category_head`]) is authoritative:
/// `` `(tactic| …) `` ⇒ tactic, `` `(conv| …) `` ⇒ conv,
/// `` `(command| …) `` ⇒ command, `` `(term| …) `` ⇒ term. Without a head the
/// outer delimiter decides: `` `(...) `` ⇒ term, `` `[...] `` ⇒ tactic,
/// `` `{...} `` ⇒ command.
pub(super) fn quotation_category(content: &str) -> SyntaxKind {
    if let Some((head, _)) = quotation_category_head(content) {
        return match head {
            "tactic" => SyntaxKind::tactic(),
            "conv" => SyntaxKind::app("conv"),
            "command" => SyntaxKind::command(),
            _ => SyntaxKind::term(),
        };
    }
    match content.trim().chars().next() {
        Some('[') => SyntaxKind::tactic(),
        Some('{') => SyntaxKind::command(),
        _ => SyntaxKind::term(),
    }
}

/// Split a category-headed quotation `(cat| body)` into `(head, body)`.
///
/// Only the categories Lean writes at quotation heads are recognized —
/// `tactic`, `conv`, `command`, `term` — and the `|` must directly follow the
/// head token, so ordinary parenthesized terms (`(a || b)`, `(p | q)`) are
/// never split. `pub(crate)`: the declaration router (`infer::elaborate_decl`)
/// uses the same recognition to send `(tactic| …)` macros to the
/// tactic-position registration path.
pub(crate) fn quotation_category_head(content: &str) -> Option<(&str, &str)> {
    let inner = content.trim().strip_prefix('(')?.strip_suffix(')')?;
    let bar = inner.find('|')?;
    let (head, rest) = inner.split_at(bar);
    let head = head.trim();
    let body = &rest[1..];
    // A doubled bar is the `||` operator, not a category delimiter.
    if body.starts_with('|') {
        return None;
    }
    if !matches!(head, "tactic" | "conv" | "command" | "term") {
        return None;
    }
    Some((head, body.trim()))
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
    /// A source category cannot be represented by the single-component protocol.
    #[error("syntax category must be one non-relative string name component")]
    SyntaxCategoryName,
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
    /// A macro or notation template whose binding structure Clean does not
    /// model exactly ([`clean_parser::TemplateRefusal`]). The declaration is
    /// refused; it is never registered with a template read another way.
    #[error("template refused: {0}")]
    TemplateRefused(String),
}

impl MacroRegistrationError {
    /// The registration error refusing a template (see
    /// [`Self::TemplateRefused`]).
    pub(super) fn refused(refusal: &clean_parser::TemplateRefusal) -> Self {
        Self::TemplateRefused(refusal.reason().to_owned())
    }
}

/// The expansion registered for a macro or notation Clean refuses: an
/// identifier no source can spell and nothing resolves, so every use that
/// reaches it fails as an unknown identifier — the use is refused, never
/// read as other syntax.
pub(super) fn refused_expansion_quote(reason: &str) -> SyntaxQuote {
    SyntaxQuote::new(
        Syntax::ident(&SurfaceName::unspellable(
            &format!("refused notation or macro template: {reason}"),
            0,
        )),
        SyntaxKind::term(),
    )
}

/// Convert a surface expression that may contain a syntax quotation into a `SyntaxQuote`.
pub(super) fn surface_expr_to_syntax_quote(
    expr: &SurfaceExpr,
) -> Result<SyntaxQuote, MacroRegistrationError> {
    surface_expr_to_template_quote(expr, None)
}

/// Where a macro's EXPANSION template is declared: its namespace and the
/// section variables in scope there. See
/// [`clean_parser::mark_template_free_references`].
pub(super) struct TemplateSite<'a> {
    pub(super) namespace: &'a clean_kernel::Name,
    pub(super) section_variables: &'a [SurfaceName],
    /// The declaring command, whose pre-resolution of the template's free
    /// names every use reads ([`clean_parser::TemplateOrigin::site`]).
    pub(super) site: Option<clean_parser::TemplateSiteId>,
}

/// [`surface_expr_to_syntax_quote`] for a macro's expansion template: its free
/// references are marked hygienic, so no binder at the use site captures
/// them (`macro "H " x:term : term => `(gf $x)` calls the global `gf` even
/// where a parameter `gf` is in scope, as in Lean 4).
pub(super) fn surface_expr_to_expansion_quote(
    expr: &SurfaceExpr,
    site: &TemplateSite<'_>,
) -> Result<SyntaxQuote, MacroRegistrationError> {
    surface_expr_to_template_quote(expr, Some(site))
}

fn hygienic_body(
    body: SurfaceExpr,
    site: Option<&TemplateSite<'_>>,
) -> Result<SurfaceExpr, MacroRegistrationError> {
    match site {
        Some(site) => clean_parser::mark_template_free_references(
            &body,
            &[],
            site.namespace,
            site.section_variables,
            site.site,
        )
        .map_err(|refusal| MacroRegistrationError::refused(&refusal)),
        None => Ok(body),
    }
}

fn surface_expr_to_template_quote(
    expr: &SurfaceExpr,
    site: Option<&TemplateSite<'_>>,
) -> Result<SyntaxQuote, MacroRegistrationError> {
    match expr {
        SurfaceExpr::SyntaxQuote(_, content) => {
            // A `(cat| …)` category head is authoritative: the body AFTER the
            // head is parsed with the quotation grammar and the category comes
            // from the head. An unparseable body is a loud registration error —
            // an explicitly-categorized quotation must never fall back to a
            // term template that could silently never fire.
            if let Some((head, body)) = quotation_category_head(content) {
                let wrapped = format!("({body})");
                let parsed = clean_parser::parse_quotation_body(&wrapped).map_err(|e| {
                    MacroRegistrationError::QuotationParse(format!(
                        "in `({head}| …)` quotation body `{body}`: {e}"
                    ))
                })?;
                return Ok(SyntaxQuote::new(
                    surface_to_syntax(&hygienic_body(parsed, site)?),
                    quotation_category(content),
                ));
            }
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
                    surface_to_syntax(&hygienic_body(body, site)?),
                    quotation_category(content),
                )),
                Err(_) => {
                    let quote = legacy_quotation(content)?;
                    Ok(match site {
                        Some(site) => SyntaxQuote::new(
                            mark_legacy_template(quote.syntax, site, &mut Vec::new()),
                            quote.category,
                        ),
                        None => quote,
                    })
                }
            }
        }
        other => Ok(SyntaxQuote::new(
            surface_to_syntax(&hygienic_body(other.clone(), site)?),
            SyntaxKind::term(),
        )),
    }
}

/// The quotation `content` read by the legacy simplified parser, the reader
/// of the quotations the quotation grammar cannot parse (a typed
/// antiquotation `$x:term`, …). Its grammar is an application of
/// identifiers, literals, parentheses and antiquotations: it has no binder.
fn legacy_quotation(content: &str) -> Result<SyntaxQuote, MacroRegistrationError> {
    parse_quotation(&format!("`{content}"))
        .map_err(|e| MacroRegistrationError::QuotationParse(e.to_string()))
}

/// Whether `kind` is an antiquotation node of the legacy quotation reader,
/// whose identifiers name the macro's pattern variables.
fn is_legacy_antiquotation(kind: &SyntaxKind) -> bool {
    [
        SyntaxKind::antiquot(),
        SyntaxKind::antiquot_typed(),
        SyntaxKind::antiquot_splice(),
        SyntaxKind::antiquot_splice_typed(),
    ]
    .contains(kind)
}

/// Mark every identifier of a legacy-read template (see [`legacy_quotation`])
/// as a free reference of the template declared at `site`, exactly as
/// [`clean_parser::mark_template_free_references`] marks a parsed one: the
/// legacy grammar binds nothing, so every identifier outside an
/// antiquotation is free, and resolves where the macro is declared — never
/// with the opens or the locals of a use (`section open A macro "M" x:term :
/// term => `(Nat.add kq $x:term) end` reads `A.kq` everywhere). `spellings`
/// collects the marked names, which the declaration pre-resolves.
fn mark_legacy_template(
    syntax: Syntax,
    site: &TemplateSite<'_>,
    spellings: &mut Vec<SurfaceName>,
) -> Syntax {
    match syntax {
        Syntax::Ident(info, name) => {
            let inert = name.is_anonymous()
                || name.is_relative_constructor()
                || name.is_global_reference()
                || name.template_origin().is_some()
                || name.template_scope().is_some()
                || ["_", "Type", "Prop"]
                    .iter()
                    .any(|keyword| name.is_unescaped_component(keyword));
            if inert {
                return Syntax::Ident(info, name);
            }
            let origin = std::sync::Arc::new(clean_parser::TemplateOrigin {
                namespace: site.namespace.clone(),
                section_variable: site.section_variables.contains(&name),
                site: site.site,
            });
            if !spellings.contains(&name) {
                spellings.push(name.clone());
            }
            Syntax::Ident(info, name.with_template_origin(origin))
        }
        Syntax::Node(mut node) if !is_legacy_antiquotation(&node.kind) => {
            node.children = std::mem::take(&mut node.children)
                .into_iter()
                .map(|child| mark_legacy_template(child, site, spellings))
                .collect();
            Syntax::Node(node)
        }
        other => other,
    }
}

/// Every spelling a use of the macro expansion `expr` resolves as a GLOBAL
/// name, which the declaration pre-resolves (see
/// [`clean_parser::template_free_reference_spellings`]); read with the same
/// grammar the registration reads the template with, the quotation grammar
/// or the legacy one.
///
/// # Errors
///
/// A template the hygiene walk refuses, or a quotation neither grammar
/// reads.
pub(crate) fn macro_template_spellings(
    expr: &SurfaceExpr,
    namespace: &clean_kernel::Name,
) -> Result<Vec<SurfaceName>, MacroRegistrationError> {
    let body = match expr {
        SurfaceExpr::SyntaxQuote(_, content) => match quotation_category_head(content) {
            Some((_, body)) => clean_parser::parse_quotation_body(&format!("({body})")),
            None => match clean_parser::parse_quotation_body(content) {
                Ok(body) => Ok(body),
                Err(_) => {
                    let quote = legacy_quotation(content)?;
                    let mut spellings = Vec::new();
                    let site = TemplateSite {
                        namespace,
                        section_variables: &[],
                        site: None,
                    };
                    let _ = mark_legacy_template(quote.syntax, &site, &mut spellings);
                    return Ok(spellings);
                }
            },
        },
        other => Ok(other.clone()),
    };
    // A body neither grammar reads refuses at registration, which reports it.
    let Ok(body) = body else {
        return Ok(Vec::new());
    };
    clean_parser::template_free_reference_spellings(&body, &[], namespace)
        .map_err(|refusal| MacroRegistrationError::refused(&refusal))
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
        // Category labels are a textual protocol field, not a rendered Name.
        SyntaxPatternItem::CategoryRef(cat) => {
            Syntax::mk_antiquot(&SurfaceName::component(cat, false))
        }
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
            SyntaxPatternItem::Variable { name, .. } => Some(name.to_string()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("_")
}

/// Convert notation pattern to Syntax, returning pattern, target kind, and variable names.
pub(super) fn notation_pattern_to_syntax(
    kind: NotationKind,
    items: &[NotationItem],
) -> (Syntax, SyntaxKind, Vec<SurfaceName>) {
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
            NotationItem::Variable(v) => v.to_string(),
        })
        .collect();

    format!("{}_{}", prefix, parts.join("_"))
}
