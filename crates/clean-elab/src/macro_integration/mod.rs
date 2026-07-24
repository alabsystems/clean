// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro system integration with elaboration
//!
//! This module provides the bridge between the macro system (clean-macro)
//! and the elaborator (clean-elab). It handles:
//!
//! - Converting between parser `SurfaceExpr` and macro `Syntax`
//! - Running macro expansion before elaboration
//! - Managing macro registries in the elaboration context
//!
//! # Architecture
//!
//! The macro expansion phase fits between parsing and elaboration:
//!
//! ```text
//! Source Code → Parser → SurfaceExpr → MacroExpand → SurfaceExpr → Elaboration → Expr
//! ```
//!
//! Macros work on `Syntax` (a generic AST), while elaboration works on
//! `SurfaceExpr` (the typed parser AST). This module provides conversion
//! functions between these representations.

mod computed_body;
mod from_syntax;
mod registration;
mod to_syntax;
mod to_syntax_helpers;

#[cfg(test)]
mod tests;

// Public re-exports from sub-modules
pub use from_syntax::syntax_to_surface;
pub use registration::MacroRegistrationError;
pub use to_syntax::surface_to_syntax;

// Re-exports for tests (pub(super) items from sub-modules)
#[cfg(test)]
use from_syntax::syntax_to_pattern;
#[cfg(test)]
use to_syntax::surface_pattern_to_syntax;

use registration::{
    notation_pattern_to_syntax, notation_to_name, pattern_kind_from_items, pattern_to_name,
    surface_expr_to_syntax_quote, syntax_pattern_to_syntax,
};

use clean_macro::registry::SyntaxCategoryRegistry;
use clean_macro::{
    builtin_registry, HygienicExpander, MacroDef, MacroExpander, MacroRegistry, MacroResult,
    Syntax, SyntaxKind, SyntaxQuote,
};
use clean_parser::{
    LevelExpr, MacroArm, NotationItem, NotationKind, SurfaceArg, SurfaceExpr, SyntaxPatternItem,
};
use std::collections::HashMap;

// Types only used by tests via `use super::*`
#[cfg(test)]
use clean_parser::{
    Projection, QAntiquotContent, QQuotationKind, Span, SurfaceBinder, SurfaceBinderInfo,
    SurfaceFieldAssign, SurfaceLit, SurfaceMatchArm, SurfacePattern, UniverseExpr,
};

/// Macro expansion context for elaboration
#[derive(Clone)]
pub struct MacroCtx {
    /// The macro registry containing all available macros
    registry: MacroRegistry,
    /// Syntax category registry
    categories: SyntaxCategoryRegistry,
    /// Whether to use hygienic expansion
    hygienic: bool,
    /// Statistics from last expansion
    last_stats: Option<clean_macro::expand::ExpansionStats>,
    /// File-scoped aliases for nullary notation parsed as bare identifiers.
    simple_notations: HashMap<String, SurfaceExpr>,
}

impl Default for MacroCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl MacroCtx {
    /// Create a new macro context with built-in macros
    pub fn new() -> Self {
        Self {
            registry: builtin_registry(),
            categories: SyntaxCategoryRegistry::new(),
            hygienic: true,
            last_stats: None,
            simple_notations: HashMap::new(),
        }
    }

    /// Create with a custom registry
    pub fn with_registry(registry: MacroRegistry) -> Self {
        Self {
            registry,
            categories: SyntaxCategoryRegistry::new(),
            hygienic: true,
            last_stats: None,
            simple_notations: HashMap::new(),
        }
    }

    /// Get read access to the registry
    pub fn registry(&self) -> &MacroRegistry {
        &self.registry
    }

    /// Get mutable access to the registry
    pub fn registry_mut(&mut self) -> &mut MacroRegistry {
        &mut self.registry
    }

    /// Enable or disable hygienic expansion
    pub fn set_hygienic(&mut self, hygienic: bool) {
        self.hygienic = hygienic;
    }

    /// Get statistics from last expansion
    pub fn last_stats(&self) -> Option<&clean_macro::expand::ExpansionStats> {
        self.last_stats.as_ref()
    }

    /// Expand macros in syntax
    pub fn expand(&mut self, syntax: Syntax) -> MacroResult<Syntax> {
        if self.hygienic {
            let mut expander = HygienicExpander::new(&self.registry);
            let result = expander.expand(syntax)?;
            self.last_stats = Some(expander.stats().clone());
            Ok(result)
        } else {
            let mut expander = MacroExpander::new(&self.registry);
            let result = expander.expand(syntax)?;
            self.last_stats = Some(expander.stats().clone());
            Ok(result)
        }
    }

    /// Register a `macro_rules` declaration into the registry.
    pub fn register_macro_rules(
        &mut self,
        name: Option<&str>,
        arms: &[MacroArm],
    ) -> Result<(), MacroRegistrationError> {
        for (idx, arm) in arms.iter().enumerate() {
            let pattern_quote = surface_expr_to_syntax_quote(&arm.pattern)?;
            // A *computed* (`do`-block) RHS is evaluated at registration time to
            // the quotation it builds (the faithful subset in `computed_body`); a
            // computed body outside that subset DEFERS with a registration error
            // rather than being mis-lowered as a pure template. A pure-template
            // RHS returns `None` here and keeps the existing fast path unchanged.
            let expansion_quote =
                match computed_body::evaluate_computed_macro_body(&arm.pattern, &arm.expansion) {
                    Some(result) => result?,
                    None => surface_expr_to_syntax_quote(&arm.expansion)?,
                };

            let macro_name = name.map_or_else(|| format!("macro_rules_{idx}"), ToString::to_string);
            let target_kind = if matches!(
                (pattern_quote.syntax.kind(), arm.pattern.as_ref()),
                (Some(kind), SurfaceExpr::SyntaxQuote(_, content))
                    if kind == &SyntaxKind::antiquot() && content.starts_with('(')
            ) {
                SyntaxKind::paren()
            } else {
                pattern_quote
                    .syntax
                    .kind()
                    .cloned()
                    .unwrap_or_else(|| pattern_quote.category.clone())
            };

            let def = MacroDef::new(
                macro_name,
                target_kind,
                pattern_quote.syntax.clone(),
                expansion_quote,
            );
            self.registry.register(def);
        }

        Ok(())
    }

    /// Register a new syntax category (`declare_syntax_cat`).
    pub fn register_syntax_category(&mut self, name: &str) {
        use clean_macro::registry::SyntaxCategory;
        self.categories.register(SyntaxCategory::new(name));
    }

    /// Check if a syntax category exists.
    pub fn has_syntax_category(&self, name: &str) -> bool {
        self.categories.exists(name)
    }

    /// Register a `syntax` declaration.
    ///
    /// This creates a macro that matches the syntax pattern and produces
    /// an AST node in the specified category.
    pub fn register_syntax(
        &mut self,
        name: Option<&str>,
        precedence: Option<u32>,
        pattern: &[SyntaxPatternItem],
        category: &str,
    ) -> Result<(), MacroRegistrationError> {
        // Build a pattern syntax from the pattern items
        let pattern_syntax = syntax_pattern_to_syntax(pattern);

        // The target kind is based on the pattern's leading literal/variable
        let target_kind = pattern_kind_from_items(pattern);

        // For syntax declarations, the expansion just wraps in the category
        let expansion = SyntaxQuote::new(pattern_syntax.clone(), SyntaxKind::app(category));

        let macro_name = name.map_or_else(
            || format!("syntax_{}", pattern_to_name(pattern)),
            ToString::to_string,
        );

        let mut def = MacroDef::new(macro_name, target_kind, pattern_syntax, expansion);
        if let Some(prec) = precedence {
            def = def.with_priority(prec as i32);
        }
        self.registry.register(def);

        Ok(())
    }

    /// Register a `notation` declaration (infixl, infixr, prefix, postfix, or notation).
    pub fn register_notation(
        &mut self,
        kind: NotationKind,
        precedence: Option<u32>,
        pattern: &[NotationItem],
        expansion: &SurfaceExpr,
    ) -> Result<(), MacroRegistrationError> {
        let expansion_quote = surface_expr_to_syntax_quote(expansion)?;

        // Build pattern syntax from notation items
        let (pattern_syntax, target_kind, var_names) = notation_pattern_to_syntax(kind, pattern);

        // Create macro name from pattern literals
        let macro_name = notation_to_name(kind, pattern);

        // Build the actual expansion: apply the expansion expression to variables
        let actual_expansion = if var_names.is_empty() {
            expansion_quote
        } else {
            // The expansion becomes: expansion var1 var2 ...
            let base = expansion_quote.syntax;
            let applied = var_names.iter().fold(base, |acc, var| {
                Syntax::mk_app(acc, vec![Syntax::mk_antiquot(var)])
            });
            SyntaxQuote::new(applied, expansion_quote.category)
        };

        let mut def = MacroDef::new(macro_name, target_kind, pattern_syntax, actual_expansion);
        if let Some(prec) = precedence {
            def = def.with_priority(prec as i32);
        }
        self.registry.register(def);

        if matches!(kind, NotationKind::Notation) && var_names.is_empty() {
            if let [NotationItem::Literal(literal)] = pattern {
                self.simple_notations
                    .insert(literal.trim().to_owned(), expansion.clone());
            }
        }

        Ok(())
    }

    /// Register a `macro` declaration (simple form with single pattern).
    pub fn register_macro(
        &mut self,
        pattern: &[SyntaxPatternItem],
        _category: &str,
        expansion: &SurfaceExpr,
    ) -> Result<(), MacroRegistrationError> {
        let expansion_quote = surface_expr_to_syntax_quote(expansion)?;
        let macro_name = format!("macro_{}", pattern_to_name(pattern));

        // A `macro "kw" a b : cat => rhs` command declares a leading-keyword syntax
        // whose USE site `kw a b` Clean parses as an application `App(ident kw, [a, b])`
        // (Clean does not extend its surface grammar dynamically). Lower the pattern
        // into that same application shape — head `ident kw`, arguments as
        // antiquotations — so it is keyed under `app_kind()` and matches the use site
        // exactly the way `macro_rules` / `notation` patterns already do.
        //
        // The prior lowering used the `syntax`-declaration helpers, producing a `seq`
        // node keyed under `app("kw")` — a kind the use site never has — so the macro
        // could never fire (`kw a b` stayed an unresolved ident). See
        // `register_macro_rules`, which is correct because it lowers from the parsed
        // quotation into the same application shape.
        if let Some((keyword, vars)) = leading_keyword_macro_form(pattern) {
            let pattern_syntax = Syntax::mk_app(
                Syntax::ident(&keyword),
                vars.iter().map(|v| Syntax::mk_antiquot(v)).collect(),
            );
            let target_kind = pattern_syntax
                .kind()
                .cloned()
                .unwrap_or_else(SyntaxKind::app_kind);
            let def = MacroDef::new(macro_name, target_kind, pattern_syntax, expansion_quote);
            self.registry.register(def);
            return Ok(());
        }

        // Fallback for shapes without a plain-application use site (nullary keyword,
        // mixfix, bracketed, repetition): keep the prior lowering. These are not yet
        // matched at the use site and fail loudly (`UnknownIdent`) rather than
        // mis-expanding — never silently wrong.
        let pattern_syntax = syntax_pattern_to_syntax(pattern);
        let target_kind = pattern_kind_from_items(pattern);
        let def = MacroDef::new(macro_name, target_kind, pattern_syntax, expansion_quote);
        self.registry.register(def);

        Ok(())
    }
}

/// Recognize the leading-keyword *application* form of a `macro` pattern: a single
/// literal keyword followed by one or more variables (`macro "twice" x : term => …`,
/// `macro "addup" x y : term => …`). Returns the keyword and the ordered variable
/// names. Returns `None` for mixfix / bracketed / category-ref / repetition patterns,
/// and for the nullary keyword form (`macro "kw" : term => …`) whose bare-ident use
/// site resolves before macro expansion — those have no plain-application use site to
/// key on and are left to the fallback (loud `UnknownIdent`, never mis-expansion).
fn leading_keyword_macro_form(pattern: &[SyntaxPatternItem]) -> Option<(String, Vec<String>)> {
    let mut keyword: Option<String> = None;
    let mut vars: Vec<String> = Vec::new();
    let mut seen_var = false;
    for item in pattern {
        match item {
            // Precedence is metadata, not part of the matched shape.
            SyntaxPatternItem::Precedence(_) => {}
            SyntaxPatternItem::Literal(lit) => {
                // The keyword must be the single leading literal, before any variable.
                if keyword.is_some() || seen_var {
                    return None;
                }
                keyword = Some(lit.trim().to_owned());
            }
            SyntaxPatternItem::Variable { name, .. } => {
                seen_var = true;
                vars.push(name.clone());
            }
            // CategoryRef / Optional / Repetition are not the simple application form.
            _ => return None,
        }
    }
    match keyword {
        Some(k) if !vars.is_empty() => Some((k, vars)),
        _ => None,
    }
}

// ============================================================================
// Level expression conversion (shared by both directions)
// ============================================================================

/// Convert a level expression to syntax for macro transport.
pub(crate) fn level_to_syntax(level: &LevelExpr) -> Syntax {
    match level {
        LevelExpr::Lit(n) => Syntax::node(
            SyntaxKind::app("levelLit"),
            vec![Syntax::mk_num(u64::from(*n))],
        ),
        LevelExpr::Param(name) => {
            Syntax::node(SyntaxKind::app("levelParam"), vec![Syntax::ident(name)])
        }
        LevelExpr::Succ(inner) => {
            Syntax::node(SyntaxKind::app("levelSucc"), vec![level_to_syntax(inner)])
        }
        LevelExpr::Max(a, b) => Syntax::node(
            SyntaxKind::app("levelMax"),
            vec![level_to_syntax(a), level_to_syntax(b)],
        ),
        LevelExpr::IMax(a, b) => Syntax::node(
            SyntaxKind::app("levelIMax"),
            vec![level_to_syntax(a), level_to_syntax(b)],
        ),
        LevelExpr::Antiquot(name) => {
            // Level antiquotation: $u in universe context
            Syntax::node(SyntaxKind::app("levelAntiquot"), vec![Syntax::ident(name)])
        }
    }
}

/// Convert macro syntax back into a level expression.
pub(crate) fn syntax_to_level(syntax: &Syntax) -> Option<LevelExpr> {
    let kind = syntax.kind()?;
    match kind.name_str() {
        "levelLit" => {
            // The child is a "num" node containing an atom with the value
            let num_node = syntax.child(0)?;
            let value = if let Some(atom_val) = num_node.as_atom() {
                // Direct atom (shouldn't happen, but handle it)
                atom_val.parse::<u64>().ok()?
            } else if num_node.kind().map(SyntaxKind::name_str) == Some("num") {
                // It's a "num" node - extract the atom child
                num_node.child(0)?.as_atom()?.parse::<u64>().ok()?
            } else {
                return None;
            };
            Some(LevelExpr::Lit(value as u32))
        }
        "levelParam" => syntax
            .child(0)?
            .as_ident()
            .map(|s| LevelExpr::Param(s.to_string())),
        "levelSucc" => Some(LevelExpr::Succ(Box::new(syntax_to_level(
            syntax.child(0)?,
        )?))),
        "levelMax" => Some(LevelExpr::Max(
            Box::new(syntax_to_level(syntax.child(0)?)?),
            Box::new(syntax_to_level(syntax.child(1)?)?),
        )),
        "levelIMax" => Some(LevelExpr::IMax(
            Box::new(syntax_to_level(syntax.child(0)?)?),
            Box::new(syntax_to_level(syntax.child(1)?)?),
        )),
        "levelAntiquot" => syntax
            .child(0)?
            .as_ident()
            .map(|s| LevelExpr::Antiquot(s.to_string())),
        _ => None,
    }
}

// ============================================================================
// High-level expansion API
// ============================================================================

/// Expand macros in a surface expression
///
/// This converts the expression to macro syntax, expands macros,
/// and converts back to a surface expression for elaboration.
pub fn expand_surface_macros(
    ctx: &mut MacroCtx,
    expr: &SurfaceExpr,
) -> Result<SurfaceExpr, MacroExpansionError> {
    let expr = expand_simple_notation_aliases(ctx, expr);

    // Convert to macro syntax
    let syntax = surface_to_syntax(&expr);

    // Expand macros
    let expanded = ctx
        .expand(syntax)
        .map_err(MacroExpansionError::MacroError)?;

    // Convert back to surface expression
    syntax_to_surface(&expanded).ok_or(MacroExpansionError::ConversionFailed)
}

fn expand_simple_notation_aliases(ctx: &MacroCtx, expr: &SurfaceExpr) -> SurfaceExpr {
    match expr {
        SurfaceExpr::Ident(_, name) => ctx
            .simple_notations
            .get(name)
            .cloned()
            .unwrap_or_else(|| expr.clone()),
        SurfaceExpr::App(span, func, args) => SurfaceExpr::App(
            *span,
            Box::new(expand_simple_notation_aliases(ctx, func)),
            args.iter()
                .map(|arg| SurfaceArg {
                    span: arg.span,
                    expr: expand_simple_notation_aliases(ctx, &arg.expr),
                    name: arg.name.clone(),
                })
                .collect(),
        ),
        SurfaceExpr::Paren(span, inner) => {
            SurfaceExpr::Paren(*span, Box::new(expand_simple_notation_aliases(ctx, inner)))
        }
        SurfaceExpr::Ascription(span, value, ty) => SurfaceExpr::Ascription(
            *span,
            Box::new(expand_simple_notation_aliases(ctx, value)),
            Box::new(expand_simple_notation_aliases(ctx, ty)),
        ),
        _ => expr.clone(),
    }
}

/// Error from macro expansion
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum MacroExpansionError {
    /// Macro expansion itself failed
    #[error("macro error: {0}")]
    MacroError(#[from] clean_macro::expand::MacroError),
    /// Could not convert expanded syntax back to surface expression
    #[error("could not convert expanded syntax to surface expression")]
    ConversionFailed,
}
