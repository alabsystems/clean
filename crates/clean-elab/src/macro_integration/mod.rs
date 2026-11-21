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
pub(crate) use registration::MacroRegistrationError;
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
// The declaration router (`infer::elaborate_decl`) reuses the `(cat| …)` head
// recognition to route `(tactic| …)` macros to tactic-position registration.
pub(crate) use registration::{macro_template_spellings, quotation_category_head};

use clean_macro::registry::SyntaxCategoryRegistry;
use clean_macro::{
    builtin_registry, HygienicExpander, MacroDef, MacroExpander, MacroRegistry, MacroResult,
    Syntax, SyntaxKind, SyntaxQuote,
};
use clean_parser::{
    LevelExpr, MacroArm, NotationItem, NotationKind, QAntiquotContent, Span, SurfaceArg,
    SurfaceExpr, SurfaceName, SyntaxPatternItem,
};
use std::collections::{HashMap, HashSet};

/// A nullary notation expansion plus the lexical section variables it captured.
///
/// Surface expressions carry identifier spellings but not Lean's syntax-scope
/// marks.  Retaining the stable FileContext identities here supplies the one
/// distinction that matters at the file boundary: after a captured variable's
/// scope ends, the alias is inert instead of rebinding its spelling to an
/// unrelated global or later section variable.
#[derive(Clone)]
struct SimpleNotationAlias {
    expansion: SurfaceExpr,
    captured_variable_ids: Vec<u64>,
}

enum SimpleNotationLookup<'a> {
    Active(&'a SurfaceExpr),
    /// Lean keeps the notation registered after a captured variable expires,
    /// but its hygienically marked reference is no longer resolvable.  Keep
    /// that state distinct from an absent alias: treating it as absent could
    /// let the notation literal be auto-bound as a fresh identifier.
    Expired,
}

// Types only used by tests via `use super::*`
#[cfg(test)]
use clean_parser::{
    Projection, QQuotationKind, SurfaceBinder, SurfaceBinderInfo, SurfaceFieldAssign, SurfaceLit,
    SurfaceMatchArm, SurfacePattern, UniverseExpr,
};

/// A `scoped notation` held against its declaring namespace (Lean attrKind
/// `scoped`, `Lean/Elab/Notation.lean`): it joins the LIVE expansion registry
/// only while that namespace is active — the current namespace (or an
/// ancestor of it) or explicitly activated by `open Ns` / `open scoped Ns`.
#[derive(Clone)]
struct ScopedNotation {
    /// Full declaring namespace path (e.g. `"Foo.Bar"`). Never empty: a
    /// root-level `scoped notation` is rejected at the declaration site.
    namespace: SurfaceName,
    /// The lowered macro definition, built eagerly at declaration time so a
    /// registration error surfaces at the declaration (fail closed) rather
    /// than at some later activation.
    def: MacroDef,
    /// For nullary literal notation (`scoped notation "x" => e`): the bare
    /// identifier alias, gated exactly like `simple_notations` but only while
    /// the declaring namespace is active.
    simple_alias: Option<(SurfaceName, SimpleNotationAlias)>,
}

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
    simple_notations: HashMap<SurfaceName, SimpleNotationAlias>,
    /// Active lexical section-variable identities, synchronized from the
    /// FileContext before each declaration is elaborated.
    active_variable_ids: HashSet<u64>,
    /// Innermost active identity for each spelling, used when a notation is
    /// registered to record exactly which binding its expansion captures.
    active_variable_by_name: HashMap<SurfaceName, u64>,
    /// `scoped notation` declarations, tagged with their declaring namespace.
    /// Kept OUT of `registry`; active ones are merged into
    /// `effective_registry` on every activation-state change.
    scoped_notations: Vec<ScopedNotation>,
    /// Activation frames for `open Ns` / `open scoped Ns`. One frame per
    /// namespace / section / `open … in` scope; the root frame (index 0,
    /// always present) holds file-level activations.
    scoped_activation_frames: Vec<Vec<SurfaceName>>,
    /// The current namespace path (empty at root). The current namespace and
    /// every dot-prefix of it activate their scoped notations implicitly,
    /// mirroring Lean's `activeScopes` (currNamespace + its prefixes).
    current_namespace: SurfaceName,
    /// Cache: `registry` plus the currently-active scoped notations. `None`
    /// when no scoped notation is active (the common case), so `expand` pays
    /// nothing for files without scoped notation.
    effective_registry: Option<MacroRegistry>,
    /// The `notation` command being registered, while the elaborator
    /// registers it ([`MacroCtx::set_template_site`]): the site its
    /// template's free references carry (`clean_parser::TemplateOrigin::site`).
    template_site: Option<clean_parser::TemplateSiteId>,
    /// Whether the template being registered carries its expansions' macro
    /// scope ([`MacroCtx::set_template_hygiene`]): `false` under `set_option
    /// hygiene false`.
    template_hygienic: bool,
}

impl Default for MacroCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl MacroCtx {
    /// Create a new macro context with built-in macros
    pub fn new() -> Self {
        Self::with_registry(builtin_registry())
    }

    /// Create with a custom registry
    pub(crate) fn with_registry(registry: MacroRegistry) -> Self {
        Self {
            registry,
            categories: SyntaxCategoryRegistry::new(),
            hygienic: true,
            last_stats: None,
            simple_notations: HashMap::new(),
            active_variable_ids: HashSet::new(),
            active_variable_by_name: HashMap::new(),
            template_site: None,
            template_hygienic: true,
            scoped_notations: Vec::new(),
            scoped_activation_frames: vec![Vec::new()],
            current_namespace: SurfaceName::from_name(clean_kernel::Name::anon()),
            effective_registry: None,
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
        // Active scoped notations expand through the merged effective
        // registry; without any, the base registry is used unchanged.
        let registry = self.effective_registry.as_ref().unwrap_or(&self.registry);
        if self.hygienic {
            let mut expander = HygienicExpander::new(registry);
            let result = expander.expand(syntax)?;
            self.last_stats = Some(expander.stats().clone());
            Ok(result)
        } else {
            let mut expander = MacroExpander::new(registry);
            let result = expander.expand(syntax)?;
            self.last_stats = Some(expander.stats().clone());
            Ok(result)
        }
    }

    // -----------------------------------------------------------------------
    // Scoped-notation gating (Lean attrKind `scoped`)
    // -----------------------------------------------------------------------

    /// Set the current namespace path (empty at root). The current namespace
    /// and its dot-prefixes implicitly activate their scoped notations.
    pub(crate) fn set_current_namespace(&mut self, namespace: &SurfaceName) {
        if &self.current_namespace != namespace {
            self.current_namespace = namespace.clone();
            self.rebuild_effective_registry();
        }
    }

    /// Push a new activation frame (namespace / section / `open … in` scope).
    pub(crate) fn push_scoped_activation_frame(&mut self) {
        self.scoped_activation_frames.push(Vec::new());
    }

    /// Pop the innermost activation frame, deactivating the `open` /
    /// `open scoped` activations made inside it. The root frame is never
    /// popped — an unbalanced pop clears it instead of underflowing.
    pub(crate) fn pop_scoped_activation_frame(&mut self) {
        if self.scoped_activation_frames.len() > 1 {
            self.scoped_activation_frames.pop();
        } else if let Some(root) = self.scoped_activation_frames.last_mut() {
            root.clear();
        }
        self.rebuild_effective_registry();
    }

    /// Activate a namespace's scoped notations in the innermost frame
    /// (`open Ns` / `open scoped Ns`). Activating a namespace that declared
    /// no scoped notation is a harmless no-op, matching Lean's tolerant
    /// `open scoped` of an arbitrary namespace.
    pub(crate) fn activate_scoped_namespace(&mut self, namespace: &SurfaceName) {
        if namespace.name().is_anon() {
            return;
        }
        if let Some(frame) = self.scoped_activation_frames.last_mut() {
            frame.push(namespace.clone());
        }
        self.rebuild_effective_registry();
    }

    /// Whether `namespace`'s scoped notations are active: it is the current
    /// namespace, a dot-prefix of it, or explicitly activated by an `open`.
    fn scoped_namespace_active(&self, namespace: &SurfaceName) -> bool {
        let mut current = self.current_namespace.name();
        loop {
            if current == namespace.name() {
                return true;
            }
            match current.inner() {
                clean_kernel::name::NameInner::Str(prefix, _)
                | clean_kernel::name::NameInner::Num(prefix, _) => current = prefix,
                clean_kernel::name::NameInner::Anon => break,
            }
        }
        self.scoped_activation_frames
            .iter()
            .flatten()
            .any(|active| active == namespace)
    }

    /// Rebuild the effective registry from the base registry plus the
    /// currently-active scoped notations. Called on every change to the base
    /// registry, the scoped-notation set, or the activation state.
    fn rebuild_effective_registry(&mut self) {
        let mut active_defs: Vec<MacroDef> = Vec::new();
        for scoped in &self.scoped_notations {
            if self.scoped_namespace_active(&scoped.namespace) {
                active_defs.push(scoped.def.clone());
            }
        }
        if active_defs.is_empty() {
            self.effective_registry = None;
            return;
        }
        let mut registry = self.registry.clone();
        for def in active_defs {
            registry.register(def);
        }
        self.effective_registry = Some(registry);
    }

    /// Synchronize the lexical section-variable bindings visible at the current
    /// source position.  Later entries with the same spelling are innermost.
    pub(crate) fn set_active_variable_bindings(
        &mut self,
        bindings: impl IntoIterator<Item = (SurfaceName, u64)>,
    ) {
        self.active_variable_ids.clear();
        self.active_variable_by_name.clear();
        for (name, id) in bindings {
            self.active_variable_ids.insert(id);
            self.active_variable_by_name.insert(name, id);
        }
    }

    fn alias_is_active(&self, alias: &SimpleNotationAlias) -> bool {
        alias
            .captured_variable_ids
            .iter()
            .all(|id| self.active_variable_ids.contains(id))
    }

    fn alias_expansion<'a>(&self, alias: &'a SimpleNotationAlias) -> SimpleNotationLookup<'a> {
        if self.alias_is_active(alias) {
            SimpleNotationLookup::Active(&alias.expansion)
        } else {
            SimpleNotationLookup::Expired
        }
    }

    /// Add the free identifiers introduced by active nullary aliases referenced
    /// by `names`, recursively.  Declaration preprocessing uses this closure so
    /// a theorem mentioning `A`, where `notation "A" => id x`, includes the
    /// captured section binder `x` in its kernel telescope.
    pub(crate) fn close_over_simple_notation_dependencies(&self, names: &mut HashSet<SurfaceName>) {
        loop {
            let mut introduced = HashSet::new();
            for name in names.iter() {
                if let Some(SimpleNotationLookup::Active(expansion)) =
                    self.lookup_simple_notation(name)
                {
                    introduced.extend(crate::where_desugar_ext::collect_free_idents(expansion));
                }
            }
            let before = names.len();
            names.extend(introduced);
            if names.len() == before {
                break;
            }
        }
    }

    fn capture_simple_alias(&self, expansion: SurfaceExpr) -> SimpleNotationAlias {
        let mut referenced = crate::where_desugar_ext::collect_free_idents(&expansion);
        self.close_over_simple_notation_dependencies(&mut referenced);
        let mut captured_variable_ids: Vec<u64> = referenced
            .iter()
            .filter_map(|name| self.active_variable_by_name.get(name).copied())
            .collect();
        captured_variable_ids.sort_unstable();
        captured_variable_ids.dedup();
        SimpleNotationAlias {
            expansion,
            captured_variable_ids,
        }
    }

    /// Look up a nullary-notation alias for a bare identifier: the file-scoped
    /// table first, then ACTIVE scoped-notation aliases.
    fn lookup_simple_notation(&self, name: &SurfaceName) -> Option<SimpleNotationLookup<'_>> {
        if let Some(alias) = self.simple_notations.get(name) {
            return Some(self.alias_expansion(alias));
        }
        self.scoped_notations.iter().find_map(|scoped| {
            scoped
                .simple_alias
                .as_ref()
                .filter(|(literal, _)| {
                    literal == name && self.scoped_namespace_active(&scoped.namespace)
                })
                .map(|(_, alias)| self.alias_expansion(alias))
        })
    }

    /// Name the `notation` command whose template is about to be registered
    /// (`None` once it is): its free references then carry that site, and
    /// resolve to what the elaborator recorded there.
    pub(crate) fn set_template_site(&mut self, site: Option<clean_parser::TemplateSiteId>) {
        self.template_site = site;
    }

    /// Whether the template about to be registered is hygienic (`true`
    /// unless declared under `set_option hygiene false`, where Lean's
    /// quotation adds no macro scope and pre-resolves nothing: its names
    /// resolve at each use, and its binders capture).
    pub(crate) fn set_template_hygiene(&mut self, hygienic: bool) {
        self.template_hygienic = hygienic;
    }

    /// A macro template over the operand variables `operands` with its free
    /// references marked hygienic against the CURRENT declaration site
    /// ([`clean_parser::mark_template_free_references`]): the namespace, the
    /// section variables in scope, and the site the elaborator recorded.
    pub(crate) fn mark_template(
        &self,
        template: &SurfaceExpr,
        operands: &[SurfaceName],
        site: clean_parser::TemplateSiteId,
    ) -> Result<SurfaceExpr, clean_parser::TemplateRefusal> {
        let section_variables: Vec<SurfaceName> =
            self.active_variable_by_name.keys().cloned().collect();
        clean_parser::mark_template_free_references(
            template,
            operands,
            self.current_namespace.name(),
            &section_variables,
            Some(site),
        )
    }

    /// Lower a macro's expansion template with its free references marked
    /// hygienic against the CURRENT declaration site: the namespace and the
    /// section variables in scope where the macro is declared.
    fn expansion_quote(
        &self,
        expansion: &SurfaceExpr,
    ) -> Result<SyntaxQuote, MacroRegistrationError> {
        if !self.template_hygienic {
            return surface_expr_to_syntax_quote(expansion);
        }
        let section_variables: Vec<SurfaceName> =
            self.active_variable_by_name.keys().cloned().collect();
        let namespace = self.current_namespace.name().clone();
        registration::surface_expr_to_expansion_quote(
            expansion,
            &registration::TemplateSite {
                namespace: &namespace,
                section_variables: &section_variables,
                site: self.template_site,
            },
        )
    }

    /// Register a `macro_rules` declaration into the registry.
    pub(crate) fn register_macro_rules(
        &mut self,
        name: Option<&SurfaceName>,
        arms: &[MacroArm],
    ) -> Result<(), MacroRegistrationError> {
        let mut refused = None;
        for (idx, arm) in arms.iter().enumerate() {
            let pattern_quote = surface_expr_to_syntax_quote(&arm.pattern)?;
            // A *computed* (`do`-block) RHS is evaluated at registration time to
            // the quotation it builds (the faithful subset in `computed_body`); a
            // computed body outside that subset DEFERS with a registration error
            // rather than being mis-lowered as a pure template. A pure-template
            // RHS returns `None` here and keeps the existing fast path unchanged.
            // A template the hygiene walk refuses registers a refusing
            // expansion, so a use is refused rather than read as other syntax,
            // and the declaration reports the refusal.
            let expansion_quote =
                match computed_body::evaluate_computed_macro_body(&arm.pattern, &arm.expansion) {
                    Some(result) => result?,
                    None => match self.expansion_quote(&arm.expansion) {
                        Err(MacroRegistrationError::TemplateRefused(reason)) => {
                            let quote = registration::refused_expansion_quote(&reason);
                            refused.get_or_insert(MacroRegistrationError::TemplateRefused(reason));
                            quote
                        }
                        other => other?,
                    },
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
            )
            .with_hygiene(self.template_hygienic);
            self.registry.register(def);
        }

        self.rebuild_effective_registry();
        refused.map_or(Ok(()), Err)
    }

    /// Register a new syntax category (`declare_syntax_cat`).
    pub(crate) fn register_syntax_category(&mut self, name: &str) {
        use clean_macro::registry::SyntaxCategory;
        self.categories.register(SyntaxCategory::new(name));
    }

    /// Register a source category only when its typed name is one string component.
    /// Escaping does not change category identity; qualification and numeric Name
    /// components cannot be represented by the current category-label protocol.
    pub(crate) fn register_typed_syntax_category(
        &mut self,
        name: &SurfaceName,
    ) -> Result<(), MacroRegistrationError> {
        let label = name
            .component_text()
            .filter(|_| !name.is_relative_constructor())
            .ok_or(MacroRegistrationError::SyntaxCategoryName)?;
        self.register_syntax_category(label);
        Ok(())
    }

    /// Check if a syntax category exists.
    pub fn has_syntax_category(&self, name: &str) -> bool {
        self.categories.exists(name)
    }

    /// Register a `syntax` declaration.
    ///
    /// This creates a macro that matches the syntax pattern and produces
    /// an AST node in the specified category.
    pub(crate) fn register_syntax(
        &mut self,
        name: Option<&SurfaceName>,
        priority: Option<&clean_kernel::BigNat>,
        pattern: &[SyntaxPatternItem],
        category: &str,
    ) -> Result<(), MacroRegistrationError> {
        // Build a pattern syntax from the pattern items
        let pattern_syntax = syntax_pattern_to_syntax(pattern);

        // The target kind is based on the pattern's leading literal/variable
        let target_kind = pattern_kind_from_items(pattern);

        // For syntax declarations, the expansion just wraps in the category
        let expansion = SyntaxQuote::new(
            pattern_syntax.clone(),
            SyntaxKind::from_name(clean_kernel::Name::anon().str(category)),
        );

        let macro_name = name.map_or_else(
            || format!("syntax_{}", pattern_to_name(pattern)),
            ToString::to_string,
        );

        let def = MacroDef::new(macro_name, target_kind, pattern_syntax, expansion)
            .with_syntax_priority(priority.unwrap_or(&clean_kernel::BigNat::Small(1000)));
        self.registry.register(def);

        self.rebuild_effective_registry();
        Ok(())
    }

    /// Lower a `notation` declaration into its macro definition plus (for the
    /// nullary literal form) the bare-identifier alias. Shared by the global
    /// and scoped registration paths so both fail closed at the declaration.
    fn build_notation_def(
        &self,
        kind: NotationKind,
        precedence: Option<u32>,
        pattern: &[NotationItem],
        expansion: &SurfaceExpr,
    ) -> Result<(MacroDef, Option<(SurfaceName, SurfaceExpr)>), MacroRegistrationError> {
        // The template's free references resolve where the notation is
        // declared, never to a binder at the use site; its pattern variables
        // are the operands (`clean_parser::mark_template_free_references`).
        let operands: Vec<SurfaceName> = pattern
            .iter()
            .filter_map(|item| match item {
                NotationItem::Variable(v) => Some(v.clone()),
                NotationItem::Literal(_) => None,
            })
            .collect();
        let section_variables: Vec<SurfaceName> =
            self.active_variable_by_name.keys().cloned().collect();
        let marked;
        let expansion = if self.template_hygienic {
            marked = clean_parser::mark_template_free_references(
                expansion,
                &operands,
                self.current_namespace.name(),
                &section_variables,
                self.template_site,
            )
            .map_err(|refusal| MacroRegistrationError::refused(&refusal))?;
            &marked
        } else {
            expansion
        };

        // Build pattern syntax from notation items
        let (pattern_syntax, target_kind, var_names) = notation_pattern_to_syntax(kind, pattern);

        // Create macro name from pattern literals
        let macro_name = notation_to_name(kind, pattern);

        // A `notation` template is a quotation over its operand variables: a
        // use SUBSTITUTES the caller's syntax for them
        // (`clean_parser::instantiate_notation_template`, with each operand an
        // antiquotation), never applies the template to it. Where an operand
        // stands in an identifier-only position (a binder, a pattern variable),
        // which an antiquotation cannot fill in Clean's surface syntax, the
        // registered expansion refuses every use instead. The fixed-arity
        // commands (`infixl " ** " => f`) name no operands: their head is
        // applied to them, which is their expansion in Lean.
        let actual_expansion = if var_names.is_empty() {
            surface_expr_to_syntax_quote(expansion)?
        } else if matches!(kind, NotationKind::Notation) {
            let antiquotations: Vec<SurfaceExpr> = var_names
                .iter()
                .map(|var| SurfaceExpr::QAntiquot {
                    span: Span::dummy(),
                    content: QAntiquotContent::Simple(var.clone()),
                })
                .collect();
            let instantiated = if self.template_hygienic {
                clean_parser::instantiate_notation_template(expansion, &var_names, &antiquotations)
            } else {
                clean_parser::instantiate_unhygienic_notation_template(
                    expansion,
                    &var_names,
                    &antiquotations,
                )
            };
            match instantiated {
                Ok(instantiated) => surface_expr_to_syntax_quote(&instantiated)?,
                Err(refusal) => registration::refused_expansion_quote(refusal.reason()),
            }
        } else {
            let base = surface_expr_to_syntax_quote(expansion)?;
            let applied = var_names.iter().fold(base.syntax, |acc, var| {
                Syntax::mk_app(acc, vec![Syntax::mk_antiquot(var)])
            });
            SyntaxQuote::new(applied, base.category)
        };

        let mut def = MacroDef::new(macro_name, target_kind, pattern_syntax, actual_expansion)
            .with_hygiene(self.template_hygienic);
        if let Some(prec) = precedence {
            def = def.with_priority(prec as i32);
        }

        let simple_alias = if matches!(kind, NotationKind::Notation) && var_names.is_empty() {
            match pattern {
                [NotationItem::Literal(literal)] => clean_parser::parse_name(literal.trim())
                    .ok()
                    .map(|name| (name, expansion.clone())),
                _ => None,
            }
        } else {
            None
        };

        Ok((def, simple_alias))
    }

    /// Register a `notation` declaration (infixl, infixr, prefix, postfix, or notation).
    pub(crate) fn register_notation(
        &mut self,
        kind: NotationKind,
        precedence: Option<u32>,
        pattern: &[NotationItem],
        expansion: &SurfaceExpr,
    ) -> Result<(), MacroRegistrationError> {
        let (def, simple_alias) = self.build_notation_def(kind, precedence, pattern, expansion)?;
        self.registry.register(def);
        if let Some((literal, alias_expansion)) = simple_alias {
            let alias = self.capture_simple_alias(alias_expansion);
            self.simple_notations.insert(literal, alias);
        }
        self.rebuild_effective_registry();
        Ok(())
    }

    /// Register a `scoped notation` against its declaring namespace. The
    /// definition is lowered eagerly (fail closed at the declaration) but
    /// only joins the live registry while `namespace` is active — the current
    /// namespace, an ancestor of it, or activated by `open` / `open scoped`.
    pub(crate) fn register_scoped_notation(
        &mut self,
        namespace: &SurfaceName,
        kind: NotationKind,
        precedence: Option<u32>,
        pattern: &[NotationItem],
        expansion: &SurfaceExpr,
    ) -> Result<(), MacroRegistrationError> {
        let (def, simple_alias) = self.build_notation_def(kind, precedence, pattern, expansion)?;
        let simple_alias = simple_alias
            .map(|(literal, expansion)| (literal, self.capture_simple_alias(expansion)));
        self.scoped_notations.push(ScopedNotation {
            namespace: namespace.clone(),
            def,
            simple_alias,
        });
        self.rebuild_effective_registry();
        Ok(())
    }

    /// Register a `macro` declaration (simple form with single pattern).
    pub(crate) fn register_macro(
        &mut self,
        pattern: &[SyntaxPatternItem],
        _category: &str,
        expansion: &SurfaceExpr,
    ) -> Result<(), MacroRegistrationError> {
        // A template the hygiene walk refuses registers a refusing expansion,
        // so a use is refused rather than read as other syntax, and the
        // declaration reports the refusal.
        let (expansion_quote, refused) = match self.expansion_quote(expansion) {
            Err(MacroRegistrationError::TemplateRefused(reason)) => (
                registration::refused_expansion_quote(&reason),
                Some(MacroRegistrationError::TemplateRefused(reason)),
            ),
            other => (other?, None),
        };
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
                vars.iter().map(Syntax::mk_antiquot).collect(),
            );
            let target_kind = pattern_syntax
                .kind()
                .cloned()
                .unwrap_or_else(SyntaxKind::app_kind);
            let def = MacroDef::new(macro_name, target_kind, pattern_syntax, expansion_quote)
                .with_hygiene(self.template_hygienic);
            self.registry.register(def);
            self.rebuild_effective_registry();
            return refused.map_or(Ok(()), Err);
        }

        // Fallback for shapes without a plain-application use site (nullary keyword,
        // mixfix, bracketed, repetition): keep the prior lowering. These are not yet
        // matched at the use site and fail loudly (`UnknownIdent`) rather than
        // mis-expanding — never silently wrong.
        let pattern_syntax = syntax_pattern_to_syntax(pattern);
        let target_kind = pattern_kind_from_items(pattern);
        let def = MacroDef::new(macro_name, target_kind, pattern_syntax, expansion_quote)
            .with_hygiene(self.template_hygienic);
        self.registry.register(def);

        self.rebuild_effective_registry();
        refused.map_or(Ok(()), Err)
    }
}

/// Recognize the leading-keyword *application* form of a `macro` pattern: a single
/// literal keyword followed by one or more variables (`macro "twice" x : term => …`,
/// `macro "addup" x y : term => …`). Returns the keyword and the ordered variable
/// names. Returns `None` for mixfix / bracketed / category-ref / repetition patterns,
/// and for the nullary keyword form (`macro "kw" : term => …`) whose bare-ident use
/// site resolves before macro expansion — those have no plain-application use site to
/// key on and are left to the fallback (loud `UnknownIdent`, never mis-expansion).
fn leading_keyword_macro_form(
    pattern: &[SyntaxPatternItem],
) -> Option<(SurfaceName, Vec<SurfaceName>)> {
    let mut keyword: Option<SurfaceName> = None;
    let mut vars: Vec<SurfaceName> = Vec::new();
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
                keyword = Some(clean_parser::parse_name(lit.trim()).ok()?);
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
            .map(|s| LevelExpr::Param(s.clone())),
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
            .map(|s| LevelExpr::Antiquot(s.clone())),
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
    let expr = expand_simple_notation_aliases(ctx, expr)?;

    // Convert to macro syntax
    let syntax = surface_to_syntax(&expr);

    // Expand macros
    let expanded = ctx
        .expand(syntax)
        .map_err(MacroExpansionError::MacroError)?;

    // Convert back to surface expression
    syntax_to_surface(&expanded).ok_or(MacroExpansionError::ConversionFailed)
}

/// Replace every active simple-notation alias in `expr`.
///
/// Every level of the walk is a `stack_safe` checkpoint. The walk recurses
/// over the SURFACE term, and `ElabCtx::elaborate` runs it BEFORE reaching its
/// own checkpoint, so unguarded it extended the stretch `elaborate` →
/// `elab_app_inner` → `elaborate_with_expected_type` → `elaborate` →
/// `expand_macros` by one iterator-adapter tower per nesting level. Measured
/// 2026-09-20 on a debug build: six levels of application nesting under that
/// stretch outgrew the 256 KB red zone (`MIN_STACK_RED_ZONE`), and
/// `codata_cmd_tests::test_codata_stream_encoding_survives_small_thread_stack`
/// aborted the whole test process with a stack overflow inside this function
/// (crash report: ~110 frames of this walk above the last `maybe_grow`).
/// Whether it faulted depended on where the previous checkpoint happened to
/// land — two sibling builds of the same walk passed — which is what an
/// inter-checkpoint stretch near the red zone looks like.
fn expand_simple_notation_aliases(
    ctx: &MacroCtx,
    expr: &SurfaceExpr,
) -> Result<SurfaceExpr, MacroExpansionError> {
    crate::stack_safe(|| expand_simple_notation_aliases_unguarded(ctx, expr))
}

/// One level of [`expand_simple_notation_aliases`]; recursion goes back through
/// the guarded entry.
fn expand_simple_notation_aliases_unguarded(
    ctx: &MacroCtx,
    expr: &SurfaceExpr,
) -> Result<SurfaceExpr, MacroExpansionError> {
    match expr {
        SurfaceExpr::Ident(_, name) => match ctx.lookup_simple_notation(name) {
            Some(SimpleNotationLookup::Active(expansion)) => Ok(expansion.clone()),
            Some(SimpleNotationLookup::Expired) => Err(
                MacroExpansionError::ExpiredNotationCapture(name.to_string()),
            ),
            None => Ok(expr.clone()),
        },
        SurfaceExpr::App(span, func, args) => Ok(SurfaceExpr::App(
            *span,
            Box::new(expand_simple_notation_aliases(ctx, func)?),
            args.iter()
                .map(|arg| {
                    Ok::<SurfaceArg, MacroExpansionError>(SurfaceArg {
                        span: arg.span,
                        expr: expand_simple_notation_aliases(ctx, &arg.expr)?,
                        name: arg.name.clone(),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?,
        )),
        SurfaceExpr::Paren(span, inner) => Ok(SurfaceExpr::Paren(
            *span,
            Box::new(expand_simple_notation_aliases(ctx, inner)?),
        )),
        SurfaceExpr::Ascription(span, value, ty) => Ok(SurfaceExpr::Ascription(
            *span,
            Box::new(expand_simple_notation_aliases(ctx, value)?),
            Box::new(expand_simple_notation_aliases(ctx, ty)?),
        )),
        _ => Ok(expr.clone()),
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
    /// A persistent notation refers to a lexical section variable whose scope
    /// has ended.  This is an unknown hygienic reference in Lean, not a fresh
    /// auto-bound identifier.
    #[error("Unknown identifier in expired notation capture: {0}")]
    ExpiredNotationCapture(String),
}
