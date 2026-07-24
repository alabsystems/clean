// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro registry and definitions
//!
//! The registry stores macro definitions and provides lookup during expansion.
//! Macros are keyed by the syntax kind they match.

use crate::quotation::SyntaxQuote;
use crate::syntax::{Syntax, SyntaxKind};
use std::collections::HashMap;
use std::sync::Arc;

/// A macro definition
#[derive(Debug, Clone)]
pub struct MacroDef {
    /// Name of the macro (for debugging)
    pub name: String,
    /// The syntax kind this macro matches
    pub kind: SyntaxKind,
    /// Pattern to match (may contain wildcards)
    pub pattern: Syntax,
    /// Replacement template (may contain antiquotations for captured values)
    pub replacement: SyntaxQuote,
    /// Priority (higher = tried first)
    pub priority: i32,
    /// Documentation string
    pub doc: Option<String>,
}

impl MacroDef {
    /// Create a new macro definition
    pub fn new(
        name: impl Into<String>,
        kind: SyntaxKind,
        pattern: Syntax,
        replacement: SyntaxQuote,
    ) -> Self {
        Self {
            name: name.into(),
            kind,
            pattern,
            replacement,
            priority: 0,
            doc: None,
        }
    }

    /// Set priority
    #[must_use]
    pub fn with_priority(mut self, priority: i32) -> Self {
        self.priority = priority;
        self
    }

    /// Set documentation
    #[must_use]
    pub fn with_doc(mut self, doc: impl Into<String>) -> Self {
        self.doc = Some(doc.into());
        self
    }

    /// Try to match this macro against syntax, returning bindings if successful
    pub fn try_match(&self, syntax: &Syntax) -> Option<HashMap<String, Syntax>> {
        match_pattern(&self.pattern, syntax)
    }

    /// Apply this macro to matched syntax
    pub fn apply(&self, bindings: &HashMap<String, Syntax>) -> Syntax {
        self.replacement.substitute(bindings)
    }

    /// Apply this macro hygienically: substitute matched antiquotations AND
    /// replace any fresh-name marker in the template with a distinct gensym'd
    /// identifier drawn from `hygiene`.
    ///
    /// For a template with no fresh markers this is byte-identical to
    /// [`MacroDef::apply`] (the common, static path is unchanged). For a computed
    /// body that introduced a `mkFreshId` / `addMacroScope` binder, each call
    /// advances the gensym counter, so two expansions of the same macro yield
    /// **distinct** fresh ids — the per-expansion freshness this enables.
    pub fn apply_hygienic(
        &self,
        bindings: &HashMap<String, Syntax>,
        hygiene: &mut crate::hygiene::HygieneState,
    ) -> Syntax {
        self.replacement.substitute_hygienic(bindings, hygiene)
    }
}

/// Match a pattern against syntax, returning captured bindings
fn match_pattern(pattern: &Syntax, syntax: &Syntax) -> Option<HashMap<String, Syntax>> {
    let mut bindings = HashMap::new();
    if match_pattern_inner(pattern, syntax, &mut bindings) {
        Some(bindings)
    } else {
        None
    }
}

fn match_pattern_inner(
    pattern: &Syntax,
    syntax: &Syntax,
    bindings: &mut HashMap<String, Syntax>,
) -> bool {
    // Simple antiquotation in pattern captures the corresponding syntax.
    //
    // A TYPED antiquotation (`$x:term`) only captures when the matched syntax
    // belongs to the declared category; an UNTYPED antiquotation (`$x`) still
    // captures any syntax. The category is the second child ident of a typed
    // antiquotation node (see `Syntax::mk_antiquot_typed`).
    if pattern.is_simple_antiquot() {
        if let Some(name) = pattern.children().first().and_then(|c| c.as_ident()) {
            if pattern.is_antiquot_typed() {
                // Enforce the declared category: bail out before binding if the
                // candidate syntax is not in the expected category.
                match pattern.children().get(1).and_then(|c| c.as_ident()) {
                    Some(category) if matches_category(category, syntax) => {}
                    // Missing or mismatched category annotation: no match.
                    _ => return false,
                }
            }
            bindings.insert(name.to_string(), syntax.clone());
            return true;
        }
        return false;
    }

    // Splice antiquotation should be handled at the node level (see match_children_with_splice)
    // If we encounter it here directly, it matches nothing
    if pattern.is_antiquot_splice() {
        return false;
    }

    // Missing pattern matches anything
    if pattern.is_missing() {
        return true;
    }

    match (pattern, syntax) {
        (Syntax::Ident(_, p_name), Syntax::Ident(_, s_name)) => p_name == s_name,

        (Syntax::Atom(_, p_val), Syntax::Atom(_, s_val)) => p_val == s_val,

        (Syntax::Node(p_node), Syntax::Node(s_node)) => {
            // Kinds must match
            if p_node.kind != s_node.kind {
                return false;
            }
            // Check if pattern has splice antiquotations
            let has_splice = p_node.children.iter().any(Syntax::is_antiquot_splice);
            if has_splice {
                // Use splice-aware matching
                match_children_with_splice(&p_node.children, &s_node.children, bindings)
            } else {
                // Children must match exactly
                if p_node.children.len() != s_node.children.len() {
                    return false;
                }
                for (p_child, s_child) in p_node.children.iter().zip(s_node.children.iter()) {
                    if !match_pattern_inner(p_child, s_child, bindings) {
                        return false;
                    }
                }
                true
            }
        }

        (Syntax::Missing(_), _) => true,

        _ => false,
    }
}

/// Match children with splice antiquotation support
/// A splice `$[x]*` matches zero or more consecutive children and binds them as a list
fn match_children_with_splice(
    pattern_children: &[Syntax],
    syntax_children: &[Syntax],
    bindings: &mut HashMap<String, Syntax>,
) -> bool {
    let mut p_idx = 0;
    let mut s_idx = 0;

    while p_idx < pattern_children.len() {
        let p_child = &pattern_children[p_idx];

        if p_child.is_antiquot_splice() {
            // Splice antiquotation: $[name]*
            // This greedily matches zero or more children
            if let Some(name) = p_child.children().first().and_then(|c| c.as_ident()) {
                // Determine how many syntax children to consume
                // Strategy: consume until next pattern element matches, or end of syntax
                let next_pattern = pattern_children.get(p_idx + 1);
                let mut end_idx = s_idx;

                if let Some(next_p) = next_pattern {
                    // Find where next pattern element matches
                    let mut found = false;
                    for i in s_idx..=syntax_children.len() {
                        if i == syntax_children.len() {
                            // Check if next pattern can match empty or is also a splice
                            if next_p.is_antiquot_splice() || next_p.is_missing() {
                                end_idx = syntax_children.len();
                                found = true;
                                break;
                            }
                        } else {
                            // Try matching next pattern at this position
                            let mut test_bindings = HashMap::new();
                            if match_pattern_inner(next_p, &syntax_children[i], &mut test_bindings)
                            {
                                end_idx = i;
                                found = true;
                                break;
                            }
                        }
                    }
                    if !found {
                        // Try consuming all remaining - the pattern may still work
                        end_idx = syntax_children.len();
                    }
                } else {
                    // No more patterns, consume all remaining syntax
                    end_idx = syntax_children.len();
                }

                // Collect matched children into a list node
                let matched: Vec<Syntax> = syntax_children[s_idx..end_idx].to_vec();
                let splice_result = Syntax::node(SyntaxKind::app("splice_list"), matched);
                bindings.insert(name.to_string(), splice_result);

                s_idx = end_idx;
            }
            p_idx += 1;
        } else {
            // Regular pattern element
            if s_idx >= syntax_children.len() {
                return false;
            }
            if !match_pattern_inner(p_child, &syntax_children[s_idx], bindings) {
                return false;
            }
            p_idx += 1;
            s_idx += 1;
        }
    }

    // All pattern elements consumed; check if all syntax children consumed
    // (unless there was a trailing splice that consumed them)
    s_idx == syntax_children.len()
}

/// Check whether `syntax` belongs to the syntax `category` declared by a typed
/// antiquotation (`$x:category`).
///
/// The mapping is intentionally permissive for the open-ended `term` category
/// (a term may be an identifier, application, literal, binder, etc.) and strict
/// for the narrow lexical categories (`ident`, `num`, `str`, ...). An unknown
/// category name is treated as "any" so that user-defined categories — which
/// the macro engine cannot introspect — keep matching as before; the
/// enforcement here targets the built-in categories that have a concrete shape.
fn matches_category(category: &str, syntax: &Syntax) -> bool {
    match category {
        // The term category covers essentially every expression-level node, an
        // identifier, or a literal. It explicitly excludes command/tactic nodes.
        "term" => is_term_syntax(syntax),
        // Identifier category: only bare identifiers.
        "ident" => syntax.is_ident(),
        // Numeric literals (`num`) and scientific/float literals.
        "num" | "numLit" => syntax_kind_is(syntax, &["num", "scientific"]),
        // String literals.
        "str" | "strLit" => syntax_kind_is(syntax, &["str"]),
        // Character literals.
        "char" | "charLit" => syntax_kind_is(syntax, &["char"]),
        // Command category: top-level command nodes.
        "command" => syntax_kind_is(syntax, &["command"]),
        // Tactic category: tactic nodes (and tactic sequences).
        "tactic" | "tacticSeq" => syntax_kind_is(syntax, &["tactic", "tacticSeq"]),
        // Unknown / user-defined category: keep matching anything so we never
        // regress custom categories the engine has no shape information for.
        _ => true,
    }
}

/// Whether `syntax` has a node kind whose name matches any of `names`.
fn syntax_kind_is(syntax: &Syntax, names: &[&str]) -> bool {
    syntax.kind().is_some_and(|k| names.contains(&k.name_str()))
}

/// Whether `syntax` is a term-category construct.
///
/// Terms are identifiers, literals, and the expression-shaped nodes
/// (application, lambda, forall, arrow, let, hole, paren). Command and tactic
/// nodes are deliberately rejected so that `$x:term` does not match them.
fn is_term_syntax(syntax: &Syntax) -> bool {
    match syntax {
        // Bare identifiers and atoms are terms.
        Syntax::Ident(_, _) | Syntax::Atom(_, _) => true,
        // Missing syntax is treated as a (placeholder) term.
        Syntax::Missing(_) => true,
        Syntax::Node(node) => matches!(
            node.kind.name_str(),
            "app"
                | "fun"
                | "forall"
                | "arrow"
                | "let"
                | "hole"
                | "paren"
                | "ident"
                | "num"
                | "str"
                | "scientific"
                | "char"
        ),
    }
}

/// Registry for macro definitions
#[derive(Debug, Clone, Default)]
pub struct MacroRegistry {
    /// Macros indexed by their target syntax kind
    macros: HashMap<SyntaxKind, Vec<Arc<MacroDef>>>,
    /// All macros by name (for lookup)
    by_name: HashMap<String, Arc<MacroDef>>,
}

impl MacroRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a macro definition
    pub fn register(&mut self, def: MacroDef) {
        let def = Arc::new(def);
        self.by_name.insert(def.name.clone(), Arc::clone(&def));

        let macros = self.macros.entry(def.kind.clone()).or_default();
        macros.push(def);

        // Keep macros sorted by priority (highest first)
        macros.sort_by_key(|b| std::cmp::Reverse(b.priority));
    }

    /// Look up a macro by name
    pub fn get_by_name(&self, name: &str) -> Option<&Arc<MacroDef>> {
        self.by_name.get(name)
    }

    /// Get all macros that could match a given syntax kind
    pub fn get_by_kind(&self, kind: &SyntaxKind) -> &[Arc<MacroDef>] {
        self.macros.get(kind).map_or(&[], |v| v.as_slice())
    }

    /// Find and apply the first matching macro
    pub fn try_expand(&self, syntax: &Syntax) -> Option<Syntax> {
        let kind = syntax.kind()?;
        let macros = self.get_by_kind(kind);

        for macro_def in macros {
            if let Some(bindings) = macro_def.try_match(syntax) {
                return Some(macro_def.apply(&bindings));
            }
        }

        None
    }

    /// Like [`MacroRegistry::try_expand`], but applies the matched macro
    /// hygienically so fresh-name markers in a computed-body template are
    /// gensym'd per expansion from `hygiene`. Static templates expand identically
    /// to [`MacroRegistry::try_expand`].
    pub fn try_expand_hygienic(
        &self,
        syntax: &Syntax,
        hygiene: &mut crate::hygiene::HygieneState,
    ) -> Option<Syntax> {
        let kind = syntax.kind()?;
        let macros = self.get_by_kind(kind);

        for macro_def in macros {
            if let Some(bindings) = macro_def.try_match(syntax) {
                return Some(macro_def.apply_hygienic(&bindings, hygiene));
            }
        }

        None
    }

    /// Get all registered macro names
    pub fn macro_names(&self) -> Vec<&str> {
        self.by_name.keys().map(String::as_str).collect()
    }

    /// Get count of registered macros
    pub fn len(&self) -> usize {
        self.by_name.len()
    }

    /// Check if registry is empty
    pub fn is_empty(&self) -> bool {
        self.by_name.is_empty()
    }
}

/// Syntax category registration
#[derive(Debug, Clone)]
pub struct SyntaxCategory {
    /// Category name
    pub name: String,
    /// Parser kind
    pub kind: SyntaxKind,
    /// Description
    pub description: Option<String>,
}

impl SyntaxCategory {
    pub fn new(name: impl Into<String>) -> Self {
        let name = name.into();
        Self {
            kind: SyntaxKind::app(&name),
            name,
            description: None,
        }
    }

    #[must_use]
    pub fn with_description(mut self, desc: impl Into<String>) -> Self {
        self.description = Some(desc.into());
        self
    }
}

/// Registry for syntax categories
#[derive(Debug, Clone, Default)]
pub struct SyntaxCategoryRegistry {
    categories: HashMap<String, SyntaxCategory>,
}

impl SyntaxCategoryRegistry {
    pub fn new() -> Self {
        let mut registry = Self::default();
        // Register built-in categories
        registry.register(SyntaxCategory::new("term").with_description("Term expressions"));
        registry.register(SyntaxCategory::new("command").with_description("Top-level commands"));
        registry.register(SyntaxCategory::new("tactic").with_description("Proof tactics"));
        registry.register(SyntaxCategory::new("doElem").with_description("Do notation elements"));
        registry.register(SyntaxCategory::new("attr").with_description("Attributes"));
        registry
    }

    /// Register a new syntax category
    pub fn register(&mut self, category: SyntaxCategory) {
        self.categories.insert(category.name.clone(), category);
    }

    /// Look up a category
    pub fn get(&self, name: &str) -> Option<&SyntaxCategory> {
        self.categories.get(name)
    }

    /// Check if a category exists
    pub fn exists(&self, name: &str) -> bool {
        self.categories.contains_key(name)
    }

    /// Get all category names
    pub fn names(&self) -> Vec<&str> {
        self.categories.keys().map(String::as_str).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_macro_def_creation() {
        let def = MacroDef::new(
            "test_macro",
            SyntaxKind::term(),
            Syntax::mk_antiquot("x"),
            SyntaxQuote::term(Syntax::ident("replaced")),
        );
        assert_eq!(def.name, "test_macro");
        assert_eq!(def.priority, 0);
    }

    #[test]
    fn test_pattern_matching_ident() {
        let pattern = Syntax::ident("foo");
        let syntax = Syntax::ident("foo");
        let bindings = match_pattern(&pattern, &syntax);
        let bindings = bindings.expect("ident 'foo' should match pattern 'foo'");
        assert!(bindings.is_empty());

        let syntax2 = Syntax::ident("bar");
        assert!(
            match_pattern(&pattern, &syntax2).is_none(),
            "'bar' should not match pattern 'foo'"
        );
    }

    #[test]
    fn test_pattern_matching_antiquot() {
        let pattern = Syntax::mk_antiquot("x");
        let syntax = Syntax::ident("anything");
        let bindings = match_pattern(&pattern, &syntax).unwrap();
        assert_eq!(bindings.len(), 1);
        assert!(bindings.contains_key("x"));
    }

    #[test]
    fn test_pattern_matching_node() {
        let pattern = Syntax::mk_app(Syntax::ident("f"), vec![Syntax::mk_antiquot("arg")]);
        let syntax = Syntax::mk_app(Syntax::ident("f"), vec![Syntax::ident("x")]);
        let bindings = match_pattern(&pattern, &syntax).unwrap();
        assert!(bindings.contains_key("arg"));
    }

    #[test]
    fn test_registry_register_and_lookup() {
        let mut registry = MacroRegistry::new();

        let def = MacroDef::new(
            "my_macro",
            SyntaxKind::term(),
            Syntax::mk_antiquot("x"),
            SyntaxQuote::term(Syntax::ident("result")),
        );

        registry.register(def);

        assert!(
            registry.get_by_name("my_macro").is_some(),
            "registered macro should be found by name"
        );
        assert_eq!(registry.len(), 1);
    }

    #[test]
    fn test_registry_try_expand() {
        let mut registry = MacroRegistry::new();

        // Register a macro that matches any term and replaces with "expanded"
        let kind = SyntaxKind::app_kind();
        let def = MacroDef::new(
            "expand_app",
            kind.clone(),
            Syntax::node(
                kind.clone(),
                vec![Syntax::ident("myMacro"), Syntax::mk_antiquot("arg")],
            ),
            SyntaxQuote::term(Syntax::mk_antiquot("arg")),
        );

        registry.register(def);

        let input = Syntax::node(kind, vec![Syntax::ident("myMacro"), Syntax::ident("hello")]);

        let result = registry.try_expand(&input);
        let expanded = result.expect("try_expand should match and expand the macro");
        assert_eq!(expanded.as_ident(), Some("hello"));
    }

    #[test]
    fn test_macro_priority() {
        let mut registry = MacroRegistry::new();

        let kind = SyntaxKind::term();

        let def1 = MacroDef::new(
            "low_priority",
            kind.clone(),
            Syntax::mk_antiquot("x"),
            SyntaxQuote::term(Syntax::ident("low")),
        )
        .with_priority(0);

        let def2 = MacroDef::new(
            "high_priority",
            kind.clone(),
            Syntax::mk_antiquot("x"),
            SyntaxQuote::term(Syntax::ident("high")),
        )
        .with_priority(100);

        registry.register(def1);
        registry.register(def2);

        let macros = registry.get_by_kind(&kind);
        assert_eq!(macros.len(), 2);
        assert_eq!(macros[0].name, "high_priority"); // Should be first due to higher priority
    }

    #[test]
    fn test_syntax_category_registry() {
        let registry = SyntaxCategoryRegistry::new();
        assert!(registry.exists("term"));
        assert!(registry.exists("command"));
        assert!(registry.exists("tactic"));
        assert!(!registry.exists("nonexistent"));
    }

    #[test]
    fn test_syntax_category_custom() {
        let mut registry = SyntaxCategoryRegistry::new();
        registry.register(SyntaxCategory::new("myCategory").with_description("Custom category"));

        assert!(registry.exists("myCategory"));
        let cat = registry.get("myCategory").unwrap();
        assert_eq!(cat.description, Some("Custom category".to_string()));
    }

    #[test]
    fn test_pattern_matching_splice_empty() {
        // Pattern: (f $[args]*)
        // Syntax: (f)
        // Should match with args = []
        let kind = SyntaxKind::app_kind();
        let pattern = Syntax::node(
            kind.clone(),
            vec![Syntax::ident("f"), Syntax::mk_antiquot_splice("args")],
        );
        let syntax = Syntax::node(kind, vec![Syntax::ident("f")]);

        let bindings = match_pattern(&pattern, &syntax);
        assert!(bindings.is_some(), "Pattern should match empty args");
        let bindings = bindings.unwrap();
        assert!(bindings.contains_key("args"));
        // args should be a splice_list with 0 children
        let args = &bindings["args"];
        assert_eq!(args.children().len(), 0);
    }

    #[test]
    fn test_pattern_matching_splice_multiple() {
        // Pattern: (f $[args]*)
        // Syntax: (f a b c)
        // Should match with args = [a, b, c]
        let kind = SyntaxKind::app_kind();
        let pattern = Syntax::node(
            kind.clone(),
            vec![Syntax::ident("f"), Syntax::mk_antiquot_splice("args")],
        );
        let syntax = Syntax::node(
            kind,
            vec![
                Syntax::ident("f"),
                Syntax::ident("a"),
                Syntax::ident("b"),
                Syntax::ident("c"),
            ],
        );

        let bindings = match_pattern(&pattern, &syntax);
        assert!(bindings.is_some(), "Pattern should match multiple args");
        let bindings = bindings.unwrap();
        let args = &bindings["args"];
        assert_eq!(args.children().len(), 3);
        assert_eq!(args.children()[0].as_ident(), Some("a"));
        assert_eq!(args.children()[1].as_ident(), Some("b"));
        assert_eq!(args.children()[2].as_ident(), Some("c"));
    }

    #[test]
    fn test_pattern_matching_splice_with_prefix() {
        // Pattern: (let $name $[exprs]*)
        // Syntax: (let x a b)
        // Should match with name = x, exprs = [a, b]
        let kind = SyntaxKind::app_kind();
        let pattern = Syntax::node(
            kind.clone(),
            vec![
                Syntax::ident("let"),
                Syntax::mk_antiquot("name"),
                Syntax::mk_antiquot_splice("exprs"),
            ],
        );
        let syntax = Syntax::node(
            kind,
            vec![
                Syntax::ident("let"),
                Syntax::ident("x"),
                Syntax::ident("a"),
                Syntax::ident("b"),
            ],
        );

        let bindings = match_pattern(&pattern, &syntax);
        assert!(bindings.is_some(), "Pattern should match with prefix");
        let bindings = bindings.unwrap();
        assert_eq!(bindings["name"].as_ident(), Some("x"));
        let exprs = &bindings["exprs"];
        assert_eq!(exprs.children().len(), 2);
    }

    #[test]
    fn test_pattern_matching_splice_with_suffix() {
        // Pattern: (fn $[args]* => $body)
        // Syntax: (fn x y => z)
        // Should match with args = [x, y], body = z
        let kind = SyntaxKind::app_kind();
        let pattern = Syntax::node(
            kind.clone(),
            vec![
                Syntax::ident("fn"),
                Syntax::mk_antiquot_splice("args"),
                Syntax::ident("=>"),
                Syntax::mk_antiquot("body"),
            ],
        );
        let syntax = Syntax::node(
            kind,
            vec![
                Syntax::ident("fn"),
                Syntax::ident("x"),
                Syntax::ident("y"),
                Syntax::ident("=>"),
                Syntax::ident("z"),
            ],
        );

        let bindings = match_pattern(&pattern, &syntax);
        assert!(bindings.is_some(), "Pattern should match with suffix");
        let bindings = bindings.unwrap();
        let args = &bindings["args"];
        assert_eq!(args.children().len(), 2);
        assert_eq!(args.children()[0].as_ident(), Some("x"));
        assert_eq!(args.children()[1].as_ident(), Some("y"));
        assert_eq!(bindings["body"].as_ident(), Some("z"));
    }

    // ---- Typed-antiquotation category enforcement (B63) ----

    #[test]
    fn test_typed_antiquot_term_matches_term_node() {
        // `$x:term` should match a term-category node (an application here).
        let pattern = Syntax::mk_antiquot_typed("x", "term");
        let syntax = Syntax::mk_app(Syntax::ident("f"), vec![Syntax::ident("a")]);

        let bindings =
            match_pattern(&pattern, &syntax).expect("$x:term should match a term (app) node");
        assert_eq!(bindings.len(), 1);
        assert!(bindings.contains_key("x"));
    }

    #[test]
    fn test_typed_antiquot_term_matches_ident() {
        // A bare identifier is a term.
        let pattern = Syntax::mk_antiquot_typed("x", "term");
        let syntax = Syntax::ident("foo");

        let bindings =
            match_pattern(&pattern, &syntax).expect("$x:term should match an identifier term");
        assert!(bindings.contains_key("x"));
    }

    #[test]
    fn test_typed_antiquot_ident_matches_ident_node() {
        // `$x:ident` should match an identifier.
        let pattern = Syntax::mk_antiquot_typed("x", "ident");
        let syntax = Syntax::ident("foo");

        let bindings =
            match_pattern(&pattern, &syntax).expect("$x:ident should match an identifier");
        assert!(bindings.contains_key("x"));
    }

    #[test]
    fn test_typed_antiquot_mismatched_category_fails() {
        // `$x:ident` against an application node (a term, not an ident) must FAIL.
        let pattern = Syntax::mk_antiquot_typed("x", "ident");
        let syntax = Syntax::mk_app(Syntax::ident("f"), vec![Syntax::ident("a")]);

        assert!(
            match_pattern(&pattern, &syntax).is_none(),
            "$x:ident must not match a non-ident (app) node"
        );
    }

    #[test]
    fn test_typed_antiquot_term_rejects_command_node() {
        // A command-category node is not a term; `$x:term` must FAIL on it.
        let pattern = Syntax::mk_antiquot_typed("x", "term");
        let syntax = Syntax::node(SyntaxKind::command(), vec![Syntax::ident("decl")]);

        assert!(
            match_pattern(&pattern, &syntax).is_none(),
            "$x:term must not match a command node"
        );
    }

    #[test]
    fn test_typed_antiquot_num_matches_numeric_literal() {
        // `$n:num` should match a numeric literal but not a string literal.
        let pattern = Syntax::mk_antiquot_typed("n", "num");

        let num = Syntax::mk_num(42);
        assert!(
            match_pattern(&pattern, &num).is_some(),
            "$n:num should match a numeric literal"
        );

        let s = Syntax::mk_str("hello");
        assert!(
            match_pattern(&pattern, &s).is_none(),
            "$n:num must not match a string literal"
        );
    }

    #[test]
    fn test_untyped_antiquot_matches_anything() {
        // An UNTYPED antiquotation still matches any category (unchanged behavior).
        let pattern = Syntax::mk_antiquot("x");

        for syntax in [
            Syntax::ident("foo"),
            Syntax::mk_app(Syntax::ident("f"), vec![Syntax::ident("a")]),
            Syntax::mk_num(7),
            Syntax::mk_str("s"),
            Syntax::node(SyntaxKind::command(), vec![Syntax::ident("decl")]),
            Syntax::node(SyntaxKind::tactic(), vec![Syntax::ident("rfl")]),
        ] {
            assert!(
                match_pattern(&pattern, &syntax).is_some(),
                "untyped $x should match any category, failed on: {}",
                syntax.pretty()
            );
        }
    }

    #[test]
    fn test_typed_antiquot_inside_node_enforces_category() {
        // (f $arg:ident) should match (f x) but not (f (g y)).
        let kind = SyntaxKind::app_kind();
        let pattern = Syntax::node(
            kind.clone(),
            vec![
                Syntax::ident("f"),
                Syntax::mk_antiquot_typed("arg", "ident"),
            ],
        );

        let good = Syntax::node(kind.clone(), vec![Syntax::ident("f"), Syntax::ident("x")]);
        let bindings =
            match_pattern(&pattern, &good).expect("$arg:ident should match an ident argument");
        assert_eq!(bindings["arg"].as_ident(), Some("x"));

        let bad = Syntax::node(
            kind,
            vec![
                Syntax::ident("f"),
                Syntax::mk_app(Syntax::ident("g"), vec![Syntax::ident("y")]),
            ],
        );
        assert!(
            match_pattern(&pattern, &bad).is_none(),
            "$arg:ident must not match an application argument"
        );
    }

    #[test]
    fn test_typed_antiquot_unknown_category_matches_anything() {
        // A user-defined / unknown category has no known shape, so it stays
        // permissive (matches anything) to avoid regressing custom categories.
        let pattern = Syntax::mk_antiquot_typed("x", "myCustomCategory");
        let syntax = Syntax::mk_app(Syntax::ident("f"), vec![Syntax::ident("a")]);

        assert!(
            match_pattern(&pattern, &syntax).is_some(),
            "unknown category should keep matching anything"
        );
    }

    // ---- Splice-antiquotation greedy-match coverage (B63) ----

    #[test]
    fn test_two_consecutive_splices_greedy_first_consumes_all() {
        // Pattern: (f $[a]* $[b]*)
        // Greedy strategy: the FIRST splice cannot see a concrete delimiter
        // before the second splice, so it consumes everything; the trailing
        // splice then matches the empty remainder.
        let kind = SyntaxKind::app_kind();
        let pattern = Syntax::node(
            kind.clone(),
            vec![
                Syntax::ident("f"),
                Syntax::mk_antiquot_splice("a"),
                Syntax::mk_antiquot_splice("b"),
            ],
        );
        let syntax = Syntax::node(
            kind,
            vec![
                Syntax::ident("f"),
                Syntax::ident("x"),
                Syntax::ident("y"),
                Syntax::ident("z"),
            ],
        );

        let bindings = match_pattern(&pattern, &syntax)
            .expect("two consecutive splices should match greedily");
        // First splice greedily consumes x, y, z; second splice gets nothing.
        assert_eq!(bindings["a"].children().len(), 3);
        assert_eq!(bindings["b"].children().len(), 0);
    }

    #[test]
    fn test_splice_then_pattern_greedy_stops_at_delimiter() {
        // Pattern: (f $[args]* end)
        // The splice greedily consumes until the literal `end` delimiter, then
        // the trailing pattern element must line up with the final child.
        let kind = SyntaxKind::app_kind();
        let pattern = Syntax::node(
            kind.clone(),
            vec![
                Syntax::ident("f"),
                Syntax::mk_antiquot_splice("args"),
                Syntax::ident("end"),
            ],
        );
        let syntax = Syntax::node(
            kind,
            vec![
                Syntax::ident("f"),
                Syntax::ident("a"),
                Syntax::ident("b"),
                Syntax::ident("end"),
            ],
        );

        let bindings = match_pattern(&pattern, &syntax)
            .expect("splice-then-delimiter should match greedily up to the delimiter");
        let args = &bindings["args"];
        assert_eq!(args.children().len(), 2);
        assert_eq!(args.children()[0].as_ident(), Some("a"));
        assert_eq!(args.children()[1].as_ident(), Some("b"));
    }

    // ---- macro_rules pure-template expansion (metaprog phase 4) ----

    #[test]
    fn test_macro_rules_twice_template_substitutes_both_operands() {
        // Model `macro_rules | `(twice $x) => `($x + $x)`:
        //   pattern  = (app twice $x)
        //   template = (app HAdd.hAdd $x $x)
        // Applied to `(app twice foo)`, `$x` binds to `foo` and the template
        // instantiates BOTH operand positions => `(app HAdd.hAdd foo foo)`.
        let mut registry = MacroRegistry::new();
        let kind = SyntaxKind::app_kind();
        let pattern = Syntax::node(
            kind.clone(),
            vec![Syntax::ident("twice"), Syntax::mk_antiquot("x")],
        );
        let template = Syntax::node(
            kind.clone(),
            vec![
                Syntax::ident("HAdd.hAdd"),
                Syntax::mk_antiquot("x"),
                Syntax::mk_antiquot("x"),
            ],
        );
        registry.register(MacroDef::new(
            "twice",
            kind.clone(),
            pattern,
            SyntaxQuote::term(template),
        ));

        let input = Syntax::node(kind, vec![Syntax::ident("twice"), Syntax::ident("foo")]);
        let expanded = registry
            .try_expand(&input)
            .expect("twice macro should match and expand");
        let children = expanded.children();
        assert_eq!(children.len(), 3, "expected (app HAdd.hAdd foo foo)");
        assert_eq!(children[0].as_ident(), Some("HAdd.hAdd"));
        assert_eq!(children[1].as_ident(), Some("foo"));
        assert_eq!(children[2].as_ident(), Some("foo"));
    }

    #[test]
    fn test_macro_rules_multi_arm_first_match_wins() {
        // Two arms registered under the same syntax kind. The arm whose literal
        // head matches the input is the one that fires; the other is skipped.
        let mut registry = MacroRegistry::new();
        let kind = SyntaxKind::app_kind();

        registry.register(MacroDef::new(
            "pickA",
            kind.clone(),
            Syntax::node(
                kind.clone(),
                vec![
                    Syntax::ident("pickA"),
                    Syntax::mk_antiquot("x"),
                    Syntax::mk_antiquot("y"),
                ],
            ),
            SyntaxQuote::term(Syntax::mk_antiquot("x")),
        ));
        registry.register(MacroDef::new(
            "pickB",
            kind.clone(),
            Syntax::node(
                kind.clone(),
                vec![
                    Syntax::ident("pickB"),
                    Syntax::mk_antiquot("x"),
                    Syntax::mk_antiquot("y"),
                ],
            ),
            SyntaxQuote::term(Syntax::mk_antiquot("y")),
        ));

        let in_a = Syntax::node(
            kind.clone(),
            vec![
                Syntax::ident("pickA"),
                Syntax::ident("a"),
                Syntax::ident("b"),
            ],
        );
        assert_eq!(
            registry
                .try_expand(&in_a)
                .map(|s| s.as_ident().map(str::to_owned)),
            Some(Some("a".to_owned())),
            "pickA arm should bind $x and expand to a"
        );

        let in_b = Syntax::node(
            kind,
            vec![
                Syntax::ident("pickB"),
                Syntax::ident("a"),
                Syntax::ident("b"),
            ],
        );
        assert_eq!(
            registry
                .try_expand(&in_b)
                .map(|s| s.as_ident().map(str::to_owned)),
            Some(Some("b".to_owned())),
            "pickB arm should bind $y and expand to b"
        );
    }

    #[test]
    fn test_macro_rules_nonmatching_head_does_not_expand() {
        // A registered arm must only fire when the literal head matches; a foreign
        // head leaves the input unmatched (no fabricated expansion).
        let mut registry = MacroRegistry::new();
        let kind = SyntaxKind::app_kind();
        registry.register(MacroDef::new(
            "only",
            kind.clone(),
            Syntax::node(
                kind.clone(),
                vec![Syntax::ident("only"), Syntax::mk_antiquot("x")],
            ),
            SyntaxQuote::term(Syntax::mk_antiquot("x")),
        ));

        let foreign = Syntax::node(kind, vec![Syntax::ident("other"), Syntax::ident("foo")]);
        assert!(
            registry.try_expand(&foreign).is_none(),
            "foreign head must not match the `only` arm"
        );
    }

    #[test]
    fn test_splice_then_pattern_no_delimiter_fails_trailing() {
        // Pattern: (f $[args]* end) against (f a b c) — no `end` present.
        // The greedy splice consumes all remaining children, leaving nothing
        // for the trailing `end` element, so the overall match must fail.
        let kind = SyntaxKind::app_kind();
        let pattern = Syntax::node(
            kind.clone(),
            vec![
                Syntax::ident("f"),
                Syntax::mk_antiquot_splice("args"),
                Syntax::ident("end"),
            ],
        );
        let syntax = Syntax::node(
            kind,
            vec![
                Syntax::ident("f"),
                Syntax::ident("a"),
                Syntax::ident("b"),
                Syntax::ident("c"),
            ],
        );

        assert!(
            match_pattern(&pattern, &syntax).is_none(),
            "missing trailing delimiter should fail the greedy splice match"
        );
    }
}
