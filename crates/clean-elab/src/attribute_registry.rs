// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! User-defined attribute registration for Lean 5.
//!
//! Provides a registry for both builtin and user-defined attributes. Builtin
//! attributes (simp, coe, inline, etc.) are pre-registered at construction.
//! Users can register additional attributes via [`AttributeRegistry::register`].
//!
//! # Example
//!
//! ```
//! use clean_elab::attribute_registry::{AttributeRegistry, AttributeKind};
//!
//! let mut registry = AttributeRegistry::new();
//! assert!(registry.is_registered("simp"));
//! registry.register("my_attr", AttributeKind::UserDefined, "A custom attribute", None)
//!     .expect("registration should succeed");
//! assert!(registry.is_registered("my_attr"));
//! ```

use std::collections::HashMap;

use clean_kernel::{Expr, Name};

use crate::error::ElabError;

/// The kind of an attribute: builtin (shipped with the system) or user-defined.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum AttributeKind {
    /// Attribute shipped with the Lean 5 system.
    Builtin,
    /// Attribute defined by user code via `registerBuiltinAttribute` or
    /// `attribute` commands.
    UserDefined,
}

/// Type alias for the handler callback invoked when an attribute is applied.
///
/// Parameters:
/// - `name`: the declaration name the attribute is applied to
/// - `args`: any arguments provided with the attribute
/// - `env`: the current kernel environment
///
/// Returns `Ok(())` on success, or an error message on failure.
pub type AttributeHandler =
    dyn Fn(&Name, &[Expr], &clean_kernel::Environment) -> Result<(), String> + Send + Sync;

/// A registered attribute declaration.
pub struct AttributeDecl {
    /// The attribute name (e.g., "simp", "coe", "inline").
    pub name: String,
    /// Whether this is a builtin or user-defined attribute.
    pub kind: AttributeKind,
    /// Human-readable description of the attribute.
    pub description: String,
    /// Optional handler invoked when the attribute is applied to a declaration.
    pub handler: Option<Box<AttributeHandler>>,
}

impl std::fmt::Debug for AttributeDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AttributeDecl")
            .field("name", &self.name)
            .field("kind", &self.kind)
            .field("description", &self.description)
            .field("handler", &self.handler.as_ref().map(|_| "..."))
            .finish()
    }
}

/// A record of an attribute application to a specific declaration.
#[derive(Debug, Clone)]
pub struct AttributeApplication {
    /// The name of the attribute being applied.
    pub attr_name: String,
    /// The declaration the attribute is applied to.
    pub target: Name,
    /// Arguments passed to the attribute.
    pub args: Vec<Expr>,
}

/// Registry of all known attributes (builtin and user-defined).
///
/// Constructed via [`AttributeRegistry::new`] which pre-registers the standard
/// set of builtin attributes. Additional attributes can be registered with
/// [`AttributeRegistry::register`].
pub struct AttributeRegistry {
    attrs: HashMap<String, AttributeDecl>,
}

impl std::fmt::Debug for AttributeRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AttributeRegistry")
            .field("count", &self.attrs.len())
            .field("names", &self.attrs.keys().collect::<Vec<_>>())
            .finish()
    }
}

/// Standard builtin attributes pre-registered by [`AttributeRegistry::new`].
pub(crate) const BUILTIN_ATTRS: &[(&str, &str)] = &[
    ("simp", "Simplification lemma"),
    ("coe", "Coercion declaration"),
    ("inline", "Inline hint for the compiler"),
    ("noinline", "Prevent inlining"),
    ("always_inline", "Always inline, even at -O0"),
    ("macro_inline", "Inline before macro expansion"),
    ("inline_if_reduce", "Inline only if it reduces term size"),
    ("reducible", "Mark definition as reducible"),
    (
        "semireducible",
        "Default reducibility (unfold during TC resolution)",
    ),
    ("irreducible", "Mark definition as irreducible"),
    ("instance", "Type class instance"),
    ("default_instance", "Default type class instance"),
    ("extern", "External (FFI) binding"),
    ("export", "Export binding for C interop"),
    ("match_pattern", "Usable in match patterns"),
    ("init", "Module initialization function"),
    ("implementedBy", "Lean implementation override"),
    ("specialize", "Specialization hint"),
    ("nospecialize", "Prevent specialization"),
    ("unbox", "Unbox hint for the compiler"),
    ("csimp", "Computational simp lemma (runtime evaluation)"),
    ("congr", "Congruence lemma for simp"),
    ("ext", "Extensionality lemma"),
    ("refl", "Reflexivity lemma"),
    ("symm", "Symmetry lemma"),
    ("deprecated", "Mark declaration as deprecated"),
    ("class", "Declare as type class"),
];

impl AttributeRegistry {
    /// Create a new registry with all standard builtin attributes pre-registered.
    #[must_use]
    pub fn new() -> Self {
        let mut attrs = HashMap::with_capacity(BUILTIN_ATTRS.len());
        for &(name, desc) in BUILTIN_ATTRS {
            attrs.insert(
                name.to_owned(),
                AttributeDecl {
                    name: name.to_owned(),
                    kind: AttributeKind::Builtin,
                    description: desc.to_owned(),
                    handler: None,
                },
            );
        }
        Self { attrs }
    }

    /// Register a new attribute.
    ///
    /// Returns an error if an attribute with the same name is already registered.
    ///
    /// # Errors
    ///
    /// Returns [`ElabError::Unsupported`] if `name` is already registered.
    pub fn register(
        &mut self,
        name: &str,
        kind: AttributeKind,
        description: &str,
        handler: Option<Box<AttributeHandler>>,
    ) -> Result<(), ElabError> {
        if self.attrs.contains_key(name) {
            return Err(ElabError::Unsupported {
                feature: format!("attribute '{name}' is already registered"),
            });
        }
        self.attrs.insert(
            name.to_owned(),
            AttributeDecl {
                name: name.to_owned(),
                kind,
                description: description.to_owned(),
                handler,
            },
        );
        Ok(())
    }

    /// Apply an attribute to a target declaration.
    ///
    /// Dispatches to the attribute's handler if one is registered. Returns
    /// an error if the attribute is unknown or the handler fails.
    ///
    /// # Errors
    ///
    /// - [`ElabError::UnknownIdent`] if the attribute is not registered.
    /// - [`ElabError::Unsupported`] if the handler returns an error.
    pub fn apply(
        &self,
        attr_name: &str,
        target_name: &Name,
        args: &[Expr],
        env: &clean_kernel::Environment,
    ) -> Result<(), ElabError> {
        let decl = self
            .attrs
            .get(attr_name)
            .ok_or_else(|| ElabError::UnknownIdent(format!("attribute '{attr_name}'")))?;
        if let Some(handler) = &decl.handler {
            handler(target_name, args, env).map_err(|msg| ElabError::Unsupported {
                feature: format!("attribute '{attr_name}' handler failed: {msg}"),
            })?;
        }
        Ok(())
    }

    /// Check whether an attribute name is registered.
    #[must_use]
    pub fn is_registered(&self, name: &str) -> bool {
        self.attrs.contains_key(name)
    }

    /// Look up an attribute declaration by name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&AttributeDecl> {
        self.attrs.get(name)
    }

    /// Iterate over all registered attribute declarations.
    pub fn all_attributes(&self) -> impl Iterator<Item = &AttributeDecl> {
        self.attrs.values()
    }

    /// Count of builtin attributes.
    #[must_use]
    pub fn builtin_count(&self) -> usize {
        self.attrs
            .values()
            .filter(|d| d.kind == AttributeKind::Builtin)
            .count()
    }

    /// Count of user-defined attributes.
    #[must_use]
    pub fn user_defined_count(&self) -> usize {
        self.attrs
            .values()
            .filter(|d| d.kind == AttributeKind::UserDefined)
            .count()
    }
}

impl Default for AttributeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_new_has_builtins() {
        let registry = AttributeRegistry::new();
        assert!(registry.is_registered("simp"));
        assert!(registry.is_registered("coe"));
        assert!(registry.is_registered("inline"));
        assert!(registry.is_registered("noinline"));
        assert!(registry.is_registered("reducible"));
        assert!(registry.is_registered("irreducible"));
        assert!(registry.is_registered("instance"));
        assert!(registry.is_registered("default_instance"));
        assert!(registry.is_registered("extern"));
        assert!(registry.is_registered("export"));
        assert!(registry.is_registered("match_pattern"));
        assert!(registry.is_registered("init"));
        assert!(registry.is_registered("implementedBy"));
        assert!(registry.is_registered("specialize"));
        assert!(registry.is_registered("unbox"));
    }

    #[test]
    fn test_registry_builtin_count() {
        let registry = AttributeRegistry::new();
        assert_eq!(registry.builtin_count(), BUILTIN_ATTRS.len());
        assert_eq!(registry.user_defined_count(), 0);
    }

    #[test]
    fn test_registry_register_user_defined() {
        let mut registry = AttributeRegistry::new();
        let initial_builtin = registry.builtin_count();

        registry
            .register(
                "my_custom_attr",
                AttributeKind::UserDefined,
                "A test attribute",
                None,
            )
            .expect("registration should succeed");

        assert!(registry.is_registered("my_custom_attr"));
        assert_eq!(registry.user_defined_count(), 1);
        assert_eq!(registry.builtin_count(), initial_builtin);

        let decl = registry.get("my_custom_attr").expect("should exist");
        assert_eq!(decl.kind, AttributeKind::UserDefined);
        assert_eq!(decl.description, "A test attribute");
    }

    #[test]
    fn test_registry_duplicate_registration_error() {
        let mut registry = AttributeRegistry::new();
        let result = registry.register("simp", AttributeKind::UserDefined, "duplicate simp", None);
        assert!(result.is_err(), "duplicate registration should fail");
    }

    #[test]
    fn test_registry_apply_unknown_attribute_error() {
        let registry = AttributeRegistry::new();
        let env = clean_kernel::Environment::new();
        let name = Name::from_string("test_decl");
        let result = registry.apply("nonexistent_attr", &name, &[], &env);
        assert!(result.is_err(), "unknown attribute should fail");
    }

    #[test]
    fn test_registry_apply_no_handler() {
        let registry = AttributeRegistry::new();
        let env = clean_kernel::Environment::new();
        let name = Name::from_string("test_decl");
        // Builtin "simp" has no handler — apply should succeed silently
        registry
            .apply("simp", &name, &[], &env)
            .expect("apply with no handler should succeed");
    }

    #[test]
    fn test_registry_apply_with_handler() {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::Arc;

        let mut registry = AttributeRegistry::new();
        let called = Arc::new(AtomicBool::new(false));
        let called_clone = Arc::clone(&called);

        registry
            .register(
                "track",
                AttributeKind::UserDefined,
                "Tracking attribute",
                Some(Box::new(move |_name, _args, _env| {
                    called_clone.store(true, Ordering::SeqCst);
                    Ok(())
                })),
            )
            .expect("registration should succeed");

        let env = clean_kernel::Environment::new();
        let name = Name::from_string("my_fn");
        registry
            .apply("track", &name, &[], &env)
            .expect("apply should succeed");
        assert!(
            called.load(Ordering::SeqCst),
            "handler should have been called"
        );
    }

    #[test]
    fn test_registry_apply_handler_error() {
        let mut registry = AttributeRegistry::new();
        registry
            .register(
                "fail_attr",
                AttributeKind::UserDefined,
                "Always fails",
                Some(Box::new(|_name, _args, _env| {
                    Err("intentional failure".to_owned())
                })),
            )
            .expect("registration should succeed");

        let env = clean_kernel::Environment::new();
        let name = Name::from_string("test_decl");
        let result = registry.apply("fail_attr", &name, &[], &env);
        assert!(result.is_err(), "handler error should propagate");
    }

    #[test]
    fn test_registry_get_returns_none_for_unknown() {
        let registry = AttributeRegistry::new();
        assert!(registry.get("nonexistent").is_none());
    }

    #[test]
    fn test_registry_all_attributes_includes_builtins_and_user() {
        let mut registry = AttributeRegistry::new();
        registry
            .register("custom1", AttributeKind::UserDefined, "Custom 1", None)
            .expect("registration should succeed");

        let all: Vec<_> = registry.all_attributes().collect();
        assert_eq!(all.len(), BUILTIN_ATTRS.len() + 1);
    }

    #[test]
    fn test_attribute_application_struct() {
        let app = AttributeApplication {
            attr_name: "simp".to_owned(),
            target: Name::from_string("my_lemma"),
            args: vec![],
        };
        assert_eq!(app.attr_name, "simp");
        assert_eq!(app.target.to_string(), "my_lemma");
        assert!(app.args.is_empty());
    }

    #[test]
    fn test_registry_default_trait() {
        let registry = AttributeRegistry::default();
        assert_eq!(registry.builtin_count(), BUILTIN_ATTRS.len());
    }
}
