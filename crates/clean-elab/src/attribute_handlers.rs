// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attribute handlers for silently-ignored attributes.
//!
//! Implements handlers for `@[coe]`, `@[init]`, `@[default_instance]`, and
//! `@[match_pattern]`. These attributes were previously parsed and registered
//! in [`super::attribute_registry`] but had no handler — they were silently
//! ignored during elaboration. This module provides concrete handler logic
//! that validates the target declaration and records the registration in an
//! [`AttributeHandlerRegistry`].
//!
//! # Architecture
//!
//! Each handler:
//! 1. Validates the declaration exists in the kernel [`Environment`].
//! 2. Stores the registration in the [`AttributeHandlerRegistry`] data structure.
//! 3. Returns `Result<(), ElabError>` for error reporting.
//!
//! The registry is independent of the kernel `Environment` — it lives at the
//! elaboration layer and can be queried during elaboration and tactic execution.

use std::collections::HashMap;
use std::sync::Arc;

use clean_kernel::{Environment, Name};

use crate::error::ElabError;

/// Default priority for `@[default_instance]` when none is specified.
pub const DEFAULT_INSTANCE_PRIORITY: u32 = 1000;

/// Information about a registered default instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefaultInstanceInfo {
    /// The declaration name registered as a default instance.
    pub name: Name,
    /// Priority for resolution ordering (higher = tried first).
    pub priority: u32,
}

/// Registry for attribute handler state.
///
/// Stores registrations produced by the four attribute handlers. This is an
/// elaboration-layer data structure — the kernel [`Environment`] does not
/// track these registrations directly.
#[derive(Debug, Clone, Default)]
pub struct AttributeHandlerRegistry {
    /// Declarations registered as coercions via `@[coe]`.
    coercions: HashMap<Name, ()>,
    /// Declarations registered as initialization functions via `@[init]`.
    init_fns: HashMap<Name, ()>,
    /// Declarations registered as default instances via `@[default_instance]`.
    default_instances: HashMap<Name, DefaultInstanceInfo>,
    /// Declarations registered as match pattern discriminators via `@[match_pattern]`.
    match_patterns: HashMap<Name, ()>,
}

impl AttributeHandlerRegistry {
    /// Create a new, empty registry.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    // ========================================================================
    // Coercion registration (@[coe])
    // ========================================================================

    /// Check if a declaration is registered as a coercion.
    #[must_use]
    pub fn is_coercion(&self, name: &Name) -> bool {
        self.coercions.contains_key(name)
    }

    /// Iterate over all registered coercion names.
    pub fn coercions(&self) -> impl Iterator<Item = &Name> {
        self.coercions.keys()
    }

    /// Number of registered coercions.
    #[must_use]
    pub fn coercion_count(&self) -> usize {
        self.coercions.len()
    }

    // ========================================================================
    // Init function registration (@[init])
    // ========================================================================

    /// Check if a declaration is registered as an initialization function.
    #[must_use]
    pub fn is_init_fn(&self, name: &Name) -> bool {
        self.init_fns.contains_key(name)
    }

    /// Iterate over all registered init function names.
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    pub fn init_fns(&self) -> impl Iterator<Item = &Name> {
        self.init_fns.keys()
    }

    /// Number of registered init functions.
    #[must_use]
    pub fn init_fn_count(&self) -> usize {
        self.init_fns.len()
    }

    // ========================================================================
    // Default instance registration (@[default_instance])
    // ========================================================================

    /// Check if a declaration is registered as a default instance.
    #[must_use]
    pub fn is_default_instance(&self, name: &Name) -> bool {
        self.default_instances.contains_key(name)
    }

    /// Get default instance info for a declaration, if registered.
    #[must_use]
    pub fn get_default_instance(&self, name: &Name) -> Option<&DefaultInstanceInfo> {
        self.default_instances.get(name)
    }

    /// Iterate over all registered default instances.
    pub fn default_instances(&self) -> impl Iterator<Item = &DefaultInstanceInfo> {
        self.default_instances.values()
    }

    /// Number of registered default instances.
    #[must_use]
    pub fn default_instance_count(&self) -> usize {
        self.default_instances.len()
    }

    // ========================================================================
    // Match pattern registration (@[match_pattern])
    // ========================================================================

    /// Check if a declaration is registered as a match pattern discriminator.
    #[must_use]
    pub fn is_match_pattern(&self, name: &Name) -> bool {
        self.match_patterns.contains_key(name)
    }

    /// Iterate over all registered match pattern names.
    pub fn match_patterns(&self) -> impl Iterator<Item = &Name> {
        self.match_patterns.keys()
    }

    /// Number of registered match patterns.
    #[must_use]
    pub fn match_pattern_count(&self) -> usize {
        self.match_patterns.len()
    }
}

// ============================================================================
// Handler functions
// ============================================================================

/// Validate that a declaration with the given name exists in the environment.
///
/// Returns `Ok(())` if found, or `Err(ElabError::UnknownIdent)` if the
/// declaration is not present.
fn validate_decl_exists(decl_name: &Name, env: &Environment) -> Result<(), ElabError> {
    if env.get_const(decl_name).is_none() {
        return Err(ElabError::UnknownIdent(format!(
            "declaration '{}' not found in environment",
            decl_name
        )));
    }
    Ok(())
}

/// Handle `@[coe]` — register a declaration as a coercion.
///
/// Validates the declaration exists in the environment, then records it in
/// the registry. Coercions allow implicit type conversion during elaboration.
///
/// # Errors
///
/// - [`ElabError::UnknownIdent`] if `decl_name` is not in `env`.
/// - [`ElabError::Unsupported`] if `decl_name` is already registered as a coercion.
pub fn handle_coe(
    decl_name: &Name,
    env: &Environment,
    registry: &mut AttributeHandlerRegistry,
) -> Result<(), ElabError> {
    validate_decl_exists(decl_name, env)?;

    if registry.coercions.contains_key(decl_name) {
        return Err(ElabError::Unsupported {
            feature: format!("'{}' is already registered as a coercion", decl_name),
        });
    }

    registry.coercions.insert(decl_name.clone(), ());
    Ok(())
}

/// Handle `@[init]` — register a declaration as an initialization function.
///
/// Validates the declaration exists in the environment, then records it in
/// the registry. Init functions are called during module initialization.
///
/// # Errors
///
/// - [`ElabError::UnknownIdent`] if `decl_name` is not in `env`.
/// - [`ElabError::Unsupported`] if `decl_name` is already registered as an init function.
pub fn handle_init(
    decl_name: &Name,
    env: &Environment,
    registry: &mut AttributeHandlerRegistry,
) -> Result<(), ElabError> {
    validate_decl_exists(decl_name, env)?;

    if registry.init_fns.contains_key(decl_name) {
        return Err(ElabError::Unsupported {
            feature: format!("'{}' is already registered as an init function", decl_name),
        });
    }

    registry.init_fns.insert(decl_name.clone(), ());
    Ok(())
}

/// Handle `@[default_instance]` — register a declaration as a default instance.
///
/// Validates the declaration exists in the environment, then records it in
/// the registry with the specified priority. Default instances are preferred
/// during type class resolution when multiple instances match.
///
/// # Errors
///
/// - [`ElabError::UnknownIdent`] if `decl_name` is not in `env`.
/// - [`ElabError::Unsupported`] if `decl_name` is already registered as a default instance.
pub fn handle_default_instance(
    decl_name: &Name,
    env: &Environment,
    registry: &mut AttributeHandlerRegistry,
    priority: Option<u32>,
) -> Result<(), ElabError> {
    validate_decl_exists(decl_name, env)?;

    if registry.default_instances.contains_key(decl_name) {
        return Err(ElabError::Unsupported {
            feature: format!(
                "'{}' is already registered as a default instance",
                decl_name
            ),
        });
    }

    registry.default_instances.insert(
        decl_name.clone(),
        DefaultInstanceInfo {
            name: decl_name.clone(),
            priority: priority.unwrap_or(DEFAULT_INSTANCE_PRIORITY),
        },
    );
    Ok(())
}

/// Handle `@[match_pattern]` — register a declaration as a match pattern.
///
/// Validates the declaration exists in the environment, then records it in
/// the registry. Match pattern declarations can appear as discriminators in
/// `match` expressions.
///
/// # Errors
///
/// - [`ElabError::UnknownIdent`] if `decl_name` is not in `env`.
/// - [`ElabError::Unsupported`] if `decl_name` is already registered as a match pattern.
pub fn handle_match_pattern(
    decl_name: &Name,
    env: &Environment,
    registry: &mut AttributeHandlerRegistry,
) -> Result<(), ElabError> {
    validate_decl_exists(decl_name, env)?;

    if registry.match_patterns.contains_key(decl_name) {
        return Err(ElabError::Unsupported {
            feature: format!("'{}' is already registered as a match pattern", decl_name),
        });
    }

    registry.match_patterns.insert(decl_name.clone(), ());
    Ok(())
}

// ============================================================================
// User-defined attribute handlers (Phase 3 extensibility surface)
// ============================================================================

/// A user-supplied handler for a custom attribute `@[name]`. Invoked with the
/// attribute's target declaration name and the current kernel [`Environment`];
/// returns `Ok(())` on success, or an [`ElabError`] to fail elaboration loudly.
///
/// This mirrors the user-defined-tactic facility: a Clean-native extension point
/// dispatched by attribute name, with no dependency on Lean `.olean` metaprograms.
pub type UserAttributeHandler =
    Arc<dyn Fn(&Name, &Environment) -> Result<(), ElabError> + Send + Sync>;

/// Registry of user-defined attribute handlers, keyed by attribute name (without
/// the surrounding `@[ ]`). Independent of the builtin [`AttributeHandlerRegistry`];
/// this is the Phase 3 extension point that lets a project register its own
/// `@[myAttr]` behaviour.
#[derive(Clone, Default)]
pub struct UserAttributeRegistry {
    handlers: HashMap<String, UserAttributeHandler>,
}

impl std::fmt::Debug for UserAttributeRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("UserAttributeRegistry")
            .field("attributes", &self.handlers.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl UserAttributeRegistry {
    /// Create an empty registry.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a handler for the custom attribute `@[name]`. A later registration
    /// for the same name replaces the earlier one (last-wins, as in Lean).
    pub fn register(&mut self, name: impl Into<String>, handler: UserAttributeHandler) {
        self.handlers.insert(name.into(), handler);
    }

    /// Whether a handler is registered for `@[name]`.
    #[must_use]
    pub fn is_registered(&self, name: &str) -> bool {
        self.handlers.contains_key(name)
    }

    /// Number of registered user attributes.
    #[must_use]
    pub fn registered_count(&self) -> usize {
        self.handlers.len()
    }

    /// Names of all registered user attributes.
    pub fn attribute_names(&self) -> impl Iterator<Item = &str> {
        self.handlers.keys().map(String::as_str)
    }

    /// Dispatch the handler for `@[name]` against `target`. Fails with
    /// [`ElabError::Unsupported`] if no handler is registered for `name`;
    /// otherwise propagates the handler's own result.
    pub fn dispatch(&self, name: &str, target: &Name, env: &Environment) -> Result<(), ElabError> {
        let handler = self
            .handlers
            .get(name)
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!("no handler registered for custom attribute @[{name}]"),
            })?;
        handler(target, env)
    }
}

#[cfg(test)]
#[path = "attribute_handlers_tests.rs"]
mod tests;
