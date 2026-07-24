// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attribute macro expansion pipeline for Lean 5.
//!
//! Provides a trait-based system for attribute macros that transform or annotate
//! declarations. Each attribute macro receives the declaration name and parsed
//! attribute, then produces an [`AttrMacroResult`] describing the effect.
//!
//! # Architecture
//!
//! 1. [`AttrMacro`] trait — defines a single `expand` method.
//! 2. [`AttrMacroRegistry`] — maps attribute names to registered macro entries.
//! 3. [`expand_attributes`] — pipeline function that applies all attributes on a
//!    declaration in priority order, collecting results and errors.
//! 4. Built-in macros (in [`builtins`]) — default handlers for `@[simp]`,
//!    `@[ext]`, `@[inline]`, `@[reducible]`, etc.
//!
//! # Example
//!
//! ```
//! use clean_elab::attr_macro::{AttrMacroRegistry, expand_attributes};
//! use clean_parser::Attribute;
//! use clean_kernel::Name;
//!
//! let registry = AttrMacroRegistry::with_builtins();
//! let attrs = vec![Attribute::Simp { priority: None }, Attribute::Inline];
//! let results = expand_attributes(&Name::from_string("my_lemma"), &attrs, &registry);
//! assert!(results.errors.is_empty());
//! assert_eq!(results.effects.len(), 2);
//! ```

#[path = "attr_macro_builtins.rs"]
pub(crate) mod builtins;

use std::collections::HashMap;

use clean_kernel::Name;
use clean_parser::Attribute;

use crate::error::ElabError;

// ============================================================================
// Result types
// ============================================================================

/// The effect produced by an attribute macro expansion.
///
/// Each variant describes a registration or transformation that the elaborator
/// should perform after expansion completes.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum AttrMacroResult {
    /// Register the declaration as a simp lemma with optional priority.
    RegisterSimpLemma { priority: Option<u32> },
    /// Register the declaration as an extensionality lemma.
    RegisterExtLemma,
    /// Register the declaration as a congruence lemma.
    RegisterCongrLemma,
    /// Register the declaration as a reflexivity lemma.
    RegisterReflLemma,
    /// Register the declaration as a symmetry lemma.
    RegisterSymmLemma,
    /// Register the declaration as a computational simp lemma.
    RegisterCsimpLemma,
    /// Set the declaration's reducibility level.
    SetReducibility(ReducibilityLevel),
    /// Mark the declaration for inlining.
    SetInline(InlineKind),
    /// Mark the declaration for specialization.
    SetSpecialize(SpecializeKind),
    /// Register an external (FFI) binding.
    RegisterExtern { extern_name: String },
    /// Register a C-export binding.
    RegisterExport { export_name: String },
    /// Register an implementation override.
    RegisterImplementedBy { impl_name: String },
    /// Register the declaration as deprecated.
    RegisterDeprecated { message: Option<String> },
    /// Register the declaration as a coercion.
    RegisterCoercion,
    /// Register the declaration as a match pattern discriminator.
    RegisterMatchPattern,
    /// Register the declaration as a type class.
    RegisterClass,
    /// Register the declaration as an initialization function.
    RegisterInit,
    /// Register instance priority.
    RegisterInstance { priority: u32 },
    /// Register default instance (lowest priority fallback).
    RegisterDefaultInstance,
    /// Custom/user-defined effect described by a tag string.
    Custom(String),
}

/// Reducibility levels for `@[reducible]`, `@[semireducible]`, `@[irreducible]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityLevel {
    /// Always unfold.
    Reducible,
    /// Default: unfold during type class resolution.
    Semireducible,
    /// Never unfold automatically.
    Irreducible,
}

/// Inline hint kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InlineKind {
    /// `@[inline]`
    Inline,
    /// `@[always_inline]`
    AlwaysInline,
    /// `@[noinline]`
    Noinline,
    /// `@[macro_inline]`
    MacroInline,
    /// `@[inline_if_reduce]`
    InlineIfReduce,
}

/// Specialization hint kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecializeKind {
    /// `@[specialize]`
    Specialize,
    /// `@[nospecialize]`
    Nospecialize,
}

// ============================================================================
// AttrMacro trait
// ============================================================================

/// Trait for attribute macros that transform or annotate declarations.
///
/// Implementors receive the declaration name and parsed attribute, then return
/// an effect describing what the elaborator should do.
pub trait AttrMacro: Send + Sync {
    /// Expand the attribute on the given declaration.
    ///
    /// # Errors
    ///
    /// Returns [`ElabError`] if the attribute is invalid for the target
    /// declaration (e.g., wrong argument count, incompatible declaration kind).
    fn expand(&self, decl_name: &Name, attr: &Attribute) -> Result<AttrMacroResult, ElabError>;
}

// ============================================================================
// Registry
// ============================================================================

/// A registered attribute macro entry with metadata.
pub(crate) struct AttrMacroEntry {
    /// The attribute name this macro handles (e.g., "simp", "inline").
    pub(crate) name: String,
    /// Priority for ordering expansion (lower = earlier).
    pub(crate) priority: u32,
    /// The macro implementation.
    pub(crate) handler: Box<dyn AttrMacro>,
}

impl std::fmt::Debug for AttrMacroEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AttrMacroEntry")
            .field("name", &self.name)
            .field("priority", &self.priority)
            .field("handler", &"<dyn AttrMacro>")
            .finish()
    }
}

/// Registry for looking up and applying attribute macros.
///
/// Maps attribute names to their macro handlers. Use
/// [`AttrMacroRegistry::with_builtins`] to get a registry pre-populated with
/// the standard Lean 5 attribute macros.
pub struct AttrMacroRegistry {
    macros: HashMap<String, AttrMacroEntry>,
}

impl std::fmt::Debug for AttrMacroRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AttrMacroRegistry")
            .field("count", &self.macros.len())
            .field("names", &self.macros.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl AttrMacroRegistry {
    /// Create an empty registry with no macros registered.
    #[must_use]
    pub fn new() -> Self {
        Self {
            macros: HashMap::new(),
        }
    }

    /// Create a registry pre-populated with all built-in attribute macros.
    #[must_use]
    pub fn with_builtins() -> Self {
        let mut registry = Self::new();
        builtins::register_builtins(&mut registry);
        registry
    }

    /// Register an attribute macro.
    ///
    /// # Errors
    ///
    /// Returns [`ElabError::Unsupported`] if a macro with the same name is
    /// already registered.
    pub fn register(
        &mut self,
        name: &str,
        priority: u32,
        handler: Box<dyn AttrMacro>,
    ) -> Result<(), ElabError> {
        if self.macros.contains_key(name) {
            return Err(ElabError::Unsupported {
                feature: format!("attribute macro '{name}' is already registered"),
            });
        }
        self.macros.insert(
            name.to_owned(),
            AttrMacroEntry {
                name: name.to_owned(),
                priority,
                handler,
            },
        );
        Ok(())
    }

    /// Look up a macro entry by attribute name.
    #[must_use]
    pub(crate) fn get(&self, name: &str) -> Option<&AttrMacroEntry> {
        self.macros.get(name)
    }

    /// Check whether a macro is registered for the given attribute name.
    #[must_use]
    pub fn is_registered(&self, name: &str) -> bool {
        self.macros.contains_key(name)
    }

    /// Number of registered macros.
    #[must_use]
    pub fn len(&self) -> usize {
        self.macros.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.macros.is_empty()
    }

    /// Iterate over all registered macro names.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.macros.keys().map(String::as_str)
    }
}

impl Default for AttrMacroRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Expansion pipeline
// ============================================================================

/// Collected results from expanding all attributes on a declaration.
#[derive(Debug, Clone)]
pub struct ExpansionResult {
    /// The effects produced by successful expansions, in priority order.
    pub effects: Vec<AttrMacroResult>,
    /// Errors from failed expansions (attribute name + error).
    pub errors: Vec<(String, ElabError)>,
    /// Attributes that had no registered macro (not necessarily errors —
    /// the caller may handle them via other mechanisms).
    pub unhandled: Vec<String>,
}

/// Map a parsed [`Attribute`] to its canonical name for registry lookup.
#[must_use]
pub(crate) fn attr_name(attr: &Attribute) -> &str {
    match attr {
        Attribute::Simp { .. } => "simp",
        Attribute::Congr => "congr",
        Attribute::Ext => "ext",
        Attribute::Refl => "refl",
        Attribute::Symm => "symm",
        Attribute::Reducible => "reducible",
        Attribute::Semireducible => "semireducible",
        Attribute::Irreducible => "irreducible",
        Attribute::Inline => "inline",
        Attribute::AlwaysInline => "always_inline",
        Attribute::Noinline => "noinline",
        Attribute::MacroInline => "macro_inline",
        Attribute::InlineIfReduce => "inline_if_reduce",
        Attribute::Specialize => "specialize",
        Attribute::Nospecialize => "nospecialize",
        Attribute::Extern(_) => "extern",
        Attribute::Export(_) => "export",
        Attribute::ImplementedBy(_) => "implementedBy",
        Attribute::Deprecated(_) => "deprecated",
        Attribute::Csimp => "csimp",
        Attribute::MatchPattern => "match_pattern",
        Attribute::Class => "class",
        Attribute::Coe => "coe",
        Attribute::Init => "init",
        Attribute::InstancePriority(_) => "instance",
        Attribute::DefaultInstance { .. } => "default_instance",
        Attribute::Aesop(_) => "aesop",
        Attribute::Unknown(name) => name.as_str(),
    }
}

/// Expand all attributes on a declaration through the registry.
///
/// Attributes are processed in priority order (lower priority number = earlier).
/// Each attribute is looked up in the registry; if a macro is registered, its
/// `expand` method is called. Unregistered attributes are collected in
/// [`ExpansionResult::unhandled`].
///
/// # Arguments
///
/// * `decl_name` — the fully qualified name of the declaration
/// * `attrs` — parsed attributes from the surface syntax
/// * `registry` — the attribute macro registry
#[must_use]
pub fn expand_attributes(
    decl_name: &Name,
    attrs: &[Attribute],
    registry: &AttrMacroRegistry,
) -> ExpansionResult {
    // Collect (index, priority, name) for sorting by priority.
    let mut indexed: Vec<(usize, u32, &str)> = attrs
        .iter()
        .enumerate()
        .map(|(i, a)| {
            let name = attr_name(a);
            let priority = registry.get(name).map_or(u32::MAX, |e| e.priority);
            (i, priority, name)
        })
        .collect();

    // Stable sort by priority so equal-priority attributes retain source order.
    indexed.sort_by_key(|&(idx, prio, _)| (prio, idx));

    let mut effects = Vec::new();
    let mut errors = Vec::new();
    let mut unhandled = Vec::new();

    for (idx, _prio, name) in &indexed {
        let attr = &attrs[*idx];
        match registry.get(name) {
            Some(entry) => match entry.handler.expand(decl_name, attr) {
                Ok(result) => effects.push(result),
                Err(e) => errors.push(((*name).to_owned(), e)),
            },
            None => unhandled.push((*name).to_owned()),
        }
    }

    ExpansionResult {
        effects,
        errors,
        unhandled,
    }
}

#[cfg(test)]
#[path = "attr_macro_tests.rs"]
mod tests;
