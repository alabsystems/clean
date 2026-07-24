// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended attribute elaboration for Lean 5.
//!
//! Provides a typed attribute system that goes beyond the string-based
//! [`super::attribute_registry::AttributeRegistry`]. Each attribute kind is
//! represented as a variant of [`ExtAttributeKind`], and applied attributes
//! are tracked in an [`AttributeManager`] keyed by declaration [`Name`].
//!
//! # Supported attributes
//!
//! `@[simp]`, `@[instance]`, `@[reducible]`, `@[irreducible]`, `@[inline]`,
//! `@[noinline]`, `@[extern]`, `@[specialize]`, `@[nospecialize]`,
//! `@[implementedBy]`, `@[macro]`, `@[init]`, `@[export]`, `@[unfolding]`,
//! `@[class]`, `@[private]`, `@[protected]`, `@[scoped]`.
//!
//! # Reference
//!
//! Lean 4 `src/Lean/Attributes.lean`, `src/Lean/Elab/DeclModifiers.lean`

use std::collections::HashMap;

use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

use crate::error::ElabError;

// ---------------------------------------------------------------------------
// ExtAttributeKind
// ---------------------------------------------------------------------------

/// Typed representation of every supported Lean 5 attribute.
///
/// Each variant captures the attribute's parameters (if any).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum ExtAttributeKind {
    /// `@[simp]` — simplification lemma.
    Simp,
    /// `@[instance <priority>]` — type class instance with optional priority.
    Instance { priority: Option<u32> },
    /// `@[reducible]` — mark definition as reducible.
    Reducible,
    /// `@[irreducible]` — mark definition as irreducible.
    Irreducible,
    /// `@[inline]` / `@[always_inline]` — inline hint.
    Inline { always: bool },
    /// `@[noinline]` — prevent inlining.
    NoInline,
    /// `@[extern "<abi>"]` — external FFI binding.
    Extern { abi: String },
    /// `@[specialize]` — specialization hint.
    Specialize,
    /// `@[nospecialize]` — prevent specialization.
    NoSpecialize,
    /// `@[implementedBy <name>]` — runtime implementation override.
    ImplementedBy { impl_name: String },
    /// `@[macro]` — macro declaration.
    Macro,
    /// `@[init]` — module initialization function.
    BuiltinInit,
    /// `@[export "<name>"]` — C export binding.
    Export { name: String },
    /// `@[unfolding]` — unfold during definitional reduction.
    Unfolding,
    /// `@[class]` — type class declaration.
    Class,
    /// `@[private]` — private visibility modifier.
    Private,
    /// `@[protected]` — protected visibility modifier.
    Protected,
    /// `@[scoped]` — scoped attribute modifier.
    Scoped,
}

impl ExtAttributeKind {
    /// Return the canonical string name used to identify this attribute.
    #[must_use]
    pub(crate) fn name(&self) -> &'static str {
        match self {
            Self::Simp => "simp",
            Self::Instance { .. } => "instance",
            Self::Reducible => "reducible",
            Self::Irreducible => "irreducible",
            Self::Inline { always: false } => "inline",
            Self::Inline { always: true } => "always_inline",
            Self::NoInline => "noinline",
            Self::Extern { .. } => "extern",
            Self::Specialize => "specialize",
            Self::NoSpecialize => "nospecialize",
            Self::ImplementedBy { .. } => "implementedBy",
            Self::Macro => "macro",
            Self::BuiltinInit => "init",
            Self::Export { .. } => "export",
            Self::Unfolding => "unfolding",
            Self::Class => "class",
            Self::Private => "private",
            Self::Protected => "protected",
            Self::Scoped => "scoped",
        }
    }

    /// Check if two kinds represent the same attribute (ignoring parameters).
    #[must_use]
    pub(crate) fn same_kind(&self, other: &Self) -> bool {
        std::mem::discriminant(self) == std::mem::discriminant(other)
    }
}

// ---------------------------------------------------------------------------
// AttributeEntry
// ---------------------------------------------------------------------------

/// A single attribute applied to a declaration.
#[derive(Debug, Clone)]
pub(crate) struct AttributeEntry {
    /// The attribute kind with parameters.
    pub(crate) kind: ExtAttributeKind,
    /// The declaration name this attribute is applied to.
    pub(crate) name: Name,
    /// The namespace in which this attribute was added (for scoped attrs).
    pub(crate) added_in: Option<Name>,
}

// ---------------------------------------------------------------------------
// AttributeManager
// ---------------------------------------------------------------------------

/// Manages the collection of applied attributes across all declarations.
///
/// Provides efficient lookup by declaration name and by attribute kind.
/// This complements the string-based [`super::attribute_registry::AttributeRegistry`]
/// with typed queries used during elaboration and tactic execution.
#[derive(Debug, Clone, Default)]
pub(crate) struct AttributeManager {
    /// Attributes keyed by the declaration name they are applied to.
    entries: HashMap<Name, Vec<AttributeEntry>>,
}

impl AttributeManager {
    /// Create an empty attribute manager.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register an attribute on a declaration.
    ///
    /// # Errors
    ///
    /// Returns [`ElabError::Unsupported`] if an attribute of the same kind
    /// is already registered on the same declaration (duplicate detection).
    pub(crate) fn register_attribute(&mut self, entry: AttributeEntry) -> Result<(), ElabError> {
        let decl_entries = self.entries.entry(entry.name.clone()).or_default();

        // Check for duplicate attribute of the same kind on the same decl.
        if decl_entries.iter().any(|e| e.kind.same_kind(&entry.kind)) {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "attribute @[{}] is already applied to '{}'",
                    entry.kind.name(),
                    entry.name,
                ),
            });
        }

        decl_entries.push(entry);
        Ok(())
    }

    /// Check if a declaration has a specific attribute kind.
    #[must_use]
    pub(crate) fn has_attribute(&self, name: &Name, kind: &ExtAttributeKind) -> bool {
        self.entries
            .get(name)
            .is_some_and(|entries| entries.iter().any(|e| e.kind.same_kind(kind)))
    }

    /// Get all attributes applied to a declaration.
    #[must_use]
    pub(crate) fn get_attributes(&self, name: &Name) -> Vec<&AttributeEntry> {
        self.entries
            .get(name)
            .map_or_else(Vec::new, |entries| entries.iter().collect())
    }

    /// Collect all declaration names tagged with `@[simp]`.
    #[must_use]
    pub(crate) fn get_simp_lemmas(&self) -> Vec<&Name> {
        self.entries
            .iter()
            .filter(|(_, entries)| {
                entries
                    .iter()
                    .any(|e| matches!(e.kind, ExtAttributeKind::Simp))
            })
            .map(|(name, _)| name)
            .collect()
    }

    /// Get all instances with their priorities, sorted by priority descending.
    ///
    /// Returns `(instance_name, priority)` pairs. Instances without an
    /// explicit priority receive a default of 100.
    #[must_use]
    pub(crate) fn get_instances(&self) -> Vec<(Name, u32)> {
        let mut result: Vec<(Name, u32)> = self
            .entries
            .iter()
            .flat_map(|(name, entries)| {
                entries.iter().filter_map(move |e| {
                    if let ExtAttributeKind::Instance { priority } = &e.kind {
                        Some((name.clone(), priority.unwrap_or(100)))
                    } else {
                        None
                    }
                })
            })
            .collect();

        // Sort by priority descending (highest first)
        result.sort_by_key(|b| std::cmp::Reverse(b.1));
        result
    }

    /// Check if a declaration is marked `@[reducible]`.
    #[must_use]
    pub(crate) fn is_reducible(&self, name: &Name) -> bool {
        self.has_attribute(name, &ExtAttributeKind::Reducible)
    }

    /// Check if a declaration is marked `@[inline]` or `@[always_inline]`.
    #[must_use]
    pub(crate) fn is_inline(&self, name: &Name) -> bool {
        self.entries.get(name).is_some_and(|entries| {
            entries
                .iter()
                .any(|e| matches!(e.kind, ExtAttributeKind::Inline { .. }))
        })
    }

    /// Check if a declaration is marked `@[irreducible]`.
    #[must_use]
    pub(crate) fn is_irreducible(&self, name: &Name) -> bool {
        self.has_attribute(name, &ExtAttributeKind::Irreducible)
    }

    /// Check if a declaration is marked `@[class]`.
    #[must_use]
    pub(crate) fn is_class(&self, name: &Name) -> bool {
        self.has_attribute(name, &ExtAttributeKind::Class)
    }

    /// Total number of registered attribute entries across all declarations.
    #[must_use]
    pub(crate) fn total_entries(&self) -> usize {
        self.entries.values().map(Vec::len).sum()
    }

    /// Number of declarations that have at least one attribute.
    #[must_use]
    pub(crate) fn declaration_count(&self) -> usize {
        self.entries.len()
    }

    /// Get attributes filtered by namespace (`added_in`).
    #[must_use]
    pub(crate) fn get_attributes_in_namespace(
        &self,
        name: &Name,
        namespace: &Name,
    ) -> Vec<&AttributeEntry> {
        self.entries.get(name).map_or_else(Vec::new, |entries| {
            entries
                .iter()
                .filter(|e| e.added_in.as_ref() == Some(namespace))
                .collect()
        })
    }
}

// ---------------------------------------------------------------------------
// Attribute elaboration
// ---------------------------------------------------------------------------

/// Parse an attribute name string into a typed [`AttributeEntry`].
///
/// Converts the string attribute name (as produced by the parser's
/// `Attribute` enum) into a typed `ExtAttributeKind`. This mirrors the
/// attribute elaboration in Lean 4's `Lean.Elab.DeclModifiers`.
///
/// # Parameters
///
/// - `attr_name`: The attribute identifier (e.g., `"simp"`, `"instance"`).
/// - `decl_name`: The declaration the attribute is applied to.
/// - `args`: Optional string arguments (e.g., priority for `@[instance 500]`,
///   ABI string for `@[extern "lean_foo"]`).
///
/// # Errors
///
/// Returns [`ElabError::Unsupported`] if the attribute name is unrecognized.
pub(crate) fn elaborate_attribute(
    attr_name: &str,
    decl_name: &Name,
    args: &[&str],
) -> Result<AttributeEntry, ElabError> {
    let kind = match attr_name {
        "simp" => ExtAttributeKind::Simp,
        "instance" => {
            let priority = args.first().and_then(|s| s.parse::<u32>().ok());
            ExtAttributeKind::Instance { priority }
        }
        "reducible" => ExtAttributeKind::Reducible,
        "irreducible" => ExtAttributeKind::Irreducible,
        "inline" => ExtAttributeKind::Inline { always: false },
        "always_inline" => ExtAttributeKind::Inline { always: true },
        "noinline" => ExtAttributeKind::NoInline,
        "extern" => ExtAttributeKind::Extern {
            abi: args.first().unwrap_or(&"").to_string(),
        },
        "specialize" => ExtAttributeKind::Specialize,
        "nospecialize" => ExtAttributeKind::NoSpecialize,
        "implementedBy" => ExtAttributeKind::ImplementedBy {
            impl_name: args.first().unwrap_or(&"").to_string(),
        },
        "macro" => ExtAttributeKind::Macro,
        "init" => ExtAttributeKind::BuiltinInit,
        "export" => ExtAttributeKind::Export {
            name: args.first().unwrap_or(&"").to_string(),
        },
        "unfolding" => ExtAttributeKind::Unfolding,
        "class" => ExtAttributeKind::Class,
        "private" => ExtAttributeKind::Private,
        "protected" => ExtAttributeKind::Protected,
        "scoped" => ExtAttributeKind::Scoped,
        other => {
            return Err(ElabError::Unsupported {
                feature: format!("unrecognized attribute: @[{other}]"),
            });
        }
    };

    Ok(AttributeEntry {
        kind,
        name: decl_name.clone(),
        added_in: None,
    })
}

// ---------------------------------------------------------------------------
// Attribute validation
// ---------------------------------------------------------------------------

/// Validate that an attribute kind is appropriate for the given declaration.
///
/// Performs basic structural checks on the declaration expression to verify
/// the attribute makes sense. For example, `@[simp]` should be applied to
/// lemmas whose conclusion is an equality or iff.
///
/// # Errors
///
/// Returns [`ElabError::Unsupported`] if the attribute is invalid for
/// the declaration kind.
pub(crate) fn validate_attribute_target(
    kind: &ExtAttributeKind,
    decl: &Expr,
) -> Result<(), ElabError> {
    match kind {
        ExtAttributeKind::Simp => validate_simp_target(decl),
        ExtAttributeKind::Instance { .. } => validate_instance_target(decl),
        ExtAttributeKind::Extern { .. } => validate_extern_target(decl),
        ExtAttributeKind::ImplementedBy { .. } => validate_extern_target(decl),
        // Most attributes are valid on any declaration.
        ExtAttributeKind::Reducible
        | ExtAttributeKind::Irreducible
        | ExtAttributeKind::Inline { .. }
        | ExtAttributeKind::NoInline
        | ExtAttributeKind::Specialize
        | ExtAttributeKind::NoSpecialize
        | ExtAttributeKind::Macro
        | ExtAttributeKind::BuiltinInit
        | ExtAttributeKind::Export { .. }
        | ExtAttributeKind::Unfolding
        | ExtAttributeKind::Class
        | ExtAttributeKind::Private
        | ExtAttributeKind::Protected
        | ExtAttributeKind::Scoped => Ok(()),
    }
}

/// Validate that `@[simp]` is applied to a proposition (Pi type target).
///
/// In Lean 4, `@[simp]` is typically applied to lemmas with an Eq or Iff
/// conclusion. We check the type is at least a Pi type (function/forall).
fn validate_simp_target(decl: &Expr) -> Result<(), ElabError> {
    // Accept any Pi type or Prop — the full check requires type inference
    // which happens at a later stage. Here we do a basic structural check.
    if decl.is_pi() || decl.is_sort() || decl.is_const() || decl.is_app() {
        return Ok(());
    }
    Err(ElabError::Unsupported {
        feature: "@[simp] requires a lemma (proposition type)".to_owned(),
    })
}

/// Validate that `@[instance]` is applied to something with a function type.
fn validate_instance_target(decl: &Expr) -> Result<(), ElabError> {
    // Instances must produce a type class value — the type should be a Pi
    // or an application of a class constructor. Accept broadly here.
    if decl.is_pi() || decl.is_app() || decl.is_const() || decl.is_sort() {
        return Ok(());
    }
    Err(ElabError::Unsupported {
        feature: "@[instance] requires a function or constructor type".to_owned(),
    })
}

/// Validate that `@[extern]` / `@[implementedBy]` target is a function.
fn validate_extern_target(decl: &Expr) -> Result<(), ElabError> {
    // Extern bindings require a function type.
    if decl.is_pi() || decl.is_const() || decl.is_app() || decl.is_sort() {
        return Ok(());
    }
    Err(ElabError::Unsupported {
        feature: "@[extern] / @[implementedBy] requires a function type".to_owned(),
    })
}
