// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Command-level option registry for `set_option` declarations.
//!
//! Lean 4 supports `set_option <name> <value>` at file scope (command level),
//! not only inside tactic blocks. Mathlib uses `set_option maxHeartbeats 400000`
//! pervasively. This module provides:
//!
//! - [`OptionsRegistry`]: global registry of known option declarations with defaults
//! - [`FileOptions`]: per-file option overrides layered on top of registry defaults
//! - [`OptionError`]: typed errors for invalid option operations

use std::collections::BTreeMap;

// ============================================================================
// Option value type (re-exported from tactic::options for consistency)
// ============================================================================

/// Value types for Lean 4 options.
///
/// Mirrors the value kinds that `set_option` accepts:
/// booleans, natural numbers, strings, and names.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum OptionValue {
    /// Boolean option (e.g., `set_option pp.all true`).
    Bool(bool),
    /// Natural number option (e.g., `set_option maxHeartbeats 400000`).
    Nat(u64),
    /// String option (e.g., `set_option pp.format "compact"`).
    String(String),
    /// Name option (e.g., `set_option trace.profiler.output `my.trace``).
    ///
    /// In Lean 4 some options accept hierarchical names rather than
    /// arbitrary strings.  The value is stored as a dotted string
    /// (e.g. `"Lean.Elab"`).
    Name(String),
}

impl OptionValue {
    /// Returns the kind name for error messages.
    #[must_use]
    pub(crate) fn kind_name(&self) -> &'static str {
        match self {
            Self::Bool(_) => "Bool",
            Self::Nat(_) => "Nat",
            Self::String(_) => "String",
            Self::Name(_) => "Name",
        }
    }
}

impl std::fmt::Display for OptionValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(v) => write!(f, "{v}"),
            Self::Nat(v) => write!(f, "{v}"),
            Self::String(v) => write!(f, "\"{v}\""),
            Self::Name(v) => write!(f, "`{v}`"),
        }
    }
}

// ============================================================================
// Option declaration
// ============================================================================

/// Declaration of a registered option: name, default value, and description.
#[derive(Debug, Clone)]
pub struct OptionDecl {
    name: String,
    default: OptionValue,
    description: String,
}

impl OptionDecl {
    /// Construct a new option declaration.
    #[must_use]
    pub fn new(
        name: impl Into<String>,
        default: OptionValue,
        description: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            default,
            description: description.into(),
        }
    }

    /// The fully qualified option name (e.g., `"maxHeartbeats"`).
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The default value used when no override is set.
    #[must_use]
    pub fn default(&self) -> &OptionValue {
        &self.default
    }

    /// Human-readable description of the option.
    #[must_use]
    pub fn description(&self) -> &str {
        &self.description
    }
}

// ============================================================================
// Error type
// ============================================================================

/// Errors that can occur when setting file-level options.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum OptionError {
    /// Option name is not registered in the registry.
    #[error("unknown option '{name}'")]
    UnknownOption { name: String },

    /// Option value type does not match the declared type.
    #[error("type mismatch for option '{name}': expected {expected}, got {actual}")]
    TypeMismatch {
        name: String,
        expected: &'static str,
        actual: &'static str,
    },
}

// ============================================================================
// Options registry
// ============================================================================

/// Global registry of known option declarations.
///
/// Pre-populated with standard Lean 4 options on construction.
/// Additional options can be registered dynamically (e.g., from
/// `register_option` commands in .olean files).
///
/// Uses `BTreeMap` for deterministic iteration order in diagnostics.
#[derive(Debug, Clone)]
pub struct OptionsRegistry {
    decls: BTreeMap<String, OptionDecl>,
}

impl Default for OptionsRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl OptionsRegistry {
    /// Create a new registry pre-populated with standard Lean 4 options.
    #[must_use]
    pub fn new() -> Self {
        let mut registry = Self {
            decls: BTreeMap::new(),
        };
        registry.register_standard_options();
        registry
    }

    /// Register a new option declaration.
    ///
    /// If an option with the same name already exists, it is overwritten.
    pub fn register(&mut self, name: &str, default: OptionValue, description: &str) {
        self.decls.insert(
            name.to_string(),
            OptionDecl {
                name: name.to_string(),
                default,
                description: description.to_string(),
            },
        );
    }

    /// Register a new option using a pre-built [`OptionDecl`].
    ///
    /// This is a convenience wrapper around [`register`](Self::register)
    /// for callers that already have a declaration struct.
    pub fn register_option(&mut self, name: &str, decl: OptionDecl) {
        self.decls.insert(name.to_string(), decl);
    }

    /// Look up the full declaration for a registered option.
    ///
    /// Returns `None` if no option with the given name exists.
    #[must_use]
    pub fn get_option(&self, name: &str) -> Option<&OptionDecl> {
        self.decls.get(name)
    }

    /// Look up the default value for a registered option.
    #[must_use]
    pub fn get_default(&self, name: &str) -> Option<&OptionValue> {
        self.decls.get(name).map(|d| &d.default)
    }

    /// Whether an option with the given name is registered.
    #[must_use]
    pub fn is_registered(&self, name: &str) -> bool {
        self.decls.contains_key(name)
    }

    /// Validate that `value` has the correct type for the option named `name`.
    ///
    /// # Errors
    ///
    /// - [`OptionError::UnknownOption`] if `name` is not registered.
    /// - [`OptionError::TypeMismatch`] if `value`'s kind differs from the
    ///   option's declared default kind.
    pub fn validate_option(&self, name: &str, value: &OptionValue) -> Result<(), OptionError> {
        let decl = self
            .decls
            .get(name)
            .ok_or_else(|| OptionError::UnknownOption {
                name: name.to_string(),
            })?;

        let expected_kind = decl.default.kind_name();
        let actual_kind = value.kind_name();
        if expected_kind != actual_kind {
            return Err(OptionError::TypeMismatch {
                name: name.to_string(),
                expected: expected_kind,
                actual: actual_kind,
            });
        }

        Ok(())
    }

    /// Iterator over all registered option declarations, sorted by name.
    pub fn all_options(&self) -> impl Iterator<Item = &OptionDecl> {
        self.decls.values()
    }

    /// Total number of registered options.
    #[must_use]
    pub fn len(&self) -> usize {
        self.decls.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }

    /// Register the standard Lean 4 options.
    ///
    /// These match Lean 4's built-in option declarations from
    /// `src/Init/Prelude.lean` and `src/Lean/Elab/Command.lean`.
    fn register_standard_options(&mut self) {
        self.register(
            "maxHeartbeats",
            OptionValue::Nat(200_000),
            "Maximum number of heartbeats for elaboration (0 = unlimited)",
        );
        self.register(
            "maxRecDepth",
            OptionValue::Nat(512),
            "Maximum recursion depth for the kernel and elaborator",
        );
        self.register(
            "pp.all",
            OptionValue::Bool(false),
            "Display all implicit arguments and universe levels",
        );
        self.register(
            "autoImplicit",
            OptionValue::Bool(true),
            "Automatically introduce unbound variables as implicit arguments",
        );
        self.register(
            "relaxedAutoImplicit",
            OptionValue::Bool(true),
            "Use relaxed auto-implicit resolution (single-letter variables)",
        );
        self.register(
            "trace.Meta.isDefEq",
            OptionValue::Bool(false),
            "Trace definitional equality checks in the Meta framework",
        );
        // Pretty-printer options
        self.register(
            "pp.universes",
            OptionValue::Bool(false),
            "Display universe levels in pretty-printed output",
        );
        self.register(
            "pp.notation",
            OptionValue::Bool(true),
            "Use notation in pretty-printed output",
        );
        self.register(
            "pp.proofs",
            OptionValue::Bool(false),
            "Display proof terms in pretty-printed output",
        );
        // Linter options
        self.register(
            "linter.unusedVariables",
            OptionValue::Bool(true),
            "Warn about unused variables",
        );
        self.register(
            "linter.unusedSimpArgs",
            OptionValue::Bool(true),
            "Warn about unused simp arguments",
        );
        // Elaboration / instance-synthesis budgets (Nat).
        self.register(
            "synthInstance.maxHeartbeats",
            OptionValue::Nat(20_000),
            "Maximum heartbeats for a single type-class synthesis problem",
        );
        self.register(
            "synthInstance.maxSize",
            OptionValue::Nat(128),
            "Maximum number of instances in a synthesis solution",
        );
        self.register(
            "compiler.maxRecInlineIfReduce",
            OptionValue::Nat(16),
            "Maximum recursive inline_if_reduce depth in the compiler",
        );
        // Extra pretty-printer options (Bool).
        for (name, default, desc) in [
            (
                "pp.structureInstances",
                true,
                "Use `{ … }` structure-instance notation",
            ),
            (
                "pp.piBinderTypes",
                true,
                "Show binder types in Pi telescopes",
            ),
            ("pp.letVarTypes", true, "Show types on `let` variables"),
            (
                "pp.funBinderTypes",
                true,
                "Show binder types on lambda binders",
            ),
            ("pp.fullNames", false, "Print fully qualified names"),
            (
                "pp.coercions.types",
                false,
                "Show types of inserted coercions",
            ),
            ("pp.coercions", true, "Display coercions"),
            (
                "pp.parens",
                false,
                "Fully parenthesize pretty-printed output",
            ),
            ("pp.explicit", false, "Show implicit arguments explicitly"),
            (
                "pp.match",
                true,
                "Use `match` notation when pretty-printing",
            ),
            ("pp.instances", true, "Display instance arguments"),
            (
                "pp.instanceTypes",
                false,
                "Show the types of instance arguments",
            ),
            ("pp.beta", false, "Beta-reduce terms before pretty-printing"),
            ("pp.deepTerms", false, "Print deeply nested terms in full"),
            (
                "pp.numericTypes",
                false,
                "Annotate numeric literals with their type",
            ),
            ("pp.mvars", true, "Display metavariables"),
        ] {
            self.register(name, OptionValue::Bool(default), desc);
        }
        // Tracing options (Bool). Real Lean registers each trace class
        // individually; the ones observed by the test corpus are enumerated
        // here so an unknown `trace.*` name is still a loud error.
        for name in [
            "trace.Meta.synthInstance",
            "trace.Meta.Tactic.simp.rewrite",
            "trace.Meta.debug",
            "trace.Elab.step",
            "trace.profiler",
        ] {
            self.register(name, OptionValue::Bool(false), "Tracing flag");
        }
        // `grind` tactic warnings (Bool).
        self.register(
            "grind.warning",
            OptionValue::Bool(true),
            "Emit warnings from the `grind` tactic",
        );
        // Hygiene toggle used by macro-expansion test fixtures (Bool).
        self.register("hygiene", OptionValue::Bool(true), "Enable macro hygiene");
        // String-valued options.
        self.register(
            "trace.profiler.output",
            OptionValue::String(String::new()),
            "File to which profiler traces are written",
        );
        self.register(
            "pp.format",
            OptionValue::String(String::new()),
            "Pretty-printer output format",
        );
    }
}

// ============================================================================
// Command-level `set_option` validation
// ============================================================================

/// Global registry of standard options, built once.
///
/// The command-level `set_option` handler validates against this shared
/// registry so an unknown option name or a wrongly-typed value is a loud
/// error rather than a silent no-op (gap sweep B21).
static STANDARD_OPTION_REGISTRY: std::sync::LazyLock<OptionsRegistry> =
    std::sync::LazyLock::new(OptionsRegistry::new);

/// Infer the [`OptionValue`] kind from the raw textual value the parser stores
/// for a `set_option` command.
///
/// The parser records the value as a string: `true`/`false` for booleans,
/// decimal digits for naturals, and any other identifier / string-literal body
/// otherwise. This mirrors how Lean 4 lexes option values and lets the
/// command-level registry type-check them (Lean `src/Lean/Data/Options.lean`).
#[must_use]
pub(crate) fn infer_option_value(raw: &str) -> OptionValue {
    if raw == "true" || raw == "false" {
        OptionValue::Bool(raw == "true")
    } else if let Ok(n) = raw.parse::<u64>() {
        OptionValue::Nat(n)
    } else {
        OptionValue::String(raw.to_string())
    }
}

/// Validate a command-level `set_option <name> <value>` against the global
/// standard-option registry.
///
/// # Errors
///
/// - [`OptionError::UnknownOption`] if `name` is not a registered option
///   (Lean: `unknown option`).
/// - [`OptionError::TypeMismatch`] if `value`'s inferred kind differs from the
///   option's declared type (Lean: `set_option value type mismatch`).
pub(crate) fn validate_command_option(name: &str, value: Option<&str>) -> Result<(), OptionError> {
    let registry = &*STANDARD_OPTION_REGISTRY;
    match value {
        Some(raw) => registry.validate_option(name, &infer_option_value(raw)),
        // No explicit value (`set_option name`): reject unknown names, but there
        // is nothing to type-check.
        None if registry.is_registered(name) => Ok(()),
        None => Err(OptionError::UnknownOption {
            name: name.to_string(),
        }),
    }
}

/// Like [`validate_command_option`], but TOLERATES an unknown option NAME as a
/// no-op — the Lean-drop-in behavior.
///
/// Real Lean core and its plugins/linters register hundreds of options that
/// Clean's finite registry does not enumerate (`genInjectivity`, `linter.*`,
/// `maxSynthPendingDepth`, …). A source file that does `set_option <suchName> …`
/// (very commonly `set_option genInjectivity false in <structure>`, `set_option
/// linter.X false`) MUST still elaborate — Lean stores the key/value and only
/// code that *reads* the option is affected. Rejecting it (the original strict
/// B21 behavior) killed the whole wrapped declaration: real Mathlib
/// `Logic/Unique` / `Data/Subtype` never defined their structures, so downstream
/// (incl. the parameterized-parent-`extends` support) never ran.
///
/// A KNOWN option given a wrongly-TYPED value is still a loud [`OptionError::
/// TypeMismatch`] — that is a genuine mistake, not registry incompleteness.
///
/// Returns `Ok(true)` if the name is a known+valid option, `Ok(false)` if the
/// name was unknown and therefore tolerated as a no-op.
///
/// NOTE: this is slightly more lenient than a fully-provisioned Lean (which
/// rejects a name registered by NO loaded module); the leniency is the scalable
/// drop-in stance while Clean's option registry is incomplete. Tightening it
/// means registering the real Lean options, tracked with the registry.
pub(crate) fn validate_command_option_lenient(
    name: &str,
    value: Option<&str>,
) -> Result<bool, OptionError> {
    match validate_command_option(name, value) {
        Ok(()) => Ok(true),
        Err(OptionError::UnknownOption { .. }) => Ok(false),
        Err(e) => Err(e),
    }
}

// ============================================================================
// File-level options
// ============================================================================

/// Per-file option overrides layered on top of registry defaults.
///
/// When `set_option maxHeartbeats 400000` appears at file scope,
/// the override is stored here. Lookups fall through to the registry
/// default when no override is present.
#[derive(Debug, Clone)]
pub struct FileOptions<'a> {
    registry: &'a OptionsRegistry,
    overrides: BTreeMap<String, OptionValue>,
}

impl<'a> FileOptions<'a> {
    /// Create a new per-file options layer backed by the given registry.
    #[must_use]
    pub fn new(registry: &'a OptionsRegistry) -> Self {
        Self {
            registry,
            overrides: BTreeMap::new(),
        }
    }

    /// Set a file-level option override.
    ///
    /// # Errors
    ///
    /// - [`OptionError::UnknownOption`] if `name` is not registered.
    /// - [`OptionError::TypeMismatch`] if `value` has a different type
    ///   than the option's declared default.
    pub fn set(&mut self, name: &str, value: OptionValue) -> Result<(), OptionError> {
        let decl = self
            .registry
            .decls
            .get(name)
            .ok_or_else(|| OptionError::UnknownOption {
                name: name.to_string(),
            })?;

        let expected_kind = decl.default.kind_name();
        let actual_kind = value.kind_name();
        if expected_kind != actual_kind {
            return Err(OptionError::TypeMismatch {
                name: name.to_string(),
                expected: expected_kind,
                actual: actual_kind,
            });
        }

        self.overrides.insert(name.to_string(), value);
        Ok(())
    }

    /// Get the effective value for an option (override or default).
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&OptionValue> {
        self.overrides
            .get(name)
            .or_else(|| self.registry.get_default(name))
    }

    /// Get the effective value as a `bool`, if the option exists and is Bool.
    #[must_use]
    pub fn get_bool(&self, name: &str) -> Option<bool> {
        match self.get(name)? {
            OptionValue::Bool(v) => Some(*v),
            _ => None,
        }
    }

    /// Get the effective value as a `u64`, if the option exists and is Nat.
    #[must_use]
    pub fn get_nat(&self, name: &str) -> Option<u64> {
        match self.get(name)? {
            OptionValue::Nat(v) => Some(*v),
            _ => None,
        }
    }

    /// Get the effective value as a `&str`, if the option exists and is String.
    #[must_use]
    pub fn get_string(&self, name: &str) -> Option<&str> {
        match self.get(name)? {
            OptionValue::String(v) => Some(v.as_str()),
            _ => None,
        }
    }

    /// Get the effective value as a name `&str`, if the option exists and is Name.
    #[must_use]
    pub fn get_name(&self, name: &str) -> Option<&str> {
        match self.get(name)? {
            OptionValue::Name(v) => Some(v.as_str()),
            _ => None,
        }
    }

    /// Remove a file-level override, falling back to the registry default.
    ///
    /// Returns `true` if an override was present and removed.
    pub fn reset(&mut self, name: &str) -> bool {
        self.overrides.remove(name).is_some()
    }

    /// Whether any file-level overrides are active.
    #[must_use]
    pub fn has_overrides(&self) -> bool {
        !self.overrides.is_empty()
    }

    /// Number of active file-level overrides.
    #[must_use]
    pub fn override_count(&self) -> usize {
        self.overrides.len()
    }
}

#[cfg(test)]
#[path = "options_registry_tests.rs"]
mod tests;
