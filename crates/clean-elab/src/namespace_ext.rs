// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended namespace management: hiding, renaming, protected names, scoped
//! attributes, and resolution with suggestions.
//!
//! Reference: Lean 4 `src/Lean/ResolveName.lean` and `src/Lean/Elab/Open.lean`.

use crate::namespace::{Alias, NamespaceError, NamespaceState};
use clean_kernel::name::Name;
use clean_kernel::Environment;
use std::collections::{HashMap, HashSet};

/// Configuration for namespace extension behavior.
#[derive(Debug, Clone)]
pub(crate) struct NamespaceExtConfig {
    /// Maximum number of completion suggestions returned on resolution failure.
    pub(crate) max_suggestions: usize,
    /// Maximum edit distance for fuzzy name matching.
    pub(crate) max_edit_distance: usize,
    /// Whether to allow re-export of protected names.
    pub(crate) allow_protected_reexport: bool,
}

impl Default for NamespaceExtConfig {
    fn default() -> Self {
        Self {
            max_suggestions: 5,
            max_edit_distance: 3,
            allow_protected_reexport: false,
        }
    }
}

/// Errors specific to namespace extension operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum NamespaceExtError {
    /// A protected name was accessed without qualification.
    #[error("'{name}' is protected and requires qualified access as '{qualified}'")]
    ProtectedAccess { name: String, qualified: String },

    /// A name could not be resolved; suggestions are provided.
    #[error("unknown name '{name}'{}", format_suggestions(.suggestions))]
    UnresolvedWithSuggestions {
        name: String,
        suggestions: Vec<String>,
    },

    /// Attempted to re-export a protected name when disallowed.
    #[error("cannot re-export protected name '{0}'")]
    ProtectedReexport(String),

    /// A renaming target collides with an existing alias.
    #[error("renaming '{from}' to '{to}' conflicts with existing alias")]
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    RenamingConflict { from: String, to: String },

    /// Wraps a base namespace error.
    #[error(transparent)]
    Base(#[from] NamespaceError),
}

fn format_suggestions(suggestions: &[String]) -> String {
    if suggestions.is_empty() {
        String::new()
    } else {
        format!("; did you mean: {}?", suggestions.join(", "))
    }
}

/// A directive controlling how names are imported from a namespace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum OpenDirective {
    /// Import all names except those in the hiding set.
    Hiding(HashSet<String>),
    /// Import only the listed names.
    Selective(Vec<String>),
    /// Import all names (no filtering).
    All,
}

/// A renaming rule: `from -> to`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RenameRule {
    pub(crate) from: String,
    pub(crate) to: String,
}

/// An export filter specifying which names to re-export.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ExportFilter {
    /// Re-export all names from the source namespace.
    All,
    /// Re-export only the listed names.
    Selected(Vec<String>),
    /// Re-export all names except those in the hiding set.
    Hiding(HashSet<String>),
}

/// Extended namespace state layered on top of [`NamespaceState`].
///
/// Tracks protected names, scoped attribute associations, and provides
/// enhanced resolution with diagnostics.
#[derive(Debug, Clone, Default)]
pub(crate) struct NamespaceExt {
    /// Names marked as `protected` — require qualified access.
    protected_names: HashSet<Name>,
    /// Scoped attribute bindings: (namespace, attr_name) -> set of decl names.
    /// These attributes are active only when the namespace is opened.
    scoped_attrs: HashMap<(Name, String), HashSet<Name>>,
    /// Configuration for completion and diagnostics.
    config: NamespaceExtConfig,
}

impl NamespaceExt {
    /// Create with default configuration.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Create with custom configuration.
    #[must_use]
    pub(crate) fn with_config(config: NamespaceExtConfig) -> Self {
        Self {
            config,
            ..Default::default()
        }
    }

    /// Mark a name as protected, requiring qualified access.
    /// In Lean 4, `protected def Foo.bar` means `bar` cannot be accessed
    /// as a short name even when `Foo` is opened.
    pub(crate) fn mark_protected(&mut self, name: Name) {
        self.protected_names.insert(name);
    }

    /// Check whether a name is protected.
    #[must_use]
    pub(crate) fn is_protected(&self, name: &Name) -> bool {
        self.protected_names.contains(name)
    }

    /// Check if accessing `short` through an open namespace would violate
    /// protection. Returns the qualified form if protected.
    #[must_use]
    pub(crate) fn check_protected_access(
        &self,
        short: &str,
        state: &NamespaceState,
    ) -> Option<NamespaceExtError> {
        // Check each open namespace for a protected name matching `short`
        for open_ns in state.open_namespaces() {
            let qualified_str = format!("{}.{}", open_ns, short);
            let qualified = Name::from_string(&qualified_str);
            if self.protected_names.contains(&qualified) {
                return Some(NamespaceExtError::ProtectedAccess {
                    name: short.to_string(),
                    qualified: qualified_str,
                });
            }
        }
        None
    }

    /// Register a scoped attribute active only when `namespace` is opened.
    pub(crate) fn register_scoped_attr(
        &mut self,
        namespace: Name,
        attr_name: &str,
        decl_name: Name,
    ) {
        self.scoped_attrs
            .entry((namespace, attr_name.to_string()))
            .or_default()
            .insert(decl_name);
    }

    /// Get all declarations with the given scoped attribute that are active
    /// (i.e., their namespace is currently opened).
    #[must_use]
    pub(crate) fn get_active_scoped_attrs(
        &self,
        attr_name: &str,
        state: &NamespaceState,
    ) -> Vec<Name> {
        let mut result = Vec::new();
        for open_ns in state.open_namespaces() {
            let key = (open_ns.clone(), attr_name.to_string());
            if let Some(decls) = self.scoped_attrs.get(&key) {
                result.extend(decls.iter().cloned());
            }
        }
        result
    }

    /// Get all scoped attribute entries regardless of open state.
    #[must_use]
    pub(crate) fn get_all_scoped_attrs(&self, attr_name: &str) -> Vec<(Name, Name)> {
        let mut result = Vec::new();
        for ((ns, attr), decls) in &self.scoped_attrs {
            if attr == attr_name {
                for decl in decls {
                    result.push((ns.clone(), decl.clone()));
                }
            }
        }
        result
    }

    /// Process an open with hiding/selective/all directive and renaming rules.
    pub(crate) fn process_open_ext(
        &self,
        env: &Environment,
        namespace: &str,
        directive: &OpenDirective,
        renamings: &[RenameRule],
        state: &mut NamespaceState,
    ) -> Result<(), NamespaceExtError> {
        let ns_name = Name::from_string(namespace);
        let prefix_dot = format!("{}.", namespace);

        let mut found_any = false;
        for ci in env.constants() {
            let ci_str = ci.name.to_string();
            if let Some(suffix) = ci_str.strip_prefix(&prefix_dot) {
                // Only import direct children
                if suffix.contains('.') {
                    continue;
                }
                found_any = true;

                // Apply directive filter
                let include = match directive {
                    OpenDirective::All => true,
                    OpenDirective::Hiding(hidden) => !hidden.contains(suffix),
                    OpenDirective::Selective(names) => names.iter().any(|n| n == suffix),
                };
                if !include {
                    continue;
                }

                // Check protected names
                if self.protected_names.contains(&ci.name) {
                    continue;
                }

                let alias = apply_rename_rules(suffix, renamings);
                state.insert_alias_pub(alias, ci.name.clone());
            }
        }

        if !found_any && env.get_const(&ns_name).is_none() {
            // Empty namespace — Lean 4 treats this as a no-op
        }

        Ok(())
    }

    /// Process an export with filtering, respecting protected-name policy.
    pub(crate) fn process_export_ext(
        &self,
        env: &Environment,
        source_ns: &str,
        filter: &ExportFilter,
        current_ns: Option<&str>,
        state: &mut NamespaceState,
    ) -> Result<(), NamespaceExtError> {
        let ns_name = Name::from_string(source_ns);
        let prefix_dot = format!("{}.", source_ns);

        for ci in env.constants() {
            let ci_str = ci.name.to_string();
            if let Some(suffix) = ci_str.strip_prefix(&prefix_dot) {
                if suffix.contains('.') {
                    continue;
                }

                // Apply export filter
                let include = match filter {
                    ExportFilter::All => true,
                    ExportFilter::Selected(names) => names.iter().any(|n| n == suffix),
                    ExportFilter::Hiding(hidden) => !hidden.contains(suffix),
                };
                if !include {
                    continue;
                }

                // Check protected re-export policy
                if self.protected_names.contains(&ci.name) && !self.config.allow_protected_reexport
                {
                    return Err(NamespaceExtError::ProtectedReexport(ci_str));
                }

                // Add alias
                state.insert_alias_pub(suffix.to_string(), ci.name.clone());

                // Record export
                let export_short = if let Some(ns) = current_ns {
                    format!("{}.{}", ns, suffix)
                } else {
                    suffix.to_string()
                };
                state.push_export(Alias {
                    short: export_short,
                    target: ci.name.clone(),
                });
            }
        }

        // Handle selective export when names don't exist as direct children
        if let ExportFilter::Selected(names) = filter {
            for name in names {
                let qualified = Name::append(&ns_name, name);
                if env.get_const(&qualified).is_some() {
                    // Already handled in the loop above via prefix scanning
                    continue;
                }
                // Name not found — silently skip (Lean 4 behavior)
            }
        }

        Ok(())
    }

    /// Resolve a name, returning fuzzy suggestions on failure.
    pub(crate) fn resolve_with_suggestions(
        &self,
        short: &str,
        state: &NamespaceState,
        env: &Environment,
    ) -> Result<Name, NamespaceExtError> {
        // Check protection first
        if let Some(err) = self.check_protected_access(short, state) {
            return Err(err);
        }

        // Try normal alias resolution
        if let Some(target) = state.resolve(short) {
            return Ok(target.clone());
        }

        // Try fully qualified
        let name = Name::from_string(short);
        if env.get_const(&name).is_some() {
            return Ok(name);
        }

        // Try current namespace qualification
        let current_ns = state.current_namespace();
        if !current_ns.is_anon() {
            let qualified_str = format!("{}.{}", current_ns, short);
            let qualified = Name::from_string(&qualified_str);
            if env.get_const(&qualified).is_some() {
                return Ok(qualified);
            }
        }

        // Try open namespaces
        for open_ns in state.open_namespaces() {
            let qualified_str = format!("{}.{}", open_ns, short);
            let qualified = Name::from_string(&qualified_str);
            if env.get_const(&qualified).is_some() {
                return Ok(qualified);
            }
        }

        // Resolution failed — compute suggestions
        let suggestions = self.compute_suggestions(short, state, env);
        Err(NamespaceExtError::UnresolvedWithSuggestions {
            name: short.to_string(),
            suggestions,
        })
    }

    /// Compute name suggestions for a failed resolution.
    #[must_use]
    pub(crate) fn compute_suggestions(
        &self,
        query: &str,
        state: &NamespaceState,
        env: &Environment,
    ) -> Vec<String> {
        let mut candidates: Vec<(usize, String)> = Vec::new();
        let max_dist = self.config.max_edit_distance;

        for alias in state.aliases().keys() {
            let dist = edit_distance(query, alias);
            if dist <= max_dist {
                candidates.push((dist, alias.clone()));
            }
        }

        let mut prefixes = vec![state.current_namespace().clone()];
        prefixes.extend(state.open_namespaces().iter().cloned());

        for ci in env.constants() {
            let ci_str = ci.name.to_string();
            for prefix in &prefixes {
                let prefix_dot = if prefix.is_anon() {
                    String::new()
                } else {
                    format!("{}.", prefix)
                };
                if let Some(suffix) = ci_str.strip_prefix(&prefix_dot) {
                    if !suffix.contains('.') {
                        let dist = edit_distance(query, suffix);
                        if dist <= max_dist {
                            candidates.push((dist, suffix.to_string()));
                        }
                    }
                }
            }
        }

        // Sort by distance, deduplicate, take max
        candidates.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
        candidates.dedup_by(|a, b| a.1 == b.1);
        candidates
            .into_iter()
            .take(self.config.max_suggestions)
            .map(|(_, name)| name)
            .collect()
    }

    /// Return the configuration.
    #[must_use]
    pub(crate) fn config(&self) -> &NamespaceExtConfig {
        &self.config
    }

    /// Return the set of protected names.
    #[must_use]
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    pub(crate) fn protected_names(&self) -> &HashSet<Name> {
        &self.protected_names
    }
}

fn apply_rename_rules(short: &str, rules: &[RenameRule]) -> String {
    for rule in rules {
        if rule.from == short {
            return rule.to.clone();
        }
    }
    short.to_string()
}

/// Levenshtein edit distance for fuzzy name matching.
#[must_use]
pub(crate) fn edit_distance(a: &str, b: &str) -> usize {
    let a_bytes = a.as_bytes();
    let b_bytes = b.as_bytes();
    let m = a_bytes.len();
    let n = b_bytes.len();

    if m == 0 {
        return n;
    }
    if n == 0 {
        return m;
    }

    // Single-row DP for space efficiency
    let mut prev_row: Vec<usize> = (0..=n).collect();
    let mut curr_row = vec![0usize; n + 1];

    for i in 1..=m {
        curr_row[0] = i;
        for j in 1..=n {
            let cost = if a_bytes[i - 1] == b_bytes[j - 1] {
                0
            } else {
                1
            };
            curr_row[j] = (prev_row[j] + 1)
                .min(curr_row[j - 1] + 1)
                .min(prev_row[j - 1] + cost);
        }
        std::mem::swap(&mut prev_row, &mut curr_row);
    }

    prev_row[n]
}
