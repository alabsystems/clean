// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended name resolution for the elaborator.
//!
//! Builds on [`crate::name_resolution`] with:
//! - Qualified name resolution (`Foo.bar.baz` through nested namespaces)
//! - Open namespace resolution (unqualified names through opened namespaces)
//! - Alias resolution (`export` and `alias` declarations)
//! - Overload resolution (type-directed disambiguation of overloaded names)
//! - Protected name resolution (`protected` visibility modifier)
//! - Auto-open resolution (associated namespaces for types)
//! - Resolution priority ordering: local > open > alias > global
//! - Ambiguity reporting with all candidate names
//! - Resolution caching for repeated lookups
//!
//! Reference: Lean 4 `src/Lean/ResolveName.lean`.

use crate::namespace::NamespaceState;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind};
use std::collections::{BTreeSet, HashMap, HashSet};

/// Configuration for extended name resolution.
#[derive(Debug, Clone)]
pub(crate) struct NameResolutionExtConfig {
    /// Whether to enable resolution caching.
    pub(crate) enable_cache: bool,
    /// Whether to auto-open associated namespaces for types.
    pub(crate) auto_open: bool,
    /// Maximum candidates to report in ambiguity errors.
    pub(crate) max_ambiguity_candidates: usize,
}

impl Default for NameResolutionExtConfig {
    fn default() -> Self {
        Self {
            enable_cache: true,
            auto_open: true,
            max_ambiguity_candidates: 10,
        }
    }
}

/// The source that provided a resolved name, ordered by priority.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ResolutionSource {
    /// Name matched as a local binding (highest priority).
    Local,
    /// Name found through an opened namespace.
    OpenNamespace(Name),
    /// Name found through an alias (export/alias declaration).
    Alias(String),
    /// Name found as a fully qualified global constant.
    Global,
    /// Name found via auto-opened associated namespace.
    AutoOpen(Name),
}

/// A single resolution candidate: a fully-qualified name plus its source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolutionCandidate {
    /// The fully-qualified name in the environment.
    pub(crate) name: Name,
    /// How this candidate was found.
    pub(crate) source: ResolutionSource,
}

/// The result of extended name resolution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ResolutionResult {
    /// Exactly one candidate found.
    Resolved(ResolutionCandidate),
    /// Multiple candidates found — caller must disambiguate.
    Ambiguous(Vec<ResolutionCandidate>),
    /// No candidates found.
    Unresolved,
}

/// Extended name resolver with caching, overload disambiguation, and
/// priority-ordered lookup.
#[derive(Debug, Clone, Default)]
pub(crate) struct NameResolutionExt {
    /// Configuration.
    config: NameResolutionExtConfig,
    /// Names marked as `protected` — skip during unqualified open lookup.
    protected_names: HashSet<Name>,
    /// Explicit aliases: short name -> qualified target.
    aliases: HashMap<String, Name>,
    /// Local bindings that shadow everything else.
    local_names: HashSet<Name>,
    /// Auto-open namespace associations: type name -> namespace to open.
    auto_open_map: HashMap<Name, Name>,
    /// Resolution cache: input name string -> cached result.
    cache: HashMap<String, ResolutionResult>,
}

impl NameResolutionExt {
    /// Create with default configuration.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Create with custom configuration.
    #[must_use]
    pub(crate) fn with_config(config: NameResolutionExtConfig) -> Self {
        Self {
            config,
            ..Default::default()
        }
    }

    /// Return the configuration.
    #[must_use]
    pub(crate) fn config(&self) -> &NameResolutionExtConfig {
        &self.config
    }

    // =========================================================================
    // Registration
    // =========================================================================

    /// Mark a name as protected — it will be skipped during unqualified
    /// open-namespace lookup (still accessible via full qualification).
    pub(crate) fn mark_protected(&mut self, name: Name) {
        self.protected_names.insert(name);
        self.invalidate_cache();
    }

    /// Check whether a name is protected.
    #[must_use]
    pub(crate) fn is_protected(&self, name: &Name) -> bool {
        self.protected_names.contains(name)
    }

    /// Register an alias: `short` resolves to `target`.
    pub(crate) fn register_alias(&mut self, short: &str, target: Name) {
        self.aliases.insert(short.to_string(), target);
        self.invalidate_cache();
    }

    /// Register a local binding (highest priority in resolution).
    pub(crate) fn register_local(&mut self, name: Name) {
        self.local_names.insert(name);
        self.invalidate_cache();
    }

    /// Remove a local binding.
    pub(crate) fn unregister_local(&mut self, name: &Name) {
        self.local_names.remove(name);
        self.invalidate_cache();
    }

    /// Register an auto-open association: when `type_name` is used,
    /// automatically open `namespace` for resolution.
    pub(crate) fn register_auto_open(&mut self, type_name: Name, namespace: Name) {
        self.auto_open_map.insert(type_name, namespace);
        self.invalidate_cache();
    }

    /// Clear the resolution cache (called automatically on state mutations).
    pub(crate) fn invalidate_cache(&mut self) {
        self.cache.clear();
    }

    /// Return the number of cached entries.
    #[must_use]
    pub(crate) fn cache_size(&self) -> usize {
        self.cache.len()
    }

    // =========================================================================
    // Core resolution
    // =========================================================================

    /// Resolve a name with full priority ordering and caching.
    ///
    /// Priority: local > current namespace > open namespace > alias > auto-open > global.
    ///
    /// Returns `ResolutionResult::Resolved` for a unique match,
    /// `Ambiguous` when multiple candidates exist at the same priority level,
    /// or `Unresolved` when nothing matches.
    #[must_use]
    pub(crate) fn resolve(
        &mut self,
        name: &Name,
        ns_state: &NamespaceState,
        env: &Environment,
    ) -> ResolutionResult {
        let key = name.to_string();
        if self.config.enable_cache {
            if let Some(cached) = self.cache.get(&key) {
                return cached.clone();
            }
        }

        let result = self.resolve_uncached(name, &key, ns_state, env);

        if self.config.enable_cache {
            self.cache.insert(key, result.clone());
        }
        result
    }

    /// Resolve without consulting or populating the cache.
    #[must_use]
    pub(crate) fn resolve_uncached(
        &self,
        name: &Name,
        name_str: &str,
        ns_state: &NamespaceState,
        env: &Environment,
    ) -> ResolutionResult {
        if name.is_anon() {
            return ResolutionResult::Unresolved;
        }

        // 1. Local bindings (highest priority)
        if self.local_names.contains(name) {
            return ResolutionResult::Resolved(ResolutionCandidate {
                name: name.clone(),
                source: ResolutionSource::Local,
            });
        }

        // 2. Qualified name — if it contains a dot, try as fully qualified first
        if name_str.contains('.') {
            if let Some(result) = self.resolve_qualified(name, name_str, env) {
                return result;
            }
        }

        // 3. Current namespace qualification
        let current_ns = ns_state.current_namespace();
        if !current_ns.is_anon() {
            let qualified_str = format!("{current_ns}.{name_str}");
            let qualified = Name::from_string(&qualified_str);
            if env.get_const(&qualified).is_some() {
                return ResolutionResult::Resolved(ResolutionCandidate {
                    name: qualified,
                    source: ResolutionSource::Local,
                });
            }
        }

        // 4. Open namespaces
        let open_candidates = self.resolve_through_opens(name_str, ns_state, env);
        if open_candidates.len() == 1 {
            return ResolutionResult::Resolved(
                open_candidates
                    .into_iter()
                    .next()
                    .expect("invariant: checked len == 1"),
            );
        }
        if open_candidates.len() > 1 {
            return self.build_ambiguous(open_candidates);
        }

        // 5. Alias resolution
        if let Some(target) = self.aliases.get(name_str) {
            if env.get_const(target).is_some() {
                return ResolutionResult::Resolved(ResolutionCandidate {
                    name: target.clone(),
                    source: ResolutionSource::Alias(name_str.to_string()),
                });
            }
        }

        // 6. Auto-open namespaces
        if self.config.auto_open {
            let auto_candidates = self.resolve_through_auto_open(name_str, env);
            if auto_candidates.len() == 1 {
                return ResolutionResult::Resolved(
                    auto_candidates
                        .into_iter()
                        .next()
                        .expect("invariant: checked len == 1"),
                );
            }
            if auto_candidates.len() > 1 {
                return self.build_ambiguous(auto_candidates);
            }
        }

        // 7. Global fully-qualified
        if env.get_const(name).is_some() {
            return ResolutionResult::Resolved(ResolutionCandidate {
                name: name.clone(),
                source: ResolutionSource::Global,
            });
        }

        ResolutionResult::Unresolved
    }

    /// Attempt to resolve a dotted qualified name by walking namespace
    /// segments. For `Foo.bar.baz`, tries `Foo.bar.baz` directly, then
    /// checks if `Foo.bar` is a namespace containing `baz`.
    fn resolve_qualified(
        &self,
        name: &Name,
        name_str: &str,
        env: &Environment,
    ) -> Option<ResolutionResult> {
        // Direct match
        if env.get_const(name).is_some() {
            return Some(ResolutionResult::Resolved(ResolutionCandidate {
                name: name.clone(),
                source: ResolutionSource::Global,
            }));
        }

        // Try splitting at each dot from the right to resolve partial qualification
        let mut dot_pos = name_str.len();
        while let Some(pos) = name_str[..dot_pos].rfind('.') {
            let prefix = &name_str[..pos];
            let suffix = &name_str[pos + 1..];
            let qualified = Name::from_string(name_str);

            // If the full dotted name exists, we already checked above.
            // Check if prefix is a known namespace and suffix resolves within it.
            let candidate = Name::from_string(&format!("{prefix}.{suffix}"));
            if env.get_const(&candidate).is_some() {
                return Some(ResolutionResult::Resolved(ResolutionCandidate {
                    name: qualified,
                    source: ResolutionSource::Global,
                }));
            }
            dot_pos = pos;
        }

        None
    }

    /// Collect candidates from opened namespaces, filtering out protected names.
    fn resolve_through_opens(
        &self,
        name_str: &str,
        ns_state: &NamespaceState,
        env: &Environment,
    ) -> Vec<ResolutionCandidate> {
        let mut candidates = Vec::new();
        let mut seen = BTreeSet::new();

        // First check aliases from NamespaceState (set by process_open)
        if let Some(target) = ns_state.resolve(name_str) {
            if !self.protected_names.contains(target)
                && env.get_const(target).is_some()
                && seen.insert(target.to_string())
            {
                // Determine which open namespace produced this alias
                let source = self.find_alias_source(target, ns_state);
                candidates.push(ResolutionCandidate {
                    name: target.clone(),
                    source,
                });
            }
        }

        // Also try qualifying with each open namespace
        for open_ns in ns_state.open_namespaces() {
            let qualified_str = format!("{open_ns}.{name_str}");
            let qualified = Name::from_string(&qualified_str);

            if self.protected_names.contains(&qualified) {
                continue;
            }

            if env.get_const(&qualified).is_some() && seen.insert(qualified_str) {
                candidates.push(ResolutionCandidate {
                    name: qualified,
                    source: ResolutionSource::OpenNamespace(open_ns.clone()),
                });
            }
        }

        candidates
    }

    /// Determine which open namespace sourced a given resolved name.
    fn find_alias_source(&self, target: &Name, ns_state: &NamespaceState) -> ResolutionSource {
        let target_str = target.to_string();
        for open_ns in ns_state.open_namespaces() {
            let prefix = format!("{open_ns}.");
            if target_str.starts_with(&prefix) {
                return ResolutionSource::OpenNamespace(open_ns.clone());
            }
        }
        ResolutionSource::Global
    }

    /// Collect candidates from auto-open namespace associations.
    fn resolve_through_auto_open(
        &self,
        name_str: &str,
        env: &Environment,
    ) -> Vec<ResolutionCandidate> {
        let mut candidates = Vec::new();
        for namespace in self.auto_open_map.values() {
            let qualified_str = format!("{namespace}.{name_str}");
            let qualified = Name::from_string(&qualified_str);
            if env.get_const(&qualified).is_some() {
                candidates.push(ResolutionCandidate {
                    name: qualified,
                    source: ResolutionSource::AutoOpen(namespace.clone()),
                });
            }
        }
        candidates
    }

    /// Build an ambiguous result, capping the number of candidates.
    fn build_ambiguous(&self, candidates: Vec<ResolutionCandidate>) -> ResolutionResult {
        let max = self.config.max_ambiguity_candidates;
        if candidates.len() > max {
            ResolutionResult::Ambiguous(candidates.into_iter().take(max).collect())
        } else {
            ResolutionResult::Ambiguous(candidates)
        }
    }

    // =========================================================================
    // Overload disambiguation
    // =========================================================================

    /// Disambiguate an ambiguous resolution using a type hint.
    ///
    /// Filters candidates to those whose constant type in the environment
    /// matches (or is compatible with) `expected_type`. If exactly one
    /// survives, return it as resolved.
    #[must_use]
    pub(crate) fn disambiguate_by_type(
        &self,
        candidates: &[ResolutionCandidate],
        expected_type: &Expr,
        env: &Environment,
    ) -> ResolutionResult {
        let filtered: Vec<ResolutionCandidate> = candidates
            .iter()
            .filter(|c| {
                if let Some(ci) = env.get_const(&c.name) {
                    type_compatible(&ci.type_, expected_type)
                } else {
                    false
                }
            })
            .cloned()
            .collect();

        match filtered.len() {
            0 => ResolutionResult::Ambiguous(candidates.to_vec()),
            1 => ResolutionResult::Resolved(
                filtered
                    .into_iter()
                    .next()
                    .expect("invariant: checked len == 1"),
            ),
            _ => ResolutionResult::Ambiguous(filtered),
        }
    }

    // =========================================================================
    // Ambiguity reporting
    // =========================================================================

    /// Format an ambiguity error message listing all candidates.
    #[must_use]
    pub(crate) fn format_ambiguity(candidates: &[ResolutionCandidate]) -> String {
        if candidates.is_empty() {
            return String::from("no candidates");
        }
        let names: Vec<String> = candidates.iter().map(|c| c.name.to_string()).collect();
        format!("ambiguous, could be any of: {}", names.join(", "))
    }

    /// Collect all candidate names as a vec (for error reporting).
    #[must_use]
    pub(crate) fn candidate_names(candidates: &[ResolutionCandidate]) -> Vec<Name> {
        candidates.iter().map(|c| c.name.clone()).collect()
    }
}

/// Shallow type compatibility check: returns true if two expressions share
/// the same outermost constructor AND (for variants that carry payload
/// meaningful to disambiguation) compatible payloads. A full definitional
/// equality check belongs to the type checker; this is a fast heuristic
/// for disambiguation.
///
/// Wave 96 (Gap 14): the previous variant used only
/// `std::mem::discriminant`, which lumped `Prop` and `Type` together
/// (both `ExprKind::Sort`) and so could not prune `Nat.add : Type` when
/// the expected type was `Prop`. We now refine the comparison on the
/// payload for `Sort`, `Const`, and `Pi`, while keeping behaviour
/// conservative: `App`, `Lam`, `BVar`, `FVar`, `MVar`, `Lit`, and
/// metadata-bearing variants still compare only by discriminant (the
/// elaborator will run the full check downstream).
fn type_compatible(actual: &Expr, expected: &Expr) -> bool {
    if std::mem::discriminant(actual.kind()) != std::mem::discriminant(expected.kind()) {
        return false;
    }
    match (actual.kind(), expected.kind()) {
        // Distinguish Prop (Sort 0) from Type (Sort 1) and higher.
        (ExprKind::Sort(a), ExprKind::Sort(b)) => a == b,
        // For constants, the head name must match — `Nat` is not `Int`.
        (ExprKind::Const(an, _), ExprKind::Const(bn, _)) => an == bn,
        // For Pi/arrow types, compare the codomain shape (most
        // function-style overloads differ in result type, not argument
        // shape). This is still shallow; the kernel handles the rest.
        (ExprKind::Pi(_, _, ab), ExprKind::Pi(_, _, bb)) => type_compatible(ab, bb),
        // Otherwise the discriminant match is sufficient.
        _ => true,
    }
}
