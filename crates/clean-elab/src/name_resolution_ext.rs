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
    Alias(Name),
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
    aliases: HashMap<Name, Name>,
    /// Local bindings that shadow everything else.
    local_names: HashSet<Name>,
    /// Auto-open namespace associations: type name -> namespace to open.
    auto_open_map: HashMap<Name, Name>,
    /// Last observations by exact Name; never reused against an unbound context.
    cache: HashMap<Name, ResolutionResult>,
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
    pub(crate) fn register_alias(&mut self, short: &Name, target: Name) {
        self.aliases.insert(short.clone(), target);
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

    /// Resolve a name with full priority ordering and retained observations.
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
        let key = name.clone();
        // The caller owns and may mutate both semantic contexts. A query-only
        // cache cannot certify that a previous positive or negative still holds.
        // Recompute before recording; no address- or display-based context key.
        let result = self.resolve_uncached(name, ns_state, env);

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

        // 2. A structurally qualified name is tried as fully qualified first
        if !crate::namespace::parent_name(name).is_anon() {
            if let Some(result) = self.resolve_qualified(name, env) {
                return result;
            }
        }

        // 3. Current namespace qualification
        let current_ns = ns_state.current_namespace();
        if !current_ns.is_anon() {
            let qualified = crate::namespace::append_names(current_ns, name);
            if env.get_const(&qualified).is_some() {
                return ResolutionResult::Resolved(ResolutionCandidate {
                    name: qualified,
                    source: ResolutionSource::Local,
                });
            }
        }

        // 4. Open namespaces
        let open_candidates = self.resolve_through_opens(name, ns_state, env);
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
        if let Some(target) = self.aliases.get(name) {
            if env.get_const(target).is_some() {
                return ResolutionResult::Resolved(ResolutionCandidate {
                    name: target.clone(),
                    source: ResolutionSource::Alias(name.clone()),
                });
            }
        }

        // 6. Auto-open namespaces
        if self.config.auto_open {
            let auto_candidates = self.resolve_through_auto_open(name, env);
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

    /// Resolve an exact structurally qualified name without a text round-trip.
    fn resolve_qualified(&self, name: &Name, env: &Environment) -> Option<ResolutionResult> {
        // Direct match
        if env.get_const(name).is_some() {
            return Some(ResolutionResult::Resolved(ResolutionCandidate {
                name: name.clone(),
                source: ResolutionSource::Global,
            }));
        }

        None
    }

    /// Collect candidates from opened namespaces, filtering out protected names.
    fn resolve_through_opens(
        &self,
        name: &Name,
        ns_state: &NamespaceState,
        env: &Environment,
    ) -> Vec<ResolutionCandidate> {
        let mut candidates = Vec::new();
        let mut seen = BTreeSet::new();

        // First check aliases from NamespaceState (set by process_open)
        if let Some(target) = ns_state.resolve(name) {
            if !self.protected_names.contains(target)
                && env.get_const(target).is_some()
                && seen.insert(target.clone())
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
            let qualified = crate::namespace::append_names(open_ns, name);

            if self.protected_names.contains(&qualified) {
                continue;
            }

            if env.get_const(&qualified).is_some() && seen.insert(qualified.clone()) {
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
        for open_ns in ns_state.open_namespaces() {
            if target != open_ns && crate::namespace::name_has_prefix(target, open_ns) {
                return ResolutionSource::OpenNamespace(open_ns.clone());
            }
        }
        ResolutionSource::Global
    }

    /// Collect candidates from auto-open namespace associations.
    fn resolve_through_auto_open(
        &self,
        name: &Name,
        env: &Environment,
    ) -> Vec<ResolutionCandidate> {
        let mut candidates = Vec::new();
        let mut seen = BTreeSet::new();
        for namespace in self.auto_open_map.values() {
            let qualified = crate::namespace::append_names(namespace, name);
            if env.get_const(&qualified).is_some() && seen.insert(qualified.clone()) {
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

#[cfg(test)]
mod typed_tests {
    use super::*;

    fn add(env: &mut Environment, name: Name) {
        env.add_decl_structural(clean_kernel::env::Declaration::Axiom {
            name,
            level_params: vec![],
            type_: Expr::type_(),
        })
        .unwrap();
    }

    fn exact(result: ResolutionResult, name: Name) {
        let ResolutionResult::Resolved(candidate) = result else {
            panic!("not exactly resolved: {result:?}")
        };
        assert_eq!(candidate.name, name);
    }

    #[test]
    fn resolver_observation_keys_keep_display_and_numeric_twins() {
        let env = Environment::new();
        let state = NamespaceState::new();
        let mut resolver = NameResolutionExt::new();
        let names = [
            Name::anon().str("A.B"),
            Name::anon().str("A").str("B"),
            Name::anon().str("7"),
            Name::anon().num(7),
        ];
        for name in &names {
            resolver.register_local(name.clone());
        }
        for name in &names {
            exact(resolver.resolve(name, &state, &env), name.clone());
        }
        assert_eq!(resolver.cache_size(), names.len());
    }

    #[test]
    fn switched_namespace_does_not_reuse_prior_query_result() {
        let mut env = Environment::new();
        let a = Name::anon().str("A");
        let b = Name::anon().str("B");
        let h = Name::anon().str("h");
        add(&mut env, a.clone().str("h"));
        add(&mut env, b.clone().str("h"));
        let mut first = NamespaceState::new();
        first.enter_namespace(a.clone());
        let mut second = NamespaceState::new();
        second.enter_namespace(b.clone());
        let mut resolver = NameResolutionExt::new();
        exact(resolver.resolve(&h, &first, &env), a.str("h"));
        exact(resolver.resolve(&h, &second, &env), b.str("h"));
    }

    #[test]
    fn added_constant_invalidates_an_observed_negative_without_a_manual_hook() {
        let mut env = Environment::new();
        let state = NamespaceState::new();
        let mut resolver = NameResolutionExt::new();
        let name = Name::anon().str("new.const");
        assert_eq!(
            resolver.resolve(&name, &state, &env),
            ResolutionResult::Unresolved
        );
        add(&mut env, name.clone());
        exact(resolver.resolve(&name, &state, &env), name);
    }

    #[test]
    fn repeated_auto_open_namespace_does_not_invent_ambiguity() {
        let mut env = Environment::new();
        let namespace = Name::anon().str("N.dot");
        let target = namespace.clone().str("f");
        add(&mut env, target.clone());
        let mut resolver = NameResolutionExt::new();
        resolver.register_auto_open(Name::anon().str("T"), namespace.clone());
        resolver.register_auto_open(Name::anon().str("Other"), namespace);
        exact(
            resolver.resolve(&Name::anon().str("f"), &NamespaceState::new(), &env),
            target,
        );
    }
}
