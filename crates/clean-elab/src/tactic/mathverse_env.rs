// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `MathverseEnvironment` — lazy-loading read-only environment wrapper for mathverse constants.
//!
//! Provides a separate caching layer that lazily loads mathverse library constants
//! and their transitive dependencies without polluting the user's active
//! elaboration environment. Uses an LRU cache to bound memory usage.
//!
//! # Feature gate
//!
//! This module requires the `mathverse-library` feature flag on `clean-elab`.

#[cfg(feature = "mathverse-library")]
use std::collections::VecDeque;

#[cfg(feature = "mathverse-library")]
use hashbrown::HashMap;

#[cfg(feature = "mathverse-library")]
use clean_kernel::name::Name;
#[cfg(feature = "mathverse-library")]
use clean_kernel::Declaration;

#[cfg(feature = "mathverse-library")]
use clean_mathverse::library::MathverseLibrary;
#[cfg(feature = "mathverse-library")]
use clean_mathverse::search::MathverseSearch;
#[cfg(feature = "mathverse-library")]
use clean_mathverse::types::ConstantIdx;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

#[cfg(feature = "mathverse-library")]
#[derive(Debug, thiserror::Error)]
pub(crate) enum MathverseEnvError {
    #[error("constant `{0}` not found in mathverse library")]
    NotFound(String),

    #[error("dependency budget exceeded: loaded {loaded} constants, limit is {limit}")]
    BudgetExceeded { loaded: usize, limit: usize },
}

// ---------------------------------------------------------------------------
// MathverseEnvironment
// ---------------------------------------------------------------------------

/// A caching wrapper that lazily loads mathverse constants and their transitive
/// dependencies. Maintains an LRU cache to bound memory usage.
///
/// Constants are loaded from the mathverse library's shard data and converted to
/// kernel `Declaration` objects suitable for `Environment::add_decl`.
#[cfg(feature = "mathverse-library")]
pub(crate) struct MathverseEnvironment {
    /// Loaded constants from mathverse shards, keyed by name string.
    loaded: HashMap<String, Declaration>,
    /// LRU tracking: most recently loaded names at the back.
    lru_names: VecDeque<String>,
    /// Maximum number of constants to cache.
    max_cached: usize,
}

#[cfg(feature = "mathverse-library")]
impl MathverseEnvironment {
    /// Create a new empty mathverse environment with the given cache capacity.
    pub(crate) fn new(max_cached: usize) -> Self {
        Self {
            loaded: HashMap::new(),
            lru_names: VecDeque::new(),
            max_cached,
        }
    }

    /// Drop every memoized reconstruction.
    ///
    /// MUST be called whenever the backing `MathverseLibrary` is replaced. The
    /// memo is keyed by NAME ONLY, so a name both corpora define would otherwise
    /// be served from the OLD library after the swap — while the trust gate reads
    /// the NEW library's headers. The gate would then validate one declaration
    /// and `add_decl` would install another.
    pub(crate) fn clear(&mut self) {
        self.loaded.clear();
        self.lru_names.clear();
    }

    /// Is `name`'s reconstruction memoized?
    ///
    /// A cache-occupancy predicate for the LRU tests. Deliberately NOT used by
    /// [`Self::load_with_deps`] to decide what to return: what is in this memo
    /// says nothing about what is in any caller's `Environment`, and conflating
    /// the two is exactly the bug that doc comment describes.
    #[cfg(test)]
    pub(crate) fn is_loaded(&self, name: &str) -> bool {
        self.loaded.contains_key(name)
    }

    /// Load a constant and its transitive dependencies from the mathverse library.
    ///
    /// Returns the declarations in topological order (dependencies first)
    /// suitable for sequential `Environment::add_decl` calls.
    ///
    /// # The cache is a MEMO, not a record of what some environment holds
    ///
    /// The returned vector is the constant's FULL closure every time. `loaded`
    /// memoizes the (pure) header → `Declaration` reconstruction, so a repeat
    /// call is cheap, but it never suppresses a declaration from the result.
    ///
    /// This is load-bearing, not a style choice. The cache is keyed by NAME
    /// only and has no notion of which `Environment` a previous call's
    /// declarations were registered into. It used to `continue` past any cached
    /// dependency, which is correct exactly once — for the first environment
    /// that asked. A second, fresh environment (the next file, the next test,
    /// the next `clean check` unit on the same thread) then received a SHORT
    /// closure and its constants were simply absent, surfacing later as a
    /// kernel `Unknown constant` instead of a trust diagnostic. Returning the
    /// full closure and letting the caller skip what its own environment
    /// already has (`load_candidate_closure_inner`'s `get_const(..).is_none()`
    /// guard) makes the result environment-independent by construction.
    ///
    /// # Budget
    ///
    /// At most `budget` constants will be loaded per invocation to prevent
    /// catastrophic latency from deeply-connected dependency graphs.
    pub(crate) fn load_with_deps(
        &mut self,
        name: &str,
        library: &MathverseLibrary,
        budget: usize,
    ) -> Result<Vec<Declaration>, MathverseEnvError> {
        // Find the root constant's index. This also validates the name exists.
        let root_idx = self.find_constant_idx(name, library)?;

        // Closure membership comes from walk_deps; the ORDER does not.
        //
        // `walk_deps` collects the closure by BFS and then drains it through a
        // LIFO stack (library.rs `walk_deps`, search.rs `DependencyIterator`),
        // so it yields REVERSE-BFS — which is not topological. Counter-example:
        // with A→B, A→C, C→B it yields C before B, and registering C first
        // fails with `Unknown constant: B`. Observed for real on Mathlib:
        //   checked registration for `_private.…unique_subtype_iff_existsUnique
        //   .match_1_5` failed: Unknown constant: ExistsUnique
        //
        // Registration REQUIRES dependencies before dependents, so sort the
        // closure topologically here. Fixed locally rather than in `walk_deps`
        // because that is shared API whose other callers (trust validation, the
        // inductive-family pre-pass) are order-independent, and several tests
        // assert on its current output.
        let dep_indices: Vec<ConstantIdx> =
            Self::topological_order(library, library.walk_deps(root_idx).collect());

        // Budget check.
        if dep_indices.len() > budget {
            return Err(MathverseEnvError::BudgetExceeded {
                loaded: dep_indices.len(),
                limit: budget,
            });
        }

        // Collect the FULL closure, serving already-reconstructed members from
        // the memo. See the doc comment: skipping cached members here made the
        // result depend on which environment happened to ask first.
        let mut result = Vec::new();
        for idx in &dep_indices {
            if let Some(dep_name) = library.get_name(*idx) {
                if let Some(cached) = self.loaded.get(dep_name).cloned() {
                    // Touch for LRU recency, then serve from the memo.
                    self.insert_cached(dep_name.to_string(), cached.clone());
                    result.push(cached);
                    continue;
                }

                if let Some(dep_header) = library.get_constant(*idx) {
                    let decl = self.header_to_declaration(dep_name, dep_header, library);
                    self.insert_cached(dep_name.to_string(), decl.clone());
                    result.push(decl);
                }
            }
        }

        Ok(result)
    }

    /// Order `closure` so every constant appears after the dependencies it
    /// references — the order checked registration requires.
    ///
    /// Iterative DFS post-order over the library's adjacency, restricted to
    /// `closure`. Iterative rather than recursive because a Mathlib closure is
    /// deep enough to blow the stack.
    ///
    /// CYCLES: mutual recursion and mutually-referential families make the
    /// dependency graph genuinely cyclic, so a strict topological order need not
    /// exist. A node already on the DFS path is treated as satisfied and the
    /// edge is skipped; the result is then a valid topological order for the
    /// acyclic part and a stable, deterministic order within each cycle. That is
    /// strictly better than reverse-BFS, which orders even the ACYCLIC part
    /// wrongly. A cycle that genuinely cannot be registered in any order still
    /// fails at `add_decl`, fail-closed, with the kernel's own diagnostic.
    fn topological_order(
        library: &MathverseLibrary,
        closure: Vec<ConstantIdx>,
    ) -> Vec<ConstantIdx> {
        let members: std::collections::HashSet<ConstantIdx> = closure.iter().copied().collect();
        let mut done: std::collections::HashSet<ConstantIdx> = std::collections::HashSet::new();
        let mut on_path: std::collections::HashSet<ConstantIdx> = std::collections::HashSet::new();
        let mut out: Vec<ConstantIdx> = Vec::with_capacity(closure.len());

        // (node, next-dependency-cursor)
        let mut stack: Vec<(ConstantIdx, usize)> = Vec::new();
        for &root in &closure {
            if done.contains(&root) {
                continue;
            }
            stack.push((root, 0));
            on_path.insert(root);
            while let Some((node, cursor)) = stack.pop() {
                let deps = library.deps().get(node as usize);
                let next = deps.and_then(|d| d.get(cursor)).copied();
                match next {
                    Some(dep) => {
                        stack.push((node, cursor + 1));
                        // Skip deps outside the closure, already emitted, or on
                        // the current path (a cycle edge).
                        if members.contains(&dep) && !done.contains(&dep) && !on_path.contains(&dep)
                        {
                            stack.push((dep, 0));
                            on_path.insert(dep);
                        }
                    }
                    None => {
                        // All dependencies emitted: this node is now safe.
                        on_path.remove(&node);
                        if done.insert(node) {
                            out.push(node);
                        }
                    }
                }
            }
        }
        out
    }

    /// Number of currently cached constants.
    #[cfg(test)]
    pub(crate) fn cached_count(&self) -> usize {
        self.loaded.len()
    }

    // -----------------------------------------------------------------------
    // Internal helpers
    // -----------------------------------------------------------------------

    /// Find the global ConstantIdx for a named constant in the library.
    fn find_constant_idx(
        &self,
        name: &str,
        library: &MathverseLibrary,
    ) -> Result<ConstantIdx, MathverseEnvError> {
        // The library uses walk_deps which needs a ConstantIdx.
        // We search linearly since MathverseLibrary doesn't expose name_to_idx directly.
        for idx in 0..library.constant_count() {
            if let Some(n) = library.get_name(idx as ConstantIdx) {
                if n == name {
                    return Ok(idx as ConstantIdx);
                }
            }
        }
        Err(MathverseEnvError::NotFound(name.to_string()))
    }

    /// Convert an mathverse constant header into a kernel Declaration.
    ///
    /// Reconstructs the real type and value expressions from the library's merged
    /// FlatExpr/FlatLevel/string tables via `reconstruct_from_shard()`.
    /// Falls back to `Expr::sort(Level::zero())` if reconstruction fails.
    ///
    /// Reconstructs declaration-level universe parameter names from the shard's
    /// string table via `reconstruct_level_params()`. Falls back to empty params
    /// if reconstruction fails (e.g. for v1 shards without level_params fields).
    fn header_to_declaration(
        &self,
        name: &str,
        header: &clean_mathverse::types::MathverseConstantHeader,
        library: &MathverseLibrary,
    ) -> Declaration {
        use clean_mathverse::shard_reconstruct::{
            reconstruct_level_params, reconstruct_single_subdag_public,
        };

        let decl_name = Name::from_string(name);

        // Reconstruct declaration-level universe parameter names from the
        // shard's string table. Falls back to empty if reconstruction fails.
        let level_params = reconstruct_level_params(
            library.strings(),
            header.level_params_start,
            header.level_params_count,
        )
        .unwrap_or_default();

        // Reconstruct the real type expression from the shard data.
        //
        // MUST pass `library.level_lists()`. The no-arg `reconstruct_from_shard`
        // hardcodes an empty level-list table (shard_reconstruct.rs:56-63), which
        // rebuilds EVERY `Const` with `vec![]` universe arguments — collapsing
        // `Const(Eq, [u])` to `Const(Eq, [])` and failing `add_decl` with
        // `LevelCountMismatch { expected: 1, got: 0 }` for every reference to a
        // universe-polymorphic constant. The writer side already documents this
        // exact failure (lean4/env_import.rs:255-262); the consumer side was
        // never updated.
        let type_expr = reconstruct_single_subdag_public(
            library.exprs(),
            library.levels(),
            library.strings(),
            library.level_lists(),
            header.type_idx,
        )
        .unwrap_or_else(|_| clean_kernel::Expr::sort(clean_kernel::Level::zero()));

        if header.has_value() {
            // Try to reconstruct the value (proof term) for theorems/definitions.
            // If reconstruction fails, fall back to Axiom with the real type.
            //
            // SOUNDNESS: We use add_decl_unchecked for mathverse library constants
            // because the constants were already verified at shard build time.
            // The trust level is tracked via ImportConfidence in the shard header,
            // and the mathverse_use tactic gates on trust level before applying.
            // See #3359 for the trust gating design.
            if let Ok(value_expr) = reconstruct_single_subdag_public(
                library.exprs(),
                library.levels(),
                library.strings(),
                library.level_lists(),
                header.value_idx,
            ) {
                // Preserve the DECLARATION KIND. Registering everything
                // value-bearing as a `Theorem` was wrong twice over: it rejected
                // real definitions downstream (`can_replay_missing_dependency`),
                // and it silently changed their reduction behaviour — a
                // `Definition` is delta-reducible, a `Theorem` is proof-irrelevant
                // and is not unfolded the same way. Mathlib closures are full of
                // match auxiliaries (`....match_1_5`) and other private
                // definitions whose bodies MUST unfold for defeq to succeed.
                match header.decl_kind() {
                    Ok(clean_mathverse::types::DeclKind::Definition) => Declaration::Definition {
                        name: decl_name,
                        level_params: level_params.clone(),
                        type_: type_expr,
                        value: value_expr,
                        // Conservative: not eagerly unfolded. The kernel can
                        // still delta-reduce on demand; marking every imported
                        // definition reducible would change unfolding strategy
                        // corpus-wide.
                        is_reducible: false,
                    },
                    Ok(clean_mathverse::types::DeclKind::Opaque) => Declaration::Opaque {
                        name: decl_name,
                        level_params: level_params.clone(),
                        type_: type_expr,
                        value: value_expr,
                    },
                    _ => Declaration::Theorem {
                        name: decl_name,
                        level_params: level_params.clone(),
                        type_: type_expr,
                        value: value_expr,
                    },
                }
            } else {
                // Value reconstruction failed; register as axiom with real type.
                Declaration::Axiom {
                    name: decl_name,
                    level_params,
                    type_: type_expr,
                }
            }
        } else {
            // Axiomatized constant: no proof term.
            Declaration::Axiom {
                name: decl_name,
                level_params,
                type_: type_expr,
            }
        }
    }

    /// Insert a declaration into the LRU cache, evicting the oldest if full.
    fn insert_cached(&mut self, name: String, decl: Declaration) {
        // If already present, move to back of LRU.
        if self.loaded.contains_key(&name) {
            self.lru_names.retain(|n| n != &name);
            self.lru_names.push_back(name);
            return;
        }

        // Evict oldest entries if at capacity.
        while self.loaded.len() >= self.max_cached {
            if let Some(evicted) = self.lru_names.pop_front() {
                self.loaded.remove(&evicted);
            } else {
                break;
            }
        }

        self.loaded.insert(name.clone(), decl);
        self.lru_names.push_back(name);
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[cfg(feature = "mathverse-library")]
mod tests {
    use super::*;
    use clean_kernel::flat::{FlatExpr, FlatLevel};
    use clean_mathverse::shard::{ShardReader, ShardWriter};
    use clean_mathverse::trust::policy::TrustPolicy;
    use clean_mathverse::types::{
        AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
    };

    /// Helper: build a test shard with named constants.
    fn build_test_shard(names: &[&str]) -> ShardReader {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));

        for &name in names {
            let ni = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        ShardReader::from_bytes(&buf).unwrap()
    }

    #[test]
    fn test_mathverse_env_new_is_empty() {
        let env = MathverseEnvironment::new(100);
        assert_eq!(env.cached_count(), 0);
        assert!(!env.is_loaded("anything"));
    }

    #[test]
    fn test_mathverse_env_load_with_deps_not_found() {
        let mut env = MathverseEnvironment::new(100);
        let lib = MathverseLibrary::new(TrustPolicy::permissive());
        let result = env.load_with_deps("Nonexistent", &lib, 1000);
        assert!(result.is_err());
    }

    #[test]
    fn test_mathverse_env_load_with_deps_single() {
        let shard = build_test_shard(&["Nat.add_comm"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        let mut env = MathverseEnvironment::new(100);
        let decls = env.load_with_deps("Nat.add_comm", &lib, 1000).unwrap();

        assert!(!decls.is_empty());
        assert!(env.is_loaded("Nat.add_comm"));
    }

    #[test]
    fn test_mathverse_env_load_with_deps_transitive() {
        let shard = build_test_shard(&["base", "dep1", "dep2"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Add deps: base(0) -> dep1(1) -> dep2(2)
        lib.add_dependency(0, 1);
        lib.add_dependency(1, 2);

        let mut env = MathverseEnvironment::new(100);
        let decls = env.load_with_deps("base", &lib, 1000).unwrap();

        // Should load all 3 (base + dep1 + dep2).
        assert_eq!(decls.len(), 3);
        assert!(env.is_loaded("base"));
        assert!(env.is_loaded("dep1"));
        assert!(env.is_loaded("dep2"));
    }

    /// The cache memoizes reconstruction; it must NOT shorten the closure.
    ///
    /// It is keyed by name only and knows nothing about which `Environment` a
    /// previous call's declarations went into, so suppressing cached members
    /// handed the SECOND environment to ask an incomplete closure — the
    /// constants were then absent and surfaced as a kernel `Unknown constant`
    /// rather than a trust diagnostic. Callers de-duplicate against their own
    /// environment instead.
    #[test]
    fn test_mathverse_env_load_with_deps_repeat_returns_full_closure() {
        let shard = build_test_shard(&["a", "b"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        lib.add_dependency(0, 1);

        let mut env = MathverseEnvironment::new(100);

        // First load: both a and b.
        let decls1 = env.load_with_deps("a", &lib, 1000).unwrap();
        assert_eq!(decls1.len(), 2);

        // Second load: SAME full closure, served from the memo.
        let decls2 = env.load_with_deps("a", &lib, 1000).unwrap();
        assert_eq!(
            decls2.len(),
            2,
            "a repeat load must still describe the whole closure; the cache is a \
             reconstruction memo, not a record of some environment's contents"
        );
    }

    #[test]
    fn test_mathverse_env_budget_exceeded() {
        let shard = build_test_shard(&["a", "b", "c", "d", "e"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Chain deps so all are reachable from a.
        lib.add_dependency(0, 1);
        lib.add_dependency(1, 2);
        lib.add_dependency(2, 3);
        lib.add_dependency(3, 4);

        let mut env = MathverseEnvironment::new(100);
        // Budget of 3 should fail since dep closure is 5.
        let result = env.load_with_deps("a", &lib, 3);
        assert!(result.is_err());
        match result.unwrap_err() {
            MathverseEnvError::BudgetExceeded { loaded, limit } => {
                assert_eq!(limit, 3);
                assert!(loaded > 3);
            }
            other => panic!("expected BudgetExceeded, got {other:?}"),
        }
    }

    #[test]
    fn test_mathverse_env_lru_eviction() {
        let shard = build_test_shard(&["a", "b", "c", "d"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();

        // Cache capacity of 2.
        let mut env = MathverseEnvironment::new(2);

        // Load a (no deps beyond itself).
        env.load_with_deps("a", &lib, 1000).unwrap();
        assert_eq!(env.cached_count(), 1);
        assert!(env.is_loaded("a"));

        // Load b.
        env.load_with_deps("b", &lib, 1000).unwrap();
        assert_eq!(env.cached_count(), 2);
        assert!(env.is_loaded("a"));
        assert!(env.is_loaded("b"));

        // Load c — should evict a (LRU).
        env.load_with_deps("c", &lib, 1000).unwrap();
        assert_eq!(env.cached_count(), 2);
        assert!(!env.is_loaded("a"), "a should have been evicted");
        assert!(env.is_loaded("b"));
        assert!(env.is_loaded("c"));

        // Load d — should evict b.
        env.load_with_deps("d", &lib, 1000).unwrap();
        assert_eq!(env.cached_count(), 2);
        assert!(!env.is_loaded("b"), "b should have been evicted");
        assert!(env.is_loaded("c"));
        assert!(env.is_loaded("d"));
    }
}
