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

    /// Check if a constant is already loaded in the cache.
    pub(crate) fn is_loaded(&self, name: &str) -> bool {
        self.loaded.contains_key(name)
    }

    /// Load a constant and its transitive dependencies from the mathverse library.
    ///
    /// Returns the declarations in topological order (dependencies first)
    /// suitable for sequential `Environment::add_decl` calls.
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

        // BFS/topological walk via the library's walk_deps.
        let dep_indices: Vec<ConstantIdx> = library.walk_deps(root_idx).collect();

        // Budget check.
        if dep_indices.len() > budget {
            return Err(MathverseEnvError::BudgetExceeded {
                loaded: dep_indices.len(),
                limit: budget,
            });
        }

        // Collect declarations for constants not yet loaded.
        let mut result = Vec::new();
        for idx in &dep_indices {
            if let Some(dep_name) = library.get_name(*idx) {
                if self.is_loaded(dep_name) {
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
            reconstruct_from_shard, reconstruct_level_params,
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
        let type_expr = reconstruct_from_shard(
            library.exprs(),
            library.levels(),
            library.strings(),
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
            if let Ok(value_expr) = reconstruct_from_shard(
                library.exprs(),
                library.levels(),
                library.strings(),
                header.value_idx,
            ) {
                Declaration::Theorem {
                    name: decl_name,
                    level_params: level_params.clone(),
                    type_: type_expr,
                    value: value_expr,
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

    #[test]
    fn test_mathverse_env_load_with_deps_already_cached() {
        let shard = build_test_shard(&["a", "b"]);
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&shard).unwrap();
        lib.add_dependency(0, 1);

        let mut env = MathverseEnvironment::new(100);

        // First load: both a and b.
        let decls1 = env.load_with_deps("a", &lib, 1000).unwrap();
        assert_eq!(decls1.len(), 2);

        // Second load: already cached, should return empty.
        let decls2 = env.load_with_deps("a", &lib, 1000).unwrap();
        assert!(
            decls2.is_empty(),
            "already-cached constants should not be re-returned"
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
