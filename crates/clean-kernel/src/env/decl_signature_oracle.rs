// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Oracle API methods are used by migration tests across multiple modules.
// Some methods are not yet called but are part of the designed interface.
//! Declaration signature oracle for #1444 migration gating.
//!
//! Provides pre-insertion equivalence checking for bvar→fvar migration.
//! Instead of detecting regressions post-hoc via full-suite test failures,
//! the oracle captures reference declaration signatures from the existing
//! (bvar-based) environment and compares them against newly-built
//! (EnvDeclBuilder-based) candidates before `add_decl`.
//!
//! ## Design
//!
//! Since clean uses de Bruijn indices, alpha-equivalence is identical to
//! structural equality (`Expr::eq`). The oracle simply:
//!
//! 1. Snapshots declaration types from a reference environment.
//! 2. Compares candidate types from EnvDeclBuilder against the snapshot.
//! 3. Reports mismatches with the declaration name and type diff context.
//!
//! This catches the exact bug class that caused #1444 to stall: off-by-one
//! bvar→fvar translation errors that produce structurally different types.
//!
//! See `designs/2026-02-15-1444-local-maximum-alternative.md`.

use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use std::collections::HashMap;

/// A mismatch between a reference declaration type and a candidate.
#[derive(Debug, Clone)]
pub struct SignatureMismatch {
    /// The declaration name that mismatched.
    pub name: Name,
    /// The reference type from the snapshot.
    pub reference: Expr,
    /// The candidate type from the migration.
    pub candidate: Expr,
}

impl std::fmt::Display for SignatureMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SignatureMismatch {{ name: {}, reference: {:?}, candidate: {:?} }}",
            self.name, self.reference, self.candidate,
        )
    }
}

/// Result of checking a batch of declarations against the oracle.
#[derive(Debug)]
pub struct OracleCheckResult {
    /// Declarations that matched the reference.
    pub matched: Vec<Name>,
    /// Declarations that did not match.
    pub mismatches: Vec<SignatureMismatch>,
    /// Declarations in the candidate set that had no reference entry.
    pub missing_reference: Vec<Name>,
}

impl OracleCheckResult {
    /// Whether all candidates matched (no mismatches, no missing references).
    pub fn passed(&self) -> bool {
        self.mismatches.is_empty() && self.missing_reference.is_empty()
    }

    /// Total number of candidates checked.
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub fn total(&self) -> usize {
        self.matched.len() + self.mismatches.len() + self.missing_reference.len()
    }
}

/// Declaration signature oracle for migration gating.
///
/// Captures reference declaration types from an environment snapshot
/// and provides comparison against candidate declarations built with
/// `EnvDeclBuilder`.
pub struct DeclSignatureOracle {
    /// Map from declaration name to its reference type expression.
    signatures: HashMap<Name, Expr>,
}

impl DeclSignatureOracle {
    /// Create a new empty oracle.
    pub fn new() -> Self {
        Self {
            signatures: HashMap::new(),
        }
    }

    /// Snapshot all declarations from an environment for a given namespace prefix.
    ///
    /// Captures the type of every constant whose name starts with `prefix`.
    /// This builds the reference set that candidates are compared against.
    ///
    /// # Example
    ///
    /// ```text
    /// let mut oracle = DeclSignatureOracle::new();
    /// oracle.snapshot_namespace(&env, "Topology.Manifold");
    /// ```
    pub fn snapshot_namespace(&mut self, env: &Environment, prefix: &str) {
        for info in env.constants() {
            let name_str = info.name.to_string();
            if name_str.starts_with(prefix) {
                self.signatures
                    .insert(info.name.clone(), info.type_.clone());
            }
        }
    }

    /// Snapshot a single declaration by name.
    ///
    /// Returns `true` if the declaration was found and added.
    pub fn snapshot_decl(&mut self, env: &Environment, name: &Name) -> bool {
        if let Some(info) = env.get_const(name) {
            self.signatures.insert(name.clone(), info.type_.clone());
            true
        } else {
            false
        }
    }

    /// Add a reference signature directly (for testing or manual construction).
    pub fn add_reference(&mut self, name: Name, type_: Expr) {
        self.signatures.insert(name, type_);
    }

    /// Check a single candidate declaration type against the oracle.
    ///
    /// Returns `Ok(())` if the candidate matches the reference, or
    /// `Err(SignatureMismatch)` if it differs.
    ///
    /// Returns `Ok(())` if there is no reference entry (caller should
    /// use `has_reference` to distinguish).
    pub fn check_one(
        &self,
        name: &Name,
        candidate_type: &Expr,
    ) -> Result<(), Box<SignatureMismatch>> {
        if let Some(reference) = self.signatures.get(name) {
            if reference == candidate_type {
                Ok(())
            } else {
                Err(Box::new(SignatureMismatch {
                    name: name.clone(),
                    reference: reference.clone(),
                    candidate: candidate_type.clone(),
                }))
            }
        } else {
            Ok(())
        }
    }

    /// Check a batch of candidate declarations against the oracle.
    ///
    /// Each entry is `(name, candidate_type)`. Returns a full result
    /// with matched, mismatched, and missing-reference lists.
    pub fn check_batch(&self, candidates: &[(Name, Expr)]) -> OracleCheckResult {
        let mut matched = Vec::new();
        let mut mismatches = Vec::new();
        let mut missing_reference = Vec::new();

        for (name, candidate_type) in candidates {
            if let Some(reference) = self.signatures.get(name) {
                if reference == candidate_type {
                    matched.push(name.clone());
                } else {
                    mismatches.push(SignatureMismatch {
                        name: name.clone(),
                        reference: reference.clone(),
                        candidate: candidate_type.clone(),
                    });
                }
            } else {
                missing_reference.push(name.clone());
            }
        }

        OracleCheckResult {
            matched,
            mismatches,
            missing_reference,
        }
    }

    /// Whether the oracle has a reference for a given name.
    pub(crate) fn has_reference(&self, name: &Name) -> bool {
        self.signatures.contains_key(name)
    }

    /// Number of reference entries in the oracle.
    pub fn len(&self) -> usize {
        self.signatures.len()
    }

    /// Whether the oracle is empty.
    pub fn is_empty(&self) -> bool {
        self.signatures.is_empty()
    }

    /// Get the reference type for a declaration name, if present.
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub fn get_reference(&self, name: &Name) -> Option<&Expr> {
        self.signatures.get(name)
    }

    /// List all declaration names in the oracle, sorted for deterministic output.
    pub fn names_sorted(&self) -> Vec<Name> {
        let mut names: Vec<Name> = self.signatures.keys().cloned().collect();
        names.sort_by_key(|a| a.to_string());
        names
    }

    /// Validate all declarations in `candidate_env` matching `prefix` against
    /// the oracle's reference signatures.
    ///
    /// This is the migration gate: snapshot a reference environment, then call
    /// this on the candidate (migrated) environment to confirm all declarations
    /// in the namespace are structurally identical.
    ///
    /// Returns `Ok(matched_count)` if all matched, or `Err(OracleCheckResult)`
    /// with the full diff.
    pub fn validate_namespace(
        &self,
        candidate_env: &Environment,
        prefix: &str,
    ) -> Result<usize, OracleCheckResult> {
        let candidates: Vec<(Name, Expr)> = candidate_env
            .constants()
            .filter(|info| info.name.to_string().starts_with(prefix))
            .map(|info| (info.name.clone(), info.type_.clone()))
            .collect();

        let result = self.check_batch(&candidates);
        if result.passed() {
            Ok(result.matched.len())
        } else {
            Err(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::BinderInfo;
    use crate::level::Level;

    /// Build a reference environment with Topology.Manifold declarations initialized.
    ///
    /// This must succeed; partial loads would hide regressions in generated overlay
    /// payload shape and make oracle tests pass trivially.
    fn make_manifold_env() -> Environment {
        let mut env = Environment::new();
        env.init_topology_manifold()
            .expect("init_topology_manifold should succeed for oracle tests");
        assert!(
            env.get_const(&Name::from_string("Topology.Manifold.ExteriorDerivative"))
                .is_some(),
            "Topology.Manifold.ExteriorDerivative should be present in oracle reference env"
        );
        env
    }

    /// Build a reference environment with Topology.LieGroup declarations initialized.
    fn make_lie_group_env() -> Environment {
        let mut env = make_manifold_env();
        env.init_topology_lie_group()
            .expect("init_topology_lie_group should succeed for oracle tests");
        assert!(
            env.get_const(&Name::from_string("Topology.LieGroup.LieAlgebra"))
                .is_some(),
            "Topology.LieGroup.LieAlgebra should be present in oracle reference env"
        );
        env
    }

    #[test]
    fn test_oracle_empty() {
        let oracle = DeclSignatureOracle::new();
        assert!(oracle.is_empty());
        assert_eq!(oracle.len(), 0);
    }

    #[test]
    fn test_oracle_snapshot_namespace() {
        let env = make_manifold_env();
        let mut oracle = DeclSignatureOracle::new();
        oracle.snapshot_namespace(&env, "Topology.Manifold");

        // Should have captured manifold declarations
        assert!(
            !oracle.is_empty(),
            "oracle should have entries after snapshot"
        );
        assert!(oracle.has_reference(&Name::from_string("Topology.Manifold.Chart")));
        assert!(oracle.has_reference(&Name::from_string("Topology.Manifold.SmoothManifold")));
    }

    #[test]
    fn test_oracle_snapshot_single_decl() {
        let env = make_manifold_env();
        let mut oracle = DeclSignatureOracle::new();
        let found = oracle.snapshot_decl(&env, &Name::from_string("Topology.Manifold.Chart"));
        assert!(found);
        assert_eq!(oracle.len(), 1);
    }

    #[test]
    fn test_oracle_check_matching_type() {
        let env = make_manifold_env();
        let mut oracle = DeclSignatureOracle::new();
        oracle.snapshot_namespace(&env, "Topology.Manifold");

        // Get the actual type from the environment
        let chart_name = Name::from_string("Topology.Manifold.Chart");
        let chart_type = env
            .get_const(&chart_name)
            .expect("Chart should exist")
            .type_
            .clone();

        // Check: identical type should pass
        oracle
            .check_one(&chart_name, &chart_type)
            .expect("identical type should pass oracle check");
    }

    #[test]
    fn test_oracle_check_mismatched_type() {
        let env = make_manifold_env();
        let mut oracle = DeclSignatureOracle::new();
        oracle.snapshot_namespace(&env, "Topology.Manifold");

        let chart_name = Name::from_string("Topology.Manifold.Chart");
        // Use a deliberately wrong type
        let wrong_type = Expr::prop();

        let err = oracle
            .check_one(&chart_name, &wrong_type)
            .expect_err("should detect mismatch");
        assert_eq!(err.name, chart_name);
    }

    #[test]
    fn test_oracle_check_missing_reference_is_ok() {
        let oracle = DeclSignatureOracle::new();
        let name = Name::from_string("NonExistent.Decl");
        // No reference entry → Ok (not an error, just unchecked)
        oracle
            .check_one(&name, &Expr::prop())
            .expect("missing reference should not produce an error");
        assert!(!oracle.has_reference(&name));
    }

    #[test]
    fn test_oracle_batch_check() {
        let env = make_manifold_env();
        let mut oracle = DeclSignatureOracle::new();
        oracle.snapshot_namespace(&env, "Topology.Manifold");

        let chart_name = Name::from_string("Topology.Manifold.Chart");
        let chart_type = env
            .get_const(&chart_name)
            .expect("Chart should exist")
            .type_
            .clone();

        let atlas_name = Name::from_string("Topology.Manifold.Atlas");
        let wrong_atlas_type = Expr::prop();

        let nonexistent = Name::from_string("Topology.Manifold.Nonexistent");

        let candidates = vec![
            (chart_name.clone(), chart_type),       // matches
            (atlas_name.clone(), wrong_atlas_type), // mismatch
            (nonexistent.clone(), Expr::prop()),    // missing reference
        ];

        let result = oracle.check_batch(&candidates);
        assert_eq!(result.matched.len(), 1);
        assert_eq!(result.matched[0], chart_name);
        assert_eq!(result.mismatches.len(), 1);
        assert_eq!(result.mismatches[0].name, atlas_name);
        assert_eq!(result.missing_reference.len(), 1);
        assert_eq!(result.missing_reference[0], nonexistent);
        assert!(!result.passed());
    }

    #[test]
    fn test_oracle_add_reference_directly() {
        let mut oracle = DeclSignatureOracle::new();
        let name = Name::from_string("Test.Decl");
        let ty = Expr::prop();
        oracle.add_reference(name.clone(), ty.clone());

        assert!(oracle.has_reference(&name));
        oracle
            .check_one(&name, &ty)
            .expect("directly added reference should match");
    }

    #[test]
    fn test_oracle_names_sorted() {
        let mut oracle = DeclSignatureOracle::new();
        oracle.add_reference(Name::from_string("Z.decl"), Expr::prop());
        oracle.add_reference(Name::from_string("A.decl"), Expr::prop());
        oracle.add_reference(Name::from_string("M.decl"), Expr::prop());

        let names = oracle.names_sorted();
        let name_strs: Vec<String> = names.iter().map(|n| n.to_string()).collect();
        assert_eq!(name_strs, vec!["A.decl", "M.decl", "Z.decl"]);
    }

    /// End-to-end test: snapshot manifold declarations, then "re-derive" them
    /// from the same environment and verify they all match.
    ///
    /// This is the baseline for the oracle: if we snapshot and immediately check
    /// against the same environment, everything should pass.
    #[test]
    fn test_oracle_manifold_self_consistency() {
        let env = make_manifold_env();
        let mut oracle = DeclSignatureOracle::new();
        oracle.snapshot_namespace(&env, "Topology.Manifold");

        // Collect all Topology.Manifold declarations as candidates
        let candidates: Vec<(Name, Expr)> = env
            .constants()
            .filter(|info| info.name.to_string().starts_with("Topology.Manifold"))
            .map(|info| (info.name.clone(), info.type_.clone()))
            .collect();

        assert!(
            !candidates.is_empty(),
            "should have manifold declarations to check"
        );

        let result = oracle.check_batch(&candidates);
        assert!(
            result.passed(),
            "self-consistency check failed: {} mismatches, {} missing references. \
             Mismatches: {:?}",
            result.mismatches.len(),
            result.missing_reference.len(),
            result
                .mismatches
                .iter()
                .map(|m| m.name.to_string())
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            result.matched.len(),
            candidates.len(),
            "all candidates should match in self-consistency check"
        );
    }

    /// Verify that the oracle detects when an EnvDeclBuilder-produced type
    /// is structurally different from the bvar-based reference.
    ///
    /// This simulates the exact #1444 failure mode: a builder migration that
    /// produces a different type expression due to an error.
    #[test]
    fn test_oracle_detects_builder_migration_error() {
        use crate::env::decl_builder::EnvDeclBuilder;

        let env = make_manifold_env();
        let mut oracle = DeclSignatureOracle::new();
        oracle.snapshot_namespace(&env, "Topology.Manifold");

        // Simulate a BAD migration of Topology.Manifold.Chart:
        // Reference: {M : Type u} → [TopologicalSpace M] → Type u
        // Bad candidate: {M : Type u} → Type u  (missing TopologicalSpace instance)
        let u = Name::from_string("u");
        let u_level = Level::param(u);
        let type_u = Expr::sort(u_level);

        let bad_chart_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(type_u.clone());
            // Deliberately skip the TopologicalSpace instance binder
            let result = b.mk_pi(m_id, BinderInfo::Implicit, type_u.clone(), type_u.clone());
            b.finish(result)
        };

        let chart_name = Name::from_string("Topology.Manifold.Chart");
        let err = oracle
            .check_one(&chart_name, &bad_chart_type)
            .expect_err("oracle should detect the missing instance binder");
        assert_eq!(err.name, chart_name);
    }

    /// LieGroup self-consistency: snapshot + immediate check = pass.
    ///
    /// Extends oracle coverage beyond Topology.Manifold to the second-largest
    /// topology namespace (20 declarations).
    #[test]
    fn test_oracle_lie_group_self_consistency() {
        let env = make_lie_group_env();

        let mut oracle = DeclSignatureOracle::new();
        oracle.snapshot_namespace(&env, "Topology.LieGroup");

        let candidates: Vec<(Name, Expr)> = env
            .constants()
            .filter(|info| info.name.to_string().starts_with("Topology.LieGroup"))
            .map(|info| (info.name.clone(), info.type_.clone()))
            .collect();

        assert!(
            !candidates.is_empty(),
            "should have LieGroup declarations to check"
        );

        let result = oracle.check_batch(&candidates);
        assert!(
            result.passed(),
            "LieGroup self-consistency failed: {} mismatches. {:?}",
            result.mismatches.len(),
            result
                .mismatches
                .iter()
                .map(|m| m.name.to_string())
                .collect::<Vec<_>>(),
        );
    }

    /// Cross-environment migration validation: build two independent environments
    /// and confirm the oracle proves they produce identical declarations.
    ///
    /// This is the core migration gate test: if two independent calls to
    /// `init_topology_manifold()` produce the same declaration types, the oracle
    /// passes. This ensures that idempotent re-initialization matches the reference.
    #[test]
    fn test_oracle_cross_env_manifold_migration() {
        // Reference environment
        let ref_env = make_manifold_env();
        let mut oracle = DeclSignatureOracle::new();
        oracle.snapshot_namespace(&ref_env, "Topology.Manifold");

        // Candidate environment (built independently)
        let candidate_env = make_manifold_env();

        // validate_namespace should pass: both environments produce identical types
        let matched = oracle
            .validate_namespace(&candidate_env, "Topology.Manifold")
            .expect("cross-env manifold validation should pass");
        assert!(
            matched > 0,
            "should have validated at least one declaration"
        );
    }

    /// Cross-environment migration validation for LieGroup namespace.
    #[test]
    fn test_oracle_cross_env_lie_group_migration() {
        let ref_env = make_lie_group_env();

        let mut oracle = DeclSignatureOracle::new();
        oracle.snapshot_namespace(&ref_env, "Topology.LieGroup");

        let candidate_env = make_lie_group_env();

        let matched = oracle
            .validate_namespace(&candidate_env, "Topology.LieGroup")
            .expect("cross-env LieGroup validation should pass");
        assert!(
            matched > 0,
            "should have validated at least one LieGroup declaration"
        );
    }

    /// Targeted validation of the LieAlgebra/LieBracket/ExpMap migration cluster.
    ///
    /// These 3 declarations were migrated from raw Expr::bvar to EnvDeclBuilder
    /// as the first oracle-gated declaration cluster for #1444.
    /// This test validates:
    /// 1. All 3 declarations exist after init
    /// 2. Cross-env oracle check passes (idempotent init produces identical types)
    /// 3. Pi-depth structure matches expected binder counts
    #[test]
    fn test_oracle_lie_group_cluster_migration_gate() {
        let cluster_names = [
            "Topology.LieGroup.LieAlgebra",
            "Topology.LieGroup.LieBracket",
            "Topology.LieGroup.ExpMap",
        ];

        // Build reference environment
        let ref_env = make_lie_group_env();

        // Snapshot only the cluster declarations
        let mut oracle = DeclSignatureOracle::new();
        for name_str in &cluster_names {
            let name = Name::from_string(name_str);
            assert!(
                oracle.snapshot_decl(&ref_env, &name),
                "reference should contain {}",
                name_str,
            );
        }
        assert_eq!(oracle.len(), 3);

        // Build candidate environment independently
        let candidate_env = make_lie_group_env();

        // Oracle gate: all 3 must match
        let candidates: Vec<(Name, Expr)> = cluster_names
            .iter()
            .map(|name_str| {
                let name = Name::from_string(name_str);
                let info = candidate_env
                    .get_const(&name)
                    .unwrap_or_else(|| panic!("candidate should contain {}", name_str));
                (name, info.type_.clone())
            })
            .collect();

        let result = oracle.check_batch(&candidates);
        assert!(
            result.passed(),
            "LieGroup cluster oracle gate failed: {} mismatches. {:?}",
            result.mismatches.len(),
            result
                .mismatches
                .iter()
                .map(|m| format!(
                    "{}: ref={:?} vs cand={:?}",
                    m.name, m.reference, m.candidate
                ))
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            result.matched.len(),
            3,
            "all 3 cluster members should match"
        );

        // Structural validation: check Pi-depth for each declaration
        use crate::expr::ExprKind;
        fn pi_depth(e: &Expr) -> usize {
            match &e.kind {
                ExprKind::Pi(_, _, body) => 1 + pi_depth(body),
                _ => 0,
            }
        }

        let la = candidate_env
            .get_const(&Name::from_string("Topology.LieGroup.LieAlgebra"))
            .unwrap();
        // {G} → [TS G] → [Group G] → {n} → [LieGroup G n] → Type u = 5 Pi
        assert_eq!(
            pi_depth(&la.type_),
            5,
            "LieAlgebra should have 5 Pi binders"
        );

        let lb = candidate_env
            .get_const(&Name::from_string("Topology.LieGroup.LieBracket"))
            .unwrap();
        // {G} → [TS G] → [Group G] → {n} → [lg] → LA → LA → LA = 7 Pi
        assert_eq!(
            pi_depth(&lb.type_),
            7,
            "LieBracket should have 7 Pi binders"
        );

        let em = candidate_env
            .get_const(&Name::from_string("Topology.LieGroup.ExpMap"))
            .unwrap();
        // {G} → [TS G] → [Group G] → {n} → [lg] → LA → G = 6 Pi
        assert_eq!(pi_depth(&em.type_), 6, "ExpMap should have 6 Pi binders");
    }

    /// Verify that validate_namespace returns Err with details when a declaration
    /// type is corrupted in the candidate environment.
    #[test]
    fn test_oracle_validate_namespace_detects_corruption() {
        let ref_env = make_manifold_env();
        let mut oracle = DeclSignatureOracle::new();
        oracle.snapshot_namespace(&ref_env, "Topology.Manifold");

        // Corrupt the oracle by replacing one reference with a wrong type
        // to simulate what happens when a migration produces a different type.
        let chart_name = Name::from_string("Topology.Manifold.Chart");
        oracle.add_reference(chart_name.clone(), Expr::prop());

        // Now validate against a correct environment — the corrupted reference
        // should cause a mismatch.
        let candidate_env = make_manifold_env();
        let err = oracle
            .validate_namespace(&candidate_env, "Topology.Manifold")
            .expect_err("should detect corrupted reference");

        assert_eq!(err.mismatches.len(), 1);
        assert_eq!(err.mismatches[0].name, chart_name);
    }
}
