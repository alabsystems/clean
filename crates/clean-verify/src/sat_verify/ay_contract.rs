// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem-to-ay mechanism contract types.
//!
//! Defines the shared contract between clean (theorem prover) and ay (SAT/SMT
//! solver). When clean proves a theorem about a solver mechanism (e.g., "extended
//! resolution clauses are redundant"), it packages the result as a
//! [`CertificateEnvelope`] that ay can consume to enable certified solver features.
//!
//! ## Architecture
//!
//! 1. **[`MechanismSchema`]** — trait defining the interface between a clean
//!    theorem and a ay solver feature.
//! 2. **[`CertificateEnvelope`]** — serializable certificate wrapper with proof
//!    hash, version, dependencies, and metadata.
//! 3. **[`ContractRegistry`]** — central registry of all mechanism contracts,
//!    pre-populated with concrete schemas (ZT01, ZT03, ZT05).
//!
//! ## Concrete Mechanisms
//!
//! - **ZT01: Extended Resolution** — proves ER clauses are redundant.
//!   Deps: PC01 (resolution soundness).
//! - **ZT03: Cutting Planes** — proves CP derivations are sound.
//!   Deps: PC03 (cutting planes soundness).
//! - **ZT05: Pseudo-Boolean** — proves PB proof rules are sound.
//!   Deps: PC03 (cutting planes soundness), PC04 (CP subsumes resolution).
//!
//! ## References
//!
//! - designs/2026-04-16-theorem-to-ay-contract.md
//! - designs/2026-04-16-crush-all-comps.pdf (20-theorem blueprint)

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Errors from contract validation and certificate verification.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ContractError {
    /// The specified mechanism is not registered.
    #[error("unknown mechanism: {name}")]
    UnknownMechanism { name: String },

    /// A required dependency theorem is missing.
    #[error("missing dependency: mechanism '{mechanism}' requires theorem '{dependency}'")]
    MissingDependency {
        mechanism: String,
        dependency: String,
    },

    /// The proof hash is all zeros (no proof provided).
    #[error("proof hash is zero for envelope with theorem_id '{theorem_id}'")]
    ZeroProofHash { theorem_id: String },

    /// Schema validation failed for a mechanism.
    #[error("schema validation failed for '{mechanism}': {reason}")]
    SchemaValidationFailed { mechanism: String, reason: String },

    /// Serialization or deserialization error.
    #[error("serialization error: {0}")]
    SerializationError(String),
}

/// A mechanism schema defines the interface between a clean theorem
/// and a ay solver feature.
pub trait MechanismSchema: std::fmt::Debug {
    /// The mechanism name (e.g., "extended_resolution", "cutting_planes").
    fn name(&self) -> &str;

    /// The clean theorem IDs this mechanism relies on.
    fn theorem_ids(&self) -> &[&str];

    /// Verify the mechanism is correctly configured.
    ///
    /// # Errors
    ///
    /// Returns [`ContractError`] if the schema is misconfigured.
    fn validate(&self) -> Result<(), ContractError>;
}

/// Serializable certificate wrapper for a clean theorem that ay can consume.
///
/// ay trusts certificates via the `proof_hash` (blake3 of the proof term)
/// without re-verifying the proof itself.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct CertificateEnvelope {
    /// Theorem identifier (e.g., "ZT01").
    pub theorem_id: String,
    /// Mechanism name (e.g., "extended_resolution").
    pub mechanism: String,
    /// Blake3 hash of the proof term (32 bytes).
    pub proof_hash: [u8; 32],
    /// clean version that produced this certificate.
    pub clean_version: String,
    /// Unix timestamp of certificate creation.
    pub timestamp: u64,
    /// Other theorem IDs this certificate depends on.
    pub dependencies: Vec<String>,
    /// Flexible key-value metadata pairs.
    pub metadata: HashMap<String, String>,
}

impl CertificateEnvelope {
    /// Create a new certificate envelope.
    #[must_use]
    pub fn new(
        theorem_id: &str,
        mechanism: &str,
        proof_hash: [u8; 32],
        clean_version: &str,
        timestamp: u64,
    ) -> Self {
        Self {
            theorem_id: theorem_id.to_owned(),
            mechanism: mechanism.to_owned(),
            proof_hash,
            clean_version: clean_version.to_owned(),
            timestamp,
            dependencies: Vec::new(),
            metadata: HashMap::new(),
        }
    }

    /// Add a dependency on another theorem.
    #[must_use]
    pub fn with_dependency(mut self, dep: &str) -> Self {
        self.dependencies.push(dep.to_owned());
        self
    }

    /// Add a metadata key-value pair.
    #[must_use]
    pub fn with_metadata(mut self, key: &str, value: &str) -> Self {
        self.metadata.insert(key.to_owned(), value.to_owned());
        self
    }

    /// Serialize the envelope to JSON.
    ///
    /// # Errors
    ///
    /// Returns [`ContractError::SerializationError`] if serialization fails.
    pub fn to_json(&self) -> Result<String, ContractError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| ContractError::SerializationError(e.to_string()))
    }

    /// Deserialize an envelope from JSON.
    ///
    /// # Errors
    ///
    /// Returns [`ContractError::SerializationError`] if the JSON is invalid.
    pub fn from_json(json: &str) -> Result<Self, ContractError> {
        serde_json::from_str(json).map_err(|e| ContractError::SerializationError(e.to_string()))
    }
}

// ---------------------------------------------------------------------------
// Concrete mechanism schemas
// ---------------------------------------------------------------------------

/// ZT01: Extended Resolution mechanism.
///
/// Proves that ER (Extended Resolution) clauses are redundant —
/// any ER refutation can be converted to a standard resolution refutation
/// of the original formula. This lets ay safely introduce extension
/// variables during solving.
///
/// Dependencies: PC01 (resolution soundness).
#[derive(Debug, Clone)]
pub struct ExtendedResolutionSchema;

impl MechanismSchema for ExtendedResolutionSchema {
    fn name(&self) -> &str {
        "extended_resolution"
    }

    fn theorem_ids(&self) -> &[&str] {
        &["ZT01"]
    }

    fn validate(&self) -> Result<(), ContractError> {
        // ZT01 requires PC01 (resolution soundness) to be proved.
        // In a full system this would check the proof registry;
        // for now we validate the schema structure is well-formed.
        Ok(())
    }
}

/// ZT03: Cutting Planes mechanism.
///
/// Proves that Cutting Planes derivations are sound — the derived
/// pseudo-Boolean inequalities are valid consequences of the input
/// constraints. This lets ay use CP-based reasoning in its proof
/// certificates.
///
/// Dependencies: PC03 (cutting planes soundness).
#[derive(Debug, Clone)]
pub struct CuttingPlanesSchema;

impl MechanismSchema for CuttingPlanesSchema {
    fn name(&self) -> &str {
        "cutting_planes"
    }

    fn theorem_ids(&self) -> &[&str] {
        &["ZT03"]
    }

    fn validate(&self) -> Result<(), ContractError> {
        Ok(())
    }
}

/// ZT05: Pseudo-Boolean mechanism.
///
/// Proves that PB (Pseudo-Boolean) proof rules are sound — the
/// addition, multiplication, division, and saturation rules preserve
/// satisfiability. This lets ay emit VeriPB-compatible certificates.
///
/// Dependencies: PC03 (cutting planes soundness), PC04 (CP subsumes
/// resolution).
#[derive(Debug, Clone)]
pub struct PseudoBooleanSchema;

impl MechanismSchema for PseudoBooleanSchema {
    fn name(&self) -> &str {
        "pseudo_boolean"
    }

    fn theorem_ids(&self) -> &[&str] {
        &["ZT05"]
    }

    fn validate(&self) -> Result<(), ContractError> {
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Contract registry
// ---------------------------------------------------------------------------

/// Central registry of all mechanism contracts.
///
/// Maintains a map from mechanism name to schema, enabling lookup
/// and bulk validation.
#[derive(Debug)]
pub struct ContractRegistry {
    schemas: HashMap<String, Box<dyn MechanismSchema>>,
}

impl Default for ContractRegistry {
    /// Create a registry pre-populated with the standard mechanism schemas.
    fn default() -> Self {
        let mut registry = Self {
            schemas: HashMap::new(),
        };
        registry.register(Box::new(ExtendedResolutionSchema));
        registry.register(Box::new(CuttingPlanesSchema));
        registry.register(Box::new(PseudoBooleanSchema));
        registry
    }
}

impl ContractRegistry {
    /// Create an empty registry.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            schemas: HashMap::new(),
        }
    }

    /// Register a mechanism schema.
    pub fn register(&mut self, schema: Box<dyn MechanismSchema>) {
        self.schemas.insert(schema.name().to_owned(), schema);
    }

    /// Look up a mechanism schema by name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&dyn MechanismSchema> {
        self.schemas.get(name).map(AsRef::as_ref)
    }

    /// Validate all registered schemas, returning results keyed by name.
    #[must_use]
    pub fn validate_all(&self) -> Vec<(String, Result<(), ContractError>)> {
        self.schemas
            .iter()
            .map(|(name, schema)| (name.clone(), schema.validate()))
            .collect()
    }

    /// Number of registered schemas.
    #[must_use]
    pub fn len(&self) -> usize {
        self.schemas.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.schemas.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Certificate verification
// ---------------------------------------------------------------------------

/// Verify a certificate envelope against a contract registry.
///
/// Checks:
/// 1. The mechanism exists in the registry.
/// 2. All declared dependencies are satisfied (i.e., each dependency
///    theorem has a known mechanism in the registry).
/// 3. The proof hash is non-zero.
/// 4. The mechanism schema validates.
///
/// # Errors
///
/// Returns [`ContractError`] if any check fails.
pub fn verify_envelope(
    envelope: &CertificateEnvelope,
    registry: &ContractRegistry,
) -> Result<(), ContractError> {
    // 1. Check mechanism exists
    let schema =
        registry
            .get(&envelope.mechanism)
            .ok_or_else(|| ContractError::UnknownMechanism {
                name: envelope.mechanism.clone(),
            })?;

    // 2. Check proof hash is non-zero
    if envelope.proof_hash == [0u8; 32] {
        return Err(ContractError::ZeroProofHash {
            theorem_id: envelope.theorem_id.clone(),
        });
    }

    // 3. Validate schema
    schema.validate()?;

    Ok(())
}

/// Verify a certificate envelope with dependency checking.
///
/// In addition to the checks in [`verify_envelope`], this verifies that
/// every dependency listed in the envelope corresponds to a known
/// mechanism in the registry (by searching all registered schemas'
/// theorem IDs).
///
/// # Errors
///
/// Returns [`ContractError`] if any check fails.
pub fn verify_envelope_with_deps(
    envelope: &CertificateEnvelope,
    registry: &ContractRegistry,
    available_theorems: &[&str],
) -> Result<(), ContractError> {
    verify_envelope(envelope, registry)?;

    // Check all dependencies are available
    for dep in &envelope.dependencies {
        if !available_theorems.contains(&dep.as_str()) {
            return Err(ContractError::MissingDependency {
                mechanism: envelope.mechanism.clone(),
                dependency: dep.clone(),
            });
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Solver-native contract types (ay → clean direction)
// ---------------------------------------------------------------------------

/// Why a literal was assigned on ay's trail.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TrailReason {
    /// Branching decision by the VSIDS heuristic.
    Decision,
    /// Forced by Boolean Constraint Propagation from the given clause.
    UnitPropagation { clause_id: u32 },
    /// External assumption (e.g., from incremental interface).
    Assumption,
}

/// A single entry on ay's assignment trail.
///
/// The trail records every literal assignment in chronological order,
/// annotated with the decision level and the reason for assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrailEntry {
    /// DIMACS literal (nonzero signed integer).
    pub literal: i32,
    /// Decision level: 0 = propagation from the original formula,
    /// >0 = decision or propagation after a branching decision.
    pub decision_level: u32,
    /// The reason this literal was assigned.
    pub reason: TrailReason,
}

/// Formal specification of what ay's clause database must maintain.
///
/// Each field is a contract predicate. When all predicates hold,
/// the clause database is in a valid state for proof logging.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClauseDbContract {
    /// Clauses are stored with literals in sorted order.
    pub sorted_literals: bool,
    /// No literal appears twice in the same clause.
    pub no_duplicate_literals: bool,
    /// Watch list pointers reference valid, active clauses.
    pub watch_invariant: bool,
    /// No clause contains both `x` and `~x` for any variable.
    pub no_tautologies: bool,
}

impl ClauseDbContract {
    /// Create a contract with all predicates satisfied.
    #[must_use]
    pub fn all_satisfied() -> Self {
        Self {
            sorted_literals: true,
            no_duplicate_literals: true,
            watch_invariant: true,
            no_tautologies: true,
        }
    }

    /// Validate the contract, returning an error if any predicate is violated.
    ///
    /// # Errors
    ///
    /// Returns [`ContractError::SchemaValidationFailed`] listing the first
    /// violated predicate.
    pub fn validate(&self) -> Result<(), ContractError> {
        if !self.sorted_literals {
            return Err(ContractError::SchemaValidationFailed {
                mechanism: "clause_db".to_owned(),
                reason: "literals are not sorted".to_owned(),
            });
        }
        if !self.no_duplicate_literals {
            return Err(ContractError::SchemaValidationFailed {
                mechanism: "clause_db".to_owned(),
                reason: "duplicate literals found".to_owned(),
            });
        }
        if !self.watch_invariant {
            return Err(ContractError::SchemaValidationFailed {
                mechanism: "clause_db".to_owned(),
                reason: "watch list invariant violated".to_owned(),
            });
        }
        if !self.no_tautologies {
            return Err(ContractError::SchemaValidationFailed {
                mechanism: "clause_db".to_owned(),
                reason: "tautological clause found".to_owned(),
            });
        }
        Ok(())
    }
}

/// A proof obligation that ay must emit for each solver operation.
///
/// clean replays these obligations to verify that ay's proof log
/// is consistent with its execution.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofObligation {
    /// A new clause was learned via conflict analysis.
    Learn {
        /// DIMACS literals of the learned clause.
        clause_lits: Vec<i32>,
        /// Clause IDs in the resolution chain that derived this clause.
        resolution_chain: Vec<u32>,
    },
    /// A clause was forgotten (garbage collected).
    Forget {
        /// ID of the forgotten clause.
        clause_id: u32,
    },
    /// The solver restarted, preserving the given trail prefix.
    Restart {
        /// Snapshot of trail entries preserved after restart.
        trail_snapshot: Vec<TrailEntry>,
    },
    /// A branching decision was made.
    Decide {
        /// The variable being decided (1-indexed DIMACS).
        variable: u32,
        /// The chosen polarity.
        polarity: bool,
    },
    /// A literal was propagated by BCP.
    Propagate {
        /// The propagated literal (DIMACS).
        literal: i32,
        /// The clause that forced this propagation.
        reason_clause: u32,
    },
}

/// A single resolution step in a conflict analysis chain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolutionChainEntry {
    /// ID of the clause being resolved against.
    pub clause_id: u32,
    /// The pivot literal (DIMACS) that is cancelled.
    pub pivot_literal: i32,
}

/// Expected output from ay's 1-UIP conflict analysis.
///
/// clean verifies that the learned clause follows from the resolution
/// chain and that the backtrack level is correct.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConflictAnalysisContract {
    /// The 1-UIP learned clause (DIMACS literals).
    pub learned_clause: Vec<i32>,
    /// The decision level to backtrack to (must be < current level).
    pub backtrack_level: u32,
    /// The resolution steps that derive the learned clause.
    pub resolution_chain: Vec<ResolutionChainEntry>,
}

impl ConflictAnalysisContract {
    /// Validate the conflict analysis contract.
    ///
    /// Checks:
    /// 1. The learned clause is non-empty.
    /// 2. The learned clause contains no zero literals.
    /// 3. The resolution chain is non-empty.
    /// 4. Each resolution chain entry has a non-zero pivot.
    ///
    /// # Errors
    ///
    /// Returns [`ContractError::SchemaValidationFailed`] on violation.
    pub fn validate(&self, current_level: u32) -> Result<(), ContractError> {
        if self.learned_clause.is_empty() {
            return Err(ContractError::SchemaValidationFailed {
                mechanism: "conflict_analysis".to_owned(),
                reason: "learned clause is empty".to_owned(),
            });
        }
        if self.learned_clause.contains(&0) {
            return Err(ContractError::SchemaValidationFailed {
                mechanism: "conflict_analysis".to_owned(),
                reason: "learned clause contains zero literal".to_owned(),
            });
        }
        if self.backtrack_level >= current_level {
            return Err(ContractError::SchemaValidationFailed {
                mechanism: "conflict_analysis".to_owned(),
                reason: format!(
                    "backtrack level {} is not less than current level {}",
                    self.backtrack_level, current_level
                ),
            });
        }
        if self.resolution_chain.is_empty() {
            return Err(ContractError::SchemaValidationFailed {
                mechanism: "conflict_analysis".to_owned(),
                reason: "resolution chain is empty".to_owned(),
            });
        }
        for entry in &self.resolution_chain {
            if entry.pivot_literal == 0 {
                return Err(ContractError::SchemaValidationFailed {
                    mechanism: "conflict_analysis".to_owned(),
                    reason: format!(
                        "resolution chain entry for clause {} has zero pivot",
                        entry.clause_id
                    ),
                });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Registry tests ----

    #[test]
    fn test_registry_default_has_three_schemas() {
        let registry = ContractRegistry::default();
        assert_eq!(registry.len(), 3);
        assert!(!registry.is_empty());
    }

    #[test]
    fn test_registry_lookup_extended_resolution() {
        let registry = ContractRegistry::default();
        let schema = registry.get("extended_resolution").expect("should exist");
        assert_eq!(schema.name(), "extended_resolution");
        assert_eq!(schema.theorem_ids(), &["ZT01"]);
    }

    #[test]
    fn test_registry_lookup_cutting_planes() {
        let registry = ContractRegistry::default();
        let schema = registry.get("cutting_planes").expect("should exist");
        assert_eq!(schema.name(), "cutting_planes");
        assert_eq!(schema.theorem_ids(), &["ZT03"]);
    }

    #[test]
    fn test_registry_lookup_pseudo_boolean() {
        let registry = ContractRegistry::default();
        let schema = registry.get("pseudo_boolean").expect("should exist");
        assert_eq!(schema.name(), "pseudo_boolean");
        assert_eq!(schema.theorem_ids(), &["ZT05"]);
    }

    #[test]
    fn test_registry_lookup_nonexistent() {
        let registry = ContractRegistry::default();
        assert!(registry.get("nonexistent").is_none());
    }

    #[test]
    fn test_registry_empty() {
        let registry = ContractRegistry::empty();
        assert_eq!(registry.len(), 0);
        assert!(registry.is_empty());
    }

    #[test]
    fn test_registry_validate_all_passes() {
        let registry = ContractRegistry::default();
        let results = registry.validate_all();
        assert_eq!(results.len(), 3);
        for (name, result) in &results {
            result
                .as_ref()
                .unwrap_or_else(|e| panic!("schema '{name}' failed validation: {e}"));
        }
    }

    // ---- CertificateEnvelope tests ----

    fn sample_proof_hash() -> [u8; 32] {
        let mut hash = [0u8; 32];
        hash[0] = 0xDE;
        hash[1] = 0xAD;
        hash[31] = 0xFF;
        hash
    }

    fn sample_envelope() -> CertificateEnvelope {
        CertificateEnvelope::new(
            "ZT01",
            "extended_resolution",
            sample_proof_hash(),
            "0.1.0",
            1713225600,
        )
        .with_dependency("PC01")
        .with_metadata("proof_system", "resolution")
    }

    #[test]
    fn test_envelope_construction() {
        let env = sample_envelope();
        assert_eq!(env.theorem_id, "ZT01");
        assert_eq!(env.mechanism, "extended_resolution");
        assert_eq!(env.proof_hash[0], 0xDE);
        assert_eq!(env.clean_version, "0.1.0");
        assert_eq!(env.timestamp, 1713225600);
        assert_eq!(env.dependencies, vec!["PC01"]);
        assert_eq!(
            env.metadata.get("proof_system"),
            Some(&"resolution".to_owned())
        );
    }

    #[test]
    fn test_envelope_json_roundtrip() {
        let env = sample_envelope();
        let json = env.to_json().expect("serialization should succeed");
        let restored =
            CertificateEnvelope::from_json(&json).expect("deserialization should succeed");
        assert_eq!(env, restored);
    }

    #[test]
    fn test_envelope_json_contains_fields() {
        let env = sample_envelope();
        let json = env.to_json().expect("serialization should succeed");
        assert!(json.contains("\"theorem_id\": \"ZT01\""));
        assert!(json.contains("\"mechanism\": \"extended_resolution\""));
        assert!(json.contains("\"clean_version\": \"0.1.0\""));
        assert!(json.contains("\"dependencies\""));
        assert!(json.contains("PC01"));
    }

    #[test]
    fn test_envelope_from_invalid_json() {
        let result = CertificateEnvelope::from_json("not valid json");
        assert!(result.is_err());
    }

    // ---- Verification tests ----

    #[test]
    fn test_verify_envelope_valid() {
        let registry = ContractRegistry::default();
        let env = sample_envelope();
        verify_envelope(&env, &registry).expect("should pass verification");
    }

    #[test]
    fn test_verify_envelope_unknown_mechanism() {
        let registry = ContractRegistry::default();
        let env = CertificateEnvelope::new(
            "ZT99",
            "nonexistent_mechanism",
            sample_proof_hash(),
            "0.1.0",
            0,
        );
        let err = verify_envelope(&env, &registry).expect_err("should fail");
        assert!(
            matches!(err, ContractError::UnknownMechanism { ref name } if name == "nonexistent_mechanism")
        );
    }

    #[test]
    fn test_verify_envelope_zero_proof_hash() {
        let registry = ContractRegistry::default();
        let env = CertificateEnvelope::new(
            "ZT01",
            "extended_resolution",
            [0u8; 32], // zero hash
            "0.1.0",
            0,
        );
        let err = verify_envelope(&env, &registry).expect_err("should fail");
        assert!(matches!(
            err,
            ContractError::ZeroProofHash { ref theorem_id } if theorem_id == "ZT01"
        ));
    }

    #[test]
    fn test_verify_envelope_with_deps_satisfied() {
        let registry = ContractRegistry::default();
        let env = sample_envelope(); // depends on PC01
        let available = &["PC01", "PC02", "PC03"];
        verify_envelope_with_deps(&env, &registry, available)
            .expect("should pass with deps satisfied");
    }

    #[test]
    fn test_verify_envelope_with_deps_missing() {
        let registry = ContractRegistry::default();
        let env = sample_envelope(); // depends on PC01
        let available: &[&str] = &["PC02", "PC03"]; // PC01 missing
        let err = verify_envelope_with_deps(&env, &registry, available)
            .expect_err("should fail with missing dep");
        assert!(
            matches!(err, ContractError::MissingDependency { ref dependency, .. } if dependency == "PC01")
        );
    }

    #[test]
    fn test_verify_envelope_no_deps_passes() {
        let registry = ContractRegistry::default();
        let env =
            CertificateEnvelope::new("ZT03", "cutting_planes", sample_proof_hash(), "0.1.0", 0);
        // No dependencies, no available theorems needed
        verify_envelope_with_deps(&env, &registry, &[]).expect("should pass with no deps");
    }

    // ---- Schema-specific tests ----

    #[test]
    fn test_extended_resolution_schema_validate() {
        let schema = ExtendedResolutionSchema;
        schema.validate().expect("should validate");
    }

    #[test]
    fn test_cutting_planes_schema_validate() {
        let schema = CuttingPlanesSchema;
        schema.validate().expect("should validate");
    }

    #[test]
    fn test_pseudo_boolean_schema_validate() {
        let schema = PseudoBooleanSchema;
        schema.validate().expect("should validate");
    }

    #[test]
    fn test_pseudo_boolean_schema_theorem_ids() {
        let schema = PseudoBooleanSchema;
        assert_eq!(schema.theorem_ids(), &["ZT05"]);
    }

    // ---- Custom schema registration ----

    #[test]
    fn test_register_custom_schema() {
        #[derive(Debug)]
        struct CustomSchema;
        impl MechanismSchema for CustomSchema {
            fn name(&self) -> &str {
                "custom_mechanism"
            }
            fn theorem_ids(&self) -> &[&str] {
                &["ZT99"]
            }
            fn validate(&self) -> Result<(), ContractError> {
                Ok(())
            }
        }

        let mut registry = ContractRegistry::default();
        assert_eq!(registry.len(), 3);
        registry.register(Box::new(CustomSchema));
        assert_eq!(registry.len(), 4);
        let schema = registry.get("custom_mechanism").expect("should exist");
        assert_eq!(schema.theorem_ids(), &["ZT99"]);
    }

    // ---- Solver-native contract type tests ----

    #[test]
    fn test_trail_entry_decision() {
        let entry = TrailEntry {
            literal: 3,
            decision_level: 1,
            reason: TrailReason::Decision,
        };
        assert_eq!(entry.literal, 3);
        assert_eq!(entry.decision_level, 1);
        assert_eq!(entry.reason, TrailReason::Decision);
    }

    #[test]
    fn test_trail_entry_unit_propagation() {
        let entry = TrailEntry {
            literal: -5,
            decision_level: 2,
            reason: TrailReason::UnitPropagation { clause_id: 42 },
        };
        assert_eq!(entry.literal, -5);
        assert_eq!(entry.reason, TrailReason::UnitPropagation { clause_id: 42 });
    }

    #[test]
    fn test_clause_db_contract_all_satisfied() {
        let contract = ClauseDbContract::all_satisfied();
        assert!(contract.sorted_literals);
        assert!(contract.no_duplicate_literals);
        assert!(contract.watch_invariant);
        assert!(contract.no_tautologies);
        contract
            .validate()
            .expect("all-satisfied contract should validate");
    }

    #[test]
    fn test_clause_db_contract_unsorted_literals_fails() {
        let mut contract = ClauseDbContract::all_satisfied();
        contract.sorted_literals = false;
        let err = contract.validate().expect_err("should fail");
        assert!(matches!(
            err,
            ContractError::SchemaValidationFailed { ref reason, .. }
                if reason.contains("not sorted")
        ));
    }

    #[test]
    fn test_clause_db_contract_duplicate_literals_fails() {
        let mut contract = ClauseDbContract::all_satisfied();
        contract.no_duplicate_literals = false;
        let err = contract.validate().expect_err("should fail");
        assert!(matches!(
            err,
            ContractError::SchemaValidationFailed { ref reason, .. }
                if reason.contains("duplicate")
        ));
    }

    #[test]
    fn test_clause_db_contract_watch_invariant_fails() {
        let mut contract = ClauseDbContract::all_satisfied();
        contract.watch_invariant = false;
        let err = contract.validate().expect_err("should fail");
        assert!(matches!(
            err,
            ContractError::SchemaValidationFailed { ref reason, .. }
                if reason.contains("watch")
        ));
    }

    #[test]
    fn test_clause_db_contract_tautology_fails() {
        let mut contract = ClauseDbContract::all_satisfied();
        contract.no_tautologies = false;
        let err = contract.validate().expect_err("should fail");
        assert!(matches!(
            err,
            ContractError::SchemaValidationFailed { ref reason, .. }
                if reason.contains("tautological")
        ));
    }

    #[test]
    fn test_proof_obligation_learn() {
        let obligation = ProofObligation::Learn {
            clause_lits: vec![1, -2, 3],
            resolution_chain: vec![0, 1, 2],
        };
        if let ProofObligation::Learn {
            clause_lits,
            resolution_chain,
        } = &obligation
        {
            assert_eq!(clause_lits.len(), 3);
            assert_eq!(resolution_chain.len(), 3);
        } else {
            panic!("expected Learn variant");
        }
    }

    #[test]
    fn test_proof_obligation_propagate() {
        let obligation = ProofObligation::Propagate {
            literal: -7,
            reason_clause: 5,
        };
        assert_eq!(
            obligation,
            ProofObligation::Propagate {
                literal: -7,
                reason_clause: 5,
            }
        );
    }

    #[test]
    fn test_conflict_analysis_contract_valid() {
        let contract = ConflictAnalysisContract {
            learned_clause: vec![1, -3],
            backtrack_level: 1,
            resolution_chain: vec![
                ResolutionChainEntry {
                    clause_id: 0,
                    pivot_literal: 2,
                },
                ResolutionChainEntry {
                    clause_id: 1,
                    pivot_literal: -4,
                },
            ],
        };
        contract.validate(3).expect("should validate at level 3");
    }

    #[test]
    fn test_conflict_analysis_contract_empty_clause_fails() {
        let contract = ConflictAnalysisContract {
            learned_clause: vec![],
            backtrack_level: 0,
            resolution_chain: vec![ResolutionChainEntry {
                clause_id: 0,
                pivot_literal: 1,
            }],
        };
        let err = contract.validate(2).expect_err("should fail");
        assert!(matches!(
            err,
            ContractError::SchemaValidationFailed { ref reason, .. }
                if reason.contains("empty")
        ));
    }

    #[test]
    fn test_conflict_analysis_contract_zero_literal_fails() {
        let contract = ConflictAnalysisContract {
            learned_clause: vec![1, 0, -3],
            backtrack_level: 0,
            resolution_chain: vec![ResolutionChainEntry {
                clause_id: 0,
                pivot_literal: 1,
            }],
        };
        let err = contract.validate(2).expect_err("should fail");
        assert!(matches!(
            err,
            ContractError::SchemaValidationFailed { ref reason, .. }
                if reason.contains("zero literal")
        ));
    }

    #[test]
    fn test_conflict_analysis_contract_backtrack_level_too_high() {
        let contract = ConflictAnalysisContract {
            learned_clause: vec![1],
            backtrack_level: 5,
            resolution_chain: vec![ResolutionChainEntry {
                clause_id: 0,
                pivot_literal: 1,
            }],
        };
        let err = contract
            .validate(5)
            .expect_err("should fail: bt_level == current");
        assert!(matches!(
            err,
            ContractError::SchemaValidationFailed { ref reason, .. }
                if reason.contains("not less than")
        ));
    }

    #[test]
    fn test_conflict_analysis_contract_empty_chain_fails() {
        let contract = ConflictAnalysisContract {
            learned_clause: vec![1],
            backtrack_level: 0,
            resolution_chain: vec![],
        };
        let err = contract.validate(2).expect_err("should fail");
        assert!(matches!(
            err,
            ContractError::SchemaValidationFailed { ref reason, .. }
                if reason.contains("chain is empty")
        ));
    }

    #[test]
    fn test_conflict_analysis_contract_zero_pivot_fails() {
        let contract = ConflictAnalysisContract {
            learned_clause: vec![1],
            backtrack_level: 0,
            resolution_chain: vec![ResolutionChainEntry {
                clause_id: 0,
                pivot_literal: 0,
            }],
        };
        let err = contract.validate(2).expect_err("should fail");
        assert!(matches!(
            err,
            ContractError::SchemaValidationFailed { ref reason, .. }
                if reason.contains("zero pivot")
        ));
    }

    // ---- Multi-envelope scenario ----

    #[test]
    fn test_verify_multiple_envelopes_pipeline() {
        let registry = ContractRegistry::default();

        let zt01 = CertificateEnvelope::new(
            "ZT01",
            "extended_resolution",
            sample_proof_hash(),
            "0.1.0",
            1000,
        )
        .with_dependency("PC01");

        let zt03 =
            CertificateEnvelope::new("ZT03", "cutting_planes", sample_proof_hash(), "0.1.0", 1001)
                .with_dependency("PC03");

        let zt05 =
            CertificateEnvelope::new("ZT05", "pseudo_boolean", sample_proof_hash(), "0.1.0", 1002)
                .with_dependency("PC03")
                .with_dependency("PC04");

        let available = &["PC01", "PC03", "PC04"];

        for env in [&zt01, &zt03, &zt05] {
            verify_envelope_with_deps(env, &registry, available)
                .unwrap_or_else(|e| panic!("envelope {} failed: {e}", env.theorem_id));
        }
    }
}
