// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Result persistence for verified theorems discovered by the search loop.
//!
//! `ResultStore` provides append-only storage of verified theorems with
//! JSON serialization to disk, deduplication by theorem name, and
//! family-based querying.
//!
//! Part of #3274.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::candidate::{CandidateTheorem, VerificationOutcome};
use crate::error::DiscoveryError;

/// A verified theorem persisted for reporting and future reference.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[non_exhaustive]
pub struct VerifiedTheorem {
    /// Generated theorem name (family + params).
    pub name: String,
    /// The `TheoremFamily` variant as a string.
    pub family: String,
    /// Parameter values as display strings.
    pub params: Vec<String>,
    /// Hash of the statement `Expr` (via `std::hash::Hash`).
    pub statement_hash: u64,
    /// Hash of the proof `Expr` if present.
    pub proof_hash: Option<u64>,
    /// ISO 8601 timestamp of when verification completed.
    pub verified_at: String,
    /// Verification wall-clock time in nanoseconds.
    pub verification_time_ns: u64,
}

/// Persistent store of verified theorem results.
///
/// Results are kept in memory and can be flushed to disk as JSON.
/// Deduplication is by theorem `name` — the last entry wins.
pub struct ResultStore {
    results: Vec<VerifiedTheorem>,
    path: PathBuf,
}

impl ResultStore {
    /// Create a new empty store that will persist to `path`.
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            results: Vec::new(),
            path: path.as_ref().to_path_buf(),
        }
    }

    /// Append a verified theorem, deduplicating by name.
    ///
    /// If a theorem with the same name already exists it is replaced
    /// with the new entry.
    pub fn add(&mut self, theorem: VerifiedTheorem) {
        if let Some(pos) = self.results.iter().position(|t| t.name == theorem.name) {
            self.results[pos] = theorem;
        } else {
            self.results.push(theorem);
        }
    }

    /// Write the store to disk as pretty-printed JSON.
    pub fn save(&self) -> Result<(), DiscoveryError> {
        let json = serde_json::to_string_pretty(&self.results)
            .map_err(|e| DiscoveryError::Serialization(e.to_string()))?;
        std::fs::write(&self.path, json)?;
        Ok(())
    }

    /// Load a store from a JSON file on disk.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, DiscoveryError> {
        let path = path.as_ref();
        let data = std::fs::read_to_string(path)?;
        let results: Vec<VerifiedTheorem> = serde_json::from_str(&data)
            .map_err(|e| DiscoveryError::Serialization(e.to_string()))?;
        Ok(Self {
            results,
            path: path.to_path_buf(),
        })
    }

    /// Return all theorems belonging to the given family name.
    pub fn by_family(&self, family: &str) -> Vec<&VerifiedTheorem> {
        self.results.iter().filter(|t| t.family == family).collect()
    }

    /// Number of stored theorems.
    #[must_use]
    pub fn len(&self) -> usize {
        self.results.len()
    }

    /// Whether the store is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.results.is_empty()
    }

    /// Immutable access to all stored results.
    pub fn results(&self) -> &[VerifiedTheorem] {
        &self.results
    }
}

/// Convert a verified outcome back into a `VerifiedTheorem` for persistence.
///
/// Returns `None` when `outcome.verified` is false.
pub fn from_outcome(
    candidate: &CandidateTheorem,
    outcome: &VerificationOutcome,
) -> Option<VerifiedTheorem> {
    if !outcome.verified {
        return None;
    }

    let name = format!(
        "{}_{}",
        candidate.family,
        candidate
            .params
            .0
            .iter()
            .map(|p| p.to_string())
            .collect::<Vec<_>>()
            .join("_")
    );

    let family = candidate.family.to_string();
    let params: Vec<String> = candidate.params.0.iter().map(|p| p.to_string()).collect();

    let statement_hash = hash_expr(&candidate.statement);
    let proof_hash = candidate.proof.as_ref().map(hash_expr);

    // Use a fixed placeholder timestamp for determinism in tests;
    // callers can override via VerifiedTheorem fields.
    let verified_at = current_timestamp();

    Some(VerifiedTheorem {
        name,
        family,
        params,
        statement_hash,
        proof_hash,
        verified_at,
        verification_time_ns: outcome.time_ns,
    })
}

/// Compute a 64-bit hash of an `Expr` via the standard `Hash` trait.
fn hash_expr(expr: &clean_kernel::Expr) -> u64 {
    let mut hasher = DefaultHasher::new();
    expr.hash(&mut hasher);
    hasher.finish()
}

/// ISO 8601 timestamp via std (no chrono dependency).
fn current_timestamp() -> String {
    // SystemTime → seconds since epoch, formatted as ISO 8601 (UTC).
    let dur = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default();
    let secs = dur.as_secs();
    // Simple epoch-seconds based ISO timestamp (good enough without chrono).
    format!("{secs}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::candidate::{CandidateId, ParamVec};
    use crate::family::TheoremFamily;
    use clean_kernel::Expr;

    fn sample_theorem(name: &str) -> VerifiedTheorem {
        VerifiedTheorem {
            name: name.to_string(),
            family: "CertSizeBound".to_string(),
            params: vec!["1".to_string(), "2".to_string()],
            statement_hash: 12345,
            proof_hash: Some(67890),
            verified_at: "1700000000".to_string(),
            verification_time_ns: 500,
        }
    }

    #[test]
    fn test_result_store_add_and_len() {
        let mut store = ResultStore::new("/tmp/test_unused.json");
        assert!(store.is_empty());

        store.add(sample_theorem("thm_a"));
        assert_eq!(store.len(), 1);

        store.add(sample_theorem("thm_b"));
        assert_eq!(store.len(), 2);
    }

    #[test]
    fn test_result_store_dedup_by_name() {
        let mut store = ResultStore::new("/tmp/test_unused.json");
        let mut t1 = sample_theorem("thm_a");
        t1.verification_time_ns = 100;
        store.add(t1);

        let mut t2 = sample_theorem("thm_a");
        t2.verification_time_ns = 999;
        store.add(t2);

        assert_eq!(store.len(), 1);
        assert_eq!(store.results()[0].verification_time_ns, 999);
    }

    #[test]
    fn test_result_store_by_family() {
        let mut store = ResultStore::new("/tmp/test_unused.json");
        store.add(sample_theorem("a"));

        let mut other_family = sample_theorem("b");
        other_family.family = "DomainTightness".to_string();
        store.add(other_family);

        assert_eq!(store.by_family("CertSizeBound").len(), 1);
        assert_eq!(store.by_family("DomainTightness").len(), 1);
        assert_eq!(store.by_family("NonExistent").len(), 0);
    }

    #[test]
    fn test_result_store_save_load_roundtrip() {
        let dir = std::env::temp_dir().join("clean_discovery_test_roundtrip.json");
        let mut store = ResultStore::new(&dir);
        store.add(sample_theorem("roundtrip_thm"));
        store.save().expect("save should succeed");

        let loaded = ResultStore::load(&dir).expect("load should succeed");
        assert_eq!(loaded.len(), 1);
        assert_eq!(loaded.results()[0].name, "roundtrip_thm");
        assert_eq!(loaded.results()[0], store.results()[0]);

        // cleanup
        let _ = std::fs::remove_file(&dir);
    }

    #[test]
    fn test_from_outcome_verified() {
        let candidate = CandidateTheorem {
            id: CandidateId(0),
            family: TheoremFamily::CertSizeBound,
            params: ParamVec::from_nats(&[2, 4]),
            statement: Expr::prop(),
            proof: Some(Expr::type_()),
        };
        let outcome = VerificationOutcome {
            candidate_id: CandidateId(0),
            verified: true,
            inferred_type: Some(Expr::prop()),
            error: None,
            time_ns: 42,
        };

        let result = from_outcome(&candidate, &outcome);
        assert!(result.is_some());
        let vt = result.unwrap();
        assert_eq!(vt.family, "CertSizeBound");
        assert_eq!(vt.params, vec!["2", "4"]);
        assert_eq!(vt.verification_time_ns, 42);
        assert!(vt.proof_hash.is_some());
    }

    #[test]
    fn test_from_outcome_not_verified_returns_none() {
        let candidate = CandidateTheorem {
            id: CandidateId(1),
            family: TheoremFamily::CertSizeBound,
            params: ParamVec::new(),
            statement: Expr::prop(),
            proof: None,
        };
        let outcome = VerificationOutcome {
            candidate_id: CandidateId(1),
            verified: false,
            inferred_type: None,
            error: Some("type mismatch".to_string()),
            time_ns: 10,
        };

        assert!(from_outcome(&candidate, &outcome).is_none());
    }

    #[test]
    fn test_from_outcome_no_proof_hash_is_none() {
        let candidate = CandidateTheorem {
            id: CandidateId(2),
            family: TheoremFamily::CertSizeBound,
            params: ParamVec::from_nats(&[1]),
            statement: Expr::prop(),
            proof: None,
        };
        let outcome = VerificationOutcome {
            candidate_id: CandidateId(2),
            verified: true,
            inferred_type: Some(Expr::type_()),
            error: None,
            time_ns: 5,
        };

        let vt = from_outcome(&candidate, &outcome).unwrap();
        assert!(vt.proof_hash.is_none());
    }

    #[test]
    fn test_load_nonexistent_file_returns_error() {
        let result = ResultStore::load("/tmp/nonexistent_clean_discovery_test.json");
        assert!(result.is_err());
    }
}
