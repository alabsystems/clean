// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRAT-to-kernel proof bridge with competition format support.
//!
//! Converts verified LRAT (Linear Resolution Asymmetric Tautology) proofs
//! into kernel-level proof certificates, enabling SAT solver certificates
//! to be type-checked by the clean kernel.
//!
//! ## Architecture
//!
//! 1. Parse CNF formula (DIMACS) and LRAT proof (text or binary).
//! 2. Run [`LratChecker`] to verify the proof is a valid refutation.
//! 3. Compute blake3 hashes of the formula and proof for provenance.
//! 4. Package into an [`LratKernelProof`] certificate.
//! 5. Optionally convert to a [`CertificateEnvelope`] for ay consumption.
//!
//! ## Competition Format
//!
//! The [`verify_competition_proof`] function accepts raw DIMACS + LRAT text,
//! the format used by SAT-COMP judges for UNSAT certificate validation.
//!
//! ## References
//!
//! - Cruz-Filipe et al. (2017): "Efficient Certified RAT Verification"
//! - Heule et al. (2017): "Trimming while Checking Clausal Proofs"

use std::collections::HashMap;
use std::time::{Duration, Instant};

use thiserror::Error;

use super::ay_contract::CertificateEnvelope;
use super::lrat::{
    is_binary_lrat, parse_binary_lrat, parse_text_lrat, ClauseId, LratChecker, LratError,
    LratResult, LratStep,
};
use super::types::Cnf;

/// Detected format of a proof or formula input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DetectedFormat {
    /// Standard text format (UTF-8 encoded).
    Text,
    /// Binary format with `'a'`/`'d'` step tags and ULEB128 integers.
    Binary,
}

impl std::fmt::Display for DetectedFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DetectedFormat::Text => write!(f, "text"),
            DetectedFormat::Binary => write!(f, "binary"),
        }
    }
}

/// Structured result from competition-mode LRAT verification.
///
/// Contains timing, clause statistics, format detection, and the underlying
/// kernel proof certificate. This is the structured output a SAT-COMP judge
/// would inspect.
#[derive(Debug, Clone)]
pub struct CompetitionResult {
    /// Whether the proof is a valid UNSAT refutation.
    pub valid: bool,
    /// Number of variables in the input formula.
    pub num_vars: u32,
    /// Number of original clauses in the input formula.
    pub original_clauses: usize,
    /// Number of derived (learned) clauses accepted during verification.
    pub derived_clauses: usize,
    /// Number of clause deletions processed.
    pub deleted_clauses: usize,
    /// Number of active clauses remaining after verification.
    pub active_clauses: usize,
    /// Total number of proof steps (additions + deletions).
    pub proof_steps: usize,
    /// Detected format of the LRAT proof input.
    pub proof_format: DetectedFormat,
    /// Wall-clock time spent parsing the CNF formula.
    pub parse_cnf_time: Duration,
    /// Wall-clock time spent parsing the LRAT proof.
    pub parse_proof_time: Duration,
    /// Wall-clock time spent on RUP/RAT verification.
    pub verify_time: Duration,
    /// Total wall-clock time (parse + verify).
    pub total_time: Duration,
    /// The full kernel proof certificate (if verification succeeded).
    pub kernel_proof: Option<LratKernelProof>,
}

/// Errors from LRAT bridge operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum LratBridgeError {
    /// LRAT parsing or verification failed.
    #[error("LRAT error: {0}")]
    Lrat(#[from] LratError),

    /// CNF formula is invalid.
    #[error("invalid CNF formula: {reason}")]
    InvalidCnf { reason: String },

    /// Proof did not derive a contradiction (not a valid refutation).
    #[error("proof is not a refutation: verified {steps} steps but no empty clause derived")]
    NotRefutation { steps: usize },
}

/// Verification status of an LRAT proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LratVerificationStatus {
    /// Proof has been verified as a valid refutation.
    Verified,
    /// Verification failed with an error message.
    Failed(String),
    /// Proof has not been checked yet.
    Unchecked,
}

/// A verified LRAT proof with its kernel-level certificate.
#[derive(Debug, Clone)]
pub struct LratKernelProof {
    /// Blake3 hash of the input CNF formula (DIMACS encoding).
    pub formula_hash: [u8; 32],
    /// Blake3 hash of the LRAT proof data.
    pub proof_hash: [u8; 32],
    /// Number of proof steps (additions + deletions).
    pub step_count: usize,
    /// Number of original clauses in the input formula.
    pub clause_count: usize,
    /// Number of derived (learned) clauses accepted.
    pub derived_count: usize,
    /// Number of clause deletions processed.
    pub deleted_count: usize,
    /// Number of variables in the input formula.
    pub num_vars: u32,
    /// Verification status.
    pub verification_status: LratVerificationStatus,
    /// Wall-clock verification time.
    pub verification_time: Duration,
}

impl LratKernelProof {
    /// Whether this proof is a verified refutation.
    #[must_use]
    pub fn is_verified(&self) -> bool {
        self.verification_status == LratVerificationStatus::Verified
    }

    /// The formula hash as a hex string.
    #[must_use]
    pub fn formula_hash_hex(&self) -> String {
        self.formula_hash
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }

    /// The proof hash as a hex string.
    #[must_use]
    pub fn proof_hash_hex(&self) -> String {
        self.proof_hash.iter().map(|b| format!("{b:02x}")).collect()
    }
}

/// Statistics about an LRAT proof derivation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LratStats {
    /// Number of derivation (Add) steps.
    pub derivation_steps: usize,
    /// Number of deletion steps.
    pub deletion_steps: usize,
    /// Maximum clause ID encountered.
    pub max_clause_id: u64,
    /// Total number of hints referenced across all derivation steps.
    pub total_hints: usize,
    /// Number of derivation steps that used at least one hint.
    pub steps_with_hints: usize,
}

impl LratStats {
    /// Hint utilization rate: fraction of derivation steps that use hints.
    ///
    /// Returns 0.0 if there are no derivation steps.
    #[must_use]
    pub fn hint_utilization_rate(&self) -> f64 {
        if self.derivation_steps == 0 {
            return 0.0;
        }
        self.steps_with_hints as f64 / self.derivation_steps as f64
    }
}

/// Verify a text LRAT proof against a CNF formula and produce a kernel certificate.
///
/// # Errors
///
/// Returns [`LratBridgeError`] if parsing, validation, or verification fails.
pub fn verify_and_certify(
    cnf: &[Vec<i32>],
    lrat_proof: &str,
) -> Result<LratKernelProof, LratBridgeError> {
    let (num_vars, formula_hash) = validate_and_hash_cnf(cnf)?;
    let proof_hash = blake3::hash(lrat_proof.as_bytes()).into();
    let steps = parse_text_lrat(lrat_proof)?;
    run_verification(cnf, num_vars, &steps, formula_hash, proof_hash)
}

/// Verify a binary LRAT proof against a CNF formula and produce a kernel certificate.
///
/// # Errors
///
/// Returns [`LratBridgeError`] if parsing, validation, or verification fails.
pub fn verify_binary_and_certify(
    cnf: &[Vec<i32>],
    lrat_data: &[u8],
) -> Result<LratKernelProof, LratBridgeError> {
    let (num_vars, formula_hash) = validate_and_hash_cnf(cnf)?;
    let proof_hash = blake3::hash(lrat_data).into();
    let steps = parse_binary_lrat(lrat_data)?;
    run_verification(cnf, num_vars, &steps, formula_hash, proof_hash)
}

/// Verify an LRAT proof with auto-detection of text vs binary format.
///
/// # Errors
///
/// Returns [`LratBridgeError`] if parsing, validation, or verification fails.
pub fn verify_auto_and_certify(
    cnf: &[Vec<i32>],
    lrat_data: &[u8],
) -> Result<LratKernelProof, LratBridgeError> {
    if is_binary_lrat(lrat_data) {
        verify_binary_and_certify(cnf, lrat_data)
    } else {
        let text = std::str::from_utf8(lrat_data).map_err(|e| LratBridgeError::InvalidCnf {
            reason: format!("LRAT data is not valid UTF-8: {e}"),
        })?;
        verify_and_certify(cnf, text)
    }
}

/// End-to-end competition format verification: DIMACS + LRAT text.
///
/// This is the entry point SAT-COMP judges would use. Parses DIMACS,
/// parses LRAT, verifies, and produces a kernel certificate.
///
/// # Errors
///
/// Returns [`LratBridgeError`] if any step fails.
pub fn verify_competition_proof(
    dimacs: &str,
    lrat: &str,
) -> Result<LratKernelProof, LratBridgeError> {
    let cnf = Cnf::from_dimacs(dimacs).map_err(|e| LratBridgeError::InvalidCnf {
        reason: e.to_string(),
    })?;
    let raw_clauses = cnf.to_dimacs_clauses();
    verify_and_certify(&raw_clauses, lrat)
}

/// Competition-mode entry point: accepts raw bytes for both CNF and proof.
///
/// Auto-detects text vs binary LRAT format. The CNF must be in text DIMACS
/// format (binary DIMACS is not used in SAT-COMP). Returns a structured
/// [`CompetitionResult`] with detailed timing breakdowns.
///
/// This is the primary entry point for SAT-COMP 2026 UNSAT certificate
/// validation. It handles:
/// - Text DIMACS CNF parsing
/// - Auto-detection of text vs binary LRAT proof format
/// - Linear-time hint-guided RUP verification
/// - Clause deletion processing
/// - Empty clause (refutation) detection
///
/// # Errors
///
/// Returns [`LratBridgeError`] if parsing or verification fails.
pub fn verify_lrat_competition(
    cnf: &[u8],
    proof: &[u8],
) -> Result<CompetitionResult, LratBridgeError> {
    let total_start = Instant::now();

    // Parse CNF (always text DIMACS).
    let parse_cnf_start = Instant::now();
    let dimacs_str = std::str::from_utf8(cnf).map_err(|e| LratBridgeError::InvalidCnf {
        reason: format!("CNF data is not valid UTF-8: {e}"),
    })?;
    let cnf_formula = Cnf::from_dimacs(dimacs_str).map_err(|e| LratBridgeError::InvalidCnf {
        reason: e.to_string(),
    })?;
    let raw_clauses = cnf_formula.to_dimacs_clauses();
    let num_vars = cnf_formula.num_vars;
    let original_clause_count = raw_clauses.len();
    let parse_cnf_time = parse_cnf_start.elapsed();

    // Parse LRAT proof (auto-detect text vs binary).
    let parse_proof_start = Instant::now();
    let proof_format = if is_binary_lrat(proof) {
        DetectedFormat::Binary
    } else {
        DetectedFormat::Text
    };
    let steps = match proof_format {
        DetectedFormat::Binary => parse_binary_lrat(proof)?,
        DetectedFormat::Text => {
            let text = std::str::from_utf8(proof).map_err(|e| LratBridgeError::InvalidCnf {
                reason: format!("LRAT text data is not valid UTF-8: {e}"),
            })?;
            parse_text_lrat(text)?
        }
    };
    let parse_proof_time = parse_proof_start.elapsed();

    // Verify.
    let verify_start = Instant::now();
    let (num_vars_checked, formula_hash) = validate_and_hash_cnf(&raw_clauses)?;
    let proof_hash: [u8; 32] = blake3::hash(proof).into();
    let mut checker = LratChecker::new(num_vars_checked);

    for (idx, clause) in raw_clauses.iter().enumerate() {
        let id = ClauseId((idx as u64) + 1);
        let lits: Vec<super::types::Lit> = clause.iter().map(|&v| super::types::Lit(v)).collect();
        checker.add_original(id, &lits)?;
    }

    let result: LratResult = checker.verify_proof(&steps)?;
    let verify_time = verify_start.elapsed();
    let total_time = total_start.elapsed();

    let valid = result.refuted;

    let kernel_proof = if valid {
        Some(LratKernelProof {
            formula_hash,
            proof_hash,
            step_count: result.verified_steps,
            clause_count: result.original_clauses,
            derived_count: result.derived_clauses,
            deleted_count: result.deleted_clauses,
            num_vars,
            verification_status: LratVerificationStatus::Verified,
            verification_time: verify_time,
        })
    } else {
        None
    };

    Ok(CompetitionResult {
        valid,
        num_vars,
        original_clauses: original_clause_count,
        derived_clauses: result.derived_clauses,
        deleted_clauses: result.deleted_clauses,
        active_clauses: result.active_clauses,
        proof_steps: result.verified_steps,
        proof_format,
        parse_cnf_time,
        parse_proof_time,
        verify_time,
        total_time,
        kernel_proof,
    })
}

/// Convert a verified LRAT kernel proof into a ay [`CertificateEnvelope`].
///
/// The envelope uses mechanism "lrat_verification" and theorem ID "LRAT01".
#[must_use]
pub fn to_certificate_envelope(proof: &LratKernelProof) -> CertificateEnvelope {
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);

    let mut metadata = HashMap::new();
    metadata.insert("formula_hash".to_owned(), proof.formula_hash_hex());
    metadata.insert("step_count".to_owned(), proof.step_count.to_string());
    metadata.insert("clause_count".to_owned(), proof.clause_count.to_string());
    metadata.insert("derived_count".to_owned(), proof.derived_count.to_string());
    metadata.insert("num_vars".to_owned(), proof.num_vars.to_string());
    metadata.insert(
        "verification_time_us".to_owned(),
        proof.verification_time.as_micros().to_string(),
    );
    metadata.insert("verified".to_owned(), proof.is_verified().to_string());

    CertificateEnvelope {
        theorem_id: "LRAT01".to_owned(),
        mechanism: "lrat_verification".to_owned(),
        proof_hash: proof.proof_hash,
        clean_version: env!("CARGO_PKG_VERSION").to_owned(),
        timestamp,
        dependencies: Vec::new(),
        metadata,
    }
}

/// Compute statistics from parsed LRAT proof steps.
#[must_use]
pub fn compute_stats(steps: &[LratStep]) -> LratStats {
    let mut derivation_steps = 0usize;
    let mut deletion_steps = 0usize;
    let mut max_clause_id = 0u64;
    let mut total_hints = 0usize;
    let mut steps_with_hints = 0usize;

    for step in steps {
        match step {
            LratStep::Add { id, hints, .. } => {
                derivation_steps += 1;
                if id.0 > max_clause_id {
                    max_clause_id = id.0;
                }
                total_hints += hints.len();
                if !hints.is_empty() {
                    steps_with_hints += 1;
                }
            }
            LratStep::Delete { clause_ids } => {
                deletion_steps += 1;
                for cid in clause_ids {
                    if cid.0 > max_clause_id {
                        max_clause_id = cid.0;
                    }
                }
            }
        }
    }

    LratStats {
        derivation_steps,
        deletion_steps,
        max_clause_id,
        total_hints,
        steps_with_hints,
    }
}

/// Compute statistics from a text LRAT proof string.
///
/// # Errors
///
/// Returns [`LratBridgeError`] if parsing fails.
pub fn compute_stats_from_text(lrat_proof: &str) -> Result<LratStats, LratBridgeError> {
    let steps = parse_text_lrat(lrat_proof)?;
    Ok(compute_stats(&steps))
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Validate a CNF clause set and compute its blake3 hash.
///
/// Returns `(max_variable, hash)`.
fn validate_and_hash_cnf(cnf: &[Vec<i32>]) -> Result<(u32, [u8; 32]), LratBridgeError> {
    let mut max_var = 0u32;
    let mut hasher = blake3::Hasher::new();

    for clause in cnf {
        for &lit in clause {
            if lit == 0 {
                return Err(LratBridgeError::InvalidCnf {
                    reason: "clause contains literal 0".to_owned(),
                });
            }
            let var = lit.unsigned_abs();
            if var > max_var {
                max_var = var;
            }
            hasher.update(&lit.to_le_bytes());
        }
        // Clause terminator in hash.
        hasher.update(&0i32.to_le_bytes());
    }

    Ok((max_var, hasher.finalize().into()))
}

/// Run LRAT verification on parsed steps and build the kernel proof.
fn run_verification(
    cnf: &[Vec<i32>],
    num_vars: u32,
    steps: &[LratStep],
    formula_hash: [u8; 32],
    proof_hash: [u8; 32],
) -> Result<LratKernelProof, LratBridgeError> {
    let start = Instant::now();
    let mut checker = LratChecker::new(num_vars);

    // Load original clauses with sequential IDs starting at 1.
    for (idx, clause) in cnf.iter().enumerate() {
        let id = ClauseId((idx as u64) + 1);
        let lits: Vec<super::types::Lit> = clause.iter().map(|&v| super::types::Lit(v)).collect();
        checker.add_original(id, &lits)?;
    }

    let result: LratResult = checker.verify_proof(steps)?;
    let elapsed = start.elapsed();

    if !result.refuted {
        return Err(LratBridgeError::NotRefutation {
            steps: result.verified_steps,
        });
    }

    Ok(LratKernelProof {
        formula_hash,
        proof_hash,
        step_count: result.verified_steps,
        clause_count: result.original_clauses,
        derived_count: result.derived_clauses,
        deleted_count: result.deleted_clauses,
        num_vars,
        verification_status: LratVerificationStatus::Verified,
        verification_time: elapsed,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // Simple UNSAT formula: (x1) AND (-x1)
    // Original clauses: 1: {1}, 2: {-1}
    // LRAT proof: derive empty clause from hints [1, 2]
    const SIMPLE_CNF: &[&[i32]] = &[&[1], &[-1]];
    const SIMPLE_LRAT: &str = "3 0 1 2 0\n";

    fn simple_cnf_owned() -> Vec<Vec<i32>> {
        SIMPLE_CNF.iter().map(|c| c.to_vec()).collect()
    }

    // Two-variable UNSAT: (x1 v x2) AND (-x1) AND (-x2)
    // Clauses: 1: {1,2}, 2: {-1}, 3: {-2}
    // Proof: derive {2} from clauses 1,2; then derive {} from 4,3
    const TWO_VAR_CNF: &[&[i32]] = &[&[1, 2], &[-1], &[-2]];
    const TWO_VAR_LRAT: &str = "4 2 0 1 2 0\n5 0 4 3 0\n";

    fn two_var_cnf_owned() -> Vec<Vec<i32>> {
        TWO_VAR_CNF.iter().map(|c| c.to_vec()).collect()
    }

    #[test]
    fn test_verify_and_certify_simple_unsat() {
        let cnf = simple_cnf_owned();
        let proof = verify_and_certify(&cnf, SIMPLE_LRAT).expect("simple UNSAT should verify");

        assert!(proof.is_verified());
        assert_eq!(proof.verification_status, LratVerificationStatus::Verified);
        assert_eq!(proof.clause_count, 2);
        assert_eq!(proof.step_count, 1);
        assert_eq!(proof.derived_count, 1);
        assert_eq!(proof.num_vars, 1);
        assert_ne!(proof.formula_hash, [0u8; 32]);
        assert_ne!(proof.proof_hash, [0u8; 32]);
    }

    #[test]
    fn test_verify_and_certify_two_variable() {
        let cnf = two_var_cnf_owned();
        let proof =
            verify_and_certify(&cnf, TWO_VAR_LRAT).expect("two-variable UNSAT should verify");

        assert!(proof.is_verified());
        assert_eq!(proof.clause_count, 3);
        assert_eq!(proof.step_count, 2);
        assert_eq!(proof.derived_count, 2);
        assert_eq!(proof.num_vars, 2);
    }

    #[test]
    fn test_verify_and_certify_invalid_lrat() {
        let cnf = simple_cnf_owned();
        // Hint references non-existent clause 99.
        let bad_lrat = "3 0 1 99 0\n";
        let err = verify_and_certify(&cnf, bad_lrat).expect_err("invalid LRAT should fail");
        assert!(matches!(err, LratBridgeError::Lrat(_)));
    }

    #[test]
    fn test_verify_and_certify_not_refutation() {
        // Formula is satisfiable: (x1 v x2)
        let cnf = vec![vec![1, 2]];
        // Proof tries to derive clause {1} from hint 1, but this doesn't
        // produce a refutation since {1} is not empty.
        // Actually, let's just provide an empty proof.
        let empty_lrat = "";
        let err = verify_and_certify(&cnf, empty_lrat);
        // Empty proof verifies 0 steps, but doesn't refute.
        assert!(err.is_err());
    }

    #[test]
    fn test_verify_and_certify_cnf_with_zero_literal() {
        let cnf = vec![vec![1, 0, -2]];
        let err = verify_and_certify(&cnf, "").expect_err("CNF with zero literal should fail");
        assert!(matches!(err, LratBridgeError::InvalidCnf { .. }));
    }

    #[test]
    fn test_verify_binary_and_certify() {
        // Build binary LRAT for the simple UNSAT case.
        // Binary format: 'a' <clause_id> <lits...> 0 <hints...> 0
        let binary_data = vec![
            b'a', // clause id 3 as ULEB128
            3,    // empty clause: terminate literals with 0
            0,
            // hints: 1 and 2 encoded as ULEB128, positive hints use 2*n encoding
            2, // hint 1 -> 2*1 = 2
            4, // hint 2 -> 2*2 = 4
            0, // terminate hints
        ];

        let cnf = simple_cnf_owned();
        let proof =
            verify_binary_and_certify(&cnf, &binary_data).expect("binary LRAT should verify");

        assert!(proof.is_verified());
        assert_eq!(proof.clause_count, 2);
        assert_eq!(proof.derived_count, 1);
    }

    #[test]
    fn test_verify_auto_detects_text() {
        let cnf = simple_cnf_owned();
        let proof = verify_auto_and_certify(&cnf, SIMPLE_LRAT.as_bytes())
            .expect("auto-detect should handle text LRAT");
        assert!(proof.is_verified());
    }

    #[test]
    fn test_verify_auto_detects_binary() {
        let binary_data = vec![b'a', 3, 0, 2, 4, 0];

        let cnf = simple_cnf_owned();
        let proof = verify_auto_and_certify(&cnf, &binary_data)
            .expect("auto-detect should handle binary LRAT");
        assert!(proof.is_verified());
    }

    #[test]
    fn test_certificate_envelope_fields() {
        let cnf = simple_cnf_owned();
        let proof = verify_and_certify(&cnf, SIMPLE_LRAT).expect("should verify");

        let envelope = to_certificate_envelope(&proof);

        assert_eq!(envelope.theorem_id, "LRAT01");
        assert_eq!(envelope.mechanism, "lrat_verification");
        assert_eq!(envelope.proof_hash, proof.proof_hash);
        assert!(envelope.dependencies.is_empty());
        assert_eq!(envelope.metadata.get("clause_count"), Some(&"2".to_owned()));
        assert_eq!(envelope.metadata.get("step_count"), Some(&"1".to_owned()));
        assert_eq!(envelope.metadata.get("verified"), Some(&"true".to_owned()));
        assert!(envelope.metadata.contains_key("formula_hash"));
        assert!(envelope.metadata.contains_key("verification_time_us"));
    }

    #[test]
    fn test_certificate_envelope_has_correct_hashes() {
        let cnf = simple_cnf_owned();
        let proof = verify_and_certify(&cnf, SIMPLE_LRAT).expect("should verify");

        let envelope = to_certificate_envelope(&proof);

        // proof_hash in envelope must match the kernel proof's proof_hash.
        assert_eq!(envelope.proof_hash, proof.proof_hash);
        // formula_hash is in metadata.
        assert_eq!(
            envelope.metadata.get("formula_hash").map(String::as_str),
            Some(proof.formula_hash_hex().as_str())
        );
    }

    #[test]
    fn test_certificate_envelope_json_roundtrip() {
        let cnf = simple_cnf_owned();
        let proof = verify_and_certify(&cnf, SIMPLE_LRAT).expect("should verify");
        let envelope = to_certificate_envelope(&proof);

        let json = envelope.to_json().expect("should serialize");
        let restored = CertificateEnvelope::from_json(&json).expect("should deserialize");

        assert_eq!(restored.theorem_id, envelope.theorem_id);
        assert_eq!(restored.mechanism, envelope.mechanism);
        assert_eq!(restored.proof_hash, envelope.proof_hash);
    }

    #[test]
    fn test_compute_stats_simple() {
        let steps = parse_text_lrat(SIMPLE_LRAT).expect("should parse");
        let stats = compute_stats(&steps);

        assert_eq!(stats.derivation_steps, 1);
        assert_eq!(stats.deletion_steps, 0);
        assert_eq!(stats.max_clause_id, 3);
        assert_eq!(stats.total_hints, 2);
        assert_eq!(stats.steps_with_hints, 1);
        assert!((stats.hint_utilization_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_compute_stats_with_deletions() {
        // LRAT with an add step and a delete step.
        let lrat = "4 2 0 1 2 0\n5 d 1 2 0\n6 0 4 3 0\n";
        let steps = parse_text_lrat(lrat).expect("should parse");
        let stats = compute_stats(&steps);

        assert_eq!(stats.derivation_steps, 2);
        assert_eq!(stats.deletion_steps, 1);
        assert_eq!(stats.max_clause_id, 6);
        assert_eq!(stats.steps_with_hints, 2);
    }

    #[test]
    fn test_compute_stats_empty_proof() {
        let stats = compute_stats(&[]);
        assert_eq!(stats.derivation_steps, 0);
        assert_eq!(stats.deletion_steps, 0);
        assert_eq!(stats.max_clause_id, 0);
        assert_eq!(stats.total_hints, 0);
        assert_eq!(stats.hint_utilization_rate(), 0.0);
    }

    #[test]
    fn test_compute_stats_from_text() {
        let stats = compute_stats_from_text(SIMPLE_LRAT).expect("should parse and compute stats");
        assert_eq!(stats.derivation_steps, 1);
        assert_eq!(stats.total_hints, 2);
    }

    #[test]
    fn test_competition_format_end_to_end() {
        let dimacs = "\
c Simple UNSAT instance
p cnf 1 2
1 0
-1 0
";
        let lrat = "3 0 1 2 0\n";

        let proof =
            verify_competition_proof(dimacs, lrat).expect("competition format should verify");

        assert!(proof.is_verified());
        assert_eq!(proof.clause_count, 2);
        assert_eq!(proof.num_vars, 1);
        assert_eq!(proof.step_count, 1);
    }

    #[test]
    fn test_competition_format_two_variable() {
        let dimacs = "\
p cnf 2 3
1 2 0
-1 0
-2 0
";
        let lrat = "4 2 0 1 2 0\n5 0 4 3 0\n";

        let proof = verify_competition_proof(dimacs, lrat)
            .expect("two-variable competition proof should verify");

        assert!(proof.is_verified());
        assert_eq!(proof.clause_count, 3);
        assert_eq!(proof.num_vars, 2);
        assert_eq!(proof.derived_count, 2);
    }

    #[test]
    fn test_competition_format_invalid_dimacs() {
        let bad_dimacs = "not valid dimacs";
        let lrat = "3 0 1 2 0\n";
        let err =
            verify_competition_proof(bad_dimacs, lrat).expect_err("invalid DIMACS should fail");
        assert!(matches!(err, LratBridgeError::InvalidCnf { .. }));
    }

    #[test]
    fn test_formula_hash_deterministic() {
        let cnf = simple_cnf_owned();
        let proof1 = verify_and_certify(&cnf, SIMPLE_LRAT).expect("should verify");
        let proof2 = verify_and_certify(&cnf, SIMPLE_LRAT).expect("should verify");
        assert_eq!(proof1.formula_hash, proof2.formula_hash);
        assert_eq!(proof1.proof_hash, proof2.proof_hash);
    }

    #[test]
    fn test_different_formulas_different_hashes() {
        let cnf1 = simple_cnf_owned();
        let cnf2 = two_var_cnf_owned();
        let proof1 = verify_and_certify(&cnf1, SIMPLE_LRAT).expect("should verify");
        let proof2 = verify_and_certify(&cnf2, TWO_VAR_LRAT).expect("should verify");
        assert_ne!(proof1.formula_hash, proof2.formula_hash);
        assert_ne!(proof1.proof_hash, proof2.proof_hash);
    }

    #[test]
    fn test_hash_hex_format() {
        let cnf = simple_cnf_owned();
        let proof = verify_and_certify(&cnf, SIMPLE_LRAT).expect("should verify");
        let hex = proof.formula_hash_hex();
        assert_eq!(hex.len(), 64);
        assert!(hex.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_lrat_verification_status_equality() {
        assert_eq!(
            LratVerificationStatus::Verified,
            LratVerificationStatus::Verified
        );
        assert_eq!(
            LratVerificationStatus::Unchecked,
            LratVerificationStatus::Unchecked
        );
        assert_ne!(
            LratVerificationStatus::Verified,
            LratVerificationStatus::Unchecked
        );
        assert_eq!(
            LratVerificationStatus::Failed("x".to_owned()),
            LratVerificationStatus::Failed("x".to_owned())
        );
        assert_ne!(
            LratVerificationStatus::Failed("x".to_owned()),
            LratVerificationStatus::Failed("y".to_owned())
        );
    }

    // ---- Competition-mode (verify_lrat_competition) tests ----

    const SIMPLE_DIMACS: &str = "p cnf 1 2\n1 0\n-1 0\n";
    const TWO_VAR_DIMACS: &str = "p cnf 2 3\n1 2 0\n-1 0\n-2 0\n";

    #[test]
    fn test_competition_raw_bytes_text_lrat() {
        let result = verify_lrat_competition(SIMPLE_DIMACS.as_bytes(), SIMPLE_LRAT.as_bytes())
            .expect("competition text LRAT should verify");

        assert!(result.valid);
        assert_eq!(result.num_vars, 1);
        assert_eq!(result.original_clauses, 2);
        assert_eq!(result.derived_clauses, 1);
        assert_eq!(result.proof_steps, 1);
        assert_eq!(result.proof_format, DetectedFormat::Text);
        assert!(result.kernel_proof.is_some());
        let kp = result.kernel_proof.as_ref().expect("kernel proof present");
        assert!(kp.is_verified());
    }

    #[test]
    fn test_competition_raw_bytes_binary_lrat() {
        // Build binary LRAT for simple UNSAT: add empty clause with hints 1, 2.
        let binary_proof = vec![
            b'a', 3, // clause id 3
            0, // empty clause (no literals)
            2, // hint 1 -> 2*1 = 2
            4, // hint 2 -> 2*2 = 4
            0, // end hints
        ];

        let result = verify_lrat_competition(SIMPLE_DIMACS.as_bytes(), &binary_proof)
            .expect("competition binary LRAT should verify");

        assert!(result.valid);
        assert_eq!(result.proof_format, DetectedFormat::Binary);
        assert_eq!(result.original_clauses, 2);
        assert_eq!(result.derived_clauses, 1);
        assert!(result.kernel_proof.is_some());
    }

    #[test]
    fn test_competition_two_variable_with_deletion() {
        // Proof with deletion step for memory management.
        let lrat_with_delete = "4 2 0 1 2 0\n5 d 1 0\n6 0 4 3 0\n";

        let result =
            verify_lrat_competition(TWO_VAR_DIMACS.as_bytes(), lrat_with_delete.as_bytes())
                .expect("competition proof with deletion should verify");

        assert!(result.valid);
        assert_eq!(result.num_vars, 2);
        assert_eq!(result.original_clauses, 3);
        assert_eq!(result.derived_clauses, 2);
        assert_eq!(result.deleted_clauses, 1);
        // After derivation and deletion, active should be:
        // original 3 + derived 2 - deleted 1 = 4
        assert_eq!(result.active_clauses, 4);
        assert_eq!(result.proof_steps, 3); // add + delete + add
    }

    #[test]
    fn test_competition_timing_fields_nonzero() {
        let result = verify_lrat_competition(SIMPLE_DIMACS.as_bytes(), SIMPLE_LRAT.as_bytes())
            .expect("should verify");

        // Total time must be >= verify time (includes parse overhead).
        assert!(result.total_time >= result.verify_time);
        // Total time must be >= parse times.
        assert!(result.total_time >= result.parse_cnf_time);
    }

    #[test]
    fn test_competition_invalid_cnf_bytes() {
        let err = verify_lrat_competition(b"\xff\xfe invalid utf8", SIMPLE_LRAT.as_bytes())
            .expect_err("invalid UTF-8 CNF should fail");
        assert!(matches!(err, LratBridgeError::InvalidCnf { .. }));
    }

    #[test]
    fn test_competition_not_refutation() {
        // SAT formula with no refutation proof.
        let sat_dimacs = b"p cnf 1 1\n1 0\n";
        // Empty proof: verifies 0 steps but no refutation.
        let result = verify_lrat_competition(sat_dimacs, b"");
        // This should succeed but report valid=false.
        let r = result.expect("should return result, not error for empty proof");
        assert!(!r.valid);
        assert!(r.kernel_proof.is_none());
    }

    #[test]
    fn test_competition_detected_format_display() {
        assert_eq!(DetectedFormat::Text.to_string(), "text");
        assert_eq!(DetectedFormat::Binary.to_string(), "binary");
    }
}
