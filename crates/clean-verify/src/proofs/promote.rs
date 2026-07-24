// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DerivedPending to DerivedProved promotion pipeline.
//!
//! Walks all DerivedPending definitions in the spec, checks if the
//! ProofLibrary has a matching proof that verifies with no HelperAxiom
//! dependencies, and if so promotes the definition to DerivedProved.
//!
//! Part of #3221: Build DerivedPending to DerivedProved promotion pipeline.

use super::ProofLibrary;
use crate::spec::{AxiomCategory, ProofStatus, Specification};
use std::collections::HashSet;

/// Summary statistics for the promotion pipeline.
#[derive(Debug, Clone, Default)]
pub struct PromotionStats {
    /// Total definitions in the spec.
    pub total: usize,
    /// DerivedLemma definitions.
    pub derived_total: usize,
    /// DerivedLemma definitions with DerivedProved status.
    pub derived_proved: usize,
    /// DerivedLemma definitions with DerivedPending status.
    pub derived_pending: usize,
    /// DerivedLemma definitions with Axiom status (no proof yet).
    pub derived_axiom: usize,
    /// FoundationalRule definitions.
    pub foundational: usize,
    /// HelperAxiom definitions.
    pub helper_axiom: usize,
    /// DerivedPending definitions that have proofs in the library.
    pub pending_with_proof: usize,
    /// DerivedPending definitions missing proofs in the library.
    pub pending_no_proof: usize,
}

impl PromotionStats {
    /// Generate a human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        let pct_proved = if self.derived_total > 0 {
            (self.derived_proved as f64 / self.derived_total as f64) * 100.0
        } else {
            0.0
        };
        let pct_with_proof = if self.derived_total > 0 {
            ((self.derived_proved + self.derived_pending) as f64 / self.derived_total as f64)
                * 100.0
        } else {
            0.0
        };
        format!(
            "Promotion Stats:\n\
             - Total definitions: {}\n\
             - FoundationalRule: {}\n\
             - HelperAxiom: {}\n\
             - DerivedLemma: {} total\n\
             -   Axiom (no proof): {}\n\
             -   DerivedPending: {} ({} with proof, {} no proof)\n\
             -   DerivedProved: {} ({pct_proved:.1}%)\n\
             - Proof coverage: {pct_with_proof:.1}%",
            self.total,
            self.foundational,
            self.helper_axiom,
            self.derived_total,
            self.derived_axiom,
            self.derived_pending,
            self.pending_with_proof,
            self.pending_no_proof,
            self.derived_proved,
        )
    }
}

/// Compute summary statistics for the promotion pipeline.
#[must_use]
pub fn count_definitions(spec: &Specification, library: &ProofLibrary) -> PromotionStats {
    let mut stats = PromotionStats {
        total: spec.definitions().len(),
        ..PromotionStats::default()
    };

    for (name, def) in spec.definitions() {
        match def.category {
            AxiomCategory::FoundationalRule => stats.foundational += 1,
            AxiomCategory::HelperAxiom => stats.helper_axiom += 1,
            AxiomCategory::DerivedLemma => {
                stats.derived_total += 1;
                match def.proof_status {
                    ProofStatus::Axiom => stats.derived_axiom += 1,
                    ProofStatus::DerivedPending => {
                        stats.derived_pending += 1;
                        if library.get(name).is_some() {
                            stats.pending_with_proof += 1;
                        } else {
                            stats.pending_no_proof += 1;
                        }
                    }
                    ProofStatus::DerivedProved => stats.derived_proved += 1,
                }
            }
        }
    }

    stats
}

/// Result of a single promotion attempt.
#[derive(Debug, Clone)]
pub struct PromotionAttempt {
    /// Name of the definition.
    pub name: String,
    /// Original status before attempt.
    pub original_status: ProofStatus,
    /// New status after attempt.
    pub new_status: ProofStatus,
    /// Whether the status changed.
    pub promoted: bool,
    /// Axiom dependencies (empty if DerivedProved).
    pub axiom_deps: HashSet<String>,
    /// Error message if verification failed.
    pub error: Option<String>,
}

/// Summary of a full promotion run.
#[derive(Debug, Default)]
pub struct PromotionReport {
    /// Individual attempt results.
    pub attempts: Vec<PromotionAttempt>,
    /// Count of definitions promoted from DerivedPending to DerivedProved.
    pub promoted_count: usize,
    /// Count of definitions that remained DerivedPending (have axiom deps).
    pub still_pending_count: usize,
    /// Count of definitions with no matching proof in the library.
    pub no_proof_count: usize,
    /// Count of definitions whose proof failed verification.
    pub error_count: usize,
}

impl PromotionReport {
    /// Generate a human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        let total = self.attempts.len();
        format!(
            "Promotion Pipeline Report:\n\
             - Total DerivedPending candidates: {total}\n\
             - Promoted to DerivedProved: {}\n\
             - Still DerivedPending (axiom deps): {}\n\
             - No proof in library: {}\n\
             - Verification errors: {}",
            self.promoted_count, self.still_pending_count, self.no_proof_count, self.error_count,
        )
    }
}

/// Build a `PromotionAttempt` for one candidate by verifying its proof.
fn try_promote_candidate(
    name: &str,
    spec: &Specification,
    library: &ProofLibrary,
) -> PromotionAttempt {
    match library.get(name) {
        Some(proof) => match proof.verify_with_deps(spec) {
            Ok((status, deps)) => PromotionAttempt {
                name: name.to_string(),
                original_status: ProofStatus::DerivedPending,
                new_status: status,
                promoted: status == ProofStatus::DerivedProved,
                axiom_deps: deps,
                error: None,
            },
            Err(e) => PromotionAttempt {
                name: name.to_string(),
                original_status: ProofStatus::DerivedPending,
                new_status: ProofStatus::DerivedPending,
                promoted: false,
                axiom_deps: HashSet::new(),
                error: Some(e.to_string()),
            },
        },
        None => PromotionAttempt {
            name: name.to_string(),
            original_status: ProofStatus::DerivedPending,
            new_status: ProofStatus::DerivedPending,
            promoted: false,
            axiom_deps: HashSet::new(),
            error: None,
        },
    }
}

/// Apply a promotion attempt's results to the spec and report.
fn apply_attempt(
    attempt: &PromotionAttempt,
    spec: &mut Specification,
    report: &mut PromotionReport,
    has_proof: bool,
) {
    if attempt.promoted {
        report.promoted_count += 1;
        if let Some(def) = spec.definitions_mut().get_mut(&attempt.name) {
            def.proof_status = ProofStatus::DerivedProved;
            def.axiom_deps.clear();
        }
    } else if attempt.error.is_some() {
        report.error_count += 1;
    } else if !has_proof {
        report.no_proof_count += 1;
    } else {
        report.still_pending_count += 1;
        if !attempt.axiom_deps.is_empty() {
            if let Some(def) = spec.definitions_mut().get_mut(&attempt.name) {
                def.axiom_deps.clone_from(&attempt.axiom_deps);
            }
        }
    }
}

/// Run the promotion pipeline on all DerivedPending definitions.
///
/// The spec is mutated in-place for any promotions.
pub fn run_promotion(spec: &mut Specification, library: &ProofLibrary) -> PromotionReport {
    let mut report = PromotionReport::default();

    let candidates: Vec<String> = spec
        .definitions()
        .iter()
        .filter(|(_, d)| {
            d.category == AxiomCategory::DerivedLemma
                && d.proof_status == ProofStatus::DerivedPending
        })
        .map(|(name, _)| name.clone())
        .collect();

    for name in &candidates {
        let has_proof = library.get(name).is_some();
        let attempt = try_promote_candidate(name, spec, library);
        apply_attempt(&attempt, spec, &mut report, has_proof);
        report.attempts.push(attempt);
    }

    report.attempts.sort_by(|a, b| a.name.cmp(&b.name));
    report
}

/// Try to promote a single named definition.
///
/// Returns the attempt result. The spec is mutated if promotion succeeds.
///
/// # Errors
/// Returns `PromotionError` if the definition does not exist, is not a
/// DerivedLemma, has no proof, or if verification fails.
pub fn promote_single(
    spec: &mut Specification,
    library: &ProofLibrary,
    name: &str,
) -> Result<PromotionAttempt, PromotionError> {
    let def = spec
        .get_definition(name)
        .ok_or_else(|| PromotionError::UnknownDefinition(name.to_string()))?;

    if def.category != AxiomCategory::DerivedLemma {
        return Err(PromotionError::NotDerivedLemma {
            name: name.to_string(),
            category: format!("{:?}", def.category),
        });
    }

    if def.proof_status == ProofStatus::DerivedProved {
        return Ok(PromotionAttempt {
            name: name.to_string(),
            original_status: ProofStatus::DerivedProved,
            new_status: ProofStatus::DerivedProved,
            promoted: false,
            axiom_deps: HashSet::new(),
            error: None,
        });
    }

    let original_status = def.proof_status;

    let proof = library
        .get(name)
        .ok_or_else(|| PromotionError::NoProof(name.to_string()))?;

    let (status, deps) =
        proof
            .verify_with_deps(spec)
            .map_err(|e| PromotionError::VerificationFailed {
                name: name.to_string(),
                error: e.to_string(),
            })?;

    let promoted = status == ProofStatus::DerivedProved;

    if promoted {
        if let Some(def) = spec.definitions_mut().get_mut(name) {
            def.proof_status = ProofStatus::DerivedProved;
            def.axiom_deps.clear();
        }
    } else if !deps.is_empty() {
        if let Some(def) = spec.definitions_mut().get_mut(name) {
            def.axiom_deps.clone_from(&deps);
        }
    }

    Ok(PromotionAttempt {
        name: name.to_string(),
        original_status,
        new_status: status,
        promoted,
        axiom_deps: deps,
        error: None,
    })
}

/// Promote a single named definition using an externally provided proof term.
///
/// This is the primary entry point for the promotion pipeline: given a theorem
/// name and a proof term (Lean syntax string), validate that the proof term
/// type-checks against the definition's type signature, analyze its axiom
/// dependencies, and update the spec definition accordingly.
///
/// The proof term is constructed as a [`ProofTerm`] internally and verified
/// through the same kernel type-checking pipeline as library proofs.
///
/// # Errors
/// Returns `PromotionError` if the definition does not exist, is not a
/// DerivedLemma, or if the proof term fails verification.
pub fn promote_with_proof_term(
    spec: &mut Specification,
    name: &str,
    proof_term_src: &str,
) -> Result<PromotionAttempt, PromotionError> {
    let def = spec
        .get_definition(name)
        .ok_or_else(|| PromotionError::UnknownDefinition(name.to_string()))?;

    if def.category != AxiomCategory::DerivedLemma {
        return Err(PromotionError::NotDerivedLemma {
            name: name.to_string(),
            category: format!("{:?}", def.category),
        });
    }

    if def.proof_status == ProofStatus::DerivedProved {
        return Ok(PromotionAttempt {
            name: name.to_string(),
            original_status: ProofStatus::DerivedProved,
            new_status: ProofStatus::DerivedProved,
            promoted: false,
            axiom_deps: HashSet::new(),
            error: None,
        });
    }

    let original_status = def.proof_status;

    // Build a ProofTerm from the external proof source and verify it.
    let proof = super::ProofTerm::new(
        name,
        proof_term_src,
        "externally provided proof term via promotion pipeline",
    );

    let (status, deps) =
        proof
            .verify_with_deps(spec)
            .map_err(|e| PromotionError::VerificationFailed {
                name: name.to_string(),
                error: e.to_string(),
            })?;

    let promoted = status == ProofStatus::DerivedProved;

    if promoted {
        if let Some(def) = spec.definitions_mut().get_mut(name) {
            def.proof_status = ProofStatus::DerivedProved;
            def.value_src = Some(proof_term_src.to_string());
            def.axiom_deps.clear();
        }
    } else if !deps.is_empty() {
        if let Some(def) = spec.definitions_mut().get_mut(name) {
            def.axiom_deps.clone_from(&deps);
        }
    }

    Ok(PromotionAttempt {
        name: name.to_string(),
        original_status,
        new_status: status,
        promoted,
        axiom_deps: deps,
        error: None,
    })
}

/// Error during promotion.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum PromotionError {
    /// Definition not found in spec.
    #[error("Unknown definition: {0}")]
    UnknownDefinition(String),
    /// Definition is not a DerivedLemma.
    #[error("Definition {name} is {category}, not DerivedLemma")]
    NotDerivedLemma {
        /// Definition name.
        name: String,
        /// Actual category.
        category: String,
    },
    /// No proof exists in the library for this definition.
    #[error("No proof in library for: {0}")]
    NoProof(String),
    /// Proof verification failed.
    #[error("Verification failed for {name}: {error}")]
    VerificationFailed {
        /// Definition name.
        name: String,
        /// Verification error details.
        error: String,
    },
}
