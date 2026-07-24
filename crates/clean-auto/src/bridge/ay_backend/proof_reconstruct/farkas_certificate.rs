// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reified Farkas certificate: owns clause-length validation, active indices,
//! and exact coefficients in a single local type.
//!
//! Eliminates the pattern where `theory_lemma.rs`, `theory_lemma_lra.rs`, and
//! `theory_lemma_lra_weighted.rs` each independently extract certificate
//! semantics from the raw `ProofTrace`.
//!
//! Part of #2854. Design: `designs/2026-03-18-smt-proof-reconstruction-reference-comparison.md`

use ay_core::{ProofId, TermId};
use num_rational::Rational64;

use super::trace::{FarkasView, ProofTrace};
use super::ReconstructionError;

/// A validated, self-contained Farkas certificate for a single theory lemma step.
///
/// Constructed once at dispatch time in `theory_lemma.rs` and passed down to
/// all LRA reconstruction modules. No downstream module needs `step_id` or
/// raw trace access for certificate meaning.
#[derive(Debug, Clone)]
pub(super) struct FarkasCertificate {
    /// Clause positions with non-zero Farkas coefficients.
    active_indices: Vec<usize>,
    /// Non-zero `(clause_idx, coefficient)` pairs, ordered by clause index.
    /// Same length as `active_indices`.
    active_coefficients: Vec<(usize, Rational64)>,
    /// Whether every active coefficient is exactly `1`.
    all_unit: bool,
}

impl FarkasCertificate {
    /// Build a certificate from a `FarkasView` summary and raw trace data.
    ///
    /// When `view` is `None` (ay omitted the annotation, common for `LiaGeneric`),
    /// synthesizes an all-unit certificate treating every clause literal as active.
    ///
    /// Validates clause length, coefficient validity, and semantic correctness
    /// at construction time so downstream consumers do not need to repeat these
    /// checks. Semantic validation calls `verify_farkas_conflict_lits_full`
    /// on the active subset before replay begins.
    pub(super) fn from_trace(
        view: Option<FarkasView>,
        clause: &[TermId],
        step_id: ProofId,
        trace: &ProofTrace<'_>,
    ) -> Result<Self, ReconstructionError> {
        match view {
            Some(fv) => Self::from_view(fv, clause, step_id, trace),
            None => Ok(Self::all_unit_fallback(clause.len())),
        }
    }

    /// Construct from an explicit `FarkasView` by extracting indices and
    /// coefficients from the trace, then semantically validating the active
    /// subset against `ay_core::proof_validation::verify_farkas_conflict_lits_full`.
    fn from_view(
        view: FarkasView,
        clause: &[TermId],
        step_id: ProofId,
        trace: &ProofTrace<'_>,
    ) -> Result<Self, ReconstructionError> {
        let clause_len = clause.len();
        if view.coefficient_count != clause_len {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!(
                    "Farkas certificate length {} != clause length {}",
                    view.coefficient_count, clause_len
                ),
            });
        }
        if !view.is_valid {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "Farkas certificate has negative coefficients".to_string(),
            });
        }

        // Extract active indices and coefficients from the trace in one pass
        // (or two calls that each do one pass over the raw proof step).
        let active_indices = trace
            .farkas_active_clause_indices(step_id)
            .unwrap_or_else(|| (0..clause_len).collect());

        let active_coefficients = trace
            .farkas_active_coefficients(step_id)
            .unwrap_or_else(|| {
                (0..clause_len)
                    .map(|i| (i, Rational64::from_integer(1)))
                    .collect()
            });

        // `all_unit` is about the replay-relevant active subset, not the raw
        // annotation tail. Zero coefficients are intentionally ignored by the
        // bridge, so `[1, 0, 1]` should still stay on the unweighted lane.
        let all_unit = active_coefficients
            .iter()
            .all(|&(_, coeff)| coeff == Rational64::from_integer(1));

        let cert = Self {
            active_indices,
            all_unit,
            active_coefficients,
        };

        // Semantic validation: build conflict literals from the active subset
        // and verify via ay-core's Farkas checker. This gates replay entry.
        cert.validate_semantics(clause, step_id, trace)?;

        Ok(cert)
    }

    /// Validate the active certificate subset semantically using ay-core's
    /// `verify_farkas_conflict_lits_full`.
    fn validate_semantics(
        &self,
        clause: &[TermId],
        step_id: ProofId,
        trace: &ProofTrace<'_>,
    ) -> Result<(), ReconstructionError> {
        trace.validate_farkas_active_conflict(clause, step_id, &self.active_coefficients)
    }

    /// Synthesize an all-unit certificate for when ay omits the annotation.
    ///
    /// Every clause literal is active with coefficient 1. This is the common
    /// fallback for `LiaGeneric` lemmas.
    fn all_unit_fallback(clause_len: usize) -> Self {
        Self {
            active_indices: (0..clause_len).collect(),
            active_coefficients: (0..clause_len)
                .map(|i| (i, Rational64::from_integer(1)))
                .collect(),
            all_unit: true,
        }
    }

    /// Active clause positions (non-zero coefficient).
    pub(super) fn active_indices(&self) -> &[usize] {
        &self.active_indices
    }

    /// Whether every active coefficient is exactly 1.
    pub(super) fn all_unit(&self) -> bool {
        self.all_unit
    }

    /// Look up the coefficient for a given clause index.
    ///
    /// O(n) scan over active coefficients. Acceptable because active sets are
    /// typically small (≤10 bounds).
    pub(super) fn coefficient_for(&self, clause_idx: usize) -> Option<Rational64> {
        self.active_coefficients
            .iter()
            .find(|&&(idx, _)| idx == clause_idx)
            .map(|&(_, coeff)| coeff)
    }
}
