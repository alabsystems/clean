// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust and quality helpers for kernel proof reconstruction acceptance.

use super::proof_reconstruct::ReconstructionResult;
#[cfg(test)]
use clean_kernel::Name;
use clean_kernel::{Expr, FVarId};

// Re-import canonical counter from the bridge trust module.
pub(crate) use crate::bridge::proof_trust::count_embedded_trusted_ay_terms;

/// Classification of a reconstructed proof's trust level.
///
/// Provides a structured signal for the tactic layer to distinguish
/// fully kernel-verified proofs from those requiring trusted axioms.
/// Named `ReconstructionQuality` to avoid collision with `ay_proof::ProofQuality`
/// which classifies ay's native proof step completeness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ReconstructionQuality {
    /// All steps kernel-reconstructed. No trustedAy axioms.
    FullyVerified,
    /// Some steps use trustedAy fallback. Count is exact.
    PartiallyTrusted { trust_count: usize },
}

impl ReconstructionQuality {
    pub fn from_trust_count(count: usize) -> Self {
        if count == 0 {
            Self::FullyVerified
        } else {
            Self::PartiallyTrusted { trust_count: count }
        }
    }

    pub fn is_fully_verified(&self) -> bool {
        matches!(self, Self::FullyVerified)
    }

    pub fn trust_count(&self) -> usize {
        match self {
            Self::FullyVerified => 0,
            Self::PartiallyTrusted { trust_count } => *trust_count,
        }
    }
}

/// Typed source classification for residual `trustedAy` sub-terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ResidualTrustSource {
    ArithmeticBoundary,
    AletheTrustStep,
    TheoryLemmaBvBitBlast,
    TheoryLemmaArrayAxiom,
    TheoryLemmaGeneric,
    LocalReconstructionGap,
}

/// Reachable residual trust carried by an accepted refutation candidate.
///
/// Fields are private to enforce that trust envelopes are only constructed
/// through the accepted reconstruction pipeline. Read-only accessors expose
/// the accounting data. Synthetic construction for cross-crate tests is
/// available through the `test-utils` feature gate on `ay_contract`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[must_use]
#[non_exhaustive]
pub struct ResidualTrustSummary {
    primary: Option<ResidualTrustSource>,
    arithmetic_boundary_steps: usize,
    alethe_trust_steps: usize,
    theory_bv_bitblast_steps: usize,
    theory_array_axiom_steps: usize,
    theory_generic_steps: usize,
    local_gap_steps: usize,
}

impl ResidualTrustSummary {
    /// Zero-value summary with no residual trust debt. Crate-internal
    /// replacement for the removed `Default` derive.
    pub(crate) fn empty() -> Self {
        Self {
            primary: None,
            arithmetic_boundary_steps: 0,
            alethe_trust_steps: 0,
            theory_bv_bitblast_steps: 0,
            theory_array_axiom_steps: 0,
            theory_generic_steps: 0,
            local_gap_steps: 0,
        }
    }

    pub fn primary(&self) -> Option<ResidualTrustSource> {
        self.primary
    }

    pub fn arithmetic_boundary_steps(&self) -> usize {
        self.arithmetic_boundary_steps
    }

    pub fn alethe_trust_steps(&self) -> usize {
        self.alethe_trust_steps
    }

    pub fn theory_bv_bitblast_steps(&self) -> usize {
        self.theory_bv_bitblast_steps
    }

    pub fn theory_array_axiom_steps(&self) -> usize {
        self.theory_array_axiom_steps
    }

    pub fn theory_generic_steps(&self) -> usize {
        self.theory_generic_steps
    }

    pub fn local_gap_steps(&self) -> usize {
        self.local_gap_steps
    }

    pub(crate) fn from_source(source: ResidualTrustSource) -> Self {
        let mut summary = Self::empty();
        summary.add_source(source);
        summary
    }

    pub(crate) fn add_source(&mut self, source: ResidualTrustSource) {
        match source {
            ResidualTrustSource::ArithmeticBoundary => self.arithmetic_boundary_steps += 1,
            ResidualTrustSource::AletheTrustStep => self.alethe_trust_steps += 1,
            ResidualTrustSource::TheoryLemmaBvBitBlast => self.theory_bv_bitblast_steps += 1,
            ResidualTrustSource::TheoryLemmaArrayAxiom => self.theory_array_axiom_steps += 1,
            ResidualTrustSource::TheoryLemmaGeneric => self.theory_generic_steps += 1,
            ResidualTrustSource::LocalReconstructionGap => self.local_gap_steps += 1,
        }
        self.primary = self.derive_primary();
    }

    pub(crate) fn merge(&mut self, other: Self) {
        self.arithmetic_boundary_steps += other.arithmetic_boundary_steps;
        self.alethe_trust_steps += other.alethe_trust_steps;
        self.theory_bv_bitblast_steps += other.theory_bv_bitblast_steps;
        self.theory_array_axiom_steps += other.theory_array_axiom_steps;
        self.theory_generic_steps += other.theory_generic_steps;
        self.local_gap_steps += other.local_gap_steps;
        self.primary = self.derive_primary();
    }

    pub fn total_steps(&self) -> usize {
        self.arithmetic_boundary_steps
            + self.alethe_trust_steps
            + self.theory_bv_bitblast_steps
            + self.theory_array_axiom_steps
            + self.theory_generic_steps
            + self.local_gap_steps
    }

    fn derive_primary(&self) -> Option<ResidualTrustSource> {
        if self.local_gap_steps > 0 {
            Some(ResidualTrustSource::LocalReconstructionGap)
        } else if self.arithmetic_boundary_steps > 0 {
            Some(ResidualTrustSource::ArithmeticBoundary)
        } else if self.alethe_trust_steps > 0 {
            Some(ResidualTrustSource::AletheTrustStep)
        } else if self.theory_bv_bitblast_steps > 0 {
            Some(ResidualTrustSource::TheoryLemmaBvBitBlast)
        } else if self.theory_array_axiom_steps > 0 {
            Some(ResidualTrustSource::TheoryLemmaArrayAxiom)
        } else if self.theory_generic_steps > 0 {
            Some(ResidualTrustSource::TheoryLemmaGeneric)
        } else {
            None
        }
    }
}

/// Configurable trust budget for proof acceptance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum TrustBudget {
    /// Accept any proof regardless of trust count (current behavior).
    Unlimited,
    /// Accept only fully kernel-verified proofs.
    ZeroTrust,
    /// Accept proofs with at most N trust sub-terms.
    AtMost(usize),
}

// count_embedded_trusted_ay_terms moved to crate::bridge::proof_trust
// and re-imported above via pub(crate) use.

/// Accepted raw ay proof reconstruction result.
///
/// The `refutation` is guaranteed to be closed (no compound witness FVars),
/// to derive the empty clause, and to carry a structured quality classification
/// computed from the exact embedded `trustedAy` count of the accepted term.
///
/// Fields are private to enforce that accepted candidates are only minted
/// by the reconstruction pipeline. Read-only accessors expose the data.
/// Synthetic construction for cross-crate tests is available through the
/// `test-utils` feature gate on `ay_contract`.
#[derive(Debug, Clone)]
#[must_use]
#[non_exhaustive]
pub struct KernelReconstructionCandidate {
    refutation: Expr,
    negated_goal_fvar: Option<FVarId>,
    quality: ReconstructionQuality,
    residual: ResidualTrustSummary,
}

impl KernelReconstructionCandidate {
    #[cfg(feature = "test-utils")]
    pub(crate) fn new(
        refutation: Expr,
        negated_goal_fvar: Option<FVarId>,
        quality: ReconstructionQuality,
        residual: ResidualTrustSummary,
    ) -> Self {
        Self {
            refutation,
            negated_goal_fvar,
            quality,
            residual,
        }
    }

    pub fn refutation(&self) -> &Expr {
        &self.refutation
    }

    pub fn negated_goal_fvar(&self) -> Option<FVarId> {
        self.negated_goal_fvar
    }

    pub fn quality(&self) -> ReconstructionQuality {
        self.quality
    }

    pub fn residual(&self) -> ResidualTrustSummary {
        self.residual
    }

    /// Consume the candidate into its constituent parts for downstream
    /// proof wrapping. Avoids cloning the refutation `Expr`.
    pub fn into_parts(
        self,
    ) -> (
        Expr,
        Option<FVarId>,
        ReconstructionQuality,
        ResidualTrustSummary,
    ) {
        (
            self.refutation,
            self.negated_goal_fvar,
            self.quality,
            self.residual,
        )
    }
}

pub(super) fn accept_kernel_reconstruction_candidate(
    raw: ReconstructionResult,
    budget: TrustBudget,
) -> Option<KernelReconstructionCandidate> {
    let ReconstructionResult {
        proof_term,
        negated_goal_fvar,
        compound_witness_fvars,
        derives_empty_clause,
        trust_subterm_count,
        residual,
        ..
    } = raw;

    if !compound_witness_fvars.is_empty() {
        tracing::debug!(
            count = compound_witness_fvars.len(),
            "rejecting raw reconstruction: compound witness FVars create open terms"
        );
        return None;
    }
    if !derives_empty_clause {
        tracing::debug!("rejecting raw reconstruction: proof does not derive empty clause");
        return None;
    }

    proof_term.and_then(|refutation| {
        let exact_trust_subterm_count = count_embedded_trusted_ay_terms(&refutation);
        if exact_trust_subterm_count > trust_subterm_count {
            tracing::warn!(
                trust_subterm_count,
                exact_trust_subterm_count,
                "accepted refutation contained more embedded trustedAy sub-terms than reconstruction reported"
            );
        } else if exact_trust_subterm_count != trust_subterm_count {
            tracing::debug!(
                trust_subterm_count,
                exact_trust_subterm_count,
                "accepted refutation pruned unreached trustedAy sub-terms from reconstruction stats"
            );
        } else if exact_trust_subterm_count > 0 {
            tracing::debug!(
                trust_subterm_count = exact_trust_subterm_count,
                "accepting partially-verified refutation with embedded trustedAy sub-terms"
            );
        }

        let residual_trust_count = residual.total_steps();
        if exact_trust_subterm_count != residual_trust_count {
            tracing::warn!(
                exact_trust_subterm_count,
                residual_trust_count,
                ?residual,
                "accepted refutation residual summary disagreed with embedded trustedAy recount"
            );
        }

        let quality = ReconstructionQuality::from_trust_count(exact_trust_subterm_count);
        let residual = if exact_trust_subterm_count == 0 {
            ResidualTrustSummary::empty()
        } else {
            residual
        };
        let within_budget = match budget {
            TrustBudget::Unlimited => true,
            TrustBudget::ZeroTrust => exact_trust_subterm_count == 0,
            TrustBudget::AtMost(max) => exact_trust_subterm_count <= max,
        };

        if !within_budget {
            tracing::debug!(
                trust_count = exact_trust_subterm_count,
                ?budget,
                "rejecting reconstruction: exceeds trust budget"
            );
            return None;
        }

        Some(KernelReconstructionCandidate {
            refutation,
            negated_goal_fvar,
            quality,
            residual,
        })
    })
}

#[cfg(test)]
mod tests;
