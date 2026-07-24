// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust-ledger storage and accounting helpers for `ProofState`.

use super::ProofState;
use clean_auto::bridge::ay_contract::ResidualTrustSummary;

/// Per-proof trust usage accumulated while tactics execute.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TrustedAyProvenanceLedger {
    /// trustedAy sub-terms caused by arithmetic-boundary residual debt.
    pub arithmetic_boundary_steps: u32,
    /// trustedAy sub-terms caused by Alethe `trust` steps.
    pub alethe_trust_steps: u32,
    /// trustedAy sub-terms caused by bitblast theory-lemma residues.
    pub theory_bv_bitblast_steps: u32,
    /// trustedAy sub-terms caused by array-axiom theory-lemma residues.
    pub theory_array_axiom_steps: u32,
    /// trustedAy sub-terms caused by generic theory-lemma residues.
    pub theory_generic_steps: u32,
    /// trustedAy sub-terms caused by local reconstruction gaps.
    pub local_gap_steps: u32,
    /// trustedAy sub-terms whose exact residual source is unavailable.
    pub unclassified_steps: u32,
}

impl TrustedAyProvenanceLedger {
    /// Total number of typed trustedAy steps with a residual source.
    pub fn typed_total(self) -> u32 {
        self.arithmetic_boundary_steps
            .saturating_add(self.alethe_trust_steps)
            .saturating_add(self.theory_bv_bitblast_steps)
            .saturating_add(self.theory_array_axiom_steps)
            .saturating_add(self.theory_generic_steps)
            .saturating_add(self.local_gap_steps)
    }

    fn total_steps(self) -> u32 {
        self.typed_total().saturating_add(self.unclassified_steps)
    }

    fn record_unclassified(&mut self, count: u32) {
        self.unclassified_steps = self.unclassified_steps.saturating_add(count);
    }

    fn record_residual(&mut self, count: u32, residual: ResidualTrustSummary) {
        let arithmetic_boundary_steps =
            saturating_residual_count(residual.arithmetic_boundary_steps(), "arithmetic_boundary");
        let alethe_trust_steps =
            saturating_residual_count(residual.alethe_trust_steps(), "alethe_trust");
        let theory_bv_bitblast_steps =
            saturating_residual_count(residual.theory_bv_bitblast_steps(), "theory_bv_bitblast");
        let theory_array_axiom_steps =
            saturating_residual_count(residual.theory_array_axiom_steps(), "theory_array_axiom");
        let theory_generic_steps =
            saturating_residual_count(residual.theory_generic_steps(), "theory_generic");
        let local_gap_steps = saturating_residual_count(residual.local_gap_steps(), "local_gap");
        let typed_total = arithmetic_boundary_steps
            .saturating_add(alethe_trust_steps)
            .saturating_add(theory_bv_bitblast_steps)
            .saturating_add(theory_array_axiom_steps)
            .saturating_add(theory_generic_steps)
            .saturating_add(local_gap_steps);

        if typed_total > count {
            tracing::warn!(
                count,
                typed_total,
                ?residual,
                "accepted residual summary exceeded embedded trustedAy recount; preserving debt as unclassified"
            );
            self.record_unclassified(count);
            return;
        }

        self.arithmetic_boundary_steps = self
            .arithmetic_boundary_steps
            .saturating_add(arithmetic_boundary_steps);
        self.alethe_trust_steps = self.alethe_trust_steps.saturating_add(alethe_trust_steps);
        self.theory_bv_bitblast_steps = self
            .theory_bv_bitblast_steps
            .saturating_add(theory_bv_bitblast_steps);
        self.theory_array_axiom_steps = self
            .theory_array_axiom_steps
            .saturating_add(theory_array_axiom_steps);
        self.theory_generic_steps = self
            .theory_generic_steps
            .saturating_add(theory_generic_steps);
        self.local_gap_steps = self.local_gap_steps.saturating_add(local_gap_steps);
        self.unclassified_steps = self
            .unclassified_steps
            .saturating_add(count.saturating_sub(typed_total));
    }
}

/// Coarse per-proof provenance for `trustedArith` debt.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TrustedArithProvenanceLedger {
    /// `trustedArith` steps recorded directly at a runtime callsite.
    pub direct_steps: u32,
    /// `trustedArith` steps recorded through `close_with_trusted_arith(...)`.
    pub goal_close_helper_steps: u32,
    /// `trustedArith` steps recorded through target-rewrite helper fallbacks.
    pub target_rewrite_helper_steps: u32,
    /// `trustedArith` steps whose source category is unavailable.
    pub unclassified_steps: u32,
}

impl TrustedArithProvenanceLedger {
    /// Total number of typed `trustedArith` steps with a coarse source class.
    pub fn typed_total(self) -> u32 {
        self.direct_steps
            .saturating_add(self.goal_close_helper_steps)
            .saturating_add(self.target_rewrite_helper_steps)
    }

    fn total_steps(self) -> u32 {
        self.typed_total().saturating_add(self.unclassified_steps)
    }

    #[cfg(test)]
    fn record_direct(&mut self, count: u32) {
        self.direct_steps = self.direct_steps.saturating_add(count);
    }

    #[cfg(test)]
    fn record_goal_close_helper(&mut self, count: u32) {
        self.goal_close_helper_steps = self.goal_close_helper_steps.saturating_add(count);
    }

    #[cfg(test)]
    fn record_target_rewrite_helper(&mut self, count: u32) {
        self.target_rewrite_helper_steps = self.target_rewrite_helper_steps.saturating_add(count);
    }

    #[cfg(test)]
    fn record_unclassified(&mut self, count: u32) {
        self.unclassified_steps = self.unclassified_steps.saturating_add(count);
    }
}

fn saturating_residual_count(count: usize, category: &'static str) -> u32 {
    match u32::try_from(count) {
        Ok(count) => count,
        Err(_) => {
            tracing::warn!(
                category,
                count,
                "residual trustedAy count exceeded u32 range; saturating ledger accounting"
            );
            u32::MAX
        }
    }
}

/// Request-local accounting for SMT proof candidates that failed kernel
/// validation before a recovery lane produced a clean proof.
///
/// These counts are *not* accepted trust debt — they track how many invalid
/// candidates the selector rejected during a single tactic request.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SmtRecoveryLedger {
    /// Direct ay proof candidates that failed `validate_proof_term` before selection.
    pub invalid_direct_ay_candidates: u32,
    /// Direct certificate proof candidates that failed `validate_proof_term` before selection.
    pub invalid_direct_certificate_candidates: u32,
    /// Bridge-produced proof candidates that failed `validate_proof_term`.
    pub invalid_bridge_candidates: u32,
}

impl SmtRecoveryLedger {
    /// True when any recovery event was recorded.
    pub fn has_events(self) -> bool {
        self.invalid_direct_ay_candidates > 0
            || self.invalid_direct_certificate_candidates > 0
            || self.invalid_bridge_candidates > 0
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ProofTrustLedger {
    /// Number of explicit `sorry` / `admit` fallbacks in this proof state.
    pub sorry_count: u32,
    /// Number of `trustedAy` fallbacks in this proof state.
    pub trusted_ay_count: u32,
    /// Typed provenance for accepted `trustedAy` sub-terms.
    pub trusted_ay_provenance: TrustedAyProvenanceLedger,
    /// Number of `trustedArith` fallbacks in this proof state.
    pub trusted_arith_count: u32,
    /// Typed provenance for `trustedArith` debt.
    pub trusted_arith_provenance: TrustedArithProvenanceLedger,
    /// Request-local recovery events for invalid SMT proof candidates.
    pub smt_recovery: SmtRecoveryLedger,
}

impl ProofTrustLedger {
    /// Total number of trusted fallback sites recorded on this proof state.
    pub fn trusted_axiom_count(self) -> u32 {
        self.sorry_count
            .saturating_add(self.trusted_ay_count)
            .saturating_add(self.trusted_arith_count)
    }

    pub(super) fn assert_invariants(self) {
        debug_assert_eq!(
            self.trusted_ay_count,
            self.trusted_ay_provenance.total_steps(),
            "trustedAy total count must match typed + unclassified provenance"
        );
        debug_assert_eq!(
            self.trusted_arith_count,
            self.trusted_arith_provenance.total_steps(),
            "trustedArith total count must match typed + unclassified provenance"
        );
    }

    /// Replace this ledger with the concrete branch that actually proved the goal.
    pub(crate) fn adopt_branch(&mut self, branch: &ProofTrustLedger) {
        *self = *branch;
        self.assert_invariants();
    }

    pub(crate) fn record_trusted_ay_unclassified(&mut self, count: u32) {
        let before = self.trusted_ay_provenance.total_steps();
        self.trusted_ay_provenance.record_unclassified(count);
        let after = self.trusted_ay_provenance.total_steps();
        debug_assert_eq!(
            after,
            before.saturating_add(count),
            "unclassified trustedAy recording must preserve the exact embedded count"
        );
        self.trusted_ay_count = after;
        self.assert_invariants();
    }

    pub(crate) fn record_trusted_ay_residual(
        &mut self,
        count: u32,
        residual: ResidualTrustSummary,
    ) {
        let before = self.trusted_ay_provenance.total_steps();
        self.trusted_ay_provenance.record_residual(count, residual);
        let after = self.trusted_ay_provenance.total_steps();
        debug_assert_eq!(
            after,
            before.saturating_add(count),
            "residual trustedAy recording must preserve the exact embedded count"
        );
        self.trusted_ay_count = after;
        self.assert_invariants();
    }

    #[cfg(test)]
    fn record_trusted_arith_with(
        &mut self,
        count: u32,
        record: impl FnOnce(&mut TrustedArithProvenanceLedger, u32),
        label: &'static str,
    ) {
        let before = self.trusted_arith_provenance.total_steps();
        record(&mut self.trusted_arith_provenance, count);
        let after = self.trusted_arith_provenance.total_steps();
        debug_assert_eq!(
            after,
            before.saturating_add(count),
            "{label} trustedArith recording must preserve the exact embedded count"
        );
        self.trusted_arith_count = after;
        self.assert_invariants();
    }

    #[cfg(test)]
    pub(crate) fn record_trusted_arith_direct(&mut self, count: u32) {
        self.record_trusted_arith_with(
            count,
            TrustedArithProvenanceLedger::record_direct,
            "direct",
        );
    }

    #[cfg(test)]
    pub(crate) fn record_trusted_arith_goal_close_helper(&mut self, count: u32) {
        self.record_trusted_arith_with(
            count,
            TrustedArithProvenanceLedger::record_goal_close_helper,
            "goal-close helper",
        );
    }

    #[cfg(test)]
    pub(crate) fn record_trusted_arith_target_rewrite_helper(&mut self, count: u32) {
        self.record_trusted_arith_with(
            count,
            TrustedArithProvenanceLedger::record_target_rewrite_helper,
            "target-rewrite helper",
        );
    }

    #[cfg(test)]
    pub(crate) fn record_trusted_arith_unclassified(&mut self, count: u32) {
        self.record_trusted_arith_with(
            count,
            TrustedArithProvenanceLedger::record_unclassified,
            "unclassified",
        );
    }
}

impl ProofState {
    /// Record that this proof used an explicit `sorry` / `admit`.
    pub(crate) fn record_sorry(&mut self) {
        self.trust_ledger.sorry_count = self.trust_ledger.sorry_count.saturating_add(1);
    }

    /// Record that this proof used a `trustedAy` fallback.
    #[cfg(test)]
    pub(crate) fn record_trusted_ay(&mut self) {
        self.record_trusted_ay_unclassified(1);
    }

    /// Record count-only `trustedAy` debt whose residual source is unknown.
    pub(crate) fn record_trusted_ay_unclassified(&mut self, count: u32) {
        self.trust_ledger.record_trusted_ay_unclassified(count);
    }

    /// Record accepted `trustedAy` debt together with its typed residual source.
    pub(crate) fn record_trusted_ay_residual(
        &mut self,
        count: u32,
        residual: ResidualTrustSummary,
    ) {
        self.trust_ledger
            .record_trusted_ay_residual(count, residual);
    }

    /// Record a `trustedArith` fallback at a direct runtime callsite.
    #[cfg(test)]
    pub(crate) fn record_trusted_arith_direct(&mut self, count: u32) {
        self.trust_ledger.record_trusted_arith_direct(count);
    }

    /// Record a `trustedArith` fallback through the goal-closing helper path.
    #[cfg(test)]
    pub(crate) fn record_trusted_arith_goal_close_helper(&mut self, count: u32) {
        self.trust_ledger
            .record_trusted_arith_goal_close_helper(count);
    }

    /// Record a `trustedArith` fallback through the target-rewrite helper path.
    #[cfg(test)]
    pub(crate) fn record_trusted_arith_target_rewrite_helper(&mut self, count: u32) {
        self.trust_ledger
            .record_trusted_arith_target_rewrite_helper(count);
    }

    /// Record count-only `trustedArith` debt whose source category is unknown.
    #[cfg(test)]
    pub(crate) fn record_trusted_arith_unclassified(&mut self, count: u32) {
        self.trust_ledger.record_trusted_arith_unclassified(count);
    }

    /// Record that this proof used a legacy `trustedArith` fallback.
    #[cfg(test)]
    pub(crate) fn record_trusted_arith(&mut self) {
        self.record_trusted_arith_unclassified(1);
    }

    /// Record that a direct ay proof candidate failed kernel validation before selection.
    #[cfg(feature = "ay-smt")]
    pub(crate) fn record_invalid_direct_ay_candidate(&mut self) {
        self.trust_ledger.smt_recovery.invalid_direct_ay_candidates = self
            .trust_ledger
            .smt_recovery
            .invalid_direct_ay_candidates
            .saturating_add(1);
    }

    /// Record that a direct certificate proof candidate failed kernel validation before selection.
    pub(crate) fn record_invalid_direct_certificate_candidate(&mut self) {
        self.trust_ledger
            .smt_recovery
            .invalid_direct_certificate_candidates = self
            .trust_ledger
            .smt_recovery
            .invalid_direct_certificate_candidates
            .saturating_add(1);
    }

    /// Record that a bridge-produced proof candidate failed kernel validation.
    pub(crate) fn record_invalid_bridge_candidate(&mut self) {
        self.trust_ledger.smt_recovery.invalid_bridge_candidates = self
            .trust_ledger
            .smt_recovery
            .invalid_bridge_candidates
            .saturating_add(1);
    }

    /// Return the typed trust ledger for this proof state.
    pub fn trust_ledger(&self) -> ProofTrustLedger {
        self.trust_ledger
    }

    /// Replace the current trust ledger with externally reconstructed accounting.
    pub fn set_trust_ledger(&mut self, ledger: ProofTrustLedger) {
        ledger.assert_invariants();
        self.trust_ledger = ledger;
    }

    /// Number of goals closed with trusted axioms in this proof state.
    /// Part of #2411.
    ///
    /// ENSURES: Returns 0 for fresh proof states (no trusted axioms used)
    pub fn trusted_axiom_count(&self) -> u32 {
        self.trust_ledger.trusted_axiom_count()
    }
}
