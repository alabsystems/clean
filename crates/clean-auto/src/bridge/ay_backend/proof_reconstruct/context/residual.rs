// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use ay_core::ProofId;
use clean_kernel::Expr;

use super::super::trace::{RuleView, StepView, TheoryLemmaView};
use super::{ReconstructionContext, ReconstructionError, ReconstructionResult};
use crate::bridge::ay_backend::reconstruction_quality::{
    ResidualTrustSource, ResidualTrustSummary,
};

impl<'a> ReconstructionContext<'a> {
    fn get_premise_residual(
        &self,
        premise: ProofId,
        from_step: ProofId,
    ) -> Result<ResidualTrustSummary, ReconstructionError> {
        self.step_residual_cache
            .get(premise.0 as usize)
            .and_then(|summary| *summary)
            .ok_or(ReconstructionError::InvalidPremise {
                premise: premise.0,
                from_step: from_step.0,
            })
    }

    fn derive_successful_step_residual(
        &self,
        step: StepView<'a>,
        step_id: ProofId,
    ) -> Result<ResidualTrustSummary, ReconstructionError> {
        match step {
            StepView::Assume(_) => Ok(ResidualTrustSummary::empty()),
            StepView::Resolution {
                clause1, clause2, ..
            } => {
                let mut summary = self.get_premise_residual(clause1, step_id)?;
                summary.merge(self.get_premise_residual(clause2, step_id)?);
                Ok(summary)
            }
            StepView::TheoryLemma { kind, .. } => Ok(match kind {
                TheoryLemmaView::BvBitBlast => {
                    ResidualTrustSummary::from_source(ResidualTrustSource::TheoryLemmaBvBitBlast)
                }
                TheoryLemmaView::ArrayAxiom => {
                    ResidualTrustSummary::from_source(ResidualTrustSource::TheoryLemmaArrayAxiom)
                }
                TheoryLemmaView::Generic => {
                    ResidualTrustSummary::from_source(ResidualTrustSource::TheoryLemmaGeneric)
                }
                // Kernel-reconstructed theory lemmas — genuinely zero trust.
                TheoryLemmaView::EufTransitive
                | TheoryLemmaView::EufCongruent
                | TheoryLemmaView::EufCongruentPred
                | TheoryLemmaView::LraFarkas
                | TheoryLemmaView::LiaGeneric => ResidualTrustSummary::empty(),
                // Catch-all for unrecognized theory lemma kinds — conservatively
                // mark as generic theory trust rather than zero trust. If this
                // branch runs for a successful step, the theory lemma was not
                // kernel-reconstructed, so empty() would undercount trust.
                TheoryLemmaView::Other => {
                    ResidualTrustSummary::from_source(ResidualTrustSource::TheoryLemmaGeneric)
                }
            }),
            StepView::Step { rule, premises, .. } => match rule {
                RuleView::Trust => Ok(ResidualTrustSummary::from_source(
                    ResidualTrustSource::AletheTrustStep,
                )),
                RuleView::Or => premises.first().copied().map_or_else(
                    || {
                        Err(ReconstructionError::UnsupportedStep {
                            step_index: step_id.0,
                            description: "Or rule missing premise residual".to_string(),
                        })
                    },
                    |premise| self.get_premise_residual(premise, step_id),
                ),
                RuleView::ThResolution => {
                    let mut summary = ResidualTrustSummary::empty();
                    for &premise in premises {
                        summary.merge(self.get_premise_residual(premise, step_id)?);
                    }
                    Ok(summary)
                }
                // Rules reconstructing to kernel primitives with no theory
                // call — genuinely zero trust.
                RuleView::OrPos
                | RuleView::OrNeg
                | RuleView::EquivPos1
                | RuleView::EquivPos2
                | RuleView::EquivNeg1
                | RuleView::EquivNeg2
                | RuleView::XorPos1
                | RuleView::XorPos2
                | RuleView::XorNeg1
                | RuleView::XorNeg2
                | RuleView::AndPos(_)
                | RuleView::AndNeg
                | RuleView::True
                | RuleView::False
                | RuleView::EqReflexive
                | RuleView::EqCongruent => Ok(ResidualTrustSummary::empty()),
                // symm / trans / cong / resolution compose premise proofs with
                // kernel primitives — zero LOCAL trust; inherit premise residuals.
                RuleView::Symm | RuleView::Trans | RuleView::Cong | RuleView::Resolution => {
                    let mut summary = ResidualTrustSummary::empty();
                    for &premise in premises {
                        summary.merge(self.get_premise_residual(premise, step_id)?);
                    }
                    Ok(summary)
                }
                // contraction propagates its single premise's residual.
                RuleView::Contraction => premises.first().copied().map_or_else(
                    || {
                        Err(ReconstructionError::UnsupportedStep {
                            step_index: step_id.0,
                            description: "Contraction rule missing premise residual".to_string(),
                        })
                    },
                    |premise| self.get_premise_residual(premise, step_id),
                ),
                RuleView::Hole | RuleView::Other => Ok(ResidualTrustSummary::from_source(
                    ResidualTrustSource::LocalReconstructionGap,
                )),
            },
            StepView::Anchor | StepView::Unknown => Ok(ResidualTrustSummary::empty()),
        }
    }

    pub(super) fn record_successful_step(&mut self, idx: usize, proof_id: ProofId, expr: Expr) {
        self.step_cache[idx] = Some(expr);
        self.stats.reconstructed_steps += 1;
        let residual = self
            .derive_successful_step_residual(self.trace().step(idx), proof_id)
            .unwrap_or_else(|error| {
                tracing::warn!(
                    step = idx,
                    %error,
                    "failed to derive residual trust summary for reconstructed step"
                );
                // Conservative: if we can't derive the trust composition from
                // premises, mark as local gap rather than zero trust. The
                // physical recount in accept_kernel_reconstruction_candidate
                // will catch any real trust subterms, but the residual
                // breakdown should not claim "clean" when derivation failed.
                ResidualTrustSummary::from_source(ResidualTrustSource::LocalReconstructionGap)
            });
        self.step_residual_cache[idx] = Some(residual);
    }

    pub(super) fn record_failed_step(&mut self, idx: usize, error: ReconstructionError) {
        // Emit opt-in audit record for TrustBoundary hits (#2875).
        if let ReconstructionError::TrustBoundary {
            step_index,
            subsystem,
            description,
        } = &error
        {
            crate::bridge::proof_trust::append_trust_boundary_audit_record(
                &crate::bridge::proof_trust::TrustBoundaryAuditRecord {
                    lane: "proof_reconstruct",
                    crate_name: "clean-auto",
                    test_name: std::thread::current()
                        .name()
                        .unwrap_or("unknown")
                        .to_string(),
                    tactic: None,
                    proof_kind: None,
                    subsystem: Some(subsystem.to_string()),
                    description: Some(description.clone()),
                    step_index: Some(*step_index),
                    arithmetic_boundary_steps: 1,
                    local_gap_steps: 0,
                    trust_subterm_count: 0,
                },
            );
        }

        let source = if matches!(&error, ReconstructionError::TrustBoundary { .. }) {
            self.stats.trust_boundary_steps += 1;
            ResidualTrustSource::ArithmeticBoundary
        } else {
            ResidualTrustSource::LocalReconstructionGap
        };
        self.stats.record_residual_source(source);
        self.stats.record_step_error(idx as u32, error);
        self.stats.trust_fallback_steps += 1;

        if let Some(trust_proof) = self.synthesize_trust_subterm_for_step(idx) {
            self.step_cache[idx] = Some(trust_proof);
            self.stats.trust_subterm_steps += 1;
            self.step_residual_cache[idx] = Some(ResidualTrustSummary::from_source(source));
        }
    }

    pub(super) fn finish_reconstruction(
        &mut self,
        root_idx: Option<usize>,
    ) -> ReconstructionResult {
        let final_idx = root_idx.or_else(|| self.step_cache.len().checked_sub(1));
        let derives_empty_clause = root_idx
            .map(|idx| self.trace().step_derives_empty_clause(idx))
            .unwrap_or(false);
        // When no steps were genuinely reconstructed (all failed), force
        // proof_term to None even if trust-carrying inserted subterms into
        // step_cache. A proof consisting entirely of trust subterms is
        // vacuous and should not be returned as a valid proof term. (#2986)
        let final_proof = if self.stats.reconstructed_steps == 0 {
            None
        } else {
            final_idx.and_then(|idx| self.step_cache[idx].clone())
        };
        if !derives_empty_clause && final_proof.is_some() {
            let err = ReconstructionError::NoContradiction {
                literal_count: final_idx
                    .map(|idx| self.trace().clause_of_step(idx).len())
                    .unwrap_or(0),
            };
            self.stats.record_proof_error(err);
        }

        let trust_subterm_count = self.stats.trust_subterm_steps;
        let residual = if let Some(last_idx) = final_idx {
            if final_proof.is_some() {
                self.step_residual_cache
                    .get(last_idx)
                    .and_then(|summary| *summary)
                    .unwrap_or_else(|| {
                        tracing::warn!(
                            step = last_idx,
                            "final reconstructed proof was missing residual trust summary"
                        );
                        // Conservative: missing residual for a proof that
                        // exists means we can't determine trust composition.
                        // Mark as local gap rather than zero trust so the
                        // selection layer doesn't treat this as fully clean.
                        ResidualTrustSummary::from_source(
                            ResidualTrustSource::LocalReconstructionGap,
                        )
                    })
            } else {
                ResidualTrustSummary::empty()
            }
        } else {
            ResidualTrustSummary::empty()
        };
        ReconstructionResult {
            proof_term: final_proof,
            negated_goal_fvar: self.negated_goal_proof.as_ref().map(|(id, _)| *id),
            compound_witness_fvars: std::mem::take(&mut self.compound_witnesses),
            derives_empty_clause,
            trust_subterm_count,
            residual,
            stats: std::mem::take(&mut self.stats),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::trace::{RuleView, StepView, TheoryLemmaView};
    use super::super::ReconstructionContext;
    use crate::bridge::ay_backend::proof_reconstruct::VariableMapping;
    use crate::bridge::ay_backend::reconstruction_quality::{
        ResidualTrustSource, ResidualTrustSummary,
    };
    use ay_core::{AletheRule, Proof, ProofId, TermStore};
    use clean_kernel::Expr;

    // --- Site 1: TheoryLemmaView::Other → TheoryLemmaGeneric ---

    #[test]
    fn test_theory_lemma_other_returns_theory_lemma_generic() {
        let terms = TermStore::new();
        let var_map = VariableMapping::new();
        let ctx = ReconstructionContext::new(&terms, &var_map, 1);
        let step = StepView::TheoryLemma {
            theory: "unknown",
            clause: &[],
            farkas: None,
            kind: TheoryLemmaView::Other,
            lia: None,
        };
        let result = ctx
            .derive_successful_step_residual(step, ProofId(0))
            .expect("TheoryLemmaView::Other should produce a residual, not an error");
        assert_eq!(
            result,
            ResidualTrustSummary::from_source(ResidualTrustSource::TheoryLemmaGeneric),
            "unrecognized theory lemma kind should conservatively mark as TheoryLemmaGeneric"
        );
    }

    // --- Site 2: RuleView::Hole | RuleView::Other → LocalReconstructionGap ---

    #[test]
    fn test_rule_hole_returns_local_reconstruction_gap() {
        let terms = TermStore::new();
        let var_map = VariableMapping::new();
        let ctx = ReconstructionContext::new(&terms, &var_map, 1);
        let step = StepView::Step {
            rule: RuleView::Hole,
            rule_name: "hole",
            clause: &[],
            premises: &[],
            args: &[],
        };
        let result = ctx
            .derive_successful_step_residual(step, ProofId(0))
            .expect("RuleView::Hole should produce a residual, not an error");
        assert_eq!(
            result,
            ResidualTrustSummary::from_source(ResidualTrustSource::LocalReconstructionGap),
            "Hole rule should conservatively mark as LocalReconstructionGap"
        );
    }

    #[test]
    fn test_rule_other_returns_local_reconstruction_gap() {
        let terms = TermStore::new();
        let var_map = VariableMapping::new();
        let ctx = ReconstructionContext::new(&terms, &var_map, 1);
        let step = StepView::Step {
            rule: RuleView::Other,
            rule_name: "unknown_rule",
            clause: &[],
            premises: &[],
            args: &[],
        };
        let result = ctx
            .derive_successful_step_residual(step, ProofId(0))
            .expect("RuleView::Other should produce a residual, not an error");
        assert_eq!(
            result,
            ResidualTrustSummary::from_source(ResidualTrustSource::LocalReconstructionGap),
            "unrecognized rule should conservatively mark as LocalReconstructionGap"
        );
    }

    // --- Site 3: record_successful_step fallback on derivation error ---

    #[test]
    fn test_record_successful_step_falls_back_to_local_gap_on_premise_miss() {
        let terms = TermStore::new();
        let var_map = VariableMapping::new();
        // Build a proof with a single Or step whose premise (ProofId(99))
        // has no cached residual — triggers the unwrap_or_else fallback.
        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::Or, vec![], vec![ProofId(99)], vec![]);
        let mut ctx = ReconstructionContext::with_proof(&proof, &terms, &var_map);
        ctx.record_successful_step(0, ProofId(0), Expr::prop());
        let result = ctx.finish_reconstruction(Some(0));
        assert_eq!(
            result.residual,
            ResidualTrustSummary::from_source(ResidualTrustSource::LocalReconstructionGap),
            "Or step with uncached premise residual should fall back to LocalReconstructionGap"
        );
    }

    // --- Site 4: finish_reconstruction missing final residual ---

    #[test]
    fn test_finish_reconstruction_missing_residual_returns_local_gap() {
        let terms = TermStore::new();
        let var_map = VariableMapping::new();
        let mut ctx = ReconstructionContext::new(&terms, &var_map, 1);
        // Set step_cache directly without going through record_successful_step,
        // so step_residual_cache[0] stays None. Must also set reconstructed_steps
        // > 0 so finish_reconstruction doesn't force proof_term to None (#2986).
        ctx.step_cache[0] = Some(Expr::prop());
        ctx.stats.reconstructed_steps = 1;
        let result = ctx.finish_reconstruction(Some(0));
        assert_eq!(
            result.residual,
            ResidualTrustSummary::from_source(ResidualTrustSource::LocalReconstructionGap),
            "final proof with missing cached residual should conservatively return LocalReconstructionGap"
        );
    }
}
