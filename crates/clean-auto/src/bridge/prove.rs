// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Top-level SMT prove method for SmtBridge.

use super::result::{ProofMethod, SmtProofResult, SmtVerificationResult};
use super::{BridgeError, BridgeResult, LogicalForm, SmtBridge};
use crate::smt::{SmtResult, TermId};
use clean_kernel::{Expr, ExprKind};

/// Equality goal terms captured during classification for proof reconstruction.
type EqGoalTerms = (TermId, TermId, Expr, Expr, Expr);

/// Maximum number of distinct lossy expressions to preview in an Unknown reason.
const LOSSY_PREVIEW_LIMIT: usize = 3;

impl<'env> SmtBridge<'env> {
    fn lossy_unknown(&self, prefix: &str) -> SmtVerificationResult {
        debug_assert!(
            !self.lossy_atoms.is_empty(),
            "lossy_unknown requires recorded lossy expressions"
        );
        SmtVerificationResult::Unknown(self.format_lossy_unknown_reason(prefix))
    }

    fn format_lossy_unknown_reason(&self, prefix: &str) -> String {
        let total = self.lossy_atoms.len();
        let mut distinct_summaries = Vec::new();

        for expr in &self.lossy_atoms {
            let summary = Self::summarize_lossy_expr(expr);
            if distinct_summaries.contains(&summary) {
                continue;
            }
            distinct_summaries.push(summary);
        }

        let preview = distinct_summaries
            .iter()
            .take(LOSSY_PREVIEW_LIMIT)
            .copied()
            .collect::<Vec<_>>()
            .join(", ");
        let omitted = distinct_summaries.len().saturating_sub(LOSSY_PREVIEW_LIMIT);
        let noun = if total == 1 {
            "expression"
        } else {
            "expressions"
        };

        if omitted == 0 {
            format!("{prefix} ({total} lossy {noun}: {preview})")
        } else {
            format!("{prefix} ({total} lossy {noun}: {preview}, +{omitted} more kinds)")
        }
    }

    fn summarize_lossy_expr(expr: &Expr) -> &'static str {
        match expr.strip_mdata().kind() {
            ExprKind::Let(..) => "Let",
            ExprKind::Proj(..) => "Proj",
            ExprKind::Sort(..) => "Sort",
            ExprKind::Lam(..) => "Lam",
            ExprKind::Pi(..) => "Pi",
            ExprKind::Lit(..) => "Lit",
            ExprKind::BVar(..) => "BVar",
            ExprKind::App(..) => Self::summarize_lossy_app_head(expr),
            _ => "Other",
        }
    }

    fn summarize_lossy_app_head(expr: &Expr) -> &'static str {
        let head = expr.strip_mdata().get_app_fn().strip_mdata();
        match head.kind() {
            ExprKind::Lam(..) => "App(Lam head)",
            _ => "App(Complex head)",
        }
    }

    /// Try to prove a proposition using SMT.
    ///
    /// For a goal `P`, we check if `¬P` is unsatisfiable.
    /// If UNSAT, then `P` must be true.
    ///
    /// Returns a tri-state [`SmtVerificationResult`]:
    /// - `Verified(proof)` — goal proved (¬goal unsatisfiable)
    /// - `Refuted(model)` — counterexample found (¬goal satisfiable)
    /// - `Unknown(reason)` — solver inconclusive
    ///
    /// # Single-shot contract (#2836)
    ///
    /// Each `SmtBridge` instance may call `prove()` at most once. The bridge
    /// accumulates solver clauses, lossy atoms, and hypothesis state that is not
    /// isolated per goal. A second call returns [`BridgeError::BridgeReuse`]
    /// before any state mutation. Create a new `SmtBridge` for each goal.
    ///
    /// REQUIRES: `goal` is a Prop-typed expression in the bridge's environment.
    /// REQUIRES: first call on this bridge instance (single-shot).
    /// ENSURES: on `Ok(Verified(proof))`, `proof.proof_term` type-checks against `goal`.
    /// ENSURES: on `Ok(Refuted(model))`, model witnesses `¬goal`.
    pub fn prove(&mut self, goal: &Expr) -> BridgeResult<SmtVerificationResult> {
        // Single-shot guard: the bridge accumulates solver clauses, lossy atoms,
        // and hypothesis state that is not reset between calls. A second prove()
        // would operate on contaminated state, producing unsound results. (#2836)
        if self.prove_called {
            return Err(BridgeError::BridgeReuse);
        }
        self.prove_called = true;

        // Run the unchanged pipeline first so every goal the existing strategies
        // already prove keeps its exact proof term and verdict (no regression).
        let primary = self.prove_core(goal)?;
        if matches!(
            primary,
            SmtVerificationResult::Verified(_) | SmtVerificationResult::Refuted(_)
        ) {
            return Ok(primary);
        }

        // Closed equality-implication lane (additive): only when the pipeline did
        // NOT produce a proof. A goal `H1 → … → Hn → (a = b)` with no local context
        // is reconstructed by introducing the antecedents as tracked hypotheses on a
        // fresh sub-bridge and proving the consequent with the full equality
        // machinery (E-graph trace + multi-hop transitivity + congruence), then
        // re-binding the antecedents as lambdas. Without this, the antecedents are
        // never registered as EUF hypotheses, so the consequent's chain/congruence
        // proof cannot be reconstructed even though the core reaches UNSAT. The
        // re-bound term is kernel-checked before it is trusted; on any failure we
        // return the original (non-proof) outcome, preserving its diagnostics.
        if self.local_ctx.is_none() {
            if let Some((antecedents, consequent)) = self.peel_equality_implication_goal(goal) {
                if let Some(result) =
                    self.try_prove_equality_under_antecedents(goal, &antecedents, &consequent)
                {
                    return Ok(result);
                }
            }
        }

        Ok(primary)
    }

    /// The fixed solve-then-reconstruct pipeline for a single goal.
    ///
    /// Extracted from [`Self::prove`] so the closed equality-implication lane can
    /// re-enter it on a consequent goal without re-tripping the single-shot guard.
    pub(super) fn prove_core(&mut self, goal: &Expr) -> BridgeResult<SmtVerificationResult> {
        self.trail_hypothesis_hints.clear();

        let goal_class = self.classify_prop(goal);

        // Closed-form comparison goals such as `0 <= 1`, `a <= a`, `3 >= 0` do
        // not need a solver round-trip or proof-trail guidance. Ge/Gt are
        // definitional abbreviations (GE.ge a b = LE.le b a) and are handled
        // by swapping arguments in build_direct_arithmetic_goal_proof.
        if matches!(
            goal_class,
            LogicalForm::Le { .. }
                | LogicalForm::Lt { .. }
                | LogicalForm::Ge { .. }
                | LogicalForm::Gt { .. }
        ) {
            if let Ok((proof_step, proof_term)) =
                self.build_direct_arithmetic_goal_proof(&goal_class)
            {
                return Ok(SmtVerificationResult::Verified(Box::new(
                    SmtProofResult::new(
                        ProofMethod::SmtUnsat,
                        "SMT proved via direct arithmetic reconstruction",
                        proof_term,
                        proof_step,
                    ),
                )));
            }
        }

        // For equality goals, translate and remember terms for proof reconstruction
        let eq_goal_terms = match &goal_class {
            LogicalForm::Eq { ty, lhs, rhs } => {
                let t1 = self.translate_term(lhs)?;
                let t2 = self.translate_term(rhs)?;
                self.term_to_type.insert(t1, ty.clone());
                self.term_to_type.insert(t2, ty.clone());
                Some((t1, t2, lhs.clone(), rhs.clone(), ty.clone()))
            }
            _ => None,
        };

        self.translate_negated_classified(&goal_class)?;
        let result = self.smt.solve();

        // If not UNSAT and we have pending foralls, try E-matching instantiation
        if !matches!(result, SmtResult::Unsat(_)) && !self.pending_foralls.is_empty() {
            if let Some(r) = self.prove_with_ematching(&goal_class, &eq_goal_terms) {
                if self.lossy_atoms.is_empty() {
                    return Ok(r);
                }
                return Ok(self.lossy_unknown(
                    "lossy translation: compound propositions treated as unconstrained atoms",
                ));
            }
        }

        self.process_solve_result(result, eq_goal_terms, &goal_class, goal)
    }

    /// Dispatch the SMT solver result to the appropriate handler.
    fn process_solve_result(
        &mut self,
        result: SmtResult,
        eq_goal_terms: Option<EqGoalTerms>,
        goal_class: &LogicalForm,
        goal: &Expr,
    ) -> BridgeResult<SmtVerificationResult> {
        match result {
            SmtResult::Unsat(core) => {
                if !self.lossy_atoms.is_empty() {
                    return Ok(self.lossy_unknown(
                        "lossy translation: UNSAT may be spurious due to unconstrained atoms",
                    ));
                }
                // Use UNSAT core to focus hypothesis set (#349, #2442 Phase 2)
                if let Some(ref core) = core {
                    self.filter_hypotheses_by_core(core);
                }
                self.refresh_trail_hypothesis_hints();
                self.reconstruct_unsat_proof(eq_goal_terms, goal_class, goal)
            }
            SmtResult::Sat(model) => {
                if !self.lossy_atoms.is_empty() {
                    return Ok(self.lossy_unknown(
                        "lossy translation: SAT result may be spurious due to unconstrained atoms",
                    ));
                }
                if let Some(reconstructed) =
                    self.try_structural_goal_reconstruction(&eq_goal_terms, goal_class, goal)
                {
                    return Ok(reconstructed);
                }
                Ok(SmtVerificationResult::Refuted(model))
            }
            SmtResult::Unknown => {
                if let Some(reconstructed) =
                    self.try_structural_goal_reconstruction(&eq_goal_terms, goal_class, goal)
                {
                    return Ok(reconstructed);
                }
                Ok(SmtVerificationResult::Unknown(
                    "solver returned unknown".into(),
                ))
            }
        }
    }

    /// Reconstruct a kernel proof from an UNSAT result.
    ///
    /// Tries equality proof reconstruction first (if the goal is an equality),
    /// then falls back to propositional reconstruction for all goal types.
    fn reconstruct_unsat_proof(
        &mut self,
        eq_goal_terms: Option<EqGoalTerms>,
        goal_class: &LogicalForm,
        goal: &Expr,
    ) -> BridgeResult<SmtVerificationResult> {
        if let Some((t1, t2, lhs_expr, rhs_expr, eq_ty)) = eq_goal_terms {
            match self.build_equality_proof(t1, t2, &lhs_expr, &rhs_expr, &eq_ty, 0) {
                Ok((proof_step, proof_term)) => {
                    return Ok(SmtVerificationResult::Verified(Box::new(
                        SmtProofResult::new(
                            ProofMethod::SmtUnsat,
                            "SMT proved equality via E-graph",
                            proof_term,
                            proof_step,
                        ),
                    )));
                }
                Err(eq_error) => {
                    let mut primary_error = eq_error;

                    match self.build_arithmetic_equality_proof(&eq_ty, &lhs_expr, &rhs_expr) {
                        Ok((proof_step, proof_term)) => {
                            return Ok(SmtVerificationResult::Verified(Box::new(
                                SmtProofResult::new(
                                    ProofMethod::SmtUnsat,
                                    "SMT proved equality via arithmetic antisymmetry",
                                    proof_term,
                                    proof_step,
                                ),
                            )));
                        }
                        Err(arith_error) => {
                            primary_error = BridgeError::ProofTraceFailed(format!(
                                "{primary_error}; arithmetic equality fallback failed: {arith_error}"
                            ));
                        }
                    }

                    // Equality reconstruction failed — try propositional ex-falso fallback
                    match self.build_propositional_proof(goal_class, goal) {
                        Ok((proof_step, proof_term)) => {
                            return Ok(SmtVerificationResult::Verified(Box::new(
                                SmtProofResult::new(
                                    ProofMethod::SmtUnsat,
                                    "SMT proved equality via propositional contradiction",
                                    proof_term,
                                    proof_step,
                                ),
                            )));
                        }
                        Err(_) => {
                            return Ok(SmtVerificationResult::Unverified {
                                reason: primary_error,
                                method: ProofMethod::SmtUnsat,
                            });
                        }
                    }
                }
            }
        }

        let arithmetic_error = match goal_class {
            LogicalForm::Le { .. }
            | LogicalForm::Lt { .. }
            | LogicalForm::Ge { .. }
            | LogicalForm::Gt { .. }
            | LogicalForm::False => match self.build_arithmetic_goal_proof(goal_class, goal) {
                Ok((proof_step, proof_term)) => {
                    return Ok(SmtVerificationResult::Verified(Box::new(
                        SmtProofResult::new(
                            ProofMethod::SmtUnsat,
                            "SMT proved via arithmetic trail reconstruction",
                            proof_term,
                            proof_step,
                        ),
                    )));
                }
                Err(error) => Some(error),
            },
            _ => None,
        };

        // Non-equality goal: propositional proof reconstruction (#2442 Phase 1)
        match self.build_propositional_proof(goal_class, goal) {
            Ok((proof_step, proof_term)) => Ok(SmtVerificationResult::Verified(Box::new(
                SmtProofResult::new(
                    ProofMethod::SmtUnsat,
                    "SMT proved via propositional reconstruction",
                    proof_term,
                    proof_step,
                ),
            ))),
            Err(e) => {
                // Enrich error with trail diagnostics (#2442 Phase 2)
                let base_error = if let Some(arith_error) = arithmetic_error {
                    BridgeError::ProofTraceFailed(format!(
                        "{arith_error}; propositional fallback failed: {e}"
                    ))
                } else {
                    e
                };
                let reason = if self.has_theory_events() {
                    let (conflicts, propagations) = self.trail_event_counts();
                    let theory_conflicts = self.trail_conflict_theories();
                    BridgeError::ProofTraceFailed(format!(
                        "{base_error} (trail: {conflicts} conflicts, {propagations} propagations, \
                         {} theory conflicts)",
                        theory_conflicts.len()
                    ))
                } else {
                    base_error
                };
                Ok(SmtVerificationResult::Unverified {
                    reason,
                    method: ProofMethod::SmtUnsat,
                })
            }
        }
    }

    fn try_structural_goal_reconstruction(
        &self,
        eq_goal_terms: &Option<EqGoalTerms>,
        goal_class: &LogicalForm,
        goal: &Expr,
    ) -> Option<SmtVerificationResult> {
        if let Some((_, _, lhs_expr, rhs_expr, eq_ty)) = eq_goal_terms.as_ref() {
            if let Ok((proof_step, proof_term)) =
                self.build_arithmetic_equality_proof(eq_ty, lhs_expr, rhs_expr)
            {
                return Some(SmtVerificationResult::Verified(Box::new(
                    SmtProofResult::new(
                        ProofMethod::SmtUnsat,
                        "SMT proved equality via structural arithmetic reconstruction",
                        proof_term,
                        proof_step,
                    ),
                )));
            }
        }

        match goal_class {
            LogicalForm::Le { .. }
            | LogicalForm::Lt { .. }
            | LogicalForm::Ge { .. }
            | LogicalForm::Gt { .. }
            | LogicalForm::False => {
                if let Ok((proof_step, proof_term)) =
                    self.build_arithmetic_goal_proof(goal_class, goal)
                {
                    return Some(SmtVerificationResult::Verified(Box::new(
                        SmtProofResult::new(
                            ProofMethod::SmtUnsat,
                            "SMT proved via structural arithmetic reconstruction",
                            proof_term,
                            proof_step,
                        ),
                    )));
                }
            }
            _ => {}
        }

        self.build_propositional_proof(goal_class, goal)
            .ok()
            .map(|(proof_step, proof_term)| {
                SmtVerificationResult::Verified(Box::new(SmtProofResult::new(
                    ProofMethod::SmtUnsat,
                    "SMT proved via structural propositional reconstruction",
                    proof_term,
                    proof_step,
                )))
            })
    }
}
