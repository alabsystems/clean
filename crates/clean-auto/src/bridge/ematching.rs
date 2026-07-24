// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E-matching instantiation for quantifier reasoning.
//!
//! Provides iterative E-matching: match trigger patterns against the E-graph,
//! instantiate quantifier bodies with matched terms, and re-solve until a proof
//! is found or saturation is reached.

use std::collections::HashSet;

use clean_kernel::Expr;

use super::expr_classifier::LogicalForm;
use super::scoring::{GoalDirectedScorer, GoalPatternExtractor, QuantifierPriorityScorer};
use super::{BridgeError, ProofMethod, SmtBridge, SmtProofResult, SmtVerificationResult};
use crate::smt::{SmtResult, TermId};

impl<'env> SmtBridge<'env> {
    /// Try to prove with E-matching instantiation rounds
    ///
    /// This performs iterative quantifier instantiation using E-matching:
    /// 1. Get the E-graph from the equality theory
    /// 2. For each pending forall, match triggers against the E-graph
    /// 3. Instantiate the forall body with matched terms
    /// 4. Add instantiated formulas as new hypotheses
    /// 5. Re-solve and repeat up to max_instantiation_rounds
    pub(super) fn prove_with_ematching(
        &mut self,
        goal_class: &LogicalForm,
        eq_goal_terms: &Option<(TermId, TermId, Expr, Expr, Expr)>,
    ) -> Option<SmtVerificationResult> {
        let max_rounds = self.max_instantiation_rounds;
        let max_per_round = self.max_instantiations_per_round;

        // Extract goal patterns for goal-directed instantiation
        let goal_patterns = {
            let mut extractor = GoalPatternExtractor::new(&self.expr_to_term);
            extractor.extract(goal_class)
        };

        // Re-score pending foralls with goal-directed scoring if we have patterns
        if !goal_patterns.is_empty() {
            let scorer = GoalDirectedScorer::new(goal_patterns);
            for pending in &mut self.pending_foralls {
                pending.priority = scorer.score(pending);
            }
        }

        for _round in 0..max_rounds {
            // Get current E-graph state
            let new_instances = self.collect_ematching_instances(max_per_round);

            if new_instances.is_empty() {
                // No new instances to add, E-matching saturated
                break;
            }

            // Add instantiated formulas as hypotheses
            for inst in &new_instances {
                if let Err(e) = self.add_hypothesis(inst) {
                    self.ematching_hypothesis_errors += 1;
                    tracing::warn!(
                        round = _round,
                        error_count = self.ematching_hypothesis_errors,
                        "E-matching hypothesis add failed: {e}",
                    );
                }
            }

            // Re-solve with new instances
            match self.smt.solve() {
                SmtResult::Unsat(_core) => {
                    // Success! Try to build proof
                    if let Some((t1, t2, lhs_expr, rhs_expr, eq_ty)) = eq_goal_terms {
                        match self.build_equality_proof(*t1, *t2, lhs_expr, rhs_expr, eq_ty, 0) {
                            Ok((proof_step, proof_term)) => {
                                return Some(SmtVerificationResult::Verified(Box::new(
                                    SmtProofResult::new(
                                        ProofMethod::SmtUnsat,
                                        "SMT proved via E-matching instantiation",
                                        proof_term,
                                        proof_step,
                                    ),
                                )));
                            }
                            Err(e) => {
                                // UNSAT but reconstruction failed (#2387 TB2)
                                return Some(SmtVerificationResult::Unverified {
                                    reason: e,
                                    method: ProofMethod::SmtUnsat,
                                });
                            }
                        }
                    }
                    // Non-equality UNSAT: no reconstruction available (#2387 TB2)
                    return Some(SmtVerificationResult::Unverified {
                        reason: BridgeError::UnsupportedExpr {
                            context: "E-matching proved non-equality goal: proof reconstruction not yet available".into(),
                        },
                        method: ProofMethod::SmtUnsat,
                    });
                }
                SmtResult::Sat(_) | SmtResult::Unknown => {
                    // Continue to next round
                }
            }
        }

        None
    }

    /// Collect E-matching instances from pending foralls
    ///
    /// Uses the E-graph to find matching terms for trigger patterns,
    /// then instantiates forall bodies with those terms.
    /// Deduplicates instances to avoid redundant instantiations across rounds.
    ///
    /// Quantifiers are processed in priority order (higher priority first).
    pub(super) fn collect_ematching_instances(&mut self, max_instances: usize) -> Vec<Expr> {
        use crate::egraph::EMatcher;

        // Sort pending_foralls by total priority (base + origin relevance bonus).
        let premise_scores = &self.premise_scores;
        self.pending_foralls.sort_by(|a, b| {
            b.total_priority(premise_scores)
                .cmp(&a.total_priority(premise_scores))
        });

        // Phase 1: Collect all candidate substitutions without mutable self borrow
        let candidate_substitutions: Vec<(usize, Expr, crate::egraph::Substitution, Vec<u32>)> = {
            // Get E-graph from equality theory
            let egraph = match self.equality_theory() {
                Some(eq) => eq.egraph(),
                None => return Vec::new(),
            };

            let matcher = EMatcher::new(egraph);
            let mut candidates = Vec::new();

            for (forall_idx, pending) in self.pending_foralls.iter().enumerate() {
                if candidates.len() >= max_instances * 2 {
                    break;
                }

                for trigger in &pending.triggers {
                    if candidates.len() >= max_instances * 2 {
                        break;
                    }

                    let substitutions = matcher.find_multi_matches(&trigger.patterns);

                    for subst in substitutions {
                        if candidates.len() >= max_instances * 2 {
                            break;
                        }
                        candidates.push((
                            forall_idx,
                            pending.body.clone(),
                            subst,
                            pending.bound_vars.clone(),
                        ));
                    }
                }
            }
            candidates
        };

        // Phase 2: Instantiate and deduplicate with mutable access to seen_instances
        // Build the eclass→expr reverse index once for the entire round (O(terms))
        // instead of scanning the full map per bound variable per substitution.
        let eclass_index = self.build_eclass_to_expr_index();
        let mut instances = Vec::new();
        let mut foralls_with_new_instances: HashSet<usize> = HashSet::new();

        for (forall_idx, body, subst, bound_vars) in candidate_substitutions {
            if instances.len() >= max_instances {
                break;
            }

            if let Some(inst_expr) =
                self.instantiate_from_substitution(&body, &subst, &bound_vars, &eclass_index)
            {
                if let Some(key) = self.expr_to_key(&inst_expr) {
                    if self.seen_instances.insert(key) {
                        instances.push(inst_expr);
                        foralls_with_new_instances.insert(forall_idx);
                    }
                } else {
                    instances.push(inst_expr);
                    foralls_with_new_instances.insert(forall_idx);
                }
            }
        }

        // Phase 3: Update instantiation counts and re-score priorities
        let scorer = QuantifierPriorityScorer::new();
        for idx in foralls_with_new_instances {
            if idx < self.pending_foralls.len() {
                self.pending_foralls[idx].instantiation_count += 1;
                self.pending_foralls[idx].priority = scorer.score(&self.pending_foralls[idx]);
            }
        }

        instances
    }
}
