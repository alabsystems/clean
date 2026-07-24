// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! EUF transitivity proof building for theory lemma reconstruction.
//!
//! Implements the Classical.em case-splitting pattern for:
//! - **Transitivity**: nested `Or.rec` on `Classical.em (aᵢ = aᵢ₊₁)` with `Eq.trans` base case
//!
//! See also `theory_lemma_congr.rs` (congruent) and `theory_lemma_pred.rs` (congruent-pred).

use ay_core::{ProofId, TermId};
use clean_kernel::Expr;

use super::em_combinator::EmSplitItem;
use super::expr_builders;
use super::theory_lemma::ClauseEquality;
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use crate::bridge::disjunction;

impl<'a> ReconstructionContext<'a> {
    /// Build the nested Classical.em proof for a transitivity lemma.
    ///
    /// Delegates to the shared `build_em_case_split` combinator, with a base
    /// case that builds the Eq.trans chain and injects the conclusion.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_em_transitivity_proof(
        &self,
        clause: &[TermId],
        props: &[Expr],
        target: &Expr,
        chain: &[(usize, bool)],
        conclusion: &ClauseEquality,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let items: Vec<EmSplitItem> = chain
            .iter()
            .map(|&(clause_idx, _)| EmSplitItem { clause_idx })
            .collect();
        self.build_em_case_split(clause, props, target, &items, step_id, 0, &|depth| {
            let trans_proof = self
                .build_transitivity_chain_from_bvars(clause, chain, conclusion, depth, step_id)?;
            Ok(disjunction::inject_into_or_chain(
                props,
                conclusion.clause_idx,
                trans_proof,
            ))
        })
    }

    /// Build the Eq.trans chain from bound variables at the base case.
    ///
    /// At nesting depth `n` (inside n lambdas), the equality proof bound
    /// at depth k (0-indexed from outermost) is `BVar(n - 1 - k)`.
    fn build_transitivity_chain_from_bvars(
        &self,
        clause: &[TermId],
        chain: &[(usize, bool)],
        conclusion: &ClauseEquality,
        depth: usize,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if chain.is_empty() {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "empty transitivity chain".to_string(),
            });
        }

        // Get the type from the conclusion equality
        let trace = self.trace();
        let eq_sort = trace.sort(conclusion.lhs);
        let alpha = expr_builders::sort_to_lean_type(eq_sort);

        if chain.len() == 1 {
            // Single equality: direct proof (possibly with symm)
            let bvar = Expr::bvar((depth - 1) as u32);
            let (_neg_eq_idx, needs_symm) = chain[0];
            if needs_symm {
                let neg_lit = clause[chain[0].0];
                let inner_eq =
                    trace
                        .as_not(neg_lit)
                        .ok_or_else(|| ReconstructionError::UnsupportedStep {
                            step_index: step_id.0,
                            description: "expected Not in chain".to_string(),
                        })?;
                let (lhs, rhs) = self.as_equality(inner_eq).ok_or_else(|| {
                    ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "expected equality in chain".to_string(),
                    }
                })?;
                let a = self.term_cache.get(&lhs).cloned().ok_or_else(|| {
                    ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "term not in cache".to_string(),
                    }
                })?;
                let b = self.term_cache.get(&rhs).cloned().ok_or_else(|| {
                    ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "term not in cache".to_string(),
                    }
                })?;
                Ok(expr_builders::mk_eq_symm(&alpha, &a, &b, &bvar))
            } else {
                Ok(bvar)
            }
        } else {
            // Multiple equalities: build Eq.trans chain right-to-left
            // chain[0] → chain[1] → ... → chain[n-1]
            let endpoints = self.get_chain_endpoints(clause, chain, step_id)?;

            // Build the chain: Eq.trans h₁ (Eq.trans h₂ (... hₙ))
            let mut current =
                self.get_chain_proof_at(clause, chain, chain.len() - 1, depth, &alpha, step_id)?;

            for i in (0..chain.len() - 1).rev() {
                let h_i = self.get_chain_proof_at(clause, chain, i, depth, &alpha, step_id)?;
                let a_expr = &endpoints[i];
                let b_expr = &endpoints[i + 1];
                let c_expr = &endpoints[i + 2];
                current =
                    expr_builders::mk_eq_trans(&alpha, a_expr, b_expr, c_expr, &h_i, &current);
            }

            Ok(current)
        }
    }

    /// Get the proof expression for chain[i] at the given nesting depth.
    /// Returns BVar with possible Eq.symm wrapping.
    fn get_chain_proof_at(
        &self,
        clause: &[TermId],
        chain: &[(usize, bool)],
        i: usize,
        depth: usize,
        alpha: &Expr,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let bvar_idx = (depth - 1 - i) as u32;
        let bvar = Expr::bvar(bvar_idx);
        let (_neg_eq_idx, needs_symm) = chain[i];

        if needs_symm {
            let neg_lit = clause[chain[i].0];
            let inner_eq = self.trace().as_not(neg_lit).ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "expected Not in chain proof".to_string(),
                }
            })?;
            let (lhs, rhs) =
                self.as_equality(inner_eq)
                    .ok_or_else(|| ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "expected equality".to_string(),
                    })?;
            let a = self.term_cache.get(&lhs).cloned().ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "term not in cache for symm".to_string(),
                }
            })?;
            let b = self.term_cache.get(&rhs).cloned().ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "term not in cache for symm".to_string(),
                }
            })?;
            Ok(expr_builders::mk_eq_symm(alpha, &a, &b, &bvar))
        } else {
            Ok(bvar)
        }
    }

    /// Get the ordered endpoint terms for a transitivity chain.
    ///
    /// For chain a₁=a₂, a₂=a₃, ..., aₙ₋₁=aₙ, returns [a₁, a₂, a₃, ..., aₙ]
    /// accounting for symmetry flags.
    fn get_chain_endpoints(
        &self,
        clause: &[TermId],
        chain: &[(usize, bool)],
        step_id: ProofId,
    ) -> ReconstructResult<Vec<Expr>> {
        let mut endpoints = Vec::with_capacity(chain.len() + 1);

        let trace = self.trace();
        for (i, &(neg_eq_idx, needs_symm)) in chain.iter().enumerate() {
            let neg_lit = clause[neg_eq_idx];
            let inner_eq =
                trace
                    .as_not(neg_lit)
                    .ok_or_else(|| ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "expected Not in chain endpoints".to_string(),
                    })?;
            let (lhs, rhs) =
                self.as_equality(inner_eq)
                    .ok_or_else(|| ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "expected equality in chain".to_string(),
                    })?;

            // If needs_symm, the edge goes rhs → lhs (reversed)
            let (from, to) = if needs_symm { (rhs, lhs) } else { (lhs, rhs) };

            let from_expr = self.term_cache.get(&from).cloned().ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "endpoint not in cache".to_string(),
                }
            })?;

            if i == 0 {
                endpoints.push(from_expr);
            }

            let to_expr = self.term_cache.get(&to).cloned().ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "endpoint not in cache".to_string(),
                }
            })?;
            endpoints.push(to_expr);
        }

        Ok(endpoints)
    }
}
