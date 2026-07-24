// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! EUF congruent-pred proof building for theory lemma reconstruction.
//!
//! Implements the Classical.em case-splitting pattern for:
//! - **Congruent-Pred**: nested `Or.rec` on `Classical.em (aᵢ = bᵢ)` then `Classical.em (P a...)`
//!   with `congr` chain + `Eq.mpr` transport at base case
//!
//! Split from `theory_lemma_euf.rs` for file size compliance.

use ay_core::{ProofId, TermId};
use clean_kernel::{BinderInfo, Expr, Level};

use super::em_combinator::EmSplitItem;
use super::expr_builders;
use super::theory_lemma::{ClauseEquality, CongruentPredParsed};
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use crate::bridge::disjunction;

impl<'a> ReconstructionContext<'a> {
    /// Build the nested Classical.em proof for a congruent-pred lemma.
    ///
    /// Clause: `{¬(a₁=b₁), ..., ¬(aₙ=bₙ), ¬(P a...), P(b...)}`
    ///
    /// Delegates to the shared `build_em_case_split` combinator. The items list
    /// concatenates equality case-splits and the predicate case-split (Option 1
    /// from the design doc), preserving the same BVar depth layout.
    pub(super) fn build_em_congruent_pred_proof(
        &self,
        clause: &[TermId],
        props: &[Expr],
        target: &Expr,
        parsed: &CongruentPredParsed,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        // Build items: equalities first, then the predicate
        let mut items: Vec<EmSplitItem> = parsed
            .neg_eqs
            .iter()
            .map(|eq| EmSplitItem {
                clause_idx: eq.clause_idx,
            })
            .collect();
        items.push(EmSplitItem {
            clause_idx: parsed.neg_pred_idx,
        });

        self.build_em_case_split(clause, props, target, &items, step_id, 0, &|depth| {
            // Base case: all equalities hold AND P(a...) holds.
            // BVar(0) = P(a...) proof (innermost, most recently bound)
            // BVar(k+1) = equality proof for neg_eqs[n_eqs - 1 - k]
            let hp = Expr::bvar(0); // proof of P(a...)

            let neg_pred_lit = clause[parsed.neg_pred_idx];
            let inner = self.unwrap_not(neg_pred_lit, step_id)?;
            let pred_a_prop = self.cached_term(inner, step_id, "P(a...) base case")?;
            let pred_b_prop = &props[parsed.pos_pred_idx]; // P(b...)

            let congr_proof =
                self.build_pred_congr_chain(clause, &parsed.neg_eqs, parsed, depth, step_id)?;

            // Eq.mpr transports BACKWARD (β → α), so we reverse:
            //   Eq.symm congr_proof : P(b...) = P(a...)
            //   Eq.mpr {P(b...)} {P(a...)} (Eq.symm congr_proof) hp : P(b...)
            let u_prop = Level::zero();
            let prop_sort = Expr::sort(Level::zero());
            let symm_proof =
                expr_builders::mk_eq_symm(&prop_sort, &pred_a_prop, pred_b_prop, &congr_proof);
            let result =
                expr_builders::mk_eq_mpr(&u_prop, pred_b_prop, &pred_a_prop, &symm_proof, &hp);

            Ok(disjunction::inject_into_or_chain(
                props,
                parsed.pos_pred_idx,
                result,
            ))
        })
    }

    /// Build the congr chain for predicate congruence: P(a...) = P(b...).
    ///
    /// Similar to `build_congruent_chain_from_bvars`, but the function is the
    /// predicate P, and the result type is Prop. Also the BVar offsets account
    /// for the extra predicate lambda binding.
    fn build_pred_congr_chain(
        &self,
        clause: &[TermId],
        neg_eqs: &[ClauseEquality],
        parsed: &CongruentPredParsed,
        depth: usize,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if neg_eqs.is_empty() {
            // No equalities → P(a...) = P(a...) is reflexivity
            let neg_pred_lit = clause[parsed.neg_pred_idx];
            let inner = self.trace().as_not(neg_pred_lit).ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "expected Not for pred refl".to_string(),
                }
            })?;
            let pred_a = self.term_cache.get(&inner).cloned().ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "P(a) not in cache for refl".to_string(),
                }
            })?;
            let prop = Expr::sort(Level::zero());
            return Ok(expr_builders::mk_eq_refl(&prop, &pred_a));
        }

        let n = neg_eqs.len();

        // Get the predicate function from the positive predicate literal
        let pos_pred_lit = clause[parsed.pos_pred_idx];
        let pred_b_expr = self.term_cache.get(&pos_pred_lit).cloned().ok_or_else(|| {
            ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "P(b...) not in cache".to_string(),
            }
        })?;
        let pred_func = pred_b_expr.get_app_fn().clone();

        // Argument types and Prop as result
        let arg_types: Vec<Expr> = neg_eqs
            .iter()
            .map(|eq| expr_builders::sort_to_lean_type(self.trace().sort(eq.lhs)))
            .collect();
        let prop_type = Expr::sort(Level::zero()); // Prop

        // Build beta types for congr chain (same structure as congruent)
        let mut betas = vec![prop_type; n];
        for k in (0..n - 1).rev() {
            betas[k] = Expr::pi(
                BinderInfo::Default,
                arg_types[k + 1].clone(),
                betas[k + 1].clone(),
            );
        }

        // Get argument expressions
        let mut a_args = Vec::with_capacity(n);
        let mut b_args = Vec::with_capacity(n);
        for eq in neg_eqs.iter() {
            a_args.push(self.term_cache.get(&eq.lhs).cloned().ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "pred arg a not in cache".to_string(),
                }
            })?);
            b_args.push(self.term_cache.get(&eq.rhs).cloned().ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "pred arg b not in cache".to_string(),
                }
            })?);
        }

        // BVar mapping: at depth = n_eqs + 1
        // BVar(0) = P(a...) proof (predicate lambda, innermost)
        // BVar(1) = equality proof for neg_eqs[n-1] (last equality)
        // BVar(k+1) = equality proof for neg_eqs[n-1-k]
        // So h_k (equality at index k) = BVar(depth - 1 - k)

        if n == 1 {
            // Single argument: congrArg P h₀
            let h0 = Expr::bvar((depth - 1) as u32);
            let u_alpha = expr_builders::infer_universe_level(&arg_types[0]);
            let u_beta = expr_builders::infer_universe_level(&betas[0]);

            Ok(expr_builders::mk_congr_arg(
                &u_alpha,
                &u_beta,
                &arg_types[0],
                &betas[0],
                &a_args[0],
                &b_args[0],
                &pred_func,
                &h0,
            ))
        } else {
            // Multi-argument: same pattern as congruent
            let h0 = Expr::bvar((depth - 1) as u32);
            let u_alpha_0 = expr_builders::infer_universe_level(&arg_types[0]);
            let u_beta_0 = expr_builders::infer_universe_level(&betas[0]);

            let mut current = expr_builders::mk_congr_arg(
                &u_alpha_0,
                &u_beta_0,
                &arg_types[0],
                &betas[0],
                &a_args[0],
                &b_args[0],
                &pred_func,
                &h0,
            );

            // Maintain running partial applications f1=P(a₀..a_{k-1}), f2=P(b₀..b_{k-1})
            // to avoid O(n²) rebuild from scratch each iteration.
            // Same pattern as theory_lemma_congr.rs:build_multi_arg_congr_chain.
            let mut f1 = pred_func.clone();
            let mut f2 = pred_func.clone();
            for k in 1..n {
                let hk = Expr::bvar((depth - 1 - k) as u32);
                let u_alpha_k = expr_builders::infer_universe_level(&arg_types[k]);
                let u_beta_k = expr_builders::infer_universe_level(&betas[k]);

                // Extend partial applications by one argument
                f1 = Expr::app(f1, a_args[k - 1].clone());
                f2 = Expr::app(f2, b_args[k - 1].clone());

                current = expr_builders::mk_congr(
                    &u_alpha_k,
                    &u_beta_k,
                    &arg_types[k],
                    &betas[k],
                    &f1,
                    &f2,
                    &a_args[k],
                    &b_args[k],
                    &current,
                    &hk,
                );
            }

            Ok(current)
        }
    }
}
