// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! EUF congruent proof building for theory lemma reconstruction.
//!
//! Implements the Classical.em case-splitting pattern for:
//! - **Congruent**: nested `Or.rec` on `Classical.em (aᵢ = bᵢ)` with `congrArg`/`congr` base case
//!
//! Split from `theory_lemma_euf.rs` for file size compliance.

use ay_core::{ProofId, TermId};
use clean_kernel::{BinderInfo, Expr};

use super::em_combinator::EmSplitItem;
use super::expr_builders;
use super::theory_lemma::ClauseEquality;
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use crate::bridge::disjunction;

impl<'a> ReconstructionContext<'a> {
    /// Build the nested Classical.em proof for a congruent lemma.
    ///
    /// Delegates to the shared `build_em_case_split` combinator, with a base
    /// case that builds the congrArg/congr chain and injects the conclusion.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_em_congruent_proof(
        &self,
        clause: &[TermId],
        props: &[Expr],
        target: &Expr,
        neg_eqs: &[ClauseEquality],
        conclusion: &ClauseEquality,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let items: Vec<EmSplitItem> = neg_eqs
            .iter()
            .map(|eq| EmSplitItem {
                clause_idx: eq.clause_idx,
            })
            .collect();
        self.build_em_case_split(clause, props, target, &items, step_id, 0, &|depth| {
            let congr_proof =
                self.build_congruent_chain_from_bvars(clause, neg_eqs, conclusion, depth, step_id)?;
            Ok(disjunction::inject_into_or_chain(
                props,
                conclusion.clause_idx,
                congr_proof,
            ))
        })
    }

    /// Build congrArg chain from bound variables for EUF congruent lemma.
    ///
    /// Given equalities h₁: a₁=b₁, ..., hₙ: aₙ=bₙ and conclusion f(ā)=f(b̄),
    /// builds: `congrArg f h₁` for single arg, or `congr` chain for multiple.
    pub(super) fn build_congruent_chain_from_bvars(
        &self,
        _clause: &[TermId],
        neg_eqs: &[ClauseEquality],
        conclusion: &ClauseEquality,
        depth: usize,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if neg_eqs.is_empty() {
            // No argument equalities — the conclusion is a reflexivity
            let eq_sort = self.trace().sort(conclusion.lhs);
            let alpha = expr_builders::sort_to_lean_type(eq_sort);
            let a_expr = self
                .term_cache
                .get(&conclusion.lhs)
                .cloned()
                .ok_or_else(|| ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "conclusion LHS not in cache".to_string(),
                })?;
            return Ok(expr_builders::mk_eq_refl(&alpha, &a_expr));
        }

        if neg_eqs.len() == 1 {
            // Single argument: congrArg f h
            let bvar = Expr::bvar((depth - 1) as u32);

            let arg_sort = self.trace().sort(neg_eqs[0].lhs);
            let alpha = expr_builders::sort_to_lean_type(arg_sort);
            let u_alpha = expr_builders::infer_universe_level(&alpha);

            // Get the function expression from the conclusion
            // conclusion.lhs = f(a₁), conclusion.rhs = f(b₁)
            let f_a = self
                .term_cache
                .get(&conclusion.lhs)
                .cloned()
                .ok_or_else(|| ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "f(a) not in cache".to_string(),
                })?;
            let func = f_a.get_app_fn().clone();
            let result_sort = self.trace().sort(conclusion.lhs);
            let beta = expr_builders::sort_to_lean_type(result_sort);
            let u_beta = expr_builders::infer_universe_level(&beta);

            let a1 = self
                .term_cache
                .get(&neg_eqs[0].lhs)
                .cloned()
                .ok_or_else(|| ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "arg a₁ not in cache".to_string(),
                })?;
            let a2 = self
                .term_cache
                .get(&neg_eqs[0].rhs)
                .cloned()
                .ok_or_else(|| ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "arg b₁ not in cache".to_string(),
                })?;

            Ok(expr_builders::mk_congr_arg(
                &u_alpha, &u_beta, &alpha, &beta, &a1, &a2, &func, &bvar,
            ))
        } else {
            self.build_multi_arg_congr_chain(neg_eqs, conclusion, depth, step_id)
        }
    }

    /// Build congr chain for multi-argument congruent lemma.
    ///
    /// For f : α₁ → α₂ → ... → αₙ → R, the congr chain builds:
    ///   congrArg f h₁ : f a₁ = f b₁  (type: Eq (α₂ → ... → R))
    ///   congr prev h₂ : f a₁ a₂ = f b₁ b₂
    ///   ...
    ///   congr prev hₙ : f a₁...aₙ = f b₁...bₙ
    fn build_multi_arg_congr_chain(
        &self,
        neg_eqs: &[ClauseEquality],
        conclusion: &ClauseEquality,
        depth: usize,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let n = neg_eqs.len();

        // Collect argument types from ay sort info
        let arg_types: Vec<Expr> = neg_eqs
            .iter()
            .map(|eq| expr_builders::sort_to_lean_type(self.trace().sort(eq.lhs)))
            .collect();

        // Result type of the full application
        let result_type = expr_builders::sort_to_lean_type(self.trace().sort(conclusion.lhs));

        // Build beta types: beta[k] = α_{k+1} → ... → αₙ → result_type
        // beta[n-1] = result_type
        // beta[k] = Pi(_, α_{k+1}, beta[k+1])
        let mut betas = vec![result_type; n];
        for k in (0..n - 1).rev() {
            betas[k] = Expr::pi(
                BinderInfo::Default,
                arg_types[k + 1].clone(),
                betas[k + 1].clone(),
            );
        }

        // Get the function and argument expressions from term_cache
        let f_a = self
            .term_cache
            .get(&conclusion.lhs)
            .cloned()
            .ok_or_else(|| ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "f(a...) not in cache".to_string(),
            })?;
        let func = f_a.get_app_fn().clone();

        let mut a_args = Vec::with_capacity(n);
        let mut b_args = Vec::with_capacity(n);
        for eq in neg_eqs.iter() {
            a_args.push(self.term_cache.get(&eq.lhs).cloned().ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "arg a not in cache".to_string(),
                }
            })?);
            b_args.push(self.term_cache.get(&eq.rhs).cloned().ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "arg b not in cache".to_string(),
                }
            })?);
        }

        // Step 0: congrArg f h₀
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
            &func,
            &h0,
        );

        // Steps 1..n-1: congr prev hₖ
        // Maintain running partial applications f1=f(a₀..a_{k-1}), f2=f(b₀..b_{k-1})
        // to avoid O(n²) rebuild from scratch each iteration.
        let mut f1 = func.clone();
        let mut f2 = func.clone();
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
