// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Congruence proof construction: congrArg and congr for multi-argument functions.

use super::{ProofBuilder, ProofReconstructionError, ProofStep};
use crate::bridge::eq_proof_builders;
use clean_kernel::{Expr, ExprKind, Level, TypeChecker};

impl<'a> ProofBuilder<'a> {
    /// Build `@congrArg.{u,v} α β a₁ a₂ f h`.
    pub(super) fn mk_congr_arg(
        &self,
        func_expr: &Expr,
        arg_proof: &Expr,
        arg_step: &ProofStep,
    ) -> Result<Expr, ProofReconstructionError> {
        let (u, v) = self.congr_universe_levels(func_expr)?;

        // Recover a₁, a₂ from the argument proof step
        let (t_a1, t_a2) =
            self.step_span(arg_step)
                .ok_or_else(|| ProofReconstructionError::StepSpanUnknown {
                    context: "congrArg arg terms".into(),
                })?;
        let a1 = self
            .term_to_expr
            .get(&t_a1)
            .ok_or(ProofReconstructionError::MissingTermMapping(t_a1))?;
        let a2 = self
            .term_to_expr
            .get(&t_a2)
            .ok_or(ProofReconstructionError::MissingTermMapping(t_a2))?;

        // α = type of a₁
        let alpha = self
            .term_to_type
            .get(&t_a1)
            .cloned()
            .ok_or(ProofReconstructionError::MissingTermMapping(t_a1))?;

        // β = codomain of f
        let env = self.env.ok_or(ProofReconstructionError::NoEnvironment)?;
        let beta = {
            let tc = TypeChecker::new(env);
            let func_ty = tc.infer_type(func_expr).map_err(|e| {
                ProofReconstructionError::CongruenceInferenceFailed {
                    func: format!("{func_expr:?}"),
                    reason: format!("codomain inference: {e:?}"),
                }
            })?;
            match func_ty.kind() {
                ExprKind::Pi(_, _, body) => body.as_ref().clone(),
                _ => {
                    return Err(ProofReconstructionError::CongruenceInferenceFailed {
                        func: format!("{func_expr:?}"),
                        reason: "expected Pi type for codomain".into(),
                    })
                }
            }
        };

        // @congrArg.{u,v} α β a₁ a₂ f h
        Ok(eq_proof_builders::mk_congr_arg(
            &u, &v, &alpha, &beta, a1, a2, func_expr, arg_proof,
        ))
    }

    /// Build `@congr.{u,v} α β f₁ f₂ a₁ a₂ hf ha` for multi-argument functions.
    ///
    /// For `f a₁ b₁ = f a₂ b₂`:
    /// 1. `@congrArg.{u₀,v₀} α₀ β₀ a₁ a₂ f h_a`
    /// 2. `@congr.{u₁,v₁} α₁ β₁ (f a₁) (f a₂) b₁ b₂ step1 h_b`
    pub(super) fn mk_congr_multi(
        &self,
        func_expr: &Expr,
        arg_proofs: &[Expr],
        arg_steps: &[ProofStep],
    ) -> Result<Expr, ProofReconstructionError> {
        if arg_proofs.is_empty() {
            return Err(ProofReconstructionError::EmptyCongruenceArgs {
                func: format!("{func_expr:?}"),
            });
        }

        let env = self.env.ok_or(ProofReconstructionError::NoEnvironment)?;
        let func_ty = {
            let tc = TypeChecker::new(env);
            tc.infer_type(func_expr).ok()
        };

        let (u0, v0, alpha_0, mut remaining_ty) = self.peel_pi_full(&func_ty)?;
        let beta_0 = remaining_ty
            .clone()
            .ok_or(ProofReconstructionError::NoEnvironment)?;

        // Recover a₁₀, a₂₀ from first arg step
        let (t_a1_0, t_a2_0) = self.step_span(&arg_steps[0]).ok_or_else(|| {
            ProofReconstructionError::StepSpanUnknown {
                context: "congr_multi first arg".into(),
            }
        })?;
        let a1_0 = self
            .term_to_expr
            .get(&t_a1_0)
            .ok_or(ProofReconstructionError::MissingTermMapping(t_a1_0))?;
        let a2_0 = self
            .term_to_expr
            .get(&t_a2_0)
            .ok_or(ProofReconstructionError::MissingTermMapping(t_a2_0))?;

        // @congrArg.{u₀,v₀} α₀ β₀ a₁₀ a₂₀ f h₁
        let mut result = eq_proof_builders::mk_congr_arg(
            &u0,
            &v0,
            &alpha_0,
            &beta_0,
            a1_0,
            a2_0,
            func_expr,
            &arg_proofs[0],
        );

        // Track partial applications for f₁, f₂ in subsequent congr steps
        let mut partial_lhs = Expr::app(func_expr.clone(), a1_0.clone());
        let mut partial_rhs = Expr::app(func_expr.clone(), a2_0.clone());

        for (i, proof) in arg_proofs[1..].iter().enumerate() {
            let idx = i + 1;
            let (u, v, _alpha_i, next_ty) = self.peel_pi_full(&remaining_ty)?;
            let beta_i = next_ty
                .clone()
                .ok_or(ProofReconstructionError::NoEnvironment)?;

            // Recover a₁ᵢ, a₂ᵢ from arg step
            let (t_a1_i, t_a2_i) = self.step_span(&arg_steps[idx]).ok_or_else(|| {
                ProofReconstructionError::StepSpanUnknown {
                    context: format!("congr_multi arg {idx}"),
                }
            })?;
            let a1_i = self
                .term_to_expr
                .get(&t_a1_i)
                .ok_or(ProofReconstructionError::MissingTermMapping(t_a1_i))?;
            let a2_i = self
                .term_to_expr
                .get(&t_a2_i)
                .ok_or(ProofReconstructionError::MissingTermMapping(t_a2_i))?;
            let alpha_i = self
                .term_to_type
                .get(&t_a1_i)
                .cloned()
                .ok_or(ProofReconstructionError::MissingTermMapping(t_a1_i))?;

            remaining_ty = next_ty;

            // @congr.{u,v} α β f₁ f₂ a₁ a₂ hf ha
            result = eq_proof_builders::mk_congr(
                &u,
                &v,
                &alpha_i,
                &beta_i,
                &partial_lhs,
                &partial_rhs,
                a1_i,
                a2_i,
                &result,
                proof,
            );

            partial_lhs = Expr::app(partial_lhs, a1_i.clone());
            partial_rhs = Expr::app(partial_rhs, a2_i.clone());
        }
        Ok(result)
    }

    /// Peel one Pi binder: returns (u, v, domain, Some(body)).
    pub(super) fn peel_pi_full(
        &self,
        ty: &Option<Expr>,
    ) -> Result<(Level, Level, Expr, Option<Expr>), ProofReconstructionError> {
        let ty_expr = ty.as_ref().ok_or(ProofReconstructionError::NoEnvironment)?;
        match ty_expr.kind() {
            ExprKind::Pi(_, domain, body) => {
                let env = self.env.ok_or(ProofReconstructionError::NoEnvironment)?;
                let tc = TypeChecker::new(env);
                let u = tc.infer_sort(domain).map_err(|e| {
                    ProofReconstructionError::SortInferenceFailed(format!("Pi domain sort: {e:?}"))
                })?;
                let v = tc.infer_sort(body).map_err(|e| {
                    ProofReconstructionError::SortInferenceFailed(format!(
                        "Pi codomain sort: {e:?}"
                    ))
                })?;
                Ok((u, v, domain.as_ref().clone(), Some(body.as_ref().clone())))
            }
            _ => Err(ProofReconstructionError::CongruenceInferenceFailed {
                func: format!("{ty_expr:?}"),
                reason: "expected Pi type".into(),
            }),
        }
    }
}
