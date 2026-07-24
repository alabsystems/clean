// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certified proof term tactics: exact_with_cert, intro_with_cert, apply_with_cert, assumption_with_cert.
//!
//! These are the certified variants of the basic proof term tactics in `proof_term`.
//! They generate proof certificates during tactic execution for independent verification.

use crate::unify::{MetaState, Unifier, UnifyResult};
use clean_kernel::cert::ProofCert;
use clean_kernel::{Expr, ExprKind};

use super::core::{Goal, LocalDecl, ProofState, TacticError};
use super::proof_term::{apply_aux, exact};

/// Result type for certified tactic execution
pub type CertifiedTacticResult = Result<ProofCert, TacticError>;

/// Close the goal with an exact proof term and return a certificate.
///
/// This is the certified variant of `exact`. It performs the same operation
/// but additionally generates a proof certificate witnessing the typing derivation.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `proof` has a type that unifies with the current goal target
/// ENSURES: On Ok, the current goal is closed and a ProofCert is returned
/// ENSURES: On Err(TypeMismatch), proof type does not unify with goal target; state is unchanged
pub fn exact_with_cert(state: &mut ProofState, proof: Expr) -> CertifiedTacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Infer the type with certificate
    let (proof_ty, cert) = state.infer_type_with_cert(&goal, &proof)?;

    // Check that the proof has the right type (via unification to handle metas)
    let target = state.metas.instantiate(&goal.target);
    let ctx = state.build_local_ctx(&goal);

    let unify_result = {
        let (metas, env) = state.metas_and_env();
        Unifier::with_env(metas, env, ctx).unify(&proof_ty, &target)
    };
    match unify_result {
        UnifyResult::Success => {
            // Part of #2154: type-check exact_with_cert proof before accepting
            state.close_goal(&goal, proof)?;
            Ok(cert)
        }
        UnifyResult::Failure(msg) => Err(TacticError::TypeMismatch {
            expected: format!("{target:?}"),
            actual: msg,
        }),
        UnifyResult::Stuck => Err(TacticError::UnificationFailed(
            "unification stuck".to_string(),
        )),
    }
}

/// Introduce a hypothesis and return a certificate for the intro step.
///
/// This is the certified variant of `intro`. It returns a certificate
/// representing the lambda abstraction being constructed. Note that the
/// certificate is for the proof term being built (λ x : A, ?body), not
/// for the final proof (which is not yet complete).
///
/// The returned certificate is for the domain type (A : Sort), confirming
/// it is a valid type. The full proof certificate is assembled when all
/// goals are closed.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Current goal target is a Pi/forall type (after WHNF)
/// ENSURES: On Ok, hypothesis is introduced and a domain type ProofCert is returned
/// ENSURES: On Err(GoalMismatch), goal target is not a Pi type; state is unchanged
pub fn intro_with_cert(state: &mut ProofState, name: &str) -> CertifiedTacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // WHNF to expose the Pi
    let target = state.whnf(&goal, &goal.target);

    match target.kind() {
        ExprKind::Pi(bi, domain, codomain) => {
            // Generate certificate for the domain type
            let (_domain_type, domain_cert) = state.infer_type_with_cert(&goal, domain)?;

            // Create a new free variable for the introduced hypothesis
            let fvar = state.fresh_fvar();

            // Create the new local declaration
            let local_decl = LocalDecl {
                fvar,
                name: name.to_string(),
                ty: domain.as_ref().clone(),
                value: None,
            };

            // Create new context with the hypothesis
            let mut new_ctx = goal.local_ctx.clone();
            new_ctx.push(local_decl);

            // Instantiate the codomain with the free variable
            let new_target = codomain.instantiate(&Expr::fvar(fvar));

            // Create new metavariable for the new goal
            let new_meta_id = state.fresh_meta_in_context(new_target.clone(), &new_ctx);

            // The proof of the original goal is λ x : A, <new_proof>
            let new_meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id)));
            let proof = Expr::lam(
                *bi,
                domain.as_ref().clone(),
                new_meta_expr.abstract_fvar(fvar),
            );

            // Part of #2154: type-check intro_with_cert proof before accepting
            state.close_goal(&goal, proof)?;

            // Add the new goal
            let new_goal = Goal {
                meta_id: new_meta_id,
                target: new_target,
                local_ctx: new_ctx,
                tag: None,
            };

            state.goals.push_front(new_goal);

            // Return the domain type certificate
            Ok(domain_cert)
        }
        _ => Err(TacticError::GoalMismatch(
            "intro requires a forall/arrow goal".to_string(),
        )),
    }
}

/// Apply a function and return a certificate for the application.
///
/// This is the certified variant of `apply`. It returns a certificate
/// for the function's type inference.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, function is applied and a ProofCert for the function type is returned
/// ENSURES: On Err, function result type cannot unify with the goal target
pub fn apply_with_cert(state: &mut ProofState, func: Expr) -> CertifiedTacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Infer the type of the function with certificate
    let (func_ty, cert) = state.infer_type_with_cert(&goal, &func)?;

    // Apply the function using the regular apply logic
    apply_aux(state, &goal, func, func_ty)?;

    Ok(cert)
}

/// Use a hypothesis from context and return a certificate.
///
/// This is the certified variant of `assumption`. It searches for a
/// hypothesis matching the goal and returns the certificate for that
/// hypothesis's type.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, a matching hypothesis is used and its type ProofCert is returned
/// ENSURES: On Err(HypothesisNotFound), no hypothesis matches; state is unchanged
pub fn assumption_with_cert(state: &mut ProofState) -> CertifiedTacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Search through hypotheses for one that matches
    for decl in &goal.local_ctx {
        let hyp_ty = state.metas.instantiate(&decl.ty);
        if state.is_def_eq(&goal, &hyp_ty, &target) {
            let hyp_expr = Expr::fvar(decl.fvar);
            // Get certificate for the hypothesis
            let (_, cert) = state.infer_type_with_cert(&goal, &hyp_expr)?;
            exact(state, hyp_expr)?;
            return Ok(cert);
        }
    }

    Err(TacticError::HypothesisNotFound(
        "no matching hypothesis found".into(),
    ))
}
