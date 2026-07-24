// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed diagnostics, classification, and superposition recovery for
//! the SMT decide tactic.
//!
//! When SMT proof reconstruction fails or is inconclusive, this module
//! provides the shared recovery lane: try superposition first, then fail
//! closed with a classified diagnostic.

use crate::tactic::{Goal, ProofState, TacticError};
use clean_kernel::{Expr, ExprKind};

use super::super::record_ay_reconstruction_failure;
use super::hypotheses::for_each_non_sort_goal_hypothesis;
use super::validation::validate_proof_term;

/// Try superposition, then fail closed as the last resort.
/// Part of #2411.
///
/// # Contract
///
/// ENSURES: On Ok, returns a kernel-validated proof from superposition
/// ENSURES: On Err, records the reconstruction miss and leaves the goal open
pub(in crate::tactic::smt) fn superposition_or_fail_closed(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic_name: &str,
) -> Result<Expr, TacticError> {
    superposition_or_fail_closed_with_reason(
        state,
        goal,
        target,
        tactic_name,
        "trustedAy whole-goal fallback removed; failing closed",
    )
}

pub(in crate::tactic::smt) fn classify_trusted_ay_fallback_target(target: &Expr) -> &'static str {
    use clean_auto::bridge::head_family::classify_cmp_head;

    let target = target.strip_mdata();
    let head = target.get_app_fn().strip_mdata();
    let args = target.get_app_args();

    match head.kind() {
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            let n = args.len();
            // Equality/propositional — not centralized in head_family
            match (name_str.as_str(), n) {
                ("Eq" | "eq", 3) => "eq",
                ("Ne" | "ne", 3) => "neq",
                ("And" | "and" | "Bool.and", 2) => "and",
                ("Or" | "or" | "Bool.or", 2) => "or",
                ("Not" | "not" | "Bool.not", 1) => "not",
                ("Iff", 2) => "iff",
                ("True", 0) => "true",
                ("False", 0) => "false",
                ("Exists", 2) => "exists",
                _ if n >= 2 => {
                    // Comparison — delegate to shared head_family classifier
                    if let Some(cmp) = classify_cmp_head(&name_str) {
                        cmp.family.as_tag()
                    } else {
                        "atom"
                    }
                }
                _ => "atom",
            }
        }
        ExprKind::Pi(_, _, body) => {
            if body.has_loose_bvars() {
                "forall"
            } else {
                "implies"
            }
        }
        _ => "atom",
    }
}

pub(in crate::tactic::smt) fn trusted_ay_fallback_target_head(target: &Expr) -> Option<String> {
    let head = target.strip_mdata().get_app_fn().strip_mdata();
    match head.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        ExprKind::Pi(_, _, _) => Some("Pi".to_string()),
        _ => None,
    }
}

fn emit_trusted_ay_fallback_diagnostic(target: &Expr, tactic_name: &str) -> (&'static str, String) {
    let goal_class = classify_trusted_ay_fallback_target(target);
    let goal_head = trusted_ay_fallback_target_head(target).unwrap_or_else(|| "?".to_string());
    tracing::warn!(
        tactic = tactic_name,
        goal_class,
        goal_head = %goal_head,
        "trustedAy whole-goal fallback removed; failing closed"
    );
    (goal_class, goal_head)
}

fn trusted_ay_fail_closed_error(
    tactic_name: &str,
    goal_class: &str,
    goal_head: &str,
    reason: &str,
) -> TacticError {
    TacticError::SmtFailed {
        tactic: tactic_name.into(),
        detail: format!("{reason}; reconstruction failed for {goal_class} ({goal_head})"),
    }
}

fn superposition_or_fail_closed_with_reason(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic_name: &str,
    reason: &str,
) -> Result<Expr, TacticError> {
    if let Some(proof) = try_superposition_fallback(state, goal, target, tactic_name)? {
        return Ok(proof);
    }

    let (goal_class, goal_head) = emit_trusted_ay_fallback_diagnostic(target, tactic_name);
    record_ay_reconstruction_failure();
    Err(trusted_ay_fail_closed_error(
        tactic_name,
        goal_class,
        &goal_head,
        reason,
    ))
}

#[cfg(test)]
pub(in crate::tactic::smt) fn force_trusted_ay_fail_closed_for_test(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
) -> Result<Expr, TacticError> {
    superposition_or_fail_closed_with_reason(
        state,
        goal,
        target,
        "decide",
        "test-only forced fail-closed outcome",
    )
}

/// Try to prove a goal using superposition as a fallback when SMT fails or
/// cannot reconstruct a proof term.
///
/// Collects hypotheses from the goal's local context, passes them to the
/// superposition prover via [`AutomationEngine`], and validates the resulting
/// proof term against the kernel type checker.
///
/// The superposition reconstruction produces proof terms that may reference
/// `Classical.byContradiction` and Skolem constants. This function ensures
/// these declarations are available in the state's environment before
/// validation and goal closure.
///
/// Returns `Ok(Some(proof_term))` if superposition produces a kernel-valid
/// proof, `Ok(None)` if superposition cannot prove the goal, and `Err(...)`
/// when classical bootstrap fails before recovery can run. Part of #1164:
/// wiring superposition reconstruction into the tactic framework.
///
/// # Contract
///
/// REQUIRES: `goal` is the current goal with a valid local context
/// REQUIRES: `target` is the instantiated goal target
/// ENSURES: On `Ok(Some(_))`, proof term is kernel-validated and `Classical`
///          is initialized
/// ENSURES: On `Ok(None)`, superposition could not prove or proof failed
///          validation
/// ENSURES: On `Err(SmtFailed)`, classical bootstrap prevented recovery
pub(crate) fn try_superposition_fallback(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic_name: &str,
) -> Result<Option<Expr>, TacticError> {
    use clean_auto::AutomationEngine;
    use clean_kernel::FVarId;

    // Collect hypotheses with their FVarIds from the tactic's local context.
    // Uses the shared non-sort hypothesis contract so the bridge lane and
    // recovery lane always agree on which declarations count as usable.
    let mut hypotheses: Vec<(Expr, FVarId)> = Vec::new();
    for_each_non_sort_goal_hypothesis(state, goal, |hyp_ty, fvar| {
        hypotheses.push((hyp_ty, fvar));
    });

    state
        .env_mut()
        .init_classical()
        .map_err(|error| TacticError::SmtFailed {
            tactic: tactic_name.to_string(),
            detail: format!("classical bootstrap failed before superposition recovery: {error}"),
        })?;

    let engine = AutomationEngine::new();
    let Some(result) = engine.try_superposition_prove_with_fvars(state.env(), target, &hypotheses)
    else {
        return Ok(None);
    };

    Ok(validate_superposition_candidate(
        state,
        goal,
        result.proof_term(),
        target,
        tactic_name,
    ))
}

/// Test-only accessor for `validate_superposition_candidate` so the
/// invalid-candidate branch can be exercised directly (Part of #2937).
#[cfg(test)]
pub(crate) fn validate_superposition_candidate_for_test(
    state: &ProofState,
    goal: &Goal,
    proof: &Expr,
    target: &Expr,
    tactic_name: &str,
) -> Option<Expr> {
    validate_superposition_candidate(state, goal, proof, target, tactic_name)
}

/// Validate a superposition proof candidate through the kernel type checker.
///
/// Returns `Some(proof)` on success. On validation failure, logs the error
/// at warn level (matching bridge/direct-proof recovery lanes) and returns
/// `None` so the caller treats it as "no usable recovery proof."
///
/// Extracted from `try_superposition_fallback` so kernel-validation errors
/// are observable instead of being silently erased by `.ok()` (Part of #2937).
fn validate_superposition_candidate(
    state: &ProofState,
    goal: &Goal,
    proof: &Expr,
    target: &Expr,
    tactic_name: &str,
) -> Option<Expr> {
    match validate_proof_term(state, goal, proof, target) {
        Ok(proof) => Some(proof),
        Err(error) => {
            tracing::warn!(
                tactic = tactic_name,
                error = %error,
                "superposition proof failed kernel validation; discarding recovery candidate"
            );
            None
        }
    }
}
