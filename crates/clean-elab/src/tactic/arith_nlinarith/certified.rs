// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certified replay helper for `nlinarith`.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId};

use super::super::arith_linarith::{
    build_linarith_proof, extract_certified_linear_constraints, fourier_motzkin_check_certified,
    CertifiedConstraint, FMCertifiedResult, LinarithCertificate,
};
use super::super::{by_contra, decide, Goal, ProofState};
use super::synthetic_rows::{build_synthetic_row_decls, SyntheticRowDecl};
use super::NlinarithConfig;
use crate::tactic::arith_push_neg::{match_le, match_lt, match_not};
use crate::tactic::hypothesis::collect_fvars;
use crate::tactic::tc_app::{nat_le_tc, nat_lt_tc};
use crate::tactic::LinearConstraint;

#[derive(Debug, Clone)]
struct ByContradictionReplay {
    negated_goal_fvar: FVarId,
    negated_goal_ty: Expr,
    original_target: Expr,
}

#[derive(Debug, Clone)]
enum ReplayWrapper {
    Direct,
    ByContradiction(Box<ByContradictionReplay>),
}

type ReplayCertificate = (
    Goal,
    LinarithCertificate,
    Vec<FVarId>,
    Vec<SyntheticRowDecl>,
    ReplayWrapper,
);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CertifiedNlinarithOutcome {
    Closed,
    NoCertifiedContradiction,
    CertifiedUnsatNoKernelProof { reason: String },
}

enum ReplayFinalizationMode {
    Normal,
    #[cfg(test)]
    ForceNoKernelProof(&'static str),
}

fn inline_synthetic_rows(mut proof: Expr, replay_rows: &[SyntheticRowDecl]) -> Expr {
    for replay_row in replay_rows.iter().rev() {
        proof = proof.subst_fvar(replay_row.decl.fvar, &replay_row.proof_value);
    }
    proof
}

fn has_uninlined_replay_rows(proof: &Expr, replay_rows: &[SyntheticRowDecl]) -> bool {
    let proof_fvars = collect_fvars(proof);
    replay_rows
        .iter()
        .any(|replay_row| proof_fvars.contains(&replay_row.decl.fvar))
}

fn wrap_certified_replay_proof(
    proof: Expr,
    replay_rows: &[SyntheticRowDecl],
    wrapper: &ReplayWrapper,
) -> Option<Expr> {
    let inlined = inline_synthetic_rows(proof, replay_rows);
    if has_uninlined_replay_rows(&inlined, replay_rows) {
        return None;
    }

    match wrapper {
        ReplayWrapper::Direct => Some(inlined),
        ReplayWrapper::ByContradiction(replay) => {
            let body = inlined.abstract_fvar(replay.negated_goal_fvar);
            if collect_fvars(&body).contains(&replay.negated_goal_fvar) {
                return None;
            }

            let body = Expr::lam(BinderInfo::Default, replay.negated_goal_ty.clone(), body);
            Some(Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Classical.byContradiction"), vec![]),
                    replay.original_target.clone(),
                ),
                body,
            ))
        }
    }
}

fn build_negated_goal_row_decl(
    state: &mut ProofState,
    goal: &Goal,
    negated_goal_fvar: FVarId,
    negated_goal_ty: &Expr,
) -> Option<SyntheticRowDecl> {
    let negated_goal = match_not(negated_goal_ty)?;
    let (rewritten_ty, rewrite_iff) = if let Some((ty, lhs, rhs)) = match_lt(&negated_goal) {
        if !matches!(ty.kind(), clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Nat"))
        {
            return None;
        }
        (
            nat_le_tc(rhs.clone(), lhs.clone()),
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("Nat.not_lt"), vec![]), lhs),
                rhs,
            ),
        )
    } else if let Some((ty, lhs, rhs)) = match_le(&negated_goal) {
        if !matches!(ty.kind(), clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Nat"))
        {
            return None;
        }
        (
            nat_lt_tc(rhs.clone(), lhs.clone()),
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("Nat.not_le"), vec![]), lhs),
                rhs,
            ),
        )
    } else {
        return None;
    };

    let proof_value = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Iff.mp"), vec![]),
                negated_goal_ty.clone(),
            ),
            rewritten_ty.clone(),
        ),
        rewrite_iff,
    );
    let proof_value = Expr::app(proof_value, Expr::fvar(negated_goal_fvar));
    let inferred_ty = state.infer_type(goal, &proof_value).ok()?;
    if !state.is_def_eq(goal, &inferred_ty, &rewritten_ty) {
        return None;
    }

    let fvar = state.fresh_fvar();
    let decl = crate::tactic::LocalDecl {
        fvar,
        name: format!("nlinarith_goal_row_{}", fvar.as_u64()),
        ty: rewritten_ty,
        value: Some(proof_value.clone()),
    };
    Some(SyntheticRowDecl { decl, proof_value })
}

fn build_replay_context(
    state: &ProofState,
    goal: &Goal,
    config: &NlinarithConfig,
) -> Option<(ProofState, Goal, Vec<SyntheticRowDecl>, ReplayWrapper)> {
    let mut scratch_state = state.clone();
    let mut scratch_goal = goal.clone();
    let mut replay_rows = Vec::new();
    let mut wrapper = ReplayWrapper::Direct;

    let mut contradiction_state = state.clone();
    if by_contra(&mut contradiction_state, "nlinarith_not_goal").is_ok() {
        if let Some(mut contradiction_goal) = contradiction_state.current_goal().cloned() {
            if let Some(negated_goal_decl) = contradiction_goal.local_ctx.last().cloned() {
                if let Some(goal_row_decl) = build_negated_goal_row_decl(
                    &mut contradiction_state,
                    &contradiction_goal,
                    negated_goal_decl.fvar,
                    &negated_goal_decl.ty,
                ) {
                    contradiction_goal
                        .local_ctx
                        .push(goal_row_decl.decl.clone());
                    replay_rows.push(goal_row_decl);
                    scratch_state = contradiction_state;
                    scratch_goal = contradiction_goal;
                    wrapper = ReplayWrapper::ByContradiction(Box::new(ByContradictionReplay {
                        negated_goal_fvar: negated_goal_decl.fvar,
                        negated_goal_ty: negated_goal_decl.ty,
                        original_target: goal.target.clone(),
                    }));
                }
            }
        }
    }

    let mut synthetic_rows = build_synthetic_row_decls(&mut scratch_state, &scratch_goal, config);
    if let Some((base_constraints, _var_map, _hypothesis_fvars)) =
        extract_certified_linear_constraints(&scratch_state, &scratch_goal)
    {
        let max_added = config
            .max_constraints
            .saturating_sub(base_constraints.len());
        synthetic_rows.truncate(max_added);
    }

    for synthetic_row in &synthetic_rows {
        scratch_goal.local_ctx.push(synthetic_row.decl.clone());
    }
    replay_rows.extend(synthetic_rows);

    Some((scratch_state, scratch_goal, replay_rows, wrapper))
}

fn normalize_replay_certificate(
    certified_constraints: &[CertifiedConstraint],
    certificate: &mut LinarithCertificate,
) {
    let hypothesis_count = certificate
        .coefficients
        .len()
        .saturating_sub(1)
        .min(certified_constraints.len());

    for source_idx in 0..hypothesis_count {
        let source_coeff = certificate.coefficients[source_idx];
        if source_coeff <= 1 {
            continue;
        }

        let Ok(scale_factor) = i64::try_from(source_coeff) else {
            continue;
        };

        let LinearConstraint::Le(source_expr) = &certified_constraints[source_idx].constraint
        else {
            continue;
        };

        let Some(scaled_expr) = source_expr.try_scale(scale_factor) else {
            continue;
        };

        let Some(scaled_idx) = (0..hypothesis_count).find(|&candidate_idx| {
            candidate_idx != source_idx
                && matches!(
                    &certified_constraints[candidate_idx].constraint,
                    LinearConstraint::Le(candidate_expr) if candidate_expr == &scaled_expr
                )
        }) else {
            continue;
        };

        certificate.coefficients[source_idx] = 0;
        certificate.coefficients[scaled_idx] += 1;
    }
}

#[cfg(test)]
pub(crate) fn build_certified_nlinarith_replay_context(
    state: &ProofState,
    goal: &Goal,
    config: &NlinarithConfig,
) -> Option<(Goal, Vec<SyntheticRowDecl>)> {
    let (_scratch_state, scratch_goal, replay_rows, _wrapper) =
        build_replay_context(state, goal, config)?;
    Some((scratch_goal, replay_rows))
}

fn certified_nlinarith_replay_certificate(
    state: &ProofState,
    goal: &Goal,
    config: &NlinarithConfig,
) -> Option<ReplayCertificate> {
    let (scratch_state, scratch_goal, replay_rows, wrapper) =
        build_replay_context(state, goal, config)?;

    let (certified_constraints, _var_map, hypothesis_fvars) =
        extract_certified_linear_constraints(&scratch_state, &scratch_goal)?;

    match fourier_motzkin_check_certified(&certified_constraints) {
        FMCertifiedResult::Unsat(mut certificate) => {
            normalize_replay_certificate(&certified_constraints, &mut certificate);
            Some((
                scratch_goal,
                certificate,
                hypothesis_fvars,
                replay_rows,
                wrapper,
            ))
        }
        FMCertifiedResult::Sat | FMCertifiedResult::Unknown => None,
    }
}

#[cfg(test)]
pub(crate) fn build_certified_nlinarith_proof(
    state: &ProofState,
    goal: &Goal,
    config: &NlinarithConfig,
) -> Option<Expr> {
    let (scratch_goal, certificate, hypothesis_fvars, replay_rows, wrapper) =
        certified_nlinarith_replay_certificate(state, goal, config)?;
    let proof = build_linarith_proof(state, &scratch_goal, &certificate, &hypothesis_fvars)?;
    wrap_certified_replay_proof(proof, &replay_rows, &wrapper)
}

fn finish_certified_nlinarith_replay(
    state: &mut ProofState,
    goal: &Goal,
    replay: ReplayCertificate,
    mode: ReplayFinalizationMode,
) -> CertifiedNlinarithOutcome {
    let (scratch_goal, certificate, hypothesis_fvars, replay_rows, wrapper) = replay;
    match mode {
        ReplayFinalizationMode::Normal => {}
        #[cfg(test)]
        ReplayFinalizationMode::ForceNoKernelProof(reason) => {
            return CertifiedNlinarithOutcome::CertifiedUnsatNoKernelProof {
                reason: reason.to_string(),
            };
        }
    }

    if let Some(proof) = build_linarith_proof(state, &scratch_goal, &certificate, &hypothesis_fvars)
    {
        if let Some(proof) = wrap_certified_replay_proof(proof, &replay_rows, &wrapper) {
            if state.close_goal(goal, proof).is_ok() {
                return CertifiedNlinarithOutcome::Closed;
            }
            tracing::debug!(
                "nlinarith: certified replay proof constructed but close_goal rejected"
            );
        } else {
            tracing::debug!("nlinarith: wrap_certified_replay_proof returned None");
        }
    } else {
        tracing::debug!("nlinarith: build_linarith_proof returned None for certified FM");
    }

    if decide(state).is_ok() {
        return CertifiedNlinarithOutcome::Closed;
    }

    CertifiedNlinarithOutcome::CertifiedUnsatNoKernelProof {
        reason: "replay and decide both failed".to_string(),
    }
}

/// Try certified nlinarith: extract certified constraints, augment with
/// synthetic product rows, run certified FM, and replay the resulting
/// certificate through the linarith proof builder.
///
/// Returns whether certified replay closed the goal, found nothing, or found a
/// certified contradiction that still lacks a kernel-valid proof.
pub(crate) fn try_certified_nlinarith(
    state: &mut ProofState,
    goal: &Goal,
    config: &NlinarithConfig,
) -> CertifiedNlinarithOutcome {
    let replay = match certified_nlinarith_replay_certificate(state, goal, config) {
        Some(replay) => replay,
        None => return CertifiedNlinarithOutcome::NoCertifiedContradiction,
    };
    finish_certified_nlinarith_replay(state, goal, replay, ReplayFinalizationMode::Normal)
}

#[cfg(test)]
pub(crate) fn force_certified_nlinarith_no_kernel_proof(
    state: &mut ProofState,
    goal: &Goal,
    config: &NlinarithConfig,
) -> CertifiedNlinarithOutcome {
    let replay = match certified_nlinarith_replay_certificate(state, goal, config) {
        Some(replay) => replay,
        None => return CertifiedNlinarithOutcome::NoCertifiedContradiction,
    };
    finish_certified_nlinarith_replay(
        state,
        goal,
        replay,
        ReplayFinalizationMode::ForceNoKernelProof("test-only forced fail-closed outcome"),
    )
}
