// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Response builders for the `prove` JSON-RPC endpoint.

use super::helpers::format_expr;
use super::types::{ProveResult, ProveStatus};
use super::verify::trust_summary_from_ledger_with_closed_proof;
use clean_auto::bridge::SmtVerificationResult;
use clean_auto::{AutomationOutcome, AutomationSource};
use clean_elab::tactic::{
    ProofTrustLedger, TrustedArithProvenanceLedger, TrustedAyProvenanceLedger,
};
use clean_kernel::env::DeclarationTrustSummary;
use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::{Environment, Expr, ExprKind, TypeChecker};

fn saturating_trust_count(count: usize, label: &'static str) -> u32 {
    match u32::try_from(count) {
        Ok(count) => count,
        Err(_) => {
            tracing::warn!(
                label,
                count,
                "prove trust count exceeded u32 range; saturating response summary"
            );
            u32::MAX
        }
    }
}

fn count_sorry_terms(expr: &Expr) -> u32 {
    fn push_zfc_children<'a>(stack: &mut Vec<&'a Expr>, set_expr: &'a ZFCSetExpr) {
        match set_expr {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
            ZFCSetExpr::Singleton(expr)
            | ZFCSetExpr::Union(expr)
            | ZFCSetExpr::PowerSet(expr)
            | ZFCSetExpr::Choice(expr) => stack.push(expr.as_ref()),
            ZFCSetExpr::Pair(left, right) => {
                stack.push(left.as_ref());
                stack.push(right.as_ref());
            }
            ZFCSetExpr::Separation { set, pred } | ZFCSetExpr::Replacement { set, func: pred } => {
                stack.push(set.as_ref());
                stack.push(pred.as_ref());
            }
        }
    }

    let mut total = 0u32;
    let mut stack = vec![expr];
    while let Some(curr) = stack.pop() {
        let is_sorry_term = matches!(curr.kind(), ExprKind::App(_, _)) && curr.is_sorry();
        total = total.saturating_add(u32::from(is_sorry_term));

        match curr.kind() {
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(_, _)
            | ExprKind::Lit(_)
            | ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => {}
            ExprKind::App(fun, arg) => {
                stack.push(fun.as_ref());
                stack.push(arg.as_ref());
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty.as_ref());
                stack.push(body.as_ref());
            }
            ExprKind::Let(_, ty, value, body, _) => {
                stack.push(ty.as_ref());
                stack.push(value.as_ref());
                stack.push(body.as_ref());
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                stack.push(inner.as_ref());
            }
            ExprKind::CubicalPath { ty, left, right } => {
                stack.push(ty.as_ref());
                stack.push(left.as_ref());
                stack.push(right.as_ref());
            }
            ExprKind::CubicalPathLam { body } => stack.push(body.as_ref()),
            ExprKind::CubicalPathApp { path, arg } => {
                stack.push(path.as_ref());
                stack.push(arg.as_ref());
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                stack.push(ty.as_ref());
                stack.push(phi.as_ref());
                stack.push(u.as_ref());
                stack.push(base.as_ref());
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                stack.push(ty.as_ref());
                stack.push(phi.as_ref());
                stack.push(base.as_ref());
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                stack.push(ty.as_ref());
                stack.push(r.as_ref());
                stack.push(s.as_ref());
                stack.push(base.as_ref());
            }
            ExprKind::ZFCSet(set_expr) => push_zfc_children(&mut stack, set_expr),
            ExprKind::ZFCMem { element, set } => {
                stack.push(element.as_ref());
                stack.push(set.as_ref());
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                stack.push(domain.as_ref());
                stack.push(pred.as_ref());
            }
        }
    }

    total
}

fn trust_ledger_from_closed_proof(proof_term: &Expr) -> ProofTrustLedger {
    let trust = DeclarationTrustSummary::from_expr(proof_term);
    let trusted_ay_count = saturating_trust_count(trust.trusted_ay_count, "trustedAy");
    let trusted_arith_count = saturating_trust_count(trust.trusted_arith_count, "trustedArith");

    ProofTrustLedger {
        sorry_count: count_sorry_terms(proof_term),
        trusted_ay_count,
        trusted_ay_provenance: TrustedAyProvenanceLedger {
            unclassified_steps: trusted_ay_count,
            ..TrustedAyProvenanceLedger::default()
        },
        trusted_arith_count,
        trusted_arith_provenance: TrustedArithProvenanceLedger {
            unclassified_steps: trusted_arith_count,
            ..TrustedArithProvenanceLedger::default()
        },
        smt_recovery: Default::default(),
    }
}

pub(crate) fn build_verified_prove_result(
    env: &Environment,
    goal: &Expr,
    proof_term: &Expr,
    proof_sketch: &str,
) -> ProveResult {
    let trust_ledger = trust_ledger_from_closed_proof(proof_term);
    let verified = TypeChecker::with_mode(env, env.mode())
        .check_type(proof_term, goal)
        .is_ok();
    let trust_summary =
        trust_summary_from_ledger_with_closed_proof(trust_ledger, Some(proof_term), verified, 0);

    // SOUNDNESS: `status` MUST follow the kernel re-check computed above. The
    // `Verified` variant is documented as "a kernel-checkable proof term was
    // produced"; reporting it when `check_type` rejected the term would make the
    // `prove` oracle lie (previously only `trust_summary.fully_verified` reflected
    // the failure). On rejection, surface the term + failing trust_summary under
    // `KernelRejected` so a client keying on `status` is never told "Verified".
    let (status, reason) = if verified {
        (ProveStatus::Verified, None)
    } else {
        (
            ProveStatus::KernelRejected,
            Some(
                "proof term failed kernel re-check: check_type rejected it against the goal"
                    .to_string(),
            ),
        )
    };

    ProveResult {
        found: true,
        proof_term: Some(format_expr(proof_term)),
        proof_sketch: Some(proof_sketch.to_string()),
        method: Some("smt".to_string()),
        status,
        reason,
        trust_summary: Some(trust_summary),
        time_ms: 0,
        time_ns: None,
    }
}

pub(crate) fn prove_result_from_smt_verification(
    env: &Environment,
    goal: &Expr,
    result: SmtVerificationResult,
) -> ProveResult {
    match result {
        SmtVerificationResult::Verified(proof_result) => build_verified_prove_result(
            env,
            goal,
            proof_result.proof_term(),
            proof_result.proof_sketch(),
        ),
        SmtVerificationResult::Unverified { reason, .. } => ProveResult {
            found: true,
            proof_term: None,
            proof_sketch: Some("SMT proved goal but proof reconstruction unavailable".into()),
            method: Some("smt_unverified".to_string()),
            status: ProveStatus::Unverified,
            reason: Some(reason.to_string()),
            trust_summary: None,
            time_ms: 0,
            time_ns: None,
        },
        SmtVerificationResult::Refuted(_) => ProveResult {
            found: false,
            proof_term: None,
            proof_sketch: None,
            method: None,
            status: ProveStatus::Refuted,
            reason: None,
            trust_summary: None,
            time_ms: 0,
            time_ns: None,
        },
        SmtVerificationResult::Unknown(reason) => ProveResult {
            found: false,
            proof_term: None,
            proof_sketch: None,
            method: None,
            status: ProveStatus::Unknown,
            reason: Some(reason),
            trust_summary: None,
            time_ms: 0,
            time_ns: None,
        },
        _ => ProveResult {
            found: false,
            proof_term: None,
            proof_sketch: None,
            method: None,
            status: ProveStatus::Unknown,
            reason: None,
            trust_summary: None,
            time_ms: 0,
            time_ns: None,
        },
    }
}

fn source_method_name(source: AutomationSource) -> &'static str {
    match source {
        AutomationSource::Smt => "smt",
        AutomationSource::Superposition => "superposition",
        AutomationSource::Oracle => "oracle",
    }
}

/// Convert an [`AutomationOutcome`] from the full cascade into a [`ProveResult`].
///
/// This is the primary response builder for the `prove` endpoint now that it
/// uses [`AutomationEngine`] instead of a bare `SmtBridge`.
pub(crate) fn prove_result_from_automation_outcome(
    env: &Environment,
    goal: &Expr,
    outcome: AutomationOutcome,
) -> ProveResult {
    match outcome {
        AutomationOutcome::Verified(proof_result) => {
            // Detect which strategy produced the proof from the proof text.
            let method = if proof_result.proof_text().contains("superposition") {
                "superposition"
            } else if proof_result.proof_text().contains("oracle") {
                "oracle"
            } else {
                "smt"
            };

            let mut result = build_verified_prove_result(
                env,
                goal,
                proof_result.proof_term(),
                proof_result.proof_text(),
            );
            result.method = Some(method.to_string());
            result
        }
        AutomationOutcome::Unverified {
            reason,
            source,
            time_ms: _,
        } => ProveResult {
            found: true,
            proof_term: None,
            proof_sketch: Some(format!(
                "{} proved goal but proof reconstruction unavailable",
                source_method_name(source)
            )),
            method: Some(format!("{}_unverified", source_method_name(source))),
            status: ProveStatus::Unverified,
            reason: Some(reason),
            trust_summary: None,
            time_ms: 0,
            time_ns: None,
        },
        AutomationOutcome::Refuted {
            source: _,
            time_ms: _,
        } => ProveResult {
            found: false,
            proof_term: None,
            proof_sketch: None,
            method: None,
            status: ProveStatus::Refuted,
            reason: None,
            trust_summary: None,
            time_ms: 0,
            time_ns: None,
        },
        AutomationOutcome::Unknown {
            reason,
            source: _,
            time_ms: _,
        } => ProveResult {
            found: false,
            proof_term: None,
            proof_sketch: None,
            method: None,
            status: ProveStatus::Unknown,
            reason: Some(reason),
            trust_summary: None,
            time_ms: 0,
            time_ns: None,
        },
        // AutomationOutcome is #[non_exhaustive]; treat unknown future variants as Unknown.
        _ => ProveResult {
            found: false,
            proof_term: None,
            proof_sketch: None,
            method: None,
            status: ProveStatus::Unknown,
            reason: None,
            trust_summary: None,
            time_ms: 0,
            time_ns: None,
        },
    }
}
