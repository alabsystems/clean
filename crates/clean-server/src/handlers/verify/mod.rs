// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification handlers: verifyC, verifyProof, verifyProofBatch, verifyFile,
//! fillSorries, composeProof.
//!
//! Primary contract: docs/JSON_RPC_API.md
//! Design deltas: designs/2026-03-14-2703-server-sorry-provenance-surface.md,
//! designs/2026-03-15-2731-trusted-arith-provenance-surface.md
//! Historical origin: #79

use crate::handlers::state::ServerState;

mod compose_proof;
mod fill_sorries;
mod fill_sorries_support;
mod fill_sorries_types;
mod parse_lean;
pub(crate) mod types;
mod verify_batch;
mod verify_c;
mod verify_file;
mod verify_proof;

use clean_elab::tactic::ProofTrustLedger;
use clean_kernel::{Environment, Expr, SorrySummary, TypeChecker};
pub use compose_proof::{
    handle_compose_proof, ComposeProofParams, ComposeProofResult, SorryReplacement,
};
pub use fill_sorries::handle_fill_sorries;
#[cfg(test)]
pub(crate) use parse_lean::parse_lean_file;
pub use types::*;
pub use verify_batch::handle_verify_proof_batch;
pub use verify_c::handle_verify_c;
pub use verify_file::handle_verify_file;
pub use verify_proof::handle_verify_proof;

// ============================================================================
// Trust summary helpers
// ============================================================================

fn sorry_provenance_from_closed_proof(closed_proof: Option<&Expr>) -> Option<SorryProvenance> {
    closed_proof.map(|proof_term| {
        let summary = SorrySummary::from_expr(proof_term);
        SorryProvenance {
            has_explicit_sorry: summary.has_explicit_sorry,
            has_synthetic_sorry: summary.has_synthetic_sorry,
        }
    })
}

pub(crate) fn trust_summary_from_ledger(
    ledger: ProofTrustLedger,
    verified: bool,
    kernel_check_failures: u64,
) -> TrustSummary {
    trust_summary_from_ledger_with_closed_proof(ledger, None, verified, kernel_check_failures)
}

pub(crate) fn trust_summary_from_ledger_with_closed_proof(
    ledger: ProofTrustLedger,
    closed_proof: Option<&Expr>,
    verified: bool,
    kernel_check_failures: u64,
) -> TrustSummary {
    let ay_provenance = if ledger.trusted_ay_count == 0 {
        None
    } else {
        Some(TrustedAyProvenance {
            arithmetic_boundary_steps: ledger
                .trusted_ay_provenance
                .arithmetic_boundary_steps
                .into(),
            alethe_trust_steps: ledger.trusted_ay_provenance.alethe_trust_steps.into(),
            theory_bv_bitblast_steps: ledger.trusted_ay_provenance.theory_bv_bitblast_steps.into(),
            theory_array_axiom_steps: ledger.trusted_ay_provenance.theory_array_axiom_steps.into(),
            theory_generic_steps: ledger.trusted_ay_provenance.theory_generic_steps.into(),
            local_gap_steps: ledger.trusted_ay_provenance.local_gap_steps.into(),
            unclassified_steps: ledger.trusted_ay_provenance.unclassified_steps.into(),
        })
    };
    let arith_provenance = if ledger.trusted_arith_count == 0 {
        None
    } else {
        Some(TrustedArithProvenance {
            direct_steps: ledger.trusted_arith_provenance.direct_steps.into(),
            goal_close_helper_steps: ledger
                .trusted_arith_provenance
                .goal_close_helper_steps
                .into(),
            target_rewrite_helper_steps: ledger
                .trusted_arith_provenance
                .target_rewrite_helper_steps
                .into(),
            unclassified_steps: ledger.trusted_arith_provenance.unclassified_steps.into(),
        })
    };
    let sorry_count = ledger.sorry_count.into();
    let ay_count = ledger.trusted_ay_count.into();
    let arith_count = ledger.trusted_arith_count.into();

    let smt_recovery = if ledger.smt_recovery.has_events() {
        Some(SmtRecoverySummary {
            invalid_direct_ay_candidates: ledger.smt_recovery.invalid_direct_ay_candidates.into(),
            invalid_direct_certificate_candidates: ledger
                .smt_recovery
                .invalid_direct_certificate_candidates
                .into(),
            invalid_bridge_candidates: ledger.smt_recovery.invalid_bridge_candidates.into(),
        })
    } else {
        None
    };

    TrustSummary {
        sorry_count,
        sorry_provenance: sorry_provenance_from_closed_proof(closed_proof),
        ay_count,
        ay_provenance,
        arith_count,
        arith_provenance,
        kernel_check_failures,
        fully_verified: verified
            && sorry_count == 0
            && ay_count == 0
            && arith_count == 0
            && kernel_check_failures == 0,
        smt_recovery,
    }
}

/// Build a trust summary from the current proof state, suitable for interactive
/// endpoints (`initProofState`, `applyTactic`, `batchApplyTactic`, `getProofState`).
///
/// For unsolved states: returns aggregate counts with `fully_verified = false`.
/// For solved states: performs kernel type-check and includes sorry provenance
/// from the closed proof term, reusing the same builder that powers `extractProof`.
pub(crate) fn trust_summary_from_proof_state(
    env: &Environment,
    state: &clean_elab::tactic::ProofState,
) -> TrustSummary {
    let ledger = state.trust_ledger();

    if state.is_complete() {
        let closed_proof = state.closed_proof();
        let goal_type = state.goal_type();
        let verified = match (closed_proof.as_ref(), goal_type.as_ref()) {
            (Some(proof), Some(target)) => verify_closed_proof(env, target, Some(proof)),
            _ => false,
        };
        trust_summary_from_ledger_with_closed_proof(ledger, closed_proof.as_ref(), verified, 0)
    } else {
        trust_summary_from_ledger_with_closed_proof(ledger, None, false, 0)
    }
}

pub(crate) fn verify_closed_proof(
    env: &Environment,
    target: &Expr,
    closed_proof: Option<&Expr>,
) -> bool {
    if let Some(proof_term) = closed_proof {
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(proof_term, target).is_ok()
    } else {
        false
    }
}

pub(crate) fn verify_closed_proof_with_trust_summary(
    env: &Environment,
    target: &Expr,
    closed_proof: Option<&Expr>,
    ledger: ProofTrustLedger,
    kernel_check_failures: u64,
) -> (bool, TrustSummary) {
    let verified = verify_closed_proof(env, target, closed_proof);
    let trust_summary = trust_summary_from_ledger_with_closed_proof(
        ledger,
        closed_proof,
        verified,
        kernel_check_failures,
    );
    (verified, trust_summary)
}

pub(crate) async fn initialize_verify_file_env(
    state: &ServerState,
) -> Result<(), clean_kernel::EnvError> {
    let mut env = state.env.write().await;
    // File-level verification and sorry-filling replay Lean sketches directly,
    // so the logical prelude must exist even when no imported module has
    // forced these declarations in transitively yet.
    env.init_true_false()?;
    env.init_and()?;
    if !env.has_ring() {
        env.init_ring()?;
    }
    if !env.has_comm_ring() {
        env.init_comm_ring()?;
    }
    if !env.has_field() {
        env.init_field()?;
    }
    if !env.has_integral_domain() {
        env.init_integral_domain()?;
    }
    if !env.has_module() || !env.has_algebra() || !env.has_domain_types() {
        env.init_module_algebra_all()?;
    }
    if !env.has_prime() {
        env.init_prime()?;
    }
    if !env.has_is_principal_ideal_ring() {
        env.init_is_principal_ideal_ring()?;
    }
    if !env.has_polynomial() {
        env.init_polynomial()?;
    }
    if !env.has_ufm() {
        env.init_ufm()?;
    }
    if !env.has_associated() {
        env.init_associated()?;
    }
    Ok(())
}
