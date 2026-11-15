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
//!
//! Every handler here replays its proof on the server's work pool
//! (`handlers/work.rs`) under the request's deadline. A replay still reports
//! "timeout exceeded" in its result when it reaches a step past its timeout;
//! one the deadline interrupted inside a step answers the timeout error, and
//! nothing it computed past the deadline (goals, cached proof states) is
//! reported or kept.
//!
//! `verifyFile`, `fillSorries` and `composeProof` parse the file they are sent
//! on the pool too, under the same deadline ([`parse_on_pool`]), before they
//! set the environment up: the parse grows with the file (`parse_lean.rs`).

use crate::handlers::state::ServerState;
use crate::handlers::work::{within, WorkError};
use crate::rpc::{RequestId, Response, RpcError};
use std::time::{Duration, Instant};

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
pub(crate) use parse_lean::{
    explicit_hole_token_at, explicit_holes, first_declaration, parse_lean_file,
};
pub use types::*;
pub use verify_batch::handle_verify_proof_batch;
pub use verify_c::handle_verify_c;
pub use verify_file::handle_verify_file;
pub use verify_proof::handle_verify_proof;

// ============================================================================
// Trust summary helpers
// ============================================================================

/// The trust debt a CLOSED proof term carries, read off the term itself and
/// off its constant closure in `env`.
///
/// The tactic ledger counts only the sorries and trusted steps the tactic
/// engine created. A closed proof can carry debt the ledger never saw: `exact
/// @sorryAx _ (!true)` (a sorry the user wrote as a term), or `exact lemma1`
/// where `lemma1` rests on `sorry` or `trustedAy`. Both were reported
/// `fully_verified: true` before 2026-09-28.
struct ClosedProofDebt {
    provenance: SorryProvenance,
    /// Sorry occurrences in the term itself, or 1 when only its closure
    /// reaches `sorryAx` / `sorry`.
    sorry_count: u64,
    trusted_ay: bool,
    trusted_arith: bool,
}

fn closed_proof_debt(env: &Environment, proof_term: &Expr) -> ClosedProofDebt {
    let own = SorrySummary::from_expr(proof_term);
    let markers =
        clean_kernel::env::DomainAxiomClosure::new().trust_markers_of_expr(env, proof_term);
    let closure_sorry = markers.iter().any(clean_kernel::is_sorry_marker);
    let own_occurrences = u64::try_from(proof_term.count_sorry_occurrences()).unwrap_or(u64::MAX);
    ClosedProofDebt {
        provenance: SorryProvenance {
            // A sorry reached only through a cited constant is non-synthetic
            // by construction: the elaborator mints its synthetic sorries in
            // place.
            has_explicit_sorry: own.has_explicit_sorry || (closure_sorry && !own.has_sorry),
            has_synthetic_sorry: own.has_synthetic_sorry,
        },
        sorry_count: own_occurrences.max(u64::from(closure_sorry)),
        trusted_ay: markers.iter().any(|m| m.to_string() == "trustedAy"),
        trusted_arith: markers.iter().any(|m| m.to_string() == "trustedArith"),
    }
}

pub(crate) fn trust_summary_from_ledger(
    ledger: ProofTrustLedger,
    verified: bool,
    kernel_check_failures: u64,
) -> TrustSummary {
    trust_summary_core(ledger, None, verified, kernel_check_failures)
}

/// The trust summary of a finished proof: the ledger's counters, raised to
/// whatever the closed proof term's own occurrences and its constant closure
/// in `env` show (see [`closed_proof_debt`]).
pub(crate) fn trust_summary_from_ledger_with_closed_proof(
    env: &Environment,
    ledger: ProofTrustLedger,
    closed_proof: Option<&Expr>,
    verified: bool,
    kernel_check_failures: u64,
) -> TrustSummary {
    let debt = closed_proof.map(|proof_term| closed_proof_debt(env, proof_term));
    trust_summary_core(ledger, debt, verified, kernel_check_failures)
}

fn trust_summary_core(
    ledger: ProofTrustLedger,
    closed_proof_debt: Option<ClosedProofDebt>,
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
    let mut sorry_count: u64 = ledger.sorry_count.into();
    let mut ay_count: u64 = ledger.trusted_ay_count.into();
    let mut arith_count: u64 = ledger.trusted_arith_count.into();
    let sorry_provenance = closed_proof_debt.map(|debt| {
        sorry_count = sorry_count.max(debt.sorry_count);
        if debt.trusted_ay {
            ay_count = ay_count.max(1);
        }
        if debt.trusted_arith {
            arith_count = arith_count.max(1);
        }
        debt.provenance
    });

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
        sorry_provenance,
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
        trust_summary_from_ledger_with_closed_proof(env, ledger, closed_proof.as_ref(), verified, 0)
    } else {
        trust_summary_from_ledger(ledger, false, 0)
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
        env,
        ledger,
        closed_proof,
        verified,
        kernel_check_failures,
    );
    (verified, trust_summary)
}

/// Set the shared environment up for a file's replay: seed the logical
/// prelude it needs ([`seed_verify_file_env`]) where it is missing, on the
/// work pool (`SharedEnv::seed`: the kernel copies the whole environment for
/// each inductive it adds). Counted as a change only when it added something:
/// an environment that has the prelude already leaves a writer's copy current
/// (`shared_env.rs`). Not charged to the request's timeout, and its waits for
/// a slot and for the environment are not either (`docs/JSON_RPC_API.md`).
pub(crate) async fn initialize_verify_file_env(state: &ServerState) -> Result<(), String> {
    match state.env.seed(&state.work, seed_verify_file_env).await {
        Ok(seeded) => seeded.map_err(|error| error.to_string()),
        Err(WorkError::Unavailable(detail)) => Err(detail),
        // It runs with no deadline.
        Err(WorkError::Interrupted) => Err("the set-up was interrupted".to_string()),
    }
}

/// The logical prelude a file's replay needs, each piece added only when it
/// is missing.
fn seed_verify_file_env(env: &mut Environment) -> Result<(), clean_kernel::EnvError> {
    // Each inductive it adds copies the whole environment: work for the pool,
    // never for a runtime worker. Tests build with debug assertions, so a
    // request path that brings it back to the runtime fails every test that
    // takes it.
    debug_assert!(
        tokio::runtime::Handle::try_current().is_err(),
        "the verify family's environment was seeded on an async runtime's thread"
    );
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

/// Parse a request's file on the work pool, under the request's deadline
/// (`start` + `timeout`) and inside its timeout: the timeout error when it
/// fires first. The parse takes a slot of its own, holding no lock, and gives
/// it back before the request sets the environment up. A file is up to the
/// transport's 10 MiB, and parsing it is not linear (`parse_lean.rs`): until
/// R87 (2026-10-17) it ran on the runtime, with no deadline.
pub(crate) async fn parse_on_pool<T: Send + 'static>(
    state: &ServerState,
    start: Instant,
    timeout: Duration,
    parse: impl FnOnce() -> T + Send + 'static,
) -> Result<T, WorkError> {
    within(
        timeout.saturating_sub(start.elapsed()),
        state.work.run(start.checked_add(timeout), parse),
    )
    .await
}

/// The response to a replay that ran on the work pool: its result, or the
/// timeout error when the request's deadline interrupted it.
pub(crate) fn replay_response<T: serde::Serialize>(
    id: RequestId,
    timeout: Duration,
    outcome: Result<T, WorkError>,
) -> Response {
    match outcome {
        Ok(result) => Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string()))),
        Err(WorkError::Interrupted) => {
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
        Err(WorkError::Unavailable(detail)) => {
            Response::error(id, RpcError::internal_error(detail))
        }
    }
}
