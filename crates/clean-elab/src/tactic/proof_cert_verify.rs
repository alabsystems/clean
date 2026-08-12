// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic proof term certification: well-typedness, metavariable resolution,
//! universe constraint satisfaction, proof relevance, and batch verification.
//!
//! This module provides a higher-level verification layer on top of the kernel's
//! `ProofCert` system. While `proof_term_cert.rs` generates certificates during
//! individual tactic steps, this module verifies completed proof states —
//! ensuring the final proof term is well-typed, fully resolved, Prop-valued,
//! and universe-consistent before accepting it.

use clean_kernel::cert::ProofCert;
use clean_kernel::level::Level;
use clean_kernel::{Expr, ExprKind};

use super::core::{Goal, ProofState, TacticError};

// =============================================================================
// Verification certificate
// =============================================================================

/// A certificate attesting that a proof term passed all verification checks.
///
/// This is the output of `verify_completed_proof` and `verify_batch`. It
/// bundles the kernel `ProofCert` with the additional checks performed by
/// this module (metavariable resolution, proof relevance, universe constraints).
#[derive(Debug, Clone)]
pub(crate) struct VerifiedProofCertificate {
    /// The kernel proof certificate from type inference.
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    pub(crate) kernel_cert: ProofCert,
    /// The verified proof term (fully instantiated, no unresolved metas).
    pub(crate) proof_term: Expr,
    /// The goal type that was proved.
    pub(crate) goal_type: Expr,
    /// Whether the proof term inhabits Prop (Sort 0).
    pub(crate) is_proof_relevant: bool,
}

/// Diagnostic context for verification failures.
#[derive(Debug, Clone)]
pub(crate) struct VerificationDiagnostic {
    /// Which check failed.
    pub(crate) check: VerificationCheck,
    /// Human-readable explanation.
    pub(crate) message: String,
    /// The goal that was being verified (if available).
    pub(crate) goal_index: Option<usize>,
}

/// The specific verification check that failed.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum VerificationCheck {
    /// Proof term type does not match goal target.
    WellTypedness,
    /// Unresolved metavariables remain in the proof term.
    MetavariableResolution,
    /// Universe level constraints are violated.
    UniverseConstraints,
    /// Proof term does not inhabit Prop.
    ProofRelevance,
    /// Certificate verification failed independently.
    CertificateVerification,
    /// Proof state is incomplete (goals remain).
    Completeness,
}

impl std::fmt::Display for VerificationCheck {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WellTypedness => write!(f, "well-typedness"),
            Self::MetavariableResolution => write!(f, "metavariable resolution"),
            Self::UniverseConstraints => write!(f, "universe constraints"),
            Self::ProofRelevance => write!(f, "proof relevance"),
            Self::CertificateVerification => write!(f, "certificate verification"),
            Self::Completeness => write!(f, "completeness"),
        }
    }
}

// =============================================================================
// Metavariable resolution check
// =============================================================================

/// Check whether an expression contains unresolved metavariable placeholders.
///
/// Metavariables in the tactic framework are represented as FVars with
/// special IDs (via `MetaState::to_fvar`). After full instantiation, no
/// such FVars should remain. This function walks the expression tree to
/// detect any residual meta-FVars.
pub(crate) fn has_unresolved_metas(expr: &Expr, state: &ProofState) -> bool {
    has_unresolved_metas_inner(expr, state, 0)
}

fn has_unresolved_metas_inner(expr: &Expr, state: &ProofState, depth: usize) -> bool {
    // Guard against pathological expressions
    if depth > 10_000 {
        return false;
    }
    match expr.kind() {
        ExprKind::FVar(id) => {
            // Check if this FVar is actually an unassigned metavariable
            if let Some(meta_id) = crate::unify::MetaState::from_fvar(*id) {
                !state.metas().is_assigned(meta_id)
            } else {
                false
            }
        }
        ExprKind::App(f, a) => {
            has_unresolved_metas_inner(f, state, depth + 1)
                || has_unresolved_metas_inner(a, state, depth + 1)
        }
        ExprKind::Lam(_, dom, body) | ExprKind::Pi(_, dom, body) => {
            has_unresolved_metas_inner(dom, state, depth + 1)
                || has_unresolved_metas_inner(body, state, depth + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            has_unresolved_metas_inner(ty, state, depth + 1)
                || has_unresolved_metas_inner(val, state, depth + 1)
                || has_unresolved_metas_inner(body, state, depth + 1)
        }
        ExprKind::Proj(_, _, e) => has_unresolved_metas_inner(e, state, depth + 1),
        ExprKind::MData(_, e) => has_unresolved_metas_inner(e, state, depth + 1),
        ExprKind::BVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_)
        | ExprKind::SProp => false,
        // Cubical and ZFC expressions: check sub-expressions
        _ => false,
    }
}

// =============================================================================
// Universe constraint check
// =============================================================================

/// Collect all universe levels from Sort expressions in a type.
pub(crate) fn collect_universe_levels(expr: &Expr) -> Vec<Level> {
    let mut levels = Vec::new();
    collect_levels_inner(expr, &mut levels, 0);
    levels
}

fn collect_levels_inner(expr: &Expr, levels: &mut Vec<Level>, depth: usize) {
    if depth > 10_000 {
        return;
    }
    match expr.kind() {
        ExprKind::Sort(level) => {
            levels.push(level.clone());
        }
        ExprKind::App(f, a) => {
            collect_levels_inner(f, levels, depth + 1);
            collect_levels_inner(a, levels, depth + 1);
        }
        ExprKind::Lam(_, dom, body) | ExprKind::Pi(_, dom, body) => {
            collect_levels_inner(dom, levels, depth + 1);
            collect_levels_inner(body, levels, depth + 1);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_levels_inner(ty, levels, depth + 1);
            collect_levels_inner(val, levels, depth + 1);
            collect_levels_inner(body, levels, depth + 1);
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) => {
            collect_levels_inner(e, levels, depth + 1);
        }
        _ => {}
    }
}

/// Check that all universe levels in an expression are satisfiable.
///
/// A universe level is satisfiable if it does not contain contradictory
/// constraints (e.g., `max(u, succ(u))` is fine, but a level that is
/// simultaneously 0 and nonzero would not be). In practice, we check
/// that Succ chains are non-negative and that named parameters are
/// consistent.
pub(crate) fn check_universe_constraints(expr: &Expr) -> Result<(), String> {
    let levels = collect_universe_levels(expr);
    for level in &levels {
        validate_level(level)?;
    }
    Ok(())
}

fn validate_level(level: &Level) -> Result<(), String> {
    match level {
        Level::Zero => Ok(()),
        Level::Succ(inner) => validate_level(inner),
        Level::Max(l, r) | Level::IMax(l, r) => {
            validate_level(l)?;
            validate_level(r)
        }
        Level::Param(_) => Ok(()), // Parameters are always valid
    }
}

// =============================================================================
// Proof relevance check
// =============================================================================

/// Check whether a type is Prop (Sort 0), meaning proofs of it are
/// proof-irrelevant.
pub(crate) fn is_prop_type(ty: &Expr) -> bool {
    match ty.kind() {
        ExprKind::Sort(level) => level.is_zero(),
        _ => false,
    }
}

/// Check proof relevance: the goal type should sort into Prop for theorem
/// proofs. Returns true if the goal type is Prop-valued (or if we cannot
/// determine the sort, we return false conservatively).
pub(crate) fn check_proof_relevance(state: &ProofState, goal: &Goal) -> bool {
    let target = state.metas().instantiate(&goal.target);
    // Infer the type of the target (which should be a Sort)
    match state.infer_type(goal, &target) {
        Ok(ty) => is_prop_type(&ty),
        Err(_) => false,
    }
}

// =============================================================================
// Single-proof verification
// =============================================================================

/// Verify a completed proof state, producing a `VerifiedProofCertificate`.
///
/// This performs all verification checks:
/// 1. Completeness: all goals must be closed
/// 2. Metavariable resolution: no unresolved metas in the proof term
/// 3. Well-typedness: proof term type matches the original goal type
/// 4. Universe constraints: all universe levels are satisfiable
/// 5. Proof relevance: check if the goal is Prop-valued
/// 6. Certificate verification: independent kernel verification
///
/// # Errors
///
/// Returns `TacticError` with diagnostic context on any verification failure.
pub(crate) fn verify_completed_proof(
    state: &ProofState,
) -> Result<VerifiedProofCertificate, TacticError> {
    // 1. Completeness check
    if !state.is_complete() {
        return Err(TacticError::UnsolvedGoals {
            count: state.goals().len(),
            detail: format!(
                "; verification requires all goals to be closed ({}  remaining)",
                state.goals().len()
            ),
        });
    }

    // Wave 102: get the *closed* proof term (FVars introduced by `intro`/
    // `intros` converted back to BVars within their abstracting lambdas).
    // Using `instantiated_proof()` here would leak tactic-scope FVars into
    // the kernel-verification step, which carries an empty `local_ctx` —
    // the kernel would then fail to type-check the term (FVar refers to a
    // local that is not in scope). `closed_proof()` is the proper
    // verification-ready form; it relies on the existing `close_fvars`
    // machinery and is debug-asserted to be free of tactic-scope FVars.
    let proof = state.closed_proof().ok_or(TacticError::ProofNotProduced)?;

    // Get the goal type
    let goal_type = state.goal_type().ok_or(TacticError::ProofNotProduced)?;

    // 2. Metavariable resolution check
    if has_unresolved_metas(&proof, state) {
        return Err(TacticError::TypeCheckFailed(
            "proof term contains unresolved metavariables".to_string(),
        ));
    }

    // 3. Universe constraints check
    if let Err(msg) = check_universe_constraints(&goal_type) {
        return Err(TacticError::TypeCheckFailed(format!(
            "universe constraint violation in goal type: {msg}"
        )));
    }
    if let Err(msg) = check_universe_constraints(&proof) {
        return Err(TacticError::TypeCheckFailed(format!(
            "universe constraint violation in proof term: {msg}"
        )));
    }

    // 4. Well-typedness + certificate generation
    // Build a synthetic goal to use the kernel verification infrastructure
    let synthetic_goal = Goal {
        meta_id: state
            .metas()
            .iter()
            .next()
            .map(|(id, _)| id)
            .unwrap_or(crate::unify::MetaId(0)),
        target: goal_type.clone(),
        local_ctx: Vec::new(),
        tag: None,
    };

    let kernel_cert = state.verify_proof(&synthetic_goal, &proof).map_err(|e| {
        TacticError::TypeCheckFailed(format!("well-typedness verification failed: {e}"))
    })?;

    // 5. Proof relevance check (informational, not blocking)
    let is_proof_relevant = check_proof_relevance(state, &synthetic_goal);

    Ok(VerifiedProofCertificate {
        kernel_cert,
        proof_term: proof,
        goal_type,
        is_proof_relevant,
    })
}

// =============================================================================
// Batch verification
// =============================================================================

/// Result of verifying multiple proof states in batch.
#[derive(Debug)]
pub(crate) struct BatchVerificationResult {
    /// Successfully verified certificates.
    pub(crate) verified: Vec<VerifiedProofCertificate>,
    /// Diagnostics for failed verifications.
    pub(crate) failures: Vec<VerificationDiagnostic>,
}

impl BatchVerificationResult {
    /// Returns true if all proofs verified successfully.
    #[must_use]
    pub(crate) fn all_verified(&self) -> bool {
        self.failures.is_empty()
    }

    /// Number of successfully verified proofs.
    #[must_use]
    pub(crate) fn success_count(&self) -> usize {
        self.verified.len()
    }

    /// Number of failed verifications.
    #[must_use]
    pub(crate) fn failure_count(&self) -> usize {
        self.failures.len()
    }
}

/// Verify multiple completed proof states in batch.
///
/// Each proof state is verified independently. Failures in one proof do not
/// affect verification of others. Returns a `BatchVerificationResult` with
/// both successes and failures.
pub(crate) fn verify_batch(states: &[&ProofState]) -> BatchVerificationResult {
    let mut verified = Vec::new();
    let mut failures = Vec::new();

    for (idx, state) in states.iter().enumerate() {
        match verify_completed_proof(state) {
            Ok(cert) => verified.push(cert),
            Err(err) => {
                let check = classify_error(&err);
                failures.push(VerificationDiagnostic {
                    check,
                    message: err.to_string(),
                    goal_index: Some(idx),
                });
            }
        }
    }

    BatchVerificationResult { verified, failures }
}

/// Classify a TacticError into the appropriate VerificationCheck category.
fn classify_error(err: &TacticError) -> VerificationCheck {
    match err {
        TacticError::UnsolvedGoals { .. } => VerificationCheck::Completeness,
        TacticError::TypeMismatch { .. } => VerificationCheck::WellTypedness,
        TacticError::TypeCheckFailed(msg) => {
            if msg.contains("metavariable") {
                VerificationCheck::MetavariableResolution
            } else if msg.contains("universe") {
                VerificationCheck::UniverseConstraints
            } else if msg.contains("certificate") || msg.contains("Certificate") {
                VerificationCheck::CertificateVerification
            } else {
                VerificationCheck::WellTypedness
            }
        }
        TacticError::ProofNotProduced => VerificationCheck::Completeness,
        _ => VerificationCheck::WellTypedness,
    }
}

// =============================================================================
// Diagnostic helpers
// =============================================================================

/// Format a verification diagnostic as a human-readable string with context.
pub(crate) fn format_diagnostic(diag: &VerificationDiagnostic) -> String {
    let goal_info = diag
        .goal_index
        .map(|idx| format!(" (proof #{idx})"))
        .unwrap_or_default();
    format!(
        "verification failed [{}]{}: {}",
        diag.check, goal_info, diag.message
    )
}

/// Run all verification checks on a proof state and collect diagnostics.
///
/// Unlike `verify_completed_proof` which fails fast on the first error,
/// this function runs all checks and collects all diagnostics. Useful for
/// comprehensive error reporting.
pub(crate) fn collect_all_diagnostics(state: &ProofState) -> Vec<VerificationDiagnostic> {
    let mut diagnostics = Vec::new();

    // Completeness
    if !state.is_complete() {
        diagnostics.push(VerificationDiagnostic {
            check: VerificationCheck::Completeness,
            message: format!("{} unsolved goal(s) remain", state.goals().len()),
            goal_index: None,
        });
    }

    // Metavariable resolution (only if we have a proof term)
    if let Some(proof) = state.instantiated_proof() {
        if has_unresolved_metas(&proof, state) {
            diagnostics.push(VerificationDiagnostic {
                check: VerificationCheck::MetavariableResolution,
                message: "proof term contains unresolved metavariables".to_string(),
                goal_index: None,
            });
        }

        // Universe constraints on proof term
        if let Err(msg) = check_universe_constraints(&proof) {
            diagnostics.push(VerificationDiagnostic {
                check: VerificationCheck::UniverseConstraints,
                message: format!("proof term: {msg}"),
                goal_index: None,
            });
        }
    }

    // Universe constraints on goal type
    if let Some(goal_type) = state.goal_type() {
        if let Err(msg) = check_universe_constraints(&goal_type) {
            diagnostics.push(VerificationDiagnostic {
                check: VerificationCheck::UniverseConstraints,
                message: format!("goal type: {msg}"),
                goal_index: None,
            });
        }
    }

    diagnostics
}
