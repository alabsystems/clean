// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LLM Integration API - Proof State Management
//!
//! Handlers for interactive tactic-based proof construction,
//! designed for LLM-guided theorem proving.
//!
//! Primary contract: docs/reference/proof-state-serialization.md
//! Design deltas: designs/2026-03-14-2716-interactive-trust-summary-surface.md,
//! designs/2026-03-15-2285-pantograph-resume-token-contract.md
//! Historical origin: #73

use super::types::ns_from_us;
use crate::proof_state;
use crate::rpc::{RequestId, Response, RpcError};
use clean_elab::{elaborate, tactic as elab_tactic};
use clean_kernel::Expr;
use clean_math_project::KERNEL_PROOF_EVIDENCE_SCHEMA_VERSION;
use clean_parser::parse_expr_with_tactics_exact;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::time::Instant;
use tracing::instrument;

use super::state::ServerState;
pub use clean_elab::tactic::execute_simple_tactic;

// ============================================================================
// Request/Response Types
// ============================================================================

/// Initialize proof state request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct InitProofStateParams {
    /// Theorem to prove (Lean expression syntax for the type)
    pub theorem: String,
    /// Optional problem identifier (for tracking)
    #[serde(default)]
    pub problem_id: Option<String>,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Initialize proof state response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InitProofStateResult {
    /// State identifier for subsequent operations
    pub state_id: String,
    /// Initial goals
    pub goals: Vec<proof_state::ApiGoal>,
    /// Whether already solved (trivially true)
    pub is_solved: bool,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
    /// Trust-filtered Mathverse Library candidates for the initial proof state.
    #[serde(default)]
    pub mathverse_candidates: Vec<proof_state::MathverseCandidate>,
    /// Live trust summary for the initial proof state (#2716).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<super::TrustSummary>,
}

/// Apply tactic request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct ApplyTacticParams {
    /// State to apply tactic to
    pub state_id: String,
    /// Goal to focus on
    pub goal_id: String,
    /// Tactic to apply (Lean tactic syntax)
    pub tactic: String,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Get proof state request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct GetProofStateParams {
    /// State to retrieve
    pub state_id: String,
    /// Output format: "llm", "full", or "compact"
    #[serde(default)]
    pub format: proof_state::OutputFormat,
}

/// Search request scoped to one cached proof-state goal.
#[derive(Debug, Clone, Deserialize)]
pub struct ProofStateGoalSearchParams {
    /// State to search from
    pub state_id: String,
    /// Goal to focus on
    pub goal_id: String,
}

/// Explain a failed attempt request.
#[derive(Debug, Clone, Deserialize)]
pub struct ExplainFailureParams {
    /// Attempt identifier returned by a tactic lifecycle call.
    pub attempt_id: String,
}

/// Close proof-state request parameters.
#[derive(Debug, Clone, Deserialize)]
pub struct CloseProofStateParams {
    /// State to close.
    pub state_id: String,
}

/// Close proof-state response.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CloseProofStateResult {
    pub state_id: String,
    pub closed: bool,
}

/// Retain proof-state request parameters.
#[derive(Debug, Clone, Deserialize)]
pub struct RetainProofStateParams {
    /// State to retain.
    pub state_id: String,
    /// Optional replacement TTL in seconds.
    #[serde(default)]
    pub ttl_sec: Option<u64>,
}

/// Retain proof-state response.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetainProofStateResult {
    pub state_id: String,
    pub retained: bool,
    pub lifecycle: proof_state::ProofStateLifecycleMetadata,
}

/// Extract proof request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct ExtractProofParams {
    /// State to extract proof from
    pub state_id: String,
    /// Format: "term", "tactic_script", or "certificate"
    #[serde(default = "default_proof_format")]
    pub format: String,
}

/// Parameters for `proofState.openObligation`.
pub type OpenObligationParams = proof_state::OpenObligationRequest;

fn default_proof_format() -> String {
    "term".to_string()
}

/// Batch apply tactic request parameters
#[derive(Debug, Clone, Deserialize)]
pub struct BatchApplyTacticParams {
    /// List of tactic applications
    pub items: Vec<BatchTacticItem>,
    /// Number of threads to use (default: number of CPUs)
    pub threads: Option<usize>,
    /// Global timeout in milliseconds (for entire batch)
    pub timeout_ms: Option<u64>,
}

/// Individual tactic application in a batch
#[derive(Debug, Clone, Deserialize)]
pub struct BatchTacticItem {
    /// Client-assigned identifier for this item
    pub id: String,
    /// State to apply tactic to
    pub state_id: String,
    /// Goal to focus on
    pub goal_id: String,
    /// Tactic to apply
    pub tactic: String,
}

/// Batch apply tactic response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchApplyTacticResult {
    /// Results for each item (in same order as input)
    pub results: Vec<BatchTacticItemResult>,
    /// Aggregate statistics
    pub stats: BatchTacticStats,
}

/// Theorem-search response for a cached proof-state goal.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchTheoremsResult {
    pub state_id: String,
    pub goal_id: String,
    pub domain_profile: proof_state::ObligationDomainProfile,
    pub candidates: Vec<proof_state::RelevantLemma>,
    #[serde(default)]
    pub mathverse_candidates: Vec<proof_state::MathverseCandidate>,
    pub time_us: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Tactic-search response for a cached proof-state goal.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchTacticsResult {
    pub state_id: String,
    pub goal_id: String,
    pub domain_profile: proof_state::ObligationDomainProfile,
    pub tactics: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub search_hints: Vec<String>,
    pub time_us: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Failure-explanation response.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExplainFailureResult {
    pub attempt_id: String,
    pub status: String,
    pub explanation: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub blockers: Vec<FailureBlocker>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub suggestions: Vec<String>,
}

/// Structured blocker reported for a failed tactic attempt.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FailureBlocker {
    pub kind: String,
    pub code: proof_state::TacticErrorCode,
    pub message: String,
    pub state_id: String,
    pub goal_id: String,
    pub tactic: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub failed_constraints: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub trace: Vec<String>,
}

/// Result for a single tactic in a batch
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchTacticItemResult {
    /// Client-assigned identifier (echoed from input)
    pub id: String,
    /// Whether the tactic succeeded
    pub success: bool,
    /// New state ID (only if success)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub new_state_id: Option<String>,
    /// New goals (only if success)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub new_goals: Vec<proof_state::ApiGoal>,
    /// Whether the proof is now complete
    pub is_solved: bool,
    /// Error information (only if failed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<proof_state::TacticApiError>,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
    /// Trust-filtered Mathverse Library candidates for this item's resulting state.
    #[serde(default)]
    pub mathverse_candidates: Vec<proof_state::MathverseCandidate>,
    /// Live trust summary for the proof state after this tactic (#2716).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<super::TrustSummary>,
}

/// Aggregate statistics for batch tactic application
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchTacticStats {
    /// Total number of items
    pub total: usize,
    /// Number of successful applications
    pub succeeded: usize,
    /// Number of failed applications
    pub failed: usize,
    /// Number of proofs completed (solved)
    pub solved: usize,
    /// Total wall time in microseconds
    pub wall_time_us: u64,
    /// Total wall time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub wall_time_ns: Option<u64>,
}

/// Extract proof response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExtractProofResult {
    /// Whether the proof is complete
    pub is_solved: bool,
    /// Proof term (if format = "term")
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_term: Option<String>,
    /// Proof term as a serialized kernel `Expr` (if format includes "certificate")
    ///
    /// This is useful for passing directly to `verifyCert` together with the returned certificate.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_expr: Option<Expr>,
    /// Tactic script (if format = "tactic_script")
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tactic_script: Option<Vec<String>>,
    /// Certificate (if format = "certificate")
    #[serde(skip_serializing_if = "Option::is_none")]
    pub certificate: Option<serde_json::Value>,
    /// Verification result
    pub verification: ProofVerification,
    /// Axiom usage summary
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<super::TrustSummary>,
}

/// Proof verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofVerification {
    /// Whether the proof verifies
    pub verified: bool,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Kernel evidence emitted only after `extractProof` has regenerated a kernel
/// certificate and checked the closed proof against the proof-state target.
#[derive(Debug, Clone, Serialize)]
pub struct KernelProofExtractionEvidence {
    pub schema_version: &'static str,
    pub theorem: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub project: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub obligation: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub linked_obligations: Vec<String>,
    pub proof_hash: String,
    pub target_hash: String,
    pub checker: &'static str,
    pub source: &'static str,
    pub checked: bool,
    pub kernel_verification: ProofVerification,
    pub trust_summary: super::TrustSummary,
    pub checked_proof_expr: Expr,
    pub checked_target_expr: Expr,
    pub proof_certificate: serde_json::Value,
}

// ============================================================================
// Handlers
// ============================================================================

/// Handle proofState.openObligation request.
///
/// Opens a server-backed proof state from a serialized kernel goal expression.
/// Pretty-only obligations are intentionally rejected because they cannot be
/// made into kernel goals without an elaboration context.
#[instrument(skip(state))]
pub async fn handle_open_obligation(
    state: &ServerState,
    id: RequestId,
    params: OpenObligationParams,
) -> Response {
    use clean_kernel::ExprKind;
    use elab_tactic::ProofState as InternalProofState;
    use proof_state::{OpenObligationResponse, OutputFormat};

    let validation = match params.validate() {
        Ok(validation) => validation,
        Err(err) => {
            return Response::error(
                id,
                open_obligation_invalid_params("INVALID_OPEN_OBLIGATION_REQUEST", err.to_string()),
            );
        }
    };

    let Some(target) = params.goal.expr.clone() else {
        return Response::error(
            id,
            open_obligation_invalid_params(
                "PRETTY_ONLY_OBLIGATION",
                "goal.expr is required to open a server-backed proof state; pretty-only obligations are rejected",
            ),
        );
    };

    let local_ctx = match open_obligation_local_context(&params.local_context) {
        Ok(local_ctx) => local_ctx,
        Err(err) => return Response::error(id, err),
    };

    let env = state.env.read().await;
    let proof_state = InternalProofState::with_elab_context(env.clone(), target, local_ctx);
    let goal = proof_state
        .current_goal()
        .expect("new proof state should contain one goal")
        .clone();
    let target_type = match proof_state.infer_type(&goal, &goal.target) {
        Ok(ty) => ty,
        Err(err) => {
            return Response::error(
                id,
                open_obligation_invalid_params(
                    "INVALID_KERNEL_GOAL",
                    format!("goal.expr is not a valid kernel expression: {err}"),
                ),
            );
        }
    };
    let target_type_whnf = proof_state.whnf(&goal, &target_type);
    if !matches!(target_type_whnf.kind(), ExprKind::Sort(_) | ExprKind::SProp) {
        return Response::error(
            id,
            open_obligation_invalid_params(
                "INVALID_KERNEL_GOAL",
                "goal.expr must itself be a type or proposition",
            ),
        );
    }

    let state_id = state.proof_cache.insert_open_obligation(
        proof_state,
        Some(params.environment_id.clone()),
        std::time::Duration::from_secs(params.ttl_sec),
        params.max_states,
        Some(params.trust_policy),
        params.domain_profile,
        params.metadata.clone(),
    );
    let state_ref = match state.proof_cache.get(&state_id) {
        Some(state_ref) => state_ref,
        None => {
            return Response::error(
                id,
                open_obligation_invalid_params(
                    "OPEN_OBLIGATION_CACHE_MISS",
                    "proof state could not be read after insertion",
                ),
            );
        }
    };

    let trust_summary = super::trust_summary_from_proof_state(&env, &state_ref.state);
    let initial_snapshot =
        proof_state::to_api_state(&state_ref, &env, OutputFormat::Llm, Some(trust_summary));
    let result = OpenObligationResponse {
        schema_version: validation.selected_schema,
        state_id: state_id.to_string(),
        environment_id: params.environment_id,
        domain_profile: params.domain_profile,
        initial_snapshot: Some(initial_snapshot),
        lifecycle: proof_state::OpenObligationLifecycle {
            ttl_sec: params.ttl_sec,
            max_states: params.max_states,
        },
        artifact_refs: params.artifact_refs,
        warnings: vec![],
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

fn open_obligation_local_context(
    local_context: &[proof_state::ObligationLocalHypothesis],
) -> Result<Vec<elab_tactic::LocalDecl>, RpcError> {
    local_context
        .iter()
        .enumerate()
        .map(|(idx, hyp)| {
            if hyp.name.trim().is_empty() {
                return Err(open_obligation_invalid_params(
                    "INVALID_LOCAL_CONTEXT",
                    "local_context entries must include a non-empty name",
                ));
            }
            let Some(ty) = hyp.type_expr.clone() else {
                return Err(open_obligation_invalid_params(
                    "PRETTY_ONLY_LOCAL_CONTEXT",
                    format!(
                        "local_context[{idx}].type_expr is required; pretty-only hypotheses are rejected"
                    ),
                ));
            };

            Ok(elab_tactic::LocalDecl {
                fvar: clean_kernel::FVarId::new(idx as u64),
                name: hyp.name.clone(),
                ty,
                value: hyp.value_expr.clone(),
            })
        })
        .collect()
}

fn open_obligation_invalid_params(code: &'static str, message: impl Into<String>) -> RpcError {
    let message = message.into();
    RpcError::with_data(
        crate::rpc::error_codes::INVALID_PARAMS,
        message.clone(),
        serde_json::json!({
            "method": "proofState.openObligation",
            "code": code,
            "fail_closed": true,
            "message": message,
        }),
    )
}

/// Handle initProofState request
///
/// Creates a new proof state from a theorem statement, returning a state ID
/// for subsequent tactic operations.
#[instrument(skip(state))]
pub async fn handle_init_proof_state(
    state: &ServerState,
    id: RequestId,
    params: InitProofStateParams,
) -> Response {
    use elab_tactic::ProofState as InternalProofState;
    use proof_state::convert_goals;

    let start = Instant::now();
    let _timeout =
        std::time::Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    // Parse the theorem
    let surface_expr = match parse_expr_with_tactics_exact(&params.theorem, &state.tactic_patterns)
    {
        Ok(expr) => expr,
        Err(e) => {
            return Response::error(
                id,
                RpcError::invalid_params(format!("failed to parse theorem: {}", e)),
            );
        }
    };

    // Elaborate the expression
    let env = state.env.read().await;
    let target = match elaborate(&env, &surface_expr) {
        Ok(expr) => expr,
        Err(e) => {
            return Response::error(
                id,
                RpcError::invalid_params(format!("elaboration failed: {}", e)),
            );
        }
    };

    // Create proof state
    let proof_state = InternalProofState::new(env.clone(), target);

    // Cache it
    let state_id = state
        .proof_cache
        .insert(proof_state.clone(), params.problem_id, None, 0);

    let goals = convert_goals(&proof_state, &env);
    let is_solved = proof_state.is_complete();
    let mathverse_candidates = proof_state::mathverse_candidates_for_state(&proof_state, &env);
    let trust_summary = super::trust_summary_from_proof_state(&env, &proof_state);
    let elapsed = start.elapsed().as_micros() as u64;

    let result = InitProofStateResult {
        state_id: state_id.to_string(),
        goals,
        is_solved,
        time_us: elapsed,
        time_ns: Some(ns_from_us(elapsed)),
        mathverse_candidates,
        trust_summary: Some(trust_summary),
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle applyTactic request
///
/// Applies a tactic to a proof state, returning the new state with updated goals.
#[instrument(skip(state))]
pub async fn handle_apply_tactic(
    state: &ServerState,
    id: RequestId,
    params: ApplyTacticParams,
) -> Response {
    use proof_state::{convert_goals, ApplyTacticResult, StateId, TacticApiError};

    let start = Instant::now();

    // Parse state ID
    let state_id = match params.state_id.parse::<StateId>() {
        Ok(id) => id,
        Err(_) => {
            let result = ApplyTacticResult {
                success: false,
                new_state_id: params.state_id.clone(),
                new_goals: vec![],
                is_solved: false,
                error: Some(TacticApiError::invalid_state_id(&params.state_id)),
                attempt_id: None,
                suggestions: vec![],
                time_us: 0,
                time_ns: None,
                mathverse_candidates: vec![],
                trust_summary: None,
            };
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }
    };

    // Get state from cache
    let state_ref = match state.proof_cache.get(&state_id) {
        Some(s) => s,
        None => {
            let result = ApplyTacticResult {
                success: false,
                new_state_id: params.state_id.clone(),
                new_goals: vec![],
                is_solved: false,
                error: Some(TacticApiError::invalid_state_id(&params.state_id)),
                attempt_id: None,
                suggestions: vec![],
                time_us: 0,
                time_ns: None,
                mathverse_candidates: vec![],
                trust_summary: None,
            };
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }
    };

    // Clone state for modification
    let mut proof_state = state_ref.state.clone();
    let env = state.env.read().await;

    // Goal addressing (C1 Task E): honor `goal_id` even when it names a
    // non-first goal. We resolve it to an index here; index 0 is the current
    // goal (the common case), any other valid index is focused before the
    // tactic runs. Only a goal_id that matches no live goal is rejected.
    let goal_index = match goal_index_for_id(&proof_state, &params.goal_id) {
        Some(index) => index,
        None => {
            let elapsed = start.elapsed().as_micros() as u64;
            let trust_summary = super::trust_summary_from_proof_state(&env, &state_ref.state);
            let mathverse_candidates =
                proof_state::mathverse_candidates_for_state(&state_ref.state, &env);
            let api_err = goal_not_current_error(&params.goal_id);
            let result = ApplyTacticResult {
                success: false,
                new_state_id: params.state_id,
                new_goals: vec![],
                is_solved: false,
                error: Some(api_err.clone()),
                attempt_id: None,
                suggestions: api_err.suggestions.clone(),
                time_us: elapsed,
                time_ns: Some(ns_from_us(elapsed)),
                mathverse_candidates,
                trust_summary: Some(trust_summary),
            };

            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }
    };

    // Parse and execute tactic (simple dispatcher for common tactics)
    let tactic_str = params.tactic.trim();
    if !proof_state::trust_policy_allows_tactic(state_ref.trust_policy, tactic_str) {
        let rejected = proof_state::constructive_only_rejected_tactic(tactic_str)
            .unwrap_or(tactic_str)
            .to_string();
        let elapsed = start.elapsed().as_micros() as u64;
        let trust_summary = super::trust_summary_from_proof_state(&env, &state_ref.state);
        let mathverse_candidates =
            proof_state::mathverse_candidates_for_state(&state_ref.state, &env);
        let api_err = TacticApiError::trust_policy_violation(
            state_ref
                .trust_policy
                .unwrap_or(proof_state::ObligationTrustPolicy::ConstructiveOnly),
            rejected,
        );
        let attempt_id = persist_failed_attempt(
            state,
            &state_ref,
            &params.state_id,
            &params.goal_id,
            tactic_str,
            api_err.clone(),
        );
        let result = ApplyTacticResult {
            success: false,
            new_state_id: params.state_id,
            new_goals: vec![],
            is_solved: false,
            error: Some(api_err.clone()),
            attempt_id: Some(attempt_id),
            suggestions: api_err.suggestions.clone(),
            time_us: elapsed,
            time_ns: Some(ns_from_us(elapsed)),
            mathverse_candidates,
            trust_summary: Some(trust_summary),
        };

        return Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
    }
    let tactic_result = execute_tactic_on_goal(&mut proof_state, goal_index, tactic_str, &env);

    let elapsed = start.elapsed().as_micros() as u64;

    match tactic_result {
        Ok(()) => {
            // State modified successfully - cache the new state with tactic tracking
            let new_state_id = match state.proof_cache.insert_child(
                proof_state.clone(),
                &state_ref,
                Some(tactic_str.to_string()),
            ) {
                Ok(state_id) => state_id,
                Err(proof_state::ProofStateLifecycleError::MaxStatesExceeded {
                    max_states,
                    live_states,
                }) => {
                    let api_err = TacticApiError::with_lifecycle_limit(max_states, live_states);
                    let attempt_id = persist_failed_attempt(
                        state,
                        &state_ref,
                        &params.state_id,
                        &params.goal_id,
                        tactic_str,
                        api_err.clone(),
                    );
                    let trust_summary =
                        super::trust_summary_from_proof_state(&env, &state_ref.state);
                    let mathverse_candidates =
                        proof_state::mathverse_candidates_for_state(&state_ref.state, &env);
                    let result = ApplyTacticResult {
                        success: false,
                        new_state_id: params.state_id,
                        new_goals: vec![],
                        is_solved: false,
                        error: Some(api_err.clone()),
                        attempt_id: Some(attempt_id),
                        suggestions: api_err.suggestions.clone(),
                        time_us: elapsed,
                        time_ns: Some(ns_from_us(elapsed)),
                        mathverse_candidates,
                        trust_summary: Some(trust_summary),
                    };

                    return Response::success_typed(id.clone(), &result).unwrap_or_else(|e| {
                        Response::error(id, RpcError::internal_error(e.to_string()))
                    });
                }
            };

            let trust_summary = super::trust_summary_from_proof_state(&env, &proof_state);
            let mathverse_candidates =
                proof_state::mathverse_candidates_for_state(&proof_state, &env);
            let result = ApplyTacticResult {
                success: true,
                new_state_id: new_state_id.to_string(),
                new_goals: convert_goals(&proof_state, &env),
                is_solved: proof_state.is_complete(),
                error: None,
                attempt_id: None,
                suggestions: vec![],
                time_us: elapsed,
                time_ns: Some(ns_from_us(elapsed)),
                mathverse_candidates,
                trust_summary: Some(trust_summary),
            };

            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(err) => {
            // Tactic failed on a valid state — return the original state's trust summary
            let trust_summary = super::trust_summary_from_proof_state(&env, &state_ref.state);
            let mathverse_candidates =
                proof_state::mathverse_candidates_for_state(&state_ref.state, &env);
            let api_err: TacticApiError = err.into();
            let attempt_id = persist_failed_attempt(
                state,
                &state_ref,
                &params.state_id,
                &params.goal_id,
                tactic_str,
                api_err.clone(),
            );
            let result = ApplyTacticResult {
                success: false,
                new_state_id: params.state_id,
                new_goals: vec![],
                is_solved: false,
                error: Some(api_err.clone()),
                attempt_id: Some(attempt_id),
                suggestions: api_err.suggestions.clone(),
                time_us: elapsed,
                time_ns: Some(ns_from_us(elapsed)),
                mathverse_candidates,
                trust_summary: Some(trust_summary),
            };

            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
    }
}

/// Handle getProofState request
///
/// Retrieves a proof state with the specified format (llm, full, or compact).
#[instrument(skip(state))]
pub async fn handle_get_proof_state(
    state: &ServerState,
    id: RequestId,
    params: GetProofStateParams,
) -> Response {
    use proof_state::{to_api_state, StateId};

    // Parse state ID
    let state_id = match params.state_id.parse::<StateId>() {
        Ok(id) => id,
        Err(_) => {
            return Response::error(
                id,
                RpcError::invalid_params(format!("invalid state_id: {}", params.state_id)),
            );
        }
    };

    // Get state from cache
    let state_ref = match state.proof_cache.get(&state_id) {
        Some(s) => s,
        None => {
            return Response::error(
                id,
                RpcError::invalid_params(format!(
                    "state not found or expired: {}",
                    params.state_id
                )),
            );
        }
    };

    let env = state.env.read().await;
    let trust_summary = super::trust_summary_from_proof_state(&env, &state_ref.state);
    let api_state = to_api_state(&state_ref, &env, params.format, Some(trust_summary));

    Response::success_typed(id.clone(), &api_state)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle proofState.searchTheorems request.
#[instrument(skip(state))]
pub async fn handle_search_theorems(
    state: &ServerState,
    id: RequestId,
    params: ProofStateGoalSearchParams,
) -> Response {
    let start = Instant::now();
    let Some((state_ref, env)) = cached_state_and_env(state, &params.state_id).await else {
        return Response::error(
            id,
            RpcError::invalid_params(format!("state not found or expired: {}", params.state_id)),
        );
    };

    if !goal_exists(&state_ref.state, &env, &params.goal_id) {
        return Response::error(
            id,
            RpcError::invalid_params(format!("goal not found: {}", params.goal_id)),
        );
    }
    let requested_goal = goal_for_id(&state_ref.state, &params.goal_id);

    let guidance = proof_state::llm_guidance_for_goal_and_profile(
        &state_ref.state,
        requested_goal,
        &env,
        state_ref.domain_profile,
    );
    let mut candidates = state.theorem_index.search_goal(
        requested_goal,
        &env,
        state_ref.domain_profile,
        state_ref.trust_policy,
        16,
    );
    let mut seen = candidates
        .iter()
        .map(|candidate| candidate.name.clone())
        .collect::<std::collections::BTreeSet<_>>();
    for candidate in guidance.relevant_lemmas {
        if candidates.len() >= 16 {
            break;
        }
        if seen.insert(candidate.name.clone()) {
            candidates.push(candidate);
        }
    }
    let elapsed = start.elapsed().as_micros() as u64;
    let result = SearchTheoremsResult {
        state_id: params.state_id,
        goal_id: params.goal_id,
        domain_profile: state_ref.domain_profile,
        candidates,
        mathverse_candidates: guidance.mathverse_candidates,
        time_us: elapsed,
        time_ns: Some(ns_from_us(elapsed)),
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle proofState.searchTactics request.
#[instrument(skip(state))]
pub async fn handle_search_tactics(
    state: &ServerState,
    id: RequestId,
    params: ProofStateGoalSearchParams,
) -> Response {
    let start = Instant::now();
    let Some((state_ref, env)) = cached_state_and_env(state, &params.state_id).await else {
        return Response::error(
            id,
            RpcError::invalid_params(format!("state not found or expired: {}", params.state_id)),
        );
    };

    if !goal_exists(&state_ref.state, &env, &params.goal_id) {
        return Response::error(
            id,
            RpcError::invalid_params(format!("goal not found: {}", params.goal_id)),
        );
    }

    let guidance = proof_state::llm_guidance_for_state_and_profile(
        &state_ref.state,
        &env,
        state_ref.domain_profile,
    );
    let elapsed = start.elapsed().as_micros() as u64;
    let result = SearchTacticsResult {
        state_id: params.state_id,
        goal_id: params.goal_id,
        domain_profile: state_ref.domain_profile,
        tactics: guidance.suggested_tactics,
        search_hints: guidance.search_hints,
        time_us: elapsed,
        time_ns: Some(ns_from_us(elapsed)),
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle proofState.close request.
#[instrument(skip(state))]
pub async fn handle_close_proof_state(
    state: &ServerState,
    id: RequestId,
    params: CloseProofStateParams,
) -> Response {
    let state_id = match params.state_id.parse::<proof_state::StateId>() {
        Ok(id) => id,
        Err(_) => {
            return Response::error(
                id,
                RpcError::invalid_params(format!("invalid state_id: {}", params.state_id)),
            );
        }
    };

    let closed = state.proof_cache.remove_subtree(&state_id);
    let result = CloseProofStateResult {
        state_id: params.state_id,
        closed,
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle proofState.retain request.
#[instrument(skip(state))]
pub async fn handle_retain_proof_state(
    state: &ServerState,
    id: RequestId,
    params: RetainProofStateParams,
) -> Response {
    let state_id = match params.state_id.parse::<proof_state::StateId>() {
        Ok(id) => id,
        Err(_) => {
            return Response::error(
                id,
                RpcError::invalid_params(format!("invalid state_id: {}", params.state_id)),
            );
        }
    };
    let ttl = params.ttl_sec.map(std::time::Duration::from_secs);
    let Some(lifecycle) = state.proof_cache.retain(&state_id, ttl) else {
        return Response::error(
            id,
            RpcError::invalid_params(format!("state not found or expired: {}", params.state_id)),
        );
    };

    let result = RetainProofStateResult {
        state_id: params.state_id,
        retained: true,
        lifecycle,
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle proofState.explainFailure request.
#[instrument(skip(state))]
pub async fn handle_explain_failure(
    state: &ServerState,
    id: RequestId,
    params: ExplainFailureParams,
) -> Response {
    let attempt_id = match params.attempt_id.parse::<proof_state::AttemptId>() {
        Ok(id) => id,
        Err(_) => {
            return Response::error(
                id,
                RpcError::invalid_params(format!("invalid attempt_id: {}", params.attempt_id)),
            );
        }
    };

    let Some(failure) = state.proof_cache.get_failure(&attempt_id) else {
        let result = ExplainFailureResult {
            attempt_id: params.attempt_id,
            status: "not-found".to_string(),
            explanation: "no persisted failure telemetry was found for this attempt id".to_string(),
            blockers: vec![],
            suggestions: vec![
                "run applyTactic again and inspect the returned attempt_id".to_string()
            ],
        };

        return Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
    };

    let details = failure.error.details.clone();
    let result = ExplainFailureResult {
        attempt_id: params.attempt_id,
        status: "failed".to_string(),
        explanation: failure.error.message.clone(),
        blockers: vec![FailureBlocker {
            kind: "tactic-error".to_string(),
            code: failure.error.code,
            message: failure.error.message,
            state_id: failure.state_id,
            goal_id: failure.goal_id,
            tactic: failure.tactic,
            failed_constraints: details
                .as_ref()
                .map(|details| details.failed_constraints.clone())
                .unwrap_or_default(),
            trace: details.map(|details| details.trace).unwrap_or_default(),
        }],
        suggestions: failure.error.suggestions,
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

fn persist_failed_attempt(
    state: &ServerState,
    state_ref: &proof_state::ProofStateRef,
    state_id: &str,
    goal_id: &str,
    tactic: &str,
    error: proof_state::TacticApiError,
) -> String {
    let failure = proof_state::FailedTacticAttempt {
        state_id: state_id.to_string(),
        goal_id: goal_id.to_string(),
        tactic: tactic.to_string(),
        error,
        step_number: state_ref.step_number,
        lifecycle: proof_state::ProofStateLifecycleMetadata {
            ttl_sec: state_ref.ttl.as_secs(),
            ttl_remaining_sec: state_ref.ttl_remaining.as_secs(),
            max_states: state_ref.max_states,
            live_states: state_ref.live_states,
        },
    };
    state
        .proof_cache
        .insert_failure(
            failure,
            state_ref
                .ttl_remaining
                .max(std::time::Duration::from_secs(1)),
        )
        .to_string()
}

async fn cached_state_and_env(
    state: &ServerState,
    state_id: &str,
) -> Option<(proof_state::ProofStateRef, clean_kernel::Environment)> {
    let parsed = match state_id.parse::<proof_state::StateId>() {
        Ok(id) => id,
        Err(_) => return None,
    };
    let state_ref = state.proof_cache.get(&parsed)?;
    let env = state.env.read().await.clone();
    Some((state_ref, env))
}

fn goal_exists(
    proof_state: &elab_tactic::ProofState,
    env: &clean_kernel::Environment,
    goal_id: &str,
) -> bool {
    proof_state::convert_goals(proof_state, env)
        .iter()
        .any(|goal| goal.goal_id == goal_id)
}

/// Run a simple tactic against the goal at `goal_index`, focusing it first when
/// it is not the current (front) goal (C1 Task E goal addressing).
///
/// For `goal_index == 0` this is exactly [`execute_simple_tactic`]. For any
/// other index the goal is rotated to the front via
/// [`elab_tactic::ProofState::focus_goal`], the tactic runs there, and the
/// preceding goals are restored, so the rest of the proof state is untouched.
/// `goal_index` is assumed in range (the caller validated it with
/// [`goal_index_for_id`]); an out-of-range index yields a `NoGoals` error
/// rather than acting on the wrong goal.
fn execute_tactic_on_goal(
    proof_state: &mut elab_tactic::ProofState,
    goal_index: usize,
    tactic_str: &str,
    env: &clean_kernel::Environment,
) -> Result<(), elab_tactic::TacticError> {
    if goal_index == 0 {
        return execute_simple_tactic(proof_state, tactic_str, env);
    }
    proof_state
        .focus_goal(goal_index, |focused| {
            execute_simple_tactic(focused, tactic_str, env)
        })
        .unwrap_or(Err(elab_tactic::TacticError::NoGoals))
}

fn goal_for_id<'a>(
    proof_state: &'a elab_tactic::ProofState,
    goal_id: &str,
) -> Option<&'a clean_elab::tactic::Goal> {
    proof_state
        .goals()
        .get(goal_index_for_id(proof_state, goal_id)?)
}

/// Resolve a `g<index>` goal id to its position in the proof state's goal
/// deque, validating that the index is in range.
///
/// Returns `None` when the id is malformed or refers to a goal that no longer
/// exists. Index `0` is the current (front) goal; any other valid index is a
/// non-first goal that `applyTactic` can address by focusing it (C1 Task E).
fn goal_index_for_id(proof_state: &elab_tactic::ProofState, goal_id: &str) -> Option<usize> {
    let index = goal_id.strip_prefix('g')?.parse::<usize>().ok()?;
    if index < proof_state.goals().len() {
        Some(index)
    } else {
        None
    }
}

fn goal_not_current_error(goal_id: &str) -> proof_state::TacticApiError {
    proof_state::TacticApiError {
        code: proof_state::TacticErrorCode::NoMatchingGoal,
        message: format!("goal not found or not current: {goal_id}"),
        details: None,
        suggestions: vec![
            "Use getProofState and apply tactics to the current first goal.".to_string(),
        ],
    }
}

/// Handle extractProof request
///
/// Extracts the proof term from a solved proof state.
/// Supports multiple output formats:
/// - "term": Pretty-printed proof term (default)
/// - "tactic_script": List of tactics that produced the proof
/// - "certificate": Cryptographic certificate for independent verification
/// - "all": All of the above
#[instrument(skip(state))]
pub async fn handle_extract_proof(
    state: &ServerState,
    id: RequestId,
    params: ExtractProofParams,
) -> Response {
    use proof_state::{pp_expr, StateId};

    let start = Instant::now();

    // Parse state ID
    let state_id = match params.state_id.parse::<StateId>() {
        Ok(id) => id,
        Err(_) => {
            return Response::error(
                id,
                RpcError::invalid_params(format!("invalid state_id: {}", params.state_id)),
            );
        }
    };

    // Get state from cache
    let state_ref = match state.proof_cache.get(&state_id) {
        Some(s) => s,
        None => {
            return Response::error(
                id,
                RpcError::invalid_params(format!(
                    "state not found or expired: {}",
                    params.state_id
                )),
            );
        }
    };

    if !state_ref.state.is_complete() {
        return Response::error(
            id,
            RpcError::invalid_params("proof not complete - goals remain"),
        );
    }

    let env = state.env.read().await;

    // Get the closed proof term (FVars converted to BVars for proper verification)
    let proof_expr_opt = state_ref.state.closed_proof();

    // Reconstruct tactic script if requested
    let tactic_script = if params.format == "tactic_script" || params.format == "all" {
        let script = state.proof_cache.reconstruct_tactic_script(&state_id);
        if script.is_empty() {
            None
        } else {
            Some(script)
        }
    } else {
        None
    };

    // Always verify proof term via kernel type-checking against goal type (#2157, #2200).
    // Certificate generation is gated on format; verification is unconditional.
    let goal_type = state_ref.state.goal_type();
    let wants_certificate = params.format == "certificate"
        || params.format == "all"
        || params.format == "kernel_evidence";
    let (certificate, verified) = if let Some(ref proof_term) = proof_expr_opt {
        use clean_kernel::TypeChecker;
        let tc = TypeChecker::with_mode(&env, env.mode());
        if let Some(ref target) = goal_type {
            if wants_certificate {
                match tc.infer_type_with_cert(proof_term) {
                    Ok((inferred_ty, cert)) => {
                        let type_ok = tc.is_def_eq(&inferred_ty, target)
                            && tc.check_type(proof_term, target).is_ok();
                        match serde_json::to_value(&cert) {
                            Ok(json) => (Some(json), type_ok),
                            Err(_) => (None, type_ok),
                        }
                    }
                    Err(_) => (None, false),
                }
            } else {
                (None, tc.check_type(proof_term, target).is_ok())
            }
        } else {
            // No goal type available — cannot verify type matches goal (#2200)
            (None, false)
        }
    } else {
        (None, false)
    };

    let elapsed = start.elapsed().as_micros() as u64;
    let verification = ProofVerification {
        verified,
        time_us: elapsed,
        time_ns: Some(ns_from_us(elapsed)),
    };
    let trust_summary = super::verify::trust_summary_from_ledger_with_closed_proof(
        state_ref.state.trust_ledger(),
        proof_expr_opt.as_ref(),
        verified,
        0,
    );

    if params.format == "kernel_evidence" {
        let result = match kernel_proof_extraction_evidence(
            &state_ref,
            proof_expr_opt.as_ref(),
            goal_type.as_ref(),
            certificate.clone(),
            verification.clone(),
            trust_summary.clone(),
        ) {
            Ok(evidence) => evidence,
            Err(err) => return Response::error(id, err),
        };
        return Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
    }

    let result = ExtractProofResult {
        is_solved: true,
        proof_term: proof_expr_opt.as_ref().map(|p| pp_expr(p, &env)),
        proof_expr: if params.format == "certificate" || params.format == "all" {
            proof_expr_opt.clone()
        } else {
            None
        },
        tactic_script,
        certificate,
        verification,
        trust_summary: Some(trust_summary),
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

fn kernel_proof_extraction_evidence(
    state_ref: &proof_state::ProofStateRef,
    proof_expr: Option<&Expr>,
    target_expr: Option<&Expr>,
    certificate: Option<serde_json::Value>,
    verification: ProofVerification,
    trust_summary: super::TrustSummary,
) -> Result<KernelProofExtractionEvidence, RpcError> {
    if !verification.verified {
        return Err(kernel_evidence_error(
            "KERNEL_PROOF_NOT_VERIFIED",
            "kernel evidence requires a proof term verified against the proof-state target",
        ));
    }
    if !trust_summary_is_clean_for_kernel_evidence(&trust_summary) {
        return Err(kernel_evidence_error(
            "KERNEL_EVIDENCE_TRUST_DEBT",
            "kernel evidence requires a fully verified trust summary with no sorry, trustedAy, or trustedArith debt",
        ));
    }
    let proof_expr = proof_expr.ok_or_else(|| {
        kernel_evidence_error(
            "KERNEL_EVIDENCE_MISSING_PROOF",
            "kernel evidence requires a closed proof term",
        )
    })?;
    let target_expr = target_expr.ok_or_else(|| {
        kernel_evidence_error(
            "KERNEL_EVIDENCE_MISSING_TARGET",
            "kernel evidence requires the proof-state target expression",
        )
    })?;
    let proof_certificate = certificate.ok_or_else(|| {
        kernel_evidence_error(
            "KERNEL_EVIDENCE_MISSING_CERTIFICATE",
            "kernel evidence requires a generated kernel certificate",
        )
    })?;
    let proof_hash = sha256_json_expr(proof_expr).map_err(|err| {
        kernel_evidence_error(
            "KERNEL_EVIDENCE_HASH_FAILED",
            format!("failed to hash checked proof expression: {err}"),
        )
    })?;
    let target_hash = sha256_json_expr(target_expr).map_err(|err| {
        kernel_evidence_error(
            "KERNEL_EVIDENCE_HASH_FAILED",
            format!("failed to hash checked target expression: {err}"),
        )
    })?;
    let context = kernel_evidence_problem_context(
        state_ref.metadata.as_ref(),
        state_ref.problem_id.as_deref(),
    );
    let linked_obligations = context.obligation.iter().cloned().collect();

    Ok(KernelProofExtractionEvidence {
        schema_version: KERNEL_PROOF_EVIDENCE_SCHEMA_VERSION,
        theorem: format!("proof-state:{}", state_ref.id),
        project: context.project,
        obligation: context.obligation,
        linked_obligations,
        proof_hash,
        target_hash,
        checker: "clean-kernel:TypeChecker::infer_type_with_cert+check_type",
        source: "clean-kernel:extractProof",
        checked: true,
        kernel_verification: verification,
        trust_summary,
        checked_proof_expr: proof_expr.clone(),
        checked_target_expr: target_expr.clone(),
        proof_certificate,
    })
}

fn trust_summary_is_clean_for_kernel_evidence(summary: &super::TrustSummary) -> bool {
    summary.fully_verified
        && summary.sorry_count == 0
        && summary.ay_count == 0
        && summary.arith_count == 0
        && summary.kernel_check_failures == 0
}

struct KernelEvidenceProblemContext {
    project: Option<String>,
    obligation: Option<String>,
}

fn kernel_evidence_problem_context(
    metadata: Option<&proof_state::ProofStateMetadata>,
    problem_id: Option<&str>,
) -> KernelEvidenceProblemContext {
    if let Some(metadata) = metadata {
        if metadata.project.is_some() || metadata.obligation_fingerprint.is_some() {
            return KernelEvidenceProblemContext {
                project: metadata.project.clone(),
                obligation: metadata.obligation_fingerprint.clone(),
            };
        }
    }

    let Some(problem_id) = problem_id else {
        return KernelEvidenceProblemContext {
            project: None,
            obligation: None,
        };
    };
    if problem_id.starts_with("sha256:") {
        return KernelEvidenceProblemContext {
            project: None,
            obligation: Some(problem_id.to_owned()),
        };
    }
    if let Some(rest) = problem_id.strip_prefix("math-project:") {
        if let Some((project, obligation)) = rest.split_once(":obligation:") {
            return KernelEvidenceProblemContext {
                project: Some(project.to_owned()),
                obligation: Some(obligation.to_owned()),
            };
        }
        return KernelEvidenceProblemContext {
            project: Some(rest.to_owned()),
            obligation: None,
        };
    }
    KernelEvidenceProblemContext {
        project: None,
        obligation: None,
    }
}

fn sha256_json_expr(expr: &Expr) -> Result<String, serde_json::Error> {
    let bytes = serde_json::to_vec(expr)?;
    Ok(format!(
        "sha256:{}",
        Sha256::digest(bytes)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    ))
}

fn kernel_evidence_error(code: &'static str, message: impl Into<String>) -> RpcError {
    let message = message.into();
    RpcError::with_data(
        crate::rpc::error_codes::INVALID_PARAMS,
        message.clone(),
        serde_json::json!({
            "method": "extractProof",
            "code": code,
            "fail_closed": true,
            "message": message,
        }),
    )
}

/// Handle batchApplyTactic request
///
/// Applies multiple tactics in parallel using rayon, useful for beam search
/// and tree exploration in LLM-guided proof search.
#[instrument(skip(state))]
pub async fn handle_batch_apply_tactic(
    state: &ServerState,
    id: RequestId,
    params: BatchApplyTacticParams,
) -> Response {
    use proof_state::{convert_goals, StateId, TacticApiError};
    use rayon::prelude::*;

    let start = Instant::now();

    // Configure thread pool if specified
    let pool = params.threads.map(|n| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(n.max(1))
            .build()
            .ok()
    });

    // Get environment snapshot (shared across all items)
    let env = state.env.read().await.clone();
    let cache = &state.proof_cache;

    // Process a single item
    let process_item = |item: &BatchTacticItem| -> BatchTacticItemResult {
        let item_start = Instant::now();

        // Parse state ID
        let state_id = match item.state_id.parse::<StateId>() {
            Ok(id) => id,
            Err(_) => {
                return BatchTacticItemResult {
                    id: item.id.clone(),
                    success: false,
                    new_state_id: None,
                    new_goals: vec![],
                    is_solved: false,
                    error: Some(TacticApiError::invalid_state_id(&item.state_id)),
                    time_us: item_start.elapsed().as_micros() as u64,
                    time_ns: None,
                    mathverse_candidates: vec![],
                    trust_summary: None,
                };
            }
        };

        // Get state from cache
        let state_ref = match cache.get(&state_id) {
            Some(s) => s,
            None => {
                return BatchTacticItemResult {
                    id: item.id.clone(),
                    success: false,
                    new_state_id: None,
                    new_goals: vec![],
                    is_solved: false,
                    error: Some(TacticApiError::invalid_state_id(&item.state_id)),
                    time_us: item_start.elapsed().as_micros() as u64,
                    time_ns: None,
                    mathverse_candidates: vec![],
                    trust_summary: None,
                };
            }
        };

        // Clone state for modification
        let mut proof_state = state_ref.state.clone();

        // Execute tactic
        let tactic_str = item.tactic.trim();
        if !proof_state::trust_policy_allows_tactic(state_ref.trust_policy, tactic_str) {
            let rejected = proof_state::constructive_only_rejected_tactic(tactic_str)
                .unwrap_or(tactic_str)
                .to_string();
            let elapsed = item_start.elapsed().as_micros() as u64;
            let trust_summary =
                super::verify::trust_summary_from_proof_state(&env, &state_ref.state);
            let mathverse_candidates =
                proof_state::mathverse_candidates_for_state(&state_ref.state, &env);
            return BatchTacticItemResult {
                id: item.id.clone(),
                success: false,
                new_state_id: None,
                new_goals: vec![],
                is_solved: false,
                error: Some(TacticApiError::trust_policy_violation(
                    state_ref
                        .trust_policy
                        .unwrap_or(proof_state::ObligationTrustPolicy::ConstructiveOnly),
                    rejected,
                )),
                time_us: elapsed,
                time_ns: Some(ns_from_us(elapsed)),
                mathverse_candidates,
                trust_summary: Some(trust_summary),
            };
        }
        // Goal addressing (C1 Task E): resolve the requested goal_id to an
        // index, rejecting an id that names no live goal. Index 0 is the
        // current goal; any other valid index is focused before the tactic runs.
        let goal_index = match goal_index_for_id(&proof_state, &item.goal_id) {
            Some(index) => index,
            None => {
                let elapsed = item_start.elapsed().as_micros() as u64;
                let trust_summary =
                    super::verify::trust_summary_from_proof_state(&env, &state_ref.state);
                let mathverse_candidates =
                    proof_state::mathverse_candidates_for_state(&state_ref.state, &env);
                return BatchTacticItemResult {
                    id: item.id.clone(),
                    success: false,
                    new_state_id: None,
                    new_goals: vec![],
                    is_solved: false,
                    error: Some(goal_not_current_error(&item.goal_id)),
                    time_us: elapsed,
                    time_ns: Some(ns_from_us(elapsed)),
                    mathverse_candidates,
                    trust_summary: Some(trust_summary),
                };
            }
        };
        let tactic_result = execute_tactic_on_goal(&mut proof_state, goal_index, tactic_str, &env);

        let elapsed = item_start.elapsed().as_micros() as u64;

        match tactic_result {
            Ok(()) => {
                // Cache the new state with tactic tracking
                let new_state_id = cache.insert_with_tactic_policy_domain_and_metadata(
                    proof_state.clone(),
                    state_ref.problem_id.clone(),
                    Some(state_id),
                    state_ref.step_number + 1,
                    Some(tactic_str.to_string()),
                    state_ref.trust_policy,
                    state_ref.domain_profile,
                    state_ref.metadata.clone(),
                );

                let trust_summary =
                    super::verify::trust_summary_from_proof_state(&env, &proof_state);
                let mathverse_candidates =
                    proof_state::mathverse_candidates_for_state(&proof_state, &env);
                BatchTacticItemResult {
                    id: item.id.clone(),
                    success: true,
                    new_state_id: Some(new_state_id.to_string()),
                    new_goals: convert_goals(&proof_state, &env),
                    is_solved: proof_state.is_complete(),
                    error: None,
                    time_us: elapsed,
                    time_ns: Some(ns_from_us(elapsed)),
                    mathverse_candidates,
                    trust_summary: Some(trust_summary),
                }
            }
            Err(err) => {
                // Tactic failed on a valid state — return original state's trust summary
                let trust_summary =
                    super::verify::trust_summary_from_proof_state(&env, &state_ref.state);
                let mathverse_candidates =
                    proof_state::mathverse_candidates_for_state(&state_ref.state, &env);
                BatchTacticItemResult {
                    id: item.id.clone(),
                    success: false,
                    new_state_id: None,
                    new_goals: vec![],
                    is_solved: false,
                    error: Some(err.into()),
                    time_us: elapsed,
                    time_ns: Some(ns_from_us(elapsed)),
                    mathverse_candidates,
                    trust_summary: Some(trust_summary),
                }
            }
        }
    };

    // Execute in parallel
    let results: Vec<BatchTacticItemResult> = match pool {
        Some(Some(pool)) => pool.install(|| params.items.par_iter().map(process_item).collect()),
        _ => params.items.par_iter().map(process_item).collect(),
    };

    // Compute stats
    let succeeded = results.iter().filter(|r| r.success).count();
    let solved = results.iter().filter(|r| r.is_solved).count();
    let wall_time = start.elapsed().as_micros() as u64;

    let result = BatchApplyTacticResult {
        results,
        stats: BatchTacticStats {
            total: params.items.len(),
            succeeded,
            failed: params.items.len() - succeeded,
            solved,
            wall_time_us: wall_time,
            wall_time_ns: Some(ns_from_us(wall_time)),
        },
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}
