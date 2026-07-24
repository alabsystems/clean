// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core theorem-proving handlers: check, prove, getType, batchCheck.

use super::check_decl_validation::validate_decl_read_only;
use super::helpers::{format_expr, format_parse_error, parse_error_col, parse_error_line};
use super::prove_result_from_automation_outcome;
use super::prove_result_from_smt_verification;
use super::state::ServerState;
use super::types::*;
use crate::progress::ProgressSender;
use crate::rpc::{RequestId, Response, RpcError};
use clean_auto::bridge::SmtBridge;
use clean_auto::{AutomationEngine, AutomationQuery};
use clean_elab::{elaborate, elaborate_decl};
use clean_kernel::TypeChecker;
use clean_parser::{parse_decl_with_tactics_exact, parse_expr_with_tactics_exact};
use serde_json::json;
use std::time::{Duration, Instant};
use tracing::{debug, instrument};

/// Handle the "check" method
#[instrument(skip(state))]
pub async fn handle_check(state: &ServerState, id: RequestId, params: CheckParams) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    // Try to complete within timeout
    let result = tokio::time::timeout(timeout, async {
        check_code_impl(state, &params.code).await
    })
    .await;

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(Ok(mut check_result)) => {
            check_result.time_ms = elapsed_ms;
            check_result.time_ns = Some(ns_from_us(elapsed_us));
            let success = check_result.valid;
            state.metrics.record_request("check", success, elapsed_us);
            Response::success_typed(id.clone(), &check_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => {
            state.metrics.record_request("check", false, elapsed_us);
            Response::error(id, e)
        }
        Err(_) => {
            state.metrics.record_request("check", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

pub(super) async fn check_code_impl(
    state: &ServerState,
    code: &str,
) -> Result<CheckResult, RpcError> {
    // First try to parse as expression (with tactic patterns for Named dispatch)
    if let Ok(surface_expr) = parse_expr_with_tactics_exact(code, &state.tactic_patterns) {
        let env = state.env.read().await;

        match elaborate(&env, &surface_expr) {
            Ok(expr) => {
                let tc = TypeChecker::with_mode(&env, env.mode());
                let type_result = tc.infer_type(&expr);
                state.cache_metrics.record_type_checker(&tc);
                return Ok(match type_result {
                    Ok(type_) => CheckResult {
                        valid: true,
                        inferred_type: Some(format_expr(&type_)),
                        errors: vec![],
                        time_ms: 0,
                        time_ns: None,
                    },
                    Err(e) => CheckResult {
                        valid: false,
                        inferred_type: None,
                        errors: vec![CheckError {
                            message: format!("Type error: {e}"),
                            line: None,
                            column: None,
                        }],
                        time_ms: 0,
                        time_ns: None,
                    },
                });
            }
            Err(e) => {
                return Ok(CheckResult {
                    valid: false,
                    inferred_type: None,
                    errors: vec![CheckError {
                        message: format!("Elaboration error: {e}"),
                        line: None,
                        column: None,
                    }],
                    time_ms: 0,
                    time_ns: None,
                });
            }
        }
    }

    // Try to parse as declaration (with tactic patterns for Named dispatch)
    match parse_decl_with_tactics_exact(code, &state.tactic_patterns) {
        Ok(surface_decl) => {
            let env = state.env.read().await;

            match elaborate_decl(&env, &surface_decl) {
                Ok(decl) => {
                    let tc = TypeChecker::with_mode(&env, env.mode());
                    let validation = validate_decl_read_only(&env, &tc, &decl);
                    state.cache_metrics.record_type_checker(&tc);
                    match validation {
                        Ok(inferred_type) => Ok(CheckResult {
                            valid: true,
                            inferred_type,
                            errors: vec![],
                            time_ms: 0,
                            time_ns: None,
                        }),
                        Err(message) => Ok(CheckResult {
                            valid: false,
                            inferred_type: None,
                            errors: vec![CheckError {
                                message,
                                line: None,
                                column: None,
                            }],
                            time_ms: 0,
                            time_ns: None,
                        }),
                    }
                }
                Err(e) => Ok(CheckResult {
                    valid: false,
                    inferred_type: None,
                    errors: vec![CheckError {
                        message: format!("Elaboration error: {e}"),
                        line: None,
                        column: None,
                    }],
                    time_ms: 0,
                    time_ns: None,
                }),
            }
        }
        Err(e) => Ok(CheckResult {
            valid: false,
            inferred_type: None,
            errors: vec![CheckError {
                message: format_parse_error(&e),
                line: parse_error_line(&e),
                column: parse_error_col(&e),
            }],
            time_ms: 0,
            time_ns: None,
        }),
    }
}

/// Handle the "prove" method
#[instrument(skip(state))]
pub async fn handle_prove(state: &ServerState, id: RequestId, params: ProveParams) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    let result = tokio::time::timeout(timeout, async { prove_impl(state, &params).await }).await;

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(Ok(mut prove_result)) => {
            prove_result.time_ms = elapsed_ms;
            prove_result.time_ns = Some(ns_from_us(elapsed_us));
            let success = prove_result.found;
            state.metrics.record_request("prove", success, elapsed_us);
            Response::success_typed(id.clone(), &prove_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => {
            state.metrics.record_request("prove", false, elapsed_us);
            Response::error(id, e)
        }
        Err(_) => {
            state.metrics.record_request("prove", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

async fn prove_impl(state: &ServerState, params: &ProveParams) -> Result<ProveResult, RpcError> {
    // Parse the goal exactly (reject trailing garbage)
    let goal_surface = parse_expr_with_tactics_exact(&params.goal, &state.tactic_patterns)
        .map_err(|e| RpcError::lean_parse_error(format!("Failed to parse goal: {e}")))?;

    let env = state.env.read().await;

    // Elaborate the goal
    let goal_expr = elaborate(&env, &goal_surface)
        .map_err(|e| RpcError::elaboration_error(format!("Failed to elaborate goal: {e}")))?;

    // Parse and elaborate hypotheses into (Expr, Option<QuantifierOrigin>) pairs
    // for the AutomationEngine query interface.
    let mut hypotheses: Vec<(
        clean_kernel::Expr,
        Option<clean_auto::bridge::QuantifierOrigin>,
    )> = Vec::with_capacity(params.hypotheses.len());
    for (i, hyp_str) in params.hypotheses.iter().enumerate() {
        let hyp_surface =
            parse_expr_with_tactics_exact(hyp_str, &state.tactic_patterns).map_err(|e| {
                RpcError::lean_parse_error(format!("Failed to parse hypothesis {i}: {e}"))
            })?;

        let hyp_expr = elaborate(&env, &hyp_surface).map_err(|e| {
            RpcError::elaboration_error(format!("Failed to elaborate hypothesis {i}: {e}"))
        })?;

        hypotheses.push((hyp_expr, None));
    }

    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));
    let strategy = params.strategy.as_deref().unwrap_or("auto");

    prove_with_strategy(&env, &goal_expr, &hypotheses, timeout, strategy)
}

/// Dispatch proof search to the selected strategy.
///
/// "smt" uses the SmtBridge directly. "superposition" uses the superposition
/// prover. "auto" (default) chains SMT -> superposition -> oracle via
/// [`AutomationEngine::auto_prove_with_query`].
fn prove_with_strategy(
    env: &clean_kernel::Environment,
    goal: &clean_kernel::Expr,
    hypotheses: &[(
        clean_kernel::Expr,
        Option<clean_auto::bridge::QuantifierOrigin>,
    )],
    timeout: Duration,
    strategy: &str,
) -> Result<ProveResult, RpcError> {
    match strategy {
        "smt" => prove_smt_only(env, goal, hypotheses),
        "superposition" => Ok(prove_superposition_only(env, goal, hypotheses)),
        _ => Ok(prove_auto_cascade(env, goal, hypotheses, timeout)),
    }
}

/// SMT-only strategy: use SmtBridge directly (original behavior).
fn prove_smt_only(
    env: &clean_kernel::Environment,
    goal: &clean_kernel::Expr,
    hypotheses: &[(
        clean_kernel::Expr,
        Option<clean_auto::bridge::QuantifierOrigin>,
    )],
) -> Result<ProveResult, RpcError> {
    let mut bridge = SmtBridge::new(env);
    let mut dropped = 0u32;
    for (hyp_expr, _origin) in hypotheses {
        if bridge.add_hypothesis(hyp_expr).is_err() {
            dropped += 1;
        }
    }
    if dropped > 0 {
        tracing::warn!(
            dropped,
            total = hypotheses.len(),
            "hypothesis(es) dropped in RPC prove handler (unsupported by SMT bridge)"
        );
    }
    match bridge.prove(goal) {
        Ok(result) => Ok(prove_result_from_smt_verification(env, goal, result)),
        Err(e) => Err(RpcError::internal_error(format!("SMT bridge error: {e}"))),
    }
}

/// Superposition-only strategy.
fn prove_superposition_only(
    env: &clean_kernel::Environment,
    goal: &clean_kernel::Expr,
    hypotheses: &[(
        clean_kernel::Expr,
        Option<clean_auto::bridge::QuantifierOrigin>,
    )],
) -> ProveResult {
    let engine = AutomationEngine::new();
    let outcome = match engine.try_superposition_prove_with_hypotheses(env, goal, hypotheses) {
        Some(result) => clean_auto::AutomationOutcome::Verified(Box::new(result)),
        None => clean_auto::AutomationOutcome::Unknown {
            reason: "superposition: no refutation found".to_string(),
            source: clean_auto::AutomationSource::Superposition,
            time_ms: 0,
        },
    };
    prove_result_from_automation_outcome(env, goal, outcome)
}

/// Full cascade: SMT -> superposition -> oracle via AutomationEngine.
fn prove_auto_cascade(
    env: &clean_kernel::Environment,
    goal: &clean_kernel::Expr,
    hypotheses: &[(
        clean_kernel::Expr,
        Option<clean_auto::bridge::QuantifierOrigin>,
    )],
    timeout: Duration,
) -> ProveResult {
    let engine = AutomationEngine::new();
    let query = AutomationQuery::new(goal, timeout).with_hypotheses(hypotheses);
    let outcome = engine.auto_prove_with_query(env, query);
    prove_result_from_automation_outcome(env, goal, outcome)
}

/// Handle the "getType" method
#[instrument(skip(state))]
pub async fn handle_get_type(
    state: &ServerState,
    id: RequestId,
    params: GetTypeParams,
) -> Response {
    let start = Instant::now();

    let result = get_type_impl(state, &params.expr).await;
    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(mut type_result) => {
            type_result.time_ms = elapsed_ms;
            type_result.time_ns = Some(ns_from_us(elapsed_us));
            state.metrics.record_request("getType", true, elapsed_us);
            Response::success_typed(id.clone(), &type_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(e) => {
            state.metrics.record_request("getType", false, elapsed_us);
            Response::error(id, e)
        }
    }
}

async fn get_type_impl(state: &ServerState, expr_str: &str) -> Result<GetTypeResult, RpcError> {
    let surface_expr = parse_expr_with_tactics_exact(expr_str, &state.tactic_patterns)
        .map_err(|e| RpcError::lean_parse_error(format!("Parse error: {e}")))?;

    let env = state.env.read().await;

    let expr = elaborate(&env, &surface_expr)
        .map_err(|e| RpcError::elaboration_error(format!("Elaboration error: {e}")))?;

    let tc = TypeChecker::with_mode(&env, env.mode());
    let type_result = tc
        .infer_type(&expr)
        .map_err(|e| RpcError::type_error(format!("Type error: {e}")));
    state.cache_metrics.record_type_checker(&tc);
    let type_ = type_result?;

    Ok(GetTypeResult {
        type_: format_expr(&type_),
        time_ms: 0,
        time_ns: None,
    })
}

/// Handle the "batchCheck" method
#[instrument(skip(state))]
pub async fn handle_batch_check(
    state: &ServerState,
    id: RequestId,
    params: BatchCheckParams,
    progress: Option<ProgressSender>,
) -> Response {
    let start = Instant::now();
    let item_count = params.items.len() as u64;
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms * 10));

    let result = tokio::time::timeout(timeout, async {
        batch_check_impl(state, &params, progress.clone()).await
    })
    .await;

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(Ok(mut batch_result)) => {
            batch_result.time_ms = elapsed_ms;
            batch_result.time_ns = Some(ns_from_us(elapsed_us));
            let all_valid = batch_result.results.iter().all(|r| r.valid);
            state
                .metrics
                .record_request("batchCheck", all_valid, elapsed_us);
            state.metrics.record_batch_items(item_count);
            Response::success_typed(id.clone(), &batch_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => {
            state
                .metrics
                .record_request("batchCheck", false, elapsed_us);
            Response::error(id, e)
        }
        Err(_) => {
            state
                .metrics
                .record_request("batchCheck", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

async fn batch_check_impl(
    state: &ServerState,
    params: &BatchCheckParams,
    progress: Option<ProgressSender>,
) -> Result<BatchCheckResult, RpcError> {
    let mut warnings = Vec::new();

    // GPU acceleration is not implemented for type checking.
    // Note: GPU was benchmarked and found to be ~100x slower than CPU due to
    // dispatch overhead and CPU-friendly control flow patterns in type checking.
    // CPU parallelism via Rayon is preferred.
    if params.use_gpu {
        let warning = "use_gpu=true was requested but GPU acceleration is not \
                       available for type checking; using CPU instead"
            .to_string();
        debug!("{}", warning);
        warnings.push(warning);
    }

    let mut results = Vec::with_capacity(params.items.len());

    if let Some(progress) = progress.as_ref() {
        progress
            .notify(
                format!("Batch check started ({} items)", params.items.len()),
                Some(0),
                None,
            )
            .await;
    }

    let total = params.items.len();

    // Adaptive progress frequency: for large batches, only send progress every N items
    let progress_interval = if total <= 100 {
        1 // Every item
    } else if total <= 500 {
        total / 50 // ~50 updates
    } else if total <= 2000 {
        total / 100 // ~100 updates
    } else {
        total / 200 // ~200 updates max
    };

    for (idx, item) in params.items.iter().enumerate() {
        let check_result = check_code_impl(state, &item.code).await;
        let valid = check_result.as_ref().is_ok_and(|r| r.valid);
        let error_msg = check_result
            .as_ref()
            .ok()
            .and_then(|r| r.errors.first().map(|e| e.message.clone()))
            .or_else(|| check_result.err().map(|e| e.message));

        results.push(BatchCheckItemResult {
            id: item.id.clone(),
            valid,
            error: error_msg.clone(),
        });

        if let Some(progress) = progress.as_ref() {
            let completed = idx + 1;
            // Only send progress on interval boundaries, first item, or last item
            let should_report =
                completed % progress_interval == 0 || completed == total || completed == 1;
            if should_report {
                let percentage = (completed * 100)
                    .checked_div(total)
                    .map_or(100, |p| p.min(100) as u8);

                progress
                    .notify(
                        format!("Checked {}/{} ({})", completed, total, item.id),
                        Some(percentage),
                        Some(json!({
                            "id": item.id,
                            "valid": valid,
                            "error": error_msg,
                        })),
                    )
                    .await;
            }
        }
    }

    Ok(BatchCheckResult {
        results,
        time_ms: 0,
        time_ns: None,
        gpu_used: false,
        warnings,
    })
}
