// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core theorem-proving handlers: check, prove, getType, batchCheck.
//!
//! Each runs its parsing, elaboration, type checking and proof search on the
//! server's work pool (`work.rs`), under the request's deadline: the request's
//! `tokio::time::timeout` fires at the deadline, the work stops at its next
//! kernel tick once the deadline has passed, and an interrupted request answers
//! the timeout error, never a result.

mod prove_strategy;

use prove_strategy::prove_with_strategy;

use super::helpers::{format_expr, format_parse_error, parse_error_col, parse_error_line};
use super::state::{ServerState, TypeCheckerSample};
use super::types::*;
use super::work::{past, within, WorkError, WorkPool, WorkSlot};
use crate::progress::ProgressSender;
use crate::rpc::{RequestId, Response, RpcError};
use clean_elab::module_driver::validate_decl_read_only;
use clean_elab::{elaborate, elaborate_decl};
use clean_kernel::{Environment, TypeChecker};
use clean_parser::{parse_decl_with_tactics_exact, parse_expr_with_tactics_exact, TacticPatterns};
use serde_json::json;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::OwnedRwLockReadGuard;
use tracing::{debug, instrument};

/// What work on the pool reads: the shared environment, held for reading until
/// the work ends, and the parser's tactic table.
pub(super) struct WorkEnv {
    pub(super) env: OwnedRwLockReadGuard<Environment>,
    pub(super) patterns: Arc<TacticPatterns>,
}

impl WorkEnv {
    /// Take a read hold on `state`'s environment. A request that will run work
    /// takes its work slot first (`work.rs`, "Lock order"): never await a slot
    /// while holding this.
    pub(super) async fn read(state: &ServerState) -> Self {
        Self {
            env: state.env.read_owned().await,
            patterns: Arc::clone(&state.tactic_patterns),
        }
    }
}

/// Wait for a work slot, then hold `state`'s environment and run `work` on the
/// pool under `deadline`. Await it inside the request's timeout. The order is
/// the pool's lock order (`work.rs`): a slot, then the environment.
pub(super) async fn run_with_env<T: Send + 'static>(
    state: &ServerState,
    deadline: Option<Instant>,
    work: impl FnOnce(&WorkEnv) -> T + Send + 'static,
) -> Result<T, WorkError> {
    // The slot first: a request waiting for one holds no lock.
    let slot = state.work.slot().await?;
    let held = WorkEnv::read(state).await;
    WorkPool::run_in(slot, deadline, move || work(&held)).await
}

/// Answer a request whose work reads the environment and changes nothing (a
/// search, an encoding): `answer` builds the response on the pool under the
/// request's deadline, holding the environment for reading ([`run_with_env`]),
/// inside its `timeout`, which `start` began. A request whose timeout fires
/// first answers the timeout error.
pub(super) async fn answer_with_env(
    state: &ServerState,
    id: RequestId,
    start: Instant,
    timeout: Duration,
    answer: impl FnOnce(RequestId, &Environment) -> Response + Send + 'static,
) -> Response {
    let deadline = start.checked_add(timeout);
    let answering = id.clone();
    let answered = within(
        timeout,
        run_with_env(state, deadline, move |held| answer(answering, &held.env)),
    )
    .await;
    match answered {
        Ok(response) => response,
        Err(error) => Response::error(id, error.into_rpc_error(timeout)),
    }
}

/// Wait for a work slot, then take a read hold on `state`'s environment that
/// the request shares with its work, for a request that answers from the
/// environment after its work has run: it renders from this hold and never
/// reads the environment a second time. A writer queued while the work ran
/// would be granted between two reads, so the second would wait outside the
/// request's timeout and see another environment than the work checked in.
/// Await it inside the request's timeout. The order is the pool's lock order
/// (`work.rs`): a slot, then the environment.
pub(super) async fn slot_then_env(
    state: &ServerState,
) -> Result<(WorkSlot, Arc<WorkEnv>), WorkError> {
    let slot = state.work.slot().await?;
    let held = Arc::new(WorkEnv::read(state).await);
    Ok((slot, held))
}

/// Handle the "check" method
#[instrument(skip(state, params))]
pub async fn handle_check(state: &ServerState, id: RequestId, params: CheckParams) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));
    let deadline = start.checked_add(timeout);
    let code = params.code;

    let result = tokio::time::timeout(
        timeout,
        run_with_env(state, deadline, move |held| check_code(held, &code)),
    )
    .await;

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(Ok((mut check_result, sample))) => {
            if let Some(sample) = sample {
                state.cache_metrics.record_sample(&sample);
            }
            check_result.time_ms = elapsed_ms;
            check_result.time_ns = Some(ns_from_us(elapsed_us));
            let success = check_result.valid;
            state.metrics.record_request("check", success, elapsed_us);
            Response::success_typed(id.clone(), &check_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(WorkError::Unavailable(detail))) => {
            state.metrics.record_request("check", false, elapsed_us);
            Response::error(id, RpcError::internal_error(detail))
        }
        Ok(Err(WorkError::Interrupted)) | Err(_) => {
            state.metrics.record_request("check", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

/// Check `code` (an expression, else a declaration) against the held
/// environment, read-only. Runs on the work pool. Returns the type checker's
/// cache sample when a checker ran.
pub(super) fn check_code(held: &WorkEnv, code: &str) -> (CheckResult, Option<TypeCheckerSample>) {
    let env: &Environment = &held.env;
    // First try to parse as expression (with tactic patterns for Named dispatch)
    if let Ok(surface_expr) = parse_expr_with_tactics_exact(code, &held.patterns) {
        match elaborate(env, &surface_expr) {
            Ok(expr) => {
                let tc = TypeChecker::with_mode(env, env.mode());
                let type_result = tc.infer_type(&expr);
                let sample = TypeCheckerSample::of(&tc);
                let result = match type_result {
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
                };
                return (result, Some(sample));
            }
            Err(e) => {
                let result = CheckResult {
                    valid: false,
                    inferred_type: None,
                    errors: vec![CheckError {
                        message: format!("Elaboration error: {e}"),
                        line: None,
                        column: None,
                    }],
                    time_ms: 0,
                    time_ns: None,
                };
                return (result, None);
            }
        }
    }

    // Try to parse as declaration (with tactic patterns for Named dispatch)
    match parse_decl_with_tactics_exact(code, &held.patterns) {
        Ok(surface_decl) => match elaborate_decl(env, &surface_decl) {
            Ok(decl) => {
                let tc = TypeChecker::with_mode(env, env.mode());
                let validation = validate_decl_read_only(env, &tc, &decl);
                let sample = TypeCheckerSample::of(&tc);
                let result = match validation {
                    Ok(inferred_type) => CheckResult {
                        valid: true,
                        inferred_type,
                        errors: vec![],
                        time_ms: 0,
                        time_ns: None,
                    },
                    Err(message) => CheckResult {
                        valid: false,
                        inferred_type: None,
                        errors: vec![CheckError {
                            message,
                            line: None,
                            column: None,
                        }],
                        time_ms: 0,
                        time_ns: None,
                    },
                };
                (result, Some(sample))
            }
            Err(e) => {
                let result = CheckResult {
                    valid: false,
                    inferred_type: None,
                    errors: vec![CheckError {
                        message: format!("Elaboration error: {e}"),
                        line: None,
                        column: None,
                    }],
                    time_ms: 0,
                    time_ns: None,
                };
                (result, None)
            }
        },
        Err(e) => {
            let result = CheckResult {
                valid: false,
                inferred_type: None,
                errors: vec![CheckError {
                    message: format_parse_error(&e),
                    line: parse_error_line(&e),
                    column: parse_error_col(&e),
                }],
                time_ms: 0,
                time_ns: None,
            };
            (result, None)
        }
    }
}

/// Handle the "prove" method
#[instrument(skip(state, params))]
pub async fn handle_prove(state: &ServerState, id: RequestId, params: ProveParams) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));
    let deadline = start.checked_add(timeout);

    let result = tokio::time::timeout(
        timeout,
        run_with_env(state, deadline, move |held| {
            prove_impl(held, &params, timeout, deadline)
        }),
    )
    .await;

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(Ok(Ok(mut prove_result))) => {
            prove_result.time_ms = elapsed_ms;
            prove_result.time_ns = Some(ns_from_us(elapsed_us));
            let success = prove_result.found;
            state.metrics.record_request("prove", success, elapsed_us);
            Response::success_typed(id.clone(), &prove_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Ok(Err(e))) => {
            state.metrics.record_request("prove", false, elapsed_us);
            Response::error(id, e)
        }
        Ok(Err(WorkError::Unavailable(detail))) => {
            state.metrics.record_request("prove", false, elapsed_us);
            Response::error(id, RpcError::internal_error(detail))
        }
        Ok(Err(WorkError::Interrupted)) | Err(_) => {
            state.metrics.record_request("prove", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

/// Parse, elaborate and prove on the work pool. The proof search gets what is
/// left of the request's time, not the whole of it: parsing and elaboration
/// spent the rest.
fn prove_impl(
    held: &WorkEnv,
    params: &ProveParams,
    timeout: Duration,
    deadline: Option<Instant>,
) -> Result<ProveResult, RpcError> {
    // Parse the goal exactly (reject trailing garbage)
    let goal_surface = parse_expr_with_tactics_exact(&params.goal, &held.patterns)
        .map_err(|e| RpcError::lean_parse_error(format!("Failed to parse goal: {e}")))?;

    let env: &Environment = &held.env;

    // Elaborate the goal
    let goal_expr = elaborate(env, &goal_surface)
        .map_err(|e| RpcError::elaboration_error(format!("Failed to elaborate goal: {e}")))?;

    // Parse and elaborate hypotheses into (Expr, Option<QuantifierOrigin>) pairs
    // for the AutomationEngine query interface.
    let mut hypotheses: Vec<(
        clean_kernel::Expr,
        Option<clean_auto::bridge::QuantifierOrigin>,
    )> = Vec::with_capacity(params.hypotheses.len());
    for (i, hyp_str) in params.hypotheses.iter().enumerate() {
        let hyp_surface = parse_expr_with_tactics_exact(hyp_str, &held.patterns).map_err(|e| {
            RpcError::lean_parse_error(format!("Failed to parse hypothesis {i}: {e}"))
        })?;

        let hyp_expr = elaborate(env, &hyp_surface).map_err(|e| {
            RpcError::elaboration_error(format!("Failed to elaborate hypothesis {i}: {e}"))
        })?;

        hypotheses.push((hyp_expr, None));
    }

    let remaining = deadline.map_or(timeout, |deadline| {
        deadline.saturating_duration_since(Instant::now())
    });
    let strategy = params.strategy.as_deref().unwrap_or("auto");

    prove_with_strategy(env, &goal_expr, &hypotheses, remaining, strategy)
}

/// Handle the "getType" method
#[instrument(skip(state, params))]
pub async fn handle_get_type(
    state: &ServerState,
    id: RequestId,
    params: GetTypeParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));
    let deadline = start.checked_add(timeout);

    // Until 2026-10-15 `getType` took no timeout and its work ran without a
    // deadline, holding its slot until it ended: a few slow ones filled every
    // slot. It runs under its deadline now, like `check`.
    let expr = params.expr;
    let result = within(
        timeout,
        run_with_env(state, deadline, move |held| get_type_impl(held, &expr)),
    )
    .await;
    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    let result = match result {
        Ok((result, sample)) => {
            if let Some(sample) = sample {
                state.cache_metrics.record_sample(&sample);
            }
            result
        }
        Err(error) => Err(error.into_rpc_error(timeout)),
    };

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

fn get_type_impl(
    held: &WorkEnv,
    expr_str: &str,
) -> (Result<GetTypeResult, RpcError>, Option<TypeCheckerSample>) {
    let surface_expr = match parse_expr_with_tactics_exact(expr_str, &held.patterns) {
        Ok(surface_expr) => surface_expr,
        Err(e) => {
            return (
                Err(RpcError::lean_parse_error(format!("Parse error: {e}"))),
                None,
            )
        }
    };

    let env: &Environment = &held.env;

    let expr = match elaborate(env, &surface_expr) {
        Ok(expr) => expr,
        Err(e) => {
            return (
                Err(RpcError::elaboration_error(format!(
                    "Elaboration error: {e}"
                ))),
                None,
            )
        }
    };

    let tc = TypeChecker::with_mode(env, env.mode());
    let type_result = tc
        .infer_type(&expr)
        .map_err(|e| RpcError::type_error(format!("Type error: {e}")));
    let sample = TypeCheckerSample::of(&tc);
    let result = type_result.map(|type_| GetTypeResult {
        type_: format_expr(&type_),
        time_ms: 0,
        time_ns: None,
    });
    (result, Some(sample))
}

/// Handle the "batchCheck" method
#[instrument(skip(state, params))]
pub async fn handle_batch_check(
    state: &ServerState,
    id: RequestId,
    params: BatchCheckParams,
    progress: Option<ProgressSender>,
) -> Response {
    let start = Instant::now();
    let item_count = params.items.len() as u64;
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms * 10));
    let deadline = start.checked_add(timeout);

    let result = tokio::time::timeout(timeout, async {
        batch_check_impl(state, params, progress.clone(), deadline).await
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
        Ok(Err(WorkError::Unavailable(detail))) => {
            state
                .metrics
                .record_request("batchCheck", false, elapsed_us);
            Response::error(id, RpcError::internal_error(detail))
        }
        Ok(Err(WorkError::Interrupted)) | Err(_) => {
            state
                .metrics
                .record_request("batchCheck", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

async fn batch_check_impl(
    state: &ServerState,
    params: BatchCheckParams,
    progress: Option<ProgressSender>,
    deadline: Option<Instant>,
) -> Result<BatchCheckResult, WorkError> {
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

    // The items are checked in order on the work pool; each result comes back
    // over `checked` as it is found, for the progress stream, and the whole
    // list when the batch ends. The clock is read before each item and after
    // it: no item starts past the deadline, and an item the deadline may have
    // cut short is no verdict, so it is neither reported nor kept (`None`).
    let (checked, mut each_checked) = tokio::sync::mpsc::unbounded_channel();
    let items = params.items;
    let work = run_with_env(state, deadline, move |held| {
        let mut results = Vec::with_capacity(items.len());
        let mut samples = Vec::new();
        for item in items {
            if past(deadline) {
                return None;
            }
            let (check_result, sample) = check_code(held, &item.code);
            if past(deadline) {
                return None;
            }
            samples.extend(sample);
            let result = BatchCheckItemResult {
                id: item.id,
                valid: check_result.valid,
                error: check_result.errors.into_iter().next().map(|e| e.message),
            };
            // The request may have stopped listening; the batch goes on.
            let _ = checked.send(result.clone());
            results.push(result);
        }
        Some((results, samples))
    });
    let report = async {
        let mut completed = 0usize;
        while let Some(result) = each_checked.recv().await {
            completed += 1;
            let Some(progress) = progress.as_ref() else {
                continue;
            };
            // Only send progress on interval boundaries, first item, or last item
            let should_report =
                completed % progress_interval == 0 || completed == total || completed == 1;
            if should_report {
                let percentage = (completed * 100)
                    .checked_div(total)
                    .map_or(100, |p| p.min(100) as u8);

                progress
                    .notify(
                        format!("Checked {}/{} ({})", completed, total, result.id),
                        Some(percentage),
                        Some(json!({
                            "id": result.id,
                            "valid": result.valid,
                            "error": result.error,
                        })),
                    )
                    .await;
            }
        }
    };
    let (finished, ()) = tokio::join!(work, report);
    let (results, samples) = finished?.ok_or(WorkError::Interrupted)?;
    for sample in &samples {
        state.cache_metrics.record_sample(sample);
    }

    Ok(BatchCheckResult {
        results,
        time_ms: 0,
        time_ns: None,
        gpu_used: false,
        warnings,
    })
}
