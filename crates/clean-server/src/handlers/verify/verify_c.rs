// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler for verifyC: C code verification with ACSL specifications.
//!
//! The verification runs on the server's work pool under the request's deadline
//! (`handlers/work.rs`), and reads the clock between functions, stopping once
//! the deadline has passed.

use super::types::*;
use crate::handlers::state::ServerState;
use crate::handlers::types::ns_from_us;
use crate::handlers::work::{past, WorkError};
use crate::progress::ProgressSender;
use crate::rpc::{RequestId, Response, RpcError};
use clean_c_sem::auto::ProofStatus;
use clean_c_sem::parser::CParser;
use serde_json::json;
use std::time::{Duration, Instant};
use tracing::instrument;

/// Handle the "verifyC" method
#[instrument(skip(state, params))]
pub async fn handle_verify_c(
    state: &ServerState,
    id: RequestId,
    params: VerifyCParams,
    progress: Option<ProgressSender>,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms * 2));
    let deadline = start.checked_add(timeout);

    let result = tokio::time::timeout(timeout, async {
        verify_c_impl(state, params, progress.clone(), deadline).await
    })
    .await
    .unwrap_or(Err(WorkError::Interrupted));

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(Ok(mut verify_result)) => {
            verify_result.time_ms = elapsed_ms;
            verify_result.time_ns = Some(ns_from_us(elapsed_us));
            let success = verify_result.success;
            state.metrics.record_request("verifyC", success, elapsed_us);
            Response::success_typed(id.clone(), &verify_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => {
            state.metrics.record_request("verifyC", false, elapsed_us);
            Response::error(id, e)
        }
        Err(WorkError::Unavailable(detail)) => {
            state.metrics.record_request("verifyC", false, elapsed_us);
            Response::error(id, RpcError::internal_error(detail))
        }
        Err(WorkError::Interrupted) => {
            state.metrics.record_request("verifyC", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

/// One progress line, sent from the work to the request.
struct Line {
    message: String,
    percentage: Option<u8>,
    details: Option<serde_json::Value>,
}

/// Run the verification on the work pool under `deadline`, forwarding its
/// progress lines to `progress` as they come.
async fn verify_c_impl(
    state: &ServerState,
    params: VerifyCParams,
    progress: Option<ProgressSender>,
    deadline: Option<Instant>,
) -> Result<Result<VerifyCResult, RpcError>, WorkError> {
    let (lines, mut each_line) = tokio::sync::mpsc::unbounded_channel::<Line>();
    let reporting = progress.is_some();
    let work = state.work.run(deadline, move || {
        verify_c_sync(&params, deadline, |line| {
            if reporting {
                let _ = lines.send(line);
            }
        })
    });
    let report = async {
        while let Some(line) = each_line.recv().await {
            if let Some(ref progress) = progress {
                progress
                    .notify(line.message, line.percentage, line.details)
                    .await;
            }
        }
    };
    let (finished, ()) = tokio::join!(work, report);
    finished?.ok_or(WorkError::Interrupted)
}

/// Verify every function of the source. Runs on the work pool, reading the
/// clock before and after each function: `None` once the request's deadline
/// has passed, and a function it passed during is not reported.
fn verify_c_sync(
    params: &VerifyCParams,
    deadline: Option<Instant>,
    progress: impl Fn(Line),
) -> Option<Result<VerifyCResult, RpcError>> {
    let mut parser = CParser::new();

    // Parse the C source with ACSL specs
    let functions = match parser.parse_translation_unit_with_specs(&params.code) {
        Ok(functions) => functions,
        Err(e) => {
            return Some(Err(RpcError::lean_parse_error(format!(
                "C parse error: {e}"
            ))))
        }
    };

    if functions.is_empty() {
        return Some(Ok(VerifyCResult {
            success: true,
            num_functions: 0,
            total_vcs: 0,
            proved: 0,
            unverified: 0,
            failed: 0,
            unknown: 0,
            functions: vec![],
            errors: vec!["No functions found in source".to_string()],
            time_ms: 0,
            time_ns: None,
        }));
    }

    let total_functions = functions.len();
    let mut func_results = Vec::with_capacity(total_functions);
    let mut total_vcs = 0;
    let mut total_proved = 0;
    let mut total_unverified = 0;
    let mut total_failed = 0;
    let mut total_unknown = 0;

    progress(Line {
        message: format!("Verifying {total_functions} function(s)"),
        percentage: Some(0),
        details: None,
    });

    for (idx, vf) in functions.into_iter().enumerate() {
        if past(deadline) {
            return None;
        }
        let summary = vf.verify();
        // A function the deadline may have cut short is no verdict: not
        // reported, and the request answers the timeout error.
        if past(deadline) {
            return None;
        }

        // Build per-VC details if requested
        let details = if params.include_details {
            summary
                .details
                .iter()
                .map(|(desc, status)| {
                    let (status_str, reason) = match status {
                        ProofStatus::SmtBridgeChecked(_) => ("proved".to_string(), None),
                        ProofStatus::StructuralMatched => ("structural_matched".to_string(), None),
                        ProofStatus::Unverified(r) => ("unverified".to_string(), Some(r.clone())),
                        ProofStatus::Failed(r) => ("failed".to_string(), Some(r.clone())),
                        ProofStatus::Unknown => ("unknown".to_string(), None),
                    };
                    VerifyCVCDetail {
                        description: desc.clone(),
                        status: status_str,
                        reason,
                    }
                })
                .collect()
        } else {
            vec![]
        };

        let func_result = VerifyCFunctionResult {
            name: vf.name.clone(),
            total_vcs: summary.total,
            proved: summary.proved,
            failed: summary.failed,
            unknown: summary.unknown,
            details,
        };

        total_vcs += summary.total;
        total_proved += summary.proved;
        total_unverified += summary.unverified;
        total_failed += summary.failed;
        total_unknown += summary.unknown;

        func_results.push(func_result);

        let percentage = ((idx + 1) * 100)
            .checked_div(total_functions)
            .map_or(100, |p| p.min(100) as u8);
        progress(Line {
            message: format!(
                "Verified {}/{} ({}: {} proved)",
                idx + 1,
                total_functions,
                vf.name,
                summary.proved
            ),
            percentage: Some(percentage),
            details: Some(json!({
                "function": vf.name,
                "proved": summary.proved,
                "failed": summary.failed,
                "unknown": summary.unknown,
            })),
        });
    }

    // SOUNDNESS (hole 11): success is fail-closed — every obligation must be
    // established (SMT bridge / structural match) or discharged as a valid
    // SMT-UNSAT goal (Unverified). A `Failed` (refuted) OR `Unknown`
    // (unproved / unsupported gap) obligation means the program is NOT
    // verified. `Unknown` must fail unconditionally — it previously passed
    // whenever `fail_unknown` was false, letting an unproved obligation
    // certify the program. The `fail_unknown` flag now only tightens further
    // (treating even SMT-UNSAT `Unverified` goals as not-verified).
    // See docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md holes 3,11.
    let unverified_ok = total_proved + total_unverified == total_vcs;
    let success = total_failed == 0
        && total_unknown == 0
        && unverified_ok
        && (!params.fail_unknown || total_unverified == 0);

    Some(Ok(VerifyCResult {
        success,
        num_functions: func_results.len(),
        total_vcs,
        proved: total_proved,
        unverified: total_unverified,
        failed: total_failed,
        unknown: total_unknown,
        functions: func_results,
        errors: vec![],
        time_ms: 0,
        time_ns: None,
    }))
}
