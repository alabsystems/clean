// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Alethe certificate verification handler (Part of #1195).
//!
//! Extracted from `external_cert.rs` to keep files under the 500-line limit.

use super::external_cert::VerifyExternalCertParams;
use super::state::ServerState;
use super::types::ns_from_us;
use crate::rpc::{RequestId, Response, RpcError};
use clean_elab::cert::external::{
    verify_alethe_certificate, ExternalCertError, ExternalCertificate,
};
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};
use tracing::instrument;

#[cfg(test)]
use super::external_cert::TEST_DELAY_MS;

#[cfg(test)]
use std::sync::atomic::Ordering;

/// Apply test-only delay if configured.
#[cfg(test)]
async fn apply_test_delay() {
    let delay_ms = TEST_DELAY_MS.load(Ordering::Relaxed);
    if delay_ms > 0 {
        tokio::time::sleep(Duration::from_millis(delay_ms)).await;
    }
}

/// No-op in production.
#[cfg(not(test))]
async fn apply_test_delay() {}

/// Result of verifying an Alethe certificate.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyAletheCertResult {
    /// Whether the proof was fully verified with no holes.
    pub valid: bool,
    /// Error code if verification failed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    /// Detailed error message if verification failed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    /// Verification time in microseconds.
    pub time_us: u64,
    /// Verification time in nanoseconds (normalized alias, Part of #2515).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Handle a request to verify an Alethe certificate.
///
/// Verifies that the provided Alethe proof is accepted by Carcara as a fully
/// checked proof of the given SMT-LIB2 problem's unsatisfiability.
#[instrument(skip(state))]
pub async fn handle_verify_alethe_certificate(
    state: &ServerState,
    id: RequestId,
    params: VerifyExternalCertParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    let result = tokio::time::timeout(timeout, async {
        apply_test_delay().await;
        match params.certificate {
            ExternalCertificate::Alethe(cert) => verify_alethe_certificate(&cert),
            _ => Err(ExternalCertError::invalid_schema(
                "expected alethe_certificate".to_string(),
            )),
        }
    })
    .await;

    let elapsed_us = start.elapsed().as_micros() as u64;

    match result {
        Ok(Ok(valid)) => {
            state
                .metrics
                .record_request("verify_alethe_certificate", true, elapsed_us);
            let out = VerifyAletheCertResult {
                valid,
                error: None,
                detail: None,
                time_us: elapsed_us,
                time_ns: Some(ns_from_us(elapsed_us)),
            };
            Response::success_typed(id, &out).unwrap_or_else(|e| {
                Response::error(RequestId::Null, RpcError::internal_error(e.to_string()))
            })
        }
        Ok(Err(err)) => {
            state
                .metrics
                .record_request("verify_alethe_certificate", false, elapsed_us);
            let out = VerifyAletheCertResult {
                valid: false,
                error: Some(err.code.as_str().to_string()),
                detail: Some(err.detail),
                time_us: elapsed_us,
                time_ns: Some(ns_from_us(elapsed_us)),
            };
            Response::success_typed(id, &out).unwrap_or_else(|e| {
                Response::error(RequestId::Null, RpcError::internal_error(e.to_string()))
            })
        }
        Err(_) => {
            state
                .metrics
                .record_request("verify_alethe_certificate", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}
