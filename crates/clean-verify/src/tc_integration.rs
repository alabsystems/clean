// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! tC backend integration protocol for clean-side VC submission and proof retrieval.

use crate::vc_protocol::VcInputFormat;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Mutex;
use std::time::Duration;
use thiserror::Error;

/// One verification condition submitted to the external tC backend.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcSubmission {
    /// Stable caller-provided verification condition identifier.
    pub vc_id: String,
    /// Payload format expected by the backend.
    pub format: VcInputFormat,
    /// Serialized verification condition body.
    pub payload: String,
    /// Maximum backend processing time for this VC.
    pub timeout: Duration,
}

impl VcSubmission {
    /// Construct one backend-facing VC submission.
    #[must_use]
    pub fn new(
        vc_id: impl Into<String>,
        format: VcInputFormat,
        payload: impl Into<String>,
        timeout: Duration,
    ) -> Self {
        Self {
            vc_id: vc_id.into(),
            format,
            payload: payload.into(),
            timeout,
        }
    }
}

/// Final backend verdict for a submitted verification condition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VcVerdict {
    /// The backend proved the VC valid.
    Valid,
    /// The backend found the VC invalid.
    Invalid,
    /// The backend could not determine the result.
    Unknown,
    /// The backend exceeded the requested timeout.
    Timeout,
}

/// Observable processing state for one submitted VC.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TcBackendStatus {
    /// The backend has accepted the VC but not finished processing it.
    Pending,
    /// The backend completed processing and produced a final verdict.
    Completed {
        /// Final verdict returned by the backend.
        verdict: VcVerdict,
    },
}

/// Connection parameters for the tC integration boundary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TcIntegrationConfig {
    /// Endpoint or DSN used to contact the backend.
    pub endpoint: String,
    /// Optional bearer token or shared secret for backend authentication.
    pub auth_token: Option<String>,
    /// Dial timeout for establishing the backend connection.
    pub connect_timeout: Duration,
    /// Default request timeout for polling and proof retrieval.
    pub request_timeout: Duration,
}

impl TcIntegrationConfig {
    /// Construct a config for one backend endpoint.
    #[must_use]
    pub fn new(endpoint: impl Into<String>) -> Self {
        Self {
            endpoint: endpoint.into(),
            ..Self::default()
        }
    }
}

impl Default for TcIntegrationConfig {
    fn default() -> Self {
        Self {
            endpoint: "mock://tc-backend".to_string(),
            auth_token: None,
            connect_timeout: Duration::from_secs(5),
            request_timeout: Duration::from_secs(30),
        }
    }
}

/// Errors returned by the tC backend integration protocol.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum TcBackendError {
    /// Caller attempted to submit a VC without an identifier.
    #[error("verification condition id must be non-empty")]
    MissingVcId,
    /// Caller attempted to submit an empty backend payload.
    #[error("verification condition `{vc_id}` payload must be non-empty")]
    EmptyPayload {
        /// Verification condition identifier.
        vc_id: String,
    },
    /// Caller attempted to resubmit an already tracked VC id.
    #[error("verification condition `{0}` has already been submitted")]
    DuplicateVc(String),
    /// Backend was asked about an unknown verification condition.
    #[error("verification condition `{0}` was not found")]
    UnknownVc(String),
    /// Mock backend state became unavailable.
    #[error("backend state is unavailable: {0}")]
    BackendState(String),
}

/// Protocol-local result type.
pub type Result<T> = std::result::Result<T, TcBackendError>;

/// clean-facing protocol for the external tC backend.
pub trait TcBackendProtocol: Send + Sync {
    /// Submit one verification condition for asynchronous processing.
    fn submit_vc(&self, submission: VcSubmission) -> Result<()>;

    /// Query the backend for the current processing status of one VC.
    fn query_status(&self, vc_id: &str) -> Result<TcBackendStatus>;

    /// Retrieve a proof artifact when the backend can produce one.
    fn retrieve_proof(&self, vc_id: &str) -> Result<Option<String>>;
}

#[derive(Clone, Debug)]
struct MockRecord {
    verdict: VcVerdict,
    proof: Option<String>,
}

/// In-memory tC backend for integration tests and API wiring.
#[derive(Debug)]
pub struct MockTcBackend {
    /// Public so tests and callers can inspect the configured connection surface.
    pub config: TcIntegrationConfig,
    records: Mutex<HashMap<String, MockRecord>>,
}

impl Default for MockTcBackend {
    fn default() -> Self {
        Self::new(TcIntegrationConfig::default())
    }
}

impl MockTcBackend {
    /// Create an empty mock backend with the provided config.
    #[must_use]
    pub fn new(config: TcIntegrationConfig) -> Self {
        Self {
            config,
            records: Mutex::new(HashMap::new()),
        }
    }

    fn lock_records(
        &self,
    ) -> std::result::Result<std::sync::MutexGuard<'_, HashMap<String, MockRecord>>, TcBackendError>
    {
        self.records.lock().map_err(|_| {
            TcBackendError::BackendState("mock backend record store poisoned".to_string())
        })
    }
}

impl TcBackendProtocol for MockTcBackend {
    fn submit_vc(&self, submission: VcSubmission) -> Result<()> {
        let vc_id = submission.vc_id.trim();
        if vc_id.is_empty() {
            return Err(TcBackendError::MissingVcId);
        }
        if submission.payload.trim().is_empty() {
            return Err(TcBackendError::EmptyPayload {
                vc_id: vc_id.to_string(),
            });
        }

        let mut records = self.lock_records()?;
        if records.contains_key(vc_id) {
            return Err(TcBackendError::DuplicateVc(vc_id.to_string()));
        }

        let verdict = classify_payload(&submission.payload);
        let proof = match verdict {
            VcVerdict::Valid => Some(format!(
                "mock-proof:{}:{}",
                vc_id,
                format_label(submission.format)
            )),
            VcVerdict::Invalid | VcVerdict::Unknown | VcVerdict::Timeout => None,
        };

        records.insert(vc_id.to_string(), MockRecord { verdict, proof });
        Ok(())
    }

    fn query_status(&self, vc_id: &str) -> Result<TcBackendStatus> {
        let records = self.lock_records()?;
        let record = records
            .get(vc_id)
            .ok_or_else(|| TcBackendError::UnknownVc(vc_id.to_string()))?;
        Ok(TcBackendStatus::Completed {
            verdict: record.verdict,
        })
    }

    fn retrieve_proof(&self, vc_id: &str) -> Result<Option<String>> {
        let records = self.lock_records()?;
        let record = records
            .get(vc_id)
            .ok_or_else(|| TcBackendError::UnknownVc(vc_id.to_string()))?;
        Ok(record.proof.clone())
    }
}

fn classify_payload(payload: &str) -> VcVerdict {
    let payload = payload.to_ascii_lowercase();
    if payload.contains("timeout") {
        VcVerdict::Timeout
    } else if payload.contains("invalid") {
        VcVerdict::Invalid
    } else if payload.contains("unknown") {
        VcVerdict::Unknown
    } else {
        VcVerdict::Valid
    }
}

fn format_label(format: VcInputFormat) -> &'static str {
    match format {
        VcInputFormat::SmtLib2 => "smtlib2",
        VcInputFormat::Why3 => "why3",
        VcInputFormat::Custom => "custom",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mock_backend_round_trips_valid_submission() {
        let backend = MockTcBackend::default();
        let submission = VcSubmission::new(
            "vc.add.nonneg",
            VcInputFormat::SmtLib2,
            "(assert (=> (and (>= x 0) (>= y 0)) (>= (+ x y) 0)))",
            Duration::from_secs(2),
        );

        backend.submit_vc(submission).expect("submit VC");

        assert_eq!(
            backend.query_status("vc.add.nonneg").expect("query status"),
            TcBackendStatus::Completed {
                verdict: VcVerdict::Valid,
            }
        );
        assert_eq!(
            backend
                .retrieve_proof("vc.add.nonneg")
                .expect("retrieve proof"),
            Some("mock-proof:vc.add.nonneg:smtlib2".to_string())
        );
    }

    #[test]
    fn mock_backend_round_trips_invalid_submission_without_proof() {
        let backend = MockTcBackend::new(TcIntegrationConfig::new("mock://integration-test"));
        let submission = VcSubmission::new(
            "vc.array.bounds",
            VcInputFormat::Why3,
            "invalid: counterexample for array bounds",
            Duration::from_millis(750),
        );

        backend.submit_vc(submission).expect("submit VC");

        assert_eq!(
            backend
                .query_status("vc.array.bounds")
                .expect("query status"),
            TcBackendStatus::Completed {
                verdict: VcVerdict::Invalid,
            }
        );
        assert_eq!(
            backend
                .retrieve_proof("vc.array.bounds")
                .expect("retrieve proof"),
            None
        );
    }

    #[test]
    fn mock_backend_rejects_duplicate_ids() {
        let backend = MockTcBackend::default();
        let submission = VcSubmission::new(
            "vc.dup",
            VcInputFormat::Custom,
            "opaque payload",
            Duration::from_secs(1),
        );

        backend
            .submit_vc(submission.clone())
            .expect("initial submission");
        let err = backend
            .submit_vc(submission)
            .expect_err("duplicate id should fail");

        assert_eq!(err, TcBackendError::DuplicateVc("vc.dup".to_string()));
    }
}
