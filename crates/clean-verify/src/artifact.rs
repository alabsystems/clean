// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured verification artifact output for `clean-verify`.

use crate::{VerificationFailure, VerificationResult};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

/// Verification backend used to produce a VC artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VerificationMode {
    /// clean kernel verification.
    Kernel,
    /// SMT-backed verification.
    SMT,
    /// Kani harness verification.
    Kani,
}

/// Verification status for a single property.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PropertyStatus {
    /// Property verified successfully.
    Verified,
    /// Property failed verification.
    Failed,
    /// Property timed out during verification.
    Timeout,
}

impl PropertyStatus {
    pub(crate) fn from_error(error: &str) -> Self {
        let error = error.to_ascii_lowercase();
        if error.contains("timeout") || error.contains("timed out") {
            Self::Timeout
        } else {
            Self::Failed
        }
    }
}

/// Source metadata and status for one verified property.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PropertyMetadata {
    /// Property identifier.
    pub name: String,
    /// Source file that registered the verification harness for this property.
    pub source_file: String,
    /// 1-based source line for the registration site.
    pub source_line: u32,
    /// Verification outcome for this property.
    pub status: PropertyStatus,
}

/// Structured artifact emitted by `clean-verify`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcArtifact {
    /// Artifact schema version encoded as a semver string.
    pub version: String,
    /// Verification backend used for this artifact.
    pub verification_mode: VerificationMode,
    /// Stable harness identifier for the run.
    pub harness_id: String,
    /// Per-property verification outcomes.
    pub properties: Vec<PropertyMetadata>,
    /// Optional SMT-LIB file emitted during verification.
    pub smt_file: Option<PathBuf>,
    /// Unix timestamp in seconds when the artifact was produced.
    pub timestamp: u64,
}

impl From<VerificationResult> for VcArtifact {
    fn from(result: VerificationResult) -> Self {
        let mut properties = result.properties;
        if properties.is_empty() && !result.failures.is_empty() {
            properties = result
                .failures
                .iter()
                .map(property_metadata_from_failure)
                .collect();
            properties.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
        }

        Self {
            version: env!("CARGO_PKG_VERSION").to_string(),
            verification_mode: VerificationMode::Kernel,
            harness_id: format!("{}::verify_kernel", env!("CARGO_PKG_NAME")),
            properties,
            smt_file: None,
            timestamp: current_timestamp_secs(),
        }
    }
}

fn property_metadata_from_failure(failure: &VerificationFailure) -> PropertyMetadata {
    let (source_file, source_line) = failure
        .location
        .as_deref()
        .and_then(parse_location)
        .unwrap_or_else(|| ("unknown".to_string(), 0));

    PropertyMetadata {
        name: failure.property.clone(),
        source_file,
        source_line,
        status: PropertyStatus::from_error(&failure.error),
    }
}

fn parse_location(location: &str) -> Option<(String, u32)> {
    let (source_file, source_line) = location.rsplit_once(':')?;
    let source_line = source_line.parse().ok()?;
    Some((source_file.to_string(), source_line))
}

fn current_timestamp_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}
