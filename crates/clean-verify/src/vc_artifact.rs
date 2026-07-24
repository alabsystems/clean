// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured verification-condition artifacts and storage interfaces.

use clean_kernel::Expr;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use thiserror::Error;

/// Stable source location for a verification condition.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceLocation {
    /// Source file path.
    pub file: String,
    /// 1-based source line.
    pub line: u32,
    /// 1-based source column.
    pub column: u32,
    /// Length of the source span in characters.
    #[serde(default)]
    pub span: u32,
}

/// Verification status for a single VC artifact.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VcStatus {
    /// Obligation was discharged successfully.
    Verified,
    /// Obligation was shown to be invalid or could not be proved.
    Failed,
    /// Backend could not determine the result.
    Unknown,
    /// Backend timed out while trying to discharge the obligation.
    Timeout,
}

/// Structured artifact for one verification condition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcArtifact {
    /// Source location for the originating obligation.
    pub source: SourceLocation,
    /// Stable obligation identifier.
    pub obligation_name: String,
    /// Goal type, serialized through the kernel `Expr` serde implementation.
    pub goal_type: Expr,
    /// Local hypotheses available while proving the goal.
    pub hypotheses: Vec<(String, Expr)>,
    /// Current verification status.
    pub status: VcStatus,
    /// Backend or prover responsible for the current status.
    pub prover: String,
    /// Unix timestamp in seconds.
    pub timestamp: u64,
    /// Optional wall-clock duration in milliseconds.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub duration_ms: Option<u64>,
}

impl VcArtifact {
    /// Serialize the artifact into compact JSON.
    pub fn to_json(&self) -> std::result::Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Serialize the artifact into pretty-printed JSON.
    pub fn to_json_pretty(&self) -> std::result::Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Parse an artifact from JSON.
    pub fn from_json(json: &str) -> std::result::Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

/// Errors produced by VC artifact stores.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum VcArtifactStoreError {
    /// Generic store failure.
    #[error("{message}")]
    Message { message: String },
}

/// Store result type for VC artifact persistence.
pub type Result<T> = std::result::Result<T, VcArtifactStoreError>;

/// Persistence interface for VC artifacts.
pub trait VcArtifactStore {
    /// Save or update an artifact by obligation name.
    fn save(&mut self, artifact: &VcArtifact) -> Result<()>;

    /// Load the most recent artifact for an obligation name, if present.
    fn load(&self, obligation_name: &str) -> Result<Option<VcArtifact>>;

    /// ListType all artifacts with a matching status in stable obligation-name order.
    fn query_by_status(&self, status: VcStatus) -> Result<Vec<VcArtifact>>;

    /// ListType all artifacts at an exact source location in stable obligation-name order.
    fn query_by_location(&self, location: &SourceLocation) -> Result<Vec<VcArtifact>>;
}

/// In-memory VC artifact store for tests and lightweight callers.
#[derive(Clone, Debug, Default)]
pub struct InMemoryVcStore {
    artifacts: HashMap<String, VcArtifact>,
}

impl InMemoryVcStore {
    /// Create an empty in-memory store.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// ListType artifacts with a matching status in stable obligation-name order.
    #[must_use]
    pub fn query_by_status(&self, status: VcStatus) -> Vec<VcArtifact> {
        self.list_matching(|artifact| artifact.status == status)
    }

    /// ListType artifacts at an exact source location in stable obligation-name order.
    #[must_use]
    pub fn query_by_location(&self, location: &SourceLocation) -> Vec<VcArtifact> {
        self.list_matching(|artifact| artifact.source == *location)
    }

    fn list_matching(&self, predicate: impl Fn(&VcArtifact) -> bool) -> Vec<VcArtifact> {
        let mut artifacts: Vec<_> = self
            .artifacts
            .values()
            .filter(|artifact| predicate(artifact))
            .cloned()
            .collect();
        artifacts.sort_by(|lhs, rhs| lhs.obligation_name.cmp(&rhs.obligation_name));
        artifacts
    }
}

impl VcArtifactStore for InMemoryVcStore {
    fn save(&mut self, artifact: &VcArtifact) -> Result<()> {
        self.artifacts
            .insert(artifact.obligation_name.clone(), artifact.clone());
        Ok(())
    }

    fn load(&self, obligation_name: &str) -> Result<Option<VcArtifact>> {
        Ok(self.artifacts.get(obligation_name).cloned())
    }

    fn query_by_status(&self, status: VcStatus) -> Result<Vec<VcArtifact>> {
        Ok(InMemoryVcStore::query_by_status(self, status))
    }

    fn query_by_location(&self, location: &SourceLocation) -> Result<Vec<VcArtifact>> {
        Ok(InMemoryVcStore::query_by_location(self, location))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_artifact(name: &str, status: VcStatus, line: u32, column: u32) -> VcArtifact {
        VcArtifact {
            source: SourceLocation {
                file: "src/spec/core_spec/type_preservation.rs".to_string(),
                line,
                column,
                span: 5,
            },
            obligation_name: name.to_string(),
            goal_type: Expr::arrow(Expr::prop(), Expr::type_()),
            hypotheses: vec![
                ("h_ctx".to_string(), Expr::const_str("CtxWellFormed")),
                ("h_term".to_string(), Expr::const_str("HasType")),
            ],
            status,
            prover: "kernel".to_string(),
            timestamp: 1_742_098_800,
            duration_ms: Some(12),
        }
    }

    #[test]
    fn vc_artifact_roundtrips_through_json() {
        let artifact = sample_artifact("vc.type_preservation.app", VcStatus::Verified, 42, 7);

        let json = artifact.to_json().expect("artifact should serialize");
        let decoded = VcArtifact::from_json(&json).expect("artifact should deserialize");

        assert_eq!(decoded, artifact);
        assert!(json.contains("\"status\":\"verified\""));
        assert!(json.contains("\"span\":5"));
    }

    #[test]
    fn in_memory_store_supports_status_and_location_queries() {
        let mut store = InMemoryVcStore::new();
        let verified = sample_artifact("vc.verified", VcStatus::Verified, 42, 7);
        let failed = sample_artifact("vc.failed", VcStatus::Failed, 42, 7);
        let timeout = sample_artifact("vc.timeout", VcStatus::Timeout, 80, 3);
        let unknown = sample_artifact("vc.unknown", VcStatus::Unknown, 81, 3);

        store.save(&timeout).expect("save timeout");
        store.save(&failed).expect("save failed");
        store.save(&unknown).expect("save unknown");
        store.save(&verified).expect("save verified");

        assert_eq!(
            store.load("vc.failed").expect("load failed"),
            Some(failed.clone())
        );
        assert_eq!(store.load("vc.missing").expect("load missing"), None);
        assert_eq!(
            store.query_by_status(VcStatus::Failed),
            vec![failed.clone()]
        );
        assert_eq!(
            store.query_by_location(&verified.source),
            vec![failed, verified]
        );
        assert_eq!(
            VcArtifactStore::query_by_status(&store, VcStatus::Unknown).expect("trait query"),
            vec![unknown]
        );
        assert_eq!(
            VcArtifactStore::query_by_location(&store, &timeout.source)
                .expect("trait location query"),
            vec![timeout]
        );
    }

    #[test]
    fn save_overwrites_existing_obligation() {
        let mut store = InMemoryVcStore::new();
        let unknown = sample_artifact("vc.same_name", VcStatus::Unknown, 9, 2);
        let verified = sample_artifact("vc.same_name", VcStatus::Verified, 11, 6);

        store.save(&unknown).expect("save unknown");
        store.save(&verified).expect("save verified");

        assert_eq!(
            store.load("vc.same_name").expect("load updated"),
            Some(verified.clone())
        );
        assert_eq!(
            store.query_by_status(VcStatus::Unknown),
            Vec::<VcArtifact>::new()
        );
        assert_eq!(store.query_by_location(&verified.source), vec![verified]);
    }
}
