// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured evidence queries over a project's attempt logs
//! (current `.cake/attempts` plus the legacy `.mathverse/attempts`).

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::attempt_log::{
    ArtifactRef, AttemptId, AttemptStatus, AttemptStatusFilter, Blake3Hash, ProofAttempt,
    ATTEMPT_LOG_DIR, LEGACY_ATTEMPT_LOG_DIR,
};
use crate::env_fingerprint::EnvFingerprint;
use crate::error::{MathverseError, MathverseResult};

const ATTEMPTS_DIR: &str = "attempts";

/// Filter for Mathverse support evidence.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceQuery {
    /// Return evidence for one theorem/declaration name, when recorded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theorem_name: Option<String>,
    /// Return evidence for one task id, including `context.external_task_id`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub task_id: Option<String>,
    /// Return evidence emitted by one authority gate.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub authority_gate: Option<String>,
    /// Return one attempt id.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub attempt_id: Option<AttemptId>,
    /// Return attempts matching one status class.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub status: Option<AttemptStatusFilter>,
}

impl EvidenceQuery {
    fn matches(&self, record: &EvidenceSupportRecord) -> bool {
        if self
            .theorem_name
            .as_ref()
            .is_some_and(|name| record.theorem_name.as_ref() != Some(name))
        {
            return false;
        }
        if self
            .task_id
            .as_ref()
            .is_some_and(|task| record.task_id.as_ref() != Some(task))
        {
            return false;
        }
        if self
            .authority_gate
            .as_ref()
            .is_some_and(|gate| record.authority_gate.as_ref() != Some(gate))
        {
            return false;
        }
        if self
            .attempt_id
            .as_ref()
            .is_some_and(|attempt_id| &record.attempt_id != attempt_id)
        {
            return false;
        }
        if self
            .status
            .is_some_and(|status| record.status.kind() != status)
        {
            return false;
        }
        true
    }
}

/// Content-addressed artifact evidence attached to one support record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceArtifact {
    /// Stable role of the artifact in the attempt record.
    pub role: String,
    /// Content-addressed artifact reference.
    pub artifact: ArtifactRef,
}

/// Structured support evidence for one theorem/task/authority-gate attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceSupportRecord {
    /// UUIDv7-shaped attempt id.
    pub attempt_id: AttemptId,
    /// Final attempt status.
    pub status: AttemptStatus,
    /// Authority gate that emitted the record, when recorded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub authority_gate: Option<String>,
    /// Theorem or declaration name, normalized from top-level or context fields.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theorem_name: Option<String>,
    /// Task id, normalized from top-level fields or `context.external_task_id`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub task_id: Option<String>,
    /// BLAKE3 hash of the goal or normalized goal shape.
    pub goal_hash: Blake3Hash,
    /// BLAKE3 hash of the trust/audit report.
    pub trust_audit_hash: Blake3Hash,
    /// Artifact references attached to the attempt.
    #[serde(default)]
    pub artifacts: Vec<EvidenceArtifact>,
    /// Artifact hashes in the same order as `artifacts`, for lightweight callers.
    #[serde(default)]
    pub artifact_hashes: Vec<Blake3Hash>,
    /// Reproducible execution fingerprint recorded by the attempt.
    pub env: EnvFingerprint,
    /// Optional source fingerprint or source evidence field, when recorded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_fingerprint: Option<Value>,
    /// Producer/context metadata preserved from the attempt's `context` object.
    #[serde(default)]
    pub context_fields: BTreeMap<String, Value>,
    /// Extra top-level evidence fields not represented by `ProofAttempt`.
    #[serde(default)]
    pub extra_fields: BTreeMap<String, Value>,
    /// Nanoseconds since Unix epoch.
    pub created_at: u64,
    /// Wall-clock duration in milliseconds.
    pub wall_time_ms: u64,
}

/// In-memory evidence index scanned from `.cake/attempts/*.jsonl` and the
/// legacy `.mathverse/attempts/*.jsonl`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MathverseEvidenceIndex {
    /// Evidence records in deterministic log-file order.
    pub records: Vec<EvidenceSupportRecord>,
}

impl MathverseEvidenceIndex {
    /// Scan a project root for `.cake/attempts/*.jsonl` evidence, plus the
    /// legacy `.mathverse/attempts/*.jsonl` directory.
    pub fn scan(root: impl AsRef<Path>) -> MathverseResult<Self> {
        Ok(Self {
            records: scan_evidence_records(root)?,
        })
    }

    /// Query this in-memory index.
    pub fn query(&self, query: &EvidenceQuery) -> Vec<EvidenceSupportRecord> {
        self.records
            .iter()
            .filter(|record| query.matches(record))
            .cloned()
            .collect()
    }
}

/// Scan and query attempt-log evidence (`.cake` plus legacy `.mathverse`) in
/// one call.
pub fn query_mathverse_evidence(
    root: impl AsRef<Path>,
    query: EvidenceQuery,
) -> MathverseResult<Vec<EvidenceSupportRecord>> {
    Ok(MathverseEvidenceIndex::scan(root)?.query(&query))
}

fn scan_evidence_records(root: impl AsRef<Path>) -> MathverseResult<Vec<EvidenceSupportRecord>> {
    let mut records = Vec::new();
    for log_dir in [LEGACY_ATTEMPT_LOG_DIR, ATTEMPT_LOG_DIR] {
        let attempts_dir = root.as_ref().join(log_dir).join(ATTEMPTS_DIR);
        if !attempts_dir.exists() {
            continue;
        }

        let mut files = Vec::new();
        for entry in fs::read_dir(&attempts_dir)? {
            let path = entry?.path();
            if path.extension().is_some_and(|ext| ext == "jsonl") {
                files.push(path);
            }
        }
        files.sort();

        for path in files {
            let content = fs::read_to_string(&path)?;
            for (line_index, line) in content.lines().enumerate() {
                if line.trim().is_empty() {
                    continue;
                }
                let value: Value = serde_json::from_str(line).map_err(|err| {
                    MathverseError::Json(err).with_context(&format!(
                        "while parsing evidence log `{}` line {}",
                        path.display(),
                        line_index + 1
                    ))
                })?;
                records.push(record_from_value(value, &path, line_index + 1)?);
            }
        }
    }

    Ok(records)
}

fn record_from_value(
    value: Value,
    path: &Path,
    line_number: usize,
) -> MathverseResult<EvidenceSupportRecord> {
    let attempt: ProofAttempt = serde_json::from_value(value.clone()).map_err(|err| {
        MathverseError::Json(err).with_context(&format!(
            "while decoding evidence attempt `{}` line {}",
            path.display(),
            line_number
        ))
    })?;

    let theorem_name = first_string(
        &value,
        &[
            "theorem_name",
            "theorem",
            "target_theorem",
            "declaration_name",
            "decl_name",
            "name",
        ],
    );
    let task_id = first_string(&value, &["task_id", "external_task_id", "task"])
        .or_else(|| nested_string(&value, "context", "external_task_id"));
    let source_fingerprint = first_value(
        &value,
        &[
            "source_fingerprint",
            "source_env_fingerprint",
            "source",
            "input_fingerprint",
        ],
    );
    let context_fields = context_fields(&value);
    let extra_fields = extra_fields(&value);
    let artifacts = evidence_artifacts(&attempt);
    let artifact_hashes = artifacts
        .iter()
        .map(|artifact| artifact.artifact.blake3.clone())
        .collect();

    Ok(EvidenceSupportRecord {
        attempt_id: attempt.attempt_id,
        status: attempt.status,
        authority_gate: attempt.authority_gate,
        theorem_name: theorem_name.or_else(|| context_name(&context_fields)),
        task_id,
        goal_hash: attempt.goal_hash,
        trust_audit_hash: attempt.trust_audit_hash,
        artifacts,
        artifact_hashes,
        env: attempt.env,
        source_fingerprint,
        context_fields,
        extra_fields,
        created_at: attempt.created_at,
        wall_time_ms: attempt.wall_time_ms,
    })
}

fn evidence_artifacts(attempt: &ProofAttempt) -> Vec<EvidenceArtifact> {
    let mut artifacts = Vec::new();
    if let Some(artifact) = &attempt.solver_artifact {
        artifacts.push(EvidenceArtifact {
            role: "solver_artifact".to_owned(),
            artifact: artifact.clone(),
        });
    }
    if let Some(artifact) = &attempt.model_response {
        artifacts.push(EvidenceArtifact {
            role: "model_response".to_owned(),
            artifact: artifact.clone(),
        });
    }
    if let Some(artifact) = attempt
        .context
        .as_ref()
        .and_then(|context| context.patch_artifact.as_ref())
    {
        artifacts.push(EvidenceArtifact {
            role: "context.patch_artifact".to_owned(),
            artifact: artifact.clone(),
        });
    }
    artifacts
}

fn first_string(value: &Value, keys: &[&str]) -> Option<String> {
    keys.iter().find_map(|key| {
        value
            .get(*key)
            .and_then(Value::as_str)
            .map(str::trim)
            .filter(|text| !text.is_empty())
            .map(str::to_owned)
    })
}

fn nested_string(value: &Value, object_key: &str, field_key: &str) -> Option<String> {
    value
        .get(object_key)
        .and_then(|object| object.get(field_key))
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|text| !text.is_empty())
        .map(str::to_owned)
}

fn first_value(value: &Value, keys: &[&str]) -> Option<Value> {
    keys.iter()
        .find_map(|key| value.get(*key).filter(|v| !v.is_null()).cloned())
}

fn context_name(context_fields: &BTreeMap<String, Value>) -> Option<String> {
    [
        "theorem_name",
        "theorem",
        "target_theorem",
        "declaration_name",
        "decl_name",
    ]
    .iter()
    .find_map(|key| {
        context_fields
            .get(*key)
            .and_then(Value::as_str)
            .map(str::trim)
            .filter(|text| !text.is_empty())
            .map(str::to_owned)
    })
}

fn context_fields(value: &Value) -> BTreeMap<String, Value> {
    value
        .get("context")
        .and_then(Value::as_object)
        .map(|object| {
            object
                .iter()
                .map(|(key, value)| (key.clone(), value.clone()))
                .collect()
        })
        .unwrap_or_default()
}

fn extra_fields(value: &Value) -> BTreeMap<String, Value> {
    const KNOWN: &[&str] = &[
        "attempt_id",
        "goal_hash",
        "status",
        "trust_audit_hash",
        "solver_artifact",
        "proof_state_before",
        "proof_state_after",
        "model_response",
        "env",
        "created_at",
        "wall_time_ms",
        "authority_gate",
        "failure_mode",
        "trust_level",
        "budget",
        "producer",
        "context",
        "replayed_from",
    ];

    value
        .as_object()
        .map(|object| {
            object
                .iter()
                .filter(|(key, _)| !KNOWN.contains(&key.as_str()))
                .map(|(key, value)| (key.clone(), value.clone()))
                .collect()
        })
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attempt_log::{ArtifactRef, AttemptContext};

    fn test_env() -> EnvFingerprint {
        EnvFingerprint {
            lean_toolchain: "leanprover/lean4:v4.18.0".to_owned(),
            clean_commit: "0123456789abcdef0123456789abcdef01234567".to_owned(),
            ay_revision: None,
            llvm2_revision: None,
            host_arch: "test-arch".to_owned(),
            host_os: "test-os".to_owned(),
            solver_binaries: Vec::new(),
        }
    }

    fn hash(label: &str) -> String {
        blake3::hash(label.as_bytes()).to_hex().to_string()
    }

    fn artifact(label: &str) -> ArtifactRef {
        ArtifactRef {
            blake3: hash(label),
            byte_len: label.len() as u64,
            kind: Some("test/artifact".to_owned()),
            logical_name: Some(format!("{label}.txt")),
        }
    }

    fn attempt(label: &str, status: AttemptStatus) -> ProofAttempt {
        let mut attempt = ProofAttempt::new(
            hash(&format!("{label}-goal")),
            status,
            hash("audit"),
            test_env(),
        );
        attempt.attempt_id = AttemptId::from(format!("attempt-{label}"));
        attempt.created_at = 1_700_000_000_000_000_000;
        attempt.wall_time_ms = 42;
        attempt
    }

    fn write_jsonl(root: &Path, file_name: &str, lines: &[String]) {
        // Write into the legacy directory: scanning it pins the read-fallback.
        let dir = root.join(LEGACY_ATTEMPT_LOG_DIR).join(ATTEMPTS_DIR);
        fs::create_dir_all(&dir).expect("create attempts dir");
        fs::write(dir.join(file_name), format!("{}\n", lines.join("\n"))).expect("write jsonl");
    }

    #[test]
    fn query_evidence_normalizes_attempt_support_records() {
        let temp = tempfile::tempdir().expect("tempdir");

        let mut first = attempt("one", AttemptStatus::Accepted);
        first.authority_gate = Some("native_gate".to_owned());
        first.solver_artifact = Some(artifact("solver"));
        first.context = Some(AttemptContext {
            external_run_id: Some("run-1".to_owned()),
            external_task_id: Some("task-1".to_owned()),
            prompt_digest: Some(hash("prompt")),
            patch_artifact: Some(artifact("patch")),
        });
        let mut first_value = serde_json::to_value(first).expect("first value");
        first_value["theorem_name"] = Value::String("Mathlib.Data.Nat.Basic.add_assoc".to_owned());
        first_value["source_fingerprint"] = serde_json::json!({
            "source_path": "Mathlib/Data/Nat/Basic.lean",
            "sha256": "source-sha"
        });

        let mut second = attempt(
            "two",
            AttemptStatus::Rejected {
                reason: "not supported".to_owned(),
            },
        );
        second.authority_gate = Some("audit_gate".to_owned());
        let second_value = serde_json::to_value(second).expect("second value");

        write_jsonl(
            temp.path(),
            "2026-05-20.jsonl",
            &[
                serde_json::to_string(&second_value).expect("second json"),
                serde_json::to_string(&first_value).expect("first json"),
            ],
        );

        let matches = query_mathverse_evidence(
            temp.path(),
            EvidenceQuery {
                theorem_name: Some("Mathlib.Data.Nat.Basic.add_assoc".to_owned()),
                task_id: Some("task-1".to_owned()),
                authority_gate: Some("native_gate".to_owned()),
                status: Some(AttemptStatusFilter::Accepted),
                ..EvidenceQuery::default()
            },
        )
        .expect("query evidence");

        assert_eq!(matches.len(), 1);
        let record = &matches[0];
        assert_eq!(record.attempt_id.as_str(), "attempt-one");
        assert_eq!(
            record.theorem_name.as_deref(),
            Some("Mathlib.Data.Nat.Basic.add_assoc")
        );
        assert_eq!(record.task_id.as_deref(), Some("task-1"));
        assert_eq!(record.authority_gate.as_deref(), Some("native_gate"));
        assert_eq!(record.artifact_hashes.len(), 2);
        assert_eq!(record.artifacts[0].role, "solver_artifact");
        assert_eq!(record.artifacts[1].role, "context.patch_artifact");
        assert_eq!(
            record.env.clean_commit,
            "0123456789abcdef0123456789abcdef01234567"
        );
        assert_eq!(
            record
                .source_fingerprint
                .as_ref()
                .and_then(|value| value.get("source_path"))
                .and_then(Value::as_str),
            Some("Mathlib/Data/Nat/Basic.lean")
        );
        assert_eq!(
            record
                .context_fields
                .get("external_task_id")
                .and_then(Value::as_str),
            Some("task-1")
        );
        assert_eq!(
            record
                .extra_fields
                .get("theorem_name")
                .and_then(Value::as_str),
            Some("Mathlib.Data.Nat.Basic.add_assoc")
        );
    }

    #[test]
    fn evidence_index_queries_by_attempt_id_and_context_theorem() {
        let temp = tempfile::tempdir().expect("tempdir");

        let mut attempt = attempt("three", AttemptStatus::Timeout { after_ms: 1_000 });
        attempt.authority_gate = Some("timeout_gate".to_owned());
        attempt.context = Some(AttemptContext {
            external_run_id: None,
            external_task_id: Some("task-3".to_owned()),
            prompt_digest: None,
            patch_artifact: None,
        });
        let mut value = serde_json::to_value(attempt).expect("attempt value");
        value["context"]["theorem_name"] = Value::String("Clean.Timeout.Target".to_owned());

        write_jsonl(
            temp.path(),
            "2026-05-21.jsonl",
            &[serde_json::to_string(&value).expect("attempt json")],
        );

        let index = MathverseEvidenceIndex::scan(temp.path()).expect("scan index");
        let matches = index.query(&EvidenceQuery {
            attempt_id: Some(AttemptId::from("attempt-three")),
            theorem_name: Some("Clean.Timeout.Target".to_owned()),
            status: Some(AttemptStatusFilter::Timeout),
            ..EvidenceQuery::default()
        });

        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].task_id.as_deref(), Some("task-3"));
        assert_eq!(
            matches[0].theorem_name.as_deref(),
            Some("Clean.Timeout.Target")
        );
    }

    #[test]
    fn malformed_json_fails_closed() {
        let temp = tempfile::tempdir().expect("tempdir");
        write_jsonl(
            temp.path(),
            "2026-05-20.jsonl",
            &["{\"attempt_id\"".to_owned()],
        );

        let err = MathverseEvidenceIndex::scan(temp.path()).expect_err("malformed json must fail");
        let message = err.to_string();
        assert!(message.contains("json:"));
        assert!(message.contains("line 1"));
    }
}
