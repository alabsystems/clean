// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse authority-evidence refresh planning.
//!
//! This module is intentionally library-only: it inspects `.mathverse` attempt
//! logs and returns deterministic data a CLI can render or execute later.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::attempt_log::{AttemptId, AttemptStatus};
use crate::env_fingerprint::EnvFingerprint;
use crate::error::MathverseResult;
use crate::evidence_query::{EvidenceQuery, EvidenceSupportRecord, MathverseEvidenceIndex};

/// Stable spelling for the authority gates commonly required before accepting
/// external Mathverse evidence.
pub const TRUST_AUDIT_GATE: &str = "trust_audit";
pub const STATEMENT_PRESERVATION_GATE: &str = "statement_preservation";
pub const TRUST_LEDGER_GATE: &str = "trust_ledger";
pub const FALSE_CONTROLS_GATE: &str = "false_controls";

/// Caller request for a Mathverse authority-evidence refresh plan.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefreshPlanRequest {
    /// Project root containing `.cake/attempts` (plus the legacy `.mathverse/attempts`).
    pub project_root: PathBuf,
    /// Required authority gates to inspect, in caller priority order.
    pub required_gates: Vec<String>,
    /// Optional theorem/declaration scope.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theorem_name: Option<String>,
    /// Optional task scope, including `context.external_task_id`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub task_id: Option<String>,
    /// Current environment fingerprint. When omitted, the project root is
    /// captured at planning time.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub current_env: Option<EnvFingerprint>,
    /// Current source or source-policy fingerprint. When supplied, accepted
    /// evidence must carry an equal source fingerprint to be current.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub current_source_fingerprint: Option<Value>,
}

impl RefreshPlanRequest {
    /// Build a request for a project root and required gates.
    pub fn new(
        project_root: impl Into<PathBuf>,
        required_gates: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        Self {
            project_root: project_root.into(),
            required_gates: required_gates.into_iter().map(Into::into).collect(),
            theorem_name: None,
            task_id: None,
            current_env: None,
            current_source_fingerprint: None,
        }
    }

    /// Scope the plan to one theorem/declaration name.
    pub fn with_theorem_name(mut self, theorem_name: impl Into<String>) -> Self {
        self.theorem_name = Some(theorem_name.into());
        self
    }

    /// Scope the plan to one task id.
    pub fn with_task_id(mut self, task_id: impl Into<String>) -> Self {
        self.task_id = Some(task_id.into());
        self
    }

    /// Use caller-supplied current fingerprints instead of capturing them.
    pub fn with_current_fingerprints(
        mut self,
        env: EnvFingerprint,
        source_fingerprint: Option<Value>,
    ) -> Self {
        self.current_env = Some(env);
        self.current_source_fingerprint = source_fingerprint;
        self
    }
}

/// Deterministic refresh plan for a `.mathverse` evidence scope.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefreshPlan {
    /// Project root scanned.
    pub project_root: PathBuf,
    /// Optional theorem/declaration scope.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theorem_name: Option<String>,
    /// Optional task scope.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub task_id: Option<String>,
    /// Current environment fingerprint used for comparisons.
    pub current_env: EnvFingerprint,
    /// Current source or source-policy fingerprint used for comparisons.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub current_source_fingerprint: Option<Value>,
    /// One entry per required gate, in deterministic request order.
    pub gates: Vec<RefreshGatePlan>,
}

impl RefreshPlan {
    /// Returns true when every required gate has current accepted evidence.
    pub fn all_current(&self) -> bool {
        self.gates
            .iter()
            .all(|gate| gate.status == RefreshGateStatus::Current)
    }

    /// Gates that need a new authority attempt.
    pub fn refresh_required(&self) -> Vec<&RefreshGatePlan> {
        self.gates
            .iter()
            .filter(|gate| gate.status != RefreshGateStatus::Current)
            .collect()
    }
}

/// Refresh status for one required authority gate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefreshGatePlan {
    /// Required authority gate.
    pub gate: String,
    /// Current, stale, or missing.
    pub status: RefreshGateStatus,
    /// Accepted current evidence, when present.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub current: Option<RefreshEvidenceRef>,
    /// Accepted evidence for this gate that failed freshness checks.
    #[serde(default)]
    pub stale: Vec<RefreshStaleEvidence>,
    /// All evidence records seen for this gate and scope.
    #[serde(default)]
    pub records: Vec<RefreshEvidenceRef>,
}

/// High-level state for one gate in the plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RefreshGateStatus {
    /// An accepted record matches the current environment and source
    /// fingerprint, when a current source fingerprint was supplied.
    Current,
    /// Accepted evidence exists, but every accepted record is stale.
    Stale,
    /// No accepted evidence exists for the gate and scope.
    Missing,
}

/// Lightweight reference to an evidence record suitable for CLI rendering.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefreshEvidenceRef {
    /// UUIDv7-shaped attempt id.
    pub attempt_id: AttemptId,
    /// Final attempt status.
    pub status: AttemptStatus,
    /// BLAKE3 hash of the goal or normalized goal shape.
    pub goal_hash: String,
    /// BLAKE3 hash of the trust/audit report.
    pub trust_audit_hash: String,
    /// Theorem/declaration name normalized from the attempt, when recorded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theorem_name: Option<String>,
    /// Task id normalized from the attempt, when recorded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub task_id: Option<String>,
    /// Source or source-policy fingerprint recorded by the attempt, when any.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_fingerprint: Option<Value>,
    /// Nanoseconds since Unix epoch.
    pub created_at: u64,
}

/// Accepted evidence that does not match the current fingerprints.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefreshStaleEvidence {
    /// Stale evidence record.
    pub evidence: RefreshEvidenceRef,
    /// Fingerprint mismatches that made the evidence stale.
    pub reasons: Vec<RefreshStaleReason>,
}

/// Specific freshness mismatch for accepted evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RefreshStaleReason {
    /// Recorded execution environment differs from the current environment.
    EnvMismatch,
    /// Caller supplied a current source fingerprint, but the record did not.
    MissingSourceFingerprint,
    /// Recorded source fingerprint differs from the current source fingerprint.
    SourceFingerprintMismatch,
}

/// Build a refresh plan by scanning `.cake/attempts` (plus the legacy
/// `.mathverse/attempts`) under the request
/// project root.
pub fn plan_mathverse_evidence_refresh(
    request: RefreshPlanRequest,
) -> MathverseResult<RefreshPlan> {
    let current_env = match request.current_env {
        Some(env) => env,
        None => EnvFingerprint::capture(&request.project_root)?,
    };
    let index = MathverseEvidenceIndex::scan(&request.project_root)?;
    Ok(plan_mathverse_evidence_refresh_from_index(
        request.project_root,
        request.required_gates,
        request.theorem_name,
        request.task_id,
        current_env,
        request.current_source_fingerprint,
        &index,
    ))
}

/// Build a refresh plan from an already scanned evidence index.
pub fn plan_mathverse_evidence_refresh_from_index(
    project_root: impl AsRef<Path>,
    required_gates: impl IntoIterator<Item = impl Into<String>>,
    theorem_name: Option<String>,
    task_id: Option<String>,
    current_env: EnvFingerprint,
    current_source_fingerprint: Option<Value>,
    index: &MathverseEvidenceIndex,
) -> RefreshPlan {
    let mut gates = Vec::new();
    for gate in normalized_required_gates(required_gates) {
        let mut records = index.query(&EvidenceQuery {
            theorem_name: theorem_name.clone(),
            task_id: task_id.clone(),
            authority_gate: Some(gate.clone()),
            ..EvidenceQuery::default()
        });
        records.sort_by(record_order);

        let refs = records.iter().map(evidence_ref).collect::<Vec<_>>();
        let mut stale = records
            .iter()
            .filter(|record| matches!(record.status, AttemptStatus::Accepted))
            .filter_map(|record| {
                let reasons = stale_reasons(record, &current_env, &current_source_fingerprint);
                (!reasons.is_empty()).then(|| RefreshStaleEvidence {
                    evidence: evidence_ref(record),
                    reasons,
                })
            })
            .collect::<Vec<_>>();
        stale.sort_by(|left, right| record_ref_order(&left.evidence, &right.evidence));

        let current = records
            .iter()
            .filter(|record| matches!(record.status, AttemptStatus::Accepted))
            .filter(|record| {
                stale_reasons(record, &current_env, &current_source_fingerprint).is_empty()
            })
            .max_by(|left, right| record_order(left, right))
            .map(evidence_ref);

        let status = if current.is_some() {
            RefreshGateStatus::Current
        } else if stale.is_empty() {
            RefreshGateStatus::Missing
        } else {
            RefreshGateStatus::Stale
        };

        gates.push(RefreshGatePlan {
            gate,
            status,
            current,
            stale,
            records: refs,
        });
    }

    RefreshPlan {
        project_root: project_root.as_ref().to_path_buf(),
        theorem_name,
        task_id,
        current_env,
        current_source_fingerprint,
        gates,
    }
}

fn normalized_required_gates(gates: impl IntoIterator<Item = impl Into<String>>) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for gate in gates {
        let gate = gate.into().trim().to_owned();
        if !gate.is_empty() && seen.insert(gate.clone()) {
            out.push(gate);
        }
    }
    out
}

fn stale_reasons(
    record: &EvidenceSupportRecord,
    current_env: &EnvFingerprint,
    current_source_fingerprint: &Option<Value>,
) -> Vec<RefreshStaleReason> {
    let mut reasons = Vec::new();
    if &record.env != current_env {
        reasons.push(RefreshStaleReason::EnvMismatch);
    }
    if let Some(current_source) = current_source_fingerprint {
        match &record.source_fingerprint {
            Some(recorded) if recorded == current_source => {}
            Some(_) => reasons.push(RefreshStaleReason::SourceFingerprintMismatch),
            None => reasons.push(RefreshStaleReason::MissingSourceFingerprint),
        }
    }
    reasons
}

fn evidence_ref(record: &EvidenceSupportRecord) -> RefreshEvidenceRef {
    RefreshEvidenceRef {
        attempt_id: record.attempt_id.clone(),
        status: record.status.clone(),
        goal_hash: record.goal_hash.clone(),
        trust_audit_hash: record.trust_audit_hash.clone(),
        theorem_name: record.theorem_name.clone(),
        task_id: record.task_id.clone(),
        source_fingerprint: record.source_fingerprint.clone(),
        created_at: record.created_at,
    }
}

fn record_order(left: &EvidenceSupportRecord, right: &EvidenceSupportRecord) -> std::cmp::Ordering {
    left.created_at
        .cmp(&right.created_at)
        .then_with(|| left.attempt_id.cmp(&right.attempt_id))
}

fn record_ref_order(left: &RefreshEvidenceRef, right: &RefreshEvidenceRef) -> std::cmp::Ordering {
    left.created_at
        .cmp(&right.created_at)
        .then_with(|| left.attempt_id.cmp(&right.attempt_id))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    use crate::attempt_log::{AttemptContext, ProofAttempt};

    fn test_env(clean_commit: &str) -> EnvFingerprint {
        EnvFingerprint {
            lean_toolchain: "leanprover/lean4:v4.test".to_owned(),
            clean_commit: clean_commit.to_owned(),
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

    fn accepted_gate(
        label: &str,
        gate: &str,
        env: EnvFingerprint,
        created_at: u64,
    ) -> ProofAttempt {
        let mut attempt = ProofAttempt::new(
            hash(&format!("{label}-goal")),
            AttemptStatus::Accepted,
            hash(&format!("{label}-audit")),
            env,
        );
        attempt.attempt_id = AttemptId::from(format!("attempt-{label}"));
        attempt.authority_gate = Some(gate.to_owned());
        attempt.created_at = created_at;
        attempt.context = Some(AttemptContext {
            external_run_id: None,
            external_task_id: Some("task-1".to_owned()),
            prompt_digest: None,
            patch_artifact: None,
        });
        attempt
    }

    fn write_attempt_value(root: &Path, file_name: &str, value: Value) {
        let dir = root.join(".mathverse").join("attempts");
        fs::create_dir_all(&dir).expect("create attempts dir");
        fs::write(
            dir.join(file_name),
            format!("{}\n", serde_json::to_string(&value).expect("json")),
        )
        .expect("write attempt log");
    }

    #[test]
    fn refresh_plan_marks_matching_gate_current() {
        let temp = tempfile::tempdir().expect("tempdir");
        let env = test_env("clean-current");
        let source = serde_json::json!({"policy": "v1", "source": "abc"});
        let attempt = accepted_gate("trust", TRUST_AUDIT_GATE, env.clone(), 20);
        let mut value = serde_json::to_value(attempt).expect("attempt value");
        value["theorem_name"] = Value::String("Math.Target".to_owned());
        value["source_fingerprint"] = source.clone();
        write_attempt_value(temp.path(), "2026-05-20.jsonl", value);

        let plan = plan_mathverse_evidence_refresh(
            RefreshPlanRequest::new(temp.path(), [TRUST_AUDIT_GATE])
                .with_theorem_name("Math.Target")
                .with_current_fingerprints(env, Some(source)),
        )
        .expect("refresh plan");

        assert!(plan.all_current());
        assert_eq!(plan.gates[0].status, RefreshGateStatus::Current);
        assert_eq!(
            plan.gates[0]
                .current
                .as_ref()
                .map(|evidence| evidence.attempt_id.as_str()),
            Some("attempt-trust")
        );
    }

    #[test]
    fn refresh_plan_marks_accepted_gate_stale_on_env_mismatch() {
        let temp = tempfile::tempdir().expect("tempdir");
        let source = serde_json::json!({"source": "abc"});
        let attempt = accepted_gate("ledger", TRUST_LEDGER_GATE, test_env("old-clean"), 10);
        let mut value = serde_json::to_value(attempt).expect("attempt value");
        value["source_fingerprint"] = source.clone();
        write_attempt_value(temp.path(), "2026-05-20.jsonl", value);

        let plan = plan_mathverse_evidence_refresh(
            RefreshPlanRequest::new(temp.path(), [TRUST_LEDGER_GATE])
                .with_task_id("task-1")
                .with_current_fingerprints(test_env("new-clean"), Some(source)),
        )
        .expect("refresh plan");

        assert_eq!(plan.gates[0].status, RefreshGateStatus::Stale);
        assert_eq!(plan.refresh_required().len(), 1);
        assert_eq!(
            plan.gates[0].stale[0].reasons,
            vec![RefreshStaleReason::EnvMismatch]
        );
    }

    #[test]
    fn refresh_plan_reports_missing_required_gate() {
        let temp = tempfile::tempdir().expect("tempdir");
        let env = test_env("clean-current");
        let attempt = accepted_gate("trust", TRUST_AUDIT_GATE, env.clone(), 10);
        write_attempt_value(
            temp.path(),
            "2026-05-20.jsonl",
            serde_json::to_value(attempt).expect("attempt value"),
        );

        let plan = plan_mathverse_evidence_refresh(
            RefreshPlanRequest::new(
                temp.path(),
                [
                    TRUST_AUDIT_GATE,
                    STATEMENT_PRESERVATION_GATE,
                    FALSE_CONTROLS_GATE,
                ],
            )
            .with_current_fingerprints(env, None),
        )
        .expect("refresh plan");

        assert_eq!(
            plan.gates
                .iter()
                .map(|gate| gate.gate.as_str())
                .collect::<Vec<_>>(),
            vec![
                TRUST_AUDIT_GATE,
                STATEMENT_PRESERVATION_GATE,
                FALSE_CONTROLS_GATE
            ]
        );
        assert_eq!(plan.gates[0].status, RefreshGateStatus::Current);
        assert_eq!(plan.gates[1].status, RefreshGateStatus::Missing);
        assert_eq!(plan.gates[2].status, RefreshGateStatus::Missing);
    }

    #[test]
    fn refresh_plan_treats_missing_source_fingerprint_as_stale_when_required() {
        let temp = tempfile::tempdir().expect("tempdir");
        let env = test_env("clean-current");
        let attempt = accepted_gate("false-controls", FALSE_CONTROLS_GATE, env.clone(), 10);
        write_attempt_value(
            temp.path(),
            "2026-05-20.jsonl",
            serde_json::to_value(attempt).expect("attempt value"),
        );

        let plan = plan_mathverse_evidence_refresh(
            RefreshPlanRequest::new(temp.path(), [FALSE_CONTROLS_GATE])
                .with_current_fingerprints(env, Some(serde_json::json!({"source": "required"}))),
        )
        .expect("refresh plan");

        assert_eq!(plan.gates[0].status, RefreshGateStatus::Stale);
        assert_eq!(
            plan.gates[0].stale[0].reasons,
            vec![RefreshStaleReason::MissingSourceFingerprint]
        );
    }
}
