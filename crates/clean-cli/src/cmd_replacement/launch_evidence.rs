// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Launch evidence states and axiom-audit evidence types.

use super::*;

#[derive(Debug, Clone)]
pub(crate) enum KernelSoundnessLaunchEvidenceState {
    Passed,
    Missing,
    Stale(String),
}

#[derive(Debug, Clone)]
pub(crate) struct KernelSoundnessLaunchEvidence {
    pub(crate) state: KernelSoundnessLaunchEvidenceState,
}

impl KernelSoundnessLaunchEvidence {
    pub(crate) fn missing() -> Self {
        Self {
            state: KernelSoundnessLaunchEvidenceState::Missing,
        }
    }

    pub(crate) fn passed() -> Self {
        Self {
            state: KernelSoundnessLaunchEvidenceState::Passed,
        }
    }

    pub(crate) fn stale(message: impl Into<String>) -> Self {
        Self {
            state: KernelSoundnessLaunchEvidenceState::Stale(message.into()),
        }
    }

    pub(crate) fn is_passed(&self) -> bool {
        matches!(self.state, KernelSoundnessLaunchEvidenceState::Passed)
    }

    pub(crate) fn status_label(&self) -> &'static str {
        match &self.state {
            KernelSoundnessLaunchEvidenceState::Passed => "passed",
            KernelSoundnessLaunchEvidenceState::Missing => "missing",
            KernelSoundnessLaunchEvidenceState::Stale(_) => "stale",
        }
    }

    pub(crate) fn summary(&self) -> String {
        match &self.state {
            KernelSoundnessLaunchEvidenceState::Passed => {
                format!("{KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_PATH} passed")
            }
            KernelSoundnessLaunchEvidenceState::Missing => {
                format!("{KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_PATH} missing")
            }
            KernelSoundnessLaunchEvidenceState::Stale(message) => {
                format!("{KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_PATH} stale: {message}")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum DenySorryLaunchEvidenceState {
    Passed,
    Missing,
    Stale(String),
}

#[derive(Debug, Clone)]
pub(crate) struct DenySorryLaunchEvidence {
    pub(crate) state: DenySorryLaunchEvidenceState,
}

impl DenySorryLaunchEvidence {
    pub(crate) fn missing() -> Self {
        Self {
            state: DenySorryLaunchEvidenceState::Missing,
        }
    }

    pub(crate) fn passed() -> Self {
        Self {
            state: DenySorryLaunchEvidenceState::Passed,
        }
    }

    pub(crate) fn stale(message: impl Into<String>) -> Self {
        Self {
            state: DenySorryLaunchEvidenceState::Stale(message.into()),
        }
    }

    pub(crate) fn is_passed(&self) -> bool {
        matches!(self.state, DenySorryLaunchEvidenceState::Passed)
    }

    pub(crate) fn status_label(&self) -> &'static str {
        match &self.state {
            DenySorryLaunchEvidenceState::Passed => "passed",
            DenySorryLaunchEvidenceState::Missing => "missing",
            DenySorryLaunchEvidenceState::Stale(_) => "stale",
        }
    }

    pub(crate) fn summary(&self) -> String {
        match &self.state {
            DenySorryLaunchEvidenceState::Passed => {
                format!("{DENY_SORRY_LAUNCH_EVIDENCE_PATH} passed")
            }
            DenySorryLaunchEvidenceState::Missing => {
                format!("{DENY_SORRY_LAUNCH_EVIDENCE_PATH} missing")
            }
            DenySorryLaunchEvidenceState::Stale(message) => {
                format!("{DENY_SORRY_LAUNCH_EVIDENCE_PATH} stale: {message}")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum AxiomAuditLaunchEvidenceState {
    Passed,
    Missing,
    Stale(String),
}

#[derive(Debug, Clone)]
pub(crate) struct AxiomAuditLaunchEvidence {
    pub(crate) state: AxiomAuditLaunchEvidenceState,
}

impl AxiomAuditLaunchEvidence {
    pub(crate) fn missing() -> Self {
        Self {
            state: AxiomAuditLaunchEvidenceState::Missing,
        }
    }

    pub(crate) fn passed() -> Self {
        Self {
            state: AxiomAuditLaunchEvidenceState::Passed,
        }
    }

    pub(crate) fn stale(message: impl Into<String>) -> Self {
        Self {
            state: AxiomAuditLaunchEvidenceState::Stale(message.into()),
        }
    }

    pub(crate) fn is_passed(&self) -> bool {
        matches!(self.state, AxiomAuditLaunchEvidenceState::Passed)
    }

    pub(crate) fn status_label(&self) -> &'static str {
        match &self.state {
            AxiomAuditLaunchEvidenceState::Passed => "passed",
            AxiomAuditLaunchEvidenceState::Missing => "missing",
            AxiomAuditLaunchEvidenceState::Stale(_) => "stale",
        }
    }

    pub(crate) fn summary(&self) -> String {
        match &self.state {
            AxiomAuditLaunchEvidenceState::Passed => {
                format!("{AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH} passed")
            }
            AxiomAuditLaunchEvidenceState::Missing => {
                format!("{AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH} missing")
            }
            AxiomAuditLaunchEvidenceState::Stale(message) => {
                format!("{AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH} stale: {message}")
            }
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct UncheckedDeclRatchetEvidence {
    pub(crate) add_decl_structural_count: u32,
    pub(crate) add_decl_unchecked_count: u32,
    pub(crate) last_updated: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct AxiomAuditEvidence {
    pub(crate) issue: IssueRef,
    pub(crate) audit_path: &'static str,
    pub(crate) release_check_command: &'static str,
    pub(crate) launch_evidence_path: &'static str,
    pub(crate) launch_evidence_status: String,
    pub(crate) launch_evidence_summary: String,
    pub(crate) total_domain_axioms: u32,
    pub(crate) total_all_axioms: u32,
    pub(crate) total_theorems: u32,
    pub(crate) constructive_theorems: u32,
    pub(crate) conjecture_rows: usize,
    pub(crate) nonzero_axiom_rows: usize,
    pub(crate) proof_mechanism_counts: BTreeMap<String, usize>,
}

impl AxiomAuditEvidence {
    pub(crate) fn from_artifact(
        artifact: &AxiomAuditArtifact,
        launch_evidence: &AxiomAuditLaunchEvidence,
    ) -> Self {
        let mut proof_mechanism_counts = BTreeMap::new();
        let mut nonzero_axiom_rows = 0;

        for conjecture in artifact.conjectures.values() {
            if conjecture.axioms > 0 {
                nonzero_axiom_rows += 1;
            }
            let mechanism = conjecture
                .proof_mechanism
                .as_deref()
                .unwrap_or("missing_proof_mechanism");
            *proof_mechanism_counts
                .entry(mechanism.to_owned())
                .or_insert(0) += 1;
        }

        Self {
            issue: IssueRef::new(
                3699,
                "Proof-system replacement certification and zero-trust gates",
            ),
            audit_path: AXIOM_AUDIT_PATH,
            release_check_command: AXIOM_AUDIT_GATE_COMMAND,
            launch_evidence_path: AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH,
            launch_evidence_status: launch_evidence.status_label().to_string(),
            launch_evidence_summary: launch_evidence.summary(),
            total_domain_axioms: artifact.total_domain_axioms,
            total_all_axioms: artifact.total_all_axioms,
            total_theorems: artifact.total_theorems,
            constructive_theorems: artifact.constructive_theorems,
            conjecture_rows: artifact.conjectures.len(),
            nonzero_axiom_rows,
            proof_mechanism_counts,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct AxiomAuditVerification {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) audit_path: String,
    pub(crate) evidence_path: Option<String>,
    pub(crate) validation_passed: bool,
    pub(crate) status: &'static str,
    pub(crate) failures: Vec<String>,
    pub(crate) lanes: Vec<AxiomAuditVerificationLane>,
    pub(crate) axiom_audit: AxiomAuditLaunchAuditEvidence,
    pub(crate) source_sha256: BTreeMap<String, String>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct AxiomAuditVerificationLane {
    pub(crate) id: &'static str,
    pub(crate) description: &'static str,
    pub(crate) status: &'static str,
}

impl AxiomAuditVerification {
    pub(crate) fn from_args(args: &AxiomAuditArgs) -> Result<Self, ReplacementError> {
        let audit_path = normalize_repo_path(&args.verify);
        let source = read_dynamic_artifact(&audit_path)?;
        let value: serde_json::Value =
            serde_json::from_str(&source).map_err(|source| ReplacementError::ParseReport {
                path: audit_path.clone(),
                source,
            })?;
        let artifact: AxiomAuditArtifact =
            serde_json::from_value(value.clone()).map_err(|source| {
                ReplacementError::ParseReport {
                    path: audit_path.clone(),
                    source,
                }
            })?;
        let recomputed = compute_axiom_audit_aggregates(&value)?;
        let mut failures = axiom_audit_aggregate_failures(&value, recomputed);
        let nonzero_axiom_rows = artifact
            .conjectures
            .values()
            .filter(|row| row.axioms > 0)
            .count();
        if artifact.total_domain_axioms != 0
            || artifact.total_all_axioms != 0
            || nonzero_axiom_rows != 0
        {
            failures.push(format!(
                "axiom audit is not closed at 0/0 with zero nonzero rows: total_domain_axioms={}, total_all_axioms={}, nonzero_axiom_rows={}",
                artifact.total_domain_axioms, artifact.total_all_axioms, nonzero_axiom_rows
            ));
        }
        let mut lanes = Vec::new();
        lanes.push(AxiomAuditVerificationLane {
            id: "aggregate_consistency",
            description: "Aggregate consistency (data/axiom_audit.json)",
            status: if failures.iter().any(|failure| failure.contains("aggregate")) {
                "failed"
            } else {
                "passed"
            },
        });
        lanes.push(AxiomAuditVerificationLane {
            id: "live_row_reconciliation_and_constructive_claims",
            description: "Rust aggregate verification plus zero domain/all axiom debt closure",
            status: if artifact.total_domain_axioms == 0
                && artifact.total_all_axioms == 0
                && nonzero_axiom_rows == 0
            {
                "passed"
            } else {
                "failed"
            },
        });

        let audit_sha = sha256_dynamic_artifact(&audit_path)?;
        let mut source_sha256 = BTreeMap::new();
        source_sha256.insert(
            AXIOM_AUDIT_RUST_SOURCE_PATH.to_string(),
            sha256_repo_artifact(AXIOM_AUDIT_RUST_SOURCE_PATH)?,
        );
        source_sha256.insert(audit_path.clone(), audit_sha.clone());

        Ok(Self {
            schema_version: AXIOM_AUDIT_VERIFY_SCHEMA_VERSION,
            generated_by: "clean replacement axiom-audit",
            audit_path: audit_path.clone(),
            evidence_path: args.evidence.as_ref().map(|path| normalize_repo_path(path)),
            validation_passed: failures.is_empty(),
            status: if failures.is_empty() {
                "passed"
            } else {
                "failed"
            },
            failures,
            lanes,
            axiom_audit: AxiomAuditLaunchAuditEvidence {
                path: audit_path,
                total_domain_axioms: artifact.total_domain_axioms,
                total_all_axioms: artifact.total_all_axioms,
                total_theorems: artifact.total_theorems,
                constructive_theorems: artifact.constructive_theorems,
                conjecture_rows: artifact.conjectures.len(),
                nonzero_axiom_rows,
                sha256: audit_sha,
            },
            source_sha256,
        })
    }

    pub(crate) fn launch_evidence_artifact(&self) -> AxiomAuditLaunchEvidenceArtifact {
        AxiomAuditLaunchEvidenceArtifact {
            schema_version: AXIOM_AUDIT_LAUNCH_EVIDENCE_SCHEMA_VERSION.to_string(),
            generated_by: AXIOM_AUDIT_GATE_COMMAND.to_string(),
            generated_at: utc_timestamp_seconds(),
            gate_command: AXIOM_AUDIT_GATE_COMMAND.to_string(),
            status: self.status.to_string(),
            summary: AxiomAuditLaunchEvidenceSummary {
                expected_steps: AXIOM_AUDIT_EXPECTED_STEPS,
                steps: AXIOM_AUDIT_EXPECTED_STEPS,
                passed: if self.validation_passed {
                    AXIOM_AUDIT_EXPECTED_STEPS
                } else {
                    self.lanes
                        .iter()
                        .filter(|lane| lane.status == "passed")
                        .count() as u32
                },
                failed: if self.validation_passed {
                    0
                } else {
                    self.lanes
                        .iter()
                        .filter(|lane| lane.status != "passed")
                        .count() as u32
                },
            },
            axiom_audit: self.axiom_audit.clone(),
            source_sha256: self.source_sha256.clone(),
            lanes: self
                .lanes
                .iter()
                .map(|lane| AxiomAuditLaunchLaneEvidence {
                    id: lane.id.to_string(),
                    description: lane.description.to_string(),
                    status: lane.status.to_string(),
                })
                .collect(),
        }
    }
}

pub(crate) fn axiom_audit_aggregate_failures(
    value: &serde_json::Value,
    recomputed: AxiomAuditAggregates,
) -> Vec<String> {
    let stored = [
        ("total_domain_axioms", recomputed.total_domain_axioms),
        ("total_theorems", recomputed.total_theorems),
        ("constructive_theorems", recomputed.constructive_theorems),
        ("total_all_axioms", recomputed.total_all_axioms),
    ];
    let mut failures = Vec::new();
    for (key, expected) in stored {
        match value.get(key).and_then(serde_json::Value::as_u64) {
            Some(actual) if actual == u64::from(expected) => {}
            Some(actual) => failures.push(format!(
                "aggregate {key}: stored {actual}, recomputed {expected}"
            )),
            None => failures.push(format!(
                "aggregate {key}: missing or non-integer, recomputed {expected}"
            )),
        }
    }
    failures
}
