// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust-core evidence report and proof-system certification evidence.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TrustCoreEvidenceReport {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) launch_ready: bool,
    pub(crate) overall_status: &'static str,
    pub(crate) issues: Vec<IssueRef>,
    pub(crate) source_artifacts: Vec<&'static str>,
    pub(crate) zero_trust_gates: Vec<ZeroTrustGateRow>,
    pub(crate) proof_system_certification: ProofSystemCertificationEvidence,
    pub(crate) kernel_differential: KernelDifferentialEvidence,
    pub(crate) fallback_denial: FallbackDenialEvidence,
    pub(crate) axiom_audit: AxiomAuditEvidence,
}

impl TrustCoreEvidenceReport {
    pub(crate) fn current() -> Result<Self, ReplacementError> {
        let baseline = load_lean4_baseline()?;
        let expressions_source = read_repo_artifact(LEAN4_EXPRESSIONS_PATH)?;
        let expressions = active_expressions(&expressions_source);
        let expressions_sha256 = sha256_expressions(&expressions);
        validate_kernel_differential_artifacts(&baseline, expressions.len(), &expressions_sha256)?;
        let kernel_soundness_launch_evidence = load_kernel_soundness_launch_evidence(
            &baseline,
            expressions.len(),
            &expressions_sha256,
        )?;
        let ratchet = load_unchecked_decl_ratchet()?;
        validate_unchecked_decl_ratchet(&ratchet)?;
        validate_sorry_bypass_lint()?;
        let deny_sorry_launch_evidence = load_deny_sorry_launch_evidence(&ratchet)?;
        let axiom_audit = load_axiom_audit()?;
        validate_axiom_audit_aggregates()?;
        let axiom_audit_launch_evidence = load_axiom_audit_launch_evidence(&axiom_audit)?;
        let zero_trust_gates = zero_trust_gate_rows(
            &ratchet,
            &axiom_audit,
            &kernel_soundness_launch_evidence,
            &deny_sorry_launch_evidence,
            &axiom_audit_launch_evidence,
        );
        let source_artifacts = trust_core_source_artifacts();
        validate_source_artifacts(REQUIRED_TRUST_CORE_SOURCE_ARTIFACTS)?;
        let verification_audit = read_repo_artifact(VERIFICATION_AUDIT_PATH)?;
        // The issue-state snapshot is machine-local gh evidence (not in git);
        // its absence degrades certification to a fail-closed Blocked row —
        // same treatment as missing kernel-soundness/deny-sorry/axiom-audit
        // launch evidence — instead of aborting the whole report.
        let verification_audit_issue_state =
            read_optional_repo_artifact(VERIFICATION_AUDIT_ISSUE_STATE_EVIDENCE_PATH)?;
        let proof_system_certification = match &verification_audit_issue_state {
            Some(issue_state) => ProofSystemCertificationEvidence::from_current(
                &zero_trust_gates,
                &verification_audit,
                issue_state,
                &replacement_rows(),
            )?,
            None => ProofSystemCertificationEvidence::missing_issue_state_snapshot(
                &zero_trust_gates,
                &replacement_rows(),
            )?,
        };

        Ok(Self {
            schema_version: TRUST_CORE_EVIDENCE_SCHEMA_VERSION,
            generated_by: "clean replacement trust-core-evidence",
            launch_ready: false,
            overall_status: "pending_evidence",
            issues: vec![
                IssueRef::new(3699, "Proof-system replacement certification and zero-trust gates"),
                IssueRef::new(3705, "Zero-trust gate forbids sorryAx and trusted fallback constructors"),
            ],
            source_artifacts,
            zero_trust_gates,
            proof_system_certification,
            kernel_differential: KernelDifferentialEvidence {
                issue: IssueRef::new(
                    3699,
                    "Proof-system replacement certification and zero-trust gates",
                ),
                test_command: "cargo test --locked -p clean-kernel --features test-utils --test lean4_parity -- lean4_parity_check",
                gate_command: KERNEL_SOUNDNESS_RUST_GATE_COMMAND,
                launch_evidence_path: KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_PATH,
                launch_evidence_status: kernel_soundness_launch_evidence
                    .status_label()
                    .to_string(),
                launch_evidence_summary: kernel_soundness_launch_evidence.summary(),
                gate_preflight_required: true,
                gate_preflight_artifacts: vec![
                    TRUST_CORE_RUST_SOURCE_PATH,
                    LEAN4_BASELINE_PATH,
                    LEAN4_EXPRESSIONS_PATH,
                ],
                gate_preflight_guards: KERNEL_GATE_PREFLIGHT_GUARDS.to_vec(),
                baseline_path: LEAN4_BASELINE_PATH,
                expressions_path: LEAN4_EXPRESSIONS_PATH,
                metrics_path: None,
                baseline_schema_version: baseline.schema_version,
                normalization_version: baseline.normalization_version,
                lean4_version: baseline.lean4_version,
                baseline_cases: baseline.cases.len(),
                expression_count: expressions.len(),
                expected_expressions_sha256: baseline.expressions_sha256.clone(),
                actual_expressions_sha256: expressions_sha256.clone(),
                expressions_sha256_match: expressions_sha256 == baseline.expressions_sha256,
            },
            fallback_denial: FallbackDenialEvidence {
                issue: IssueRef::new(
                    3705,
                    "Zero-trust gate forbids sorryAx and trusted fallback constructors",
                ),
                gate_command: DENY_SORRY_RUST_GATE_COMMAND,
                launch_evidence_path: DENY_SORRY_LAUNCH_EVIDENCE_PATH,
                launch_evidence_status: deny_sorry_launch_evidence.status_label().to_string(),
                launch_evidence_summary: deny_sorry_launch_evidence.summary(),
                ratchet_path: UNCHECKED_DECL_RATCHET_PATH,
                static_lint: "clean replacement trust-core-evidence --deny-sorry",
                deny_sorry_lanes: vec![
                    "clean-kernel --test deny_sorry_gate",
                    "clean-kernel --test lean4_parity under DENY_SORRY=1",
                    "clean-elab soundness_gate accept under DENY_SORRY=1",
                    "clean-elab soundness_gate reject under DENY_SORRY=1",
                ],
                unchecked_decl_ratchet: UncheckedDeclRatchetEvidence {
                    add_decl_structural_count: ratchet.add_decl_structural_count,
                    add_decl_unchecked_count: ratchet.add_decl_unchecked_count,
                    last_updated: ratchet.last_updated,
                },
            },
            axiom_audit: AxiomAuditEvidence::from_artifact(
                &axiom_audit,
                &axiom_audit_launch_evidence,
            ),
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct VerificationAuditLaneExpectation {
    pub(crate) issue: u32,
    pub(crate) title: &'static str,
    pub(crate) closure_evidence_gate: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ProofSystemCertificationEvidence {
    pub(crate) issue: IssueRef,
    pub(crate) status: ReplacementStatus,
    pub(crate) launch_ready: bool,
    pub(crate) zero_trust_gates_passed: bool,
    pub(crate) verification_audit_path: &'static str,
    pub(crate) verification_audit_issue_state_evidence_path: &'static str,
    pub(crate) verification_audit_refresh_required: bool,
    pub(crate) verification_audit_open_lanes: Vec<VerificationAuditLaneEvidence>,
    pub(crate) replay_parity_rows: Vec<ProofSystemReplayParityRow>,
    pub(crate) blocking_verification_audit_lanes: usize,
    pub(crate) blocking_replay_parity_rows: usize,
    pub(crate) evidence_summary: String,
}

impl ProofSystemCertificationEvidence {
    pub(crate) fn from_current(
        zero_trust_gates: &[ZeroTrustGateRow],
        verification_audit: &str,
        verification_audit_issue_state: &str,
        replacement_rows: &[ReplacementRow],
    ) -> Result<Self, ReplacementError> {
        let zero_trust_gates_passed = zero_trust_gates
            .iter()
            .filter(|gate| gate.required_for_launch)
            .all(|gate| gate.status == ZeroTrustGateStatus::Passed);
        let verification_audit_open_lanes = proof_system_verification_audit_lanes(
            verification_audit,
            verification_audit_issue_state,
        )?;
        let replay_parity_rows = proof_system_replay_parity_rows(replacement_rows)?;
        let blocking_verification_audit_lanes = verification_audit_open_lanes.len();
        let blocking_replay_parity_rows = replay_parity_rows
            .iter()
            .filter(|row| row.blocks_certification)
            .count();
        let status = if zero_trust_gates_passed
            && blocking_verification_audit_lanes == 0
            && blocking_replay_parity_rows == 0
        {
            ReplacementStatus::Green
        } else if zero_trust_gates_passed {
            ReplacementStatus::InProgress
        } else {
            ReplacementStatus::Blocked
        };
        let launch_ready = status == ReplacementStatus::Green;

        Ok(Self {
            issue: IssueRef::new(
                3697,
                "clean proof system: zero-trust kernel, Mathverse, and replay certification",
            ),
            status,
            launch_ready,
            zero_trust_gates_passed,
            verification_audit_path: VERIFICATION_AUDIT_PATH,
            verification_audit_issue_state_evidence_path:
                VERIFICATION_AUDIT_ISSUE_STATE_EVIDENCE_PATH,
            verification_audit_refresh_required: true,
            verification_audit_open_lanes,
            replay_parity_rows,
            blocking_verification_audit_lanes,
            blocking_replay_parity_rows,
            evidence_summary: format!(
                "zero_trust_gates_passed={zero_trust_gates_passed}, verification_audit_open_lanes={blocking_verification_audit_lanes}, replay_parity_blockers={blocking_replay_parity_rows}"
            ),
        })
    }

    /// Fail-closed certification row for a checkout without the machine-local
    /// issue-state snapshot: every verification-audit lane counts as blocking
    /// (unknown state is not evidence of closure), so the row can never be
    /// Green; the status formula otherwise matches [`Self::from_current`].
    pub(crate) fn missing_issue_state_snapshot(
        zero_trust_gates: &[ZeroTrustGateRow],
        replacement_rows: &[ReplacementRow],
    ) -> Result<Self, ReplacementError> {
        let zero_trust_gates_passed = zero_trust_gates
            .iter()
            .filter(|gate| gate.required_for_launch)
            .all(|gate| gate.status == ZeroTrustGateStatus::Passed);
        let replay_parity_rows = proof_system_replay_parity_rows(replacement_rows)?;
        let blocking_verification_audit_lanes = PROOF_SYSTEM_VERIFICATION_AUDIT_LANES.len();
        let blocking_replay_parity_rows = replay_parity_rows
            .iter()
            .filter(|row| row.blocks_certification)
            .count();
        let status = if zero_trust_gates_passed {
            ReplacementStatus::InProgress
        } else {
            ReplacementStatus::Blocked
        };

        Ok(Self {
            issue: IssueRef::new(
                3697,
                "clean proof system: zero-trust kernel, Mathverse, and replay certification",
            ),
            status,
            launch_ready: false,
            zero_trust_gates_passed,
            verification_audit_path: VERIFICATION_AUDIT_PATH,
            verification_audit_issue_state_evidence_path:
                VERIFICATION_AUDIT_ISSUE_STATE_EVIDENCE_PATH,
            verification_audit_refresh_required: true,
            verification_audit_open_lanes: vec![],
            replay_parity_rows,
            blocking_verification_audit_lanes,
            blocking_replay_parity_rows,
            evidence_summary: format!(
                "zero_trust_gates_passed={zero_trust_gates_passed}, verification_audit_open_lanes={blocking_verification_audit_lanes}, replay_parity_blockers={blocking_replay_parity_rows}; {VERIFICATION_AUDIT_ISSUE_STATE_EVIDENCE_PATH} is missing on this checkout, so every verification-audit lane counts as blocking until a fresh gh issue-state snapshot is captured"
            ),
        })
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct VerificationAuditLaneEvidence {
    pub(crate) issue: IssueRef,
    pub(crate) audit_path: &'static str,
    pub(crate) state: &'static str,
    pub(crate) closure_evidence_gate: &'static str,
    pub(crate) blocks_certification: bool,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ProofSystemReplayParityRow {
    pub(crate) row_id: &'static str,
    pub(crate) issue: IssueRef,
    pub(crate) status: ReplacementStatus,
    pub(crate) evidence_artifact: &'static str,
    pub(crate) gate_command: &'static str,
    pub(crate) blocker: &'static str,
    pub(crate) blocks_certification: bool,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct KernelDifferentialEvidence {
    pub(crate) issue: IssueRef,
    pub(crate) test_command: &'static str,
    pub(crate) gate_command: &'static str,
    pub(crate) launch_evidence_path: &'static str,
    pub(crate) launch_evidence_status: String,
    pub(crate) launch_evidence_summary: String,
    pub(crate) gate_preflight_required: bool,
    pub(crate) gate_preflight_artifacts: Vec<&'static str>,
    pub(crate) gate_preflight_guards: Vec<&'static str>,
    pub(crate) baseline_path: &'static str,
    pub(crate) expressions_path: &'static str,
    pub(crate) metrics_path: Option<&'static str>,
    pub(crate) baseline_schema_version: u32,
    pub(crate) normalization_version: u32,
    pub(crate) lean4_version: String,
    pub(crate) baseline_cases: usize,
    pub(crate) expression_count: usize,
    pub(crate) expected_expressions_sha256: String,
    pub(crate) actual_expressions_sha256: String,
    pub(crate) expressions_sha256_match: bool,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct FallbackDenialEvidence {
    pub(crate) issue: IssueRef,
    pub(crate) gate_command: &'static str,
    pub(crate) launch_evidence_path: &'static str,
    pub(crate) launch_evidence_status: String,
    pub(crate) launch_evidence_summary: String,
    pub(crate) ratchet_path: &'static str,
    pub(crate) static_lint: &'static str,
    pub(crate) deny_sorry_lanes: Vec<&'static str>,
    pub(crate) unchecked_decl_ratchet: UncheckedDeclRatchetEvidence,
}
