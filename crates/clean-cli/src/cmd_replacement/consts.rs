// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Schema versions, artifact paths, and gate expectation constants.

use super::*;

pub(crate) const SCHEMA_VERSION: &str = "clean-replacement-status-v1";
pub(crate) const TACTIC_PARITY_SCHEMA_VERSION: &str = "clean-tactic-parity-report-v1";
pub(crate) const TACTIC_PARITY_COUNT_ARTIFACT_SCHEMA_VERSION: &str =
    "clean-tactic-parity-count-artifact-v1";
pub(crate) const TACTIC_PARITY_COUNT_ARTIFACT_PATH: &str = "reports/tactic-parity-counts.json";
pub(crate) const STRICT_SOLVER_FRAGMENT_DASHBOARD_SCHEMA_VERSION: &str =
    "clean-strict-solver-fragment-dashboard-v1";
pub(crate) const STRICT_SOLVER_FRAGMENT_DASHBOARD_PATH: &str =
    "reports/strict-solver-fragment-dashboard.json";
pub(crate) const STRICT_SOLVER_FRAGMENT_EXPECTED_ROW_COUNT: usize = 10;
pub(crate) const STRICT_SOLVER_FRAGMENT_EXPECTED_SUPPORTED_ZERO_TRUST_ROWS: usize = 3;
pub(crate) const STRICT_SOLVER_FRAGMENT_EXPECTED_ZERO_TRUST_RECOVERY_ROWS: usize = 1;
pub(crate) const STRICT_SOLVER_FRAGMENT_EXPECTED_RESIDUAL_TRUST_ACCEPTANCE_ROWS: usize = 0;
pub(crate) const TRUST_CORE_EVIDENCE_SCHEMA_VERSION: &str = "clean-trust-core-evidence-v1";
pub(crate) const TRUST_BOUNDARY_AUDIT_SCHEMA_VERSION: &str = "clean-trust-boundary-audit-report-v1";
pub(crate) const REPORT_VALIDATION_SCHEMA_VERSION: &str = "clean-replacement-report-validation-v1";
pub(crate) const TRUST_BOUNDARY_EXPECTED_TESTS_PATH: &str =
    "scripts/trust_boundary_expected_tests.txt";
pub(crate) const RELEASE_ISSUE_HYGIENE_SCHEMA_VERSION: &str = "clean-release-issue-hygiene-gate-v0";
pub(crate) const TARGET_CLAIM: &str =
    "clean + Mathverse fully replace Lean4 for practical theorem-proving workflows";
pub(crate) const RELEASE_ISSUE_REQUIRED_FIELDS: &[&str] = &[
    "number",
    "title",
    "url",
    "labels",
    "assignees",
    "body",
    "comments",
];
pub(crate) const RELEASE_ISSUE_GH_JSON_FIELDS: &str =
    "number,title,url,labels,assignees,body,comments";
pub(crate) const RELEASE_ISSUE_WATCHED_LABELS: &[&str] =
    &["urgent", "P1", "blocked", "local-maximum"];
pub(crate) const RELEASE_ISSUE_OWNER_ACTION: &str = "assign a release owner or add Wn/Rn/Mn/provN";
pub(crate) const RELEASE_DECISION_ACTION: &str = "add a visible `Release decision:` note";
pub(crate) const LEAN4_BASELINE_PATH: &str = "tests/differential/lean4_baseline.json";
pub(crate) const LEAN4_EXPRESSIONS_PATH: &str = "tests/differential/expressions.txt";
pub(crate) const KERNEL_SOUNDNESS_GATE_PATH: &str = "scripts/kernel_soundness_gate.sh";
pub(crate) const KERNEL_SOUNDNESS_GATE_COMMAND: &str = "./scripts/kernel_soundness_gate.sh";
pub(crate) const KERNEL_SOUNDNESS_RUST_GATE_COMMAND: &str =
    "clean replacement trust-core-evidence --kernel-soundness";
pub(crate) const KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_SCHEMA_VERSION: &str =
    "clean-kernel-soundness-launch-evidence-v1";
pub(crate) const KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_PATH: &str =
    "reports/kernel-soundness-launch-evidence.json";
pub(crate) const KERNEL_SOUNDNESS_EXPECTED_STEPS: u32 = 3;
pub(crate) const DENY_SORRY_GATE_PATH: &str = "scripts/deny_sorry_gate.sh";
pub(crate) const DENY_SORRY_GATE_COMMAND: &str = "./scripts/deny_sorry_gate.sh";
pub(crate) const DENY_SORRY_RUST_GATE_COMMAND: &str =
    "clean replacement trust-core-evidence --deny-sorry";
pub(crate) const DENY_SORRY_LAUNCH_EVIDENCE_SCHEMA_VERSION: &str =
    "clean-deny-sorry-launch-evidence-v1";
pub(crate) const DENY_SORRY_LAUNCH_EVIDENCE_PATH: &str = "reports/deny-sorry-launch-evidence.json";
pub(crate) const DENY_SORRY_EXPECTED_STEPS: u32 = 6;
pub(crate) const TRUST_CORE_RUST_SOURCE_PATH: &str = "crates/clean-cli/src/cmd_replacement.rs";
pub(crate) const LINT_SORRY_BYPASS_PATH: &str = "scripts/lint_sorry_bypass.sh";
pub(crate) const AXIOM_AUDIT_RELEASE_CHECK_PATH: &str = "scripts/axiom_audit_release_check.sh";
pub(crate) const AXIOM_AUDIT_GATE_COMMAND: &str = "clean replacement axiom-audit --verify data/axiom_audit.json --evidence reports/axiom-audit-launch-evidence.json --json";
pub(crate) const AXIOM_AUDIT_LAUNCH_EVIDENCE_SCHEMA_VERSION: &str =
    "clean-axiom-audit-launch-evidence-v1";
pub(crate) const AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH: &str =
    "reports/axiom-audit-launch-evidence.json";
pub(crate) const AXIOM_AUDIT_EXPECTED_STEPS: u32 = 2;
pub(crate) const AXIOM_AUDIT_VERIFY_SCHEMA_VERSION: &str = "clean-axiom-audit-verify-v1";
pub(crate) const AXIOM_AUDIT_RUST_SOURCE_PATH: &str = "crates/clean-cli/src/cmd_replacement.rs";
pub(crate) const UNCHECKED_DECL_RATCHET_PATH: &str = "data/unchecked_decl_ratchet.json";
pub(crate) const AXIOM_AUDIT_PATH: &str = "data/axiom_audit.json";
pub(crate) const VERIFICATION_AUDIT_PATH: &str = "docs/VERIFICATION_AUDIT.md";
pub(crate) const VERIFICATION_AUDIT_ISSUE_STATE_EVIDENCE_PATH: &str =
    "reports/2026-04-27-proof-system-verification-audit-issue-state.md";
pub(crate) const PROOF_SYSTEM_CERTIFICATION_BLOCKER_REPORT_PATH: &str =
    "reports/2026-04-27-proof-system-certification-blockers.md";
pub(crate) const PROOF_SYSTEM_REPLAY_PARITY_ROW_IDS: &[&str] = &[
    "kernel-differential",
    "tactic-parity",
    "strict-reconstruction",
    "mathverse-replay",
];
pub(crate) const PROOF_SYSTEM_VERIFICATION_AUDIT_LANES: &[VerificationAuditLaneExpectation] = &[
    VerificationAuditLaneExpectation {
        issue: 3656,
        title: "Bridge-dependent Rat theorem rollback",
        closure_evidence_gate:
            "Direct bridge consumers demoted or otherwise removed from theorem story.",
    },
    VerificationAuditLaneExpectation {
        issue: 3646,
        title: "MASQUERADE shorthand false negatives",
        closure_evidence_gate:
            "Parser-shorthand detector catches known shorthand patterns without widening false positives.",
    },
    VerificationAuditLaneExpectation {
        issue: 3640,
        title: "Axiom audit live-row drift",
        closure_evidence_gate:
            "`data/axiom_audit.json` reconciled against live verification output on current `main`.",
    },
    VerificationAuditLaneExpectation {
        issue: 464,
        title: "Constructive TypePreservation frontier",
        closure_evidence_gate:
            "Remaining `church_rosser_whnf` leaf closed or sharply reduced with current blocker documented.",
    },
];
pub(crate) const KERNEL_GATE_PREFLIGHT_MARKERS: &[&str] = &[
    "validate_differential_artifacts",
    "--- Lane 0: Differential artifact preflight ---",
    "unset REGEN_BASELINE",
    "Path(\"tests/differential/expressions.txt\")",
    "Path(\"tests/differential/lean4_baseline.json\")",
    "case.get(\"expr\") != expression",
];
pub(crate) const KERNEL_GATE_PREFLIGHT_GUARDS: &[&str] = &[
    "baseline schema_version equals 1",
    "baseline normalization_version equals 2",
    "expressions_sha256 matches expressions.txt",
    "baseline case count matches active expressions",
    "baseline case expressions match expressions.txt order",
    "type_norm is present for every baseline case",
    "REGEN_BASELINE is unset before the parity lane",
];
pub(crate) const KERNEL_SOUNDNESS_EXPECTED_LANES: &[KernelSoundnessLaneExpectation] = &[
    KernelSoundnessLaneExpectation {
        id: "differential_artifact_preflight",
        expected_tests: None,
        expected_output: None,
    },
    KernelSoundnessLaneExpectation {
        id: "kernel_lean4_parity",
        expected_tests: Some(1),
        expected_output: None,
    },
    KernelSoundnessLaneExpectation {
        id: "elab_soundness_gate",
        expected_tests: None,
        expected_output: Some("soundness_gate: PASS"),
    },
];
pub(crate) const DENY_SORRY_EXPECTED_LANES: &[DenySorryLaneExpectation] = &[
    DenySorryLaneExpectation {
        id: "lint_sorry_bypass",
        expected_tests: None,
    },
    DenySorryLaneExpectation {
        id: "unchecked_decl_ratchet_zero",
        expected_tests: None,
    },
    DenySorryLaneExpectation {
        id: "kernel_deny_sorry_gate",
        expected_tests: Some(11),
    },
    DenySorryLaneExpectation {
        id: "kernel_lean4_parity",
        expected_tests: Some(1),
    },
    DenySorryLaneExpectation {
        id: "elab_soundness_gate_accept",
        expected_tests: Some(1),
    },
    DenySorryLaneExpectation {
        id: "elab_soundness_gate_reject",
        expected_tests: Some(1),
    },
];
pub(crate) const AXIOM_AUDIT_EXPECTED_LANES: &[AxiomAuditLaneExpectation] = &[
    AxiomAuditLaneExpectation {
        id: "aggregate_consistency",
    },
    AxiomAuditLaneExpectation {
        id: "live_row_reconciliation_and_constructive_claims",
    },
];
pub(crate) const SORRY_BYPASS_ALLOWED_FILES: &[&str] = &[
    "crates/clean-kernel/src/sorry/build.rs",
    "crates/clean-kernel/src/sorry/tests.rs",
    "crates/clean-kernel/src/sorry/mod.rs",
    "crates/clean-kernel/src/expr/sorry.rs",
    "crates/clean-kernel/src/env/core.rs",
    "crates/clean-kernel/tests/sorry_scan_equivalence.rs",
];
