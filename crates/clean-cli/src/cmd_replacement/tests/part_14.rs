// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 14) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use super::support::*;
use crate::cmd_replacement::*;

#[test]
fn tactic_parity_count_artifact_consistency_rejects_stale_full_corpus_allowed_evidence_kinds_fingerprint(
) {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_sha256 =
        "stale".to_owned();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
        "representative tactic artifact must keep full-corpus evidence kind fingerprint fresh",
    );
    assert!(failures.iter().any(|failure| {
        failure
            .contains("full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_sha256")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_acceptance_criteria() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_criteria_required.pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must keep full-corpus acceptance criteria");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_corpus_acceptance_criteria_required")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_stale_acceptance_criteria_fingerprint() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_criteria_fingerprint_sha256 = "stale".to_owned();

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must keep criteria fingerprint fresh");
    assert!(failures
        .iter()
        .any(|failure| { failure.contains("full_corpus_acceptance_criteria_fingerprint_sha256") }));
}

#[test]
fn tactic_parity_report_linkage_rejects_strict_dashboard_drift() {
    let mut report = TacticParityReport::current();
    report
        .strict_solver_fragment_dashboard
        .supported_zero_trust_rows -= 1;

    let failures = validate_tactic_parity_report_linkage(&report)
        .expect_err("strict dashboard/count drift must fail closed");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("supported_zero_trust_rows")));
}

#[test]
fn tactic_parity_report_marks_visible_strict_qf_uf_recovery_zero_trust() {
    let report = TacticParityReport::current();
    let strict_qf_uf = strict_reconstruction_row(&report, "ay_verify_strict_qf_uf");
    let dashboard = strict_reconstruction_row(&report, "strict_solver_fragment_dashboard");

    assert!(!report.launch_ready);
    assert_eq!(
        report
            .reconstruction_counts
            .get(&StrictReconstructionStatus::SupportedZeroTrust)
            .copied()
            .unwrap_or(0),
        2
    );
    assert_eq!(
        report
            .reconstruction_counts
            .get(&StrictReconstructionStatus::EvidenceGap)
            .copied()
            .unwrap_or(0),
        0
    );
    assert_eq!(
        report
            .reconstruction_counts
            .get(&StrictReconstructionStatus::ParityGap)
            .copied()
            .unwrap_or(0),
        0
    );
    assert_eq!(
        strict_qf_uf.status,
        StrictReconstructionStatus::SupportedZeroTrust
    );
    assert!(strict_qf_uf.evidence.contains("--features ay-smt"));
    assert!(strict_qf_uf.evidence.contains("ay_tactics_tests"));
    assert_eq!(
        dashboard.status,
        StrictReconstructionStatus::SupportedZeroTrust
    );
    assert_eq!(dashboard.evidence, STRICT_SOLVER_FRAGMENT_DASHBOARD_PATH);
}

#[test]
fn tactic_parity_report_includes_generated_strict_solver_fragment_dashboard_counts() {
    let report = TacticParityReport::current();
    let dashboard = &report.strict_solver_fragment_dashboard;

    assert_eq!(
        dashboard.schema_version,
        STRICT_SOLVER_FRAGMENT_DASHBOARD_SCHEMA_VERSION
    );
    assert_eq!(
        dashboard.source_artifact,
        STRICT_SOLVER_FRAGMENT_DASHBOARD_PATH
    );
    assert_eq!(dashboard.row_count, dashboard.rows.len());
    assert_eq!(dashboard.row_count, 10);
    assert_eq!(dashboard.supported_zero_trust_rows, 3);
    assert_eq!(dashboard.unsupported_reject_and_fallback_rows, 7);
    assert_eq!(dashboard.direct_trust_rejected_rows, 10);
    assert_eq!(dashboard.zero_trust_recovery_rows, 1);
    assert_eq!(dashboard.residual_trust_acceptance_rows, 0);
    assert!(dashboard.strict_reconstruction_gate.passed);
    assert!(dashboard.strict_reconstruction_gate.row_count.passed);
    assert_eq!(dashboard.strict_reconstruction_gate.row_count.expected, 10);
    assert_eq!(dashboard.strict_reconstruction_gate.row_count.observed, 10);
    assert!(
        dashboard
            .strict_reconstruction_gate
            .supported_zero_trust_rows
            .passed
    );
    assert!(
        dashboard
            .strict_reconstruction_gate
            .zero_trust_recovery_rows
            .passed
    );
    assert!(
        dashboard
            .strict_reconstruction_gate
            .residual_trust_acceptance_rows
            .passed
    );

    let qf_uf = dashboard
        .rows
        .iter()
        .find(|row| row.fragment == "QF_UF")
        .expect("QF_UF strict dashboard row");
    assert_eq!(
        qf_uf.behavior,
        StrictSolverFragmentBehavior::SupportedZeroTrust
    );
    assert!(qf_uf.zero_trust_required);
    assert!(qf_uf.zero_trust_recovery);

    let qf_bv = dashboard
        .rows
        .iter()
        .find(|row| row.fragment == "QF_BV")
        .expect("QF_BV strict dashboard row");
    assert_eq!(
        qf_bv.behavior,
        StrictSolverFragmentBehavior::UnsupportedRejectAndFallback
    );
    assert!(!qf_bv.zero_trust_required);
    assert!(!qf_bv.residual_trust_accepted_in_strict);
}

#[test]
fn strict_solver_fragment_dashboard_artifact_matches_report_counts() {
    let report = TacticParityReport::current();
    let dashboard = &report.strict_solver_fragment_dashboard;
    let artifact = fs::read_to_string(repo_artifact_path(STRICT_SOLVER_FRAGMENT_DASHBOARD_PATH))
        .expect("strict solver-fragment dashboard artifact should be checked in");
    if artifact.contains("\"stub\": true") {
        eprintln!("SKIP: strict solver-fragment dashboard is a stub artifact");
        return;
    }
    let artifact_json: serde_json::Value =
        serde_json::from_str(&artifact).expect("strict dashboard artifact should be JSON");
    let rows = artifact_json["rows"]
        .as_array()
        .expect("strict dashboard artifact rows should be an array");

    assert_eq!(
        artifact_json["schema_version"],
        STRICT_SOLVER_FRAGMENT_DASHBOARD_SCHEMA_VERSION
    );
    assert_eq!(artifact_json["summary"]["row_count"], rows.len());
    assert_eq!(artifact_json["summary"]["row_count"], dashboard.row_count);
    assert_eq!(
        artifact_json["summary"]["supported_zero_trust_rows"],
        dashboard.supported_zero_trust_rows
    );
    assert_eq!(
        artifact_json["summary"]["unsupported_reject_and_fallback_rows"],
        dashboard.unsupported_reject_and_fallback_rows
    );
    assert_eq!(
        artifact_json["summary"]["zero_trust_recovery_rows"],
        dashboard.zero_trust_recovery_rows
    );
    assert_eq!(
        artifact_json["summary"]["residual_trust_acceptance_rows"],
        dashboard.residual_trust_acceptance_rows
    );
    assert_eq!(
        artifact_json["strict_reconstruction_gate"]["passed"],
        dashboard.strict_reconstruction_gate.passed
    );
    assert_eq!(
        artifact_json["strict_reconstruction_gate"]["row_count"]["observed"],
        dashboard.strict_reconstruction_gate.row_count.observed
    );
    assert_eq!(
        artifact_json["strict_reconstruction_gate"]["supported_zero_trust_rows"]["observed"],
        dashboard
            .strict_reconstruction_gate
            .supported_zero_trust_rows
            .observed
    );
    assert_eq!(
        artifact_json["strict_reconstruction_gate"]["zero_trust_recovery_rows"]["observed"],
        dashboard
            .strict_reconstruction_gate
            .zero_trust_recovery_rows
            .observed
    );
    assert_eq!(
        artifact_json["strict_reconstruction_gate"]["residual_trust_acceptance_rows"]["observed"],
        dashboard
            .strict_reconstruction_gate
            .residual_trust_acceptance_rows
            .observed
    );
}

#[test]
fn strict_solver_fragment_dashboard_gate_fails_closed_on_count_drift() {
    let gate = StrictSolverFragmentDashboardGate::from_counts(9, 3, 1, 0);
    assert!(!gate.passed);
    assert!(!gate.row_count.passed);
    assert!(gate.supported_zero_trust_rows.passed);

    let gate = StrictSolverFragmentDashboardGate::from_counts(10, 2, 1, 0);
    assert!(!gate.passed);
    assert!(!gate.supported_zero_trust_rows.passed);

    let gate = StrictSolverFragmentDashboardGate::from_counts(10, 3, 0, 0);
    assert!(!gate.passed);
    assert!(!gate.zero_trust_recovery_rows.passed);

    let gate = StrictSolverFragmentDashboardGate::from_counts(10, 3, 1, 1);
    assert!(!gate.passed);
    assert!(!gate.residual_trust_acceptance_rows.passed);
}

#[test]
fn tactic_parity_json_has_stable_schema() {
    let report = TacticParityReport::current();
    let json = serde_json::to_string(&report).expect("serialize tactic parity report");

    assert!(json.contains(TACTIC_PARITY_SCHEMA_VERSION));
    assert!(json.contains("strict_reconstruction"));
    assert!(json.contains("trusted_arith_count"));
    assert!(json.contains("trusted_ay_count"));
    assert!(json.contains("strict_solver_fragment_dashboard"));
    assert!(json.contains("row_count"));
    assert!(json.contains("ProofCarrying"));
    assert!(json.contains("SupportedZeroTrust"));
}
