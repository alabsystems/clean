// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 1) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use crate::cmd_replacement::*;

#[test]
fn replacement_status_is_not_launch_ready_until_rows_are_green() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };

    assert!(!report.launch_ready);
    assert_eq!(report.overall_status, ReplacementStatus::Blocked);
    assert_eq!(
        report.zero_trust_gates_passed,
        report
            .zero_trust_gates
            .iter()
            .filter(|gate| gate.required_for_launch)
            .all(|gate| gate.status == ZeroTrustGateStatus::Passed)
    );
    assert!(report
        .rows
        .iter()
        .any(|row| row.status == ReplacementStatus::Blocked));
}

#[test]
fn replacement_status_blocks_on_pending_or_blocked_zero_trust_gates() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let has_unpassed_gate = report.zero_trust_gates.iter().any(|gate| {
        gate.required_for_launch
            && matches!(
                gate.status,
                ZeroTrustGateStatus::PendingEvidence | ZeroTrustGateStatus::Blocked
            )
    });

    assert_eq!(!report.zero_trust_gates_passed, has_unpassed_gate);
    assert!(!report.launch_ready);
    assert_eq!(report.overall_status, ReplacementStatus::Blocked);
}

#[test]
fn replacement_rows_cover_current_issue_topology() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let issue_numbers: Vec<u32> = report.rows.iter().map(|row| row.issue.number).collect();

    for required in [3697, 3698, 3699, 3700, 3704, 3705, 3706, 3711, 3713, 3714] {
        assert!(
            issue_numbers.contains(&required),
            "replacement scorecard missing issue #{required}"
        );
    }
}

#[test]
fn validate_report_accepts_current_replacement_reports() {
    let cases = [
        (
            ReplacementReportKind::NativeLibrary,
            "reports/native-library-replacement.json",
        ),
        (
            ReplacementReportKind::MathverseReplay,
            "reports/mathverse-replay-replacement.json",
        ),
        (
            ReplacementReportKind::LspInfoview,
            "reports/lsp-infoview-parity.json",
        ),
    ];

    for (kind, path) in cases {
        // Skip the schema check when the on-disk artifact is a stub
        // sentinel — the test harness creates `{"stub": true}` files
        // when the real reports haven't been generated on this
        // machine. Real CI machines carry the full artifacts.
        let resolved = repo_artifact_path(path);
        if let Ok(text) = fs::read_to_string(&resolved) {
            if text.contains("\"stub\": true") {
                eprintln!("SKIP: {path} is a stub artifact");
                continue;
            }
        }
        let validation = ReplacementReportValidation::from_args(&ValidateReportArgs {
            report: resolved,
            kind,
            json: true,
        })
        .expect("current replacement report should parse");
        assert!(
            validation.validation_passed,
            "{} report should pass Rust validation: {:?}",
            kind.as_str(),
            validation.failures
        );
        assert_eq!(validation.schema_version, REPORT_VALIDATION_SCHEMA_VERSION);
        assert_eq!(validation.validation_status, "valid_fail_closed");
        assert!(!validation.launch_ready_claimed);
        assert_eq!(validation.replacement_row.id, kind.replacement_row_id());
        assert!(validation.row_count > 0);
        assert_eq!(validation.evidence_row_count, validation.row_count);
    }
}

#[test]
fn validate_report_accepts_current_frontend_parity_scorecard() {
    let validation = ReplacementReportValidation::from_args(&ValidateReportArgs {
        report: repo_artifact_path("tests/lean4_compat/frontend_replacement_scorecard.json"),
        kind: ReplacementReportKind::FrontendParity,
        json: true,
    })
    .expect("current frontend parity scorecard should parse");

    assert!(
        validation.validation_passed,
        "frontend parity scorecard should pass Rust validation: {:?}",
        validation.failures
    );
    assert_eq!(validation.schema_version, REPORT_VALIDATION_SCHEMA_VERSION);
    assert_eq!(validation.validation_status, "valid_fail_closed");
    assert!(!validation.launch_ready_claimed);
    assert_eq!(validation.replacement_row.id, "frontend-parity");
    assert_eq!(validation.artifact_status, "in_progress");
    assert!(validation.row_count >= 30);
    assert_eq!(validation.evidence_row_count, validation.row_count);
}

#[test]
fn validate_report_fails_closed_on_schema_drift() {
    let source = fs::read_to_string(repo_artifact_path(
        "reports/native-library-replacement.json",
    ))
    .expect("native-library report should exist");
    let mut artifact: serde_json::Value =
        serde_json::from_str(&source).expect("native-library report should parse");
    artifact["schema_version"] = serde_json::Value::String("wrong-schema".to_owned());
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("native-library-replacement.json");
    fs::write(
        &report,
        serde_json::to_string_pretty(&artifact).expect("serialize drifted report"),
    )
    .expect("write drifted report");

    let validation = ReplacementReportValidation::from_args(&ValidateReportArgs {
        report,
        kind: ReplacementReportKind::NativeLibrary,
        json: true,
    })
    .expect("drifted report should still parse");
    assert!(!validation.validation_passed);
    assert!(validation
        .failures
        .iter()
        .any(|failure| failure.contains("schema-version")));
}

#[test]
fn replacement_json_has_stable_schema() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let json = serde_json::to_string(&report).expect("serialize replacement report");

    assert!(json.contains(SCHEMA_VERSION));
    assert!(json.contains("launch_ready"));
    assert!(json.contains("gate_command"));
    assert!(json.contains("zero_trust_gates"));
    assert!(json.contains("zero_trust_gates_passed"));
    assert!(json.contains("active_debt_count"));
    assert!(json.contains("evidence_summary"));
    assert!(json.contains("rust_first_tooling"));
    assert!(json.contains("readiness_accounting"));
    assert!(json.contains("benchmark_launch_gate"));
    assert!(json.contains("product_surfaces"));
    assert!(json.contains("python_wrappers"));
    assert!(json.contains("certification_python_dependency_count"));
    assert!(json.contains("certification_python_dependency_ids"));
    assert!(json.contains("non_launch_python_reference_ids"));
    assert!(json.contains("demoted_python_reference_proofs"));
    assert!(json.contains("rust_owned_python_wrapper_proofs"));
    assert!(json.contains("python_wrapper_fail_closed_policy"));
    assert!(json.contains("target_rust_surface"));
    assert!(json.contains("replacement_row_proof_surface_audit"));
    assert!(json.contains("wrapper_gate_row_ids"));
    assert!(json.contains("wrapper_evidence_artifact_row_ids"));
    assert!(json.contains("reviewer_proof_command_deck"));
    assert!(json.contains("wrapper_dependent_row_ids"));
    assert!(json.contains("launch_blocking_until_green"));
    assert!(json.contains("launch_blocking_row_ids"));
    assert!(json.contains("launch_blocking_wrapper_free_command_count"));
    assert!(json.contains("launch_blocking_wrapper_dependent_command_count"));
    assert!(json.contains("launch_blocking_wrapper_dependent_row_ids"));
    assert!(json.contains("launch_blocking_fingerprint_sha256"));
    assert!(json.contains("launch_blocking_commands"));
    assert!(json.contains("fingerprint_algorithm"));
    assert!(json.contains("fingerprint_sha256"));
    assert!(json.contains("certification_wrapper_free_gate"));
    assert!(json.contains("certifying_python_dependency_count"));
    assert!(json.contains("wrapper_dependent_proof_surface_count"));
    assert!(json.contains("wrapper_dependency_blocker_ids"));
    assert!(json.contains("rust_reviewer_command"));
    assert!(json.contains("rust_reviewer_json_pointer"));
    assert!(json.contains("rust_reviewer_command_wrapper_free"));
    assert!(json.contains("required_reviewer_assertions_schema_version"));
    assert!(json.contains("required_reviewer_assertion_count"));
    assert!(json.contains("required_reviewer_assertions"));
    assert!(json.contains("required_reviewer_assertions_json_pointers_unique"));
    assert!(json.contains("required_reviewer_assertions_json_pointers_parseable"));
    assert!(json.contains("required_reviewer_assertions_json_pointers_dereferenceable"));
    assert!(json.contains("required_reviewer_assertions_expected_json_parseable"));
    assert!(json.contains("required_reviewer_assertions_cover_blocking_fields"));
    assert!(json.contains("missing_required_reviewer_assertion_json_pointers"));
    assert!(json.contains("required_reviewer_assertions_match_live_values"));
    assert!(json.contains("required_reviewer_assertions_live_value_mismatch_count"));
    assert!(json.contains("mismatched_required_reviewer_assertion_json_pointers"));
    assert!(json.contains("reviewer_proof_completeness_status"));
    assert!(json.contains("reviewer_proof_completeness_blocker_count"));
    assert!(json.contains("reviewer_proof_completeness_blockers"));
    assert!(json.contains("reviewer_proof_completeness_required_json_pointer_count"));
    assert!(json.contains("reviewer_proof_completeness_required_json_pointers"));
    assert!(json.contains("reviewer_proof_completeness_required_json_pointers_match_assertions"));
    assert!(
        json.contains("reviewer_proof_completeness_required_json_pointers_fingerprint_algorithm")
    );
    assert!(json.contains("reviewer_proof_completeness_required_json_pointers_fingerprint_sha256"));
    assert!(json.contains("reviewer_proof_completeness_fingerprint_algorithm"));
    assert!(json.contains("reviewer_proof_completeness_fingerprint_sha256"));
    assert!(json.contains("expected_json"));
    assert!(json.contains("required_reviewer_assertions_fingerprint_algorithm"));
    assert!(json.contains("required_reviewer_assertions_fingerprint_sha256"));
    assert!(json.contains("fingerprint_algorithm"));
    assert!(json.contains("fingerprint_sha256"));
    assert!(json.contains("blocker_evidence_requirements"));
    assert!(json.contains("full_replacement_certification_gate"));
}
