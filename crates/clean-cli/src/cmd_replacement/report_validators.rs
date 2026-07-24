// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-kind replacement report validators.

use super::*;

pub(crate) fn validate_native_library_report(
    value: &serde_json::Value,
    checks: &mut Vec<ReplacementReportValidationCheck>,
    failures: &mut Vec<String>,
) {
    let rows = value
        .get("rows")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    push_report_validation_check(
        checks,
        failures,
        "native-evidence-rows",
        string_array_contains(
            value,
            &["summary", "native_evidence_rows"],
            "native-shard-trust-gate",
        ),
        "summary.native_evidence_rows should include native-shard-trust-gate".to_owned(),
    );
    push_report_validation_check(
        checks,
        failures,
        "mathlib-compatibility-row",
        string_array_contains(
            value,
            &["summary", "compatibility_only_rows"],
            "mathlib-olean-compatibility",
        ) && row_value_by_id(&rows, "mathlib-olean-compatibility")
            .and_then(|row| row.get("status"))
            .and_then(serde_json::Value::as_str)
            == Some("compatibility_only"),
        "Mathlib row must stay compatibility_only and be counted as compatibility-only".to_owned(),
    );
    push_report_validation_check(
        checks,
        failures,
        "native-non-claim",
        value
            .get("claim")
            .and_then(serde_json::Value::as_str)
            .is_some_and(|claim| claim.contains("Full native Mathlib replacement is not claimed")),
        "claim should explicitly avoid full native Mathlib replacement".to_owned(),
    );
    push_report_validation_check(
        checks,
        failures,
        "api-coverage-matrix-present",
        value
            .get("api_coverage_matrix")
            .and_then(serde_json::Value::as_object)
            .is_some_and(|matrix| !matrix.is_empty()),
        "api_coverage_matrix should be present and non-empty".to_owned(),
    );
}

pub(crate) fn validate_mathverse_replay_report(
    value: &serde_json::Value,
    checks: &mut Vec<ReplacementReportValidationCheck>,
    failures: &mut Vec<String>,
) {
    push_report_validation_check(
        checks,
        failures,
        "mathverse-corpus-blocked-row",
        string_array_contains(
            value,
            &["summary", "blocked_rows"],
            "production-corpus-replay-coverage",
        ),
        "summary.blocked_rows should include production-corpus-replay-coverage".to_owned(),
    );
    let corpus = value
        .get("summary")
        .and_then(|summary| summary.get("production_corpus"));
    let found = corpus
        .and_then(|corpus| corpus.get("found"))
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    let native_gate_verified = corpus
        .and_then(|corpus| corpus.get("native_gate_verified"))
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    let applied = corpus
        .and_then(|corpus| corpus.get("applied_through_strict_mathverse_use"))
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    let rejected = corpus
        .and_then(|corpus| corpus.get("rejected"))
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    let unsupported = corpus
        .and_then(|corpus| corpus.get("unsupported"))
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    push_report_validation_check(
        checks,
        failures,
        "mathverse-corpus-accounting",
        found > 0 && found == native_gate_verified + applied + rejected + unsupported,
        format!(
            "found={found}, native_gate_verified={native_gate_verified}, applied={applied}, rejected={rejected}, unsupported={unsupported}"
        ),
    );
    push_report_validation_check(
        checks,
        failures,
        "mathverse-corpus-incomplete",
        corpus
            .and_then(|corpus| corpus.get("status"))
            .and_then(serde_json::Value::as_str)
            == Some("incomplete")
            && applied == 0,
        "production corpus should remain explicitly incomplete until strict replay application lands"
            .to_owned(),
    );
}

pub(crate) fn validate_lsp_infoview_report(
    value: &serde_json::Value,
    checks: &mut Vec<ReplacementReportValidationCheck>,
    failures: &mut Vec<String>,
) {
    let rows = value
        .get("rows")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    push_report_validation_check(
        checks,
        failures,
        "lsp-standard-row-partial",
        row_value_by_id(&rows, "standard-lsp-parity")
            .and_then(|row| row.get("status"))
            .and_then(serde_json::Value::as_str)
            .is_some_and(|status| status.starts_with("partial_")),
        "standard-lsp-parity should remain partial until full parity evidence exists".to_owned(),
    );
    let code_action_evidence_passed = row_value_by_id(&rows, "standard-lsp-parity")
        .and_then(|row| row.get("evidence"))
        .and_then(serde_json::Value::as_array)
        .is_some_and(|evidence_items| {
            evidence_items.iter().any(|evidence| {
                evidence.get("function").and_then(serde_json::Value::as_str)
                    == Some(
                        "backend::tests::test_code_action_import_quickfix_from_unknown_identifier_diagnostic",
                    )
                    && evidence.get("run_status").and_then(serde_json::Value::as_str)
                        == Some("passed")
                    && evidence
                        .get("observed_result")
                        .and_then(serde_json::Value::as_str)
                        == Some("1 passed; 0 failed; 138 filtered out")
            })
        });
    push_report_validation_check(
        checks,
        failures,
        "lsp-code-action-evidence",
        code_action_evidence_passed,
        "standard-lsp-parity should include exact passing code-action import evidence".to_owned(),
    );
    push_report_validation_check(
        checks,
        failures,
        "lsp-fail-closed-blocker",
        value
            .get("overall_blockers")
            .and_then(serde_json::Value::as_array)
            .is_some_and(|blockers| {
                blockers.iter().any(|blocker| {
                    blocker.as_str().is_some_and(|blocker| {
                        blocker.contains("HN launch readiness remains false")
                    })
                })
            }),
        "overall blockers should keep HN launch readiness false".to_owned(),
    );
}

pub(crate) fn json_u64_at(value: &serde_json::Value, path: &[&str]) -> u64 {
    let mut cursor = value;
    for key in path {
        cursor = match cursor.get(*key) {
            Some(next) => next,
            None => return 0,
        };
    }
    cursor.as_u64().unwrap_or_default()
}

pub(crate) fn validate_frontend_parity_report(
    value: &serde_json::Value,
    checks: &mut Vec<ReplacementReportValidationCheck>,
    failures: &mut Vec<String>,
) {
    let rows = value
        .get("rows")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    let required_dimensions = [
        "parse",
        "elab",
        "kernel",
        "trust",
        "diagnostic",
        "expected_failure",
        "lean4_vs_clean_run_artifact",
        "exit_status_cross_check",
        "diagnostic_artifact_cross_check",
    ];
    let dimensions: std::collections::BTreeSet<&str> = rows
        .iter()
        .filter_map(|row| row.get("dimension").and_then(serde_json::Value::as_str))
        .collect();
    let missing_dimensions: Vec<&str> = required_dimensions
        .iter()
        .copied()
        .filter(|dimension| !dimensions.contains(dimension))
        .collect();
    push_report_validation_check(
        checks,
        failures,
        "frontend-required-dimensions",
        missing_dimensions.is_empty(),
        if missing_dimensions.is_empty() {
            format!(
                "required parse/elab/kernel/trust/diagnostic/failure dimensions present across {} row(s)",
                rows.len()
            )
        } else {
            format!("missing dimensions: {}", missing_dimensions.join(", "))
        },
    );

    let required_rows = [
        "phase1-parse-only-corpus",
        "phase1-profiled-elab-corpus",
        "frontend-slice-parse-elab-kernel",
        "trust-boundary",
        "diagnostic-profile-boundary",
        "expected-failure-profile-boundary",
        "lean4-vs-clean-run-artifact-guard",
        "exit-status-evidence-cross-check-guard",
        "diagnostic-artifact-cross-check-guard",
    ];
    let missing_rows: Vec<&str> = required_rows
        .iter()
        .copied()
        .filter(|row_id| row_value_by_id(&rows, row_id).is_none())
        .collect();
    push_report_validation_check(
        checks,
        failures,
        "frontend-required-rows",
        missing_rows.is_empty(),
        if missing_rows.is_empty() {
            "stable/canary corpus parse, elab, kernel, trust, diagnostic, and failure rows present"
                .to_owned()
        } else {
            format!("missing rows: {}", missing_rows.join(", "))
        },
    );

    let ready_rows: Vec<String> = rows
        .iter()
        .filter(|row| {
            row.get("replacement_ready")
                .and_then(serde_json::Value::as_bool)
                .unwrap_or(false)
        })
        .filter_map(|row| row.get("id").and_then(serde_json::Value::as_str))
        .map(str::to_owned)
        .collect();
    push_report_validation_check(
        checks,
        failures,
        "frontend-fail-closed-no-ready-rows",
        ready_rows.is_empty(),
        if ready_rows.is_empty() {
            "all frontend rows remain fail-closed and non-ready".to_owned()
        } else {
            format!(
                "unexpected replacement-ready rows: {}",
                ready_rows.join(", ")
            )
        },
    );

    let non_fail_closed_rows: Vec<String> = rows
        .iter()
        .filter(|row| row.get("fail_closed").and_then(serde_json::Value::as_bool) != Some(true))
        .filter_map(|row| row.get("id").and_then(serde_json::Value::as_str))
        .map(str::to_owned)
        .collect();
    push_report_validation_check(
        checks,
        failures,
        "frontend-all-rows-fail-closed",
        non_fail_closed_rows.is_empty(),
        if non_fail_closed_rows.is_empty() {
            "all frontend scorecard rows mark fail_closed=true".to_owned()
        } else {
            format!("rows not fail-closed: {}", non_fail_closed_rows.join(", "))
        },
    );

    let corpus_files = json_u64_at(
        value,
        &["summary", "frontend_corpus_classification_entries"],
    );
    let phase1_files = json_u64_at(value, &["summary", "phase1_manifest_entries"]);
    let elab_files = json_u64_at(value, &["summary", "phase1_elab_entries"]);
    let parse_only_files = json_u64_at(value, &["summary", "phase1_parse_only_entries"]);
    let kernel_slice_files = json_u64_at(value, &["summary", "frontend_slice_elab_entries"]);
    push_report_validation_check(
        checks,
        failures,
        "frontend-corpus-accounting",
        corpus_files > 0
            && phase1_files > 0
            && phase1_files == elab_files + parse_only_files
            && kernel_slice_files > 0
            && kernel_slice_files <= elab_files,
        format!(
            "corpus={corpus_files}, phase1={phase1_files}, elab={elab_files}, parse_only={parse_only_files}, kernel_slice={kernel_slice_files}"
        ),
    );

    let kernel_row = row_value_by_id(&rows, "frontend-slice-parse-elab-kernel");
    push_report_validation_check(
        checks,
        failures,
        "frontend-bounded-kernel-slice",
        kernel_row
            .and_then(|row| row.get("status"))
            .and_then(serde_json::Value::as_str)
            == Some("bounded_slice_pass")
            && kernel_row
                .and_then(|row| row.get("observed_pass"))
                .and_then(serde_json::Value::as_u64)
                == Some(kernel_slice_files)
            && kernel_row
                .and_then(|row| row.get("observed_total"))
                .and_then(serde_json::Value::as_u64)
                == Some(kernel_slice_files),
        format!("kernel slice row should pass exactly {kernel_slice_files} bounded entries"),
    );

    let run_row = row_value_by_id(&rows, "lean4-vs-clean-run-artifact-guard");
    let valid_run_artifacts = run_row
        .and_then(|row| row.get("observed_elab_valid_run_artifacts"))
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    let missing_run_artifacts = run_row
        .and_then(|row| row.get("observed_elab_missing_run_artifacts"))
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    push_report_validation_check(
        checks,
        failures,
        "frontend-run-artifact-gate-partial",
        run_row
            .and_then(|row| row.get("status"))
            .and_then(serde_json::Value::as_str)
            == Some("partial_differential_artifacts")
            && valid_run_artifacts > 0
            && run_row
                .and_then(|row| row.get("observed_replacement_ready_rows"))
                .and_then(serde_json::Value::as_u64)
                == Some(0),
        format!(
            "valid_run_artifacts={valid_run_artifacts}, missing_run_artifacts={missing_run_artifacts}"
        ),
    );

    push_report_validation_check(
        checks,
        failures,
        "frontend-classification-source",
        rows.iter().all(|row| {
            row.get("evidence")
                .and_then(serde_json::Value::as_array)
                .is_some_and(|evidence_items| {
                    evidence_items.iter().any(|evidence| {
                        evidence.get("path").and_then(serde_json::Value::as_str)
                            == Some("tests/lean4_compat/frontend_corpus_classification.json")
                    })
                })
        }),
        "every frontend row should cite tests/lean4_compat/frontend_corpus_classification.json"
            .to_owned(),
    );
}
