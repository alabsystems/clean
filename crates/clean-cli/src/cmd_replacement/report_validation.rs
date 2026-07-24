// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Replacement report validation core.

use super::*;

impl ReplacementReportValidation {
    pub(crate) fn from_args(args: &ValidateReportArgs) -> Result<Self, ReplacementError> {
        let report_path = args.report.display().to_string();
        let raw =
            fs::read_to_string(&args.report).map_err(|source| ReplacementError::ReadReport {
                path: report_path.clone(),
                source,
            })?;
        let value: serde_json::Value =
            serde_json::from_str(&raw).map_err(|source| ReplacementError::ParseReport {
                path: report_path.clone(),
                source,
            })?;

        let mut checks = Vec::new();
        let mut failures = Vec::new();
        let kind = args.kind;

        let report_schema_version = value
            .get("schema_version")
            .and_then(serde_json::Value::as_str)
            .unwrap_or_default()
            .to_owned();
        push_report_validation_check(
            &mut checks,
            &mut failures,
            "schema-version",
            report_schema_version == kind.expected_schema(),
            format!(
                "expected {}, observed {}",
                kind.expected_schema(),
                missing_string(&report_schema_version)
            ),
        );

        let artifact_status = value
            .get(kind.status_field())
            .and_then(serde_json::Value::as_str)
            .unwrap_or_default()
            .to_owned();
        push_report_validation_check(
            &mut checks,
            &mut failures,
            "artifact-status",
            artifact_status == kind.expected_status(),
            format!(
                "expected {}={}, observed {}",
                kind.status_field(),
                kind.expected_status(),
                missing_string(&artifact_status)
            ),
        );

        let replacement_row_value = value.get("replacement_row");
        let replacement_row = ReplacementReportRowValidation {
            id: replacement_row_value
                .and_then(|row| row.get("id"))
                .and_then(serde_json::Value::as_str)
                .unwrap_or_default()
                .to_owned(),
            issue: replacement_row_value
                .and_then(|row| row.get("issue"))
                .and_then(serde_json::Value::as_u64)
                .unwrap_or_default(),
            expected_by_scorecard: replacement_row_value
                .and_then(|row| row.get("expected_by_scorecard"))
                .and_then(serde_json::Value::as_bool)
                .unwrap_or(false),
            recommended_scorecard_status: replacement_row_value
                .and_then(|row| row.get("recommended_scorecard_status"))
                .and_then(serde_json::Value::as_str)
                .unwrap_or_default()
                .to_owned(),
        };
        push_report_validation_check(
            &mut checks,
            &mut failures,
            "replacement-row",
            replacement_row.id == kind.replacement_row_id()
                && replacement_row.issue == kind.issue()
                && replacement_row.expected_by_scorecard
                && replacement_row.recommended_scorecard_status == kind.expected_status(),
            format!(
                "expected row {} issue #{} status {}; observed row {} issue #{} status {} expected_by_scorecard={}",
                kind.replacement_row_id(),
                kind.issue(),
                kind.expected_status(),
                missing_string(&replacement_row.id),
                replacement_row.issue,
                missing_string(&replacement_row.recommended_scorecard_status),
                replacement_row.expected_by_scorecard,
            ),
        );

        let rows = value
            .get("rows")
            .and_then(serde_json::Value::as_array)
            .cloned()
            .unwrap_or_default();
        let row_count = rows.len();
        let mut seen_row_ids = std::collections::BTreeSet::new();
        let mut duplicate_row_ids = Vec::new();
        let mut evidence_row_count = 0usize;
        for row in &rows {
            if let Some(id) = row.get("id").and_then(serde_json::Value::as_str) {
                if !seen_row_ids.insert(id.to_owned()) {
                    duplicate_row_ids.push(id.to_owned());
                }
            }
            if row
                .get("evidence")
                .and_then(serde_json::Value::as_array)
                .is_some_and(|evidence| !evidence.is_empty())
            {
                evidence_row_count += 1;
            }
        }
        push_report_validation_check(
            &mut checks,
            &mut failures,
            "rows-present",
            row_count > 0,
            format!("{row_count} row(s) found"),
        );
        push_report_validation_check(
            &mut checks,
            &mut failures,
            "row-ids-unique",
            duplicate_row_ids.is_empty(),
            if duplicate_row_ids.is_empty() {
                "all row ids are unique".to_owned()
            } else {
                format!("duplicate row ids: {}", duplicate_row_ids.join(", "))
            },
        );
        push_report_validation_check(
            &mut checks,
            &mut failures,
            "rows-have-evidence",
            row_count > 0 && evidence_row_count == row_count,
            format!("{evidence_row_count}/{row_count} rows carry evidence"),
        );

        if let Some(summary_count) = value
            .get("summary")
            .and_then(|summary| summary.get("row_count"))
            .and_then(serde_json::Value::as_u64)
        {
            push_report_validation_check(
                &mut checks,
                &mut failures,
                "summary-row-count",
                summary_count as usize == row_count,
                format!("summary row_count={summary_count}, actual rows={row_count}"),
            );
        }

        let non_claims = value
            .get("non_claims")
            .and_then(serde_json::Value::as_array)
            .cloned()
            .unwrap_or_default();
        let overall_blockers = value
            .get("overall_blockers")
            .and_then(serde_json::Value::as_array)
            .cloned()
            .unwrap_or_default();
        push_report_validation_check(
            &mut checks,
            &mut failures,
            "non-claims-present",
            !non_claims.is_empty(),
            format!("{} non-claim(s) found", non_claims.len()),
        );
        push_report_validation_check(
            &mut checks,
            &mut failures,
            "blockers-present",
            !overall_blockers.is_empty(),
            format!("{} overall blocker(s) found", overall_blockers.len()),
        );

        let launch_ready_claimed = report_claims_launch_readiness(&value);
        push_report_validation_check(
            &mut checks,
            &mut failures,
            "no-launch-ready-claim",
            !launch_ready_claimed,
            "artifact must not claim replacement launch readiness while row is non-green"
                .to_owned(),
        );

        match kind {
            ReplacementReportKind::NativeLibrary => {
                validate_native_library_report(&value, &mut checks, &mut failures)
            }
            ReplacementReportKind::MathverseReplay => {
                validate_mathverse_replay_report(&value, &mut checks, &mut failures)
            }
            ReplacementReportKind::LspInfoview => {
                validate_lsp_infoview_report(&value, &mut checks, &mut failures)
            }
            ReplacementReportKind::FrontendParity => {
                validate_frontend_parity_report(&value, &mut checks, &mut failures)
            }
        }

        let validation_passed = failures.is_empty();
        Ok(Self {
            schema_version: REPORT_VALIDATION_SCHEMA_VERSION,
            generated_by: "clean replacement validate-report",
            report_kind: kind,
            report_path,
            report_schema_version,
            artifact_status,
            replacement_row,
            validation_passed,
            validation_status: if validation_passed {
                "valid_fail_closed"
            } else {
                "invalid"
            },
            launch_ready_claimed,
            row_count,
            evidence_row_count,
            blocker_count: overall_blockers.len(),
            checks,
            failures,
        })
    }
}

pub(crate) fn push_report_validation_check(
    checks: &mut Vec<ReplacementReportValidationCheck>,
    failures: &mut Vec<String>,
    id: &'static str,
    passed: bool,
    detail: String,
) {
    if !passed {
        failures.push(format!("{id}: {detail}"));
    }
    checks.push(ReplacementReportValidationCheck {
        id,
        status: if passed {
            ReplacementReportValidationCheckStatus::Pass
        } else {
            ReplacementReportValidationCheckStatus::Fail
        },
        detail,
    });
}

pub(crate) fn missing_string(value: &str) -> &str {
    if value.is_empty() {
        "<missing>"
    } else {
        value
    }
}

pub(crate) fn string_array_contains(
    value: &serde_json::Value,
    path: &[&str],
    expected: &str,
) -> bool {
    let mut cursor = value;
    for key in path {
        cursor = match cursor.get(*key) {
            Some(next) => next,
            None => return false,
        };
    }
    cursor
        .as_array()
        .is_some_and(|items| items.iter().any(|item| item.as_str() == Some(expected)))
}

pub(crate) fn row_value_by_id<'a>(
    rows: &'a [serde_json::Value],
    row_id: &str,
) -> Option<&'a serde_json::Value> {
    rows.iter()
        .find(|row| row.get("id").and_then(serde_json::Value::as_str) == Some(row_id))
}

pub(crate) fn report_claims_launch_readiness(value: &serde_json::Value) -> bool {
    value
        .get("launch_ready")
        .and_then(serde_json::Value::as_bool)
        .unwrap_or(false)
        || value
            .get("replacement_row")
            .and_then(|row| row.get("recommended_scorecard_status"))
            .and_then(serde_json::Value::as_str)
            == Some("green")
}
