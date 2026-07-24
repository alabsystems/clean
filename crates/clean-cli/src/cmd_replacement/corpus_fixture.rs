// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Full-corpus fixture generation and validation.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityFullCorpusFixtureGeneration {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) output_path: String,
    pub(crate) artifact_schema_version: &'static str,
    pub(crate) coverage_claimed: bool,
    pub(crate) launch_readiness_claimed: bool,
    pub(crate) validation: TacticParityFullCorpusValidation,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityFullCorpusFixtureArtifact {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) source_corpus: &'static str,
    pub(crate) full_lean4_corpus_coverage_claimed: bool,
    pub(crate) launch_readiness_claimed: bool,
    pub(crate) summary: TacticParityFullCorpusFixtureSummary,
    pub(crate) tactics: Vec<serde_json::Value>,
    pub(crate) blockers: Vec<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityFullCorpusFixtureSummary {
    pub(crate) enumerated_fixture_total: u32,
    pub(crate) matched_fixture_total: u32,
    pub(crate) clean_gap_total: u32,
    pub(crate) reviewed_blocker_total: u32,
    pub(crate) unreviewed_blocker_total: u32,
}

impl TacticParityFullCorpusFixtureGeneration {
    pub(crate) fn write_to_path(output: &Path) -> Result<Self, ReplacementError> {
        let artifact = TacticParityFullCorpusFixtureArtifact {
            schema_version: TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED,
            generated_by: "clean replacement tactic-parity generate-full-corpus-fixture",
            source_corpus: "generated schema fixture only; not full Lean4 tactic corpus evidence",
            full_lean4_corpus_coverage_claimed: false,
            launch_readiness_claimed: false,
            summary: TacticParityFullCorpusFixtureSummary {
                enumerated_fixture_total: 0,
                matched_fixture_total: 0,
                clean_gap_total: 0,
                reviewed_blocker_total: 0,
                unreviewed_blocker_total: 0,
            },
            tactics: Vec::new(),
            blockers: Vec::new(),
        };
        write_json_path(output, &artifact)?;
        let validation = TacticParityFullCorpusValidation::from_report_path(output);

        Ok(Self {
            schema_version: "clean-tactic-parity-full-corpus-fixture-generation-v1",
            generated_by: "clean replacement tactic-parity generate-full-corpus-fixture",
            output_path: output.display().to_string(),
            artifact_schema_version: TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED,
            coverage_claimed: artifact.full_lean4_corpus_coverage_claimed,
            launch_readiness_claimed: artifact.launch_readiness_claimed,
            validation,
        })
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityFullCorpusValidation {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) report_path: String,
    pub(crate) artifact_present: bool,
    pub(crate) report_schema_version: Option<String>,
    pub(crate) tactic_outcome_row_count: usize,
    pub(crate) blocker_row_count: usize,
    pub(crate) contains_tactic_outcome_evidence: bool,
    pub(crate) corpus_manifest_present: bool,
    pub(crate) corpus_manifest_valid: bool,
    pub(crate) reviewer_evidence_present: bool,
    pub(crate) reviewer_evidence_valid: bool,
    pub(crate) reviewer_evidence_provenance_valid: bool,
    pub(crate) schema_fixture_only: bool,
    pub(crate) acceptance_evidence_candidate: bool,
    pub(crate) missing_acceptance_requirements: Vec<String>,
    pub(crate) validation_passed: bool,
    pub(crate) validation_status: &'static str,
    pub(crate) check_count: usize,
    pub(crate) passed_count: usize,
    pub(crate) required_fields: Vec<&'static str>,
    pub(crate) checks: Vec<ReplacementReportValidationCheck>,
    pub(crate) failures: Vec<String>,
}

impl TacticParityFullCorpusValidation {
    pub(crate) fn from_report_path(report: &Path) -> Self {
        let report_path = report.display().to_string();
        let mut checks = Vec::new();
        let mut failures = Vec::new();
        let mut value = None;
        let mut report_schema_version = None;
        let mut tactic_outcome_row_count = 0usize;
        let mut blocker_row_count = 0usize;
        let mut corpus_manifest_present = false;
        let mut corpus_manifest_valid = false;
        let mut reviewer_evidence_present = false;
        let mut reviewer_evidence_valid = false;
        let mut reviewer_evidence_provenance_valid = false;

        match fs::read_to_string(report) {
            Ok(raw) => {
                push_report_validation_check(
                    &mut checks,
                    &mut failures,
                    "artifact-readable",
                    true,
                    format!("read {report_path}"),
                );
                match serde_json::from_str::<serde_json::Value>(&raw) {
                    Ok(parsed) => value = Some(parsed),
                    Err(error) => push_report_validation_check(
                        &mut checks,
                        &mut failures,
                        "artifact-json",
                        false,
                        format!("failed to parse {report_path}: {error}"),
                    ),
                }
            }
            Err(error) => push_report_validation_check(
                &mut checks,
                &mut failures,
                "artifact-readable",
                false,
                format!("failed to read {report_path}: {error}"),
            ),
        }

        if let Some(value) = &value {
            report_schema_version = value
                .get("schema_version")
                .and_then(serde_json::Value::as_str)
                .map(ToOwned::to_owned);
            push_report_validation_check(
                &mut checks,
                &mut failures,
                "schema-version",
                report_schema_version.as_deref()
                    == Some(TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED),
                format!(
                    "expected {}, observed {}",
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED,
                    report_schema_version.as_deref().unwrap_or("<missing>")
                ),
            );

            let missing_fields: Vec<&str> = TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS
                .iter()
                .copied()
                .filter(|field| value.get(*field).is_none())
                .collect();
            push_report_validation_check(
                &mut checks,
                &mut failures,
                "required-fields",
                missing_fields.is_empty(),
                if missing_fields.is_empty() {
                    "all required full-corpus artifact fields are present".to_owned()
                } else {
                    format!("missing fields: {}", missing_fields.join(", "))
                },
            );

            let tactic_rows = value.get("tactics").and_then(serde_json::Value::as_array);
            tactic_outcome_row_count = tactic_rows.map_or(0, Vec::len);
            let missing_tactic_outcome_fields: Vec<String> = tactic_rows
                .into_iter()
                .flatten()
                .enumerate()
                .flat_map(|(index, row)| {
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS
                        .iter()
                        .copied()
                        .filter(move |field| row.get(*field).is_none())
                        .map(move |field| format!("tactics[{index}].{field}"))
                })
                .collect();
            push_report_validation_check(
                &mut checks,
                &mut failures,
                "tactic-outcome-fields",
                missing_tactic_outcome_fields.is_empty(),
                if missing_tactic_outcome_fields.is_empty() {
                    format!(
                        "{} tactic outcome rows satisfy the Lean4-vs-clean row field contract",
                        tactic_outcome_row_count
                    )
                } else {
                    format!(
                        "missing tactic outcome fields: {}",
                        missing_tactic_outcome_fields.join(", ")
                    )
                },
            );

            blocker_row_count = value
                .get("blockers")
                .and_then(serde_json::Value::as_array)
                .map_or(0, Vec::len);

            if tactic_outcome_row_count > 0 {
                let manifest = value.get("corpus_manifest");
                corpus_manifest_present = manifest.is_some();
                let missing_manifest_fields: Vec<&str> = manifest
                    .filter(|manifest| manifest.is_object())
                    .map(|manifest| {
                        TACTIC_FULL_CORPUS_ACCEPTANCE_MANIFEST_REQUIRED_FIELDS
                            .iter()
                            .copied()
                            .filter(|field| manifest.get(*field).is_none())
                            .collect()
                    })
                    .unwrap_or_else(|| {
                        TACTIC_FULL_CORPUS_ACCEPTANCE_MANIFEST_REQUIRED_FIELDS.to_vec()
                    });
                corpus_manifest_valid = missing_manifest_fields.is_empty();
                push_report_validation_check(
                    &mut checks,
                    &mut failures,
                    "corpus-manifest",
                    corpus_manifest_valid,
                    if corpus_manifest_valid {
                        "full-corpus tactic outcome rows have a corpus_manifest contract".to_owned()
                    } else {
                        format!(
                            "missing corpus_manifest fields: {}",
                            missing_manifest_fields.join(", ")
                        )
                    },
                );

                let reviewer_evidence = value.get("reviewer_evidence");
                reviewer_evidence_present = reviewer_evidence.is_some();
                let missing_reviewer_fields: Vec<&str> = reviewer_evidence
                    .filter(|reviewer_evidence| reviewer_evidence.is_object())
                    .map(|reviewer_evidence| {
                        TACTIC_FULL_CORPUS_ACCEPTANCE_REVIEWER_EVIDENCE_REQUIRED_FIELDS
                            .iter()
                            .copied()
                            .filter(|field| reviewer_evidence.get(*field).is_none())
                            .collect()
                    })
                    .unwrap_or_else(|| {
                        TACTIC_FULL_CORPUS_ACCEPTANCE_REVIEWER_EVIDENCE_REQUIRED_FIELDS.to_vec()
                    });
                reviewer_evidence_valid = missing_reviewer_fields.is_empty();
                push_report_validation_check(
                    &mut checks,
                    &mut failures,
                    "reviewer-evidence",
                    reviewer_evidence_valid,
                    if reviewer_evidence_valid {
                        "full-corpus tactic outcome rows have reviewer_evidence".to_owned()
                    } else {
                        format!(
                            "missing reviewer_evidence fields: {}",
                            missing_reviewer_fields.join(", ")
                        )
                    },
                );

                if corpus_manifest_valid && reviewer_evidence_valid {
                    let manifest = manifest.expect("validated corpus_manifest exists");
                    let reviewer_evidence =
                        reviewer_evidence.expect("validated reviewer_evidence exists");
                    let manifest_id = manifest
                        .get("manifest_id")
                        .and_then(serde_json::Value::as_str);
                    let manifest_digest = manifest
                        .get("source_digest_sha256")
                        .and_then(serde_json::Value::as_str);
                    let reviewed_manifest_id = reviewer_evidence
                        .get("manifest_id")
                        .and_then(serde_json::Value::as_str);
                    let reviewed_digest = reviewer_evidence
                        .get("source_digest_sha256")
                        .and_then(serde_json::Value::as_str);
                    reviewer_evidence_provenance_valid = manifest_id == reviewed_manifest_id
                        && manifest_digest == reviewed_digest
                        && manifest_id.is_some()
                        && manifest_digest.is_some();
                    push_report_validation_check(
                        &mut checks,
                        &mut failures,
                        "reviewer-evidence-provenance",
                        reviewer_evidence_provenance_valid,
                        if reviewer_evidence_provenance_valid {
                            "reviewer_evidence references the validated corpus_manifest provenance"
                                .to_owned()
                        } else {
                            format!(
                                "reviewer_evidence provenance mismatch: manifest_id={:?}, reviewed_manifest_id={:?}, source_digest_sha256={:?}, reviewed_source_digest_sha256={:?}",
                                manifest_id,
                                reviewed_manifest_id,
                                manifest_digest,
                                reviewed_digest
                            )
                        },
                    );
                }
            }

            let overclaim = value
                .get("full_lean4_corpus_coverage_claimed")
                .and_then(serde_json::Value::as_bool)
                .unwrap_or(false)
                || value
                    .get("launch_readiness_claimed")
                    .and_then(serde_json::Value::as_bool)
                    .unwrap_or(false);
            push_report_validation_check(
                &mut checks,
                &mut failures,
                "no-launch-overclaim",
                !overclaim,
                "full-corpus validation artifact must not claim launch readiness by itself"
                    .to_owned(),
            );
        }

        let validation_passed = failures.is_empty();
        let contains_tactic_outcome_evidence = tactic_outcome_row_count
            >= TACTIC_FULL_CORPUS_ACCEPTANCE_MINIMUM_TACTIC_OUTCOME_ROWS as usize;
        let schema_fixture_only =
            value.is_some() && validation_passed && !contains_tactic_outcome_evidence;
        let acceptance_evidence_candidate = validation_passed
            && contains_tactic_outcome_evidence
            && corpus_manifest_valid
            && reviewer_evidence_valid
            && reviewer_evidence_provenance_valid
            && !schema_fixture_only;
        let missing_acceptance_requirements = tactic_full_corpus_missing_acceptance_requirements(
            value.is_some(),
            report_schema_version.as_deref(),
            contains_tactic_outcome_evidence,
            corpus_manifest_valid,
            reviewer_evidence_valid,
            reviewer_evidence_provenance_valid,
            schema_fixture_only,
            acceptance_evidence_candidate,
        );
        let passed_count = checks
            .iter()
            .filter(|check| check.status == ReplacementReportValidationCheckStatus::Pass)
            .count();
        Self {
            schema_version: "clean-tactic-parity-full-corpus-validation-v1",
            generated_by: "clean replacement tactic-parity validate-full-corpus",
            report_path,
            artifact_present: value.is_some(),
            report_schema_version,
            tactic_outcome_row_count,
            blocker_row_count,
            contains_tactic_outcome_evidence,
            corpus_manifest_present,
            corpus_manifest_valid,
            reviewer_evidence_present,
            reviewer_evidence_valid,
            reviewer_evidence_provenance_valid,
            schema_fixture_only,
            acceptance_evidence_candidate,
            missing_acceptance_requirements,
            validation_passed,
            validation_status: if validation_passed {
                "valid_fail_closed"
            } else {
                "invalid"
            },
            check_count: checks.len(),
            passed_count,
            required_fields: TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS.to_vec(),
            checks,
            failures,
        }
    }
}

pub(crate) fn tactic_full_corpus_missing_acceptance_requirements(
    artifact_present: bool,
    report_schema_version: Option<&str>,
    contains_tactic_outcome_evidence: bool,
    corpus_manifest_valid: bool,
    reviewer_evidence_valid: bool,
    reviewer_evidence_provenance_valid: bool,
    schema_fixture_only: bool,
    acceptance_evidence_candidate: bool,
) -> Vec<String> {
    if acceptance_evidence_candidate {
        return Vec::new();
    }

    let mut requirements = Vec::new();
    if !artifact_present {
        requirements.push(format!(
            "submit readable {}",
            TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED
        ));
    }
    if report_schema_version != Some(TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED) {
        requirements.push(format!(
            "use schema_version {}",
            TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED
        ));
    }
    if schema_fixture_only {
        requirements.push(
            "replace generated schema fixture with real Lean4-vs-clean tactic outcome rows"
                .to_owned(),
        );
    }
    if !contains_tactic_outcome_evidence {
        requirements.push(format!(
            "include at least {} tactics[] Lean4-vs-clean outcome row",
            TACTIC_FULL_CORPUS_ACCEPTANCE_MINIMUM_TACTIC_OUTCOME_ROWS
        ));
    }
    if contains_tactic_outcome_evidence && !corpus_manifest_valid {
        requirements.push(format!(
            "include corpus_manifest fields: {}",
            TACTIC_FULL_CORPUS_ACCEPTANCE_MANIFEST_REQUIRED_FIELDS.join(", ")
        ));
    }
    if contains_tactic_outcome_evidence && !reviewer_evidence_valid {
        requirements.push(format!(
            "include reviewer_evidence fields: {}",
            TACTIC_FULL_CORPUS_ACCEPTANCE_REVIEWER_EVIDENCE_REQUIRED_FIELDS.join(", ")
        ));
    }
    if contains_tactic_outcome_evidence
        && corpus_manifest_valid
        && reviewer_evidence_valid
        && !reviewer_evidence_provenance_valid
    {
        requirements.push(
            "make reviewer_evidence manifest_id and source_digest_sha256 match corpus_manifest"
                .to_owned(),
        );
    }
    requirements
}
