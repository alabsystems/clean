// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic parity count artifact and generated-case backing checks.

use super::*;

impl TacticParityCountArtifact {
    pub(crate) fn current(
        tactic_rows: &[TacticParityRow],
        dashboard: &StrictSolverFragmentDashboard,
    ) -> Self {
        let tactics: Vec<_> = tactic_rows.iter().filter_map(tactic_count_row).collect();
        let summary = TacticParityCountSummary::from_rows(&tactics);
        let strict_solver_fragments = StrictSolverFragmentCountSummary::from_dashboard(dashboard);

        Self {
            schema_version: TACTIC_PARITY_COUNT_ARTIFACT_SCHEMA_VERSION,
            status: "ready",
            generated_by: "clean replacement tactic-parity --json",
            source_artifact: TACTIC_PARITY_COUNT_ARTIFACT_PATH,
            reproduction_command:
                "clean replacement tactic-parity --json | jq '.lean4_vs_clean_tactic_counts'",
            corpus: "checked-in representative replacement tactic count corpus for issue #3711",
            coverage_scope: "representative-generated-cases-only",
            full_lean4_corpus_coverage_claimed: false,
            launch_readiness_claimed: false,
            remaining_substantive_replacement_blocker:
                "All status-bearing tactic rows have generated representative backing; substantive Lean4 tactic replacement still requires broader Lean4 corpus parity coverage beyond representative generated cases.",
            full_corpus_acceptance_gate: TACTIC_FULL_CORPUS_ACCEPTANCE_GATE,
            representative_generated_backing_satisfies_full_corpus_acceptance: false,
            full_corpus_acceptance_evidence_status:
                TACTIC_FULL_CORPUS_ACCEPTANCE_EVIDENCE_STATUS,
            full_corpus_acceptance_artifact_required:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED,
            full_corpus_acceptance_artifact_present: false,
            full_corpus_acceptance_artifact_schema_required:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED,
            full_corpus_acceptance_artifact_schema_validated: false,
            full_corpus_acceptance_validator_required:
                TACTIC_FULL_CORPUS_ACCEPTANCE_VALIDATOR_REQUIRED,
            full_corpus_acceptance_validator_present: false,
            full_corpus_input_discovery_command: TACTIC_FULL_CORPUS_INPUT_DISCOVERY_COMMAND,
            full_corpus_fixture_generator_command: TACTIC_FULL_CORPUS_FIXTURE_GENERATOR_COMMAND,
            full_corpus_fixture_counts_as_acceptance_evidence: false,
            full_corpus_fixture_acceptance_blocker:
                TACTIC_FULL_CORPUS_FIXTURE_ACCEPTANCE_BLOCKER,
            full_corpus_acceptance_minimum_tactic_outcome_rows:
                TACTIC_FULL_CORPUS_ACCEPTANCE_MINIMUM_TACTIC_OUTCOME_ROWS,
            full_corpus_acceptance_tactic_outcome_row_contract:
                TACTIC_FULL_CORPUS_ACCEPTANCE_TACTIC_OUTCOME_ROW_CONTRACT,
            full_corpus_acceptance_manifest_required_fields:
                TACTIC_FULL_CORPUS_ACCEPTANCE_MANIFEST_REQUIRED_FIELDS.to_vec(),
            full_corpus_acceptance_reviewer_evidence_required_fields:
                TACTIC_FULL_CORPUS_ACCEPTANCE_REVIEWER_EVIDENCE_REQUIRED_FIELDS.to_vec(),
            full_corpus_acceptance_artifact_required_fields:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS.to_vec(),
            full_corpus_acceptance_artifact_required_fields_fingerprint_algorithm:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS_FINGERPRINT_ALGORITHM,
            full_corpus_acceptance_artifact_required_fields_fingerprint_sha256:
                tactic_full_corpus_list_fingerprint(
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS,
                ),
            full_corpus_acceptance_artifact_required_summary_fields:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_SUMMARY_FIELDS.to_vec(),
            full_corpus_acceptance_artifact_required_summary_fields_fingerprint_algorithm:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_SUMMARY_FIELDS_FINGERPRINT_ALGORITHM,
            full_corpus_acceptance_artifact_required_summary_fields_fingerprint_sha256:
                tactic_full_corpus_list_fingerprint(
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_SUMMARY_FIELDS,
                ),
            full_corpus_acceptance_artifact_required_tactic_fields:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS.to_vec(),
            full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_algorithm:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS_FINGERPRINT_ALGORITHM,
            full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_sha256:
                tactic_full_corpus_list_fingerprint(
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS,
                ),
            full_corpus_acceptance_artifact_required_evidence_fields:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_EVIDENCE_FIELDS.to_vec(),
            full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_algorithm:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_EVIDENCE_FIELDS_FINGERPRINT_ALGORITHM,
            full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_sha256:
                tactic_full_corpus_list_fingerprint(
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_EVIDENCE_FIELDS,
                ),
            full_corpus_acceptance_artifact_required_blocker_fields:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_BLOCKER_FIELDS.to_vec(),
            full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_algorithm:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_BLOCKER_FIELDS_FINGERPRINT_ALGORITHM,
            full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_sha256:
                tactic_full_corpus_list_fingerprint(
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_BLOCKER_FIELDS,
                ),
            full_corpus_acceptance_artifact_required_invariants:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_INVARIANTS.to_vec(),
            full_corpus_acceptance_artifact_required_invariants_fingerprint_algorithm:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_INVARIANTS_FINGERPRINT_ALGORITHM,
            full_corpus_acceptance_artifact_required_invariants_fingerprint_sha256:
                tactic_full_corpus_list_fingerprint(
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_INVARIANTS,
                ),
            full_corpus_acceptance_artifact_allowed_evidence_kinds:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_ALLOWED_EVIDENCE_KINDS.to_vec(),
            full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_algorithm:
                TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_ALLOWED_EVIDENCE_KINDS_FINGERPRINT_ALGORITHM,
            full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_sha256:
                tactic_full_corpus_list_fingerprint(
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_ALLOWED_EVIDENCE_KINDS,
                ),
            full_corpus_acceptance_criteria_required:
                TACTIC_FULL_CORPUS_ACCEPTANCE_CRITERIA_REQUIRED.to_vec(),
            full_corpus_acceptance_criteria_fingerprint_algorithm:
                TACTIC_FULL_CORPUS_ACCEPTANCE_CRITERIA_FINGERPRINT_ALGORITHM,
            full_corpus_acceptance_criteria_fingerprint_sha256:
                tactic_full_corpus_list_fingerprint(
                    TACTIC_FULL_CORPUS_ACCEPTANCE_CRITERIA_REQUIRED,
                ),
            full_corpus_reviewer_evidence_required:
                TACTIC_FULL_CORPUS_REVIEWER_EVIDENCE_REQUIRED.to_vec(),
            full_corpus_reviewer_evidence_fingerprint_algorithm:
                TACTIC_FULL_CORPUS_REVIEWER_EVIDENCE_FINGERPRINT_ALGORITHM,
            full_corpus_reviewer_evidence_fingerprint_sha256:
                tactic_full_corpus_list_fingerprint(
                    TACTIC_FULL_CORPUS_REVIEWER_EVIDENCE_REQUIRED,
                ),
            summary,
            tactics,
            strict_solver_fragments,
        }
    }
}

pub(crate) fn tactic_full_corpus_list_fingerprint(items: &[&str]) -> String {
    let mut hasher = Sha256::new();
    for item in items {
        hasher.update(item.as_bytes());
        hasher.update(b"\n");
    }
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}

pub(crate) fn validate_generated_tactic_case_backing(
    artifact: &TacticParityCountArtifact,
) -> Result<(), Vec<String>> {
    let mut failures = Vec::new();
    const GENERATED_BACKED_PROOF_CARRYING_TACTICS: &[&str] = &[
        "simp",
        "rw",
        "exact",
        "mathverse",
        "linarith",
        "nlinarith",
        "aesop",
        "grind",
    ];

    for row in &artifact.tactics {
        if row.status == TacticParityStatus::ProofCarrying && row.clean_gap_count != 0 {
            failures.push(format!(
                "{} is ProofCarrying but has clean_gap_count={}",
                row.tactic, row.clean_gap_count
            ));
        }

        let Some(generated_cases) = &row.generated_cases else {
            if GENERATED_BACKED_PROOF_CARRYING_TACTICS.contains(&row.tactic) {
                failures.push(format!(
                    "{} is generated-backed but has no generated_cases section",
                    row.tactic
                ));
            }
            continue;
        };

        let case_count = generated_cases.cases.len() as u32;
        let matched_case_count = generated_cases
            .cases
            .iter()
            .filter(|case| case.matched)
            .count() as u32;
        let expected_gap_count = case_count.saturating_sub(matched_case_count);
        let expected_fail_closed = case_count == matched_case_count;

        if generated_cases.case_count != case_count {
            failures.push(format!(
                "{} generated case_count={} does not match listed cases={}",
                row.tactic, generated_cases.case_count, case_count
            ));
        }
        if generated_cases.matched_case_count != matched_case_count {
            failures.push(format!(
                "{} generated matched_case_count={} does not match matched cases={}",
                row.tactic, generated_cases.matched_case_count, matched_case_count
            ));
        }
        if generated_cases.fail_closed != expected_fail_closed {
            failures.push(format!(
                "{} generated fail_closed={} does not match matched coverage={}",
                row.tactic, generated_cases.fail_closed, expected_fail_closed
            ));
        }
        if row.lean4_count != case_count {
            failures.push(format!(
                "{} lean4_count={} does not match generated case_count={}",
                row.tactic, row.lean4_count, case_count
            ));
        }
        if row.clean_count != matched_case_count {
            failures.push(format!(
                "{} clean_count={} does not match generated matched_case_count={}",
                row.tactic, row.clean_count, matched_case_count
            ));
        }
        if row.matched_count != matched_case_count {
            failures.push(format!(
                "{} matched_count={} does not match generated matched_case_count={}",
                row.tactic, row.matched_count, matched_case_count
            ));
        }
        if row.clean_gap_count != expected_gap_count {
            failures.push(format!(
                "{} clean_gap_count={} does not match generated gap count={}",
                row.tactic, row.clean_gap_count, expected_gap_count
            ));
        }
        if row.status == TacticParityStatus::ProofCarrying && !generated_cases.fail_closed {
            failures.push(format!(
                "{} is ProofCarrying but generated cases are not fail-closed",
                row.tactic
            ));
        }

        for case in &generated_cases.cases {
            if !case.case_id.starts_with(row.tactic) {
                failures.push(format!(
                    "{} generated case_id={} does not use tactic prefix",
                    row.tactic, case.case_id
                ));
            }
            let expected_lean4_fixture = format!("generated:lean4-{}-representative", row.tactic);
            if case.lean4_fixture != expected_lean4_fixture {
                failures.push(format!(
                    "{} generated case {} has lean4_fixture={}",
                    row.tactic, case.case_id, case.lean4_fixture
                ));
            }
            let expected_clean_fixture = format!("generated:clean-{}-representative", row.tactic);
            if case.clean_fixture != expected_clean_fixture {
                failures.push(format!(
                    "{} generated case {} has clean_fixture={}",
                    row.tactic, case.case_id, case.clean_fixture
                ));
            }
            if case.evidence.trim().is_empty() {
                failures.push(format!(
                    "{} generated case {} has empty evidence",
                    row.tactic, case.case_id
                ));
            }
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures)
    }
}
