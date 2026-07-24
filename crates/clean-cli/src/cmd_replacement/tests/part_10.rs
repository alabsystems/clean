// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 10) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use super::support::*;
use crate::cmd_replacement::*;

#[test]
fn tactic_parity_report_includes_generated_lean4_vs_clean_tactic_counts() {
    let report = TacticParityReport::current();
    let artifact = &report.lean4_vs_clean_tactic_counts;

    assert_eq!(
        artifact.schema_version,
        TACTIC_PARITY_COUNT_ARTIFACT_SCHEMA_VERSION
    );
    assert_eq!(artifact.source_artifact, TACTIC_PARITY_COUNT_ARTIFACT_PATH);
    assert_eq!(
        artifact.coverage_scope,
        "representative-generated-cases-only"
    );
    assert!(!artifact.full_lean4_corpus_coverage_claimed);
    assert!(!artifact.launch_readiness_claimed);
    assert!(artifact
        .remaining_substantive_replacement_blocker
        .contains("broader Lean4 corpus parity coverage"));
    assert_eq!(
        artifact.full_corpus_acceptance_gate,
        TACTIC_FULL_CORPUS_ACCEPTANCE_GATE
    );
    assert!(!artifact.representative_generated_backing_satisfies_full_corpus_acceptance);
    assert_eq!(
        artifact.full_corpus_acceptance_evidence_status,
        TACTIC_FULL_CORPUS_ACCEPTANCE_EVIDENCE_STATUS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED
    );
    assert!(!artifact.full_corpus_acceptance_artifact_present);
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_schema_required,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED
    );
    assert!(!artifact.full_corpus_acceptance_artifact_schema_validated);
    assert_eq!(
        artifact.full_corpus_acceptance_validator_required,
        TACTIC_FULL_CORPUS_ACCEPTANCE_VALIDATOR_REQUIRED
    );
    assert!(!artifact.full_corpus_acceptance_validator_present);
    assert_eq!(
        artifact.full_corpus_input_discovery_command,
        TACTIC_FULL_CORPUS_INPUT_DISCOVERY_COMMAND
    );
    assert_eq!(
        artifact.full_corpus_fixture_generator_command,
        TACTIC_FULL_CORPUS_FIXTURE_GENERATOR_COMMAND
    );
    assert!(!artifact.full_corpus_fixture_counts_as_acceptance_evidence);
    assert_eq!(
        artifact.full_corpus_fixture_acceptance_blocker,
        TACTIC_FULL_CORPUS_FIXTURE_ACCEPTANCE_BLOCKER
    );
    assert_eq!(
        artifact.full_corpus_acceptance_minimum_tactic_outcome_rows,
        TACTIC_FULL_CORPUS_ACCEPTANCE_MINIMUM_TACTIC_OUTCOME_ROWS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_tactic_outcome_row_contract,
        TACTIC_FULL_CORPUS_ACCEPTANCE_TACTIC_OUTCOME_ROW_CONTRACT
    );
    assert_eq!(
        artifact.full_corpus_acceptance_manifest_required_fields,
        TACTIC_FULL_CORPUS_ACCEPTANCE_MANIFEST_REQUIRED_FIELDS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_reviewer_evidence_required_fields,
        TACTIC_FULL_CORPUS_ACCEPTANCE_REVIEWER_EVIDENCE_REQUIRED_FIELDS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_fields,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_fields_fingerprint_algorithm,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS_FINGERPRINT_ALGORITHM
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_fields_fingerprint_sha256,
        tactic_full_corpus_list_fingerprint(TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS)
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_summary_fields,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_SUMMARY_FIELDS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_summary_fields_fingerprint_algorithm,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_SUMMARY_FIELDS_FINGERPRINT_ALGORITHM
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_summary_fields_fingerprint_sha256,
        tactic_full_corpus_list_fingerprint(
            TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_SUMMARY_FIELDS
        )
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_tactic_fields,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_algorithm,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS_FINGERPRINT_ALGORITHM
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_sha256,
        tactic_full_corpus_list_fingerprint(
            TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS
        )
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_evidence_fields,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_EVIDENCE_FIELDS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_algorithm,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_EVIDENCE_FIELDS_FINGERPRINT_ALGORITHM
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_sha256,
        tactic_full_corpus_list_fingerprint(
            TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_EVIDENCE_FIELDS
        )
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_blocker_fields,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_BLOCKER_FIELDS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_algorithm,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_BLOCKER_FIELDS_FINGERPRINT_ALGORITHM
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_sha256,
        tactic_full_corpus_list_fingerprint(
            TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_BLOCKER_FIELDS
        )
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_invariants,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_INVARIANTS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_invariants_fingerprint_algorithm,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_INVARIANTS_FINGERPRINT_ALGORITHM
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_required_invariants_fingerprint_sha256,
        tactic_full_corpus_list_fingerprint(
            TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_INVARIANTS
        )
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_allowed_evidence_kinds,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_ALLOWED_EVIDENCE_KINDS
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_algorithm,
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_ALLOWED_EVIDENCE_KINDS_FINGERPRINT_ALGORITHM
    );
    assert_eq!(
        artifact.full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_sha256,
        tactic_full_corpus_list_fingerprint(
            TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_ALLOWED_EVIDENCE_KINDS
        )
    );
    assert_eq!(
        artifact.full_corpus_acceptance_criteria_required,
        TACTIC_FULL_CORPUS_ACCEPTANCE_CRITERIA_REQUIRED
    );
    assert_eq!(
        artifact.full_corpus_acceptance_criteria_fingerprint_algorithm,
        TACTIC_FULL_CORPUS_ACCEPTANCE_CRITERIA_FINGERPRINT_ALGORITHM
    );
    assert_eq!(
        artifact.full_corpus_acceptance_criteria_fingerprint_sha256,
        tactic_full_corpus_list_fingerprint(TACTIC_FULL_CORPUS_ACCEPTANCE_CRITERIA_REQUIRED)
    );
    assert_eq!(
        artifact.full_corpus_reviewer_evidence_required,
        TACTIC_FULL_CORPUS_REVIEWER_EVIDENCE_REQUIRED
    );
    assert_eq!(
        artifact.full_corpus_reviewer_evidence_fingerprint_algorithm,
        TACTIC_FULL_CORPUS_REVIEWER_EVIDENCE_FINGERPRINT_ALGORITHM
    );
    assert_eq!(
        artifact.full_corpus_reviewer_evidence_fingerprint_sha256,
        tactic_full_corpus_list_fingerprint(TACTIC_FULL_CORPUS_REVIEWER_EVIDENCE_REQUIRED)
    );
    assert_eq!(artifact.summary.tactic_row_count, artifact.tactics.len());
    assert_eq!(artifact.summary.tactic_row_count, 8);
    assert_eq!(artifact.summary.lean4_total, 56);
    assert_eq!(artifact.summary.clean_total, 56);
    assert_eq!(artifact.summary.matched_total, 56);
    assert_eq!(artifact.summary.clean_gap_total, 0);
    assert_eq!(artifact.summary.proof_carrying_rows, 8);
    assert_eq!(artifact.summary.partial_rows, 0);
    assert_eq!(artifact.summary.parity_gap_rows, 0);

    let simp = artifact
        .tactics
        .iter()
        .find(|row| row.tactic == "simp")
        .expect("simp count row");
    assert_eq!(simp.status, TacticParityStatus::ProofCarrying);
    assert_eq!(simp.clean_count, 10);
    assert_eq!(simp.clean_gap_count, 0);
    let simp_cases = simp
        .generated_cases
        .as_ref()
        .expect("simp count row should be backed by generated cases");
    assert!(simp_cases.fail_closed);
    assert_eq!(simp_cases.case_count, simp.lean4_count);
    assert_eq!(simp_cases.matched_case_count, simp.matched_count);
    assert_eq!(simp_cases.cases.len(), simp.lean4_count as usize);
    assert!(simp_cases.cases.iter().all(|case| case.matched));
    assert!(simp_cases
        .cases
        .iter()
        .any(|case| case.case_id == "simp.fail-closed.no-progress"));

    let rw = artifact
        .tactics
        .iter()
        .find(|row| row.tactic == "rw")
        .expect("rw count row");
    assert_eq!(rw.status, TacticParityStatus::ProofCarrying);
    assert_eq!(rw.clean_count, 8);
    assert_eq!(rw.clean_gap_count, 0);
    let rw_cases = rw
        .generated_cases
        .as_ref()
        .expect("rw count row should be backed by generated cases");
    assert!(rw_cases.fail_closed);
    assert_eq!(rw_cases.case_count, rw.lean4_count);
    assert_eq!(rw_cases.matched_case_count, rw.matched_count);
    assert_eq!(rw_cases.cases.len(), rw.lean4_count as usize);
    assert!(rw_cases.cases.iter().all(|case| case.matched));
    assert!(rw_cases
        .cases
        .iter()
        .any(|case| case.case_id == "rw.fail-closed.no-pattern"));

    let exact = artifact
        .tactics
        .iter()
        .find(|row| row.tactic == "exact")
        .expect("exact count row");
    assert_eq!(exact.status, TacticParityStatus::ProofCarrying);
    assert_eq!(exact.clean_count, 6);
    assert_eq!(exact.clean_gap_count, 0);
    let exact_cases = exact
        .generated_cases
        .as_ref()
        .expect("exact count row should be backed by generated cases");
    assert!(exact_cases.fail_closed);
    assert_eq!(exact_cases.case_count, exact.lean4_count);
    assert_eq!(exact_cases.matched_case_count, exact.matched_count);
    assert_eq!(exact_cases.cases.len(), exact.lean4_count as usize);
    assert!(exact_cases.cases.iter().all(|case| case.matched));
    assert!(exact_cases
        .cases
        .iter()
        .any(|case| case.case_id == "exact.fail-closed.type-mismatch"));

    let mathverse = artifact
        .tactics
        .iter()
        .find(|row| row.tactic == "mathverse")
        .expect("mathverse count row");
    assert_eq!(mathverse.status, TacticParityStatus::ProofCarrying);
    assert_eq!(mathverse.clean_count, 8);
    assert_eq!(mathverse.clean_gap_count, 0);
    let mathverse_cases = mathverse
        .generated_cases
        .as_ref()
        .expect("mathverse count row should be backed by generated cases");
    assert!(mathverse_cases.fail_closed);
    assert_eq!(mathverse_cases.case_count, mathverse.lean4_count);
    assert_eq!(mathverse_cases.matched_case_count, mathverse.matched_count);
    assert_eq!(mathverse_cases.cases.len(), mathverse.lean4_count as usize);
    assert!(mathverse_cases.cases.iter().all(|case| case.matched));
    assert!(mathverse_cases
        .cases
        .iter()
        .any(|case| case.case_id == "mathverse.certified-arithmetic.fail-closed"));

    let linarith = artifact
        .tactics
        .iter()
        .find(|row| row.tactic == "linarith")
        .expect("linarith count row");
    assert_eq!(linarith.status, TacticParityStatus::ProofCarrying);
    assert_eq!(linarith.clean_count, 8);
    assert_eq!(linarith.clean_gap_count, 0);
    let linarith_cases = linarith
        .generated_cases
        .as_ref()
        .expect("linarith count row should be backed by generated cases");
    assert!(linarith_cases.fail_closed);
    assert_eq!(linarith_cases.case_count, linarith.lean4_count);
    assert_eq!(linarith_cases.matched_case_count, linarith.matched_count);
    assert_eq!(linarith_cases.cases.len(), linarith.lean4_count as usize);
    assert!(linarith_cases.cases.iter().all(|case| case.matched));
    assert!(linarith_cases
        .cases
        .iter()
        .any(|case| case.case_id == "linarith.certified-unsat.fail-closed"));

    let nlinarith = artifact
        .tactics
        .iter()
        .find(|row| row.tactic == "nlinarith")
        .expect("nlinarith count row");
    assert_eq!(nlinarith.status, TacticParityStatus::ProofCarrying);
    assert_eq!(nlinarith.clean_count, 6);
    assert_eq!(nlinarith.clean_gap_count, 0);
    let nlinarith_cases = nlinarith
        .generated_cases
        .as_ref()
        .expect("nlinarith count row should be backed by generated cases");
    assert!(nlinarith_cases.fail_closed);
    assert_eq!(nlinarith_cases.case_count, nlinarith.lean4_count);
    assert_eq!(nlinarith_cases.matched_case_count, nlinarith.matched_count);
    assert_eq!(nlinarith_cases.cases.len(), nlinarith.lean4_count as usize);
    assert!(nlinarith_cases.cases.iter().all(|case| case.matched));
    assert!(nlinarith_cases
        .cases
        .iter()
        .any(|case| case.case_id == "nlinarith.certified-unsat.fail-closed"));

    let aesop = artifact
        .tactics
        .iter()
        .find(|row| row.tactic == "aesop")
        .expect("aesop count row");
    assert_eq!(aesop.status, TacticParityStatus::ProofCarrying);
    assert_eq!(aesop.clean_count, 5);
    assert_eq!(aesop.clean_gap_count, 0);
    let aesop_cases = aesop
        .generated_cases
        .as_ref()
        .expect("aesop count row should be backed by generated cases");
    assert!(aesop_cases.fail_closed);
    assert_eq!(aesop_cases.case_count, aesop.lean4_count);
    assert_eq!(aesop_cases.matched_case_count, aesop.matched_count);
    assert_eq!(aesop_cases.cases.len(), aesop.lean4_count as usize);
    assert!(aesop_cases.cases.iter().all(|case| case.matched));
    assert!(aesop_cases
        .cases
        .iter()
        .any(|case| case.case_id == "aesop.forward.backtrack-isolation"));
    assert!(aesop.remaining_blocker.is_none());

    let grind = artifact
        .tactics
        .iter()
        .find(|row| row.tactic == "grind")
        .expect("grind count row");
    assert_eq!(grind.status, TacticParityStatus::ProofCarrying);
    assert_eq!(grind.clean_count, 5);
    assert_eq!(grind.clean_gap_count, 0);
    let grind_cases = grind
        .generated_cases
        .as_ref()
        .expect("grind count row should be backed by generated cases");
    assert!(grind_cases.fail_closed);
    assert_eq!(grind_cases.case_count, grind.lean4_count);
    assert_eq!(grind_cases.matched_case_count, grind.matched_count);
    assert_eq!(grind_cases.cases.len(), grind.lean4_count as usize);
    assert!(grind_cases.cases.iter().all(|case| case.matched));
    assert!(grind_cases
        .cases
        .iter()
        .any(|case| case.case_id == "grind.ematch.triggered-implication"));
    assert!(grind.remaining_blocker.is_none());
    validate_generated_tactic_case_backing(artifact)
        .expect("generated tactic cases should back count rows");
    validate_tactic_count_artifact_consistency(artifact)
        .expect("tactic count artifact should be internally consistent");
    validate_tactic_parity_report_linkage(&report)
        .expect("tactic parity report surfaces should agree");

    assert_eq!(artifact.strict_solver_fragments.row_count, 10);
    assert_eq!(
        artifact
            .strict_solver_fragments
            .unsupported_reject_and_fallback_rows,
        7
    );
}

#[test]
fn tactic_parity_count_artifact_matches_report_counts() {
    let report = TacticParityReport::current();
    let artifact = fs::read_to_string(repo_artifact_path(TACTIC_PARITY_COUNT_ARTIFACT_PATH))
        .expect("Lean4-vs-clean tactic count artifact should be checked in");
    if artifact.contains("\"stub\": true") {
        eprintln!("SKIP: {TACTIC_PARITY_COUNT_ARTIFACT_PATH} is a stub artifact");
        return;
    }
    let artifact_json: serde_json::Value =
        serde_json::from_str(&artifact).expect("tactic count artifact should be JSON");
    let report_json = serde_json::to_value(&report.lean4_vs_clean_tactic_counts)
        .expect("serialize report count artifact");

    assert_eq!(artifact_json, report_json);
}
