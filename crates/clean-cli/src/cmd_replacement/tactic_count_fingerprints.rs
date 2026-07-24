// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Count artifact fingerprint-contract validation.

use super::*;

/// Fingerprint-contract checks split out of
/// `validate_tactic_count_artifact_consistency` (same checks, same order).
pub(crate) fn validate_tactic_count_artifact_fingerprints(
    artifact: &TacticParityCountArtifact,
    failures: &mut Vec<String>,
) {
    if artifact.full_corpus_acceptance_artifact_required_fields_fingerprint_algorithm
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS_FINGERPRINT_ALGORITHM
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_fields_fingerprint_algorithm must describe the stable full-corpus artifact field fingerprint"
                .to_owned(),
        );
    }
    let expected_required_fields_fingerprint = tactic_full_corpus_list_fingerprint(
        &artifact.full_corpus_acceptance_artifact_required_fields,
    );
    if artifact.full_corpus_acceptance_artifact_required_fields_fingerprint_sha256
        != expected_required_fields_fingerprint
    {
        failures.push(format!(
            "full_corpus_acceptance_artifact_required_fields_fingerprint_sha256={} does not match required fields fingerprint={}",
            artifact.full_corpus_acceptance_artifact_required_fields_fingerprint_sha256,
            expected_required_fields_fingerprint
        ));
    }
    if artifact
        .full_corpus_acceptance_artifact_required_summary_fields
        .as_slice()
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_SUMMARY_FIELDS
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_summary_fields must keep the exact full-corpus artifact summary field contract"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_artifact_required_summary_fields_fingerprint_algorithm
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_SUMMARY_FIELDS_FINGERPRINT_ALGORITHM
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_summary_fields_fingerprint_algorithm must describe the stable full-corpus artifact summary field fingerprint"
                .to_owned(),
        );
    }
    let expected_required_summary_fields_fingerprint = tactic_full_corpus_list_fingerprint(
        &artifact.full_corpus_acceptance_artifact_required_summary_fields,
    );
    if artifact.full_corpus_acceptance_artifact_required_summary_fields_fingerprint_sha256
        != expected_required_summary_fields_fingerprint
    {
        failures.push(format!(
            "full_corpus_acceptance_artifact_required_summary_fields_fingerprint_sha256={} does not match required summary fields fingerprint={}",
            artifact.full_corpus_acceptance_artifact_required_summary_fields_fingerprint_sha256,
            expected_required_summary_fields_fingerprint
        ));
    }
    if artifact
        .full_corpus_acceptance_artifact_required_tactic_fields
        .as_slice()
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_tactic_fields must keep the exact full-corpus artifact tactic field contract"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_algorithm
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS_FINGERPRINT_ALGORITHM
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_algorithm must describe the stable full-corpus artifact tactic field fingerprint"
                .to_owned(),
        );
    }
    let expected_required_tactic_fields_fingerprint = tactic_full_corpus_list_fingerprint(
        &artifact.full_corpus_acceptance_artifact_required_tactic_fields,
    );
    if artifact.full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_sha256
        != expected_required_tactic_fields_fingerprint
    {
        failures.push(format!(
            "full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_sha256={} does not match required tactic fields fingerprint={}",
            artifact.full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_sha256,
            expected_required_tactic_fields_fingerprint
        ));
    }
    if artifact
        .full_corpus_acceptance_artifact_required_evidence_fields
        .as_slice()
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_EVIDENCE_FIELDS
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_evidence_fields must keep the exact full-corpus artifact evidence field contract"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_algorithm
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_EVIDENCE_FIELDS_FINGERPRINT_ALGORITHM
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_algorithm must describe the stable full-corpus artifact evidence field fingerprint"
                .to_owned(),
        );
    }
    let expected_required_evidence_fields_fingerprint = tactic_full_corpus_list_fingerprint(
        &artifact.full_corpus_acceptance_artifact_required_evidence_fields,
    );
    if artifact.full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_sha256
        != expected_required_evidence_fields_fingerprint
    {
        failures.push(format!(
            "full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_sha256={} does not match required evidence fields fingerprint={}",
            artifact.full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_sha256,
            expected_required_evidence_fields_fingerprint
        ));
    }
    if artifact
        .full_corpus_acceptance_artifact_required_blocker_fields
        .as_slice()
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_BLOCKER_FIELDS
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_blocker_fields must keep the exact full-corpus artifact blocker review field contract"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_algorithm
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_BLOCKER_FIELDS_FINGERPRINT_ALGORITHM
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_algorithm must describe the stable full-corpus artifact blocker review field fingerprint"
                .to_owned(),
        );
    }
    let expected_required_blocker_fields_fingerprint = tactic_full_corpus_list_fingerprint(
        &artifact.full_corpus_acceptance_artifact_required_blocker_fields,
    );
    if artifact.full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_sha256
        != expected_required_blocker_fields_fingerprint
    {
        failures.push(format!(
            "full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_sha256={} does not match required blocker fields fingerprint={}",
            artifact.full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_sha256,
            expected_required_blocker_fields_fingerprint
        ));
    }
    if artifact
        .full_corpus_acceptance_artifact_required_invariants
        .as_slice()
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_INVARIANTS
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_invariants must keep the exact full-corpus artifact acceptance invariants"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_artifact_required_invariants_fingerprint_algorithm
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_INVARIANTS_FINGERPRINT_ALGORITHM
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_invariants_fingerprint_algorithm must describe the stable full-corpus artifact invariant fingerprint"
                .to_owned(),
        );
    }
    let expected_required_invariants_fingerprint = tactic_full_corpus_list_fingerprint(
        &artifact.full_corpus_acceptance_artifact_required_invariants,
    );
    if artifact.full_corpus_acceptance_artifact_required_invariants_fingerprint_sha256
        != expected_required_invariants_fingerprint
    {
        failures.push(format!(
            "full_corpus_acceptance_artifact_required_invariants_fingerprint_sha256={} does not match required invariants fingerprint={}",
            artifact.full_corpus_acceptance_artifact_required_invariants_fingerprint_sha256,
            expected_required_invariants_fingerprint
        ));
    }
    if artifact
        .full_corpus_acceptance_artifact_allowed_evidence_kinds
        .as_slice()
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_ALLOWED_EVIDENCE_KINDS
    {
        failures.push(
            "full_corpus_acceptance_artifact_allowed_evidence_kinds must keep the exact full-corpus evidence kind allowlist"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_algorithm
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_ALLOWED_EVIDENCE_KINDS_FINGERPRINT_ALGORITHM
    {
        failures.push(
            "full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_algorithm must describe the stable full-corpus evidence kind fingerprint"
                .to_owned(),
        );
    }
    let expected_allowed_evidence_kinds_fingerprint = tactic_full_corpus_list_fingerprint(
        &artifact.full_corpus_acceptance_artifact_allowed_evidence_kinds,
    );
    if artifact.full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_sha256
        != expected_allowed_evidence_kinds_fingerprint
    {
        failures.push(format!(
            "full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_sha256={} does not match allowed evidence kinds fingerprint={}",
            artifact.full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_sha256,
            expected_allowed_evidence_kinds_fingerprint
        ));
    }
    if artifact.full_corpus_acceptance_criteria_required.as_slice()
        != TACTIC_FULL_CORPUS_ACCEPTANCE_CRITERIA_REQUIRED
    {
        failures.push(
            "full_corpus_acceptance_criteria_required must keep the exact full-corpus acceptance criteria"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_criteria_fingerprint_algorithm
        != TACTIC_FULL_CORPUS_ACCEPTANCE_CRITERIA_FINGERPRINT_ALGORITHM
    {
        failures.push(
            "full_corpus_acceptance_criteria_fingerprint_algorithm must describe the stable criteria fingerprint"
                .to_owned(),
        );
    }
    let expected_criteria_fingerprint =
        tactic_full_corpus_list_fingerprint(&artifact.full_corpus_acceptance_criteria_required);
    if artifact.full_corpus_acceptance_criteria_fingerprint_sha256 != expected_criteria_fingerprint
    {
        failures.push(format!(
            "full_corpus_acceptance_criteria_fingerprint_sha256={} does not match criteria fingerprint={}",
            artifact.full_corpus_acceptance_criteria_fingerprint_sha256,
            expected_criteria_fingerprint
        ));
    }
    if artifact.full_corpus_reviewer_evidence_fingerprint_algorithm
        != TACTIC_FULL_CORPUS_REVIEWER_EVIDENCE_FINGERPRINT_ALGORITHM
    {
        failures.push(
            "full_corpus_reviewer_evidence_fingerprint_algorithm must describe the stable reviewer evidence fingerprint"
                .to_owned(),
        );
    }
    let expected_reviewer_evidence_fingerprint =
        tactic_full_corpus_list_fingerprint(&artifact.full_corpus_reviewer_evidence_required);
    if artifact.full_corpus_reviewer_evidence_fingerprint_sha256
        != expected_reviewer_evidence_fingerprint
    {
        failures.push(format!(
            "full_corpus_reviewer_evidence_fingerprint_sha256={} does not match reviewer evidence fingerprint={}",
            artifact.full_corpus_reviewer_evidence_fingerprint_sha256,
            expected_reviewer_evidence_fingerprint
        ));
    }
}
