// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 13) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use super::support::*;
use crate::cmd_replacement::*;

#[test]
fn tactic_parity_count_artifact_consistency_rejects_unblocked_full_corpus_gate() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_gate = "accepted";

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must keep full-corpus gate blocked");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_corpus_acceptance_gate")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_representative_backing_as_full_corpus() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.representative_generated_backing_satisfies_full_corpus_acceptance = true;

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic backing must not satisfy full-corpus acceptance");
    assert!(failures.iter().any(|failure| {
        failure.contains("representative_generated_backing_satisfies_full_corpus_acceptance")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_premature_acceptance_evidence_status() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_evidence_status = "submitted";

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must keep full-corpus evidence unsubmitted");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_corpus_acceptance_evidence_status")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_premature_full_corpus_artifact_present() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_artifact_present = true;

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must not mark full-corpus artifact present");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_corpus_acceptance_artifact_present")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_premature_full_corpus_schema_validation() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_artifact_schema_validated = true;

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must not mark full-corpus schema validated");
    assert!(failures
        .iter()
        .any(|failure| { failure.contains("full_corpus_acceptance_artifact_schema_validated") }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_changed_full_corpus_validator_contract() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_validator_required = "python scripts/tactic_parity.py";

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
        "representative tactic artifact must keep the Rust-owned full-corpus validator contract",
    );
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_corpus_acceptance_validator_required")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_premature_full_corpus_validator_present() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_validator_present = true;

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
        "representative tactic artifact must not mark the full-corpus validator present",
    );
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_corpus_acceptance_validator_present")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_changed_input_discovery_command() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_input_discovery_command =
        "python scripts/tactic_parity/discover_inputs.py";

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must keep Rust-owned input discovery");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_corpus_input_discovery_command")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_fixture_as_acceptance_evidence() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_fixture_counts_as_acceptance_evidence = true;

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("generated full-corpus fixture must not count as acceptance evidence");
    assert!(failures
        .iter()
        .any(|failure| { failure.contains("full_corpus_fixture_counts_as_acceptance_evidence") }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_changed_fixture_generator_contract() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_fixture_generator_command = "python scripts/tactic_parity_full_corpus.py";

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("generated full-corpus fixture must keep the Rust-owned generator command");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_corpus_fixture_generator_command")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_fixture_acceptance_blocker() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_fixture_acceptance_blocker = "fixture accepted";

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("generated full-corpus fixture blocker must remain explicit");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_corpus_fixture_acceptance_blocker")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_lowered_outcome_row_minimum() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_minimum_tactic_outcome_rows = 0;

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("full-corpus acceptance must require real Lean4-vs-clean tactic outcome rows");
    assert!(failures
        .iter()
        .any(|failure| { failure.contains("full_corpus_acceptance_minimum_tactic_outcome_rows") }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_outcome_row_contract() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_tactic_outcome_row_contract =
        "tactics[] rows may omit Lean4 results";

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("full-corpus acceptance must keep the tactic outcome row contract");
    assert!(failures
        .iter()
        .any(|failure| { failure.contains("full_corpus_acceptance_tactic_outcome_row_contract") }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_manifest_contract() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact
        .full_corpus_acceptance_manifest_required_fields
        .pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("full-corpus acceptance must keep manifest field contract");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_corpus_acceptance_manifest_required_fields")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_reviewer_evidence_contract() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact
        .full_corpus_acceptance_reviewer_evidence_required_fields
        .pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("full-corpus acceptance must keep reviewer evidence field contract");
    assert!(failures.iter().any(|failure| {
        failure.contains("full_corpus_acceptance_reviewer_evidence_required_fields")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_full_corpus_artifact_fields() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact
        .full_corpus_acceptance_artifact_required_fields
        .pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must keep full-corpus artifact field contract");
    assert!(failures
        .iter()
        .any(|failure| { failure.contains("full_corpus_acceptance_artifact_required_fields") }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_stale_full_corpus_artifact_fields_fingerprint()
{
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_artifact_required_fields_fingerprint_sha256 =
        "stale".to_owned();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
        "representative tactic artifact must keep full-corpus artifact field fingerprint fresh",
    );
    assert!(failures.iter().any(|failure| {
        failure.contains("full_corpus_acceptance_artifact_required_fields_fingerprint_sha256")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_full_corpus_artifact_summary_fields() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact
        .full_corpus_acceptance_artifact_required_summary_fields
        .pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
        "representative tactic artifact must keep full-corpus artifact summary field contract",
    );
    assert!(failures.iter().any(|failure| {
        failure.contains("full_corpus_acceptance_artifact_required_summary_fields")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_stale_full_corpus_artifact_summary_fields_fingerprint(
) {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_artifact_required_summary_fields_fingerprint_sha256 =
        "stale".to_owned();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
            "representative tactic artifact must keep full-corpus artifact summary field fingerprint fresh",
        );
    assert!(failures.iter().any(|failure| {
        failure
            .contains("full_corpus_acceptance_artifact_required_summary_fields_fingerprint_sha256")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_full_corpus_artifact_tactic_fields() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact
        .full_corpus_acceptance_artifact_required_tactic_fields
        .pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
        "representative tactic artifact must keep full-corpus artifact tactic field contract",
    );
    assert!(failures.iter().any(|failure| {
        failure.contains("full_corpus_acceptance_artifact_required_tactic_fields")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_stale_full_corpus_artifact_tactic_fields_fingerprint(
) {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_sha256 =
        "stale".to_owned();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
            "representative tactic artifact must keep full-corpus artifact tactic field fingerprint fresh",
        );
    assert!(failures.iter().any(|failure| {
        failure
            .contains("full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_sha256")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_full_corpus_artifact_evidence_fields()
{
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact
        .full_corpus_acceptance_artifact_required_evidence_fields
        .pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
        "representative tactic artifact must keep full-corpus artifact evidence field contract",
    );
    assert!(failures.iter().any(|failure| {
        failure.contains("full_corpus_acceptance_artifact_required_evidence_fields")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_stale_full_corpus_artifact_evidence_fields_fingerprint(
) {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_sha256 =
        "stale".to_owned();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
            "representative tactic artifact must keep full-corpus artifact evidence field fingerprint fresh",
        );
    assert!(failures.iter().any(|failure| {
        failure
            .contains("full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_sha256")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_full_corpus_artifact_blocker_fields() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact
        .full_corpus_acceptance_artifact_required_blocker_fields
        .pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
        "representative tactic artifact must keep full-corpus artifact blocker field contract",
    );
    assert!(failures.iter().any(|failure| {
        failure.contains("full_corpus_acceptance_artifact_required_blocker_fields")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_stale_full_corpus_artifact_blocker_fields_fingerprint(
) {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_sha256 =
        "stale".to_owned();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
            "representative tactic artifact must keep full-corpus artifact blocker field fingerprint fresh",
        );
    assert!(failures.iter().any(|failure| {
        failure
            .contains("full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_sha256")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_full_corpus_artifact_invariants() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact
        .full_corpus_acceptance_artifact_required_invariants
        .pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
        "representative tactic artifact must keep full-corpus artifact acceptance invariants",
    );
    assert!(failures.iter().any(|failure| {
        failure.contains("full_corpus_acceptance_artifact_required_invariants")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_stale_full_corpus_artifact_invariants_fingerprint(
) {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_acceptance_artifact_required_invariants_fingerprint_sha256 =
        "stale".to_owned();

    let failures = validate_tactic_count_artifact_consistency(&artifact).expect_err(
        "representative tactic artifact must keep full-corpus artifact invariant fingerprint fresh",
    );
    assert!(failures.iter().any(|failure| {
        failure.contains("full_corpus_acceptance_artifact_required_invariants_fingerprint_sha256")
    }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_full_corpus_allowed_evidence_kinds() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact
        .full_corpus_acceptance_artifact_allowed_evidence_kinds
        .pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must keep full-corpus evidence kind allowlist");
    assert!(failures.iter().any(|failure| {
        failure.contains("full_corpus_acceptance_artifact_allowed_evidence_kinds")
    }));
}
