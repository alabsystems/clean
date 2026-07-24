// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 11) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use super::support::*;
use crate::cmd_replacement::*;

#[test]
fn tactic_parity_discover_full_corpus_inputs_reports_missing_real_artifacts() {
    let registry = repo_artifact_path("evals/registry/tactic-parity.yaml");
    if !registry.exists() {
        eprintln!("SKIP: tactic-parity registry not present on this machine");
        return;
    }
    let discovery = TacticParityFullCorpusInputDiscovery::from_registry_path(&registry);

    assert!(discovery.registry_present);
    assert!(discovery.registry_valid);
    assert_eq!(discovery.discovery_status, "blocked_missing_real_artifacts");
    assert_eq!(discovery.lane_count, 7);
    assert_eq!(discovery.expected_real_artifact_count, 7);
    assert_eq!(discovery.discovered_real_artifact_count, 0);
    assert_eq!(discovery.missing_real_artifact_count, 7);
    assert_eq!(discovery.missing_outcome_evidence_count, 7);
    assert!(!discovery.full_corpus_artifact_present);
    assert!(!discovery.representative_generated_backing_counts_as_acceptance_evidence);
    assert!(!discovery.full_lean4_corpus_coverage_claimed);
    assert!(!discovery.launch_readiness_claimed);
    assert!(!discovery.acceptance_evidence_candidate);
    assert!(discovery.blockers.iter().any(|blocker| blocker
        .contains("metrics/benchmarks/tactic-parity/{run_id}/lean4/simp-counts.json")));
    assert!(discovery
        .blockers
        .iter()
        .any(|blocker| blocker.contains("reports/tactic-parity-full-corpus.json")));

    let simp = discovery
        .lanes
        .iter()
        .find(|lane| lane.tactic_lane == "simp")
        .expect("simp discovery lane");
    assert_eq!(
        simp.source_case_ids,
        vec!["simp_all_opaque_target_no_progress".to_owned()]
    );
    assert!(simp.source_corpus_valid);
    assert!(simp.runner_present);
    assert!(!simp.real_generated_count_artifact_present);
    assert!(simp.missing_generated_count_evidence);
    assert!(simp.missing_full_corpus_outcome_evidence);
}

#[test]
fn tactic_parity_discover_full_corpus_inputs_keeps_representative_counts_nonclaiming() {
    let report = TacticParityReport::current();
    let discovery = TacticParityFullCorpusInputDiscovery::from_registry_path(&repo_artifact_path(
        "evals/registry/tactic-parity.yaml",
    ));

    assert_eq!(
        report.lean4_vs_clean_tactic_counts.summary.matched_total,
        56
    );
    assert!(report
        .lean4_vs_clean_tactic_counts
        .tactics
        .iter()
        .all(|row| row.generated_cases.is_some()));
    assert_eq!(
        report.lean4_vs_clean_tactic_counts.coverage_scope,
        "representative-generated-cases-only"
    );
    assert!(
        !report
            .lean4_vs_clean_tactic_counts
            .representative_generated_backing_satisfies_full_corpus_acceptance
    );
    assert!(!discovery.representative_generated_backing_counts_as_acceptance_evidence);
    assert!(!discovery.acceptance_evidence_candidate);
}

#[test]
fn tactic_parity_discover_full_corpus_inputs_json_contract_is_stable() {
    let registry = repo_artifact_path("evals/registry/tactic-parity.yaml");
    if !registry.exists() {
        eprintln!("SKIP: tactic-parity registry not present on this machine");
        return;
    }
    let discovery = TacticParityFullCorpusInputDiscovery::from_registry_path(&registry);
    let json = serde_json::to_value(&discovery).expect("serialize discovery JSON");

    assert_eq!(
        json["schema_version"],
        "clean-tactic-parity-full-corpus-input-discovery-v1"
    );
    assert_eq!(
        json["generated_by"],
        "clean replacement tactic-parity discover-full-corpus-inputs"
    );
    assert!(json["registry_path"]
        .as_str()
        .expect("registry path string")
        .ends_with("evals/registry/tactic-parity.yaml"));
    assert_eq!(json["discovery_status"], "blocked_missing_real_artifacts");
    assert_eq!(json["lane_count"], 7);
    assert_eq!(json["expected_real_artifact_count"], 7);
    assert_eq!(json["discovered_real_artifact_count"], 0);
    assert_eq!(json["missing_real_artifact_count"], 7);
    assert_eq!(json["missing_outcome_evidence_count"], 7);
    assert_eq!(
        json["representative_generated_backing_counts_as_acceptance_evidence"],
        false
    );
    assert_eq!(json["full_lean4_corpus_coverage_claimed"], false);
    assert_eq!(json["launch_readiness_claimed"], false);
    assert_eq!(json["acceptance_evidence_candidate"], false);
    assert_eq!(json["lanes"][0]["tactic_lane"], "simp");
    assert_eq!(
        json["lanes"][0]["expected_generated_count_artifact_path"],
        "metrics/benchmarks/tactic-parity/{run_id}/lean4/simp-counts.json"
    );
    assert_eq!(
        json["lanes"][0]["real_generated_count_artifact_present"],
        false
    );
    assert_eq!(json["lanes"][0]["missing_generated_count_evidence"], true);
    assert_eq!(
        json["lanes"][0]["missing_full_corpus_outcome_evidence"],
        true
    );
}

#[test]
fn tactic_parity_validate_full_corpus_missing_artifact_fails_closed() {
    let dir = tempfile::tempdir().expect("tempdir");
    let missing_report = dir.path().join("missing-full-corpus.json");

    let validation = TacticParityFullCorpusValidation::from_report_path(&missing_report);

    assert!(!validation.validation_passed);
    assert_eq!(validation.validation_status, "invalid");
    assert!(!validation.artifact_present);
    assert!(validation.report_schema_version.is_none());
    assert!(validation
        .failures
        .iter()
        .any(|failure| failure.contains("artifact-readable")));
}

#[test]
fn tactic_parity_validate_full_corpus_invalid_schema_fails_closed() {
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("tactic-parity-full-corpus.json");
    fs::write(
        &report,
        serde_json::json!({
            "schema_version": "clean-tactic-parity-full-corpus-v0",
            "generated_by": "test fixture",
            "source_corpus": "test fixture",
            "full_lean4_corpus_coverage_claimed": false,
            "launch_readiness_claimed": false,
            "summary": {},
            "tactics": [],
            "blockers": []
        })
        .to_string(),
    )
    .expect("write invalid schema fixture");

    let validation = TacticParityFullCorpusValidation::from_report_path(&report);

    assert!(!validation.validation_passed);
    assert_eq!(validation.validation_status, "invalid");
    assert!(validation.artifact_present);
    assert_eq!(
        validation.report_schema_version.as_deref(),
        Some("clean-tactic-parity-full-corpus-v0")
    );
    assert!(validation
        .failures
        .iter()
        .any(|failure| failure.contains("schema-version")));
}

#[test]
fn tactic_parity_validate_full_corpus_missing_required_field_fails_closed() {
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("tactic-parity-full-corpus.json");
    fs::write(
        &report,
        serde_json::json!({
            "schema_version": TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED,
            "generated_by": "test fixture",
            "source_corpus": "test fixture",
            "full_lean4_corpus_coverage_claimed": false,
            "launch_readiness_claimed": false,
            "summary": {},
            "tactics": []
        })
        .to_string(),
    )
    .expect("write missing required field fixture");

    let validation = TacticParityFullCorpusValidation::from_report_path(&report);

    assert!(!validation.validation_passed);
    assert_eq!(validation.validation_status, "invalid");
    assert!(validation.artifact_present);
    assert_eq!(
        validation.report_schema_version.as_deref(),
        Some(TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED)
    );
    assert!(validation
        .failures
        .iter()
        .any(|failure| failure.contains("required-fields") && failure.contains("blockers")));
}

#[test]
fn tactic_parity_validate_full_corpus_rejects_overclaiming_complete_fixture() {
    for (case, coverage_claimed, launch_readiness_claimed) in [
        ("coverage-claimed", true, false),
        ("launch-readiness-claimed", false, true),
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        let report = dir.path().join(format!("{case}.json"));
        fs::write(
            &report,
            serde_json::json!({
                "schema_version": TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED,
                "generated_by": "test fixture",
                "source_corpus": "complete schema fixture; not full Lean4 corpus evidence",
                "full_lean4_corpus_coverage_claimed": coverage_claimed,
                "launch_readiness_claimed": launch_readiness_claimed,
                "summary": {},
                "tactics": [],
                "blockers": []
            })
            .to_string(),
        )
        .expect("write overclaiming complete fixture");

        let validation = TacticParityFullCorpusValidation::from_report_path(&report);

        assert!(!validation.validation_passed, "{case} must fail closed");
        assert_eq!(validation.validation_status, "invalid");
        assert!(validation.artifact_present);
        assert_eq!(
            validation.report_schema_version.as_deref(),
            Some(TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED)
        );
        assert_eq!(validation.check_count, 5);
        assert_eq!(validation.passed_count, 4);
        assert!(validation
            .failures
            .iter()
            .any(|failure| failure.contains("no-launch-overclaim")));
    }
}

#[test]
fn tactic_parity_validate_full_corpus_minimal_temp_fixture_passes_schema_contract() {
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("tactic-parity-full-corpus.json");
    fs::write(
        &report,
        serde_json::json!({
            "schema_version": TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED,
            "generated_by": "test fixture",
            "source_corpus": "minimal temp schema fixture; not full Lean4 corpus evidence",
            "full_lean4_corpus_coverage_claimed": false,
            "launch_readiness_claimed": false,
            "summary": {},
            "tactics": [],
            "blockers": []
        })
        .to_string(),
    )
    .expect("write minimal schema fixture");

    let validation = TacticParityFullCorpusValidation::from_report_path(&report);

    assert!(validation.validation_passed, "{:?}", validation.failures);
    assert_eq!(validation.validation_status, "valid_fail_closed");
    assert!(validation.artifact_present);
    assert_eq!(
        validation.report_schema_version.as_deref(),
        Some(TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED)
    );
    assert_eq!(validation.tactic_outcome_row_count, 0);
    assert_eq!(validation.blocker_row_count, 0);
    assert!(!validation.contains_tactic_outcome_evidence);
    assert!(validation.schema_fixture_only);
    assert!(!validation.acceptance_evidence_candidate);
    assert_eq!(validation.check_count, 5);
    assert_eq!(validation.passed_count, validation.check_count);
    assert!(validation.failures.is_empty());
}

#[test]
fn tactic_parity_validate_full_corpus_distinguishes_real_outcome_rows_from_schema_fixture() {
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("tactic-parity-full-corpus-outcome.json");
    fs::write(
            &report,
            serde_json::json!({
                "schema_version": TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED,
                "generated_by": "test fixture",
                "source_corpus": "single generated Lean4-vs-clean tactic outcome fixture",
                "full_lean4_corpus_coverage_claimed": false,
                "launch_readiness_claimed": false,
                "summary": {},
                "tactics": [{
                    "tactic": "simp",
                    "fixture_id": "fixture:simp.basic",
                    "lean4_fixture": "lean4:simp.basic",
                    "clean_fixture": "clean:simp.basic",
                    "lean4_result": "closed",
                    "clean_result": "closed",
                    "matched": true,
                    "evidence": [{
                        "evidence_id": "evidence:simp.basic",
                        "kind": "generated_fixture_execution",
                        "path": "tests/generated/simp/basic.lean",
                        "command": "clean replacement tactic-parity validate-full-corpus --report /tmp/tactic-parity-full-corpus.json --json",
                        "exit_status": 0,
                        "stdout_digest_sha256": "fixture-digest",
                        "reviewed_at": "1970-01-01T00:00:00Z"
                    }],
                    "reviewed_blocker": null
                }],
                "blockers": []
            })
            .to_string(),
        )
        .expect("write tactic outcome fixture");

    let validation = TacticParityFullCorpusValidation::from_report_path(&report);

    assert!(!validation.validation_passed);
    assert_eq!(validation.tactic_outcome_row_count, 1);
    assert_eq!(validation.blocker_row_count, 0);
    assert!(validation.contains_tactic_outcome_evidence);
    assert!(!validation.schema_fixture_only);
    assert!(!validation.corpus_manifest_present);
    assert!(!validation.corpus_manifest_valid);
    assert!(!validation.reviewer_evidence_present);
    assert!(!validation.reviewer_evidence_valid);
    assert!(!validation.acceptance_evidence_candidate);
    assert_eq!(validation.check_count, 7);
    assert_eq!(validation.passed_count, 5);
    assert!(validation
        .failures
        .iter()
        .any(|failure| failure.contains("corpus-manifest")));
    assert!(validation
        .failures
        .iter()
        .any(|failure| failure.contains("reviewer-evidence")));
}

#[test]
fn tactic_parity_validate_full_corpus_acceptance_candidate_requires_manifest_and_review() {
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir.path().join("tactic-parity-full-corpus-candidate.json");
    fs::write(
            &report,
            serde_json::json!({
                "schema_version": TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED,
                "generated_by": "test fixture",
                "source_corpus": "single generated Lean4-vs-clean tactic outcome fixture",
                "full_lean4_corpus_coverage_claimed": false,
                "launch_readiness_claimed": false,
                "corpus_manifest": {
                    "manifest_id": "manifest:single-simp",
                    "source": "tests/generated/simp/basic.lean",
                    "fixture_count": 1,
                    "generated_at": "1970-01-01T00:00:00Z",
                    "source_digest_sha256": "fixture-source-digest"
                },
                "reviewer_evidence": {
                    "reviewer": "test-fixture",
                    "reviewed_at": "1970-01-01T00:00:00Z",
                    "scope": "single tactic outcome fixture",
                    "decision": "schema-only acceptance candidate, not full corpus coverage",
                    "notes": "Validates the manifest/reviewer contract without claiming coverage.",
                    "manifest_id": "manifest:single-simp",
                    "source_digest_sha256": "fixture-source-digest"
                },
                "summary": {},
                "tactics": [{
                    "tactic": "simp",
                    "fixture_id": "fixture:simp.basic",
                    "lean4_fixture": "lean4:simp.basic",
                    "clean_fixture": "clean:simp.basic",
                    "lean4_result": "closed",
                    "clean_result": "closed",
                    "matched": true,
                    "evidence": [{
                        "evidence_id": "evidence:simp.basic",
                        "kind": "generated_fixture_execution",
                        "path": "tests/generated/simp/basic.lean",
                        "command": "clean replacement tactic-parity validate-full-corpus --report /tmp/tactic-parity-full-corpus.json --json",
                        "exit_status": 0,
                        "stdout_digest_sha256": "fixture-digest",
                        "reviewed_at": "1970-01-01T00:00:00Z"
                    }],
                    "reviewed_blocker": null
                }],
                "blockers": []
            })
            .to_string(),
        )
        .expect("write tactic outcome candidate fixture");

    let validation = TacticParityFullCorpusValidation::from_report_path(&report);

    assert!(validation.validation_passed, "{:?}", validation.failures);
    assert_eq!(validation.tactic_outcome_row_count, 1);
    assert!(validation.contains_tactic_outcome_evidence);
    assert!(validation.corpus_manifest_present);
    assert!(validation.corpus_manifest_valid);
    assert!(validation.reviewer_evidence_present);
    assert!(validation.reviewer_evidence_valid);
    assert!(validation.reviewer_evidence_provenance_valid);
    assert!(!validation.schema_fixture_only);
    assert!(validation.acceptance_evidence_candidate);
    assert_eq!(
        validation.missing_acceptance_requirements,
        Vec::<String>::new()
    );
    assert_eq!(validation.check_count, 8);
    assert_eq!(validation.passed_count, validation.check_count);
}
