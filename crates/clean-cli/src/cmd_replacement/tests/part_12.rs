// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 12) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use crate::cmd_replacement::*;

#[test]
fn tactic_parity_validate_full_corpus_rejects_reviewer_provenance_mismatch() {
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir
        .path()
        .join("tactic-parity-full-corpus-provenance-mismatch.json");
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
                    "notes": "This intentionally points at the wrong manifest provenance.",
                    "manifest_id": "manifest:other",
                    "source_digest_sha256": "other-source-digest"
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
        .expect("write provenance mismatch fixture");

    let validation = TacticParityFullCorpusValidation::from_report_path(&report);

    assert!(!validation.validation_passed);
    assert_eq!(validation.tactic_outcome_row_count, 1);
    assert!(validation.contains_tactic_outcome_evidence);
    assert!(validation.corpus_manifest_valid);
    assert!(validation.reviewer_evidence_valid);
    assert!(!validation.reviewer_evidence_provenance_valid);
    assert!(!validation.acceptance_evidence_candidate);
    assert_eq!(
        validation.missing_acceptance_requirements,
        vec![
            "make reviewer_evidence manifest_id and source_digest_sha256 match corpus_manifest"
                .to_owned()
        ]
    );
    assert_eq!(validation.check_count, 8);
    assert_eq!(validation.passed_count, 7);
    assert!(validation.failures.iter().any(|failure| {
        failure.contains("reviewer-evidence-provenance")
            && failure.contains("manifest:other")
            && failure.contains("other-source-digest")
    }));
}

#[test]
fn tactic_parity_validate_full_corpus_rejects_incomplete_tactic_outcome_row() {
    let dir = tempfile::tempdir().expect("tempdir");
    let report = dir
        .path()
        .join("tactic-parity-full-corpus-incomplete-outcome.json");
    fs::write(
        &report,
        serde_json::json!({
            "schema_version": TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED,
            "generated_by": "test fixture",
            "source_corpus": "incomplete tactic outcome fixture",
            "full_lean4_corpus_coverage_claimed": false,
            "launch_readiness_claimed": false,
            "summary": {},
            "tactics": [{
                "tactic": "simp",
                "fixture_id": "fixture:simp.basic",
                "lean4_fixture": "lean4:simp.basic",
                "clean_fixture": "clean:simp.basic",
                "matched": true,
                "evidence": [],
                "reviewed_blocker": null
            }],
            "blockers": []
        })
        .to_string(),
    )
    .expect("write incomplete tactic outcome fixture");

    let validation = TacticParityFullCorpusValidation::from_report_path(&report);

    assert!(!validation.validation_passed);
    assert_eq!(validation.tactic_outcome_row_count, 1);
    assert!(validation.contains_tactic_outcome_evidence);
    assert!(!validation.schema_fixture_only);
    assert!(!validation.acceptance_evidence_candidate);
    assert_eq!(validation.check_count, 7);
    assert_eq!(validation.passed_count, 4);
    assert!(validation
        .failures
        .iter()
        .any(|failure| failure.contains("tactic-outcome-fields")
            && failure.contains("lean4_result")
            && failure.contains("clean_result")));
}

#[test]
fn tactic_parity_validate_full_corpus_json_contract_is_stable_for_minimal_temp_fixture() {
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
    let json = serde_json::to_value(&validation).expect("serialize validation JSON");

    assert_eq!(
        json["schema_version"],
        "clean-tactic-parity-full-corpus-validation-v1"
    );
    assert_eq!(
        json["generated_by"],
        "clean replacement tactic-parity validate-full-corpus"
    );
    assert_eq!(
        json["report_schema_version"],
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED
    );
    assert_eq!(json["validation_passed"], true);
    assert_eq!(json["validation_status"], "valid_fail_closed");
    assert_eq!(json["tactic_outcome_row_count"], 0);
    assert_eq!(json["blocker_row_count"], 0);
    assert_eq!(json["contains_tactic_outcome_evidence"], false);
    assert_eq!(json["corpus_manifest_present"], false);
    assert_eq!(json["corpus_manifest_valid"], false);
    assert_eq!(json["reviewer_evidence_present"], false);
    assert_eq!(json["reviewer_evidence_valid"], false);
    assert_eq!(json["reviewer_evidence_provenance_valid"], false);
    assert_eq!(json["schema_fixture_only"], true);
    assert_eq!(json["acceptance_evidence_candidate"], false);
    assert_eq!(
        json["missing_acceptance_requirements"],
        serde_json::json!([
            "replace generated schema fixture with real Lean4-vs-clean tactic outcome rows",
            "include at least 1 tactics[] Lean4-vs-clean outcome row"
        ])
    );
    assert_eq!(json["check_count"], 5);
    assert_eq!(json["passed_count"], 5);
    assert_eq!(json["failures"], serde_json::json!([]));
}

#[test]
fn tactic_parity_generate_full_corpus_fixture_writes_nonclaiming_schema_artifact() {
    let dir = tempfile::tempdir().expect("tempdir");
    let output = dir.path().join("tactic-parity-full-corpus.json");

    let generation = TacticParityFullCorpusFixtureGeneration::write_to_path(&output)
        .expect("write full-corpus fixture");
    let artifact: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(&output).expect("read generated full-corpus fixture"),
    )
    .expect("parse generated full-corpus fixture");

    assert_eq!(
        generation.schema_version,
        "clean-tactic-parity-full-corpus-fixture-generation-v1"
    );
    assert_eq!(
        generation.generated_by,
        "clean replacement tactic-parity generate-full-corpus-fixture"
    );
    assert!(!generation.coverage_claimed);
    assert!(!generation.launch_readiness_claimed);
    assert!(generation.validation.validation_passed);
    assert_eq!(
        artifact["schema_version"],
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED
    );
    assert_eq!(
        artifact["source_corpus"],
        "generated schema fixture only; not full Lean4 tactic corpus evidence"
    );
    assert_eq!(artifact["full_lean4_corpus_coverage_claimed"], false);
    assert_eq!(artifact["launch_readiness_claimed"], false);
    assert_eq!(artifact["summary"]["enumerated_fixture_total"], 0);
    assert_eq!(artifact["summary"]["matched_fixture_total"], 0);
    assert_eq!(artifact["summary"]["clean_gap_total"], 0);
    assert_eq!(artifact["summary"]["reviewed_blocker_total"], 0);
    assert_eq!(artifact["summary"]["unreviewed_blocker_total"], 0);
    assert_eq!(artifact["tactics"], serde_json::json!([]));
    assert_eq!(artifact["blockers"], serde_json::json!([]));

    let report = TacticParityReport::current();
    let count_artifact = &report.lean4_vs_clean_tactic_counts;
    assert!(!count_artifact.full_corpus_acceptance_artifact_present);
    assert!(!count_artifact.full_lean4_corpus_coverage_claimed);
    assert!(!count_artifact.launch_readiness_claimed);
}

#[test]
fn tactic_parity_generate_full_corpus_fixture_json_contract_is_stable() {
    let dir = tempfile::tempdir().expect("tempdir");
    let output = dir.path().join("tactic-parity-full-corpus.json");

    let generation = TacticParityFullCorpusFixtureGeneration::write_to_path(&output)
        .expect("write full-corpus fixture");
    let json = serde_json::to_value(&generation).expect("serialize generation JSON");

    assert_eq!(
        json["schema_version"],
        "clean-tactic-parity-full-corpus-fixture-generation-v1"
    );
    assert_eq!(
        json["generated_by"],
        "clean replacement tactic-parity generate-full-corpus-fixture"
    );
    assert_eq!(json["output_path"], output.display().to_string());
    assert_eq!(
        json["artifact_schema_version"],
        TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED
    );
    assert_eq!(json["coverage_claimed"], false);
    assert_eq!(json["launch_readiness_claimed"], false);
    assert_eq!(
        json["validation"]["schema_version"],
        "clean-tactic-parity-full-corpus-validation-v1"
    );
    assert_eq!(json["validation"]["validation_status"], "valid_fail_closed");
    assert_eq!(json["validation"]["validation_passed"], true);
    assert_eq!(json["validation"]["tactic_outcome_row_count"], 0);
    assert_eq!(
        json["validation"]["contains_tactic_outcome_evidence"],
        false
    );
    assert_eq!(json["validation"]["corpus_manifest_present"], false);
    assert_eq!(json["validation"]["corpus_manifest_valid"], false);
    assert_eq!(json["validation"]["reviewer_evidence_present"], false);
    assert_eq!(json["validation"]["reviewer_evidence_valid"], false);
    assert_eq!(
        json["validation"]["reviewer_evidence_provenance_valid"],
        false
    );
    assert_eq!(json["validation"]["schema_fixture_only"], true);
    assert_eq!(json["validation"]["acceptance_evidence_candidate"], false);
    assert_eq!(
        json["validation"]["missing_acceptance_requirements"],
        serde_json::json!([
            "replace generated schema fixture with real Lean4-vs-clean tactic outcome rows",
            "include at least 1 tactics[] Lean4-vs-clean outcome row"
        ])
    );
    assert_eq!(json["validation"]["check_count"], 5);
    assert_eq!(json["validation"]["passed_count"], 5);
    assert_eq!(json["validation"]["failures"], serde_json::json!([]));
}

#[test]
fn tactic_parity_full_corpus_human_renderers_surface_fixture_flow_contract() {
    let dir = tempfile::tempdir().expect("tempdir");
    let output = dir.path().join("tactic-parity-full-corpus.json");

    let generation = TacticParityFullCorpusFixtureGeneration::write_to_path(&output)
        .expect("write full-corpus fixture");

    let mut generation_output = Vec::new();
    render_tactic_parity_full_corpus_fixture_generation_human(&mut generation_output, &generation)
        .expect("render generation human output");
    let generation_output =
        String::from_utf8(generation_output).expect("generation human output is utf-8");

    assert!(generation_output.contains("Clean tactic parity full-corpus fixture generation"));
    assert!(generation_output
        .contains("schema_version: clean-tactic-parity-full-corpus-fixture-generation-v1"));
    assert!(generation_output.contains(&format!("output_path: {}", output.display())));
    assert!(generation_output.contains("coverage_claimed: false"));
    assert!(generation_output.contains("launch_readiness_claimed: false"));
    assert!(generation_output.contains("validation_status: valid_fail_closed"));

    let validation = TacticParityFullCorpusValidation::from_report_path(&output);
    let mut validation_output = Vec::new();
    render_tactic_parity_full_corpus_validation_human(&mut validation_output, &validation)
        .expect("render validation human output");
    let validation_output =
        String::from_utf8(validation_output).expect("validation human output is utf-8");

    assert!(validation_output.contains("Clean tactic parity full-corpus validation"));
    assert!(
        validation_output.contains("schema_version: clean-tactic-parity-full-corpus-validation-v1")
    );
    assert!(validation_output.contains(&format!("report_path: {}", output.display())));
    assert!(validation_output.contains("validation_status: valid_fail_closed"));
    assert!(validation_output.contains("summary: artifact_present=true, passed=5/5"));
    assert!(validation_output.contains("tactic_outcome_rows=0"));
    assert!(validation_output.contains("acceptance_evidence_candidate=false"));
    assert!(validation_output.contains("missing_acceptance_requirements: replace generated schema fixture with real Lean4-vs-clean tactic outcome rows; include at least 1 tactics[] Lean4-vs-clean outcome row"));
}

#[test]
fn tactic_parity_generated_case_backing_rejects_count_drift() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    let grind = artifact
        .tactics
        .iter_mut()
        .find(|row| row.tactic == "grind")
        .expect("grind count row");
    let generated_cases = grind
        .generated_cases
        .as_mut()
        .expect("grind generated cases");
    generated_cases.matched_case_count -= 1;

    let failures = validate_generated_tactic_case_backing(&artifact)
        .expect_err("generated case/count drift must fail closed");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("matched_case_count")));
}

#[test]
fn tactic_parity_generated_case_backing_rejects_missing_required_cases() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    let exact = artifact
        .tactics
        .iter_mut()
        .find(|row| row.tactic == "exact")
        .expect("exact count row");
    exact.generated_cases = None;

    let failures = validate_generated_tactic_case_backing(&artifact)
        .expect_err("generated-backed exact row must fail closed without generated cases");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("exact is generated-backed")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_summary_drift() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.summary.matched_total -= 1;

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("summary/count drift must fail closed");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("matched_total")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_full_corpus_greenwash() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_lean4_corpus_coverage_claimed = true;
    artifact.launch_readiness_claimed = true;

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must reject full-corpus greenwash");
    assert!(failures
        .iter()
        .any(|failure| failure.contains("full_lean4_corpus_coverage_claimed")));
    assert!(failures
        .iter()
        .any(|failure| failure.contains("launch_readiness_claimed")));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_weakened_reviewer_evidence_checklist() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_reviewer_evidence_required.pop();

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must keep full-corpus reviewer checklist");
    assert!(failures
        .iter()
        .any(|failure| { failure.contains("full_corpus_reviewer_evidence_required") }));
}

#[test]
fn tactic_parity_count_artifact_consistency_rejects_stale_reviewer_evidence_fingerprint() {
    let report = TacticParityReport::current();
    let mut artifact = report.lean4_vs_clean_tactic_counts.clone();
    artifact.full_corpus_reviewer_evidence_fingerprint_sha256 = "stale".to_owned();

    let failures = validate_tactic_count_artifact_consistency(&artifact)
        .expect_err("representative tactic artifact must keep reviewer evidence fingerprint fresh");
    assert!(failures
        .iter()
        .any(|failure| { failure.contains("full_corpus_reviewer_evidence_fingerprint_sha256") }));
}
