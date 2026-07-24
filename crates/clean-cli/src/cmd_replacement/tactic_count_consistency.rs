// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Count artifact consistency and report linkage validation.

use super::*;

pub(crate) fn validate_tactic_count_artifact_consistency(
    artifact: &TacticParityCountArtifact,
) -> Result<(), Vec<String>> {
    let mut failures = Vec::new();
    let expected_summary = TacticParityCountSummary::from_rows(&artifact.tactics);

    if artifact.coverage_scope != "representative-generated-cases-only" {
        failures.push(format!(
            "coverage_scope={} must remain representative-generated-cases-only until full Lean4 corpus parity evidence exists",
            artifact.coverage_scope
        ));
    }
    if artifact.full_lean4_corpus_coverage_claimed {
        failures.push(
            "full_lean4_corpus_coverage_claimed must remain false for the representative count artifact"
                .to_owned(),
        );
    }
    if artifact.launch_readiness_claimed {
        failures.push(
            "launch_readiness_claimed must remain false until broader Lean4 tactic corpus parity evidence exists"
                .to_owned(),
        );
    }
    if !artifact
        .remaining_substantive_replacement_blocker
        .contains("broader Lean4 corpus parity coverage")
    {
        failures.push(
            "remaining_substantive_replacement_blocker must name the broader Lean4 corpus parity coverage blocker"
                .to_owned(),
        );
    }
    if artifact.full_corpus_reviewer_evidence_required.as_slice()
        != TACTIC_FULL_CORPUS_REVIEWER_EVIDENCE_REQUIRED
    {
        failures.push(
            "full_corpus_reviewer_evidence_required must keep the exact full-corpus reviewer evidence checklist"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_gate != TACTIC_FULL_CORPUS_ACCEPTANCE_GATE {
        failures.push(format!(
            "full_corpus_acceptance_gate={} must remain blocked until full-corpus reviewer evidence is present and validated",
            artifact.full_corpus_acceptance_gate
        ));
    }
    if artifact.representative_generated_backing_satisfies_full_corpus_acceptance {
        failures.push(
            "representative_generated_backing_satisfies_full_corpus_acceptance must remain false until full-corpus evidence is validated"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_evidence_status
        != TACTIC_FULL_CORPUS_ACCEPTANCE_EVIDENCE_STATUS
    {
        failures.push(format!(
            "full_corpus_acceptance_evidence_status={} must remain not_submitted until the full-corpus gate is replaced by validated evidence",
            artifact.full_corpus_acceptance_evidence_status
        ));
    }
    if artifact.full_corpus_acceptance_artifact_required
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED
    {
        failures.push(format!(
            "full_corpus_acceptance_artifact_required={} must point at the required full-corpus tactic parity artifact",
            artifact.full_corpus_acceptance_artifact_required
        ));
    }
    if artifact.full_corpus_acceptance_artifact_present {
        failures.push(
            "full_corpus_acceptance_artifact_present must remain false until the required full-corpus tactic parity artifact is checked in and validated"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_artifact_schema_required
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED
    {
        failures.push(format!(
            "full_corpus_acceptance_artifact_schema_required={} must name the required full-corpus tactic parity schema",
            artifact.full_corpus_acceptance_artifact_schema_required
        ));
    }
    if artifact.full_corpus_acceptance_artifact_schema_validated {
        failures.push(
            "full_corpus_acceptance_artifact_schema_validated must remain false until the required full-corpus tactic parity artifact schema is validated"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_validator_required
        != TACTIC_FULL_CORPUS_ACCEPTANCE_VALIDATOR_REQUIRED
    {
        failures.push(format!(
            "full_corpus_acceptance_validator_required={} must name the required Rust-owned full-corpus tactic parity validator",
            artifact.full_corpus_acceptance_validator_required
        ));
    }
    if artifact.full_corpus_acceptance_validator_present {
        failures.push(
            "full_corpus_acceptance_validator_present must remain false until the Rust-owned full-corpus tactic parity validator exists and is wired"
                .to_owned(),
        );
    }
    if artifact.full_corpus_input_discovery_command != TACTIC_FULL_CORPUS_INPUT_DISCOVERY_COMMAND {
        failures.push(format!(
            "full_corpus_input_discovery_command={} must name the Rust-owned full-corpus input discovery command",
            artifact.full_corpus_input_discovery_command
        ));
    }
    if artifact.full_corpus_fixture_generator_command
        != TACTIC_FULL_CORPUS_FIXTURE_GENERATOR_COMMAND
    {
        failures.push(format!(
            "full_corpus_fixture_generator_command={} must name the Rust-owned non-coverage fixture generator",
            artifact.full_corpus_fixture_generator_command
        ));
    }
    if artifact.full_corpus_fixture_counts_as_acceptance_evidence {
        failures.push(
            "full_corpus_fixture_counts_as_acceptance_evidence must remain false because the generated fixture is schema scaffolding, not full-corpus evidence"
                .to_owned(),
        );
    }
    if artifact.full_corpus_fixture_acceptance_blocker
        != TACTIC_FULL_CORPUS_FIXTURE_ACCEPTANCE_BLOCKER
    {
        failures.push(
            "full_corpus_fixture_acceptance_blocker must keep the exact non-evidence blocker for generated schema fixtures"
                .to_owned(),
        );
    }
    if artifact.full_corpus_acceptance_minimum_tactic_outcome_rows
        != TACTIC_FULL_CORPUS_ACCEPTANCE_MINIMUM_TACTIC_OUTCOME_ROWS
    {
        failures.push(format!(
            "full_corpus_acceptance_minimum_tactic_outcome_rows={} must require at least one real Lean4-vs-clean tactic outcome row before acceptance evidence can begin",
            artifact.full_corpus_acceptance_minimum_tactic_outcome_rows
        ));
    }
    if artifact.full_corpus_acceptance_tactic_outcome_row_contract
        != TACTIC_FULL_CORPUS_ACCEPTANCE_TACTIC_OUTCOME_ROW_CONTRACT
    {
        failures.push(
            "full_corpus_acceptance_tactic_outcome_row_contract must keep the exact Lean4-vs-clean outcome row contract"
                .to_owned(),
        );
    }
    if artifact
        .full_corpus_acceptance_manifest_required_fields
        .as_slice()
        != TACTIC_FULL_CORPUS_ACCEPTANCE_MANIFEST_REQUIRED_FIELDS
    {
        failures.push(
            "full_corpus_acceptance_manifest_required_fields must keep the exact full-corpus manifest field contract"
                .to_owned(),
        );
    }
    if artifact
        .full_corpus_acceptance_reviewer_evidence_required_fields
        .as_slice()
        != TACTIC_FULL_CORPUS_ACCEPTANCE_REVIEWER_EVIDENCE_REQUIRED_FIELDS
    {
        failures.push(
            "full_corpus_acceptance_reviewer_evidence_required_fields must keep the exact reviewer evidence field contract"
                .to_owned(),
        );
    }
    if artifact
        .full_corpus_acceptance_artifact_required_fields
        .as_slice()
        != TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS
    {
        failures.push(
            "full_corpus_acceptance_artifact_required_fields must keep the exact full-corpus artifact field contract"
                .to_owned(),
        );
    }

    validate_tactic_count_artifact_fingerprints(artifact, &mut failures);

    if artifact.summary.tactic_row_count != expected_summary.tactic_row_count {
        failures.push(format!(
            "summary tactic_row_count={} does not match tactics={}",
            artifact.summary.tactic_row_count, expected_summary.tactic_row_count
        ));
    }
    if artifact.summary.lean4_total != expected_summary.lean4_total {
        failures.push(format!(
            "summary lean4_total={} does not match row total={}",
            artifact.summary.lean4_total, expected_summary.lean4_total
        ));
    }
    if artifact.summary.clean_total != expected_summary.clean_total {
        failures.push(format!(
            "summary clean_total={} does not match row total={}",
            artifact.summary.clean_total, expected_summary.clean_total
        ));
    }
    if artifact.summary.matched_total != expected_summary.matched_total {
        failures.push(format!(
            "summary matched_total={} does not match row total={}",
            artifact.summary.matched_total, expected_summary.matched_total
        ));
    }
    if artifact.summary.clean_gap_total != expected_summary.clean_gap_total {
        failures.push(format!(
            "summary clean_gap_total={} does not match row total={}",
            artifact.summary.clean_gap_total, expected_summary.clean_gap_total
        ));
    }
    if artifact.summary.proof_carrying_rows != expected_summary.proof_carrying_rows {
        failures.push(format!(
            "summary proof_carrying_rows={} does not match rows={}",
            artifact.summary.proof_carrying_rows, expected_summary.proof_carrying_rows
        ));
    }
    if artifact.summary.partial_rows != expected_summary.partial_rows {
        failures.push(format!(
            "summary partial_rows={} does not match rows={}",
            artifact.summary.partial_rows, expected_summary.partial_rows
        ));
    }
    if artifact.summary.parity_gap_rows != expected_summary.parity_gap_rows {
        failures.push(format!(
            "summary parity_gap_rows={} does not match rows={}",
            artifact.summary.parity_gap_rows, expected_summary.parity_gap_rows
        ));
    }

    let strict = &artifact.strict_solver_fragments;
    if strict.row_count
        != strict.supported_zero_trust_rows + strict.unsupported_reject_and_fallback_rows
    {
        failures.push(format!(
            "strict_solver_fragments row_count={} does not match supported+unsupported={}",
            strict.row_count,
            strict.supported_zero_trust_rows + strict.unsupported_reject_and_fallback_rows
        ));
    }
    if strict.zero_trust_recovery_rows > strict.supported_zero_trust_rows {
        failures.push(format!(
            "strict_solver_fragments zero_trust_recovery_rows={} exceeds supported_zero_trust_rows={}",
            strict.zero_trust_recovery_rows, strict.supported_zero_trust_rows
        ));
    }

    if let Err(generated_failures) = validate_generated_tactic_case_backing(artifact) {
        failures.extend(generated_failures);
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures)
    }
}

pub(crate) fn validate_tactic_parity_report_linkage(
    report: &TacticParityReport,
) -> Result<(), Vec<String>> {
    let mut failures = Vec::new();

    if let Err(artifact_failures) =
        validate_tactic_count_artifact_consistency(&report.lean4_vs_clean_tactic_counts)
    {
        failures.extend(artifact_failures);
    }

    let artifact_strict = &report.lean4_vs_clean_tactic_counts.strict_solver_fragments;
    let dashboard = &report.strict_solver_fragment_dashboard;

    if artifact_strict.source_artifact != dashboard.source_artifact {
        failures.push(format!(
            "strict_solver_fragments source_artifact={} does not match dashboard={}",
            artifact_strict.source_artifact, dashboard.source_artifact
        ));
    }
    if artifact_strict.row_count != dashboard.row_count {
        failures.push(format!(
            "strict_solver_fragments row_count={} does not match dashboard row_count={}",
            artifact_strict.row_count, dashboard.row_count
        ));
    }
    if artifact_strict.supported_zero_trust_rows != dashboard.supported_zero_trust_rows {
        failures.push(format!(
            "strict_solver_fragments supported_zero_trust_rows={} does not match dashboard={}",
            artifact_strict.supported_zero_trust_rows, dashboard.supported_zero_trust_rows
        ));
    }
    if artifact_strict.unsupported_reject_and_fallback_rows
        != dashboard.unsupported_reject_and_fallback_rows
    {
        failures.push(format!(
            "strict_solver_fragments unsupported_reject_and_fallback_rows={} does not match dashboard={}",
            artifact_strict.unsupported_reject_and_fallback_rows,
            dashboard.unsupported_reject_and_fallback_rows
        ));
    }
    if artifact_strict.zero_trust_recovery_rows != dashboard.zero_trust_recovery_rows {
        failures.push(format!(
            "strict_solver_fragments zero_trust_recovery_rows={} does not match dashboard={}",
            artifact_strict.zero_trust_recovery_rows, dashboard.zero_trust_recovery_rows
        ));
    }

    let observed_row_count = dashboard.rows.len();
    let observed_supported_zero_trust_rows = dashboard
        .rows
        .iter()
        .filter(|row| row.behavior == StrictSolverFragmentBehavior::SupportedZeroTrust)
        .count();
    let observed_unsupported_reject_and_fallback_rows = dashboard
        .rows
        .iter()
        .filter(|row| row.behavior == StrictSolverFragmentBehavior::UnsupportedRejectAndFallback)
        .count();
    let observed_zero_trust_recovery_rows = dashboard
        .rows
        .iter()
        .filter(|row| row.zero_trust_recovery)
        .count();

    if dashboard.row_count != observed_row_count {
        failures.push(format!(
            "strict_solver_fragment_dashboard row_count={} does not match rows={}",
            dashboard.row_count, observed_row_count
        ));
    }
    if dashboard.supported_zero_trust_rows != observed_supported_zero_trust_rows {
        failures.push(format!(
            "strict_solver_fragment_dashboard supported_zero_trust_rows={} does not match rows={}",
            dashboard.supported_zero_trust_rows, observed_supported_zero_trust_rows
        ));
    }
    if dashboard.unsupported_reject_and_fallback_rows
        != observed_unsupported_reject_and_fallback_rows
    {
        failures.push(format!(
            "strict_solver_fragment_dashboard unsupported_reject_and_fallback_rows={} does not match rows={}",
            dashboard.unsupported_reject_and_fallback_rows,
            observed_unsupported_reject_and_fallback_rows
        ));
    }
    if dashboard.zero_trust_recovery_rows != observed_zero_trust_recovery_rows {
        failures.push(format!(
            "strict_solver_fragment_dashboard zero_trust_recovery_rows={} does not match rows={}",
            dashboard.zero_trust_recovery_rows, observed_zero_trust_recovery_rows
        ));
    }

    let expected_dashboard_status = if dashboard.strict_reconstruction_gate.passed {
        "passed"
    } else {
        "blocked"
    };
    if dashboard.status != expected_dashboard_status {
        failures.push(format!(
            "strict_solver_fragment_dashboard status={} does not match gate={}",
            dashboard.status, expected_dashboard_status
        ));
    }

    let dashboard_row = report
        .strict_reconstruction
        .iter()
        .find(|row| row.fragment == "strict_solver_fragment_dashboard");
    match dashboard_row {
        Some(row) => {
            let expected_status = if dashboard.strict_reconstruction_gate.passed {
                StrictReconstructionStatus::SupportedZeroTrust
            } else {
                StrictReconstructionStatus::EvidenceGap
            };
            if row.status != expected_status {
                failures.push(format!(
                    "strict_reconstruction dashboard status={:?} does not match gate={:?}",
                    row.status, expected_status
                ));
            }
            if row.evidence != dashboard.source_artifact {
                failures.push(format!(
                    "strict_reconstruction dashboard evidence={} does not match dashboard source={}",
                    row.evidence, dashboard.source_artifact
                ));
            }
            if row.zero_trust_recovery != (dashboard.zero_trust_recovery_rows > 0) {
                failures.push(format!(
                    "strict_reconstruction dashboard zero_trust_recovery={} does not match dashboard rows={}",
                    row.zero_trust_recovery,
                    dashboard.zero_trust_recovery_rows
                ));
            }
        }
        None => failures.push(
            "strict_reconstruction is missing strict_solver_fragment_dashboard row".to_string(),
        ),
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures)
    }
}
