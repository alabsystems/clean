// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Human renderers for status, validation, and corpus surfaces.

use super::*;

pub(crate) fn render_human(
    out: &mut impl Write,
    report: &ReplacementStatusReport,
) -> Result<(), ReplacementError> {
    writeln!(out, "clean replacement status")?;
    writeln!(out, "target_claim: {}", report.target_claim)?;
    writeln!(out, "launch_ready: {}", report.launch_ready)?;
    writeln!(out, "overall_status: {}", report.overall_status.as_str())?;
    writeln!(
        out,
        "zero_trust_gates_passed: {}",
        report.zero_trust_gates_passed
    )?;
    writeln!(
        out,
        "product_epic: #{} {}",
        report.product_epic.number, report.product_epic.title
    )?;
    writeln!(
        out,
        "rust_first_tooling: {} commands [{}]",
        report.rust_first_tooling.commands.len(),
        report.rust_first_tooling.overall_status.as_str()
    )?;
    writeln!(
        out,
        "readiness_accounting: {}/{} required rows green; launch blockers {:?}",
        report.readiness_accounting.green_required_row_count,
        report.readiness_accounting.required_row_count,
        report.readiness_accounting.launch_blocking_row_ids
    )?;
    writeln!(
        out,
        "python_wrappers: {} remaining, {} launch-blocking",
        report.readiness_accounting.remaining_python_wrapper_count,
        report
            .readiness_accounting
            .launch_blocking_python_wrapper_count
    )?;
    writeln!(
        out,
        "python_certification_dependencies: {} {:?}",
        report
            .readiness_accounting
            .certification_python_dependency_count,
        report
            .readiness_accounting
            .certification_python_dependency_ids
    )?;
    writeln!(
        out,
        "full_replacement_certification: launch_ready={}, rows_ready={}, zero_trust_gates_passed={}, rust_first_tooling_ready={}",
        report
            .readiness_accounting
            .full_replacement_certification_gate
            .launch_ready,
        report
            .readiness_accounting
            .full_replacement_certification_gate
            .replacement_rows_ready,
        report
            .readiness_accounting
            .full_replacement_certification_gate
            .zero_trust_gates_passed,
        report
            .readiness_accounting
            .full_replacement_certification_gate
            .rust_first_tooling_ready
    )?;
    writeln!(out, "zero_trust_gates:")?;
    for gate in &report.zero_trust_gates {
        writeln!(out, "- {} [{}]", gate.id, gate.status.as_str())?;
        writeln!(out, "  gate: {}", gate.command)?;
        writeln!(out, "  active_debt_count: {}", gate.active_debt_count)?;
        writeln!(out, "  evidence: {}", gate.evidence_summary)?;
        writeln!(out, "  blocker: {}", gate.fail_closed_reason)?;
    }
    writeln!(out, "rows:")?;
    for row in &report.rows {
        writeln!(
            out,
            "- {} [{}] #{} {}",
            row.id,
            row.status.as_str(),
            row.issue.number,
            row.area
        )?;
        writeln!(out, "  gate: {}", row.gate_command)?;
        if let Some(evidence) = replacement_row_runtime_evidence(report, row) {
            writeln!(out, "  evidence: {}", evidence)?;
        }
        writeln!(out, "  blocker: {}", row.blocker)?;
    }
    Ok(())
}

pub(crate) fn replacement_row_runtime_evidence<'a>(
    report: &'a ReplacementStatusReport,
    row: &ReplacementRow,
) -> Option<&'a str> {
    match row.id {
        "proof-system-certification" => {
            Some(report.proof_system_certification.evidence_summary.as_str())
        }
        "kernel-differential" => report
            .zero_trust_gates
            .iter()
            .find(|gate| gate.id == "kernel-soundness")
            .map(|gate| gate.evidence_summary.as_str()),
        "fallback-denial" => report
            .zero_trust_gates
            .iter()
            .find(|gate| gate.id == "deny-sorry")
            .map(|gate| gate.evidence_summary.as_str()),
        _ => None,
    }
}

pub(crate) fn render_report_validation_human(
    out: &mut impl Write,
    validation: &ReplacementReportValidation,
) -> Result<(), ReplacementError> {
    writeln!(out, "clean replacement report validation")?;
    writeln!(out, "schema_version: {}", validation.schema_version)?;
    writeln!(out, "report_kind: {}", validation.report_kind.as_str())?;
    writeln!(out, "report_path: {}", validation.report_path)?;
    writeln!(out, "validation_status: {}", validation.validation_status)?;
    writeln!(
        out,
        "summary: rows={}, evidence_rows={}, blockers={}, launch_ready_claimed={}",
        validation.row_count,
        validation.evidence_row_count,
        validation.blocker_count,
        validation.launch_ready_claimed
    )?;
    for check in &validation.checks {
        writeln!(out, "- {:?}: {}", check.status, check.id)?;
        writeln!(out, "  {}", check.detail)?;
    }
    if !validation.failures.is_empty() {
        writeln!(out, "failures: {}", validation.failures.join("; "))?;
    }
    Ok(())
}

pub(crate) fn render_tactic_parity_full_corpus_validation_human(
    out: &mut impl Write,
    validation: &TacticParityFullCorpusValidation,
) -> Result<(), ReplacementError> {
    writeln!(out, "Clean tactic parity full-corpus validation")?;
    writeln!(out, "schema_version: {}", validation.schema_version)?;
    writeln!(out, "report_path: {}", validation.report_path)?;
    writeln!(out, "validation_status: {}", validation.validation_status)?;
    writeln!(
        out,
        "summary: artifact_present={}, passed={}/{}, required_fields={}, tactic_outcome_rows={}, acceptance_evidence_candidate={}",
        validation.artifact_present,
        validation.passed_count,
        validation.check_count,
        validation.required_fields.len(),
        validation.tactic_outcome_row_count,
        validation.acceptance_evidence_candidate
    )?;
    for check in &validation.checks {
        writeln!(out, "- {:?}: {}", check.status, check.id)?;
        writeln!(out, "  {}", check.detail)?;
    }
    if !validation.failures.is_empty() {
        writeln!(out, "failures: {}", validation.failures.join("; "))?;
    }
    if !validation.missing_acceptance_requirements.is_empty() {
        writeln!(
            out,
            "missing_acceptance_requirements: {}",
            validation.missing_acceptance_requirements.join("; ")
        )?;
    }
    Ok(())
}

pub(crate) fn render_tactic_parity_full_corpus_input_discovery_human(
    out: &mut impl Write,
    discovery: &TacticParityFullCorpusInputDiscovery,
) -> Result<(), ReplacementError> {
    writeln!(out, "Clean tactic parity full-corpus input discovery")?;
    writeln!(out, "schema_version: {}", discovery.schema_version)?;
    writeln!(out, "registry_path: {}", discovery.registry_path)?;
    writeln!(out, "discovery_status: {}", discovery.discovery_status)?;
    writeln!(
        out,
        "summary: lanes={}, real_artifacts={}/{}, missing_outcome_evidence={}, acceptance_evidence_candidate={}",
        discovery.lane_count,
        discovery.discovered_real_artifact_count,
        discovery.expected_real_artifact_count,
        discovery.missing_outcome_evidence_count,
        discovery.acceptance_evidence_candidate
    )?;
    for lane in &discovery.lanes {
        writeln!(
            out,
            "- {}: corpus_cases={}, real_artifact_present={}, outcome_artifact_present={}",
            lane.tactic_lane,
            lane.source_case_count,
            lane.real_generated_count_artifact_present,
            !lane.missing_full_corpus_outcome_evidence
        )?;
        if !lane.blockers.is_empty() {
            writeln!(out, "  blockers: {}", lane.blockers.join("; "))?;
        }
    }
    if !discovery.blockers.is_empty() {
        writeln!(out, "blockers: {}", discovery.blockers.join("; "))?;
    }
    Ok(())
}

pub(crate) fn render_tactic_parity_full_corpus_fixture_generation_human(
    out: &mut impl Write,
    generation: &TacticParityFullCorpusFixtureGeneration,
) -> Result<(), ReplacementError> {
    writeln!(out, "Clean tactic parity full-corpus fixture generation")?;
    writeln!(out, "schema_version: {}", generation.schema_version)?;
    writeln!(out, "output_path: {}", generation.output_path)?;
    writeln!(
        out,
        "artifact_schema_version: {}",
        generation.artifact_schema_version
    )?;
    writeln!(out, "coverage_claimed: {}", generation.coverage_claimed)?;
    writeln!(
        out,
        "launch_readiness_claimed: {}",
        generation.launch_readiness_claimed
    )?;
    writeln!(
        out,
        "validation_status: {}",
        generation.validation.validation_status
    )?;
    if !generation.validation.failures.is_empty() {
        writeln!(
            out,
            "failures: {}",
            generation.validation.failures.join("; ")
        )?;
    }
    Ok(())
}

pub(crate) fn render_release_issue_hygiene_human(
    out: &mut impl Write,
    report: &ReleaseIssueHygieneReport,
) -> Result<(), ReplacementError> {
    writeln!(out, "clean release issue hygiene")?;
    writeln!(out, "schema_version: {}", report.schema_version)?;
    writeln!(out, "ready: {}", report.ready)?;
    writeln!(out, "status: {}", report.status)?;
    writeln!(out, "input_mode: {}", report.input_source.mode)?;
    writeln!(
        out,
        "summary: scanned={}, release_impacting={}, non_ready={}",
        report.summary.scanned, report.summary.release_impacting, report.summary.non_ready
    )?;
    writeln!(out, "watched_labels: {}", report.watched_labels.join(", "))?;
    writeln!(
        out,
        "missing_fields: {}",
        release_issue_join_or_dash(&report.missing_fields)
    )?;
    writeln!(
        out,
        "suggested_actions: {}",
        release_issue_join_or_dash(&report.suggested_actions)
    )?;
    if !report.non_ready_issues.is_empty() {
        writeln!(out, "non_ready_issues:")?;
        for issue in &report.non_ready_issues {
            writeln!(out, "- #{} {}", issue.number, issue.title)?;
            writeln!(out, "  missing_fields: {}", issue.missing_fields.join(", "))?;
            writeln!(
                out,
                "  suggested_actions: {}",
                issue.suggested_actions.join("; ")
            )?;
        }
    }
    writeln!(out, "blocker: {}", report.parity_blocker)?;
    Ok(())
}
