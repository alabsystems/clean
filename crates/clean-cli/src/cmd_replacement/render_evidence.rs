// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Human renderers for hygiene, axiom-audit, parity, and evidence.

use super::*;

pub(crate) fn release_issue_join_or_dash(values: &[String]) -> String {
    if values.is_empty() {
        "-".to_string()
    } else {
        values.join("; ")
    }
}

pub(crate) fn render_axiom_audit_human(
    out: &mut impl Write,
    verification: &AxiomAuditVerification,
) -> Result<(), ReplacementError> {
    writeln!(out, "clean axiom-audit verification")?;
    writeln!(out, "schema_version: {}", verification.schema_version)?;
    writeln!(out, "status: {}", verification.status)?;
    writeln!(out, "audit_path: {}", verification.audit_path)?;
    writeln!(
        out,
        "summary: domain_axioms={}, all_axioms={}, nonzero_rows={}",
        verification.axiom_audit.total_domain_axioms,
        verification.axiom_audit.total_all_axioms,
        verification.axiom_audit.nonzero_axiom_rows
    )?;
    if let Some(evidence_path) = &verification.evidence_path {
        writeln!(out, "evidence_path: {evidence_path}")?;
    }
    for lane in &verification.lanes {
        writeln!(out, "- {}: {}", lane.id, lane.status)?;
    }
    if !verification.failures.is_empty() {
        writeln!(out, "failures: {}", verification.failures.join("; "))?;
    }
    Ok(())
}

pub(crate) fn utc_timestamp_seconds() -> String {
    let seconds = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .unwrap_or(0);
    format!("unix:{seconds}")
}

pub(crate) fn render_tactic_parity_human(
    out: &mut impl Write,
    report: &TacticParityReport,
) -> Result<(), ReplacementError> {
    writeln!(out, "Clean tactic parity status")?;
    writeln!(out, "schema_version: {}", report.schema_version)?;
    writeln!(out, "launch_ready: {}", report.launch_ready)?;
    writeln!(out, "tactics:")?;
    for row in &report.tactics {
        writeln!(
            out,
            "- {} [{}]",
            row.tactic,
            row.lean4_parity_status.as_str()
        )?;
        writeln!(out, "  evidence: {}", row.evidence)?;
        writeln!(out, "  blocker: {}", row.blocker)?;
    }
    writeln!(
        out,
        "lean4_vs_clean_tactic_counts: {}",
        report.lean4_vs_clean_tactic_counts.source_artifact
    )?;
    writeln!(out, "strict_reconstruction:")?;
    for row in &report.strict_reconstruction {
        writeln!(out, "- {} [{}]", row.fragment, row.status.as_str())?;
        writeln!(out, "  evidence: {}", row.evidence)?;
        writeln!(out, "  blocker: {}", row.blocker)?;
    }
    writeln!(out, "strict_solver_fragment_dashboard:")?;
    writeln!(
        out,
        "  evidence: {}",
        report.strict_solver_fragment_dashboard.source_artifact
    )?;
    writeln!(
        out,
        "  strict_reconstruction_gate: {}",
        report
            .strict_solver_fragment_dashboard
            .strict_reconstruction_gate
            .passed
    )?;
    writeln!(
        out,
        "  row_count: {}",
        report.strict_solver_fragment_dashboard.row_count
    )?;
    writeln!(
        out,
        "  supported_zero_trust_rows: {}",
        report
            .strict_solver_fragment_dashboard
            .supported_zero_trust_rows
    )?;
    writeln!(
        out,
        "  unsupported_reject_and_fallback_rows: {}",
        report
            .strict_solver_fragment_dashboard
            .unsupported_reject_and_fallback_rows
    )?;
    Ok(())
}

pub(crate) fn render_trust_core_evidence_human(
    out: &mut impl Write,
    report: &TrustCoreEvidenceReport,
) -> Result<(), ReplacementError> {
    writeln!(out, "clean trust-core evidence")?;
    writeln!(out, "schema_version: {}", report.schema_version)?;
    writeln!(out, "launch_ready: {}", report.launch_ready)?;
    writeln!(out, "overall_status: {}", report.overall_status)?;
    writeln!(
        out,
        "kernel_differential: {} cases, {} expressions, sha256_match={}",
        report.kernel_differential.baseline_cases,
        report.kernel_differential.expression_count,
        report.kernel_differential.expressions_sha256_match
    )?;
    writeln!(
        out,
        "kernel_gate: {}, preflight_required={}, launch_evidence={}",
        report.kernel_differential.gate_command,
        report.kernel_differential.gate_preflight_required,
        report.kernel_differential.launch_evidence_status
    )?;
    writeln!(
        out,
        "fallback_denial: structural={}, unchecked={}, last_updated={}, launch_evidence={}",
        report
            .fallback_denial
            .unchecked_decl_ratchet
            .add_decl_structural_count,
        report
            .fallback_denial
            .unchecked_decl_ratchet
            .add_decl_unchecked_count,
        report.fallback_denial.unchecked_decl_ratchet.last_updated,
        report.fallback_denial.launch_evidence_status
    )?;
    writeln!(
        out,
        "axiom_audit: domain_axioms={}, all_axioms={}, nonzero_rows={}",
        report.axiom_audit.total_domain_axioms,
        report.axiom_audit.total_all_axioms,
        report.axiom_audit.nonzero_axiom_rows
    )?;
    writeln!(
        out,
        "proof_system_certification: status={}, zero_trust_gates_passed={}, verification_audit_open_lanes={}, replay_parity_blockers={}",
        report.proof_system_certification.status.as_str(),
        report.proof_system_certification.zero_trust_gates_passed,
        report
            .proof_system_certification
            .blocking_verification_audit_lanes,
        report.proof_system_certification.blocking_replay_parity_rows
    )?;
    Ok(())
}

pub(crate) fn render_trust_boundary_audit_markdown(report: &TrustBoundaryAuditReport) -> String {
    let mut lines = vec![
        "<!-- Andrew Yates <andrewyates.name@gmail.com> -->\n".to_owned(),
        "# Gate 2 TrustBoundary Audit Report\n".to_owned(),
        "**Issue:** #2875\n".to_owned(),
        "**Generated by:** `clean replacement trust-boundary-audit`\n".to_owned(),
        format!("**Input files:** {}\n", report.input_files.join(", ")),
        String::new(),
        "## Summary\n".to_owned(),
        format!("- **Total raw hits:** {}", report.total_raw_hits),
    ];
    for (crate_name, count) in &report.by_crate {
        lines.push(format!("  - `{crate_name}`: {count}"));
    }
    lines.push(format!(
        "- **Expected boundary-only hits:** {}",
        report.expected_boundary_only_hits
    ));
    lines.push(format!("- **Unexpected hits:** {}", report.unexpected_hits));
    lines.push(String::new());

    if !report.unexpected_groups.is_empty() {
        lines.push("## Unexpected Hits\n".to_owned());
        lines.push(format!(
            "These hits were NOT matched by any pattern in `{}`.\n",
            report.expected_patterns_path
        ));
        append_trust_boundary_hit_table(&mut lines, &report.unexpected_groups);
        lines.push(String::new());
    }

    if !report.expected_groups.is_empty() {
        lines.push("## Expected Boundary-Only Hits\n".to_owned());
        lines.push(format!(
            "These hits matched patterns in `{}` and are expected.\n",
            report.expected_patterns_path
        ));
        append_trust_boundary_hit_table(&mut lines, &report.expected_groups);
        lines.push(String::new());
    }

    lines.push("## Gate 2 Recommendation\n".to_owned());
    lines.push(format!("**{}**\n", report.recommendation));
    lines.push("## Rerun Commands\n".to_owned());
    lines.push("```bash".to_owned());
    lines.extend(report.rerun_commands.iter().cloned());
    lines.push("```".to_owned());
    lines.join("\n")
}

pub(crate) fn append_trust_boundary_hit_table(
    lines: &mut Vec<String>,
    hits: &[TrustBoundaryGroupedHit],
) {
    lines.push("| Crate | Test | Lane | Tactic | Subsystem | Count | Arith |".to_owned());
    lines.push("|-------|------|------|--------|-----------|-------|-------|".to_owned());
    for hit in hits {
        lines.push(format!(
            "| {} | `{}` | {} | {} | {} | {} | {} |",
            hit.crate_name,
            hit.test_name,
            hit.lane,
            hit.tactic,
            hit.subsystem,
            hit.count,
            hit.total_arith
        ));
    }
}
