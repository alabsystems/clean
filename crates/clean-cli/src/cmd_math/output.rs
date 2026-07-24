// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::io::{self, Write};

use serde::Serialize;

use super::artifact::ArtifactEnvelopeReport;
use super::error::MathError;
use super::proof_state::ProofStateBridgeReport;
use crate::math_project::{has_error, CertificateSummary};

pub(super) fn fail_on_violations(
    violations: &[crate::math_project::ValidationViolation],
    context: &str,
) -> Result<(), MathError> {
    if has_error(violations) {
        return Err(MathError::Failed(format!(
            "{context} produced validation errors"
        )));
    }
    Ok(())
}

pub(super) fn write_output<T: Serialize>(
    json: bool,
    value: &T,
    render_human: impl FnOnce(&mut dyn Write) -> io::Result<()>,
) -> Result<(), MathError> {
    let stdout = io::stdout();
    let mut out = stdout.lock();
    if json {
        writeln!(out, "{}", serde_json::to_string_pretty(value)?)?;
    } else {
        render_human(&mut out)?;
    }
    Ok(())
}

pub(super) fn render_project_status(
    out: &mut dyn Write,
    report: &crate::math_project::MathProjectStatusReport,
) -> io::Result<()> {
    writeln!(out, "project: {}", report.project)?;
    writeln!(out, "domain_profile: {}", report.domain_profile)?;
    writeln!(out, "status: {}", report.status)?;
    writeln!(out, "theorem_packs: {}", report.theorem_packs)?;
    writeln!(out, "obligation_sources: {}", report.obligation_sources)?;
    writeln!(
        out,
        "cached_replay_reports: {}",
        report.replay_cache.cached_reports
    )?;
    writeln!(out, "violations: {}", report.violations.len())
}

pub(super) fn render_hygiene(
    out: &mut dyn Write,
    report: &crate::math_project::HygieneReport,
) -> io::Result<()> {
    writeln!(out, "project: {}", report.project)?;
    writeln!(out, "status: {}", report.status)?;
    for check in &report.checks {
        writeln!(out, "- {}: {}", check.name, check.status)?;
    }
    Ok(())
}

pub(super) fn render_artifact(
    out: &mut dyn Write,
    report: &ArtifactEnvelopeReport,
) -> io::Result<()> {
    writeln!(out, "source_system: {}", report.source_system)?;
    writeln!(out, "artifact_kind: {}", report.artifact_kind)?;
    writeln!(out, "certificate_format: {}", report.certificate_format)?;
    writeln!(out, "status: {}", report.status)
}

pub(super) fn render_certificate(
    out: &mut dyn Write,
    report: &CertificateSummary,
) -> io::Result<()> {
    writeln!(out, "project: {}", report.project)?;
    writeln!(out, "obligation: {}", report.obligation)?;
    writeln!(out, "proof_status: {}", report.proof_status)?;
    writeln!(out, "synthetic_sorry: {}", report.synthetic_sorry)
}

pub(super) fn render_proof_state_report(
    out: &mut dyn Write,
    report: &ProofStateBridgeReport,
) -> io::Result<()> {
    writeln!(out, "operation: {}", report.operation)?;
    writeln!(out, "status: {}", report.status)?;
    writeln!(out, "detail: {}", report.detail)
}
