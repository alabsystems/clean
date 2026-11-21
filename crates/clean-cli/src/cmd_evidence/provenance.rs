// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Provenance recorded by the historical P3 experiments.

use super::evaluate::evaluate;
use super::reading::Outcome;
use super::{read_json, Figure, TrustPinsSchema, TrustRevision, TRUST_PINS};
use crate::EvidenceCheckError;
use serde::Deserialize;
use std::io::Write;
use std::path::Path;

pub(super) struct ReportProvenance {
    pub(super) fields: Vec<(&'static str, Option<String>)>,
    pub(super) legs: Option<Vec<RecordedLeg>>,
}

#[derive(Deserialize)]
pub(super) struct RecordedLeg {
    leg: String,
    package: Option<String>,
    test: Option<String>,
    workspace: Option<String>,
    command: String,
    exit_status: i32,
}

#[derive(Deserialize)]
struct TrustProvenance {
    #[serde(rename = "schema")]
    _schema: TrustPinsSchema,
    measured_at: String,
    clean_commit: Option<String>,
    trust: TrustRevision,
    clean_pin_in_trust: String,
    #[serde(default)]
    legs: Vec<RecordedLeg>,
}

pub(super) fn read_trust(root: &Path) -> Result<ReportProvenance, EvidenceCheckError> {
    let report: TrustProvenance = read_json(root, TRUST_PINS)?;
    Ok(ReportProvenance {
        fields: vec![
            ("Measured at", Some(report.measured_at)),
            ("Measured Trust commit", Some(report.trust.commit)),
            (
                "Measured Clean pin in Trust",
                Some(report.clean_pin_in_trust),
            ),
            ("Producer's Clean checkout", report.clean_commit),
            ("Recorded producer command", None),
            ("Recorded Rust toolchain", None),
            ("Recorded Lean toolchain", None),
        ],
        legs: Some(report.legs),
    })
}

pub(super) fn write_explanation(
    figure: &'static Figure,
    root: &Path,
    output: &mut impl Write,
) -> anyhow::Result<()> {
    if let Some(reason) = figure.absent_reason() {
        writeln!(output, "{} — absent: {reason}", figure.id)?;
        writeln!(output, "  Plan {} (lane {})", figure.plan_unit, figure.lane)?;
        return Ok(());
    }
    let report = figure
        .provenance
        .map(|read_provenance| read_provenance(root))
        .transpose()?;
    let kind = if figure.historical {
        "historical evidence"
    } else {
        "evidence"
    };
    writeln!(output, "{} — {kind}", figure.id)?;
    if let Some(module) = figure.producer_module {
        writeln!(output, "  Producer module  {module}")?;
    } else {
        writeln!(output, "  Producer  manual inventory")?;
    }
    writeln!(
        output,
        "  Check inputs     {}",
        figure.input_scope.join(", ")
    )?;
    let Some(report) = report else {
        return write_reading(figure, root, output);
    };
    for (label, value) in report.fields {
        let value = value.as_deref().filter(|value| !value.trim().is_empty());
        writeln!(
            output,
            "  {label}  {}",
            value.unwrap_or("unavailable").escape_debug()
        )?;
    }
    let Some(legs) = report.legs else {
        return Ok(());
    };
    writeln!(output, "Recorded test legs")?;
    if legs.is_empty() {
        writeln!(output, "  unavailable")?;
    }
    for leg in legs {
        write!(output, "  {}", leg.leg.escape_debug())?;
        if let Some(target) = leg.package.or(leg.test) {
            write!(output, " {}", target.escape_debug())?;
        }
        if let Some(workspace) = leg.workspace {
            write!(output, " in {}", workspace.escape_debug())?;
        }
        writeln!(output, " (exit {})", leg.exit_status)?;
        writeln!(output, "    {}", leg.command.escape_debug())?;
    }
    Ok(())
}

/// For a figure whose record has no further provenance, show what its
/// reading records: commit, date, labels, non-claims and freshness.
fn write_reading(
    figure: &'static Figure,
    root: &Path,
    output: &mut impl Write,
) -> anyhow::Result<()> {
    let Some(result) = evaluate(root, &[figure]).into_iter().next() else {
        return Ok(());
    };
    let reading = match result? {
        Outcome::Absent { reason } => {
            writeln!(output, "  Absent  {}", reason.escape_debug())?;
            return Ok(());
        }
        Outcome::Measured(reading) => reading,
    };
    for (label, value) in [
        ("Recorded commit", reading.commit.as_deref()),
        ("Recorded at", reading.recorded_at.as_deref()),
    ] {
        writeln!(
            output,
            "  {label}  {}",
            value.unwrap_or("unavailable").escape_debug()
        )?;
    }
    for label in &reading.labels {
        writeln!(output, "  Label  {}", label.escape_debug())?;
    }
    for claim in &reading.non_claims {
        writeln!(output, "  Not claimed  {}", claim.escape_debug())?;
    }
    writeln!(
        output,
        "  Freshness  {} ({})",
        reading.freshness.label(),
        reading.freshness.reason.escape_debug()
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cmd_evidence::{find_figure, CLEAN_FIGURE, CLEAN_PINS, SCOREBOARD, TRUST_FIGURE};
    use serde_json::{json, Value};
    use std::fs;

    fn write_report(root: &Path, path: &str, report: Value) {
        let path = root.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, serde_json::to_vec(&report).unwrap()).unwrap();
    }

    #[test]
    fn clean_explanation_uses_recorded_metadata_without_a_scoreboard() {
        let root = tempfile::tempdir().unwrap();
        write_report(
            root.path(),
            CLEAN_PINS,
            json!({
                "schema": "clean.patched_kernel_control.v1",
                "mutation": {"id": "check-type-nat-zero-false"},
                "measured_commit": "clean-measurement",
                "generated_at": "2026-11-17T00:00:00Z",
                "minted_by": "recorded producer --flag",
                "toolchain": "recorded targo",
                "lean_toolchain": "recorded Lean",
                "legs": [{
                    "leg": "undeclared", "package": "clean-kernel",
                    "exit_status": 101, "command": "recorded test command"
                }]
            }),
        );
        let figure = find_figure(CLEAN_FIGURE).unwrap();
        let mut output = Vec::new();
        write_explanation(figure, root.path(), &mut output).unwrap();
        let output = String::from_utf8(output).unwrap();
        for fragment in [
            SCOREBOARD,
            "Report generated  2026-11-17T00:00:00Z",
            "Measured Clean commit  clean-measurement",
            "Recorded producer command  recorded producer --flag",
            "Recorded Rust toolchain  recorded targo",
            "Recorded Lean toolchain  recorded Lean",
            "undeclared clean-kernel (exit 101)\n    recorded test command",
        ] {
            assert!(output.contains(fragment), "missing {fragment:?}: {output}");
        }
    }

    #[test]
    fn trust_explanation_distinguishes_revisions_and_omits_absent_run_details() {
        let root = tempfile::tempdir().unwrap();
        write_report(
            root.path(),
            TRUST_PINS,
            json!({
                "schema": "clean.p3-trust-leg/v2",
                "measured_at": "2026-11-15T22:23:17Z",
                "trust": {"commit": "trust-measurement"},
                "clean_pin_in_trust": "measured-clean-pin",
                "clean_commit": "producer-clean-head",
                "legs": [{
                    "leg": "unmodified", "test": "p3_planted_temporal",
                    "workspace": "crates/trust-spec-temporal", "exit_status": 0,
                    "command": "recorded command\nwith a newline"
                }]
            }),
        );
        let figure = find_figure(TRUST_FIGURE).unwrap();
        let mut output = Vec::new();
        write_explanation(figure, root.path(), &mut output).unwrap();
        let output = String::from_utf8(output).unwrap();
        for fragment in [
            "Measured at  2026-11-15T22:23:17Z",
            "Measured Trust commit  trust-measurement",
            "Measured Clean pin in Trust  measured-clean-pin",
            "Producer's Clean checkout  producer-clean-head",
            "Recorded producer command  unavailable",
            "Recorded Rust toolchain  unavailable",
            "Recorded Lean toolchain  unavailable",
            "unmodified p3_planted_temporal in crates/trust-spec-temporal (exit 0)",
            "recorded command\\nwith a newline",
        ] {
            assert!(output.contains(fragment), "missing {fragment:?}: {output}");
        }
    }
}
